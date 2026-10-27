module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Bound
public import Certificates.Data.TabCo1ThreeKit

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Block CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F Matrix

attribute [local instance] CFSG.Sporadic.Co1Schreier.vecAct

section Spec

theorem boundOKF_spec {cs : Array (Array ℕ)} {nb nfix : ℕ} {base : List ℕ}
    {conds : List (List Cond)} {cnts : List ℕ} {span : List (ℕ × ℕ)} {comb : List ℕ}
    (h : boundOKF cs nb base nfix conds cnts span comb = true) :
    cs.size = nb ∧ conds.length = base.length ∧ cnts.length = base.length ∧
      (∀ i < base.length, base.getD i 0 ∈ certVecs.toList ∧
        (i < nfix → cnts.getD i 0 = 1) ∧
        (¬ i < nfix → (candList (xsSet ()) cs (base.take i) (base.getD i 0)
          (conds.getD i [])).length ≤ cnts.getD i 0)) ∧ spanOK cs nb base span comb = true := by
  unfold boundOKF at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, fun i hi => ?_, h5⟩
  have := h4 i hi
  unfold lvlOKF at this
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨contains_xs.1 this.1, fun hf => ?_, fun hf => ?_⟩
  · have h6 := this.2
    rw [if_pos hf] at h6
    exact of_decide_eq_true h6
  · have h6 := this.2
    rw [if_neg hf] at h6
    exact of_decide_eq_true h6

end Spec

section Main

variable
  {cs : Array (Array ℕ)} {H : Subgroup GL24} {base : List ℕ}

theorem card_le_of_boundOKF (hHA : H ≤ GA) {nb nfix : ℕ} {β : ℕ → GL24}
    (hcs : ∀ a < nb, ActsBy (β a) (cs.getD a #[]))
    (hcl : ∀ (a j : ℕ), (cs.getD a #[])[j]?.getD 0 < 2 ^ 24)
    (hcomm : ∀ g ∈ H, ∀ a < nb, g * β a = β a * g)
    (hfix : ∀ g ∈ H, ∀ i < nfix, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      toVecD 24 (base.getD i 0) = toVecD 24 (base.getD i 0))
    {conds : List (List Cond)} {cnts : List ℕ} {span : List (ℕ × ℕ)} {comb : List ℕ}
    (h : boundOKF cs nb base nfix conds cnts span comb = true) : Nat.card H ≤ cnts.prod := by
  obtain ⟨hsz, -, hcnt, hlev, hspanOK⟩ := boundOKF_spec h
  obtain ⟨hs24, -, hspj, hspan⟩ := spanOK_spec hspanOK
  let B : ℕ → Matrix (Fin 24) (Fin 24) (ZMod 2) :=
    fun a => if a < nb then ((β a : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) else 0
  have hB : ∀ a v, B a *ᵥ toVecD 24 v = toVecD 24 (vecMulN 24 (cs.getD a #[]) v) := by
    intro a v
    by_cases ha : a < nb
    · simp only [B, if_pos ha]
      exact hcs a ha v
    · simp only [B, if_neg ha]
      rw [cs_getD_of_le hsz (by omega), toVecD_vecMulN_empty, Matrix.zero_mulVec]
  have hcB : ∀ g ∈ H, ∀ a, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) * B a =
      B a * ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
    intro g hg a
    by_cases ha : a < nb
    · simp only [B, if_pos ha]
      rw [← Units.val_mul, ← Units.val_mul, hcomm g hg a ha]
    · simp only [B, if_neg ha, Matrix.mul_zero, Matrix.zero_mul]
  have horb : ∀ i < base.length,
      Nat.card (MulAction.orbit (vCh H base i) (toVecD 24 (base.getD i 0))) ≤ cnts.getD i 0 := by
    intro i hi
    obtain ⟨hu, hf1, hf2⟩ := hlev i hi
    by_cases hf : i < nfix
    · rw [hf1 hf]
      have hsub : (MulAction.orbit (vCh H base i) (toVecD 24 (base.getD i 0)) : Set Vec24) ⊆
          {toVecD 24 (base.getD i 0)} := by
        intro w hw
        obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 hw
        have hgw : g • toVecD 24 (base.getD i 0) =
            ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ toVecD 24 (base.getD i 0) := by
          rw [Subgroup.smul_def, vecAct_smul]
        rw [hgw, hfix g (vCh_le i g.2) i hf]
        rfl
      calc Nat.card (MulAction.orbit (vCh H base i) (toVecD 24 (base.getD i 0)))
          = Set.ncard (MulAction.orbit (vCh H base i) (toVecD 24 (base.getD i 0)) : Set Vec24) :=
            Nat.card_coe_set_eq _
        _ ≤ Set.ncard ({toVecD 24 (base.getD i 0)} : Set Vec24) :=
            Set.ncard_le_ncard hsub (Set.finite_singleton _)
        _ = 1 := Set.ncard_singleton _
    · exact le_trans (card_orbit_le_candList hHA hB hcl hcB i hu (conds.getD i []))
        (hf2 hf)
  have key := card_le_prod_of_orbit_bound (H := H) (base := base) (fun i => cnts.getD i 0) horb
    (fun g hg => eq_one_of_fix_span hB (hcB g (vCh_le _ hg))
      (fun j hj => fix_of_mem_vCh hg hj) hs24 (fun s hs => (hspj s hs).1) hspan)
  rwa [← hcnt, prod_range_getD] at key

theorem card_le_of_listBoundF {rs : List Native.Rows} {βs : List GL24}
    (hr : List.Forall₂ MRep rs βs) (hHA : H ≤ GA)
    (hcomm : ∀ g ∈ H, ∀ β ∈ βs, g * β = β * g) {nb nfix : ℕ} (hnb : rs.length = nb)
    (hfix : ∀ g ∈ H, ∀ i < nfix, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      toVecD 24 (base.getD i 0) = toVecD 24 (base.getD i 0))
    {conds : List (List Cond)} {cnts : List ℕ} {span : List (ℕ × ℕ)} {comb : List ℕ}
    (h : boundOKF (colsOf rs) nb base nfix conds cnts span comb = true) :
    Nat.card H ≤ cnts.prod := by
  subst hnb
  have hlen : rs.length = βs.length := hr.length_eq
  refine card_le_of_boundOKF (β := fun a => βs.getD a 1) hHA ?_ ?_ ?_ hfix h
  · intro a ha
    rw [colsOf_getD ha]
    exact (getD_rep hr MRep.one a).actsBy
  · intro a j
    by_cases ha : a < rs.length
    · rw [colsOf_getD ha]
      exact CFSG.Sporadic.Co1.Module.transposeRows_lt _ j
    · rw [colsOf_getD_of_le (not_lt.1 ha)]
      simp
  · intro g hg a ha
    refine hcomm g hg _ ?_
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _

theorem card_le_of_powBoundF (hHA : H ≤ GA) {k : GL24} {kR : Native.Rows} (rk : MRep kR k)
    (n nfix : ℕ) (hcent : H ≤ Subgroup.centralizer ({k} : Set GL24))
    (hfix : ∀ g ∈ H, ∀ i < nfix, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      toVecD 24 (base.getD i 0) = toVecD 24 (base.getD i 0))
    {conds : List (List Cond)} {cnts : List ℕ} {span : List (ℕ × ℕ)} {comb : List ℕ}
    (h : boundOKF (colsOf (powList kR n)) n base nfix conds cnts span comb = true) :
    Nat.card H ≤ cnts.prod := by
  have hr : List.Forall₂ MRep (powList kR n) ((List.range n).map fun a => k ^ a) := by
    unfold powList
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun a _ => ?_
    exact rk.pow a
  have hlen : (powList kR n).length = n := by simp [powList]
  have hc : ∀ g ∈ H, ∀ β ∈ (List.range n).map (fun a => k ^ a), g * β = β * g := by
    intro g hg β hβ
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hβ
    have h0 := hcent hg
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 h0
    exact comm_pow_aux h1 a
  exact card_le_of_listBoundF hr hHA hc hlen hfix h

end Main

section Cent


theorem card_cent_le_of_powBoundN {k : GL24} {kR : Native.Rows} (rk : MRep kR k) (n : ℕ)
    {base : List ℕ} {conds : List (List Cond)} {cnts : List ℕ} {span : List (ℕ × ℕ)}
    {comb : List ℕ}
    (h : boundOK (colsOf (powList kR n)) n base conds cnts span comb = true) :
    Nat.card ↥(Subgroup.centralizer ({k} : Set GL24) ⊓ GA) ≤ cnts.prod := by
  have hr : List.Forall₂ MRep (powList kR n) ((List.range n).map fun a => k ^ a) := by
    unfold powList
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun a _ => ?_
    exact rk.pow a
  have hlen : (powList kR n).length = n := by simp [powList]
  have hcomm : ∀ g ∈ Subgroup.centralizer ({k} : Set GL24) ⊓ GA,
      ∀ β ∈ (List.range n).map (fun a => k ^ a), g * β = β * g := by
    intro g hg β hβ
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hβ
    have h0 := (Subgroup.mem_inf.1 hg).1
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 h0
    exact comm_pow_aux h1 a
  exact card_le_of_listBound hr inf_le_right hcomm hlen h

end Cent

end CFSG.HardMathSupport.Dickson.I271.TabCo1
