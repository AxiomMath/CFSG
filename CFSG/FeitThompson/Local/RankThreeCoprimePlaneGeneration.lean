module

public import CFSG.FeitThompson.Local.SubgroupIndicatorElementaryPlane
public import CFSG.FeitThompson.Local.WielandtFixedPointOrderSolvable
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {p : ℕ} {E V : Type*} [Group E] [Group V] {ρ : E →* MulAut V} {N : Subgroup V}

theorem fixedPoints_comp_bot_subtype (ρ : E →* MulAut V) :
    FixedPoints.subgroup (ρ.comp (⊥ : Subgroup E).subtype).range V = ⊤ := by
  ext v
  simp only [Subgroup.mem_top, iff_true]
  rw [mem_fixedPoints_comp_subtype_iff]
  intro b hb
  rw [Subgroup.mem_bot] at hb
  simp [hb]

theorem fixedPoints_comp_top_subtype (ρ : E →* MulAut V) :
    FixedPoints.subgroup (ρ.comp (⊤ : Subgroup E).subtype).range V
      = FixedPoints.subgroup ρ.range V := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype, MonoidHom.range_eq_map]

theorem fixedPoints_comp_subtype_mono (ρ : E →* MulAut V) {B₁ B₂ : Subgroup E} (h : B₁ ≤ B₂) :
    FixedPoints.subgroup (ρ.comp B₂.subtype).range V
      ≤ FixedPoints.subgroup (ρ.comp B₁.subtype).range V := by
  intro v hv
  rw [mem_fixedPoints_comp_subtype_iff] at hv ⊢
  exact fun b hb => hv b (h hb)

private theorem isInvariantSubgroup_of_forall_apply_mem (h : ∀ b : E, ∀ v ∈ N, ρ b v ∈ N) :
    IsInvariantSubgroup ρ N :=
  isInvariantSubgroup_iff_forall_map_eq.2 fun b => le_antisymm
    (by rintro x ⟨v, hv, rfl⟩; exact h b v hv)
    (fun v hv => ⟨ρ b⁻¹ v, h b⁻¹ v hv, by
      change ρ b (ρ b⁻¹ v) = v
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]⟩)

theorem isInvariantSubgroup_fixedPoints_comp_subtype [IsMulCommutative E] (ρ : E →* MulAut V)
    (B : Subgroup E) :
    IsInvariantSubgroup ρ (FixedPoints.subgroup (ρ.comp B.subtype).range V) := by
  refine isInvariantSubgroup_of_forall_apply_mem fun b v hv => ?_
  rw [mem_fixedPoints_comp_subtype_iff] at hv ⊢
  intro d hd
  have h1 : ρ d (ρ b v) = ρ (d * b) v := by rw [map_mul]; rfl
  rw [h1, IsMulCommutative.is_comm.comm d b, map_mul]
  change ρ b (ρ d v) = _
  rw [hv d hd]

theorem isInvariantSubgroup_iSup_fixedPoints [IsMulCommutative E] (ρ : E →* MulAut V)
    (S : Set (Subgroup E)) :
    IsInvariantSubgroup ρ
      (⨆ D ∈ S, FixedPoints.subgroup (ρ.comp (D : Subgroup E).subtype).range V) := by
  refine isInvariantSubgroup_iff_forall_map_eq.2 fun b => ?_
  rw [Subgroup.map_iSup]
  refine iSup_congr fun D => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun _ => (isInvariantSubgroup_fixedPoints_comp_subtype ρ D).map_eq b

theorem natCard_fixedPoints_restrictAut_comp_subtype_eq_natCard_inf
    (hN : IsInvariantSubgroup ρ N)
    (B : Subgroup E) :
    Nat.card (FixedPoints.subgroup (hN.restrictAut.comp B.subtype).range ↥N)
      = Nat.card (N ⊓ FixedPoints.subgroup (ρ.comp B.subtype).range V : Subgroup V) := by
  rw [← hN.restrictAut_comp B.subtype, ← Subgroup.card_subtype N _,
    (hN.comp B.subtype).map_subtype_fixedPoints_restrictAut,
    fixedPoints_range_comp_subtype, ← fixedPoints_range_comp_subtype]

private theorem natCard_comap_of_surjective {G H : Type*} [Group G] [Group H] [Finite G]
    {f : G →* H} (hf : Function.Surjective f) (B : Subgroup H) :
    Nat.card (B.comap f) = Nat.card B * Nat.card f.ker := by
  have hfin : Finite H := Finite.of_surjective f hf
  have hidx : B.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : Nat.card (B.comap f) * B.index = Nat.card G := by
    rw [← Subgroup.index_comap_of_surjective B hf]; exact Subgroup.card_mul_index _
  have h2 : Nat.card f.ker * Nat.card H = Nat.card G := by
    have h : f.ker.index = Nat.card H := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective f hf, Subgroup.card_top]
    rw [← h]; exact Subgroup.card_mul_index _
  have h3 : Nat.card B * B.index = Nat.card H := Subgroup.card_mul_index _
  refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hidx) ?_
  rw [h1, ← h2, ← h3]; ring

theorem natCard_subgroup_card_sq_mem [IsMulCommutative E] (hp : p.Prime) (hE : Nat.card E = p ^ 3)
    (hexp : ∀ x : E, x ^ p = 1) {a : E} (ha : a ≠ 1) :
    Nat.card {D : Subgroup E // Nat.card D = p ^ 2 ∧ a ∈ D} = p + 1 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by simp [hE, hp0])
  set Z : Subgroup E := Subgroup.zpowers a with hZdef
  have hZcard : Nat.card Z = p := by
    rw [hZdef, Nat.card_zpowers, orderOf_eq_of_pow_eq_one hp hexp ha]
  have hker : (QuotientGroup.mk' Z).ker = Z := QuotientGroup.ker_mk' Z
  have hsurj : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  have hQcard : Nat.card (E ⧸ Z) = p ^ 2 := by
    have h := Subgroup.card_mul_index Z
    rw [hZcard, Subgroup.index_eq_card, hE] at h
    have hp2 : p * Nat.card (E ⧸ Z) = p * p ^ 2 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) hp2
  have hQexp : ∀ x : E ⧸ Z, x ^ p = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H v => rw [← QuotientGroup.mk_pow, hexp v, QuotientGroup.mk_one]
  have haZ : (QuotientGroup.mk' Z) a = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_zpowers a
  rw [← card_subgroupsOfCard_of_card_eq_sq (A := E ⧸ Z) hp hQcard hQexp]
  refine Nat.card_congr (Equiv.symm ?_)
  refine
    { toFun := fun B => ⟨Subgroup.comap (QuotientGroup.mk' Z) B.1, ?_, ?_⟩
      invFun := fun D => ⟨Subgroup.map (QuotientGroup.mk' Z) D.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [natCard_comap_of_surjective hsurj, hker, hZcard, (mem_subgroupsOfCard.1 B.2)]; ring
  · rw [Subgroup.mem_comap, haZ]; exact one_mem _
  · rw [mem_subgroupsOfCard]
    have hZD : Z ≤ D.1 := Subgroup.zpowers_le.2 D.2.2
    have h1 : Subgroup.comap (QuotientGroup.mk' Z) (Subgroup.map (QuotientGroup.mk' Z) D.1) = D.1 :=
      Subgroup.comap_map_eq_self (by rw [hker]; exact hZD)
    have h2 := natCard_comap_of_surjective hsurj (Subgroup.map (QuotientGroup.mk' Z) D.1)
    rw [h1, hker, hZcard, D.2.1] at h2
    have h3 : p * p = Nat.card (Subgroup.map (QuotientGroup.mk' Z) D.1) * p := by rw [← h2]; ring
    exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hp0) h3).symm
  · intro B
    ext1
    exact Subgroup.map_comap_eq_self_of_surjective hsurj B.1
  · intro D
    ext1
    exact Subgroup.comap_map_eq_self (by rw [hker]; exact Subgroup.zpowers_le.2 D.2.2)

theorem card_subgroupsOfCard_sq_of_card_eq_cube [IsMulCommutative E] (hp : p.Prime)
    (hE : Nat.card E = p ^ 3) (hexp : ∀ x : E, x ^ p = 1) :
    Nat.card (subgroupsOfCard E (p ^ 2)) = p ^ 2 + p + 1 := by
  classical
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hq1 : 1 ≤ q := by omega
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by simp [hE, hp0])
  have := Fintype.ofFinite E
  have := Fintype.ofFinite (Subgroup E)
  set P : Finset (Subgroup E) := {D | Nat.card D = p ^ 2} with hP
  set T : Finset E := {a | a ≠ 1} with hT
  have hPcard : P.card = Nat.card (subgroupsOfCard E (p ^ 2)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext D
    simp [hP]
  have hTcard : T.card = p ^ 3 - 1 := by
    rw [hT, Finset.filter_ne' Finset.univ 1, Finset.card_erase_of_mem (Finset.mem_univ 1),
      Finset.card_univ, ← Nat.card_eq_fintype_card, hE]
  have hswap : ∑ D ∈ P, ∑ a ∈ T, (if a ∈ D then 1 else 0)
      = ∑ a ∈ T, ∑ D ∈ P, (if a ∈ D then 1 else 0) := Finset.sum_comm
  have hL : ∀ D ∈ P, (∑ a ∈ T, (if a ∈ D then 1 else 0)) = p ^ 2 - 1 := by
    intro D hD
    rw [← Finset.card_filter]
    have hDcard : Nat.card D = p ^ 2 := by simpa [hP] using hD
    have heq : {a ∈ T | a ∈ D} = (D : Set E).toFinset.erase 1 := by
      ext a
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        Set.mem_toFinset, SetLike.mem_coe, and_comm]
    have hcardD : (D : Set E).toFinset.card = p ^ 2 := by
      rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
      simpa using hDcard
    rw [heq, Finset.card_erase_of_mem (by simp), hcardD]
  have hR : ∀ a ∈ T, (∑ D ∈ P, (if a ∈ D then 1 else 0)) = p + 1 := by
    intro a ha
    have ha1 : a ≠ 1 := by simpa [hT] using ha
    rw [← Finset.card_filter, ← natCard_subgroup_card_sq_mem hp hE hexp ha1,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext D
    simp [hP]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, hTcard] at hswap
  have hA : p ^ 3 - 1 = q ^ 3 + 3 * q ^ 2 + 3 * q := Nat.sub_eq_of_eq_add (by rw [hq]; ring)
  have hB : p ^ 2 - 1 = q ^ 2 + 2 * q := Nat.sub_eq_of_eq_add (by rw [hq]; ring)
  rw [hA, hB] at hswap
  have hkey : P.card * (q ^ 2 + 2 * q) = (p ^ 2 + p + 1) * (q ^ 2 + 2 * q) := by
    rw [hswap, hq]; ring
  have hpos : 0 < q ^ 2 + 2 * q := by
    have : 0 < 2 * q := by omega
    omega
  rw [← hPcard]
  exact Nat.eq_of_mul_eq_mul_right hpos hkey

section Main

variable [IsMulCommutative E] [Finite V] [Group.IsSolvable V]

theorem natCard_mul_natCard_fixedPoints_pow_eq_finprod_of_card_eq_cube (hp : p.Prime)
    (hE : Nat.card E = p ^ 3)
    (hexp : ∀ x : E, x ^ p = 1) (ρ : E →* MulAut V) (hcop : p.Coprime (Nat.card V)) :
    Nat.card V * Nat.card (FixedPoints.subgroup ρ.range V) ^ (p * (p + 1))
      = ∏ᶠ D ∈ subgroupsOfCard E (p ^ 2),
          Nat.card (FixedPoints.subgroup (ρ.comp (D : Subgroup E).subtype).range V) := by
  classical
  have hcount1 := card_subgroupsOfCard_sq_of_card_eq_cube hp hE hexp
  have hcount2 := fun a (ha : a ≠ (1 : E)) => natCard_subgroup_card_sq_mem hp hE hexp ha
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp1 : 1 < p := hp.one_lt
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by simp [hE, hp0])
  have := Fintype.ofFinite E
  have := Fintype.ofFinite (Subgroup E)
  have hEsolv : Group.IsSolvable E :=
    Group.isSolvable_of_comm (fun a b => IsMulCommutative.is_comm.comm a b)
  have hcopE : (Nat.card E).Coprime (Nat.card V) := by rw [hE]; exact hcop.pow_left 3
  have hbt : (⊥ : Subgroup E) ≠ (⊤ : Subgroup E) := by
    intro h
    have hc : Nat.card (⊥ : Subgroup E) = Nat.card (⊤ : Subgroup E) := by rw [h]
    rw [Subgroup.card_bot, Subgroup.card_top, hE] at hc
    have : p ^ 1 ≤ p ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [pow_one] at this
    omega
  have htb : (⊤ : Subgroup E) ≠ (⊥ : Subgroup E) := hbt.symm
  set m : Subgroup E → ℕ := fun D => if D = ⊥ then p ^ 2 else if D = ⊤ then p + 1 else 0 with hm
  set n : Subgroup E → ℕ := fun D => if Nat.card D = p ^ 2 then 1 else 0 with hn
  have hmbot : m ⊥ = p ^ 2 := by rw [hm]; simp
  have hmtop : m ⊤ = p + 1 := by rw [hm]; simp only [if_neg htb, ite_true]
  have hpair : ∀ f : Subgroup E → ℕ, (∀ D, D ≠ ⊥ → D ≠ ⊤ → f D = 0) →
      ∑ D : Subgroup E, f D = f ⊥ + f ⊤ := by
    intro f hf
    rw [← Finset.sum_pair (f := f) hbt]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro D _ hD
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hD
    exact hf D hD.1 hD.2
  have hpairP : ∀ f : Subgroup E → ℕ, (∀ D, D ≠ ⊥ → D ≠ ⊤ → f D = 1) →
      ∏ D : Subgroup E, f D = f ⊥ * f ⊤ := by
    intro f hf
    rw [← Finset.prod_pair (f := f) hbt]
    refine (Finset.prod_subset (Finset.subset_univ _) ?_).symm
    intro D _ hD
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hD
    exact hf D hD.1 hD.2
  have hcover : ∀ a : E, ∑ D with a ∈ D, m D = ∑ D with a ∈ D, n D := by
    intro a
    rw [Finset.sum_filter, Finset.sum_filter]
    have hLHS := hpair (fun D => if a ∈ D then m D else 0) (by
      intro D h1 h2
      simp only [hm, if_neg h1, if_neg h2, ite_self])
    have hRHS : ∑ D : Subgroup E, (if a ∈ D then n D else 0)
        = Nat.card {D : Subgroup E // Nat.card D = p ^ 2 ∧ a ∈ D} := by
      have h : ∀ D : Subgroup E, (if a ∈ D then n D else 0)
          = (if (Nat.card D = p ^ 2 ∧ a ∈ D) then 1 else 0) := by
        intro D
        by_cases h1 : a ∈ D <;> by_cases h2 : Nat.card D = p ^ 2 <;>
          simp only [hn, h1, h2, if_true, if_false, and_true, and_false]
      rw [Finset.sum_congr rfl (fun D _ => h D), Finset.sum_boole, Nat.cast_id,
        Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hLHS, hRHS, hmbot, hmtop]
    by_cases ha : a = 1
    · subst ha
      rw [if_pos (one_mem _), if_pos (one_mem _)]
      have hc : Nat.card {D : Subgroup E // Nat.card D = p ^ 2 ∧ (1 : E) ∈ D} = p ^ 2 + p + 1 := by
        rw [← hcount1]
        exact Nat.card_congr
          { toFun := fun x => ⟨x.1, mem_subgroupsOfCard.2 x.2.1⟩
            invFun := fun x => ⟨x.1, mem_subgroupsOfCard.1 x.2, one_mem _⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      rw [hc, add_assoc]
    · rw [if_neg (by simpa [Subgroup.mem_bot] using ha), if_pos (Subgroup.mem_top a),
        hcount2 a ha, zero_add]
  have key := prod_natCard_fixedPoints_comp_subtype_pow_eq ρ hcopE (fun D : Subgroup E => D) m n
    hcover
  rw [hpairP _ (by
    intro D h1 h2
    simp only [hm, if_neg h1, if_neg h2, zero_mul, pow_zero])] at key
  rw [hmbot, hmtop, fixedPoints_comp_bot_subtype, fixedPoints_comp_top_subtype, Subgroup.card_bot,
    Subgroup.card_top, Subgroup.card_top, hE, mul_one] at key
  have hRHS : ∏ D : Subgroup E,
      Nat.card (FixedPoints.subgroup (ρ.comp (D : Subgroup E).subtype).range V) ^
        (n D * Nat.card D)
      = (∏ᶠ D ∈ subgroupsOfCard E (p ^ 2),
          Nat.card (FixedPoints.subgroup (ρ.comp (D : Subgroup E).subtype).range V)) ^ p ^ 2 := by
    have hset : (subgroupsOfCard E (p ^ 2) : Set (Subgroup E))
        = ↑({D : Subgroup E | Nat.card D = p ^ 2} : Finset (Subgroup E)) := by
      ext D
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        mem_subgroupsOfCard]
    rw [hset, finprod_mem_coe_finset, ← Finset.prod_pow, Finset.prod_filter]
    refine Finset.prod_congr rfl fun D _ => ?_
    by_cases hD : Nat.card D = p ^ 2
    · rw [if_pos hD]
      simp only [hn, if_pos hD, one_mul, hD]
    · rw [if_neg hD]
      simp only [hn, if_neg hD, zero_mul, pow_zero]
  rw [hRHS] at key
  refine Nat.pow_left_injective (n := p ^ 2) (by positivity) ?_
  simp only
  rw [mul_pow, ← pow_mul, ← key]
  congr 1
  ring

theorem iSup_fixedPoints_subgroupsOfCard_eq_top (hp : p.Prime) (hE : Nat.card E = p ^ 3)
    (hexp : ∀ x : E, x ^ p = 1) (ρ : E →* MulAut V) (hcop : p.Coprime (Nat.card V)) :
    (⨆ D ∈ subgroupsOfCard E (p ^ 2),
        FixedPoints.subgroup (ρ.comp (D : Subgroup E).subtype).range V) = ⊤ := by
  classical
  have hp0 : p ≠ 0 := hp.ne_zero
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by simp [hE, hp0])
  set J : Subgroup V := ⨆ D ∈ subgroupsOfCard E (p ^ 2),
    FixedPoints.subgroup (ρ.comp (D : Subgroup E).subtype).range V
  have hJinv : IsInvariantSubgroup ρ J := isInvariantSubgroup_iSup_fixedPoints ρ _
  have hle : ∀ D ∈ subgroupsOfCard E (p ^ 2),
      FixedPoints.subgroup (ρ.comp (D : Subgroup E).subtype).range V ≤ J := fun D hD =>
    le_biSup (fun D : Subgroup E =>
      FixedPoints.subgroup (ρ.comp (D : Subgroup E).subtype).range V) hD
  obtain ⟨D₀, hD₀⟩ : (subgroupsOfCard E (p ^ 2)).Nonempty := by
    have hpos : 0 < Nat.card (subgroupsOfCard E (p ^ 2)) := by
      rw [card_subgroupsOfCard_sq_of_card_eq_cube hp hE hexp]; positivity
    rw [Nat.card_pos_iff] at hpos
    obtain ⟨⟨D, hD⟩⟩ := hpos.1
    exact ⟨D, hD⟩
  have hCE : FixedPoints.subgroup ρ.range V ≤ J := by
    refine le_trans ?_ (hle D₀ hD₀)
    rw [← fixedPoints_comp_top_subtype]
    exact fixedPoints_comp_subtype_mono ρ le_top
  have hcopJ : p.Coprime (Nat.card J) :=
    hcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card J)
  have hV := natCard_mul_natCard_fixedPoints_pow_eq_finprod_of_card_eq_cube hp hE hexp ρ hcop
  have hJid := natCard_mul_natCard_fixedPoints_pow_eq_finprod_of_card_eq_cube hp hE hexp
    hJinv.restrictAut hcopJ
  have hfixD : ∀ D ∈ subgroupsOfCard E (p ^ 2),
      Nat.card (FixedPoints.subgroup (hJinv.restrictAut.comp (D : Subgroup E).subtype).range ↥J)
        = Nat.card (FixedPoints.subgroup (ρ.comp (D : Subgroup E).subtype).range V) := by
    intro D hD
    rw [natCard_fixedPoints_restrictAut_comp_subtype_eq_natCard_inf hJinv D,
      inf_eq_right.2 (hle D hD)]
  have hfixE : Nat.card (FixedPoints.subgroup hJinv.restrictAut.range ↥J)
      = Nat.card (FixedPoints.subgroup ρ.range V) := by
    rw [← fixedPoints_comp_top_subtype hJinv.restrictAut,
      natCard_fixedPoints_restrictAut_comp_subtype_eq_natCard_inf hJinv ⊤,
      fixedPoints_comp_top_subtype,
      inf_eq_right.2 hCE]
  rw [hfixE, finprod_mem_congr rfl hfixD, ← hV] at hJid
  have hposC : 0 < Nat.card (FixedPoints.subgroup ρ.range V) ^ (p * (p + 1)) := by
    have : 0 < Nat.card (FixedPoints.subgroup ρ.range V) := Nat.card_pos
    positivity
  have hcard : Nat.card ↥J = Nat.card V := Nat.eq_of_mul_eq_mul_right hposC hJid
  exact J.eq_top_of_card_eq hcard

end Main

section Iso

variable [Finite V] [Group.IsSolvable V]

private theorem isMulCommutative_of_mulEquiv (e : E ≃* Multiplicative (Fin 3 → ZMod p)) :
    IsMulCommutative E :=
  ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩

private theorem natCard_eq_cube_of_mulEquiv (e : E ≃* Multiplicative (Fin 3 → ZMod p)) :
    Nat.card E = p ^ 3 := by
  rw [Nat.card_congr e.toEquiv, natCard_multiplicative_pi_zmod]

private theorem pow_eq_one_of_mulEquiv_cube (hp : p.Prime)
    (e : E ≃* Multiplicative (Fin 3 → ZMod p)) (x : E) : x ^ p = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine e.injective ?_
  rw [map_pow, map_one]
  refine Multiplicative.toAdd.injective ?_
  simp only [toAdd_pow, toAdd_one]
  funext i
  simp

theorem natCard_mul_natCard_fixedPoints_pow_eq_finprod_of_mulEquiv_cube (hp : p.Prime)
    (e : E ≃* Multiplicative (Fin 3 → ZMod p)) (ρ : E →* MulAut V)
    (hcop : p.Coprime (Nat.card V)) :
    Nat.card V * Nat.card (FixedPoints.subgroup ρ.range V) ^ (p * (p + 1))
      = ∏ᶠ D ∈ subgroupsOfCard E (p ^ 2),
          Nat.card (FixedPoints.subgroup (ρ.comp (D : Subgroup E).subtype).range V) :=
  letI := isMulCommutative_of_mulEquiv e
  natCard_mul_natCard_fixedPoints_pow_eq_finprod_of_card_eq_cube hp
    (natCard_eq_cube_of_mulEquiv e) (pow_eq_one_of_mulEquiv_cube hp e) ρ hcop

theorem iSup_fixedPoints_subgroupsOfCard_eq_top_of_mulEquiv (hp : p.Prime)
    (e : E ≃* Multiplicative (Fin 3 → ZMod p)) (ρ : E →* MulAut V)
    (hcop : p.Coprime (Nat.card V)) :
    (⨆ D ∈ subgroupsOfCard E (p ^ 2),
        FixedPoints.subgroup (ρ.comp (D : Subgroup E).subtype).range V) = ⊤ :=
  letI := isMulCommutative_of_mulEquiv e
  iSup_fixedPoints_subgroupsOfCard_eq_top hp (natCard_eq_cube_of_mulEquiv e)
    (pow_eq_one_of_mulEquiv_cube hp e) ρ hcop

end Iso

end CFSG.FeitThompson
