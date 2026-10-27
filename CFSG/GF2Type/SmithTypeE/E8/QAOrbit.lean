module

public import CFSG.GF2Type.SmithTypeE.E8.ModPairs
public import CFSG.GF2Type.SmithTypeE.E8.FactsForm
public import CFSG.GF2Type.SmithTypeE.E8.IdMod

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.GF2Type.SmithTypeE.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.SmithE8M
open CFSG.SeitzReduction.EPilot (pinnedElt)

@[expose] def SbSet (b : Fin e7Data.d) : Finset (Fin e7Data.d) :=
  Finset.univ.filter fun c => c = ⟨0, by decide⟩ ∨ ∃ i : Fin 126,
    e7Data.wt 0 ⬝ᵥ e8mRoot i = 1 ∧ e7Data.wt b ⬝ᵥ e8mRoot i = -1 ∧
      e7Data.wt c = e7Data.wt b + MinData.toWeight (e8mRoot i)

set_option maxRecDepth 20000 in
theorem sb_closed : ∀ i j : Fin 126, e7Data.wt 0 ⬝ᵥ e8mRoot i = 1 → e7Data.wt 0 ⬝ᵥ e8mRoot j = 1 →
    ∀ b : Fin e7Data.d, wgrade b = -1 → e7Data.wt b ⬝ᵥ e8mRoot i = -1 →
      (e7Data.wt b + MinData.toWeight (e8mRoot i)) ⬝ᵥ e8mRoot j = -1 →
        e7Data.wt b + MinData.toWeight (e8mRoot i) + MinData.toWeight (e8mRoot j) =
          e7Data.wt 0 := by
  decide +kernel

section Group

theorem card_SbSet {b : Fin e7Data.d} (hb : wgrade b = -1) : (SbSet b).card ≤ 11 := by
  have hsub : SbSet b ⊆ insert ⟨0, by decide⟩ ((Finset.univ.filter fun k : Fin 126 =>
      e7Data.wt 0 ⬝ᵥ e8mRoot k = 1 ∧ e7Data.wt b ⬝ᵥ e8mRoot k = -1).image
        fun k : Fin 126 => e7Shift (e8mRoot k) b) := by
    intro c hc
    rw [SbSet, Finset.mem_filter] at hc
    rcases hc.2 with h | ⟨i, hi1, hi2, hi3⟩
    · exact Finset.mem_insert.2 (Or.inl h)
    · refine Finset.mem_insert.2 (Or.inr (Finset.mem_image.2 ⟨i, ?_, ?_⟩))
      · exact Finset.mem_filter.2 ⟨Finset.mem_univ i, hi1, hi2⟩
      · exact wt_e7Shift hi3
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le (⟨0, by decide⟩ : Fin e7Data.d) ((Finset.univ.filter fun k : Fin 126 =>
      e7Data.wt 0 ⬝ᵥ e8mRoot k = 1 ∧ e7Data.wt b ⬝ᵥ e8mRoot k = -1).image
        fun k : Fin 126 => e7Shift (e8mRoot k) b)
  have h3 := Finset.card_image_le (s := Finset.univ.filter fun k : Fin 126 =>
      e7Data.wt 0 ⬝ᵥ e8mRoot k = 1 ∧ e7Data.wt b ⬝ᵥ e8mRoot k = -1) (f := fun k : Fin 126 => e7Shift (e8mRoot k) b)
  have h4 := m1_counts b
  rw [hb] at h4
  have h5 : M1n (-1) = 10 := by decide
  rw [h5] at h4
  omega

@[expose] noncomputable def Ysp (b : Fin e7Data.d) :
    Submodule (ZMod 2) (Fin e7Data.d →₀ ZMod 2) :=
  Finsupp.supported (ZMod 2) (ZMod 2) (↑(insert b (SbSet b)) : Set (Fin e7Data.d))

@[expose] noncomputable def Ysp' (b : Fin e7Data.d) :
    Submodule (ZMod 2) (Fin e7Data.d →₀ ZMod 2) :=
  Finsupp.supported (ZMod 2) (ZMod 2) (↑(SbSet b) : Set (Fin e7Data.d))

theorem Ysp'_le (b : Fin e7Data.d) : Ysp' b ≤ Ysp b :=
  Finsupp.supported_mono (by simp)

theorem finrank_supported_finset (S : Finset (Fin e7Data.d)) :
    Module.finrank (ZMod 2) (Finsupp.supported (ZMod 2) (ZMod 2) (↑S : Set (Fin e7Data.d))) =
      S.card := by
  rw [(Finsupp.supportedEquivFinsupp (M := ZMod 2) (R := ZMod 2)
    (↑S : Set (Fin e7Data.d))).finrank_eq, Module.finrank_finsupp_self]
  simp

@[expose] def Good (Y Y' : Submodule (ZMod 2) (Fin e7Data.d →₀ ZMod 2))
    (q : ↥(adjointGroup .E7 (ZMod 2))) : Prop :=
  ∀ y ∈ Y, e7Rep56 (ZMod 2) q y - y ∈ Y'

theorem Good.mul {Y Y' : Submodule (ZMod 2) (Fin e7Data.d →₀ ZMod 2)} (hle : Y' ≤ Y)
    {q q' : ↥(adjointGroup .E7 (ZMod 2))} (hq : Good Y Y' q) (hq' : Good Y Y' q') :
    Good Y Y' (q * q') := by
  intro y hy
  have h1 := hq' y hy
  have h2 := hq y hy
  have h3 := hq _ (hle h1)
  have e : e7Rep56 (ZMod 2) (q * q') y - y =
      e7Rep56 (ZMod 2) q (e7Rep56 (ZMod 2) q' y - y) + (e7Rep56 (ZMod 2) q y - y) := by
    rw [F.rep_mul_apply, map_sub]
    abel
  rw [e]
  refine Y'.add_mem ?_ h2
  have e2 : e7Rep56 (ZMod 2) q (e7Rep56 (ZMod 2) q' y - y) =
      (e7Rep56 (ZMod 2) q (e7Rep56 (ZMod 2) q' y - y) - (e7Rep56 (ZMod 2) q' y - y)) +
        (e7Rep56 (ZMod 2) q' y - y) := by abel
  rw [e2]
  exact Y'.add_mem h3 h1

@[expose] def goodGroup (Y Y' : Submodule (ZMod 2) (Fin e7Data.d →₀ ZMod 2)) (hle : Y' ≤ Y) :
    Subgroup ↥(adjointGroup .E7 (ZMod 2)) where
  carrier := {q | Good Y Y' q ∧ Good Y Y' q⁻¹}
  mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hle hb.1, by
    rw [mul_inv_rev]
    exact hb.2.mul hle ha.2⟩
  one_mem' := ⟨fun y _ => by
      rw [F.rep_one_apply, sub_self]
      exact Y'.zero_mem,
    fun y _ => by
      rw [inv_one, F.rep_one_apply, sub_self]
      exact Y'.zero_mem⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by
    rw [inv_inv]
    exact ha.1⟩

theorem shift_mem_SbSet {b : Fin e7Data.d} (hb : wgrade b = -1)
    {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (hRA : e7Data.wt 0 ⬝ᵥ β = 1)
    {c : Fin e7Data.d} (hc : c ∈ insert b (SbSet b)) (hcb : e7Data.wt c ⬝ᵥ β = -1) :
    e7Shift β c ∈ SbSet b := by
  obtain ⟨j, hj, hjβ⟩ := exists_e8mRoot_eq hβ
  have hsh : e7Data.wt (e7Shift β c) = e7Data.wt c + MinData.toWeight β :=
    wt_e7Shift_of_dotProduct hβ hcb
  rw [SbSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases Finset.mem_insert.1 hc with rfl | hcS
  · right
    refine ⟨⟨j, hj⟩, ?_, ?_, ?_⟩
    · show e7Data.wt 0 ⬝ᵥ e8mRoot j = 1
      rw [hjβ]
      exact hRA
    · show e7Data.wt c ⬝ᵥ e8mRoot j = -1
      rw [hjβ]
      exact hcb
    · show e7Data.wt (e7Shift β c) = e7Data.wt c + MinData.toWeight (e8mRoot j)
      rw [hjβ]
      exact hsh
  · rw [SbSet, Finset.mem_filter] at hcS
    rcases hcS.2 with h0 | ⟨i, hi1, hi2, hi3⟩
    · exfalso
      subst h0
      have h1 : e7Data.wt 0 ⬝ᵥ β = -1 := hcb
      omega
    · left
      have hj1 : e7Data.wt 0 ⬝ᵥ e8mRoot j = 1 := by
        rw [hjβ]
        exact hRA
      have h := sb_closed i ⟨j, hj⟩ hi1 hj1 b hb hi2 (by
        rw [← hi3]
        show e7Data.wt c ⬝ᵥ e8mRoot j = -1
        rw [hjβ]
        exact hcb)
      refine e7Data_valid.wt_injective ?_
      show e7Data.wt (e7Shift β c) = e7Data.wt 0
      rw [hsh, hi3, ← hjβ]
      exact h

theorem good_pinnedElt {b : Fin e7Data.d} (hb : wgrade b = -1)
    {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (hRA : e7Data.wt 0 ⬝ᵥ β = 1) :
    Good (Ysp b) (Ysp' b) (pinnedElt .E7 β 1) := by
  have hY : Ysp b ≤ (Ysp' b).comap (e7Rep56 (ZMod 2) (pinnedElt .E7 β 1) - 1) := by
    rw [Ysp, Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    show (e7Rep56 (ZMod 2) (pinnedElt .E7 β 1) - 1) (Finsupp.single c 1) ∈ Ysp' b
    rw [LinearMap.sub_apply, Module.End.one_apply, e7Rep56_pinnedElt_single hβ,
      add_sub_cancel_left]
    by_cases hcb : e7Data.wt c ⬝ᵥ β = -1
    · rw [if_pos hcb]
      exact Finsupp.single_mem_supported (ZMod 2) _ (Finset.mem_coe.2
        (shift_mem_SbSet hb hβ hRA (Finset.mem_coe.1 hc) hcb))
    · rw [if_neg hcb]
      exact Submodule.zero_mem _
  intro y hy
  exact hY hy

theorem QA_good {b : Fin e7Data.d} (hb : wgrade b = -1) {q : ↥(adjointGroup .E7 (ZMod 2))}
    (hq : (q : ModGL .E7 (ZMod 2)) ∈ QA) : Good (Ysp b) (Ysp' b) q := by
  have hW : QA ≤ (goodGroup (Ysp b) (Ysp' b) (Ysp'_le b)).map
      (adjointGroup .E7 (ZMod 2)).subtype := by
    refine iSup₂_le fun β hβ => ?_
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    obtain ⟨hroot, h1⟩ := mem_RA_wt hβ
    have hc : c = 0 ∨ c = 1 := by
      revert c
      decide
    rcases hc with rfl | rfl
    · rw [CFSG.Blueprint.Chevalley.pinnedX_zero]
      exact one_mem _
    · have hgood := good_pinnedElt hb hroot h1
      have hinv : (pinnedElt .E7 β (1 : ZMod 2))⁻¹ = pinnedElt .E7 β 1 :=
        inv_eq_of_mul_eq_one_right (F.pinnedElt_mul_self β)
      refine ⟨pinnedElt .E7 β 1, ⟨hgood, ?_⟩, rfl⟩
      rw [hinv]
      exact hgood
  obtain ⟨g, hg, hgq⟩ := hW hq
  have : g = q := Subtype.ext hgq
  subst this
  exact hg.1

theorem single_mem_Ysp (b : Fin e7Data.d) : (Finsupp.single b 1 : Fin e7Data.d →₀ ZMod 2) ∈ Ysp b :=
  Finsupp.single_mem_supported (ZMod 2) _ (Finset.mem_coe.2 (Finset.mem_insert_self _ _))

theorem card_orbit_basis_le {b : Fin e7Data.d} (hb : wgrade b = -1) :
    Nat.card (Set.range fun q : ↥QAg =>
      e7Rep56 (ZMod 2) (q : ↥(adjointGroup .E7 (ZMod 2))) (Finsupp.single b 1)) ≤ 2 ^ 11 := by
  have hsub : (Set.range fun q : ↥QAg =>
      e7Rep56 (ZMod 2) (q : ↥(adjointGroup .E7 (ZMod 2))) (Finsupp.single b 1)) ⊆
      (fun y => (Finsupp.single b 1 : Fin e7Data.d →₀ ZMod 2) + y) '' (Ysp' b : Set _) := by
    rintro _ ⟨q, rfl⟩
    refine ⟨e7Rep56 (ZMod 2) (q : ↥(adjointGroup .E7 (ZMod 2))) (Finsupp.single b 1) -
      Finsupp.single b 1, QA_good hb q.2 _ (single_mem_Ysp b), ?_⟩
    simp only
    abel
  have hfin : (Ysp' b : Set (Fin e7Data.d →₀ ZMod 2)).Finite := Set.toFinite _
  calc Nat.card (Set.range fun q : ↥QAg =>
        e7Rep56 (ZMod 2) (q : ↥(adjointGroup .E7 (ZMod 2))) (Finsupp.single b 1))
      = (Set.range fun q : ↥QAg =>
        e7Rep56 (ZMod 2) (q : ↥(adjointGroup .E7 (ZMod 2))) (Finsupp.single b 1)).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ ((fun y => (Finsupp.single b 1 : Fin e7Data.d →₀ ZMod 2) + y) ''
          (Ysp' b : Set (Fin e7Data.d →₀ ZMod 2))).ncard := Set.ncard_le_ncard hsub (hfin.image _)
    _ ≤ (Ysp' b : Set (Fin e7Data.d →₀ ZMod 2)).ncard := Set.ncard_image_le hfin
    _ = Nat.card (Ysp' b) := (Nat.card_coe_set_eq _).symm
    _ = 2 ^ Module.finrank (ZMod 2) (Ysp' b) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Ysp' b), Nat.card_zmod]
    _ ≤ 2 ^ 11 := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        rw [Ysp', finrank_supported_finset]
        exact card_SbSet hb

theorem card_orbit_le {w : Fin e7Data.d →₀ ZMod 2} (hw : w ∈ weightVec) (hw0 : w ∉ W0)
    (hf : F.ff e7Y56 w = 0) :
    Nat.card (Set.range fun q : ↥QAg =>
      e7Rep56 (ZMod 2) (q : ↥(adjointGroup .E7 (ZMod 2))) w) ≤ 2 ^ 11 := by
  obtain ⟨g₁, hg₁⟩ := hw
  obtain ⟨g, b, hg1, hg2⟩ := pair_normal_form_weights (w := e7Y56) (w' := w)
    ⟨1, (F.rep_one_apply e7Y56).symm⟩ ⟨g₁, hg₁.symm⟩
  have hgs : e7Rep56 (ZMod 2) g e7Y56 = e7Y56 := hg1.symm
  have hb_not_W0 : ¬ ((Finsupp.single b 1 : Fin e7Data.d →₀ ZMod 2) ∈ W0) := by
    intro h
    apply hw0
    rw [hg2]
    exact e7Rep56_mem_W0 hgs h
  have hb_le : wgrade b ≤ 0 := by
    by_contra hpos
    push Not at hpos
    refine hb_not_W0 ((mem_W0 _).2 fun c hc => ?_)
    have hcb : c ≠ b := fun h => by
      subst h
      omega
    simp [Finsupp.single_apply, Ne.symm hcb]
  have hff : F.ff e7Y56 (Finsupp.single b 1) = 0 := by
    have h1 := F.ff_rep g e7Y56 (Finsupp.single b 1)
    rw [hgs, ← hg2, hf] at h1
    exact h1.symm
  have hb_opp : b ≠ F.opI ⟨0, by decide⟩ := by
    intro h
    have h2 := F.ff_single_single ⟨0, by decide⟩ b
    rw [if_pos h] at h2
    rw [F.single_e7Y56] at hff
    rw [hff] at h2
    exact absurd h2 (by decide)
  have hb : wgrade b = -1 := by
    rcases w0_wgrade_cases b with h | h | h | h
    · omega
    · omega
    · exact h
    · exact absurd (F.grade_neg_three_eq_opI h) hb_opp
  have hgP : (g : ModGL .E7 (ZMod 2)) ∈ parabolicSubgroup .E7 (ZMod 2) {i | i ≠ e7n6} :=
    (e7Rep56_e7Y56_eq_iff g).1 hgs
  have hN : (g : ModGL .E7 (ZMod 2)) ∈ Subgroup.normalizer (QA : Set (ModGL .E7 (ZMod 2))) := by
    have := adjointGroup_inf_normalizer_parabolicRadical (τ := .E7) (K := ZMod 2)
      {i | i ≠ e7n6}
    rw [← this] at hgP
    exact hgP.2
  have hsub : (Set.range fun q : ↥QAg =>
      e7Rep56 (ZMod 2) (q : ↥(adjointGroup .E7 (ZMod 2))) w) ⊆
      (e7Rep56 (ZMod 2) g) '' (Set.range fun q : ↥QAg =>
        e7Rep56 (ZMod 2) (q : ↥(adjointGroup .E7 (ZMod 2))) (Finsupp.single b 1)) := by
    rintro _ ⟨q, rfl⟩
    have hq : ((q : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) ∈ QA := q.2
    have hq' : ((g⁻¹ * (q : ↥(adjointGroup .E7 (ZMod 2))) * g : ↥(adjointGroup .E7 (ZMod 2))) :
        ModGL .E7 (ZMod 2)) ∈ QA := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hN)
        ((q : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2))).1 hq
      simpa using h1
    refine ⟨_, ⟨⟨g⁻¹ * (q : ↥(adjointGroup .E7 (ZMod 2))) * g, hq'⟩, rfl⟩, ?_⟩
    show e7Rep56 (ZMod 2) g (e7Rep56 (ZMod 2) (g⁻¹ * (q : ↥(adjointGroup .E7 (ZMod 2))) * g)
      (Finsupp.single b 1)) = e7Rep56 (ZMod 2) (q : ↥(adjointGroup .E7 (ZMod 2))) w
    rw [← F.rep_mul_apply, hg2, ← F.rep_mul_apply]
    congr 1
    group
  have hfin : (Set.range fun q : ↥QAg =>
      e7Rep56 (ZMod 2) (q : ↥(adjointGroup .E7 (ZMod 2))) (Finsupp.single b 1)).Finite :=
    Set.toFinite _
  calc Nat.card (Set.range fun q : ↥QAg =>
        e7Rep56 (ZMod 2) (q : ↥(adjointGroup .E7 (ZMod 2))) w)
      = (Set.range fun q : ↥QAg =>
        e7Rep56 (ZMod 2) (q : ↥(adjointGroup .E7 (ZMod 2))) w).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ ((e7Rep56 (ZMod 2) g) '' (Set.range fun q : ↥QAg =>
        e7Rep56 (ZMod 2) (q : ↥(adjointGroup .E7 (ZMod 2))) (Finsupp.single b 1))).ncard :=
        Set.ncard_le_ncard hsub (hfin.image _)
    _ ≤ (Set.range fun q : ↥QAg =>
        e7Rep56 (ZMod 2) (q : ↥(adjointGroup .E7 (ZMod 2))) (Finsupp.single b 1)).ncard :=
        Set.ncard_image_le hfin
    _ = Nat.card (Set.range fun q : ↥QAg =>
        e7Rep56 (ZMod 2) (q : ↥(adjointGroup .E7 (ZMod 2))) (Finsupp.single b 1)) :=
        (Nat.card_coe_set_eq _).symm
    _ ≤ 2 ^ 11 := card_orbit_basis_le hb

end Group

end CFSG.GF2Type.SmithTypeE.E8
