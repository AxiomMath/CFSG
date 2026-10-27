module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Rep
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.GF2Type.SmithTypeE.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.Quasithin.SmithCurtis.Chev CFSG.SeitzReduction CFSG.SeitzReduction.EPilot


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem e7Psi_pinnedElt {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (c : K) :
    e7Psi K (pinnedElt .E7 β c) = e7Data_valid.xm K β c :=
  (e7Equiv (K := K)).symm_apply_eq.2
    (Subtype.ext (CFSG.SeitzReduction.E8Pilot.coe_e7Isogeny_xm hβ c).symm)

theorem e7Rep56_pinnedElt {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (c : K) :
    e7Rep56 K (pinnedElt .E7 β c) = 1 + c • e7Data.rootOp K β := by
  rw [e7Rep56, pullRep_apply, e7Psi_pinnedElt hβ, minRep_xm]

theorem e7Rep56_pinnedElt_apply {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (c : K)
    (v : Fin e7Data.d →₀ K) : e7Rep56 K (pinnedElt .E7 β c) v = v + c • e7Data.rootOp K β v := by
  rw [e7Rep56_pinnedElt hβ]
  simp

theorem cartan_e7_symm : ∀ i j : Fin 7, (Tag.E7).cartan i j = (Tag.E7).cartan j i := by
  intro i j
  simp only [Tag.cartan, Tag.cartanE]
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 20000 in
theorem rootOp_single_cases {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (a : Fin e7Data.d) :
    (e7Data.wt a ⬝ᵥ β ≠ -1 ∧ e7Data.rootOp K β (Finsupp.single a 1) = 0) ∨
    (e7Data.wt a ⬝ᵥ β = -1 ∧ ∃ b : Fin e7Data.d,
      e7Data.wt b = e7Data.wt a + MinData.toWeight β ∧
        e7Data.rootOp K β (Finsupp.single a 1) = Finsupp.single b 1) := by
  by_cases h : e7Data.wt a ⬝ᵥ β = -1
  · right
    refine ⟨h, ?_⟩
    have hne : e7Data.rootOp K β (Finsupp.single a 1) ≠ 0 :=
      (e7Data_valid.rootOp_single_ne_zero_iff cartan_e7_symm hβ a).2 h
    rcases e7Data_valid.isSignedMap_rootOp (R := K) hβ a with h0 | ⟨b, hb, hs⟩
    · exact absurd h0 hne
    · refine ⟨b, hb, ?_⟩
      rcases hs with hs | hs
      · exact hs
      · rw [hs, ← Finsupp.single_neg, CharTwo.neg_eq]
  · left
    refine ⟨h, ?_⟩
    by_contra hne
    exact h ((e7Data_valid.rootOp_single_ne_zero_iff cartan_e7_symm hβ a).1 hne)

open Classical in
@[expose] def e7Shift (β : Fin (Tag.rank .E7) → ℤ) (a : Fin e7Data.d) : Fin e7Data.d :=
  if h : ∃ b : Fin e7Data.d, e7Data.wt b = e7Data.wt a + MinData.toWeight β then h.choose else a

theorem wt_e7Shift {β : Fin (Tag.rank .E7) → ℤ} {a b : Fin e7Data.d}
    (hb : e7Data.wt b = e7Data.wt a + MinData.toWeight β) :
    e7Shift β a = b := by
  classical
  have h : ∃ b : Fin e7Data.d, e7Data.wt b = e7Data.wt a + MinData.toWeight β := ⟨b, hb⟩
  rw [e7Shift, dif_pos h]
  exact e7Data_valid.wt_injective (h.choose_spec.trans hb.symm)

theorem exists_wt_eq_of_dotProduct {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    {a : Fin e7Data.d} (h : e7Data.wt a ⬝ᵥ β = -1) :
    ∃ b : Fin e7Data.d, e7Data.wt b = e7Data.wt a + MinData.toWeight β := by
  rcases rootOp_single_cases (K := ZMod 2) hβ a with ⟨h1, -⟩ | ⟨-, b, hb, -⟩
  · exact absurd h h1
  · exact ⟨b, hb⟩

theorem wt_e7Shift_of_dotProduct {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    {a : Fin e7Data.d} (h : e7Data.wt a ⬝ᵥ β = -1) :
    e7Data.wt (e7Shift β a) = e7Data.wt a + MinData.toWeight β := by
  obtain ⟨b, hb⟩ := exists_wt_eq_of_dotProduct hβ h
  rw [wt_e7Shift hb]
  exact hb

theorem e7Rep56_pinnedElt_single {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (a : Fin e7Data.d) :
    e7Rep56 K (pinnedElt .E7 β 1) (Finsupp.single a 1) =
      Finsupp.single a 1 +
        if e7Data.wt a ⬝ᵥ β = -1 then Finsupp.single (e7Shift β a) 1 else 0 := by
  rw [e7Rep56_pinnedElt_apply hβ, one_smul]
  rcases rootOp_single_cases (K := K) hβ a with ⟨h1, h2⟩ | ⟨h1, b, hb, h2⟩
  · rw [h2, if_neg h1, add_zero]
  · rw [h2, if_pos h1, wt_e7Shift hb]

theorem e7Rep56_nC_single (i : Fin (Tag.rank .E7)) (a : Fin e7Data.d) :
    e7Rep56 K (nC .E7 K i) (Finsupp.single a 1) = Finsupp.single (e7Data_valid.sRefl i a) 1 := by
  rw [e7Rep56, pullRep_apply, e7Psi_nC, minRep_nm_single]
  split_ifs
  · rw [← Finsupp.single_neg, CharTwo.neg_eq]
  · rfl

theorem e7Rep56_prod_nC_single (l : List (Fin (Tag.rank .E7))) (a : Fin e7Data.d) :
    e7Rep56 K ((l.map (nC .E7 K)).prod) (Finsupp.single a 1) =
      Finsupp.single (l.foldr (fun i b => e7Data_valid.sRefl i b) a) 1 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, List.foldr_cons]
    rw [ih, e7Rep56_nC_single]

theorem e7Rep56_nWC_single (w : WeylGroup .E7) (a : Fin e7Data.d) :
    ∃ b : Fin e7Data.d, e7Rep56 K (nWC .E7 K w) (Finsupp.single a 1) = Finsupp.single b 1 := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem .E7).exists_reduced_word w
  refine ⟨ω.foldr (fun i b => e7Data_valid.sRefl i b) a, ?_⟩
  have h : nWC .E7 K ((coxeterSystem .E7).wordProd ω) = (ω.map (nC .E7 K)).prod := by
    refine Subtype.ext ?_
    rw [show ((nWC .E7 K ((coxeterSystem .E7).wordProd ω) : adjointGroup .E7 K) : ModGL .E7 K) =
      canonicalRep (coxeterSystem .E7) K ((coxeterSystem .E7).wordProd ω) from rfl,
      canonicalRep_wordProd hω, Subgroup.val_list_prod, List.map_map]
    rfl
  rw [h, e7Rep56_prod_nC_single]

end CFSG.GF2Type.SmithTypeE.E8
