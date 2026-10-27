module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015U6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015FourU6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015Four
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsGamma

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.CatB.I1015

section Holds


theorem i1015fourU62At_holds (G : Type) [Group G] [Finite G] : I1015fourU62At G := by
  intro X K hK hcat
  have hGA : GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  obtain ⟨E, T, hEK, hEe, hEc, hTK, hT2, hTn, hEN⟩ := u6_exists_E_T hGA (n := 1) odd_one hK hcat
  exact ⟨E, T, hEK, hEe, by rw [hEc]; norm_num, hTK, hT2, hTn, hEN⟩

theorem i1015fourAt_holds (G : Type) [Group G] [Finite G] : I1015fourAt G := by
  intro K hK hcat
  have hGA : GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases hi with h5 | h6 | h8 | hD
  · exact four_noThree_types hGA hK (Or.inl ⟨i, h5, ⟨e⟩⟩)
  · exact four_u6two hGA hK ⟨i, h6, ⟨e⟩⟩
  · exact four_noThree_types hGA hK (Or.inr (Or.inl ⟨i, h8, ⟨e⟩⟩))
  · exact four_noThree_types hGA hK (Or.inr (Or.inr ⟨i, hD, ⟨e⟩⟩))

theorem i1015twoAt_u6_holds (G : Type) [Group G] [Finite G] :
    ∀ (X K : Subgroup G) (n : ℕ), GLAPComponent 3 X K → Odd n →
      catalogIs (PSimple 3 K) (S10.isU6n n) →
      ∃ E T : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ T ≤ K ∧ IsPGroup 2 T ∧
        ¬ T ≤ GLAPPrimeCoreOf 3 K ∧ E ≤ Subgroup.normalizer (T : Set G) := by
  intro X K n hK hn hcat
  have hGA : GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  obtain ⟨E, T, hEK, hEe, hEc, hTK, hT2, hTn, hEN⟩ := u6_exists_E_T hGA hn hK hcat
  obtain ⟨E', hE'E, hE'e, hE'c⟩ := exists_sub_card_pow hEe (k := 3) (by
    rw [hEc]
    exact ⟨Nat.card (Subgroup.center (PQuot 3 K)), by norm_num⟩)
  exact ⟨E', T, hE'E.trans hEK, hE'e, hE'c, hTK, hT2, hTn, hE'E.trans hEN⟩

theorem i1015coverAt_centre_holds (G : Type) [Group G] [Finite G] :
    ∀ (X K : Subgroup G) (n : ℕ), GLAPComponent 3 X K →
      (catalogIs (PSimple 3 K) (S10.isU6n n) ∨ catalogIs (PSimple 3 K) (S10.isTE6n n)) →
      Subgroup.center (PQuot 3 K) ≠ ⊥ → Nat.card (Subgroup.center (PQuot 3 K)) = 3 := by
  intro X K n hK hcat hZne
  have hGA : GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  rcases (Nat.dvd_prime Nat.prime_three).1 (card_center_pQuot_dvd_three hGA hK hcat) with h | h
  · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hZne
  · exact h

theorem i1015coverAt_u6_holds (G : Type) [Group G] [Finite G] :
    ∀ (X K : Subgroup G) (n : ℕ), GLAPComponent 3 X K → Odd n →
      catalogIs (PSimple 3 K) (S10.isU6n n) → Subgroup.center (PQuot 3 K) ≠ ⊥ →
      ∃ E T : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ T ≤ K ∧ IsPGroup 2 T ∧
        ¬ T ≤ GLAPPrimeCoreOf 3 K ∧ E ≤ Subgroup.normalizer (T : Set G) := by
  intro X K n hK hn hcat hZne
  have hGA : GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hZ3 := i1015coverAt_centre_holds G X K n hK (Or.inl hcat) hZne
  obtain ⟨E, T, hEK, hEe, hEc, hTK, hT2, hTn, hEN⟩ := u6_exists_E_T hGA hn hK hcat
  exact ⟨E, T, hEK, hEe, by rw [hEc, hZ3]; norm_num, hTK, hT2, hTn, hEN⟩

theorem i1015twoAt_of_TE6Rank (hR : TE6Rank) (G : Type) [Group G] [Finite G] : I1015twoAt G := by
  intro X K n hK hn
  refine ⟨fun hcat => i1015twoAt_u6_holds G X K n hK hn hcat, fun hcat => ?_⟩
  obtain ⟨E, T, hEK, hEe, hEc, hTK, hT2, hTn, hEN⟩ := te6_exists_E_T hR hn hK hcat
  obtain ⟨E', hE'E, hE'e, hE'c⟩ := exists_sub_card_pow hEe (k := 4) (by
    rw [hEc]
    exact dvd_mul_right _ _)
  exact ⟨E', T, hE'E.trans hEK, hE'e, hE'c, hTK, hT2, hTn, hE'E.trans hEN⟩

theorem i1015coverAt_of_TE6Rank (hR : TE6Rank) (G : Type) [Group G] [Finite G] : I1015coverAt G := by
  intro X K n hK hn hcat hZne
  have hZ3 := i1015coverAt_centre_holds G X K n hK hcat hZne
  refine ⟨hZ3, fun hU6 => i1015coverAt_u6_holds G X K n hK hn hU6 hZne, fun hTE6 => ?_⟩
  obtain ⟨E, T, hEK, hEe, hEc, hTK, hT2, hTn, hEN⟩ := te6_exists_E_T hR hn hK hTE6
  exact ⟨E, T, hEK, hEe, by rw [hEc, hZ3]; norm_num, hTK, hT2, hTn, hEN⟩

end Holds

end CFSG.LocalAnalysis.GLTheoremA
