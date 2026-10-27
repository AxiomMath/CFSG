module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FiveAux.Steinberg
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7FiveAux.Steinberg
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4InnerAux.SteinbergD4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie

variable {τ : Tag} {K : Type} [Field K]

private theorem kernelReflectionGroup_one_eq_top (τ : Tag) (K : Type) [Field K] :
    kernelReflectionGroup (τ := τ) (1 : Fin τ.rank → Kˣ) = ⊤ := by
  rw [eq_top_iff, ← (coxeterSystem τ).subgroup_closure_range_simple, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  refine Subgroup.subset_closure ⟨1, i, ⟨IsRoot.smul (isRoot_single τ i) 1, ?_⟩, ?_⟩
  · simp [rootChar]
  · group

private theorem not_dvd_twelve_of_five_le {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ p ∣ 12 := by
  intro h
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) h
  interval_cases p <;> first | omega | norm_num at hp | norm_num at h

private theorem card_weylGroup_G2 : Nat.card (WeylGroup Tag.G2) = 12 := by
  have h := CFSG.GH74.GLS.SP.card_coxeterGroup_fin_two
    (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan Tag.G2))
  simp only [CFSG.LieType.RootSystem.coxeterMatrix,
    TauCeti.coxeterMatrixOfCartanMatrix_apply, Tag.cartan] at h
  norm_num at h
  exact h

private theorem not_dvd_card_weylGroup_G2 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ p ∣ Nat.card (WeylGroup Tag.G2) := by
  rw [card_weylGroup_G2]
  exact not_dvd_twelve_of_five_le hp h5

private theorem le_of_not_dvd_card
    {p : ℕ} (hp : p.Prime) {τ : Tag}
    (hnd : ¬ p ∣ Nat.card (WeylGroup τ)) {K : Type} [Field K] {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i ^ p = 1) : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := by
  intro w hw
  refine mem_kernelReflectionGroup_of_coprime hp ha hw ?_
  exact Nat.coprime_comm.2 <|
    (hp.coprime_iff_not_dvd).2 fun h => hnd (h.trans (orderOf_dvd_natCard w))

theorem rootCharStabilizerSubgroup_le_kernelReflectionGroup_of_odd
    {K : Type} [Field K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hE6 : τ = .E6 → p ≠ 3) {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i ^ p = 1) :
    rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := by
  have hp' : p = 3 ∨ p = 5 ∨ p = 7 ∨ 7 < p := by
    rcases Nat.lt_or_ge 7 p with h | h
    · exact Or.inr (Or.inr (Or.inr h))
    · interval_cases p <;> first | omega | exact absurd hp (by norm_num)
  rcases hp' with rfl | rfl | rfl | h7
  ·
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
    · by_cases ha1 : a = 1
      · rw [ha1, kernelReflectionGroup_one_eq_top]
        exact le_top
      · exact rootCharStabilizer_le_kernelReflectionGroup_G2_three_kd264alg
          (by funext i; simpa using ha i) ha1
    · exact (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three a ha).le
    · exact (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_D4_three a ha).le
    · exact absurd rfl (hE6 rfl)
    · exact (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_three a ha).le
    · exact (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_three a ha).le
  ·
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact le_of_not_dvd_card hp (not_dvd_card_weylGroup_G2 hp (by norm_num)) ha
    · exact le_of_not_dvd_card hp
        (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_F4 hp (by norm_num)) ha
    · exact le_of_not_dvd_card hp
        (CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 hp (by norm_num)) ha
    · exact (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E6_five a ha).le
    · exact (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_five a ha).le
    · exact (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_five a ha).le
  ·
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact le_of_not_dvd_card hp (not_dvd_card_weylGroup_G2 hp (by norm_num)) ha
    · exact le_of_not_dvd_card hp
        (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_F4 hp (by norm_num)) ha
    · exact le_of_not_dvd_card hp
        (CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 hp (by norm_num)) ha
    · have hnd : ¬ 7 ∣ Nat.card (WeylGroup Tag.E6) := by
        rw [CFSG.RankThree.E6.card_weylGroup_E6]
        norm_num
      exact le_of_not_dvd_card hp hnd ha
    · exact (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_seven a ha).le
    · exact (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_seven a ha).le
  ·
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact le_of_not_dvd_card hp (not_dvd_card_weylGroup_G2 hp (by omega)) ha
    · exact le_of_not_dvd_card hp
        (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_F4 hp (by omega)) ha
    · exact le_of_not_dvd_card hp
        (CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 hp (by omega)) ha
    · exact le_of_not_dvd_card hp
        (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp h7 (Or.inl rfl)) ha
    · exact le_of_not_dvd_card hp
        (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp h7 (Or.inr (Or.inl rfl))) ha
    · exact le_of_not_dvd_card hp
        (CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp h7 (Or.inr (Or.inr rfl))) ha

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
