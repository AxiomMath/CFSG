module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Pocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34StepA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Misc2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2G2Def
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Core
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Syl

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem exists_quaternion_of_pocketData_q8 [Finite G] (hG1 : Asc82NoQ8InL2)
    (hG2 : Asc82OddCoreCentralizerQ8) {x : G} {X : Subgroup G} {y : G} {K : Subgroup G}
    (hD : Sec3PocketData x X y K) :
    ∃ f : QuaternionGroup 2 →* G, Function.Injective f ∧ f (QuaternionGroup.a 2) = y ∧
      f.range ≤ CFSG.inSubgroup (CFSG.pCore 2) K := by
  obtain ⟨hyK, hKle, hKsub, hKSL⟩ := hD.pocket
  obtain ⟨f, hf, hfy, hfK⟩ := exists_quaternion_of_isSL23Mod hKSL hyK hD.involution_y
  have hyX : y ∈ X := hD.mem
  have hfX : f.range ≤ X := hfK.trans hD.le
  obtain ⟨f', hf', hf'mk⟩ := exists_injective_quotient_oddCore hf hfX
  have hFN : FStarQuotientNoL81 (↥X ⧸ oddCore ↥X) := by
    have h := hD.inFStar
    unfold InFStar IsFStarGroup IsFGroup at h
    rcases h with ⟨-, hΩ | hT⟩ | ⟨-, h9 | h81 | h3 | hU3⟩
    · exact Or.inl hΩ
    · exact Or.inr (Or.inl hT)
    · exact Or.inr (Or.inr (Or.inl h9))
    · exact (hG1 _ (Or.inr h81) f' hf').elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hU3)))
  have hbar : (QuotientGroup.mk (⟨y, hyX⟩ : ↥X) : ↥X ⧸ oddCore ↥X) = f' (QuaternionGroup.a 2) := by
    rw [hf'mk]
    congr 1
    exact Subtype.ext hfy.symm
  have hG2' : oddCore ↥(centralizer
      ({(QuotientGroup.mk (⟨y, hyX⟩ : ↥X) : ↥X ⧸ oddCore ↥X)} : Set (↥X ⧸ oddCore ↥X))) = ⊥ := by
    rw [hbar]
    exact hG2 (↥X ⧸ oddCore ↥X) hFN f' hf'
  have hKy : K ≤ centralizer ({y} : Set G) := hKle.trans inf_le_right
  have hO : oddCore ↥K ≤ Subgroup.center ↥K :=
    oddCore_le_center_of_pocket (inFStar_isQuasisimple hD.inFStar) hyX hD.involution_y hG2'
      (inf_le_inf_right _ hD.component.1) hD.le hKy hKsub
  exact ⟨f, hf, hfy, le_pCore_of_isSL23Mod hKSL hO hfK (natCard_range_quaternion hf)⟩

theorem asc82Lemma34b_of_inputs_q8 (hG1 : Asc82NoQ8InL2) (hG2 : Asc82OddCoreCentralizerQ8)
    (hP : Asc82Q8Pocket) : Asc82Lemma34b := by
  intro G _ _ t L hSet x X y K u I hD hu hmem hI hIF hQI _
  obtain ⟨f, hf, hfy, hfQ⟩ := exists_quaternion_of_pocketData_q8 hG1 hG2 hD
  have hfI : f.range ≤ I := hfQ.trans hQI
  have hyI : y ∈ I := hfI ⟨QuaternionGroup.a 2, hfy⟩
  obtain ⟨f', hf', hf'mk⟩ := exists_injective_quotient_oddCore hf hfI
  have hbar : f' (QuaternionGroup.a 2) = QuotientGroup.mk (⟨y, hyI⟩ : ↥I) := by
    rw [hf'mk]
    congr 1
    exact Subtype.ext hfy
  rcases inF_pocketable_or_isLnEps3 hG1 hIF hf' with ⟨hInF, hPock⟩ | hLn
  · refine Or.inl ⟨hInF, ?_⟩
    have hpocket := hP _ hPock f' hf'
    rw [hbar] at hpocket
    exact isI4PlusIn_of_quotient hyI hD.involution_y hpocket
  · exact Or.inr hLn

theorem asc82Lemma34c_of_inputs_q8 (hT2 : Asc82Thm2Q) (hC1 : Asc82CommuteStep)
    (hC3 : Asc82CommutingPocket) (hG1 : Asc82NoQ8InL2) (hG2 : Asc82OddCoreCentralizerQ8)
    (hS : Asc82SchurU43) : Asc82Lemma34c := by
  intro G _ _ t L hSet x X y K hD J hJ hJF
  have hy := hD.involution_y
  rcases asc82Lemma34a_of_inputs hT2 hC1 G t L hSet x X y K y J hD hy
      ⟨1, Subgroup.one_mem _, (one_mul y).symm⟩ hJ hJF with hKJ | hQJ
  · exact hC3 G t L hSet x X y K hD J hJ hJF hKJ
  · obtain ⟨f, hf, hfy, hfQ⟩ := exists_quaternion_of_pocketData_q8 hG1 hG2 hD
    have hfJ : f.range ≤ J := hfQ.trans hQJ
    have hyJ : y ∈ J := hfJ ⟨QuaternionGroup.a 2, hfy⟩
    have hJc : ∀ a ∈ J, a * y = y * a := fun a ha =>
      (Subgroup.mem_centralizer_iff.mp (hJ.1 ha) y rfl).symm
    have hT := isTwoU43_of_mem_center hJF hy hyJ hJc
    let fJ : QuaternionGroup 2 →* ↥J := f.codRestrict J (fun g => hfJ ⟨g, rfl⟩)
    have hfJinj : Function.Injective fJ := fun a b hab => hf (congrArg Subtype.val hab)
    have hz : fJ (QuaternionGroup.a 2) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (by
        change (g : G) * f (QuaternionGroup.a 2) = f (QuaternionGroup.a 2) * g
        rw [hfy]
        exact hJc g g.2)
    exact false_of_central_quaternion hS (inFStar_isQuasisimple hJF) hT hfJinj hz

end CFSG.OddStandard.SmallF3.Omega
