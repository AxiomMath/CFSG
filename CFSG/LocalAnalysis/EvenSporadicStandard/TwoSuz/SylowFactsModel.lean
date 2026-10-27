module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.SylowData
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SZGammaThree
public import Certificates.Certificate1379102

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup
open CFSG.ComponentClassification.GrSLit.L34Sec5S
open CFSG.ComponentClassification.GrSLit
open CFSG.Sporadic.Recognition.SuzMultiplier (gcS SuzCover)

section Model


theorem Yu_eq_one_of_not_lt (i : Fin gcS) (hi : ¬ i.val < 7) : Yu i = 1 := by
  rw [Yu]
  exact GenSys.letterU_one coverGS coverGS_valid
    (getD_oneM_of_le _ (by rw [coverGS_size.1]; omega))
    (getD_oneM_of_le _ (by rw [coverGS_size.2]; omega))

theorem vm_Yu (i : Fin gcS) : vm (Yu i) = ofMt (coverGS.mats.getD i.val oneM) := by
  have e : 2 * i.val / 2 = i.val := by omega
  rw [Yu, GenSys.vm_letterU, GenSys.letter, if_pos (by omega), e]

theorem Lhat_eq_closure_range :
    (Lhat : Subgroup GL12) = Subgroup.closure (Set.range Yu) := by
  have htop : Subgroup.closure (Set.range (PresentedGroup.of : Fin gcS → SuzCover)) = ⊤ :=
    PresentedGroup.closure_range_of _
  have hL : (Lhat : Subgroup GL12) = (⊤ : Subgroup SuzCover).map rho := by
    rw [Lhat, MonoidHom.range_eq_map]
  rw [hL, ← htop, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (rho_of i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, ⟨i, rfl⟩, rho_of i⟩

theorem twoSuz_sylow_model :
    CFSG.ComponentClassification.GrSLit.IsElemTwo
        (CFSG.ComponentClassification.GrSLit.L34Sec5S.zGammaThree Ssub) ∧
      Nat.card (CFSG.ComponentClassification.GrSLit.L34Sec5S.zGammaThree Ssub) = 32 ∧
      ∃ Q : Subgroup GL12, Q ≤ Ssub ∧ CFSG.ComponentClassification.GrSLit.IsElemTwo Q ∧
        Nat.card Q = 8 ∧
        (Lhat : Subgroup GL12) ≤
          Ssub ⊔ ((Lhat : Subgroup GL12) ⊓ Subgroup.centralizer (Q : Set GL12)) := by
  obtain ⟨-, hZ, hZsq, Q, hQS, hQc, hQsq, hQ8, hY⟩ := Certificates.certificate1379102
  rw [← Ssub_eq] at hZ hZsq hQS hY
  refine ⟨⟨zGammaThree_comm Ssub, hZsq⟩, hZ, Q, hQS, ⟨hQc, hQsq⟩, hQ8, ?_⟩
  refine Lhat_eq_closure_range.le.trans ((Subgroup.closure_le _).mpr ?_)
  rintro _ ⟨i, rfl⟩
  by_cases hi7 : i.val < 7
  · exact sup_le_sup_left (inf_le_inf_right _ AB_le_Lhat) _ (hY i.val hi7 (Yu i) (vm_Yu i))
  · rw [Yu_eq_one_of_not_lt i hi7]
    exact one_mem _

end Model

end CFSG.EvenSporadicStandard.TwoSuz
