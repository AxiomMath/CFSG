module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111KBig
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11KBigRWit
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11KBigRThm
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11KBigAsm
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L111N
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11T

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem s900_residual_witness {G : Type} [Group G] [Finite G] (hp : Asc82Pre11)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R)
    (hres : ∃ P : Subgroup G, IsSylow2Of P (secXH t z) ∧
      (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥P ≃* CFSG.Open.SemidihedralGroup n)) ∧
      oddCoreIn (secXH t z) ⊔ P ≠ secXH t z) :
    orderOf z = 2 ∧ ∃ J : Subgroup G, z ∈ J ∧
      CFSG.Open.IsSubnormal J (centralizer ({z} : Set G)) ∧
      ∃ Sy : Sylow 2 J, (∃ r : ℕ, 3 ≤ r ∧
        Nonempty ((Sy : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
      CFSG.Open.classicalInvolutionWitness J := by
  obtain ⟨P, hPX, ⟨n, hn, hsd⟩, hXP⟩ := hres
  obtain ⟨-, -, -, -, -, htz⟩ := sec10D_basic hp.basic hctx.toSec10Ctx
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hΘX : Subgroup.closure (secTheta t z R) ≤ secXH t z := by
    apply Subgroup.closure_mono
    rintro s ⟨-, h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  have hzX : z ∈ secXH t z :=
    hΘX (sec11_z_mem_closure_Theta hp (asc82Lemma111N_of hp (asc82Step111T_of hp)) hctx)
  exact ⟨hz2, s900_witness_of_semidihedral hn hPX hsd hXP hzX hz2 (sec11KB_X_le htz)
    fun _ hh _ hx => sec11KB_X_conj hh hx⟩

theorem asc82Step1111KBigSD_of_classicalInvolution
    (hCI : CFSG.ComponentClassification.GSLit.ClassicalInvolutionInput)
    (hCL1 : CFSG.ComponentClassification.CatLeaf.GLS3OddLieAutComponentsInput)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    Asc82Step1111KBigSD := by
  intro hp G _ _ t L S z K1 K2 T R hctx _ _ _ _ hres
  obtain ⟨hz, J, hzJ, hJ, Sy, hSy, hw⟩ := s900_residual_witness hp hctx hres
  exact (c3b_false_of_witness hCI hCL1 hO hctx.toSec3SettingLB hz hzJ hJ Sy hSy hw).elim

end CFSG.OddStandard.SmallF3.Omega
