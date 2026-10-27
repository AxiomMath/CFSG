module

public import CFSG.Assembly.Defs
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs
import CFSG.Adapters.LinearFieldTransport
import CFSG.ClassicalInvolution.Basic
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedAltSevenQuaternion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankOneCover
import CFSG.Milestones.LR_dihedral_simple_recognition

public section

namespace CFSG.ComponentClassification.QuaternionComponent

open Subgroup

theorem ringChar_ne_two_of_card {K : Type*} [Field K] [Finite K] {p f : ℕ} (hp : Odd p)
    (hK : Nat.card K = p ^ f) : ringChar K ≠ 2 := by
  have : Fintype K := Fintype.ofFinite K
  intro h
  have h0 := FiniteField.even_card_iff_char_two.mp h
  rw [← Nat.card_eq_fintype_card, hK] at h0
  have h1 : p ^ f % 2 = 1 := Nat.odd_iff.mp hp.pow
  omega

theorem oddCore_le_center {J : Type*} [Group J] [Finite J] (hJ : Open.IsQuasisimple J) {z : J}
    (hz : orderOf z = 2) : CFSG.oddCore J ≤ center J := by
  rcases Quasisimple.normal_le_center_or_eq_top hJ (CFSG.oddCore J) with h | h
  · exact h
  · exact absurd (h ▸ mem_top z)
      (UnbalancedCatalog.EvenCatalog.not_mem_oddCore_of_orderOf_eq_two hz)

theorem classicalInvolutionWitness_of_component {G : Type} [Group G] [Finite G] {z : G}
    (hz : orderOf z = 2) {J : Subgroup G}
    (hJ : Assembly.IsComponentOf J (centralizer ({z} : Set G))) (hzJ : z ∈ J) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    Open.classicalInvolutionWitness J ∧ Open.IsSubnormal J (centralizer ({z} : Set G)) := by
  obtain ⟨hJC, hJsub, hJq⟩ := hJ
  refine ⟨?_, (AssemblyBPredicates.isSubnormal_iff_open J _).mp hJsub⟩
  have hU := (ClassicalInvolution.unique_involution_of_quaternion_sylow hzJ hz hJC S hS).1
  have hz2 : orderOf (⟨z, hzJ⟩ : J) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have hrank : CFSG.pRank 2 J ≤ 1 :=
    UnbalancedAltSeven.pRank_le_one_of_unique hz2 fun y hy =>
      Subtype.ext (hU y y.2 (by rw [Subgroup.orderOf_coe]; exact hy))
  have hJq' : Open.IsQuasisimple J := (AssemblyBPredicates.isQuasisimple_iff_open J).mp hJq
  have hAq : Open.IsQuasisimple (J ⧸ CFSG.oddCore J) :=
    Quasisimple.central_quotient hJq' (CFSG.oddCore J) (oddCore_le_center hJq' hz2)
  have hAn : CFSG.IsQuasisimple (J ⧸ CFSG.oddCore J) :=
    (AssemblyBPredicates.isQuasisimple_iff_native _).mp hAq
  obtain ⟨-, _, -, -, -, hZcard, r, hr, -, -, hTs, hTnab, hTsyl, hcover⟩ :=
    UnbalancedGS.rank_one_quasisimple_odd_core_quotient_central_cover.{0, 0} hrank hAn
  have : IsSimpleGroup ((J ⧸ CFSG.oddCore J) ⧸ center (J ⧸ CFSG.oddCore J)) := hTs
  obtain ⟨P⟩ : Nonempty (Sylow 2 ((J ⧸ CFSG.oddCore J) ⧸ center (J ⧸ CFSG.oddCore J))) :=
    inferInstance
  obtain ⟨⟨eP⟩, -, -⟩ := hTsyl P
  have hP : Nonempty ((P : Subgroup ((J ⧸ CFSG.oddCore J) ⧸ center (J ⧸ CFSG.oddCore J))) ≃*
      DihedralGroup (2 ^ ((r - 1) - 1))) := by
    rw [show r - 1 - 1 = r - 2 by omega]
    exact ⟨eP⟩
  rcases CFSG.Milestones.lr_dihedral_simple_recognition _ hTnab P (r - 1) (by omega) hP with
    ⟨p, f, hp, hp2, hf, hmodel⟩ | h7
  · have hfact : Fact p.Prime := ⟨hp⟩
    obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hmodel
    obtain ⟨F, -, -⟩ := hcover K (ringChar_ne_two_of_card (hp.odd_of_ne_two hp2) hK)
      (eK.trans ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
        (LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K)))
    exact Or.inl ⟨p, f, hfact, hp2, hf, ⟨F.trans (ClassicalModels.specialLinearFieldEquiv
      (ClassicalModels.finiteFieldEquivGaloisField K p f hf hK) (Fin 2))⟩⟩
  · exact Or.inr ⟨hAq, hZcard, h7⟩

end CFSG.ComponentClassification.QuaternionComponent
