module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.CoverCentre
public import CFSG.GroupTheory.NormalizerQuotientQuotient
public import CFSG.GroupTheory.QuasiDihedralFusion.Transport
public import CFSG.Quasithin.Background.A3Structure312Quotient

public section

namespace CFSG.GroupTheory

open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)

variable {K : Type} [Group K] [Finite K]

theorem pCoreOf_center_eq_pCore (hq : CFSG.Open.IsQuasisimple K) :
    CFSG.Open.pCoreOf 2 (Subgroup.center K) = CFSG.pCore 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOcenter := CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 (Subgroup.center K)
  refine le_antisymm ?_ ?_
  · simp only [CFSG.pCore]
    exact le_sSup ⟨Subgroup.normal_of_le_center hOcenter,
      CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 _⟩
  · refine CFSG.ClassicalGroups.PCoreSection.le_pCoreOf
      (GL83.I243.Cover.pCore_le_center (p := 2) hq) (fun x hx y hy => ?_)
      (CFSG.pCore_isPGroup (p := 2) (G := K))
    rw [show x * y * x⁻¹ = y by rw [(Subgroup.mem_center_iff.mp hx y).symm]; group]
    exact hy

variable [(CFSG.Open.pCoreOf 2 (Subgroup.center K)).Normal]

theorem odd_card_center_quotient_pCoreOf_center (hq : CFSG.Open.IsQuasisimple K) :
    Odd (Nat.card (Subgroup.center (K ⧸ CFSG.Open.pCoreOf 2 (Subgroup.center K)))) := by
  rw [Nat.card_congr (Subgroup.centerCongr
    (QuotientGroup.quotientMulEquivOfEq (pCoreOf_center_eq_pCore hq))).toEquiv]
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20p_odd_center_bar2 K

omit [Finite K] in
theorem isQuasisimple_quotient_pCoreOf_center (hq : CFSG.Open.IsQuasisimple K) :
    CFSG.Open.IsQuasisimple (K ⧸ CFSG.Open.pCoreOf 2 (Subgroup.center K)) :=
  CFSG.ComponentClassification.Quasisimple.central_quotient hq _
    (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 _)

noncomputable def quotientPCoreOfCenterEquiv (hq : CFSG.Open.IsQuasisimple K) :
    (K ⧸ CFSG.Open.pCoreOf 2 (Subgroup.center K)) ⧸
        Subgroup.center (K ⧸ CFSG.Open.pCoreOf 2 (Subgroup.center K)) ≃*
      K ⧸ Subgroup.center K :=
  have : Group.IsPerfect K := ⟨hq.1⟩
  have hOcenter := CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 (Subgroup.center K)
  (QuotientGroup.quotientMulEquivOfEq
    (CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact hOcenter)).symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient _ (Subgroup.center K) hOcenter)

theorem isMulCommutative_normalizerQuotient_of_quotient_pCoreOf_center (S : Subgroup K)
    (hS : IsSylowTwoOf S ⊤)
    (h : IsMulCommutative (normalizerQuotient
      (S.map (QuotientGroup.mk' (CFSG.Open.pCoreOf 2 (Subgroup.center K)))))) :
    IsMulCommutative (normalizerQuotient S) :=
  CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv
    (normalizerQuotient_quotientEquiv _ S
      (hS.le_of_normalizes le_top (by simp [Subgroup.normalizer_eq_top])
        (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 _))).symm h

theorem isMulCommutative_normalizerQuotient_of_forall_quotient_pCoreOf_center
    (h : ∀ S' : Subgroup (K ⧸ CFSG.Open.pCoreOf 2 (Subgroup.center K)), IsSylowTwoOf S' ⊤ →
      IsMulCommutative (normalizerQuotient S'))
    (S : Subgroup K) (hS : IsSylowTwoOf S ⊤) :
    IsMulCommutative (normalizerQuotient S) :=
  isMulCommutative_normalizerQuotient_of_quotient_pCoreOf_center S hS
    (h _ (CFSG.Quasithin.A312.isSylowTwoOf_top_map _ (QuotientGroup.mk'_surjective _) hS))

end CFSG.GroupTheory
