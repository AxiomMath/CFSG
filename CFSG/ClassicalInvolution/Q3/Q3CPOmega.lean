module

public import CFSG.ClassicalInvolution.Q3.Q3CPTwin
public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen

public section

namespace CFSG.ClassicalInvolution.Q3.Q3CP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem not_hasTwin_satU (hnab : ∃ a b : G, a * b ≠ b * a) (hz : IsClassicalMember3 K z)
    (hΔ : DeltaConnected K) (hB : ¬ BootData3 (conjClass3 K)) (hA2 : ¬ A2Configuration z K) :
    ¬ Asc77.AscHypOmega.HasTwin (satU (.sl2 3 1) K z) z := by
  rintro ⟨J, hJ, hne, hU⟩
  exact hne (noTwins3_of_typeC hnab hz hΔ hB hA2 hJ hU)

theorem omega5At_of_typeC (hnab : ∃ a b : G, a * b ≠ b * a) (hz : IsClassicalMember3 K z)
    (hΔ : DeltaConnected K) (hB : ¬ BootData3 (conjClass3 K)) (hA2 : ¬ A2Configuration z K) :
    Asc77.AscHypOmega.Omega5At (CoreAssembly.conjClass (satU (.sl2 3 1) K z))
      (satU (.sl2 3 1) K z) z := by
  intro J _ _ v _ _ _ hvz
  have hm := (IsClassicalMemberU.ofQ3 hz).satU_member
  exact Asc77.AscHypOmega.centralizer_le_normalizer_of_not_hasTwin
    (hm.isUniqueInvolution (MemberType.cert_sl2 3 1))
    (not_hasTwin_satU hnab hz hΔ hB hA2)
    (Subgroup.mem_centralizer_singleton_iff.mpr hvz)

theorem hypOmegaModU_of_typeC (hnab : ∃ a b : G, a * b ≠ b * a) (hz : IsClassicalMember3 K z)
    (hΔ : DeltaConnected K) (hB : ¬ BootData3 (conjClass3 K)) (hA2 : ¬ A2Configuration z K) :
    HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) :=
  hypOmegaModU_conjClass (MemberType.cert_sl2 3 1) (IsClassicalMemberU.ofQ3 hz).satU_member
    (isIntrinsicU_satU _ _ _) (omega5At_of_typeC hnab hz hΔ hB hA2)

theorem hypOmegaGen_of_typeC (hnab : ∃ a b : G, a * b ≠ b * a) (hz : IsClassicalMember3 K z)
    (hΔ : DeltaConnected K) (hB : ¬ BootData3 (conjClass3 K)) (hA2 : ¬ A2Configuration z K) :
    Disconnected.AschTight.HypOmegaGen (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) :=
  hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) (hypOmegaModU_of_typeC hnab hz hΔ hB hA2)

end CFSG.ClassicalInvolution.Q3.Q3CP
