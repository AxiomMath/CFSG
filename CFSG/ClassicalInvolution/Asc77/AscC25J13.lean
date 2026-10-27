module

public import CFSG.ClassicalInvolution.Q3.Q3CLBasic
public import CFSG.ClassicalInvolution.Asc77.AscC25J7
public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section AE

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem crossIn_aEmpty (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') {a : G}
    (hΛ : HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K' a))) :
    ∀ M ∈ conjFamily (crossIn K' a), AEmpty (conjFamily (crossIn K' a)) M := by
  classical
  have hΩg : HypOmegaGen (conjFamily (crossIn K' a)) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΛ
  rintro M ⟨c₁, rfl⟩ J hJstar hJnbr zK zJ hzK hzJ
  exfalso
  apply hJnbr
  obtain ⟨hJΛ, hJne, U, hU, hUJ, hUN⟩ := hJstar
  obtain ⟨c₂, rfl⟩ := hJΛ
  obtain ⟨R₀, hR₀, hUR₀, hUcyc, hUidx⟩ := hU
  obtain ⟨J₃, -, hR₀syl⟩ := exists_isSylow2In_of_mem_RSet hR₀
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩg hR₀
  obtain ⟨y, hyU, hy4⟩ := C25V.exists_orderOf_four_of_cyclic hUR₀ hUcyc hUidx h8 hR₀syl.2.1
  have hyJ := hUJ hyU
  have hyN := hUN hyU
  have hy4' : orderOf (y : G) = 4 := by rw [Subgroup.orderOf_coe, hy4]
  have hyK : (y : G) ∈ conjSub (c₂ : G) K' := le_conjSub_of_mem_cross c₂ hyJ
  have hyz : y * zK * y⁻¹ = zK := hzK.conj_eq (mem_normalizer_iff_conjSub_eq.mp hyN)
  have hzK' : (zK : G) = (c₁ : G) * z * (c₁ : G)⁻¹ :=
    crossIn_coe_eq_of_isUniqueInvolution h.hz' c₁ hzK
  have hzJ' : (zJ : G) = (c₂ : G) * z * (c₂ : G)⁻¹ :=
    crossIn_coe_eq_of_isUniqueInvolution h.hz' c₂ hzJ
  have hcomm : ((c₁ : G) * z * (c₁ : G)⁻¹) * (y : G) = (y : G) * ((c₁ : G) * z * (c₁ : G)⁻¹) := by
    rw [← hzK']
    have : (y : G) * (zK : G) * (y : G)⁻¹ = (zK : G) := by
      have := congrArg Subtype.val hyz
      simpa using this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  have heq := eq_conj_z_of_commute_order_four h (c := (c₂ : G)) (g := (c₁ : G)) (y₀ := (y : G))
    hyK hy4' hcomm
  have hzz : zK = zJ := Subtype.ext (by rw [hzK', hzJ', heq])
  rw [← hzz] at hzJ
  have hJMem : conjSub c₂ (crossIn K' a) ∈ conjFamily (crossIn K' a) := ⟨c₂, rfl⟩
  have hMMem : conjSub c₁ (crossIn K' a) ∈ conjFamily (crossIn K' a) := ⟨c₁, rfl⟩
  exact CFSG.ClassicalInvolution.Q3.Q3CL.T3.twin_mem_omegaNbr hΩg hMMem hJMem hJne hzK hzJ

end AE

end CFSG.ClassicalInvolution.Asc77.C25J
