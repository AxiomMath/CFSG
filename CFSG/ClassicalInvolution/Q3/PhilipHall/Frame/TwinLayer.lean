module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent3Fam

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

section Core

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G} {K : Subgroup G}

@[expose] noncomputable abbrev exactCore (c : G) (K : Subgroup G) : Subgroup G :=
  TwinADescent.coreAt c K

@[expose] abbrev tqMembers (Ω : Set (Subgroup G)) (c : G) : Set (Subgroup G) :=
  tqMembers3 Ω c

theorem exactCore_le_left (c : G) (K : Subgroup G) : exactCore c K ≤ K :=
  TwinADescent.coreAt_le_left c K

theorem exactCore_le_centralizer (c : G) (K : Subgroup G) :
    exactCore c K ≤ Subgroup.centralizer ({c} : Set G) :=
  TwinADescent.coreAt_le_centralizer c K

theorem isSylow2In_exactCore_iff (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hcK : c ∈ trivialOnQuot K) {V : Subgroup G} :
    IsSylow2In V (exactCore c K) ↔ IsSylow2In V K ∧ V ≤ Subgroup.centralizer ({c} : Set G) :=
  TwinADescent.isSylow2In_coreAt_iff hc2 hcK

theorem mem_trivialOnQuot_iff_exists_sylow (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hK : K ∈ Ω) :
    c ∈ trivialOnQuot K ↔ ∃ R, IsSylow2In R K ∧ R ≤ Subgroup.centralizer ({c} : Set G) := by
  constructor
  · intro h
    have hcomm : ⁅Subgroup.zpowers c, K⁆ ≤ oddCoreOf K :=
      Subgroup.commutator_le.mpr fun a ha x hx =>
        (mem_trivialOnQuot_iff.mp (Subgroup.zpowers_le.mpr h ha)).2 x hx
    obtain ⟨R, hR, hRc⟩ := AscE184Sect.exists_isSylow2In_centralizer hc2 hcomm
    exact ⟨R, hR, by rwa [centralizer_zpowers_eq_singleton'] at hRc⟩
  · intro h
    exact TwinADescent3.mem_tq_of_sylCent hΩ h2 hK h

theorem mem_tqMembers_iff_exists_sylow (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    K ∈ tqMembers Ω c ↔
      K ∈ Ω ∧ ∃ R, IsSylow2In R K ∧ R ≤ Subgroup.centralizer ({c} : Set G) :=
  and_congr_right fun hK => mem_trivialOnQuot_iff_exists_sylow hΩ h2 hc2 hK

theorem exactCore_cover (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcK : c ∈ trivialOnQuot K)
    (h2K : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)) :
    ∀ x ∈ K, ∃ i ∈ exactCore c K, ∃ n ∈ oddCoreOf K, x = i * n := by
  have hcomm : ⁅Subgroup.zpowers c, K⁆ ≤ oddCoreOf K :=
    Subgroup.commutator_le.mpr fun a ha x hx =>
      (mem_trivialOnQuot_iff.mp (Subgroup.zpowers_le.mpr hcK ha)).2 x hx
  obtain ⟨R, hR, hRc⟩ := AscE184Sect.exists_isSylow2In_centralizer hc2 hcomm
  have hRc' : R ≤ Subgroup.centralizer ({c} : Set G) := by
    rwa [centralizer_zpowers_eq_singleton'] at hRc
  have hRK : R ≤ exactCore c K := le_tightCore_of_isPGroup (le_inf hR.1 hRc') hR.2.1
  intro x hx
  obtain ⟨r, hr, o, ho, rfl⟩ := TwinExact.mem_mul_oddCore_of_sylow h2K hR x hx
  exact ⟨r, hRK hr, o, ho, rfl⟩

theorem mem_exactCore_of_uniqueInvolution (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hK : K ∈ Ω) (hcK : c ∈ trivialOnQuot K) {z : G}
    (hz : IsUniqueInvolution K z) : z ∈ exactCore c K := by
  have hcomm : ⁅Subgroup.zpowers c, K⁆ ≤ oddCoreOf K :=
    Subgroup.commutator_le.mpr fun a ha x hx =>
      (mem_trivialOnQuot_iff.mp (Subgroup.zpowers_le.mpr hcK ha)).2 x hx
  obtain ⟨R, hR, hRc⟩ := AscE184Sect.exists_isSylow2In_centralizer hc2 hcomm
  have hRc' : R ≤ Subgroup.centralizer ({c} : Set G) := by
    rwa [centralizer_zpowers_eq_singleton'] at hRc
  have hR8 : 8 ≤ Nat.card ↥R :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR)
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hR.1 hR.2.1 (by omega)
  have hRK : R ≤ exactCore c K := le_tightCore_of_isPGroup (le_inf hR.1 hRc') hR.2.1
  exact hRK hzR

end Core

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer
