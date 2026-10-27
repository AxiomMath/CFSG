module

public import CFSG.ClassicalInvolution.Asc77.AscC25V16

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open scoped MatrixGroups commutatorElement

theorem exists_orderOf_four_of_cyclic {Y : Type} [Group Y] [Finite Y] {U R₀ : Subgroup Y}
    (hUR : U ≤ R₀) (hcyc : IsCyclic ↥U) (hidx : U.relIndex R₀ = 2) (h8 : 8 ≤ Nat.card R₀)
    (h2 : IsPGroup 2 ↥R₀) : ∃ y ∈ U, orderOf y = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2) (G := ↥R₀)).mp h2
  have hcardU : Nat.card U * 2 = Nat.card R₀ := by
    have h1 := Subgroup.card_mul_index (U.subgroupOf R₀)
    have e : Nat.card (U.subgroupOf R₀) = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUR).toEquiv
    rw [e] at h1
    rw [← h1]
    congr 1
    exact hidx.symm
  have hm3 : 3 ≤ m := by
    by_contra hlt
    push Not at hlt
    have : Nat.card R₀ ≤ 2 ^ 2 := by
      rw [hm]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hU : Nat.card U = 2 ^ (m - 1) := by
    have : 2 ^ m = 2 ^ (m - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥U)
  have hog : orderOf g = 2 ^ (m - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hU]
  refine ⟨((g ^ (2 ^ (m - 3)) : ↥U) : Y), (g ^ (2 ^ (m - 3))).2, ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_pow_of_dvd (by positivity), hog]
  · have : 2 ^ (m - 1) = 2 ^ (m - 3) * 4 := by
      rw [show m - 1 = (m - 3) + 2 by omega, pow_add]; norm_num
    rw [this]
    exact Nat.mul_div_cancel_left _ (by positivity)
  · rw [hog]
    exact pow_dvd_pow 2 (by omega)

section AE

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem genSection_conjFamily {Y₀ : Type} [Group Y₀] [Finite Y₀] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {L : Subgroup Y₀} {z : Y₀} (hL : IsClassicalMember p f L z)
    (hΛ : HypOmegaMod p f (conjFamily L)) (hA : ∀ M ∈ conjFamily L, AEmpty (conjFamily L) M) :
    GenSection p f (oddQuotientFamily (restrictFamily (conjFamily L) (conjGen L))) := by
  set X := conjGen L with hX
  set N₀ : Subgroup ↥X := classicalInvolutionOddCore ↥X with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΛ₁ : HypOmegaMod p f (restrictFamily (conjFamily L) X) := hΛ.restrict X
  have hΛ' : HypOmegaMod p f (quotFamily (restrictFamily (conjFamily L) X) N₀) :=
    oddQuotHyp p f hp hq ↥X _ hΛ₁ N₀ hN₀odd
  have hΛA : ∀ M ∈ restrictFamily (conjFamily L) X,
      AEmpty (restrictFamily (conjFamily L) X) M := by
    rintro _ ⟨M, hM, hMY, rfl⟩
    exact AEmpty.restrict hp hΛ hMY (hA M hM)
  exact
    { hyp := hΛ'
      oddCore := CFSG.ComponentClassification.OddCore.quotient_corefree ↥X
      gen := omegaGen_quotFamily_of_gen _ N₀ (inClass_restrict_conjugates hL).generated
      aEmpty := aEmpty_quotFamily hp hq hΛ₁ hΛ' hN₀odd hΛA }

theorem aEmpty_conjFamily_perfectCore
    (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') {a : G} {e₀ : ℕ} (hp' : p ≠ 2)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hmem : IsClassicalMember p e₀ (perfectCoreIn K' a) ⟨z, hzA⟩) :
    ∀ M ∈ conjFamily (perfectCoreIn K' a), AEmpty (conjFamily (perfectCoreIn K' a)) M := by
  classical
  have hΛ : HypOmegaMod p e₀ (conjFamily (perfectCoreIn K' a)) :=
    fs_hypOmegaMod_conjFamily h.hΩ h.hK' h.hz' hzA hmem
  rintro M ⟨c₁, rfl⟩ J hJstar hJnbr zK zJ hzK hzJ
  exfalso
  apply hJnbr
  obtain ⟨hJΛ, hJne, U, hU, hUJ, hUN⟩ := hJstar
  obtain ⟨c₂, rfl⟩ := hJΛ
  obtain ⟨R₀, hR₀, hUR₀, hUcyc, hUidx⟩ := hU
  obtain ⟨J₃, -, hR₀syl⟩ := exists_isSylow2In_of_mem_RSet hR₀
  have h8 := hΛ.eight_le_of_mem_RSet hp' hR₀
  obtain ⟨y, hyU, hy4⟩ := exists_orderOf_four_of_cyclic hUR₀ hUcyc hUidx h8 hR₀syl.2.1
  have hyJ := hUJ hyU
  have hyN := hUN hyU
  have hy4' : orderOf (y : G) = 4 := by rw [Subgroup.orderOf_coe, hy4]
  have hyK : (y : G) ∈ conjSub (c₂ : G) K' := le_conjSub_of_mem c₂ hyJ
  have hyz : y * zK * y⁻¹ = zK := hzK.conj_eq (mem_normalizer_iff_conjSub_eq.mp hyN)
  have hzK' : (zK : G) = (c₁ : G) * z * (c₁ : G)⁻¹ := fs_coe_eq_of_isUniqueInvolution h.hz' c₁ hzK
  have hzJ' : (zJ : G) = (c₂ : G) * z * (c₂ : G)⁻¹ := fs_coe_eq_of_isUniqueInvolution h.hz' c₂ hzJ
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
  have hJMem : conjSub c₂ (perfectCoreIn K' a) ∈ conjFamily (perfectCoreIn K' a) := ⟨c₂, rfl⟩
  have hMMem : conjSub c₁ (perfectCoreIn K' a) ∈ conjFamily (perfectCoreIn K' a) := ⟨c₁, rfl⟩
  rcases mem_kPerp_of_twin hΛ hJMem hMMem hzJ hzK with hEq | hnbr
  · exact absurd hEq hJne
  · exact hnbr

end AE

end CFSG.ClassicalInvolution.Asc77.C25V
