module

public import CFSG.ClassicalInvolution.Asc77.AscR10G2Q
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf13Rows
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf51Ambient
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.T3Core CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Uniform CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3T6D


section Layer


theorem tightlyEmbedded_of_layer {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K H Λ : Subgroup G} {z : G} (hΩ : ConjInvariant Ω) (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hHdef : omegaGen (aStar Ω K) = H) (hΛH : Λ ≤ H)
    (hΛN : ∀ g ∈ Subgroup.normalizer (H : Set G), g ∈ Subgroup.normalizer (Λ : Set G))
    (hzΛ : z ∈ Λ) (hconj : ∀ x ∈ Λ, x * x = 1 → x ≠ 1 → ∃ h ∈ Λ, h * z * h⁻¹ = x) :
    TightlyEmbedded Λ := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  refine ⟨even_iff_two_dvd.mpr (hz2 ▸ Subgroup.orderOf_dvd_natCard Λ hzΛ), fun g hg => ?_⟩
  by_contra hnot
  have heven : Even (Nat.card ↥(Λ ⊓ rightConjugate Λ g)) := Nat.not_odd_iff_even.mp hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  have hx' : orderOf (x : G) = 2 := (Subgroup.orderOf_coe x).trans hx
  have hx2 : (x : G) * (x : G) = 1 := by rw [← pow_two]; exact hx' ▸ pow_orderOf_eq_one _
  have hx1 : (x : G) ≠ 1 := fun h => by rw [h, orderOf_one] at hx'; omega
  have hxH : (x : G) ∈ Λ := (Subgroup.mem_inf.mp x.2).1
  have hxg : g * (x : G) * g⁻¹ ∈ Λ :=
    (mem_rightConjugate_iff Λ g x).mp (Subgroup.mem_inf.mp x.2).2
  have hy2 : (g * (x : G) * g⁻¹) * (g * (x : G) * g⁻¹) = 1 := by
    calc (g * (x : G) * g⁻¹) * (g * (x : G) * g⁻¹) = g * ((x : G) * (x : G)) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hy1 : g * (x : G) * g⁻¹ ≠ 1 := fun h => hx1 (by
    have := congrArg (fun w => g⁻¹ * w * g) h
    simpa [mul_assoc] using this)
  obtain ⟨h, hh, hhx⟩ := hconj x hxH hx2 hx1
  obtain ⟨h', hh', hh'y⟩ := hconj _ hxg hy2 hy1
  have hc : h'⁻¹ * g * h * z * (h'⁻¹ * g * h)⁻¹ = z := by
    calc h'⁻¹ * g * h * z * (h'⁻¹ * g * h)⁻¹
        = h'⁻¹ * (g * (h * z * h⁻¹) * g⁻¹) * h' := by group
      _ = h'⁻¹ * (g * (x : G) * g⁻¹) * h' := by rw [hhx]
      _ = h'⁻¹ * (h' * z * h'⁻¹) * h' := by rw [hh'y]
      _ = z := by group
  have hcz : h'⁻¹ * g * h ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hc
  have hHS : H ≤ conjStab (aStar Ω K) := hHdef.symm.le.trans (omegaGen_aStar_le_conjStab hΩ hK)
  have hmem : g ∈ conjStab (aStar Ω K) := by
    have e : g = h' * (h'⁻¹ * g * h) * h⁻¹ := by group
    rw [e]
    exact (conjStab (aStar Ω K)).mul_mem
      ((conjStab (aStar Ω K)).mul_mem (hHS (hΛH hh'))
        (centralizer_le_conjStab_aStar hΩ hK hz hcz))
      ((conjStab (aStar Ω K)).inv_mem (hHS (hΛH hh)))
  apply hg
  have := conjStab_le_normalizer_omegaGen (aStar Ω K) hmem
  rw [show omegaGen (aStar Ω K) = H from hHdef] at this
  exact hΛN g this


theorem frame_false_of_layerSection (h4 : Asc75Theorem4) {T : Type} [Group T] [Finite T]
    [CaseIAmbient T] {R : Subgroup T} {t : T} {J : Subgroup T} {zK zJ : T}
    (hh : FrameCaseIHyps T R t J zK zJ) {H : Subgroup T}
    (hHdef : omegaGen (aStar (CoreAssembly.conjClass R) R) = H) {Λ : Subgroup T} (hΛH : Λ ≤ H)
    (hΛN : ∀ g ∈ Subgroup.normalizer (H : Set T), g ∈ Subgroup.normalizer (Λ : Set T))
    (hq : CFSG.IsQuasisimple (↥Λ ⧸ classicalInvolutionOddCore ↥Λ))
    (hzΛ : zK ∈ Λ) (htΛ : zJ ∈ Λ)
    (hconj : ∀ x ∈ Λ, x * x = 1 → x ≠ 1 → ∃ h ∈ Λ, h * zK * h⁻¹ = x)
    (hk : ∃ k ∈ Λ, k * k = zK ∧ k ^ 4 = 1) (hHn : ¬ Λ.Normal) : False := by
  have hv := hh.viol
  have hΩg : HypOmegaGen (CoreAssembly.conjClass R) := hh.datum.hyp
  have hK : R ∈ CoreAssembly.conjClass R := CoreAssembly.mem_conjClass_self R
  have hz : IsUniqueInvolution R zK := hv.hzK
  have ht : IsUniqueInvolution J zJ := hv.hzJ
  have hT : TightlyEmbedded Λ :=
    tightlyEmbedded_of_layer hΩg.conjInvariant hK hz hHdef hΛH hΛN hzΛ hconj
  have hlay : twoPrimeLayerIn Λ = Λ := twoPrimeLayerIn_eq_self hq
  have hne' : twoPrimeLayerIn Λ ≠ oddCoreIn Λ := by
    rw [hlay]
    intro h
    exact not_mem_oddCoreIn hz (h ▸ hzΛ)
  have hF : IsSimpleGroup (CFSG.generalizedFitting T) :=
    CaseIAmbient.isSimpleGroup_generalizedFitting
  rcases h4 T Λ hT hne' with hBn | ⟨hr, -⟩ | ⟨g, hg, P, hPs, hPN, n, hn, φ, hφ, hker⟩
  · exact false_of_normalIn_twoPrimeLayerIn_top hT hHn hF hne' hBn
  · rw [hlay] at hr
    have h2 := two_le_pRank_of_commuting hz.sq ht.sq hz.ne_one ht.ne_one
      (AViol.ne_involution_gen hΩg hK hv).symm (AViol.comm_gen hΩg hv) hzΛ htΛ
    omega
  · obtain ⟨k, hkΛ, hkk, hk4⟩ := hk
    have hkC : k ∈ oUpperTwoPrime (Λ ⊔ P) :=
      Subgroup.subset_closure ⟨(le_sup_left : Λ ≤ Λ ⊔ P) hkΛ, 2, by simpa using hk4⟩
    have hzC : zK ∈ oUpperTwoPrime (Λ ⊔ P) :=
      Subgroup.subset_closure ⟨(le_sup_left : Λ ≤ Λ ⊔ P) hzΛ, 1, by simpa [pow_two] using hz.sq⟩
    set k' : ↥(oUpperTwoPrime (Λ ⊔ P)) := ⟨k, hkC⟩ with hk'
    set z' : ↥(oUpperTwoPrime (Λ ⊔ P)) := ⟨zK, hzC⟩ with hz'
    have hkz : k' ^ 2 = z' := Subtype.ext (by rw [pow_two, Subgroup.coe_mul]; exact hkk)
    have hk'4 : k' ^ 4 = 1 := Subtype.ext (by simpa using hk4)
    have hz1 : φ z' ≠ 1 := by
      intro h
      have hzk : z' ∈ φ.ker := h
      rw [hker, Subgroup.mem_subgroupOf] at hzk
      exact not_mem_oddCoreIn hz hzk
    have h44 : (φ k') ^ 4 = 1 := by rw [← map_pow, hk'4, map_one]
    exact hz1 (by rw [← hkz, map_pow]; exact prod_sq_eq_one_of_pow_four _ h44)


end Layer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
