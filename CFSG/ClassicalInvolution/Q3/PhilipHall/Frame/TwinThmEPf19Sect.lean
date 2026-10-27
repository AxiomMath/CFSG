module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf24RedAE5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Corrected

structure E189RedData {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (k : G)
    (H Y : Subgroup G) (Λ : Set (Subgroup ↥Y)) : Prop where
  yH : Y ≤ H
  kY : K ≤ Y
  jY : conjSub k K ≤ Y
  sub : Λ ⊆ restrictFamily Ω Y
  inv : ConjInvariant Λ
  kΛ : K.subgroupOf Y ∈ Λ
  jΛ : (conjSub k K).subgroupOf Y ∈ Λ
  gen : (⨆ L ∈ Λ, L) = ⊤
  trans : ∀ L ∈ Λ, ∃ y : ↥Y, conjSub y (K.subgroupOf Y) = L
  twin : ∃ K' ∈ twinSet Λ (K.subgroupOf Y), K' ≠ K.subgroupOf Y

@[expose] def E189ReduceQ8' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H → E18_6Q8 → E18_7Q8 → E18_4CQ8 →
    ∀ z t k : G, IsUniqueInvolution K z → t = k * z * k⁻¹ → k ∈ H → z * t = t * z → t ≠ z →
      t ∈ (S : Subgroup G) → conjSub t K ≠ K →
      E189ConclG Ω K H z t ∨
        ∃ (Y : Subgroup G) (Λ : Set (Subgroup ↥Y)), E189RedData Ω K k H Y Λ ∧
          ((∀ L ∈ quotFamily Λ (classicalInvolutionOddCore ↥Y),
              L ∈ dstarComp (quotFamily Λ (classicalInvolutionOddCore ↥Y))
                ((K.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)))) ∨
            Nonempty (TC.Thin.AEIdent (quotFamily Λ (classicalInvolutionOddCore ↥Y)) 5))

@[expose] def E189AE5Q8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H → E18_6Q8 → E18_7Q8 → E18_4CQ8 →
    ∀ z t k : G, IsUniqueInvolution K z → t = k * z * k⁻¹ → k ∈ H → z * t = t * z → t ≠ z →
      conjSub t K ≠ K → ∀ (Y : Subgroup G) (Λ : Set (Subgroup ↥Y)), E189RedData Ω K k H Y Λ →
        Nonempty (TC.Thin.AEIdent Λ 5) → FixesUniqueCoset (z * t) H

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem e18_9Q8_of' (h6 : E18_6Q8) (h7 : E18_7Q8) (h4 : E18_4CQ8) (hred : E189ReduceQ8')
    (hleaf : E189LeafQ8) (hodd : E189OddCoreQ8) (_hae5 : E189AE5Q8) : E18_9Q8 := by
  intro G _ _ Ω K S R W H c z hz h htS htz hzt
  set t : G := h⁻¹ * z * h with ht
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  have hzH : Subgroup.centralizer ({z} : Set G) ≤ H := c.centralizer_le hz
  have ht2 : t * t = 1 := by
    calc (h⁻¹ * z * h) * (h⁻¹ * z * h) = h⁻¹ * (z * z) * h := by group
      _ = 1 := by rw [hz.sq]; group
  have ht1 : t ≠ 1 := by
    intro h1
    apply hz.ne_one
    have : z = h * t * h⁻¹ := by rw [ht]; group
    rw [this, h1]
    group
  have hJ : conjSub h⁻¹ K ∈ Ω := hΩ.conjInvariant h⁻¹ K hK
  have hJt : IsUniqueInvolution (conjSub h⁻¹ K) t := by
    have := hz.conj h⁻¹
    simpa [ht] using this
  have hzt' : z * t = t * z := hzt
  have ha2 : (z * t) * (z * t) = 1 := mul_involution_of_commute hz.sq ht2 hzt'
  have ha1 : z * t ≠ 1 := by
    intro h1
    apply htz
    have : t = z⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, inv_eq_of_mul_eq_one_right hz.sq]
  have hzfix : FixesUniqueCoset z H :=
    fixesUniqueCoset_of_centralizer_le hzH (h7 G Ω K S R W H c z hz.ne_one hz.sq hzH)
  have hKcent : ∀ w ∈ K, z * w = w * z := fun w hw => e189_commute_of_mem hz hw
  have hKH : K ≤ H := fun w hw =>
    hzH (Subgroup.mem_centralizer_singleton_iff.mpr (hKcent w hw).symm)
  have htH : t ∈ H := hzH (Subgroup.mem_centralizer_singleton_iff.mpr hzt'.symm)
  by_cases hnorm : conjSub t K = K
  ·
    rcases e189_caseA hΩ hK hJ hz hJt htz hzt' hnorm with ⟨g, hg⟩ | hperp
    · have e : g * t * g⁻¹ = (g * h⁻¹) * z * (g * h⁻¹)⁻¹ := by rw [ht]; group
      rw [← hg, e]
      exact fixesUniqueCoset_conj hzfix _
    · have hne : conjSub h⁻¹ K ≠ K := fun h' => htz (hJt.eq (by rw [h']; exact hz))
      have hnbr : conjSub h⁻¹ K ∈ omegaNbr Ω K := hperp.resolve_left hne
      have hca := centralizer_le_mul_of_omegaNbr hΩ hK c.hyp.trans hz hzH c.stand.hR.1
        c.stand.hR.2.1 c.stand.hR.2.2 c.stand.hW.1 c.stand.hW.2.1 c.stand.hW.2.2 c.hyp.cent hnbr
        hJt ha1 ha2
      exact fixesUniqueCoset_of_centralizer_le hca (h7 G Ω K S R W H c _ ha1 ha2 hca)
  ·
    obtain ⟨k, hkH, hk⟩ := h7 G Ω K S R W H c z hz.ne_one hz.sq hzH h⁻¹
      (by simpa [ht] using htH)
    have hkt : k * z * k⁻¹ = t := by rw [hk, ht]; simp
    have hJ' : conjSub k K ∈ Ω := hΩ.conjInvariant k K hK
    have hJ'H : conjSub k K ≤ H := by
      have := conjSub_mono (n := k) hKH
      rwa [conjSub_eq_self_of_mem hkH] at this
    have hJ't : IsUniqueInvolution (conjSub k K) t := by
      have := hz.conj k
      rwa [hkt] at this
    have hHn : Nat.card H < Nat.card G := natCard_lt_of_ne_top c.proper
    have hAΩ : ∀ L ∈ Ω, AEmpty Ω L :=
      aEmpty_forall_of_transitive hΩ.conjInvariant (e18_3Q8 G Ω K S R W H c) c.stand.aEmpty
    have hconclG : E189ConclG Ω K H z t ∨ FixesUniqueCoset (z * t) H := by
      rcases hred G Ω K S R W H c h6 h7 h4 z t k hz hkt.symm hkH hzt' htz htS hnorm with
        hG | ⟨Y, Λ, ⟨hYH, hKY, hJY, hΛsub, hΛc, hKΛ, hJΛ, hgen, hT, hE⟩, hcase⟩
      · exact Or.inl hG
      · rcases hcase with hC | hAE5
        · exact Or.inl (e189_apply_q hleaf hodd c.stand.ih hΩ c.stand.cls c.stand.q8 c.stand.two hAΩ
            hHn hK hz hkt.symm Y Λ hYH hKY hJY hΛsub hΛc hKΛ hJΛ hgen hT hC hE hzt' hnorm)
        · exact Or.inr (e189_ae5_quot_fixes h7 c hz hkt.symm hzt' htz hnorm Y Λ hYH hKY hJY hΛsub
            hΛc hKΛ hJΛ hgen hT hE hAE5)
    rcases hconclG with hG | hfix
    swap
    · exact hfix
    unfold E189ConclG at hG
    rcases hG with ⟨K'', hK''tw, -, R₁, R₂, hR₁Ω, hR₁K, hR₂Ω, hR₂K'', hRc, u, x, hu, hu1, hu2, hux, hF⟩ |
      ⟨x, hxH, M', hM'tw, hM'ne, R₁, R₂, hR₁Ω, hR₁K, hR₂Ω, hR₂M', hRc, hcommM⟩
    ·
      obtain ⟨hK''Ω, z', hz'K, hz'K''⟩ := hK''tw
      have hz'z : z' = z := hz'K.eq hz
      subst hz'z
      have hcu := centralizer_le_of_fusion hΩ hK c.hyp.trans hz hzH c.stand.hR.1 c.stand.hR.2.1
        c.stand.hR.2.2 c.stand.hW.1 c.stand.hW.2.1 c.stand.hW.2.2 c.hyp.cent hK''Ω hz'K''
        (Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hR₁Ω hR₁K)
        (Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK''Ω hR₂Ω hR₂K'') hRc hu1 hu2 hF
      have hfu := fixesUniqueCoset_of_centralizer_le hcu (h7 G Ω K S R W H c u hu1 hu2 hcu)
      rw [← hux]
      exact fixesUniqueCoset_conj hfu x
    ·
      have hxK : conjSub x K ∈ Ω := hΩ.conjInvariant x K hK
      have hRsyl : IsSylow2In R K :=
        Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK c.stand.hR.1 c.stand.hR.2.1
      have hRx : IsSylow2In (conjSub x R) (conjSub x K) := hRsyl.conj x
      have hR₁syl : IsSylow2In R₁ (conjSub x K) :=
        Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hxK hR₁Ω hR₁K
      
      obtain ⟨k, hk, hkR⟩ := exists_conjSub_eq_of_isSylow2In hRx hR₁syl
      have hxKH : conjSub x K ≤ H := by
        have := conjSub_mono (n := x) hKH
        rwa [conjSub_eq_self_of_mem hxH] at this
      have hx'H : k * x ∈ H := H.mul_mem (hxKH hk) hxH
      have hKx' : conjSub (k * x) K = conjSub x K := by
        rw [conjSub_mul, conjSub_eq_self_of_mem hk]
      have hRx' : conjSub (k * x) R = R₁ := by rw [conjSub_mul, hkR]
      have cx := c.conj_of_mem hx'H
      rw [hKx', hRx'] at cx
      have hR₂syl : IsSylow2In R₂ M' := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hM'tw.1 hR₂Ω hR₂M'
      have hR₁₂2 : IsPGroup 2 ↥(R₁ ⊔ R₂) :=
        hR₁syl.2.1.to_sup_of_normal_left' hR₂syl.2.1 fun y hy =>
          mem_normalizer_iff_conjSub_eq.mpr
            (conjSub_eq_of_mem_of_commutes hy fun a ha b hb => (hRc b hb a ha).symm)
      have hRA : R₁ ⊔ R₂ ≤ Subgroup.centralizer ({z * t} : Set G) :=
        sup_le (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hcommM r (Subgroup.mem_sup_left hr)))
          (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hcommM r (Subgroup.mem_sup_right hr)))
      have hX : Subgroup.centralizer ({z * t} : Set G) ≠ ⊤ := c.centralizer_ne_top h6 ha1
      have hC := h4 G Ω (conjSub x K) (conjSylow (k * x) S) R₁ (conjSub (k * x) W) H cx M' hM'tw
        hM'ne R₂ hR₂Ω hR₂M' hR₁₂2 (z * t) ha1 ha2 hRA hX
      exact fixesUniqueCoset_of_centralizer_le hC (h7 G Ω K S R W H c _ ha1 ha2 hC)

end Corrected

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
