module

public import CFSG.ClassicalInvolution.Asc77.AscC25X4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer

namespace C25X

section Layer

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G}


theorem zStar_of_connected {S : Sylow 2 G} {R R' : Subgroup G} {t u₁ u₂ : G}
    (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haR : ∀ x ∈ R, a * x = x * a) (haR' : ∀ x ∈ R', a * x = x * a)
    (hconn : ∀ L ∈ oddQuotientFamily (exactPair Ω a),
      L = T7H.exactImg Ω a K ∨ L = T7H.exactImg Ω a K') :
    z ∈ zStarOf (Subgroup.centralizer ({a} : Set G)) := by
  classical
  obtain ⟨hzY, -, -, hK₂, hK₂', -⟩ := layer_a_frame hyp ha2 ha1 haR haR'
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hzK : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one ha2
  have hz2 : z * z = 1 := hzK.sq
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  set H := Subgroup.centralizer ({a} : Set G) with hH
  set Y := exactLayer Ω a with hY
  have hzH : z ∈ H := exactLayer_le_centralizer Ω a hzY
  have hBN : ∀ b ∈ H, b ∈ Subgroup.normalizer (oddCoreOf Y : Set G) := fun b hb =>
    T7L.mem_normalizer_oddCoreOf
      (mem_normalizer_iff_conjSub_eq.mpr (conjSub_exactLayer hΩ.conjInvariant hb))
  have hOY : oddCoreOf Y ≤ oddCoreOf H :=
    Balance.le_oddCoreIn_of_normalizes
      ((oddCoreOf_le_self Y).trans (exactLayer_le_centralizer Ω a)) hBN (oddCoreOf_odd_natCard _)
  have key : ∀ c ∈ H, z * (c * z * c⁻¹) ∈ oddCoreOf Y := by
    intro c hc
    have hKc : conjSub c K ∈ tqMembers Ω a :=
      conjSub_mem_tqMembers hΩ.conjInvariant hc hK₂
    have hzc : IsUniqueInvolution (conjSub c K) (c * z * c⁻¹) := hzK.conj c
    have hz'c : c * z * c⁻¹ ∈ exactCore a (conjSub c K) :=
      (T7H.isUniqueInvolution_exactCore hp hΩ hcpg hKc hzc).mem
    have hz'Y : c * z * c⁻¹ ∈ Y := exactCore_le_exactLayer hKc hz'c
    have hbar := T7H.exactImg_isUnique hp hΩ hcpg hKc hzc hz'Y
    have hmem := T7H.exactImg_mem hKc
    have hbarK := T7H.exactImg_isUnique hp hΩ hcpg hK₂ hzK hzY
    have hbarK' := T7H.exactImg_isUnique hp hΩ hcpg hK₂' hzK' hzY
    have heq : T7H.toBar Ω a (c * z * c⁻¹) hz'Y = T7H.toBar Ω a z hzY := by
      rcases hconn _ hmem with h | h
      · rw [h] at hbar
        exact hbar.eq hbarK
      · rw [h] at hbar
        exact hbar.eq hbarK'
    have h1 : (⟨c * z * c⁻¹, hz'Y⟩ : ↥Y)⁻¹ * ⟨z, hzY⟩ ∈ classicalInvolutionOddCore ↥Y :=
      QuotientGroup.eq.mp heq
    have h2 : (c * z * c⁻¹)⁻¹ * z ∈ oddCoreOf Y := Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
    have h3 := (oddCoreOf Y).inv_mem h2
    have e : ((c * z * c⁻¹)⁻¹ * z)⁻¹ = z * (c * z * c⁻¹) := by
      rw [mul_inv_rev, inv_inv, hzinv]
    rwa [e] at h3
  unfold zStarOf
  refine Subgroup.mem_map.mpr ⟨⟨z, hzH⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro c
  obtain ⟨c0, rfl⟩ := QuotientGroup.mk_surjective c
  rw [← QuotientGroup.mk'_apply (classicalInvolutionOddCore ↥H) c0, ← map_mul, ← map_mul,
    QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have hk := hOY (key (c0 : G)⁻¹ (H.inv_mem c0.2))
  obtain ⟨y, hy, hyval⟩ := Subgroup.mem_map.mp hk
  have hyval' : (y : G) = z * ((c0 : G)⁻¹ * z * ((c0 : G)⁻¹)⁻¹) := hyval
  have e : (c0 * (⟨z, hzH⟩ : ↥H))⁻¹ * (⟨z, hzH⟩ * c0) = y := by
    apply Subtype.ext
    rw [hyval']
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, mul_inv_rev, hzinv, mul_assoc]
  rw [e]
  exact hy

theorem layer_a_typed (hmf : NC4Fact p) {S : Sylow 2 G} {R R' : Subgroup G} {t u₁ u₂ : G}
    (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haR : ∀ x ∈ R, a * x = x * a) (haR' : ∀ x ∈ R', a * x = x * a) :
    z ∈ zStarOf (Subgroup.centralizer ({a} : Set G)) ∨ LayerOrthType p f Ω a 5 true ∨
      LayerOrthType p f Ω a 6 (!piSign p f) := by
  rcases layer_a_tag hmf hyp ha2 ha1 haR haR' with h | h
  · exact Or.inl (zStar_of_connected hyp ha2 ha1 haR haR' h)
  · exact Or.inr h

end Layer

end C25X

end CFSG.ClassicalInvolution.Asc77
