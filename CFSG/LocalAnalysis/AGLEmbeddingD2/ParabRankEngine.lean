module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.RealThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabRealThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo

public section

namespace CFSG.AGLEmbeddingD2.ParabRankEngine

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbeddingD2.ParabRealThree
  CFSG.AGLEmbeddingD2.RealThreeRank
open scoped commutatorElement

variable {K Y : Type*} [Group K] [Group Y]

@[expose] def RealThreeOver (π : K →* Y) (Λ : Subgroup K) (J : Subgroup Y) : Prop :=
  ∃ g ∈ ⁅Λ, Λ⁆, π g ∈ J ∧ g ^ 3 = 1 ∧ g ∉ Subgroup.center K ∧ ∃ w ∈ Λ, w * g * w⁻¹ = g⁻¹

theorem mul_eq_inv_commutatorElement {x y : K} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (h3 : (x * y) ^ 3 = 1) : x * y = ⁅x, y⁆⁻¹ := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq, hx])
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq, hy])
  rw [commutatorElement_def, hx', hy', eq_inv_iff_mul_eq_one]
  calc x * y * (x * y * x * y) = (x * y) ^ 3 := by
        rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, pow_add, pow_add, pow_one]
        group
    _ = 1 := h3

theorem RealThreeOver.of_involutions {π : K →* Y} {Λ : Subgroup K} {J : Subgroup Y} {x y : K}
    (hx : x ∈ Λ) (hy : y ∈ Λ) (hxJ : π x ∈ J) (hyJ : π y ∈ J) (hx2 : x ^ 2 = 1)
    (hy2 : y ^ 2 = 1) (h3 : (x * y) ^ 3 = 1) (hc : x * y ∉ Subgroup.center K) :
    RealThreeOver π Λ J := by
  refine ⟨x * y, ?_, by rw [map_mul]; exact mul_mem hxJ hyJ, h3, hc, x, hx,
    conj_mul_eq_inv_of_sq hx2 hy2⟩
  rw [mul_eq_inv_commutatorElement hx2 hy2 h3]
  exact inv_mem (Subgroup.commutator_mem_commutator hx hy)

theorem realThreeOver_rankOne {D : UniversalRootDatum K} {H : Fin D.rank → Subgroup K}
    {π : K →* Y} {J : Subgroup Y} (hBJ : borel D H ≤ J.comap π) {i : Fin D.rank}
    (hi : i ∈ negIndices D (J.comap π)) (hr : HasRealOrderThree D i) :
    RealThreeOver π (rankOne D.rootGroup i) J := by
  obtain ⟨x, hx, y, hy, hx2, hy2, h3, c, hc⟩ := hr
  have hL := rankOne_le_of_mem_negIndices hBJ hi
  have hxL : x ∈ rankOne D.rootGroup i := le_sup_left (a := D.rootGroup (Pi.single i 1)) hx
  have hyL : y ∈ rankOne D.rootGroup i := le_sup_right (b := D.rootGroup (-Pi.single i 1)) hy
  refine RealThreeOver.of_involutions hxL hyL (hL hxL) (hL hyL) hx2 hy2 h3 fun hz => hc ?_
  exact (Subgroup.mem_center_iff.mp hz c).symm

theorem RealThreeOver.conj {π : K →* Y} {Λ : Subgroup K} {J : Subgroup Y}
    (h : RealThreeOver π Λ J) {k : K} (hk : π k ∈ J) :
    RealThreeOver π (Λ.map (MulAut.conj k).toMonoidHom) J := by
  obtain ⟨g, hg, hgJ, hg3, hgc, w, hw, hwg⟩ := h
  refine ⟨k * g * k⁻¹, ?_, ?_, ?_, fun hz => hgc ?_, k * w * k⁻¹, ⟨w, hw, rfl⟩, ?_⟩
  · rw [← Subgroup.map_commutator]
    exact ⟨g, hg, rfl⟩
  · rw [map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem hk hgJ) (inv_mem hk)
  · rw [conj_pow, hg3, mul_one, mul_inv_cancel]
  · rw [Subgroup.mem_center_iff] at hz ⊢
    intro a
    have := hz (k * a * k⁻¹)
    have e : k * g * k⁻¹ * (k * a * k⁻¹) = k * (g * a) * k⁻¹ := by group
    have e' : k * a * k⁻¹ * (k * g * k⁻¹) = k * (a * g) * k⁻¹ := by group
    rw [e, e'] at this
    exact mul_left_cancel (mul_right_cancel this)
  · calc k * w * k⁻¹ * (k * g * k⁻¹) * (k * w * k⁻¹)⁻¹ = k * (w * g * w⁻¹) * k⁻¹ := by group
      _ = (k * g * k⁻¹)⁻¹ := by rw [hwg]; group

section Engine

variable {X : Type*} [Group X] [Finite X] {π : K →* Y} {J : Subgroup Y}

theorem commute_map_of_commutes {Λ₁ Λ₂ : Subgroup K}
    (h : CFSG.AGLEmbedding.ParabPrime.Commutes Λ₁ Λ₂) :
    ∀ a ∈ Λ₁.map π, ∀ b ∈ Λ₂.map π, Commute a b := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  change π a * π b = π b * π a
  rw [← map_mul, ← map_mul, h a ha b hb]

omit [Finite X] in
theorem RealThreeOver.image (hπker : π.ker ≤ Subgroup.center K) {Λ : Subgroup K}
    (h : RealThreeOver π Λ J) (ρ : X →* Y) (hρ : Function.Surjective ρ) :
    ∃ g ∈ ⁅Λ.map π, Λ.map π⁆, g ∈ (J.comap ρ).map ρ ∧ g ^ 3 = 1 ∧ g ≠ 1 ∧
      ∃ w ∈ Λ.map π, w * g * w⁻¹ = g⁻¹ := by
  obtain ⟨g, hg, hgJ, hg3, hgc, w, hw, hwg⟩ := h
  refine ⟨π g, ?_, ?_, by rw [← map_pow, hg3, map_one], fun h1 => hgc (hπker h1), π w,
    ⟨w, hw, rfl⟩, by rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, hwg]⟩
  · rw [← Subgroup.map_commutator]
    exact ⟨g, hg, rfl⟩
  · rw [Subgroup.map_comap_eq_self_of_surjective hρ]
    exact hgJ

theorem three_le_pRank_of_triple (hπker : π.ker ≤ Subgroup.center K) (ρ : X →* Y)
    (hρ : Function.Surjective ρ) (hρker : ρ.ker ≤ Subgroup.center X) {Λ₁ Λ₂ Λ₃ : Subgroup K}
    (c12 : CFSG.AGLEmbedding.ParabPrime.Commutes Λ₁ Λ₂)
    (c13 : CFSG.AGLEmbedding.ParabPrime.Commutes Λ₁ Λ₃)
    (c23 : CFSG.AGLEmbedding.ParabPrime.Commutes Λ₂ Λ₃)
    (h₁ : RealThreeOver π Λ₁ J) (h₂ : RealThreeOver π Λ₂ J) (h₃ : RealThreeOver π Λ₃ J) :
    3 ≤ CFSG.Open.pRank 3 (J.comap ρ) := by
  obtain ⟨g₁, hg₁, hP₁, h3₁, h1₁, w₁, -, hi₁⟩ := h₁.image hπker ρ hρ
  obtain ⟨g₂, hg₂, hP₂, h3₂, h1₂, w₂, hw₂, hi₂⟩ := h₂.image hπker ρ hρ
  obtain ⟨g₃, hg₃, hP₃, h3₃, h1₃, w₃, hw₃, hi₃⟩ := h₃.image hπker ρ hρ
  have hkP : ρ.ker ≤ J.comap ρ := fun z hz => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hz]
    exact one_mem J
  exact three_le_pRank_of_real_triple ρ hρ hρker hkP (commute_map_of_commutes c12)
    (commute_map_of_commutes c13) (commute_map_of_commutes c23) hg₁ hg₂ hg₃ hP₁ hP₂ hP₃
    h3₁ h3₂ h3₃ h1₁ h1₂ h1₃ hw₂ hw₃ hi₁ hi₂ hi₃

theorem three_le_pRank_of_pair (hπker : π.ker ≤ Subgroup.center K) (ρ : X →* Y)
    (hρ : Function.Surjective ρ) (hρker : ρ.ker ≤ Subgroup.center X)
    (h3 : 3 ∣ Nat.card ρ.ker) {Λ₁ Λ₂ : Subgroup K}
    (c12 : CFSG.AGLEmbedding.ParabPrime.Commutes Λ₁ Λ₂)
    (h₁ : RealThreeOver π Λ₁ J) (h₂ : RealThreeOver π Λ₂ J) :
    3 ≤ CFSG.Open.pRank 3 (J.comap ρ) := by
  obtain ⟨g₁, hg₁, hP₁, h3₁, h1₁, w₁, -, hi₁⟩ := h₁.image hπker ρ hρ
  obtain ⟨g₂, hg₂, hP₂, h3₂, h1₂, w₂, hw₂, hi₂⟩ := h₂.image hπker ρ hρ
  have hkP : ρ.ker ≤ J.comap ρ := fun z hz => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hz]
    exact one_mem J
  exact three_le_pRank_of_real_pair ρ hρ hρker hkP h3 (commute_map_of_commutes c12) hg₁ hg₂
    hP₁ hP₂ h3₁ h3₂ h1₁ h1₂ hi₁ hw₂ hi₂

variable {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

theorem three_le_pRank_of_orth (hext : SteinbergExtras D n H)
    (hπker : π.ker ≤ Subgroup.center K) (ρ : X →* Y) (hρ : Function.Surjective ρ)
    (hρker : ρ.ker ≤ Subgroup.center X) (hBJ : borel D H ≤ J.comap π)
    (hr : ∀ i, HasRealOrderThree D i) {a b c : Fin D.rank} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (cab : D.cartan a b = 0) (cac : D.cartan a c = 0) (cbc : D.cartan b c = 0)
    (ha : a ∈ negIndices D (J.comap π)) (hb : b ∈ negIndices D (J.comap π))
    (hc : c ∈ negIndices D (J.comap π)) : 3 ≤ CFSG.Open.pRank 3 (J.comap ρ) :=
  three_le_pRank_of_triple hπker ρ hρ hρker (commutes_rankOne_of_cartan_eq_zero hext hab cab)
    (commutes_rankOne_of_cartan_eq_zero hext hac cac)
    (commutes_rankOne_of_cartan_eq_zero hext hbc cbc) (realThreeOver_rankOne hBJ ha (hr a))
    (realThreeOver_rankOne hBJ hb (hr b)) (realThreeOver_rankOne hBJ hc (hr c))

end Engine

end CFSG.AGLEmbeddingD2.ParabRankEngine
