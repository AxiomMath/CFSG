module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FCore69

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_comm {S : Subgroup G} {g : G} (h : ∀ s ∈ S, g * s = s * g) :
    g ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [h x hx, mul_inv_cancel_right]
    exact hx
  · intro hx
    have h1 := h _ hx
    have h2 : g * (g * x * g⁻¹) = g * x := by
      rw [h1]; group
    have h3 : g * x * g⁻¹ = x := mul_left_cancel h2
    rwa [h3] at hx

theorem core610_Z_le {B R₁ R₂ Z : Subgroup G} (hBel : IsElemAbelian 3 B)
    (hSC : ∀ E : Subgroup G, IsElemAbelian 3 E → B ≤ E → E = B)
    (hR₁exp : ∀ g ∈ R₁, g ^ 3 = 1)
    (hZR : Z ≤ R₁) (hZcent : ∀ z ∈ Z, ∀ r ∈ R₁, z * r = r * z)
    (hR₂ : ∀ r₁ ∈ R₁, ∀ r₂ ∈ R₂, r₁ * r₂ = r₂ * r₁)
    (hBR : ∀ b ∈ B, ∃ r₁ ∈ R₁, ∃ r₂ ∈ R₂, b = r₁ * r₂) : Z ≤ B := by
  intro z hz
  refine mem_of_cube_centralizes hBel hSC (hR₁exp z (hZR hz)) fun b hb => ?_
  obtain ⟨r₁, h1, r₂, h2, rfl⟩ := hBR b hb
  rw [← mul_assoc, hZcent z hz r₁ h1, mul_assoc, hR₂ z (hZR hz) r₂ h2, mul_assoc]

theorem core610_R₁_le {B R₁ R₂ Z : Subgroup G}
    (hBc : Nat.card B = 81) (hR₁c : Nat.card R₁ = 27) (hZc : Nat.card Z = 3)
    (hR₂ : ∀ r₁ ∈ R₁, ∀ r₂ ∈ R₂, r₁ * r₂ = r₂ * r₁) (hR₁R₂ : R₁ ⊓ R₂ = Z)
    (hBR : ∀ b ∈ B, ∃ r₁ ∈ R₁, ∃ r₂ ∈ R₂, b = r₁ * r₂)
    (hBR₂ : B ≤ Subgroup.normalizer (R₂ : Set G))
    (hBcard : Nat.card ↥(B ⊓ R₂) = 9) : R₁ ≤ R₂ ⊔ B := by
  have hR₁N : R₁ ≤ Subgroup.normalizer (R₂ : Set G) := fun r hr =>
    mem_normalizer_of_comm fun s hs => hR₂ r hr s hs
  have h1 := card_sup_mul_card_inf hBR₂
  have h2 := card_sup_mul_card_inf hR₁N
  have hinf1 : Nat.card ↥(R₂ ⊓ B) = 9 := by rw [inf_comm]; exact hBcard
  have hinf2 : Nat.card ↥(R₂ ⊓ R₁) = 3 := by rw [inf_comm, hR₁R₂]; exact hZc
  rw [hinf1, hBc] at h1
  rw [hinf2, hR₁c] at h2
  have hle : R₂ ⊔ B ≤ R₂ ⊔ R₁ := by
    refine sup_le le_sup_left fun b hb => ?_
    obtain ⟨r₁, h1, r₂, h2, rfl⟩ := hBR b hb
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left h2)
  have hcard : Nat.card ↥(R₂ ⊔ R₁) ≤ Nat.card ↥(R₂ ⊔ B) := by omega
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq]
  exact le_sup_right

theorem core610_cent_le {B R₁ R₂ Z : Subgroup G}
    (hZcenter : ∀ z ∈ R₁, (∀ r ∈ R₁, z * r = r * z) → z ∈ Z)
    (hR₂ : ∀ r₁ ∈ R₁, ∀ r₂ ∈ R₂, r₁ * r₂ = r₂ * r₁)
    (hR₁le : R₁ ≤ R₂ ⊔ B) {r : G} (hr : r ∈ R₁) (hrB : ∀ b ∈ B, r * b = b * r) : r ∈ Z := by
  refine hZcenter r hr fun y hy => ?_
  have hB : B ≤ Subgroup.centralizer {r} := fun b hb => by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact hrB b hb
  have hR2 : R₂ ≤ Subgroup.centralizer {r} := fun b hb => by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact hR₂ r hr b hb
  have := sup_le hR2 hB (hR₁le hy)
  rw [Subgroup.mem_centralizer_iff] at this
  exact this r rfl

theorem conj_mul_aux {u r₁ r₂ : G} (hc : u * r₂ = r₂ * u) :
    u * (r₁ * r₂) * u⁻¹ = (u * r₁ * u⁻¹ * r₁⁻¹) * (r₁ * r₂) := by
  have hc' : r₂ * u⁻¹ = u⁻¹ * r₂ := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hc]; group
  calc u * (r₁ * r₂) * u⁻¹ = u * r₁ * (r₂ * u⁻¹) := by group
    _ = u * r₁ * (u⁻¹ * r₂) := by rw [hc']
    _ = _ := by group

theorem comm_mul_aux {u r₁ r₂ : G} (hc : u * r₂ = r₂ * u) :
    u * (r₁ * r₂) * u⁻¹ * (r₁ * r₂)⁻¹ = u * r₁ * u⁻¹ * r₁⁻¹ := by
  rw [conj_mul_aux hc]; group

theorem core610 {B A R₁ R₂ Z : Subgroup G}
    (hBc : Nat.card B = 81) (hBel : IsElemAbelian 3 B)
    (hSC : ∀ E : Subgroup G, IsElemAbelian 3 E → B ≤ E → E = B)
    (hAB : A ≤ B) (hAc : Nat.card A = 9)
    (hR₁c : Nat.card R₁ = 27) (hR₁exp : ∀ g ∈ R₁, g ^ 3 = 1)
    (hZR : Z ≤ R₁) (hZc : Nat.card Z = 3) (hZcent : ∀ z ∈ Z, ∀ r ∈ R₁, z * r = r * z)
    (hZcenter : ∀ z ∈ R₁, (∀ r ∈ R₁, z * r = r * z) → z ∈ Z)
    (hcomm : ∀ a ∈ R₁, ∀ c ∈ R₁, a * c * a⁻¹ * c⁻¹ ∈ Z)
    (hR₂ : ∀ r₁ ∈ R₁, ∀ r₂ ∈ R₂, r₁ * r₂ = r₂ * r₁) (hR₁R₂ : R₁ ⊓ R₂ = Z)
    (hBR : ∀ b ∈ B, ∃ r₁ ∈ R₁, ∃ r₂ ∈ R₂, b = r₁ * r₂)
    (hBR₂ : B ≤ Subgroup.normalizer (R₂ : Set G))
    (hBcard : Nat.card ↥(B ⊓ R₂) = 9) (hAB0 : A ⊓ (B ⊓ R₂) = ⊥)
    (h66v : ∀ U : Subgroup G, U ≤ Subgroup.normalizer (B : Set G) → IsPGroup 3 ↥U →
      Nat.card ↥⁅U, B⁆ = 3 → (⁅U, B⁆ ≤ A ∨ A ≤ Subgroup.centralizer (U : Set G)) ∧
        Nat.card ↥(B ⊓ Subgroup.centralizer (U : Set G)) = 27) : False := by
  have hZB : Z ≤ B := core610_Z_le hBel hSC hR₁exp hZR hZcent hR₂ hBR
  have hR₁le : R₁ ≤ R₂ ⊔ B := core610_R₁_le hBc hR₁c hZc hR₂ hR₁R₂ hBR hBR₂ hBcard
  have hZR₂ : Z ≤ R₂ := hR₁R₂ ▸ inf_le_right
  have hconj : ∀ u ∈ R₁, ∀ b ∈ B, u * b * u⁻¹ ∈ B := by
    intro u hu b hb
    obtain ⟨r₁, h1, r₂, h2, rfl⟩ := hBR b hb
    rw [conj_mul_aux (hR₂ u hu r₂ h2)]
    exact Subgroup.mul_mem _ (hZB (hcomm u hu r₁ h1)) hb
  have hnorm : R₁ ≤ Subgroup.normalizer (B : Set G) := fun u hu => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj u hu x, fun hx => ?_⟩
    have h := hconj u⁻¹ (Subgroup.inv_mem _ hu) _ hx
    have h' : u⁻¹ * (u * x * u⁻¹) * u⁻¹⁻¹ = x := by group
    rwa [h'] at h
  obtain ⟨y, hyR, hyZ⟩ : ∃ y ∈ R₁, y ∉ Z := by
    by_contra hno
    push Not at hno
    have := Subgroup.card_le_of_le (show R₁ ≤ Z from hno)
    omega
  set U := Z ⊔ Subgroup.zpowers y with hU
  have hUR : U ≤ R₁ := sup_le hZR (Subgroup.zpowers_le.2 hyR)
  have hyU : y ∈ U := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hUp : IsPGroup 3 U := fun g =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (hR₁exp _ (hUR g.2))⟩
  have hcommle : ⁅U, B⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro u hu b hb
    obtain ⟨r₁, h1, r₂, h2, rfl⟩ := hBR b hb
    rw [commutatorElement_def, comm_mul_aux (hR₂ u (hUR hu) r₂ h2)]
    exact hcomm u (hUR hu) r₁ h1
  have hcard : Nat.card ↥⁅U, B⁆ = 3 := by
    have hd : Nat.card ↥⁅U, B⁆ ∣ 3 := hZc ▸ Subgroup.card_dvd_of_le hcommle
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exfalso
      have hbot : ⁅U, B⁆ = ⊥ := Subgroup.card_eq_one.1 h
      refine hyZ (core610_cent_le hZcenter hR₂ hR₁le hyR fun b hb => ?_)
      have := Subgroup.commutator_mem_commutator hyU hb
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact h
  have hcZ : ⁅U, B⁆ = Z := Subgroup.eq_of_le_of_card_ge hcommle (by rw [hZc, hcard])
  obtain ⟨hor, hD⟩ := h66v U (hUR.trans hnorm) hUp hcard
  rcases hor with hA | hA
  · have hle : Z ≤ A ⊓ (B ⊓ R₂) := le_inf (hcZ ▸ hA) (le_inf hZB hZR₂)
    rw [hAB0] at hle
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_bot] at this
    omega
  · have hAD : A ≤ B ⊓ Subgroup.centralizer (U : Set G) := le_inf hAB hA
    have hB2D : B ⊓ R₂ ≤ B ⊓ Subgroup.centralizer (U : Set G) :=
      le_inf inf_le_left fun x hx => by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact hR₂ h (hUR hh) x hx.2
    have hsup : A ⊔ (B ⊓ R₂) ≤ B ⊓ Subgroup.centralizer (U : Set G) := sup_le hAD hB2D
    have hN : B ⊓ R₂ ≤ Subgroup.normalizer (A : Set G) := fun x hx =>
      mem_normalizer_of_comm fun s hs =>
        comm_of_isMulCommutative hBel.1 x hx.1 s (hAB hs)
    have h1 := card_sup_mul_card_inf hN
    rw [hAB0, Subgroup.card_bot, hAc, hBcard] at h1
    have h2 := Subgroup.card_le_of_le hsup
    omega

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
