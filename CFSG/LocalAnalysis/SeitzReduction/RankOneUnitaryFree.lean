module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiEndingBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarGroups
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryCharBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

section General

variable {G : Type*} [Group G]

theorem exists_eq_or_eq_mul_t_of_mem_sup_zpowers {H : Subgroup G} {t : G} (ht2 : t ^ 2 = 1)
    (htH : t ∈ normalizer (H : Set G)) {x : G} (hx : x ∈ H ⊔ zpowers t) :
    ∃ h ∈ H, x = h ∨ x = h * t := by
  have hzN : zpowers t ≤ normalizer (H : Set G) := zpowers_le.mpr htH
  have hx' : x ∈ ((H ⊔ zpowers t : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left _ _ hzN] at hx'
  obtain ⟨h, hh, z, hz, rfl⟩ := Set.mem_mul.mp hx'
  rcases mem_zpowers_involution_eq_one_or_eq ht2 hz with rfl | rfl
  · exact ⟨h, hh, Or.inl (mul_one h)⟩
  · exact ⟨h, hh, Or.inr rfl⟩

theorem conj_t_of_mem_sup_zpowers_of_free {U₁ R₂ : Subgroup G} {t : G} (ht2 : t ^ 2 = 1)
    (htU₁ : t ∈ normalizer (U₁ : Set G)) (htR₂ : t ∈ normalizer (R₂ : Set G)) (hR₂U₁ : R₂ ≤ U₁)
    (hR₂2 : ∀ r ∈ R₂, r ^ 2 = 1)
    (hU₁c : ∀ x ∈ U₁, ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ R₂) (hU₁2 : ∀ x ∈ U₁, x ^ 2 ∈ R₂)
    (hfreeR₂ : ∀ r ∈ R₂, t * r * t⁻¹ = r → ∃ s ∈ R₂, s * t * s⁻¹ * t⁻¹ = r)
    (hfreeU₁ : ∀ x ∈ U₁, t * x * t⁻¹ * x⁻¹ ∈ R₂ → ∃ w ∈ U₁, (w * t * w⁻¹ * t⁻¹)⁻¹ * x ∈ R₂)
    (hnot : ∀ g : G, g * t * g⁻¹ ∉ U₁) (g : G) (hg : g * t * g⁻¹ ∈ U₁ ⊔ zpowers t) :
    ∃ u ∈ U₁, g * t * g⁻¹ = u * t * u⁻¹ := by
  have htt : t * t = 1 := by rw [← sq, ht2]
  obtain ⟨x, hx, hxe | hxe⟩ := exists_eq_or_eq_mul_t_of_mem_sup_zpowers ht2 htU₁ hg
  · exact absurd (hxe ▸ hx) (hnot g)
  · have hinv : x * t * (x * t) = 1 := by
      rw [← hxe]
      calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [htt]; group
    obtain ⟨w, hw, hwx⟩ := conj_of_free_series htt htR₂ hR₂U₁
      (fun r hr => by rw [← sq]; exact hR₂2 r hr) hU₁c (fun x hx => by rw [← sq]; exact hU₁2 x hx)
      hfreeR₂ hfreeU₁ hx hinv
    exact ⟨w, hw, by rw [hxe, hwx]⟩


theorem conj_t_not_mem_centralizer_of_card {G : Type*} [Group G] [Finite G] {t : G}
    {R₂ U₁ : Subgroup G} {q : ℕ} (hR₂card : Nat.card R₂ = q ^ 2) (hR₂2 : ∀ r ∈ R₂, r ^ 2 = 1)
    (hR₂c : ∀ x ∈ R₂, ∀ y ∈ R₂, x * y = y * x) (ht2 : t ^ 2 = 1)
    (hU₁C : U₁ ≤ centralizer (R₂ : Set G)) (hU₁2 : IsPGroup 2 U₁)
    (hbound : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({t} : Set G) →
      Nat.card P < Nat.card U₁)
    (hel : ∀ B : Subgroup G, B ≤ centralizer ({t} : Set G) → (∀ x ∈ B, x ^ 2 = 1) →
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → Nat.card B < 2 * q ^ 2)
    (g : G) : g * t * g⁻¹ ∉ centralizer (R₂ : Set G) := by
  intro hx
  obtain ⟨x, hxdef⟩ : ∃ x : G, x = g * t * g⁻¹ := ⟨_, rfl⟩
  rw [← hxdef] at hx
  have hx2 : x ^ 2 = 1 := by
    rw [hxdef, sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * t ^ 2 * g⁻¹ by rw [sq]; group, ht2]
    group
  have htx : t = g⁻¹ * x * g⁻¹⁻¹ := by rw [hxdef]; group
  by_cases hxR : x ∈ R₂
  · have hU₁x : U₁ ≤ centralizer ({x} : Set G) := fun u hu =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hU₁C hu) x hxR).symm
    exact conj_ne_of_card_le hU₁2 hU₁x le_rfl (fun Q hQ hQt => hbound Q hQ hQt) g⁻¹ htx.symm
  · set B := R₂ ⊔ zpowers x with hB
    have hxN : x ∈ normalizer (R₂ : Set G) := centralizer_le_normalizer _ hx
    have hBR : B ≤ centralizer (R₂ : Set G) :=
      sup_le (fun r hr => mem_centralizer_iff.mpr fun r' hr' => hR₂c r' hr' r hr)
        (zpowers_le.mpr hx)
    have hBx : B ≤ centralizer ({x} : Set G) :=
      sup_le (fun r hr => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx r hr))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
    have hBel : ∀ y ∈ B, y ^ 2 = 1 := by
      intro y hy
      obtain ⟨r, hr, hyr | hyr⟩ := exists_eq_or_eq_mul_t_of_mem_sup_zpowers hx2 hxN hy
      · rw [hyr]
        exact hR₂2 r hr
      · have hrx : Commute r x := mem_centralizer_iff.mp hx r hr
        rw [hyr, hrx.mul_pow, hR₂2 r hr, hx2, one_mul]
    have hBc : ∀ y ∈ B, ∀ z ∈ B, y * z = z * y := by
      intro y hy z hz
      obtain ⟨r, hr, hzr | hzr⟩ := exists_eq_or_eq_mul_t_of_mem_sup_zpowers hx2 hxN hz
      · rw [hzr]
        exact (mem_centralizer_iff.mp (hBR hy) r hr).symm
      · rw [hzr]
        have h1 : r * y = y * r := mem_centralizer_iff.mp (hBR hy) r hr
        have h2 : y * x = x * y := mem_centralizer_singleton_iff.mp (hBx hy)
        calc y * (r * x) = r * y * x := by rw [h1, mul_assoc]
          _ = r * x * y := by rw [mul_assoc, h2, ← mul_assoc]
    have hR₂B : R₂ ≤ B := le_sup_left
    have hxB : x ∈ B := mem_sup_right (mem_zpowers x)
    have hcardB : 2 * q ^ 2 ≤ Nat.card B := by
      obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hR₂B
      have hpos : 0 < Nat.card B := Nat.card_pos
      have hq : 0 < Nat.card R₂ := Nat.card_pos
      have hm1 : m ≠ 1 := by
        rintro rfl
        rw [mul_one] at hm
        exact hxR ((Subgroup.eq_of_le_of_card_ge hR₂B hm.le).symm ▸ hxB)
      have hm0 : m ≠ 0 := by
        rintro rfl
        omega
      rw [hm, ← hR₂card]
      have : 2 ≤ m := by omega
      nlinarith
    set B' := B.map (MulAut.conj g⁻¹).toMonoidHom with hB'
    have hB'card : Nat.card B' = Nat.card B :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    have hB't : B' ≤ centralizer ({t} : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_singleton_iff, htx]
      have h2 : y * x = x * y := mem_centralizer_singleton_iff.mp (hBx hy)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g⁻¹ * y * g⁻¹⁻¹ * (g⁻¹ * x * g⁻¹⁻¹) = g⁻¹ * (y * x) * g⁻¹⁻¹ := by group
        _ = g⁻¹ * (x * y) * g⁻¹⁻¹ := by rw [h2]
        _ = g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) := by group
    have hB'el : ∀ y ∈ B', y ^ 2 = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow, hBel y hy, map_one]
    have hB'c : ∀ y ∈ B', ∀ z ∈ B', y * z = z * y := by
      rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
      rw [← map_mul, ← map_mul, hBc y hy z hz]
    have := hel B' hB't hB'el hB'c
    omega

theorem conj_t_not_mem_of_card {G : Type*} [Group G] [Finite G] {t : G}
    {R₂ U₁ : Subgroup G} {q : ℕ} (hR₂card : Nat.card R₂ = q ^ 2) (hR₂2 : ∀ r ∈ R₂, r ^ 2 = 1)
    (hR₂c : ∀ x ∈ R₂, ∀ y ∈ R₂, x * y = y * x) (ht2 : t ^ 2 = 1)
    (hU₁C : U₁ ≤ centralizer (R₂ : Set G)) (hU₁2 : IsPGroup 2 U₁)
    (hbound : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({t} : Set G) →
      Nat.card P < Nat.card U₁)
    (hel : ∀ B : Subgroup G, B ≤ centralizer ({t} : Set G) → (∀ x ∈ B, x ^ 2 = 1) →
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → Nat.card B < 2 * q ^ 2)
    (g : G) : g * t * g⁻¹ ∉ U₁ := fun hg =>
  conj_t_not_mem_centralizer_of_card hR₂card hR₂2 hR₂c ht2 hU₁C hU₁2 hbound hel g (hU₁C hg)

end General

namespace U3R2

variable {G : Type} [Group G] [Finite G] {L T₁ R₂ : Subgroup G} {t : G} {f : ℕ}

theorem conj_t_of_mem_sup_zpowers (hR : U3R2 G L T₁ R₂ t f) {U₁ : Subgroup G}
    (htU₁ : t ∈ normalizer (U₁ : Set G)) (hR₂U₁ : R₂ ≤ U₁) (hR₂2 : ∀ r ∈ R₂, r ^ 2 = 1)
    (hU₁c : ∀ x ∈ U₁, ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ R₂) (hU₁2 : ∀ x ∈ U₁, x ^ 2 ∈ R₂)
    (hfix : ∀ x ∈ U₁, t * x * t⁻¹ * x⁻¹ ∈ R₂ → x ∈ T₁ ⊔ R₂)
    (hcov : ∀ w ∈ T₁, ∃ u ∈ U₁, ∃ r ∈ R₂, u * t * u⁻¹ = r * w * t)
    (hnot : ∀ g : G, g * t * g⁻¹ ∉ U₁) (g : G) (hg : g * t * g⁻¹ ∈ U₁ ⊔ zpowers t) :
    ∃ u ∈ U₁, g * t * g⁻¹ = u * t * u⁻¹ := by
  refine conj_t_of_mem_sup_zpowers_of_free hR.t_sq htU₁ hR.t_mem_normalizer hR₂U₁ hR₂2 hU₁c hU₁2
    (fun r hr hrt => ?_) (fun x hx hxt => ?_) hnot g hg
  · obtain ⟨s, hs, hsr⟩ := hR.rho_onto r (hR.rho_ker r hr (by
      calc r * t = t * r * t⁻¹ * t := by rw [hrt]
        _ = t * r := by group))
    exact ⟨s, hs, by rw [hR.t_inv]; exact hsr⟩
  · obtain ⟨w, hw, r₀, hr₀, rfl⟩ := hR.mem_sup_iff.mp (hfix x hx hxt)
    obtain ⟨u, hu, r, hr, hut⟩ := hcov w hw
    refine ⟨u, hu, ?_⟩
    have hwr : w * r = r * w := hR.commT₁ w hw r hr
    have e : (u * t * u⁻¹ * t⁻¹)⁻¹ * (w * r₀) = r⁻¹ * r₀ := by
      rw [hut]
      calc (r * w * t * t⁻¹)⁻¹ * (w * r₀) = (r * w)⁻¹ * (w * r₀) := by group
        _ = (w * r)⁻¹ * (w * r₀) := by rw [hwr]
        _ = r⁻¹ * r₀ := by group
    rw [e]
    exact mul_mem (inv_mem hr) hr₀

end U3R2

end CFSG.SeitzReduction.RankOne
