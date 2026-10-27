module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7FourInvol
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7FourAlg

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Module

variable {G : Type*} [Group G] {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q]

theorem end_add_self (x : Module.End (ZMod 2) Q) : x + x = 0 := by
  have : (2 : ZMod 2) = 0 := rfl
  rw [← two_smul (ZMod 2) x, this, zero_smul]

theorem nilMap_mul_self (ρ : Representation (ZMod 2) G Q) {g : G} (hg : g ^ 2 = 1) :
    nilMap ρ g * nilMap ρ g = 0 := by
  ext v
  exact nilMap_sq ρ hg v

theorem rho_eq_one_add (ρ : Representation (ZMod 2) G Q) (g : G) :
    ρ g = 1 + nilMap ρ g := by
  show ρ g = 1 + (ρ g - 1)
  abel

theorem rank_one_sandwich (α β : Module.End (ZMod 2) Q)
    (h : finrank (ZMod 2) (LinearMap.range α) = 1) :
    α * β * α = α ∨ α * β * α = 0 := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 h
  obtain ⟨d, hd⟩ := hv ⟨α (β (v : Q)), ⟨β (v : Q), rfl⟩⟩
  have hd' : α (β (v : Q)) = d • (v : Q) := (congrArg Subtype.val hd).symm
  have key : α * β * α = d • α := by
    ext x
    obtain ⟨c, hc⟩ := hv ⟨α x, ⟨x, rfl⟩⟩
    have hc' : α x = c • (v : Q) := (congrArg Subtype.val hc).symm
    simp only [Module.End.mul_apply, LinearMap.smul_apply]
    rw [hc', map_smul, map_smul, hd', smul_smul, smul_smul, mul_comm]
  rcases (by decide : ∀ d : ZMod 2, d = 0 ∨ d = 1) d with rfl | rfl
  · right; rw [zero_smul] at key; exact key
  · left; rw [one_smul] at key; exact key

theorem finrank_range_nilMap_conj_le (ρ : Representation (ZMod 2) G Q) [Finite Q] (c t : G) :
    finrank (ZMod 2) (LinearMap.range (nilMap ρ (c * t * c⁻¹))) ≤
      finrank (ZMod 2) (LinearMap.range (nilMap ρ t)) := by
  have : Module.Finite (ZMod 2) Q := Module.Finite.of_finite
  have hle : LinearMap.range (nilMap ρ (c * t * c⁻¹)) ≤
      (LinearMap.range (nilMap ρ t)).map (ρ c) := by
    rintro _ ⟨v, rfl⟩
    refine ⟨nilMap ρ t (ρ c⁻¹ v), ⟨ρ c⁻¹ v, rfl⟩, ?_⟩
    have h1 : ρ c (ρ c⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul]; simp
    simp only [nilMap_apply, map_sub, h1, map_mul, Module.End.mul_apply]
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_map_le _ _)

theorem finrank_range_nilMap_isConj [Finite Q] (ρ : Representation (ZMod 2) G Q) {a b : G}
    (h : IsConj a b) :
    finrank (ZMod 2) (LinearMap.range (nilMap ρ b)) ≤
      finrank (ZMod 2) (LinearMap.range (nilMap ρ a)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc]
  exact finrank_range_nilMap_conj_le ρ c a

theorem nilMap_ne_zero (ρ : Representation (ZMod 2) G Q) (hρ : Function.Injective ρ) {t : G}
    (ht : t ≠ 1) : nilMap ρ t ≠ 0 := by
  intro h
  apply ht
  apply hρ
  rw [rho_eq_one_add ρ t, h, add_zero, map_one]

theorem one_le_finrank_range [Finite Q] (ρ : Representation (ZMod 2) G Q)
    (hρ : Function.Injective ρ) {t : G} (ht : t ≠ 1) :
    1 ≤ finrank (ZMod 2) (LinearMap.range (nilMap ρ t)) := by
  have : Module.Finite (ZMod 2) Q := Module.Finite.of_finite
  by_contra hlt
  have h0 : finrank (ZMod 2) (LinearMap.range (nilMap ρ t)) = 0 := by omega
  have : LinearMap.range (nilMap ρ t) = ⊥ := Submodule.finrank_eq_zero.1 h0
  exact nilMap_ne_zero ρ hρ ht (LinearMap.range_eq_bot.1 this)

theorem two_le_finrank_range_nilMap [Finite Q] (ρ : Representation (ZMod 2) G Q)
    (hρ : Function.Injective ρ)
    (hconj : ∀ a b : G, a ≠ 1 → a ^ 2 = 1 → b ≠ 1 → b ^ 2 = 1 → IsConj a b)
    (h5 : ∃ a b : G, a ≠ 1 ∧ a ^ 2 = 1 ∧ b ≠ 1 ∧ b ^ 2 = 1 ∧ orderOf (a * b) = 5)
    {t : G} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) :
    2 ≤ finrank (ZMod 2) (LinearMap.range (nilMap ρ t)) := by
  by_contra hlt
  have ht : finrank (ZMod 2) (LinearMap.range (nilMap ρ t)) = 1 := by
    have := one_le_finrank_range ρ hρ ht1
    omega
  have hrank : ∀ s : G, s ≠ 1 → s ^ 2 = 1 →
      finrank (ZMod 2) (LinearMap.range (nilMap ρ s)) = 1 := by
    intro s hs1 hs2
    have h1 := finrank_range_nilMap_isConj ρ (hconj t s ht1 ht2 hs1 hs2)
    have h2 := one_le_finrank_range ρ hρ hs1
    omega
  obtain ⟨a, b, ha1, ha2, hb1, hb2, hab⟩ := h5
  have hra := hrank a ha1 ha2
  have hrb := hrank b hb1 hb2
  have hα := nilMap_mul_self ρ ha2
  have hβ := nilMap_mul_self ρ hb2
  have hcases := order_cases (R := Module.End (ZMod 2) Q) end_add_self hα hβ
    (nilMap_ne_zero ρ hρ ha1) (nilMap_ne_zero ρ hρ hb1)
    (rank_one_sandwich _ (nilMap ρ b) hra) (rank_one_sandwich _ (nilMap ρ a) hrb)
  have hu : (1 + nilMap ρ a) * (1 + nilMap ρ b) = ρ (a * b) := by
    rw [← rho_eq_one_add, ← rho_eq_one_add, map_mul]
  rw [hu, ← map_pow, ← map_pow] at hcases
  have hone : ∀ n : ℕ, ρ ((a * b) ^ n) = 1 → orderOf (a * b) ∣ n := by
    intro n hn
    apply orderOf_dvd_of_pow_eq_one
    apply hρ
    rw [hn, map_one]
  rcases hcases with h | h
  · have := hone 3 (by rw [h])
    rw [hab] at this
    omega
  · have := hone 4 (by rw [h])
    rw [hab] at this
    omega

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
