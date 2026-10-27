module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDWedgeCheck
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDSetting
public import Mathlib.Algebra.CharP.Pi

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup Matrix

variable {G : Type*} [Group G]

theorem hom_wedge_A₁_of_coords {d : Data G} (hz2 : d.z * d.z = 1) (hzA : d.z ∈ d.A₁)
    (κ : G → (Fin 8 → ZMod 2))
    (hκmul : ∀ a ∈ d.A₁, ∀ b ∈ d.A₁, κ (a * b) = κ a + κ b)
    (hκker : ∀ a ∈ d.A₁, κ a = 0 ↔ a ∈ zpowers d.z)
    (hκsurj : ∀ v, ∃ a ∈ d.A₁, κ a = v)
    (gens : Fin 5 → G) (hgK : ∀ g, gens g ∈ d.K₁)
    (hgA : ∀ g, ∀ a ∈ d.A₁, gens g * a * (gens g)⁻¹ ∈ d.A₁)
    (hκconj : ∀ g, ∀ a ∈ d.A₁, κ (gens g * a * (gens g)⁻¹) = wedgeMatN g *ᵥ κ a) :
    ∀ β : G → G → G, (∀ a ∈ d.A₁, ∀ b ∈ d.A₁, β a b ∈ d.A₁) →
    (∀ a ∈ d.A₁, ∀ a' ∈ d.A₁, ∀ b ∈ d.A₁,
      (β a b * β a' b)⁻¹ * β (a * a') b ∈ zpowers d.z) →
    (∀ a ∈ d.A₁, ∀ b ∈ d.A₁, ∀ b' ∈ d.A₁,
      (β a b * β a b')⁻¹ * β a (b * b') ∈ zpowers d.z) →
    (∀ a ∈ d.A₁, β a a ∈ zpowers d.z) →
    (∀ b ∈ d.A₁, β d.z b ∈ zpowers d.z) →
    (∀ k ∈ d.K₁, ∀ a ∈ d.A₁, ∀ b ∈ d.A₁,
      (k * β a b * k⁻¹)⁻¹ * β (k * a * k⁻¹) (k * b * k⁻¹) ∈ zpowers d.z) →
    ∀ a ∈ d.A₁, ∀ b ∈ d.A₁, β a b ∈ zpowers d.z := by
  intro β hβA hβ₁ hβ₂ hβ₃ hβ₄ hβ₅
  have c2 : ∀ u v : Fin 8 → ZMod 2, u + v = 0 → v = u := fun u v huv => by
    calc v = (u + u) + v := by rw [CharTwo.add_self_eq_zero, zero_add]
      _ = u + (u + v) := by rw [add_assoc]
      _ = u := by rw [huv, add_zero]
  have hκ1 : κ 1 = 0 := (hκker 1 (one_mem _)).mpr (one_mem _)
  have hκinv : ∀ a ∈ d.A₁, κ a⁻¹ = κ a := fun a ha => by
    have := hκmul a ha a⁻¹ (inv_mem ha)
    rw [mul_inv_cancel, hκ1] at this
    exact c2 _ _ this.symm
  have hκz : ∀ {x y : G}, x ∈ d.A₁ → y ∈ d.A₁ → x⁻¹ * y ∈ zpowers d.z → κ y = κ x := by
    intro x y hx hy hxy
    have h0 := (hκker _ (mul_mem (inv_mem hx) hy)).mpr hxy
    rw [hκmul _ (inv_mem hx) _ hy, hκinv x hx] at h0
    exact c2 _ _ h0
  have hκeq : ∀ {x y : G}, x ∈ d.A₁ → y ∈ d.A₁ → κ x = κ y → x⁻¹ * y ∈ zpowers d.z := by
    intro x y hx hy hxy
    refine (hκker _ (mul_mem (inv_mem hx) hy)).mp ?_
    rw [hκmul _ (inv_mem hx) _ hy, hκinv x hx, hxy, CharTwo.add_self_eq_zero]
  have hzpA : ∀ {c : G}, c ∈ zpowers d.z → c ∈ d.A₁ := fun hc => (zpowers_le.mpr hzA) hc
  have B1 : ∀ {a a' b : G}, a ∈ d.A₁ → a' ∈ d.A₁ → b ∈ d.A₁ →
      κ (β (a * a') b) = κ (β a b) + κ (β a' b) := by
    intro a a' b ha ha' hb
    rw [hκz (mul_mem (hβA a ha b hb) (hβA a' ha' b hb)) (hβA _ (mul_mem ha ha') b hb)
      (hβ₁ a ha a' ha' b hb), hκmul _ (hβA a ha b hb) _ (hβA a' ha' b hb)]
  have B2 : ∀ {a b b' : G}, a ∈ d.A₁ → b ∈ d.A₁ → b' ∈ d.A₁ →
      κ (β a (b * b')) = κ (β a b) + κ (β a b') := by
    intro a b b' ha hb hb'
    rw [hκz (mul_mem (hβA a ha b hb) (hβA a ha b' hb')) (hβA _ ha _ (mul_mem hb hb'))
      (hβ₂ a ha b hb b' hb'), hκmul _ (hβA a ha b hb) _ (hβA a ha b' hb')]
  have B3 : ∀ {a : G}, a ∈ d.A₁ → κ (β a a) = 0 := fun ha => (hκker _ (hβA _ ha _ ha)).mpr
    (hβ₃ _ ha)
  have B4 : ∀ {b : G}, b ∈ d.A₁ → κ (β d.z b) = 0 := fun hb => (hκker _ (hβA _ hzA _ hb)).mpr
    (hβ₄ _ hb)
  have B5 : ∀ {b : G}, b ∈ d.A₁ → κ (β 1 b) = 0 := fun hb => by
    have := B1 (one_mem _) (one_mem _) hb
    rw [mul_one] at this
    exact (add_eq_left.mp this.symm)
  have B6 : ∀ {a b : G}, a ∈ d.A₁ → b ∈ d.A₁ → κ (β b a) = κ (β a b) := by
    intro a b ha hb
    have h1 := B3 (mul_mem ha hb)
    rw [B1 ha hb (mul_mem ha hb), B2 ha ha hb, B2 hb ha hb, B3 ha, B3 hb, zero_add,
      add_zero] at h1
    exact c2 _ _ h1
  have B7 : ∀ {a a' b : G}, a ∈ d.A₁ → a' ∈ d.A₁ → b ∈ d.A₁ → a⁻¹ * a' ∈ zpowers d.z →
      κ (β a' b) = κ (β a b) := by
    intro a a' b ha ha' hb haa
    have e : a' = a * (a⁻¹ * a') := by group
    rw [e, B1 ha (hzpA haa) hb]
    have hc1 : a⁻¹ * a' = 1 ∨ a⁻¹ * a' = d.z := by
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp haa
      rw [← hn, zpow_eq_zpow_emod n (show d.z ^ (2 : ℤ) = 1 by rw [zpow_two, hz2])]
      rcases Int.emod_two_eq_zero_or_one n with h | h <;> rw [h]
      · left; rw [zpow_zero]
      · right; rw [zpow_one]
    rcases hc1 with e1 | e1
    · rw [e1, B5 hb, add_zero]
    · rw [e1, B4 hb, add_zero]
  have B7' : ∀ {a b b' : G}, a ∈ d.A₁ → b ∈ d.A₁ → b' ∈ d.A₁ → b⁻¹ * b' ∈ zpowers d.z →
      κ (β a b') = κ (β a b) := by
    intro a b b' ha hb hb' hbb
    rw [← B6 ha hb', ← B6 ha hb]
    exact B7 hb hb' ha hbb
  have B8 : ∀ (g : Fin 5) {a b : G}, a ∈ d.A₁ → b ∈ d.A₁ →
      κ (β (gens g * a * (gens g)⁻¹) (gens g * b * (gens g)⁻¹)) = wedgeMatN g *ᵥ κ (β a b) := by
    intro g a b ha hb
    rw [hκz (hgA g _ (hβA a ha b hb)) (hβA _ (hgA g a ha) _ (hgA g b hb))
      (hβ₅ _ (hgK g) a ha b hb), hκconj g _ (hβA a ha b hb)]
  choose σ hσA hσκ using hκsurj
  have hσ : ∀ {a : G}, a ∈ d.A₁ → (σ (κ a))⁻¹ * a ∈ zpowers d.z := fun ha =>
    hκeq (hσA _) ha (hσκ _)
  set β' : (Fin 8 → ZMod 2) → (Fin 8 → ZMod 2) → (Fin 8 → ZMod 2) :=
    fun u v => κ (β (σ u) (σ v)) with hβ'
  have hzero := hom_wedge_N β'
    (fun u u' v => by
      simp only [hβ']
      rw [B7 (mul_mem (hσA u) (hσA u')) (hσA _) (hσA v)
        (hκeq (mul_mem (hσA u) (hσA u')) (hσA _) (by rw [hκmul _ (hσA u) _ (hσA u'), hσκ, hσκ,
          hσκ])), B1 (hσA u) (hσA u') (hσA v)])
    (fun u v v' => by
      simp only [hβ']
      rw [B7' (hσA u) (mul_mem (hσA v) (hσA v')) (hσA _)
        (hκeq (mul_mem (hσA v) (hσA v')) (hσA _) (by rw [hκmul _ (hσA v) _ (hσA v'), hσκ, hσκ,
          hσκ])), B2 (hσA u) (hσA v) (hσA v')])
    (fun u => B3 (hσA u))
    (fun g u v => by
      simp only [hβ']
      rw [B7 (hgA g _ (hσA u)) (hσA _) (hσA _) (hκeq (hgA g _ (hσA u)) (hσA _)
          (by rw [hκconj g _ (hσA u), hσκ, hσκ])),
        B7' (hgA g _ (hσA u)) (hgA g _ (hσA v)) (hσA _) (hκeq (hgA g _ (hσA v)) (hσA _)
          (by rw [hκconj g _ (hσA v), hσκ, hσκ])), B8 g (hσA u) (hσA v)])
  intro a ha b hb
  refine (hκker _ (hβA a ha b hb)).mp ?_
  have h1 := hzero (κ a) (κ b)
  simp only [hβ'] at h1
  rwa [← B7 (hσA _) ha (hσA _) (hσ ha), ← B7' ha (hσA _) hb (hσ hb)] at h1

theorem hom_wedge_A₄_of_coords {d : Data G} (κ : G → (Fin 4 → ZMod 2))
    (hκmul : ∀ a ∈ d.A₄, ∀ b ∈ d.A₄, κ (a * b) = κ a + κ b)
    (hκker : ∀ a ∈ d.A₄, κ a = 0 → a = 1)
    (hκsurj : ∀ v, ∃ a ∈ d.A₄, κ a = v)
    (gens : Fin 3 → G) (hgΛ : ∀ g, gens g ∈ d.Λ)
    (hgA : ∀ g, ∀ a ∈ d.A₄, gens g * a * (gens g)⁻¹ ∈ d.A₄)
    (hκconj : ∀ g, ∀ a ∈ d.A₄, κ (gens g * a * (gens g)⁻¹) = wedgeMatW g *ᵥ κ a) :
    ∀ β : G → G → G, (∀ a ∈ d.A₄, ∀ b ∈ d.A₄, β a b ∈ d.A₄) →
    (∀ a ∈ d.A₄, ∀ b ∈ d.A₄, ∀ c ∈ d.A₄, β (a * b) c = β a c * β b c) →
    (∀ a ∈ d.A₄, ∀ b ∈ d.A₄, ∀ c ∈ d.A₄, β a (b * c) = β a b * β a c) →
    (∀ a ∈ d.A₄, β a a = 1) →
    (∀ l ∈ d.Λ, ∀ a ∈ d.A₄, ∀ b ∈ d.A₄, β (l * a * l⁻¹) (l * b * l⁻¹) = l * β a b * l⁻¹) →
    ∀ a ∈ d.A₄, ∀ b ∈ d.A₄, β a b = 1 := by
  intro β hβA hβ₁ hβ₂ hβ₃ hβ₄
  have hκ1 : κ 1 = 0 := by
    have := hκmul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    exact (add_eq_left.mp this.symm)
  have hκinj : ∀ {x y : G}, x ∈ d.A₄ → y ∈ d.A₄ → κ x = κ y → x = y := by
    intro x y hx hy hxy
    have hxi : κ x⁻¹ = κ x := by
      have := hκmul x hx x⁻¹ (inv_mem hx)
      rw [mul_inv_cancel, hκ1] at this
      calc κ x⁻¹ = (κ x + κ x) + κ x⁻¹ := by rw [CharTwo.add_self_eq_zero, zero_add]
        _ = κ x + (κ x + κ x⁻¹) := by rw [add_assoc]
        _ = κ x := by rw [← this, add_zero]
    have h0 : κ (x⁻¹ * y) = 0 := by
      rw [hκmul _ (inv_mem hx) _ hy, hxi, hxy, CharTwo.add_self_eq_zero]
    have := hκker _ (mul_mem (inv_mem hx) hy) h0
    calc x = x * (x⁻¹ * y) := by rw [this, mul_one]
      _ = y := by group
  choose σ hσA hσκ using hκsurj
  have hσ : ∀ {a : G}, a ∈ d.A₄ → σ (κ a) = a := fun ha => hκinj (hσA _) ha (hσκ _)
  set β' : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) :=
    fun u v => κ (β (σ u) (σ v)) with hβ'
  have hσmul : ∀ u v, σ (u + v) = σ u * σ v := fun u v => hκinj (hσA _)
    (mul_mem (hσA u) (hσA v)) (by rw [hσκ, hκmul _ (hσA u) _ (hσA v), hσκ, hσκ])
  have hzero := hom_wedge_W β'
    (fun u u' v => by
      simp only [hβ']
      rw [hσmul, hβ₁ _ (hσA u) _ (hσA u') _ (hσA v), hκmul _ (hβA _ (hσA u) _ (hσA v)) _
        (hβA _ (hσA u') _ (hσA v))])
    (fun u v v' => by
      simp only [hβ']
      rw [hσmul, hβ₂ _ (hσA u) _ (hσA v) _ (hσA v'), hκmul _ (hβA _ (hσA u) _ (hσA v)) _
        (hβA _ (hσA u) _ (hσA v'))])
    (fun u => by simp only [hβ']; rw [hβ₃ _ (hσA u), hκ1])
    (fun g u v => by
      simp only [hβ']
      have hgu : σ (wedgeMatW g *ᵥ u) = gens g * σ u * (gens g)⁻¹ := by
        rw [← hσκ u, ← hκconj g _ (hσA u), hσ (hgA g _ (hσA u)), hσκ]
      have hgv : σ (wedgeMatW g *ᵥ v) = gens g * σ v * (gens g)⁻¹ := by
        rw [← hσκ v, ← hκconj g _ (hσA v), hσ (hgA g _ (hσA v)), hσκ]
      rw [hgu, hgv, hβ₄ _ (hgΛ g) _ (hσA u) _ (hσA v), hκconj g _ (hβA _ (hσA u) _ (hσA v))])
  intro a ha b hb
  have h1 := hzero (κ a) (κ b)
  simp only [hβ', hσ ha, hσ hb] at h1
  exact hκker _ (hβA a ha b hb) h1

end CFSG.EvenSmallLie.UnitarySix.YamadaD
