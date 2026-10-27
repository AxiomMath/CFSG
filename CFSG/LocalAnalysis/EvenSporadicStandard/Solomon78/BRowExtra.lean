module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.CenterAt

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

theorem CenterInvAt.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {a : X}
    (h : CenterInvAt a) : CenterInvAt (e a) := by
  intro z hzz hzc
  have h1 := h (e.symm z) (by rw [← map_mul, hzz, map_one]) (by
    intro y hy
    apply e.injective
    rw [map_mul, map_mul]
    have := hzc (e y) (by rw [← map_mul, ← map_mul, hy])
    simpa using this)
  rcases h1 with h1 | h1
  · left
    simpa using congrArg e h1
  · right
    simpa using congrArg e h1

variable {G : Type*} [Group G]

section Twist

variable {Q : Subgroup G} {x w : G}

theorem tw_inv (hx2 : x * x = 1) (hxc : ∀ q ∈ Q, q * x = x * q) {a : G} (ha : a ∈ Q)
    (h : w * a = x * (a * w)) : w * a⁻¹ = x * (a⁻¹ * w) := by
  have e1 : a * w = x * (w * a) := by rw [h, ← mul_assoc, hx2, one_mul]
  calc w * a⁻¹ = a⁻¹ * (a * w) * a⁻¹ := by group
    _ = a⁻¹ * (x * (w * a)) * a⁻¹ := by rw [e1]
    _ = (a⁻¹ * x) * w := by group
    _ = (x * a⁻¹) * w := by rw [hxc a⁻¹ (Q.inv_mem ha)]
    _ = x * (a⁻¹ * w) := by group

theorem tw_mul_tw (hx2 : x * x = 1) (hxc : ∀ q ∈ Q, q * x = x * q) {a b : G} (ha : a ∈ Q)
    (hwa : w * a = x * (a * w)) (hwb : w * b = x * (b * w)) : w * (a * b) = (a * b) * w := by
  calc w * (a * b) = (w * a) * b := by group
    _ = x * (a * w) * b := by rw [hwa]
    _ = x * a * (w * b) := by group
    _ = x * a * (x * (b * w)) := by rw [hwb]
    _ = (x * a * x) * (b * w) := by group
    _ = (a * x * x) * (b * w) := by rw [← hxc a ha]
    _ = a * b * w := by rw [mul_assoc a x x, hx2, mul_one]; group

theorem tw_conj_un (hx2 : x * x = 1) (hxc : ∀ q ∈ Q, q * x = x * q) {a t : G} (ha : a ∈ Q)
    (ht : t ∈ Q) (hwa : w * a = x * (a * w)) (hwai : w * a⁻¹ = x * (a⁻¹ * w))
    (hwt : w * t = t * w) : w * (a * t * a⁻¹) = (a * t * a⁻¹) * w := by
  have hxat : a * t * x = x * (a * t) := hxc (a * t) (Q.mul_mem ha ht)
  calc w * (a * t * a⁻¹) = (w * a) * t * a⁻¹ := by group
    _ = (x * (a * w)) * t * a⁻¹ := by rw [hwa]
    _ = x * (a * (w * t) * a⁻¹) := by group
    _ = x * (a * (t * w) * a⁻¹) := by rw [hwt]
    _ = x * (a * t * (w * a⁻¹)) := by group
    _ = x * (a * t * (x * (a⁻¹ * w))) := by rw [hwai]
    _ = (x * (a * t * x)) * (a⁻¹ * w) := by group
    _ = (x * (x * (a * t))) * (a⁻¹ * w) := by rw [hxat]
    _ = (a * t * a⁻¹) * w := by rw [← mul_assoc x x, hx2, one_mul]; group

end Twist

theorem eq_of_normalizes_centralizer_extraspecial (Q : Subgroup G) {x w g : G} (hx2 : x * x = 1)
    (hx1 : x ≠ 1)
    (hxc : ∀ q ∈ Q, q * x = x * q)
    (hZ : ∀ q ∈ Q, (∀ y ∈ Q, q * y = y * q) → q = 1 ∨ q = x)
    (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a ∨ a * b = x * (b * a))
    (hwQ : w ∈ Q) (hw2 : w * w = 1)
    (hCQ : ∀ c : G, (∀ q ∈ Q, c * q = q * c) → c ∈ Q)
    (hgN : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hgx : g * x = x * g)
    (hgT : ∀ t ∈ Q, w * t = t * w → g * t = t * g) :
    g = 1 ∨ g = x ∨ g = w ∨ g = x * w := by
  by_cases hall : ∀ u ∈ Q, g * u = u * g
  · rcases hZ g (hCQ g hall) (fun y hy => hall y hy) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · push Not at hall
    obtain ⟨u, huQ, hgu⟩ := hall
    have hwu : w * u = x * (u * w) := by
      rcases hcomm w hwQ u huQ with h | h
      · exact absurd (hgT u huQ h) hgu
      · exact h
    have hu₁Q : g * u * g⁻¹ ∈ Q := hgN u huQ
    have hwu₁ : w * (g * u * g⁻¹) = x * ((g * u * g⁻¹) * w) := by
      rcases hcomm w hwQ _ hu₁Q with h | h
      · exfalso
        have h1 := hgT _ hu₁Q h
        apply hgu
        calc g * u = g⁻¹ * (g * (g * u * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * u * g⁻¹) * g) * g := by rw [h1]
          _ = u * g := by group
      · exact h
    have hwui : w * u⁻¹ = x * (u⁻¹ * w) := tw_inv hx2 hxc huQ hwu
    have hδQ : u⁻¹ * (g * u * g⁻¹) ∈ Q := Q.mul_mem (Q.inv_mem huQ) hu₁Q
    have hδw : w * (u⁻¹ * (g * u * g⁻¹)) = (u⁻¹ * (g * u * g⁻¹)) * w :=
      tw_mul_tw hx2 hxc (Q.inv_mem huQ) hwui hwu₁
    obtain ⟨δ, hδ⟩ : ∃ δ, δ = u⁻¹ * (g * u * g⁻¹) := ⟨_, rfl⟩
    rw [← hδ] at hδQ hδw
    have hu₁δ : g * u * g⁻¹ = u * δ := by rw [hδ]; group
    have hδT : ∀ t ∈ Q, w * t = t * w → δ * t = t * δ := by
      intro t htQ htw
      have hwutu : w * (u * t * u⁻¹) = (u * t * u⁻¹) * w :=
        tw_conj_un hx2 hxc huQ htQ hwu hwui htw
      have h1 := hgT _ (Q.mul_mem (Q.mul_mem huQ htQ) (Q.inv_mem huQ)) hwutu
      have hgt : g * t = t * g := hgT t htQ htw
      have hgt' : g⁻¹ * t = t * g⁻¹ := by
        calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * t) * g⁻¹ := by rw [hgt]
          _ = t * g⁻¹ := by group
      have hh : u⁻¹ * g * u * t = t * (u⁻¹ * g * u) := by
        calc u⁻¹ * g * u * t = u⁻¹ * (g * (u * t * u⁻¹)) * u := by group
          _ = u⁻¹ * ((u * t * u⁻¹) * g) * u := by rw [h1]
          _ = t * (u⁻¹ * g * u) := by group
      rw [hδ]
      calc u⁻¹ * (g * u * g⁻¹) * t = u⁻¹ * g * u * (g⁻¹ * t) := by group
        _ = u⁻¹ * g * u * (t * g⁻¹) := by rw [hgt']
        _ = (u⁻¹ * g * u * t) * g⁻¹ := by group
        _ = (t * (u⁻¹ * g * u)) * g⁻¹ := by rw [hh]
        _ = t * (u⁻¹ * (g * u * g⁻¹)) := by group
    have hD : ∀ c : G, (∀ t ∈ Q, w * t = t * w → c * t = t * c) → c * u = u * c →
        ∀ q ∈ Q, c * q = q * c := by
      intro c hcT hcu q hq
      rcases hcomm w hwQ q hq with h | h
      · exact hcT q hq h
      · have hq' : q * u⁻¹ ∈ Q := Q.mul_mem hq (Q.inv_mem huQ)
        have hwq' : w * (q * u⁻¹) = (q * u⁻¹) * w := tw_mul_tw hx2 hxc hq h hwui
        have h1 := hcT _ hq' hwq'
        calc c * q = c * (q * u⁻¹) * u := by group
          _ = (q * u⁻¹) * c * u := by rw [h1]
          _ = (q * u⁻¹) * (c * u) := by group
          _ = (q * u⁻¹) * (u * c) := by rw [hcu]
          _ = q * c := by group
    have hxu : u * x = x * u := hxc u huQ
    rcases hcomm δ hδQ u huQ with hδu | hδu
    ·
      have hδall : ∀ q ∈ Q, δ * q = q * δ := hD δ hδT hδu
      rcases hZ δ hδQ hδall with h1 | h1
      · exfalso
        apply hgu
        rw [h1, mul_one] at hu₁δ
        calc g * u = (g * u * g⁻¹) * g := by group
          _ = u * g := by rw [hu₁δ]
      ·
        have hcT : ∀ t ∈ Q, w * t = t * w → (g * w) * t = t * (g * w) := by
          intro t htQ htw
          calc g * w * t = g * (w * t) := by group
            _ = g * (t * w) := by rw [htw]
            _ = (g * t) * w := by group
            _ = (t * g) * w := by rw [hgT t htQ htw]
            _ = t * (g * w) := by group
        have hcu : (g * w) * u = u * (g * w) := by
          have hgu' : g * u = x * (u * g) := by
            calc g * u = (g * u * g⁻¹) * g := by group
              _ = (u * x) * g := by rw [hu₁δ, h1]
              _ = x * (u * g) := by rw [hxu]; group
          calc g * w * u = g * (w * u) := by group
            _ = g * (x * (u * w)) := by rw [hwu]
            _ = (g * x) * (u * w) := by group
            _ = (x * g) * (u * w) := by rw [hgx]
            _ = x * ((g * u) * w) := by group
            _ = x * ((x * (u * g)) * w) := by rw [hgu']
            _ = (x * x) * (u * (g * w)) := by group
            _ = u * (g * w) := by rw [hx2, one_mul]
        have hall' := hD (g * w) hcT hcu
        have hgwQ : g * w ∈ Q := hCQ _ hall'
        rcases hZ _ hgwQ hall' with h2 | h2
        · right; right; left
          calc g = (g * w) * w := by rw [mul_assoc, hw2, mul_one]
            _ = w := by rw [h2, one_mul]
        · right; right; right
          calc g = (g * w) * w := by rw [mul_assoc, hw2, mul_one]
            _ = x * w := by rw [h2]
    ·
      exfalso
      have hδx : δ * x = x * δ := hxc δ hδQ
      have hcT : ∀ t ∈ Q, w * t = t * w → (δ * w) * t = t * (δ * w) := by
        intro t htQ htw
        calc δ * w * t = δ * (w * t) := by group
          _ = δ * (t * w) := by rw [htw]
          _ = (δ * t) * w := by group
          _ = (t * δ) * w := by rw [hδT t htQ htw]
          _ = t * (δ * w) := by group
      have hcu : (δ * w) * u = u * (δ * w) := by
        calc δ * w * u = δ * (w * u) := by group
          _ = δ * (x * (u * w)) := by rw [hwu]
          _ = (δ * x) * (u * w) := by group
          _ = (x * δ) * (u * w) := by rw [hδx]
          _ = x * ((δ * u) * w) := by group
          _ = x * ((x * (u * δ)) * w) := by rw [hδu]
          _ = (x * x) * (u * (δ * w)) := by group
          _ = u * (δ * w) := by rw [hx2, one_mul]
      have hall' := hD (δ * w) hcT hcu
      have hδwQ : δ * w ∈ Q := Q.mul_mem hδQ hwQ
      have hδδ : δ * δ = 1 := by
        rcases hZ _ hδwQ hall' with h2 | h2
        · have : δ = w := by
            calc δ = (δ * w) * w := by rw [mul_assoc, hw2, mul_one]
              _ = w := by rw [h2, one_mul]
          rw [this, hw2]
        · have : δ = x * w := by
            calc δ = (δ * w) * w := by rw [mul_assoc, hw2, mul_one]
              _ = x * w := by rw [h2]
          have hxw : w * x = x * w := hxc w hwQ
          rw [this]
          calc x * w * (x * w) = x * (w * x) * w := by group
            _ = x * (x * w) * w := by rw [hxw]
            _ = (x * x) * (w * w) := by group
            _ = 1 := by rw [hx2, hw2, one_mul]
      have huu : ∀ q ∈ Q, (u * u) * q = q * (u * u) := by
        intro q hq
        rcases hcomm u huQ q hq with h | h
        · calc u * u * q = u * (u * q) := by group
            _ = u * (q * u) := by rw [h]
            _ = (u * q) * u := by group
            _ = (q * u) * u := by rw [h]
            _ = q * (u * u) := by group
        · have hxq : q * x = x * q := hxc q hq
          calc u * u * q = u * (u * q) := by group
            _ = u * (x * (q * u)) := by rw [h]
            _ = (u * x) * (q * u) := by group
            _ = (x * u) * (q * u) := by rw [hxu]
            _ = x * ((u * q) * u) := by group
            _ = x * ((x * (q * u)) * u) := by rw [h]
            _ = (x * x) * (q * (u * u)) := by group
            _ = q * (u * u) := by rw [hx2, one_mul]
      have hguu : g * (u * u) * g⁻¹ = u * u := by
        rcases hZ (u * u) (Q.mul_mem huQ huQ) huu with h | h
        · rw [h]; group
        · rw [h, hgx]; group
      have hsq : (u * δ) * (u * δ) = u * u := by
        rw [← hu₁δ, ← hguu]; group
      have hsq' : (u * δ) * (u * δ) = x * (u * u) := by
        calc (u * δ) * (u * δ) = u * (δ * u) * δ := by group
          _ = u * (x * (u * δ)) * δ := by rw [hδu]
          _ = (u * x) * (u * (δ * δ)) := by group
          _ = (x * u) * (u * 1) := by rw [hxu, hδδ]
          _ = x * (u * u) := by group
      have : x * (u * u) = 1 * (u * u) := by rw [← hsq', hsq, one_mul]
      exact hx1 (mul_right_cancel this)

end CFSG.EvenSporadicStandard.Solomon78
