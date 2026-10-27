module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEOrb1

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

namespace ThmE

section Orb2

variable {G : Type} [Group G]

theorem orb4_inv_conj_conj {d : G} (hd : d * d = 1) (a : G) :
    d * (d * a * d⁻¹) * d⁻¹ = a := by
  have : d * (d * a * d⁻¹) * d⁻¹ = (d * d) * a * (d * d)⁻¹ := by group
  rw [this, hd]
  group

theorem orbit4_core' [Finite G] {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    {K₀ R₀ H S S₁ A : Subgroup G} {t d₁ d₂ : G} (hK₀ : K₀ ∈ Ω) (ht : IsUniqueInvolution K₀ t)
    (hR₀K : R₀ ≤ K₀) (hq8 : IsQuatSub R₀) (hS₁ : IsPGroup 2 S₁) (hR₀S : R₀ ≤ S₁)
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) (hd₁S : d₁ ∈ S₁) (hd₂S : d₂ ∈ S₁)
    (m₁ : conjSub d₁ K₀ ≠ K₀) (m₂ : conjSub d₂ K₀ ≠ K₀) (m₃ : conjSub (d₁ * d₂) K₀ ≠ K₀)
    (hF6 : ∀ v ∈ S₁, v * t = t * v → v ∈ H → v ∈ S)
    (hbad : ∀ u ∈ K₀, orderOf u = 4 → u ∉ H) (hA₁ : d₁ ∈ A)
    (hAN : ∀ c ∈ S, c * t = t * c → c * d₂ = d₂ * c → conjSub c A = A)
    (hAD : ∀ w ∈ A, w * w = 1 → w * t = t * w → w = 1 ∨ w = d₁ ∨ w = d₂ ∨ w = d₁ * d₂) :
    False := by
  obtain ⟨x, hxR, hx4⟩ := hq8.exists_orderOf_four
  obtain ⟨r, hrR, hxr⟩ := orb4_noncentral hq8 hxR hx4
  have hxK : x ∈ K₀ := hR₀K hxR
  have hxS : x ∈ S₁ := hR₀S hxR
  have hxsq : x * x = t := sq_eq_of_orderOf_four ht hxK hx4
  have ht2 : t * t = 1 := ht.sq
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hd₁t := g₁.comm_t
  have hd₂t := g₂.comm_t
  have hd₃t := g₃.comm_t
  have hd₁i : d₁⁻¹ = d₁ := inv_eq_of_mul_eq_one_right g₁.sq
  have hd₂i : d₂⁻¹ = d₂ := inv_eq_of_mul_eq_one_right g₂.sq
  have hd₃i : (d₁ * d₂)⁻¹ = d₁ * d₂ := inv_eq_of_mul_eq_one_right g₃.sq
  have hd₃S : d₁ * d₂ ∈ S₁ := S₁.mul_mem hd₁S hd₂S
  obtain ⟨y₁, hy₁⟩ : ∃ y, y = d₁ * x * d₁⁻¹ := ⟨_, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y, y = d₂ * x * d₂⁻¹ := ⟨_, rfl⟩
  obtain ⟨y₃, hy₃⟩ : ∃ y, y = (d₁ * d₂) * x * (d₁ * d₂)⁻¹ := ⟨_, rfl⟩
  have hy₁R : y₁ ∈ conjSub d₁ R₀ := hy₁ ▸ conj_mem_conjSub hxR
  have hy₂R : y₂ ∈ conjSub d₂ R₀ := hy₂ ▸ conj_mem_conjSub hxR
  have hy₃R : y₃ ∈ conjSub (d₁ * d₂) R₀ := hy₃ ▸ conj_mem_conjSub hxR
  have hxR' : x ∈ conjSub 1 R₀ := by rw [conjSub_one]; exact hxR
  have hrR' : r ∈ conjSub 1 R₀ := by rw [conjSub_one]; exact hrR
  have hconj_eq : ∀ a b : G, conjSub a K₀ = conjSub b K₀ → conjSub (a⁻¹ * b) K₀ = K₀ := by
    intro a b h
    rw [conjSub_mul, ← h, conjSub_inv_conjSub]
  have n01 : conjSub 1 K₀ ≠ conjSub d₁ K₀ := by
    intro h
    have := hconj_eq _ _ h
    rw [inv_one, one_mul] at this
    exact m₁ this
  have n02 : conjSub 1 K₀ ≠ conjSub d₂ K₀ := by
    intro h
    have := hconj_eq _ _ h
    rw [inv_one, one_mul] at this
    exact m₂ this
  have n03 : conjSub 1 K₀ ≠ conjSub (d₁ * d₂) K₀ := by
    intro h
    have := hconj_eq _ _ h
    rw [inv_one, one_mul] at this
    exact m₃ this
  have n12 : conjSub d₁ K₀ ≠ conjSub d₂ K₀ := by
    intro h
    have := hconj_eq _ _ h
    rw [hd₁i] at this
    exact m₃ this
  have n13 : conjSub d₁ K₀ ≠ conjSub (d₁ * d₂) K₀ := by
    intro h
    have := hconj_eq _ _ h
    rw [hd₁i, ← mul_assoc, g₁.sq, one_mul] at this
    exact m₂ this
  have n23 : conjSub d₂ K₀ ≠ conjSub (d₁ * d₂) K₀ := by
    intro h
    have := hconj_eq _ _ h
    have e : d₂⁻¹ * (d₁ * d₂) = d₁ := by
      rw [hd₂i, ← mul_assoc, ← hc, mul_assoc, g₂.sq, mul_one]
    rw [e] at this
    exact m₁ this
  have hcomm := fun {a b : G} (ha : a ∈ S₁) (hb : b ∈ S₁) (hat : a * t = t * a)
    (hbt : b * t = t * b) (hne : conjSub a K₀ ≠ conjSub b K₀) =>
      TwinThmEW.commutes_conj_twins hΩ hK₀ ht hR₀K hS₁ hR₀S ha hb hat hbt hne
  have h1S : (1 : G) ∈ S₁ := S₁.one_mem
  have h1t : (1 : G) * t = t * 1 := by simp
  have c01 := hcomm h1S hd₁S h1t hd₁t n01
  have c02 := hcomm h1S hd₂S h1t hd₂t n02
  have c03 := hcomm h1S hd₃S h1t hd₃t n03
  have c12 := hcomm hd₁S hd₂S hd₁t hd₂t n12
  have c13 := hcomm hd₁S hd₃S hd₁t hd₃t n13
  have c23 := hcomm hd₂S hd₃S hd₂t hd₃t n23
  have hxy₁ : Commute x y₁ := (c01 x hxR' y₁ hy₁R)
  have hxy₂ : Commute x y₂ := (c02 x hxR' y₂ hy₂R)
  have hxy₃ : Commute x y₃ := (c03 x hxR' y₃ hy₃R)
  have hy₁y₂ : Commute y₁ y₂ := (c12 y₁ hy₁R y₂ hy₂R)
  have hy₁y₃ : Commute y₁ y₃ := (c13 y₁ hy₁R y₃ hy₃R)
  have hy₂y₃ : Commute y₂ y₃ := (c23 y₂ hy₂R y₃ hy₃R)
  have hry₁ : Commute r y₁ := (c01 r hrR' y₁ hy₁R)
  have hry₂ : Commute r y₂ := (c02 r hrR' y₂ hy₂R)
  have hry₃ : Commute r y₃ := (c03 r hrR' y₃ hy₃R)
  have hsq : ∀ δ y : G, δ * t = t * δ → y = δ * x * δ⁻¹ → y * y = t := by
    intro δ y hδ hy
    rw [hy]
    calc δ * x * δ⁻¹ * (δ * x * δ⁻¹) = δ * (x * x) * δ⁻¹ := by group
      _ = δ * t * δ⁻¹ := by rw [hxsq]
      _ = t := by rw [hδ]; group
  have hy₁sq : y₁ * y₁ = t := hsq d₁ y₁ hd₁t hy₁
  have hy₂sq : y₂ * y₂ = t := hsq d₂ y₂ hd₂t hy₂
  have hy₃sq : y₃ * y₃ = t := hsq (d₁ * d₂) y₃ hd₃t hy₃
  have hxy₂' : Commute x y₂⁻¹ := hxy₂.inv_right
  have hcc : (x * y₂⁻¹) * (x * y₂⁻¹) = 1 := by
    have e : (x * y₂⁻¹) * (x * y₂⁻¹) = (x * x) * (y₂⁻¹ * y₂⁻¹) := by
      calc (x * y₂⁻¹) * (x * y₂⁻¹) = x * (y₂⁻¹ * x) * y₂⁻¹ := by group
        _ = x * (x * y₂⁻¹) * y₂⁻¹ := by rw [← hxy₂'.eq]
        _ = (x * x) * (y₂⁻¹ * y₂⁻¹) := by group
    rw [e, hxsq]
    have : y₂⁻¹ * y₂⁻¹ = t⁻¹ := by
      rw [← hy₂sq]; group
    rw [this, hti, ht2]
  have hci : (x * y₂⁻¹)⁻¹ = x * y₂⁻¹ := inv_eq_of_mul_eq_one_right hcc
  have hcd₂ : (x * y₂⁻¹) * d₂ = d₂ * (x * y₂⁻¹) := by
    have e1 : d₂ * (x * y₂⁻¹) * d₂⁻¹ = y₂ * x⁻¹ := by
      calc d₂ * (x * y₂⁻¹) * d₂⁻¹ = (d₂ * x * d₂⁻¹) * (d₂ * y₂⁻¹ * d₂⁻¹) := by group
        _ = y₂ * (d₂ * y₂ * d₂⁻¹)⁻¹ := by rw [← hy₂]; group
        _ = y₂ * x⁻¹ := by rw [hy₂, orb4_inv_conj_conj g₂.sq]
    have e2 : y₂ * x⁻¹ = x * y₂⁻¹ := by
      have : (x * y₂⁻¹)⁻¹ = y₂ * x⁻¹ := by group
      rw [← this, hci]
    rw [e2] at e1
    exact (mul_inv_eq_iff_eq_mul.mp e1).symm
  have hsqt : ∀ y : G, y * y = t → y * t = t * y := by
    intro y hy
    calc y * t = y * (y * y) := by rw [hy]
      _ = (y * y) * y := by group
      _ = t * y := by rw [hy]
  have hxt : x * t = t * x := hsqt x hxsq
  have hy₁t : y₁ * t = t * y₁ := hsqt y₁ hy₁sq
  have hy₂t : y₂ * t = t * y₂ := hsqt y₂ hy₂sq
  have hy₃t : y₃ * t = t * y₃ := hsqt y₃ hy₃sq
  have hct : (x * y₂⁻¹) * t = t * (x * y₂⁻¹) := by
    have h1 : Commute x t := hxt
    have h2 : Commute y₂⁻¹ t := (show Commute y₂ t from hy₂t).inv_left
    exact (h1.mul_left h2).eq
  have hy₂S : y₂ ∈ S₁ := hy₂ ▸ S₁.mul_mem (S₁.mul_mem hd₂S hxS) (S₁.inv_mem hd₂S)
  have hcS₁ : x * y₂⁻¹ ∈ S₁ := S₁.mul_mem hxS (S₁.inv_mem hy₂S)
  have hcH : x * y₂⁻¹ ∈ H := by
    apply g₂.cent
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcd₂
  have hcS : x * y₂⁻¹ ∈ S := hF6 _ hcS₁ hct hcH
  have hcA : conjSub (x * y₂⁻¹) A = A := hAN _ hcS hct hcd₂
  have hwA' : (x * y₂⁻¹) * d₁ * (x * y₂⁻¹)⁻¹ * d₁⁻¹ ∈ A := by
    have h1 : (x * y₂⁻¹) * d₁ * (x * y₂⁻¹)⁻¹ ∈ conjSub (x * y₂⁻¹) A := conj_mem_conjSub hA₁
    rw [hcA] at h1
    exact A.mul_mem h1 (A.inv_mem hA₁)
  have e3 : d₁ * y₂ * d₁⁻¹ = y₃ := by rw [hy₂, hy₃]; group
  have hd₁y : d₁ * (x * y₂⁻¹) * d₁⁻¹ = y₁ * y₃⁻¹ := by
    calc d₁ * (x * y₂⁻¹) * d₁⁻¹ = (d₁ * x * d₁⁻¹) * (d₁ * y₂ * d₁⁻¹)⁻¹ := by group
      _ = y₁ * y₃⁻¹ := by rw [e3, ← hy₁]
  have hwdef : (x * y₂⁻¹) * d₁ * (x * y₂⁻¹)⁻¹ * d₁⁻¹ = (x * y₂⁻¹) * (y₁ * y₃⁻¹) := by
    rw [hci]
    calc (x * y₂⁻¹) * d₁ * (x * y₂⁻¹) * d₁⁻¹ = (x * y₂⁻¹) * (d₁ * (x * y₂⁻¹) * d₁⁻¹) := by group
      _ = _ := by rw [hd₁y]
  rw [hwdef] at hwA'
  have pairsq : ∀ a b : G, Commute a b → a * a = t → b * b = t → (a * b⁻¹) * (a * b⁻¹) = 1 := by
    intro a b hab ha hb
    have hab' : Commute a b⁻¹ := hab.inv_right
    have e : (a * b⁻¹) * (a * b⁻¹) = (a * a) * (b⁻¹ * b⁻¹) := by
      calc (a * b⁻¹) * (a * b⁻¹) = a * (b⁻¹ * a) * b⁻¹ := by group
        _ = a * (a * b⁻¹) * b⁻¹ := by rw [← hab'.eq]
        _ = (a * a) * (b⁻¹ * b⁻¹) := by group
    rw [e, ha]
    have : b⁻¹ * b⁻¹ = t⁻¹ := by rw [← hb]; group
    rw [this, hti, ht2]
  have hab : Commute (x * y₂⁻¹) (y₁ * y₃⁻¹) :=
    (hxy₁.mul_right hxy₃.inv_right).mul_left
      (hy₁y₂.symm.inv_left.mul_right hy₂y₃.inv_left.inv_right)
  have hww : ((x * y₂⁻¹) * (y₁ * y₃⁻¹)) * ((x * y₂⁻¹) * (y₁ * y₃⁻¹)) = 1 := by
    have h1 := pairsq x y₂ hxy₂ hxsq hy₂sq
    have h2 := pairsq y₁ y₃ hy₁y₃ hy₁sq hy₃sq
    calc ((x * y₂⁻¹) * (y₁ * y₃⁻¹)) * ((x * y₂⁻¹) * (y₁ * y₃⁻¹))
        = (x * y₂⁻¹) * ((y₁ * y₃⁻¹) * (x * y₂⁻¹)) * (y₁ * y₃⁻¹) := by group
      _ = (x * y₂⁻¹) * ((x * y₂⁻¹) * (y₁ * y₃⁻¹)) * (y₁ * y₃⁻¹) := by rw [← hab.eq]
      _ = ((x * y₂⁻¹) * (x * y₂⁻¹)) * ((y₁ * y₃⁻¹) * (y₁ * y₃⁻¹)) := by group
      _ = 1 := by rw [h1, h2, one_mul]
  have hwt : ((x * y₂⁻¹) * (y₁ * y₃⁻¹)) * t = t * ((x * y₂⁻¹) * (y₁ * y₃⁻¹)) := by
    have h1 : Commute x t := hxt
    have h2 : Commute y₂⁻¹ t := (show Commute y₂ t from hy₂t).inv_left
    have h3 : Commute y₁ t := hy₁t
    have h4 : Commute y₃⁻¹ t := (show Commute y₃ t from hy₃t).inv_left
    exact ((h1.mul_left h2).mul_left (h3.mul_left h4)).eq
  have hw1 : (x * y₂⁻¹) * (y₁ * y₃⁻¹) ≠ 1 := by
    intro h
    have hq : x * (y₂⁻¹ * (y₁ * y₃⁻¹)) = 1 := by rw [← mul_assoc]; exact h
    have hxq : x = (y₂⁻¹ * (y₁ * y₃⁻¹))⁻¹ := eq_inv_of_mul_eq_one_left hq
    have hrq : Commute r (y₂⁻¹ * (y₁ * y₃⁻¹)) := hry₂.inv_right.mul_right (hry₁.mul_right hry₃.inv_right)
    have hrx : Commute r x := by rw [hxq]; exact hrq.inv_right
    exact hxr hrx.eq.symm
  have hxw : x * ((x * y₂⁻¹) * (y₁ * y₃⁻¹)) = ((x * y₂⁻¹) * (y₁ * y₃⁻¹)) * x :=
    (((Commute.refl x).mul_right hxy₂.inv_right).mul_right (hxy₁.mul_right hxy₃.inv_right)).eq
  rcases hAD _ hwA' hww hwt with h | h | h | h
  · exact hw1 h
  · apply hbad x hxK hx4
    apply g₁.cent
    rw [Subgroup.mem_centralizer_singleton_iff, ← h]
    exact hxw
  · apply hbad x hxK hx4
    apply g₂.cent
    rw [Subgroup.mem_centralizer_singleton_iff, ← h]
    exact hxw
  · apply hbad x hxK hx4
    apply g₃.cent
    rw [Subgroup.mem_centralizer_singleton_iff, ← h]
    exact hxw

end Orb2

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
