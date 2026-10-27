module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf3Lift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

theorem mem_normalizer_of_comm {G : Type} [Group G] (S : Subgroup G) (g : G)
    (h : ∀ s ∈ S, s * g = g * s) : g ∈ Subgroup.normalizer (S : Set G) :=
  Subgroup.centralizer_le_normalizer (S : Set G) (Subgroup.mem_centralizer_iff.mpr h)

section Lift

variable {H : Type} [Group H] [Finite H] (N : Subgroup H) [N.Normal]

theorem lift_odd_normalizing (hN : Odd (Nat.card N)) {A B : Subgroup H} (hA : IsPGroup 2 A)
    (hB : IsPGroup 2 B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {xb : H ⧸ N}
    (hodd : Odd (orderOf xb))
    (hxA : xb ∈ Subgroup.normalizer
      ((A.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)))
    (hxB : ∀ b ∈ B, xb * QuotientGroup.mk' N b = QuotientGroup.mk' N b * xb) :
    ∃ x : H, Odd (orderOf x) ∧ QuotientGroup.mk' N x = xb ∧ (∀ a ∈ A, x * a * x⁻¹ ∈ A) ∧
      (∀ b ∈ B, x * b = b * x) := by
  classical
  set π := QuotientGroup.mk' N with hπ
  set D : Subgroup H := A ⊔ B with hD
  have hAN : A ≤ Subgroup.normalizer (B : Set H) := fun a ha =>
    mem_normalizer_of_comm B a fun b hb => (hAB a ha b hb).symm
  have hD2 : IsPGroup 2 D := hA.to_sup_of_normal_right' hB hAN
  have hxB' : xb ∈ Subgroup.normalizer ((B.map π : Subgroup (H ⧸ N)) : Set (H ⧸ N)) :=
    mem_normalizer_of_comm _ xb fun y hy => by
      obtain ⟨b, hb, rfl⟩ := hy
      exact (hxB b hb).symm
  have hxD : conjSub xb (D.map π) = D.map π := by
    rw [hD, Subgroup.map_sup, conjSub_sup,
      mem_normalizer_iff_conjSub_eq.mp hxA, mem_normalizer_iff_conjSub_eq.mp hxB']
  obtain ⟨x₁, hx₁⟩ := QuotientGroup.mk'_surjective N xb
  set D₁ : Subgroup H := conjSub x₁ D with hD₁
  have hD₁2 : IsPGroup 2 D₁ := isPGroup_conjSub x₁ hD2
  have hmap : D₁.map π = D.map π := by
    rw [← hxD, ← hx₁]
    ext y
    simp only [hD₁, conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
      exact ⟨π d, ⟨d, hd, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
      exact ⟨x₁ * d * x₁⁻¹, ⟨d, hd, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩
  obtain ⟨n₁, hn₁, hconj⟩ := exists_odd_conj N hN hD₁2 hD2 hmap
  set x₂ : H := n₁ * x₁ with hx₂
  have hx₂D : conjSub x₂ D = D := by
    rw [hx₂, conjSub_mul, ← hD₁, hconj]
  have hπx₂ : π x₂ = xb := by
    have hπn : π n₁ = 1 := (QuotientGroup.eq_one_iff n₁).mpr hn₁
    rw [hx₂, map_mul, hπn, one_mul, hx₁]
  have hDN : D ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hD2 le_rfl
      (hN.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  have hinj : ∀ d₁ ∈ D, ∀ d₂ ∈ D, π d₁ = π d₂ → d₁ = d₂ := by
    intro d₁ hd₁ d₂ hd₂ h
    have h1 : d₁⁻¹ * d₂ ∈ D ⊓ N := ⟨D.mul_mem (D.inv_mem hd₁) hd₂, QuotientGroup.eq.mp h⟩
    rw [hDN, Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  have hconjD : ∀ d ∈ D, x₂ * d * x₂⁻¹ ∈ D := fun d hd => by
    have := conj_mem_conjSub (n := x₂) hd
    rwa [hx₂D] at this
  have hπc : ∀ d : H, π (x₂ * d * x₂⁻¹) = xb * π d * xb⁻¹ := fun d => by
    rw [map_mul, map_mul, map_inv, hπx₂]
  refine ⟨x₂, ?_, hπx₂, ?_, ?_⟩
  ·
    set m := orderOf xb with hm
    have h1 : x₂ ^ m ∈ N := by
      have : π (x₂ ^ m) = 1 := by rw [map_pow, hπx₂, hm, pow_orderOf_eq_one]
      exact (QuotientGroup.eq_one_iff _).mp this
    have h2 : Odd (orderOf (x₂ ^ m)) := hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N h1)
    have h3 : x₂ ^ (m * orderOf (x₂ ^ m)) = 1 := by
      rw [pow_mul, pow_orderOf_eq_one]
    exact (hodd.mul h2).of_dvd_nat (orderOf_dvd_of_pow_eq_one h3)
  · intro a ha
    have haD : a ∈ D := Subgroup.mem_sup_left ha
    have h1 := hconjD a haD
    have h2 : xb * π a * xb⁻¹ ∈ A.map π :=
      (Subgroup.mem_normalizer_iff.mp hxA (π a)).mp ⟨a, ha, rfl⟩
    obtain ⟨a', ha', hpa'⟩ := h2
    have ha'D : a' ∈ D := Subgroup.mem_sup_left ha'
    have := hinj _ h1 _ ha'D (by rw [hπc, ← hpa'])
    rw [this]
    exact ha'
  · intro b hb
    have hbD : b ∈ D := Subgroup.mem_sup_right hb
    have h1 := hconjD b hbD
    have h2 : π (x₂ * b * x₂⁻¹) = π b := by
      rw [hπc]
      calc xb * π b * xb⁻¹ = (π b * xb) * xb⁻¹ := by rw [hxB b hb]
        _ = π b := by group
    have h3 := hinj _ h1 b hbD h2
    calc x₂ * b = (x₂ * b * x₂⁻¹) * x₂ := by group
      _ = b * x₂ := by rw [h3]

end Lift

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus
