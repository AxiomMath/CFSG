module

public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.Quasithin

theorem apply_apply_of_mul_self_eq_one {S : Type} [CommGroup S] {a₀ : MulAut S}
    (ha₀ : a₀ * a₀ = 1) (y : S) : a₀ (a₀ y) = y := by
  have h := congrArg (fun f : MulAut S => f y) ha₀
  exact h

theorem split_decomp {S : Type} [CommGroup S] (a₀ : MulAut S) (S₁ : Subgroup S)
    (hsup : S₁ ⊔ S₁.map a₀.toMonoidHom = ⊤) (v : S) :
    ∃ x ∈ S₁, ∃ y ∈ S₁, x * a₀ y = v := by
  have hv : v ∈ S₁ ⊔ S₁.map a₀.toMonoidHom := by
    rw [hsup]
    exact Subgroup.mem_top v
  obtain ⟨x, hx, z, hz, hxz⟩ := Subgroup.mem_sup.mp hv
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
  exact ⟨x, hx, y, hy, hxz⟩

theorem split_inj {S : Type} [CommGroup S] (a₀ : MulAut S) (S₁ : Subgroup S)
    (hinf : S₁ ⊓ S₁.map a₀.toMonoidHom = ⊥) {x₁ y₁ x₂ y₂ : S}
    (hx₁ : x₁ ∈ S₁) (hy₁ : y₁ ∈ S₁) (hx₂ : x₂ ∈ S₁) (hy₂ : y₂ ∈ S₁)
    (h : x₁ * a₀ y₁ = x₂ * a₀ y₂) : x₁ = x₂ ∧ y₁ = y₂ := by
  have hz : x₁ * x₂⁻¹ = a₀ (y₂ * y₁⁻¹) := by
    have h2 : a₀ y₂ = x₂⁻¹ * (x₁ * a₀ y₁) := by
      rw [h, inv_mul_cancel_left]
    rw [map_mul, map_inv, h2]
    calc x₁ * x₂⁻¹ = x₁ * x₂⁻¹ * (a₀ y₁ * (a₀ y₁)⁻¹) := by rw [mul_inv_cancel, mul_one]
      _ = x₂⁻¹ * (x₁ * a₀ y₁) * (a₀ y₁)⁻¹ := by ac_rfl
  have hzero : x₁ * x₂⁻¹ = 1 := by
    have hmem : x₁ * x₂⁻¹ ∈ S₁ ⊓ S₁.map a₀.toMonoidHom :=
      Subgroup.mem_inf.mpr ⟨S₁.mul_mem hx₁ (S₁.inv_mem hx₂),
        Subgroup.mem_map.mpr ⟨y₂ * y₁⁻¹, S₁.mul_mem hy₂ (S₁.inv_mem hy₁), hz.symm⟩⟩
    rw [hinf] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hx : x₁ = x₂ := mul_inv_eq_one.mp hzero
  subst hx
  exact ⟨rfl, a₀.injective (mul_left_cancel h)⟩

theorem card_split {S : Type} [CommGroup S] [Finite S] (a₀ : MulAut S) (S₁ : Subgroup S)
    (hinf : S₁ ⊓ S₁.map a₀.toMonoidHom = ⊥) (hsup : S₁ ⊔ S₁.map a₀.toMonoidHom = ⊤) :
    Nat.card S = Nat.card S₁ ^ 2 := by
  have hbij : Function.Bijective (fun p : S₁ × S₁ => (p.1 : S) * a₀ (p.2 : S)) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
      obtain ⟨h1, h2⟩ := split_inj a₀ S₁ hinf x₁.2 y₁.2 x₂.2 y₂.2 h
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    · intro v
      obtain ⟨x, hx, y, hy, hv⟩ := split_decomp a₀ S₁ hsup v
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), hv⟩
  rw [sq, ← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

theorem card_fixV_le_of_split {S : Type} [CommGroup S] [Finite S] (a₀ : MulAut S)
    (ha₀ : a₀ * a₀ = 1) (S₁ : Subgroup S)
    (hinf : S₁ ⊓ S₁.map a₀.toMonoidHom = ⊥) (hsup : S₁ ⊔ S₁.map a₀.toMonoidHom = ⊤)
    {A E : Subgroup (MulAut S)} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (ha₀A : a₀ ∈ A)
    (hEA : E ≤ A) (hEinv : ∀ b ∈ E, ∀ x ∈ S₁, b x ∈ S₁) :
    Nat.card (fixV A) ≤ Nat.card ↥(S₁ ⊓ fixV E) := by
  have hex : ∀ v ∈ fixV A, ∃ x ∈ S₁ ⊓ fixV E, x * a₀ x = v := by
    intro v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := split_decomp a₀ S₁ hsup v
    have hfix : a₀ (x * a₀ y) = x * a₀ y := mem_fixV.mp hv a₀ ha₀A
    have hax : a₀ x * y = x * a₀ y := by
      rw [map_mul, apply_apply_of_mul_self_eq_one ha₀] at hfix
      exact hfix
    have hxy : x = y := (split_inj a₀ S₁ hinf hx hy hy hx (hax.symm.trans (mul_comm _ _))).1
    subst hxy
    refine ⟨x, Subgroup.mem_inf.mpr ⟨hx, mem_fixV.mpr ?_⟩, rfl⟩
    intro b hb
    have hbA : b ∈ A := hEA hb
    have hbv : b (x * a₀ x) = x * a₀ x := mem_fixV.mp hv b hbA
    have hc : a₀ (b x) = b (a₀ x) := congrArg (fun f : MulAut S => f x) (hAc a₀ ha₀A b hbA)
    have hbx : b x * a₀ (b x) = x * a₀ x := by
      calc b x * a₀ (b x) = b x * b (a₀ x) := by rw [hc]
        _ = b (x * a₀ x) := (map_mul b x (a₀ x)).symm
        _ = x * a₀ x := hbv
    exact (split_inj a₀ S₁ hinf (hEinv b hb x hx) (hEinv b hb x hx) hx hx hbx).1
  choose! g hg using hex
  have hG : Function.Injective
      (fun v : fixV A => (⟨g v.1, (hg v.1 v.2).1⟩ : ↥(S₁ ⊓ fixV E))) := by
    intro v w hvw
    have h1 : g v.1 = g w.1 := congrArg Subtype.val hvw
    apply Subtype.ext
    calc v.1 = g v.1 * a₀ (g v.1) := ((hg v.1 v.2).2).symm
      _ = g w.1 * a₀ (g w.1) := by rw [h1]
      _ = w.1 := (hg w.1 w.2).2
  exact Nat.card_le_card_of_injective _ hG

end CFSG.HardMathSupport.U4FF
