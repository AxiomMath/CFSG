module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23T

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup

section Counting

variable {S : Type} [Group S] [Finite S]

theorem card_mod_three_of_fpf (ρ : MulAut S) (hρ : ρ ^ 3 = 1) (hfpf : ∀ g : S, ρ g = g → g = 1)
    (H : Subgroup S) (hH : ∀ h ∈ H, ρ h ∈ H) : Nat.card H % 3 = 1 := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  let f : Function.End H := fun h => ⟨ρ h, hH h h.2⟩
  have hf : ∀ k : ℕ, ∀ h : H, ((f ^ k) h : S) = (ρ ^ k) h := by
    intro k
    induction k with
    | zero => intro h; rfl
    | succ k ih =>
      intro h
      rw [pow_succ, pow_succ]
      show ((f ^ k) (f h) : S) = (ρ ^ k) (ρ h)
      rw [ih]
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext h
    apply Subtype.ext
    rw [pow_one, hf 3 h, hρ]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf3
  have hfix : Fintype.card f.fixedPoints = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, Subtype.ext (map_one ρ)⟩, ?_⟩
    rintro ⟨y, hy⟩
    exact Subtype.ext (Subtype.ext (hfpf y (congrArg Subtype.val hy)))
  rw [Nat.card_eq_fintype_card]
  have h2 : Fintype.card f.fixedPoints % 3 = 1 := by simp [hfix]
  have h3 : Fintype.card H % 3 = Fintype.card f.fixedPoints % 3 := hmod
  omega

theorem eq_bot_of_card_le_two (ρ : MulAut S) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : S, ρ g = g → g = 1) (H : Subgroup S) (hH : ∀ h ∈ H, ρ h ∈ H)
    (h2 : Nat.card H ≤ 2) : H = ⊥ := by
  have hmod := card_mod_three_of_fpf ρ hρ hfpf H hH
  haveI : Nonempty H := ⟨⟨1, one_mem H⟩⟩
  have hpos : 0 < Nat.card H := Nat.card_pos
  have h1 : Nat.card H = 1 := by omega
  exact Subgroup.eq_bot_of_card_eq H h1

theorem forall_mul_rho_rho_sq (ρ : MulAut S) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : S, ρ g = g → g = 1) (g : S) : g * ρ g * ρ (ρ g) = 1 := by
  have hρ3 : ∀ x : S, ρ (ρ (ρ x)) = x := by
    intro x
    have h := congrArg (fun f : MulAut S => f x) hρ
    simpa [pow_succ, MulAut.mul_apply] using h
  let c : S → S := fun x => x⁻¹ * ρ x
  have hc_inj : Function.Injective c := by
    intro a b hab
    simp only [c] at hab
    have h1 : b * a⁻¹ = ρ (b * a⁻¹) := by
      rw [map_mul, map_inv]
      calc b * a⁻¹ = b * (a⁻¹ * ρ a) * (ρ a)⁻¹ := by group
        _ = b * (b⁻¹ * ρ b) * (ρ a)⁻¹ := by rw [hab]
        _ = ρ b * (ρ a)⁻¹ := by group
    have h2 := hfpf (b * a⁻¹) h1.symm
    exact (mul_inv_eq_one.mp h2).symm
  have hc_surj : Function.Surjective c := Finite.injective_iff_surjective.mp hc_inj
  have hc3 : ∀ x : S, c x * ρ (c x) * ρ (ρ (c x)) = 1 := by
    intro x
    simp only [c, map_mul, map_inv]
    rw [hρ3 x]
    group
  obtain ⟨w, hw⟩ := hc_surj g
  rw [← hw]
  exact hc3 w

theorem map_eq_of_forall_mem (ρ : MulAut S) (N : Subgroup S) (hN : ∀ n ∈ N, ρ n ∈ N) :
    N.map ρ.toMonoidHom = N := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro x ⟨n, hn, rfl⟩
    exact hN n hn
  · rw [Subgroup.card_map_of_injective ρ.injective]

theorem rho_mem_center (ρ : MulAut S) {z : S} (hz : z ∈ center S) : ρ z ∈ center S := by
  have hchar : (center S).Characteristic := Subgroup.centerCharacteristic
  exact Subgroup.characteristic_iff_map_le.mp hchar ρ ⟨z, hz, rfl⟩

theorem rho_mem_commutator (ρ : MulAut S) {g : S} (hg : g ∈ commutator S) :
    ρ g ∈ commutator S := by
  have hchar : (commutator S).Characteristic := inferInstance
  exact Subgroup.characteristic_iff_map_le.mp hchar ρ ⟨g, hg, rfl⟩

end Counting

section Quotient

variable {S : Type} [Group S]

@[expose] noncomputable def quotAut (ρ : MulAut S) (N : Subgroup S) [N.Normal]
    (hN : N.map ρ.toMonoidHom = N) : MulAut (S ⧸ N) :=
  QuotientGroup.congr N N ρ hN

theorem quotAut_mk (ρ : MulAut S) (N : Subgroup S) [N.Normal] (hN : N.map ρ.toMonoidHom = N)
    (g : S) : quotAut ρ N hN (QuotientGroup.mk g) = QuotientGroup.mk (ρ g) := rfl

end Quotient

section QuotientFpf

variable {S : Type} [Group S] [Finite S]

theorem quotAut_pow_three (ρ : MulAut S) (hρ : ρ ^ 3 = 1) (N : Subgroup S) [N.Normal]
    (hN : N.map ρ.toMonoidHom = N) : quotAut ρ N hN ^ 3 = 1 := by
  apply MulEquiv.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro g
  have hf : ∀ k : ℕ, ∀ g : S, (quotAut ρ N hN ^ k) (QuotientGroup.mk g) =
      QuotientGroup.mk ((ρ ^ k) g) := by
    intro k
    induction k with
    | zero => intro g; rfl
    | succ k ih =>
      intro g
      rw [pow_succ, pow_succ, MulAut.mul_apply, quotAut_mk, ih, MulAut.mul_apply]
  rw [hf 3 g, hρ]
  rfl

theorem quotAut_fpf (ρ : MulAut S) (hρ : ρ ^ 3 = 1) (hfpf : ∀ g : S, ρ g = g → g = 1)
    (N : Subgroup S) [N.Normal] (hN : N.map ρ.toMonoidHom = N) (x : S ⧸ N)
    (hx : quotAut ρ N hN x = x) : x = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [quotAut_mk] at hx
  have hA : ∀ a ∈ N, ρ a ∈ N := by
    intro a ha
    have h : ρ a ∈ N.map ρ.toMonoidHom := ⟨a, ha, rfl⟩
    rwa [hN] at h
  have hcard : Nat.card N % 3 = 1 := card_mod_three_of_fpf ρ hρ hfpf N hA
  have ht : g⁻¹ * ρ g ∈ N := QuotientGroup.eq.mp hx.symm
  obtain ⟨s, hs, hfix⟩ :=
    CFSG.GH74.GLS.Bg.TwoGroups.L23.exists_fixed_in_coset ρ hρ N hA hcard g ht
  have hs1 : s = 1 := hfpf s hfix
  rw [QuotientGroup.eq_one_iff]
  rw [hs1, mul_one] at hs
  exact (Subgroup.inv_mem_iff N).mp hs

end QuotientFpf

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
