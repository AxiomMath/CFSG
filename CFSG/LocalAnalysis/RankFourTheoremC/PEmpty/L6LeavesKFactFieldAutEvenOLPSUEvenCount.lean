module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLinAlg

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

theorem dvd_sub_of_pow_modEq {q r d : ℕ} (hq : 1 ≤ q) (hd : 0 < d) (hdvd : r ∣ q ^ d - 1)
    (hmin : ∀ k : ℕ, 0 < k → k < d → ¬ r ∣ q ^ k - 1) {a b : ℕ} (hab : a ≤ b)
    (h : q ^ a ≡ q ^ b [MOD r]) : d ∣ b - a := by
  have hcast : ∀ k : ℕ, ((q : ZMod r) ^ k = 1 ↔ r ∣ q ^ k - 1) := fun k => by
    have h1 : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one, sub_eq_zero]
  have hx : (q : ZMod r) ^ d = 1 := (hcast d).2 hdvd
  have hord : orderOf (q : ZMod r) = d := by
    rw [orderOf_eq_iff hd]
    exact ⟨hx, fun m hm hm0 hm1 => hmin m hm0 hm ((hcast m).1 hm1)⟩
  have hu : IsUnit (q : ZMod r) := IsUnit.of_pow_eq_one hx hd.ne'
  have h1 : (q : ZMod r) ^ a = (q : ZMod r) ^ b := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h
    simpa [Nat.cast_pow] using this
  have h2 : (q : ZMod r) ^ (b - a) = 1 := by
    have h3 : (q : ZMod r) ^ b = (q : ZMod r) ^ a * (q : ZMod r) ^ (b - a) := by
      rw [← pow_add, Nat.add_sub_cancel' hab]
    rw [h3] at h1
    exact ((hu.pow a).mul_left_cancel (by rw [mul_one]; exact h1)).symm
  rw [← hord]
  exact orderOf_dvd_iff_pow_eq_one.2 h2

variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] [Module.Finite F V]

theorem pow_modEq_pow_finrank_fixed {r : ℕ} (hr : r.Prime) (g : V ≃ₗ[F] V) (hg : g ^ r = 1)
    (W : Submodule F V) (hW : ∀ v ∈ W, g v ∈ W) :
    Nat.card F ^ Module.finrank F W ≡
      Nat.card F ^ Module.finrank F ↥(W ⊓ LinearMap.ker (g.toLinearMap - LinearMap.id))
        [MOD r] := by
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite W := inferInstance
  have hinj : Function.Injective fun w : W => (⟨g w, hW w w.2⟩ : W) := by
    intro a b hab
    exact Subtype.ext (g.injective (congrArg Subtype.val hab))
  let σ : Equiv.Perm W := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
  have hσw : ∀ w : W, ((σ w : W) : V) = g w := fun w => rfl
  have hσ : σ ^ r = 1 := by
    ext w
    have key : ∀ (n : ℕ) (w : W), (((σ ^ n) w : W) : V) = (g ^ n) w := by
      intro n
      induction n with
      | zero => intro w; simp
      | succ n ih =>
        intro w
        rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, LinearEquiv.mul_apply, ih (σ w), hσw]
    have := key r w
    rw [hg] at this
    simpa using this
  have h := card_modEq_card_fixed_of_pow_eq_one hr σ hσ
  let N : Submodule F V := W ⊓ LinearMap.ker (g.toLinearMap - LinearMap.id)
  have hN : ∀ x : V, x ∈ N ↔ x ∈ W ∧ g x = x := fun x => by
    simp [N, LinearMap.mem_ker, sub_eq_zero]
  have h1 : Nat.card {x : W // σ x = x} = Nat.card N :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, (hN _).2 ⟨x.1.2, congrArg Subtype.val x.2⟩⟩
        invFun := fun y => ⟨⟨y.1, ((hN _).1 y.2).1⟩, Subtype.ext ((hN _).1 y.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have e1 : Nat.card W = Nat.card F ^ Module.finrank F W := Module.natCard_eq_pow_finrank (K := F)
  have e2 : Nat.card N = Nat.card F ^ Module.finrank F N := Module.natCard_eq_pow_finrank (K := F)
  rw [h1, e1, e2] at h
  exact h

theorem exists_ne_zero_fixed_of_stable [CharP F 2] (R : Subgroup (V ≃ₗ[F] V)) (hR : IsPGroup 2 R)
    (U : Submodule F V) (hU : ∀ x ∈ R, ∀ u ∈ U, x u ∈ U) (hU0 : U ≠ ⊥) :
    ∃ v ∈ U, v ≠ 0 ∧ ∀ x ∈ R, x v = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite V := Module.finite_of_finite F
  letI : MulAction R U :=
    { smul := fun x u => ⟨x.1 u, hU x.1 x.2 u u.2⟩
      one_smul := fun u => Subtype.ext rfl
      mul_smul := fun x y u => Subtype.ext rfl }
  by_contra hno
  push Not at hno
  have h := hR.card_modEq_card_fixedPoints U
  have hfix : MulAction.fixedPoints R U = {0} := by
    ext v
    constructor
    · intro hv
      by_contra hv0
      have hv0' : (v : V) ≠ 0 := fun h0 => hv0 (Subtype.ext h0)
      obtain ⟨x, hx, hxv⟩ := hno v v.2 hv0'
      exact hxv (congrArg Subtype.val (hv ⟨x, hx⟩))
    · intro hv x
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact Subtype.ext (map_zero x.1)
  rw [hfix] at h
  have hcard1 : Nat.card (({0} : Set U) : Type _) = 1 := by simp
  rw [hcard1] at h
  have heven : Even (Nat.card U) := by
    rw [Module.natCard_eq_pow_finrank (K := F)]
    have hfin : 0 < Module.finrank F U := Submodule.one_le_finrank_iff.2 hU0
    have hF : Even (Nat.card F) := by
      haveI : Fintype F := Fintype.ofFinite F
      have := FiniteField.even_card_of_char_two (F := F) (ringChar.eq F 2)
      rw [Nat.card_eq_fintype_card]
      exact Nat.even_iff.mpr this
    exact hF.pow_of_ne_zero (by omega)
  have h2 : Nat.card U % 2 = 1 % 2 := h
  have h3 := Nat.even_iff.mp heven
  omega

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
