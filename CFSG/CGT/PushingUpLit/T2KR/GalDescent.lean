module

public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.CGT.PushingUpLit.T2KR

section Descent

variable {F W : Type} [Field F] [CharP F 2] [AddCommGroup W] [Module F W]

theorem exists_add_eq_one (σ : F ≃+* F) (hσ : σ ≠ 1) (hσσ : ∀ x, σ (σ x) = x) :
    ∃ ω : F, ω + σ ω = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact hσ (RingEquiv.ext hcon)
  have hδ : x + σ x ≠ 0 := by
    intro h
    apply hx
    have h2 : x + x = 0 := CharTwo.add_self_eq_zero x
    linear_combination h - h2
  refine ⟨x / (x + σ x), ?_⟩
  have hfix : σ (x + σ x) = x + σ x := by rw [map_add, hσσ, add_comm]
  rw [map_div₀, hfix, ← add_div, div_self hδ]

theorem card_eq_sq_card_fixed (σ : F ≃+* F) (hσ : σ ≠ 1) (hσσ : ∀ x, σ (σ x) = x)
    (β : W →+ W) (hβ : ∀ (c : F) (w : W), β (c • w) = σ c • β w) (hββ : ∀ w, β (β w) = w) :
    Nat.card W = Nat.card {w : W // β w = w} ^ 2 := by
  obtain ⟨ω, hω⟩ := exists_add_eq_one σ hσ hσσ
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hσω : σ ω = 1 + ω := by linear_combination hω - ω * h2
  have h3 : ∀ x : W, (2 : F) • x = 0 := fun x => by rw [h2, zero_smul]
  let C : AddSubgroup W :=
    { carrier := {w | β w = w}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at *
        rw [map_add, ha, hb]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at *
        rw [map_neg, ha] }
  let Φ : C × C → W := fun p => (p.1 : W) + ω • (p.2 : W)
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
      simp only [Φ] at h
      have ha1 : β a = a := ha
      have hb1 : β b = b := hb
      have ha1' : β a' = a' := ha'
      have hb1' : β b' = b' := hb'
      have h' := congrArg β h
      rw [map_add, map_add, hβ, hβ, ha1, hb1, ha1', hb1', hσω] at h'
      have hbb : b = b' := by
        have : b - b' = 0 := by linear_combination (norm := module) h' - h
        exact sub_eq_zero.1 this
      subst hbb
      have haa : a = a' := by
        have : a - a' = 0 := by linear_combination (norm := module) h
        exact sub_eq_zero.1 this
      subst haa
      rfl
    · intro w
      have hu0 : β ((1 + ω) • w + ω • β w) = (1 + ω) • w + ω • β w := by
        rw [map_add, hβ, hβ, hββ, map_add, map_one, hσω]
        linear_combination (norm := module) h3 (β w)
      have hu1 : β (w + β w) = w + β w := by
        rw [map_add, hββ, add_comm]
      refine ⟨(⟨(1 + ω) • w + ω • β w, hu0⟩, ⟨w + β w, hu1⟩), ?_⟩
      show (1 + ω) • w + ω • β w + ω • (w + β w) = w
      linear_combination (norm := module) ω • h3 w + ω • h3 (β w)
  have e1 : Nat.card W = Nat.card (C × C) := (Nat.card_congr (Equiv.ofBijective Φ hΦ)).symm
  rw [e1, Nat.card_prod, sq]
  rfl

theorem card_fixed_twisted [Finite F] (σ : F ≃+* F) (hσ : σ ≠ 1) (hσσ : ∀ x, σ (σ x) = x) (c : F)
    (hc : c * σ c = 1) : Nat.card {B : F // c * σ B = B} ^ 2 = Nat.card F := by
  let β : F →+ F :=
    { toFun := fun x => c * σ x
      map_zero' := by simp
      map_add' := fun x y => by rw [map_add, mul_add] }
  have h := card_eq_sq_card_fixed (W := F) σ hσ hσσ β
    (fun d w => by
      show c * σ (d • w) = σ d • (c * σ w)
      rw [smul_eq_mul, smul_eq_mul, map_mul]
      ring)
    (fun w => by
      show c * σ (c * σ w) = w
      rw [map_mul, hσσ]
      linear_combination w * hc)
  exact h.symm

end Descent

theorem eq_one_of_pow_two_pow_eq_one {F : Type} [Field F] [CharP F 2] {d : F} {k : ℕ}
    (h : d ^ 2 ^ k = 1) : d = 1 := by
  have h1 : (d - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h1)

section Involutions

instance finite_ringEquiv (n : ℕ) : Finite (GaloisField 2 n ≃+* GaloisField 2 n) :=
  Finite.of_injective
    (fun τ : GaloisField 2 n ≃+* GaloisField 2 n => (τ : GaloisField 2 n → GaloisField 2 n))
    DFunLike.coe_injective

@[expose] noncomputable def toGal (n : ℕ) (τ : GaloisField 2 n ≃+* GaloisField 2 n) :
    Gal(GaloisField 2 n/ZMod 2) :=
  AlgEquiv.ofRingEquiv (R := ZMod 2) (f := τ) (fun x => by
    have := RingHom.ext_zmod ((τ : GaloisField 2 n →+* GaloisField 2 n).comp
      (algebraMap (ZMod 2) (GaloisField 2 n))) (algebraMap (ZMod 2) (GaloisField 2 n))
    exact congrArg (fun f => f x) this)

theorem toGal_apply (n : ℕ) (τ : GaloisField 2 n ≃+* GaloisField 2 n) (x : GaloisField 2 n) :
    toGal n τ x = τ x := rfl

theorem toGal_injective (n : ℕ) : Function.Injective (toGal n) := fun a b h =>
  RingEquiv.ext fun x => by rw [← toGal_apply, ← toGal_apply, h]

theorem toGal_mul (n : ℕ) (a b : GaloisField 2 n ≃+* GaloisField 2 n) :
    toGal n (a * b) = toGal n a * toGal n b := by
  ext x
  rfl

theorem toGal_one (n : ℕ) : toGal n 1 = 1 := by
  ext x
  rfl

theorem card_involutions_le_two (n : ℕ) :
    Nat.card {τ : GaloisField 2 n ≃+* GaloisField 2 n // τ * τ = 1} ≤ 2 := by
  classical
  let e : {τ : GaloisField 2 n ≃+* GaloisField 2 n // τ * τ = 1} →
      {a : Gal(GaloisField 2 n/ZMod 2) // a ^ 2 = 1} := fun τ =>
    ⟨toGal n τ.1, by rw [pow_two, ← toGal_mul, τ.2, toGal_one]⟩
  have he : Function.Injective e := fun a b h =>
    Subtype.ext (toGal_injective n (congrArg Subtype.val h))
  have h1 := Nat.card_le_card_of_injective e he
  have : Fintype Gal(GaloisField 2 n/ZMod 2) := Fintype.ofFinite _
  have h2 : Nat.card {a : Gal(GaloisField 2 n/ZMod 2) // a ^ 2 = 1} ≤ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le (α := Gal(GaloisField 2 n/ZMod 2)) (by norm_num)
  exact h1.trans h2

theorem even_of_involution {n : ℕ} (hn : n ≠ 0) (σ : GaloisField 2 n ≃+* GaloisField 2 n)
    (hσ : σ ≠ 1) (hσσ : ∀ x, σ (σ x) = x) : Even n := by
  have h := card_fixed_twisted (F := GaloisField 2 n) σ hσ hσσ 1 (by rw [map_one, mul_one])
  rw [GaloisField.card 2 n hn] at h
  set c := Nat.card {B : GaloisField 2 n // 1 * σ B = B} with hc
  have hdvd : c ∣ 2 ^ n := ⟨c, by rw [← h]; ring⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hk, ← pow_mul] at h
  have := Nat.pow_right_injective (le_refl 2) h
  exact ⟨k, by omega⟩

theorem ringEquiv_mul_comm (n : ℕ) (a b : GaloisField 2 n ≃+* GaloisField 2 n) :
    a * b = b * a := by
  apply toGal_injective n
  rw [toGal_mul, toGal_mul]
  exact (inferInstance : IsMulCommutative Gal(GaloisField 2 n/ZMod 2)).is_comm.comm _ _

end Involutions

end CFSG.CGT.PushingUpLit.T2KR
