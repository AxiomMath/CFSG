module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.CharAndCard

public section

namespace CFSG.SectionRank.OddCover

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W]

@[expose] def biaddHom (b : K → K → W) (hadd₁ : ∀ x x' y, b (x + x') y = b x y + b x' y)
    (hadd₂ : ∀ x y y', b x (y + y') = b x y + b x y') : K →+ K →+ W :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (b x) (hadd₂ x)) fun x x' => by
    ext y
    exact hadd₁ x x' y

theorem biaddHom_apply (b : K → K → W) (hadd₁ : ∀ x x' y, b (x + x') y = b x y + b x' y)
    (hadd₂ : ∀ x y y', b x (y + y') = b x y + b x y') (x y : K) :
    biaddHom b hadd₁ hadd₂ x y = b x y :=
  rfl

theorem nsmul_nsmul_of_biadd (b : K → K → W) (hadd₁ : ∀ x x' y, b (x + x') y = b x y + b x' y)
    (hadd₂ : ∀ x y y', b x (y + y') = b x y + b x y') (m n : ℕ) (x y : K) :
    b (m • x) (n • y) = (m * n) • b x y := by
  have hl : ∀ (m : ℕ) (x y : K), b (m • x) y = m • b x y := by
    intro m x y
    induction m with
    | zero =>
      have h := hadd₁ 0 0 y
      rw [add_zero, left_eq_add] at h
      rw [zero_smul, zero_smul, h]
    | succ m ih => rw [succ_nsmul, hadd₁, ih, succ_nsmul]
  have hr : ∀ (n : ℕ) (x y : K), b x (n • y) = n • b x y := by
    intro n x y
    induction n with
    | zero =>
      have h := hadd₂ x 0 0
      rw [add_zero, left_eq_add] at h
      rw [zero_smul, zero_smul, h]
    | succ n ih => rw [succ_nsmul, hadd₂, ih, succ_nsmul]
  rw [hl, hr, smul_smul]

theorem exists_sq_add_sq [Fintype K] (hK : Fintype.card K % 2 = 1) (x : K) :
    ∃ a c : K, a ^ 2 + c ^ 2 = x := by
  obtain ⟨a, c, h⟩ := FiniteField.exists_root_sum_quadratic (R := K)
    (f := Polynomial.X ^ 2) (g := Polynomial.X ^ 2 - Polynomial.C x)
    (Polynomial.degree_X_pow 2) (Polynomial.degree_X_pow_sub_C (by norm_num) x) hK
  refine ⟨a, c, ?_⟩
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C] at h
  linear_combination h

theorem not_dvd_two_mul_pow_add_one {p f n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 2 ≤ f)
    (hn : n < f) (h9 : p ^ f ≠ 9) : ¬ p ^ f - 1 ∣ 2 * (p ^ n + 1) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hg : 1 ≤ g := by omega
  have hPn : p ^ n ≤ p ^ g := Nat.pow_le_pow_right hp.pos (by omega)
  have hPg : p ≤ p ^ g := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ g := Nat.pow_le_pow_right hp.pos hg
  have hP4 : 4 ≤ p ^ g := by
    by_contra hcon
    have h3 : p ^ g = 3 := by omega
    have hpg : p = 3 := by omega
    subst hpg
    have hg1 : g = 1 := by
      by_contra hg1
      have : 3 ^ 2 ≤ 3 ^ g := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hg1
    exact h9 (by norm_num)
  intro hdvd
  have hpos : 0 < 2 * (p ^ n + 1) := by positivity
  have hle := Nat.le_of_dvd hpos hdvd
  rw [pow_succ] at hle
  have : p ^ g * 3 ≤ p ^ g * p := Nat.mul_le_mul_left _ hp3
  omega

variable [Finite K]

theorem square_invariant_alternating_eq_zero {p f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (b : K → K → W) (hadd₁ : ∀ x x' y, b (x + x') y = b x y + b x' y)
    (hadd₂ : ∀ x y y', b x (y + y') = b x y + b x y') (halt : ∀ x, b x x = 0)
    (hinv : ∀ a : K, a ≠ 0 → ∀ x y, b (a ^ 2 * x) (a ^ 2 * y) = b x y) (h9 : p ^ f ≠ 9)
    (x y : K) : b x y = 0 := by
  classical
  have := Fintype.ofFinite K
  set B := biaddHom b hadd₁ hadd₂ with hBdef
  have hB : ∀ x y, b x y = B x y := fun _ _ => rfl
  have hchar : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hf0 : f ≠ 0 := by
    rintro rfl
    have := (Finite.one_lt_card (α := K))
    rw [hK, pow_zero] at this
    exact lt_irrefl _ this
  rcases Nat.lt_or_ge f 2 with hf | hf
  ·
    obtain rfl : f = 1 := by omega
    have : NeZero p := ⟨hp.out.ne_zero⟩
    have hbij : Function.Bijective (ZMod.castHom (dvd_refl p) K) :=
      (ZMod.castHom (dvd_refl p) K).injective.bijective_of_nat_card_le (by
        rw [hK, Nat.card_zmod, pow_one])
    obtain ⟨m, rfl⟩ := hbij.2 x
    obtain ⟨n, rfl⟩ := hbij.2 y
    have hm : (ZMod.castHom (dvd_refl p) K) m = m.val • (1 : K) := by
      rw [nsmul_one, ZMod.castHom_apply, ZMod.natCast_val]
    have hn : (ZMod.castHom (dvd_refl p) K) n = n.val • (1 : K) := by
      rw [nsmul_one, ZMod.castHom_apply, ZMod.natCast_val]
    rw [hm, hn, nsmul_nsmul_of_biadd b hadd₁ hadd₂, halt, smul_zero]
  by_contra hxy
  have hodd : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card, hK]
    exact Nat.odd_iff.1 ((hp.out.odd_of_ne_two hp2).pow)
  let Partner : K → K → Prop := fun α β => ∀ u v, b (α * u) v = b u (β * v)
  have hsq : ∀ a : K, a ≠ 0 → Partner (a ^ 2) ((a ^ 2)⁻¹) := by
    intro a ha u v
    have h := hinv a ha u ((a ^ 2)⁻¹ * v)
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 ha), one_mul] at h
    exact h
  have hzero : Partner 0 0 := fun u v => by
    rw [zero_mul, zero_mul, hB, hB, map_zero, AddMonoidHom.zero_apply, map_zero]
  have hplus : ∀ α β α' β', Partner α β → Partner α' β' → Partner (α + α') (β + β') :=
    fun α β α' β' h h' u v => by rw [add_mul, add_mul, hadd₁, hadd₂, h, h']
  have hall : ∀ α : K, ∃ β, Partner α β := by
    intro α
    obtain ⟨a, c, hac⟩ := exists_sq_add_sq hodd α
    have hpart : ∀ a : K, ∃ β, Partner (a ^ 2) β := fun a => by
      by_cases ha : a = 0
      · exact ⟨0, by rw [ha, zero_pow two_ne_zero]; exact hzero⟩
      · exact ⟨_, hsq a ha⟩
    obtain ⟨β, hβ⟩ := hpart a
    obtain ⟨β', hβ'⟩ := hpart c
    exact ⟨β + β', hac ▸ hplus _ _ _ _ hβ hβ'⟩
  have huniq : ∀ α β β', Partner α β → Partner α β' → β = β' := by
    intro α β β' h h'
    by_contra hne
    apply hxy
    have hd : β - β' ≠ 0 := sub_ne_zero.2 hne
    have key : b x ((β - β') * ((β - β')⁻¹ * y)) = 0 := by
      rw [sub_mul, hB, map_sub, ← hB, ← hB, ← h, ← h', sub_self]
    rwa [← mul_assoc, mul_inv_cancel₀ hd, one_mul] at key
  choose τ hτ using hall
  have hτeq : ∀ α β, Partner α β → τ α = β := fun α β h => huniq α _ _ (hτ α) h
  let τR : K →+* K :=
    { toFun := τ
      map_one' := hτeq 1 1 fun u v => by rw [one_mul, one_mul]
      map_mul' := fun α α' => hτeq _ _ fun u v => by
        rw [mul_assoc, hτ α, hτ α', mul_comm (τ α) (τ α'), mul_assoc]
      map_zero' := hτeq 0 0 hzero
      map_add' := fun α α' => hτeq _ _ (hplus _ _ _ _ (hτ α) (hτ α')) }
  have hτsq : ∀ a : K, a ≠ 0 → τR (a ^ 2) = (a ^ 2)⁻¹ := fun a ha => hτeq _ _ (hsq a ha)
  let : Algebra (ZMod p) K := ZMod.algebra K p
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hcomm : ∀ r : ZMod p, τR (algebraMap (ZMod p) K r) = algebraMap (ZMod p) K r :=
    fun r => DFunLike.congr_fun
      (RingHom.ext_zmod (τR.comp (algebraMap (ZMod p) K)) (algebraMap (ZMod p) K)) r
  let τA : K →ₐ[ZMod p] K := { τR with commutes' := hcomm }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) K).2 τA
  have hfin : Module.finrank (ZMod p) K = f := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod p) (V := K)
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card] at h1
    exact (Nat.pow_right_injective hp.out.two_le h1).symm
  have hτpow : ∀ z : K, τR z = z ^ (p ^ (n : ℕ)) := by
    intro z
    have h := DFunLike.congr_fun hn z
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card] at h
    exact h.symm
  have hall1 : ∀ a : Kˣ, a ^ (2 * (p ^ (n : ℕ) + 1)) = 1 := by
    intro a
    apply Units.ext
    have h := hτsq a a.ne_zero
    rw [hτpow, ← pow_mul] at h
    rw [Units.val_pow_eq_pow_val, Units.val_one, mul_add, mul_one, pow_add, h,
      inv_mul_cancel₀ (pow_ne_zero 2 a.ne_zero)]
  have hdvd := (FiniteField.forall_pow_eq_one_iff (K := K) _).1 hall1
  rw [← Nat.card_eq_fintype_card, hK] at hdvd
  exact not_dvd_two_mul_pow_add_one hp.out hp2 hf (hfin ▸ n.isLt) h9 hdvd

end CFSG.SectionRank.OddCover
