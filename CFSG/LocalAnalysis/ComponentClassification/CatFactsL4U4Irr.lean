module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Order
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open Polynomial Module

variable {F : Type*} [Field F] [Fintype F]

theorem end_eq_one_of_pow_eq_one {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] {s e : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (hsq : s ∣ Fintype.card F ^ 2 ^ e + 1) (hd : finrank F W < 2 ^ (e + 1))
    {u : Module.End F W} (hu : u ^ s = 1) : u = 1 := by
  classical
  let b := Module.finBasisOfFinrankEq F W rfl
  let φ : (Module.End F W)ˣ ≃* GL (Fin (finrank F W)) F :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  have : Finite (Module.End F W)ˣ := Finite.of_equiv _ φ.symm.toEquiv
  have hcard : ¬ s ∣ Nat.card (Module.End F W)ˣ := by
    rw [Nat.card_congr φ.toEquiv]
    exact not_dvd_card_GL hs hs2 hsq hd
  have h1 := eq_one_of_pow_eq_one_of_not_dvd hs hcard (Units.pow_ofPowEqOne hu hs.ne_zero)
  have h2 := congrArg Units.val h1
  rwa [Units.val_ofPowEqOne, Units.val_one] at h2

theorem one_add_pow_of_mul_self_eq_zero {R : Type*} [Ring R] {N : R} (hN : N * N = 0) (n : ℕ) :
    (1 + N) ^ n = 1 + n • N := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, smul_mul_assoc, hN,
      smul_zero, add_zero, succ_nsmul]
    abel

theorem natCast_ne_zero_of_dvd {s e : ℕ} (hs : s.Prime) (hsq : s ∣ Fintype.card F ^ 2 ^ e + 1) :
    (s : F) ≠ 0 := by
  intro h0
  have hc : ringChar F ∣ s := (ringChar.spec F s).1 h0
  have hcs : ringChar F = s :=
    (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime F (ringChar F)) hs).1 hc
  apply not_dvd_of_dvd_pow_add_one hs hsq
  obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
  rw [hn, ← hcs]
  exact dvd_pow_self _ (Nat.pos_iff_ne_zero.1 n.2)

theorem invariant_eq_bot_or_top {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {s e : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hsq : s ∣ Fintype.card F ^ 2 ^ e + 1)
    (hdim : finrank F V ≤ 2 ^ (e + 1)) {g : Module.End F V} (hgs : g ^ s = 1) (hg1 : g ≠ 1)
    (W : Submodule F V) (hW : W ≤ W.comap g) : W = ⊥ ∨ W = ⊤ := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hbot, htop⟩ := hne
  have hlt := Submodule.finrank_lt htop
  have hpos : 0 < finrank F W := Nat.pos_of_ne_zero fun h => hbot (Submodule.finrank_eq_zero.1 h)
  have hWg : ∀ w ∈ W, g w = w := by
    have hpow : ∀ (n : ℕ) (w : W), (((g.restrict hW) ^ n) w : V) = (g ^ n) w := by
      intro n
      induction n with
      | zero => intro w; rfl
      | succ n ih =>
        intro w
        rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih, pow_succ',
          Module.End.mul_apply]
    have hr : (g.restrict hW) ^ s = 1 := by
      refine LinearMap.ext fun w => Subtype.ext ?_
      rw [hpow, hgs]
      rfl
    have := end_eq_one_of_pow_eq_one hs hs2 hsq (by omega) hr
    intro w hw
    have h := congrArg (fun u : Module.End F W => (u ⟨w, hw⟩ : V)) this
    simpa using h
  have hQg : ∀ v, g v - v ∈ W := by
    have hq : (W.mapQ W g hW) ^ s = 1 := by
      rw [← Submodule.mapQ_pow]
      refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
      simp [hgs]
    have hdq : finrank F (V ⧸ W) < 2 ^ (e + 1) := by
      have := W.finrank_quotient_add_finrank
      omega
    have := end_eq_one_of_pow_eq_one hs hs2 hsq hdq hq
    intro v
    have h := congrArg (fun u : Module.End F (V ⧸ W) => u (Submodule.Quotient.mk v)) this
    simp only [Submodule.mapQ_apply, Module.End.one_apply] at h
    exact (Submodule.Quotient.eq W).1 h
  set N := g - 1 with hN
  have hNN : N * N = 0 := by
    refine LinearMap.ext fun v => ?_
    have h1 := hQg v
    rw [Module.End.mul_apply, hN, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sub_apply,
      Module.End.one_apply, hWg _ h1, sub_self, LinearMap.zero_apply]
  have hgN : g = 1 + N := by rw [hN]; abel
  have h1 := one_add_pow_of_mul_self_eq_zero hNN s
  rw [← hgN, hgs] at h1
  have hsN : (s : F) • N = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    have := congrArg (· - 1) h1
    simpa using this.symm
  apply hg1
  rw [hgN, (smul_eq_zero.1 hsN).resolve_left (natCast_ne_zero_of_dvd hs hsq), add_zero]

omit [Fintype F] in
theorem commute_aeval {V : Type*} [AddCommGroup V] [Module F V] {g k : Module.End F V}
    (hk : Commute g k) (P : F[X]) : Commute k (aeval g P) := by
  rw [aeval_eq_sum_range]
  exact Commute.sum_right _ _ _ fun i _ => (hk.symm.pow_right i).smul_right _

omit [Fintype F] in
theorem exists_eq_aeval_of_commute {V : Type*} [AddCommGroup V] [Module F V] [Nontrivial V]
    {g : Module.End F V} (hirr : ∀ W : Submodule F V, W ≤ W.comap g → W = ⊥ ∨ W = ⊤)
    {k : Module.End F V} (hk : Commute g k) : ∃ P : F[X], k = aeval g P := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  set φ : F[X] →ₗ[F] V := (LinearMap.applyₗ v).comp (aeval g).toLinearMap with hφdef
  have hφ : ∀ P, φ P = aeval g P v := fun P => rfl
  set W := LinearMap.range φ with hWdef
  have hWg : W ≤ W.comap g := by
    rintro _ ⟨P, rfl⟩
    refine ⟨X * P, ?_⟩
    rw [hφ, hφ, map_mul, aeval_X, Module.End.mul_apply]
  have hvW : v ∈ W := ⟨1, by rw [hφ, map_one, Module.End.one_apply]⟩
  have hW : W = ⊤ := (hirr W hWg).resolve_left fun h => hv (by
    rw [h] at hvW
    exact (Submodule.mem_bot F).1 hvW)
  obtain ⟨P, hP⟩ : k v ∈ W := hW ▸ Submodule.mem_top
  refine ⟨P, LinearMap.ext fun w => ?_⟩
  obtain ⟨Q, rfl⟩ : w ∈ W := hW ▸ Submodule.mem_top
  rw [hφ, ← Module.End.mul_apply, (commute_aeval hk Q).eq, Module.End.mul_apply, ← hP, hφ,
    ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]

omit [Fintype F] in
theorem bilin_aeval_left {V : Type*} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    {g g' : Module.End F V} (hgg : ∀ x y, B (g x) y = B x (g' y)) (P : F[X]) (x y : V) :
    B (aeval g P x) y = B x (aeval g' P y) := by
  have hpow : ∀ (n : ℕ) (x y : V), B ((g ^ n) x) y = B x ((g' ^ n) y) := by
    intro n
    induction n with
    | zero => intro x y; rfl
    | succ n ih =>
      intro x y
      rw [pow_succ', Module.End.mul_apply, hgg, ih, pow_succ, Module.End.mul_apply]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, hP, hQ,
      LinearMap.add_apply, map_add]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul,
      LinearMap.smul_apply, hpow]

theorem expand_card_pow (P : F[X]) (m : ℕ) :
    expand F (Fintype.card F ^ m) P = P ^ (Fintype.card F ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, expand_mul, FiniteField.Polynomial.expand_card, map_pow, ih, ← pow_mul]

theorem eq_one_or_eq_neg_one_of_isometry {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {s e : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (he : 1 ≤ e)
    (hq : Odd (Fintype.card F)) (hsq : s ∣ Fintype.card F ^ 2 ^ e + 1)
    (hdim : finrank F V ≤ 2 ^ (e + 1)) (B : LinearMap.BilinForm F V)
    (hB : ∀ y, (∀ x, B x y = 0) → y = 0) {g k : Module.End F V} (hgs : g ^ s = 1)
    (hg1 : g ≠ 1) (hgB : ∀ x y, B (g x) (g y) = B x y) (hkB : ∀ x y, B (k x) (k y) = B x y)
    (hgk : Commute g k) {c : F} (hk2 : k * k = c • 1) : k = 1 ∨ k = -1 := by
  classical
  have hirr := invariant_eq_bot_or_top hs hs2 hsq hdim hgs hg1
  have : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact hg1 (LinearMap.ext fun v => Subsingleton.elim _ _)
  obtain ⟨P, hP⟩ := exists_eq_aeval_of_commute hirr hgk
  set N := Fintype.card F ^ 2 ^ e with hNdef
  set g' := g ^ (s - 1) with hg'
  have hgg' : ∀ y, g (g' y) = y := by
    intro y
    rw [← Module.End.mul_apply, hg', ← pow_succ', show s - 1 + 1 = s by have := hs.two_le; omega,
      hgs, Module.End.one_apply]
  have hgg : ∀ x y, B (g x) y = B x (g' y) := by
    intro x y
    conv_lhs => rw [← hgg' y]
    exact hgB x (g' y)
  have hgN : g ^ N = g' := by
    obtain ⟨t, ht⟩ := hsq
    have ht1 : 1 ≤ t := by
      rcases t with _ | t
      · simp at ht
      · omega
    have hst : s ≤ s * t := Nat.le_mul_of_pos_right s ht1
    have hN' : N = (s - 1) + s * (t - 1) := by
      rw [Nat.mul_sub_one]
      have := hs.two_le
      omega
    rw [hN', pow_add, pow_mul, hgs, one_pow, mul_one]
  have hkN : aeval g' P = k ^ N := by
    rw [← hgN, ← expand_aeval, hNdef, expand_card_pow, map_pow, ← hP]
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hk2
    obtain ⟨y, hy⟩ := exists_ne (0 : V)
    apply hy
    apply hB
    intro x
    have h1 : k (k x) = 0 := by rw [← Module.End.mul_apply, hk2, LinearMap.zero_apply]
    rw [← hkB, ← hkB, h1, map_zero, LinearMap.zero_apply]
  have hkk : k ^ N = k := by
    set M := Fintype.card F ^ 2 ^ (e - 1) with hM
    have hNM : N = M ^ 2 := by
      rw [hNdef, hM, ← pow_mul, ← pow_succ, show e - 1 + 1 = e by omega]
    obtain ⟨u, hu⟩ : Odd M := hq.pow
    have hcM : c ^ (M - 1) = 1 := by
      have h1 : c ^ M = c := FiniteField.pow_card_pow (2 ^ (e - 1)) c
      have h2 : c ^ (M - 1) * c = 1 * c := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega), h1, one_mul]
      exact mul_right_cancel₀ hc h2
    have hexp : N = 2 * ((M - 1) * (u + 1)) + 1 := by
      rw [hNM, hu, Nat.add_sub_cancel]
      ring
    rw [hexp, pow_succ, pow_mul, sq, hk2, smul_pow, one_pow, pow_mul, hcM, one_pow, one_smul,
      one_mul]
  have hadj : ∀ x y, B (k x) y = B x (k y) := by
    intro x y
    conv_lhs => rw [hP]
    rw [bilin_aeval_left B hgg, hkN, hkk]
  have hk1 : k * k = 1 := by
    refine LinearMap.ext fun y => ?_
    rw [Module.End.one_apply, Module.End.mul_apply]
    apply sub_eq_zero.1
    apply hB
    intro x
    rw [map_sub, ← hadj, hkB, sub_self]
  have hinv : LinearMap.ker (k - 1) ≤ (LinearMap.ker (k - 1)).comap g := by
    intro v hv
    rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      ← Module.End.mul_apply, ← hgk.eq, Module.End.mul_apply]
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    rw [hv, sub_self]
  rcases hirr _ hinv with hbot | htop
  · right
    have hinj : Function.Injective ⇑(k - 1) := LinearMap.ker_eq_bot.1 hbot
    have hsurj : Function.Surjective ⇑(k - 1) := LinearMap.injective_iff_surjective.1 hinj
    refine LinearMap.ext fun v => ?_
    obtain ⟨w, rfl⟩ := hsurj v
    have h1 : (k + 1) ((k - 1) w) = 0 := by
      rw [← Module.End.mul_apply, add_mul, mul_sub, mul_sub, hk1, one_mul, mul_one, one_mul,
        sub_add_sub_cancel, sub_self, LinearMap.zero_apply]
    rw [LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg] at h1
    rw [h1, LinearMap.neg_apply, Module.End.one_apply]
  · left
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ LinearMap.ker (k - 1) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    rw [hv, Module.End.one_apply]

end CFSG.ComponentClassification.CatFactsL4U4
