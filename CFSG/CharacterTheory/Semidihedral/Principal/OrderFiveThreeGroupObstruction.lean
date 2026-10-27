module

public import CFSG.CharacterTheory.Semidihedral.Principal.FourGroupCosetDegreeBound
public import CFSG.CharacterTheory.Semidihedral.Principal.TensorGapBound
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

theorem finrank_sub_trace_of_cube_eq_one {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] {s : Module.End ℂ W} (hs : s ^ 3 = 1) {q : ℚ}
    (hq : LinearMap.trace ℂ W s = q) :
    ∃ d : ℕ, (Module.finrank ℂ W : ℂ) - LinearMap.trace ℂ W s = 3 * d ∧
      LinearMap.trace ℂ W (s ^ 2) = LinearMap.trace ℂ W s ∧ (d = 0 → s = 1) := by
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ)) with hζdef
  have hζ : IsPrimitiveRoot ζ 3 := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  let E : Fin 3 → Submodule ℂ W := fun j => s.eigenspace (ζ ^ (j : ℕ))
  have htr : ∀ i : ℕ, LinearMap.trace ℂ W (s ^ i) =
      ∑ j : Fin 3, (ζ ^ (j : ℕ)) ^ i * (Module.finrank ℂ (E j) : ℂ) := by
    intro i
    have h := EigenCalculus.trace_mul_pow_eq_sum (Commute.one_right s) (by norm_num) hs hζ i
    rw [one_mul] at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (1 : Module.End ℂ W).restrict (EigenCalculus.mapsTo_eigenspace (Commute.one_right s)
      (ζ ^ (j : ℕ))) = 1 from by ext; rfl, LinearMap.trace_one]
  have hfin : Module.finrank ℂ W = ∑ j : Fin 3, Module.finrank ℂ (E j) :=
    EigenCalculus.finrank_eq_sum (by norm_num : (3 : ℕ) ≠ 0) hs hζ
  have htr1 : LinearMap.trace ℂ W s =
      ∑ j : Fin 3, (ζ ^ (j : ℕ)) ^ 1 * (Module.finrank ℂ (E j) : ℂ) := by
    rw [← htr 1, pow_one]
  have hq' : ∑ j : Fin 3, ((Module.finrank ℂ (E j) : ℤ) : ℂ) * ζ ^ (j : ℕ) = q := by
    rw [← hq, htr1]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have h12 := CosetConstantEigenspaces.coeff_eq_of_sum_pow_rat (by norm_num : Nat.Prime 3) hζ
    (fun j => (Module.finrank ℂ (E j) : ℤ)) hq' 1 2 (by decide) (by decide)
  simp only [Nat.cast_inj] at h12
  have hgeom : 1 + ζ + ζ ^ 2 = 0 := by
    have h := hζ.geom_sum_eq_zero (by norm_num)
    simpa [Finset.sum_range_succ] using h
  have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  refine ⟨Module.finrank ℂ (E 1), ?_, ?_, ?_⟩
  · rw [htr1, hfin, Fin.sum_univ_three, Fin.sum_univ_three, ← h12]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_mul]
    push_cast
    linear_combination (-(Module.finrank ℂ (E 1) : ℂ)) * hgeom
  · rw [htr 2, htr1, Fin.sum_univ_three, Fin.sum_univ_three, ← h12]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, one_pow, pow_one]
    linear_combination ((Module.finrank ℂ (E 1) : ℂ) * ζ) * hζ3
  · intro hd
    have h2 : Module.finrank ℂ (E 2) = 0 := by rw [← h12]; exact hd
    have hsum : Module.finrank ℂ W = Module.finrank ℂ (E 0) := by
      rw [hfin, Fin.sum_univ_three, hd, h2, add_zero, add_zero]
    have htop : E 0 = ⊤ := Submodule.eq_top_of_finrank_eq hsum.symm
    ext v
    have hv : v ∈ E 0 := htop ▸ Submodule.mem_top
    change v ∈ s.eigenspace (ζ ^ ((0 : Fin 3) : ℕ)) at hv
    rw [Fin.val_zero, pow_zero, Module.End.mem_eigenspace_iff, one_smul] at hv
    rw [hv, Module.End.one_apply]

theorem card_subtype_modEq_fixed {X : Type*} [Fintype X] [DecidableEq X] {p : ℕ}
    [Fact p.Prime] (σ : X → X) (hσ : ∀ x, σ^[p] x = x) (P : X → Prop) [DecidablePred P]
    (hP : ∀ x, P x → P (σ x)) :
    Fintype.card {x // P x} ≡ Fintype.card {x // P x ∧ σ x = x} [MOD p] := by
  let f : Function.End {x // P x} := fun y => ⟨σ y, hP y y.2⟩
  have hfpow : ∀ (n : ℕ) (y : {x // P x}), ((f ^ n) y : X) = σ^[n] y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', Function.iterate_succ_apply']
      change σ ((f ^ n) y : X) = _
      rw [ih]
  have hf : f ^ p ^ 1 = 1 := by
    rw [pow_one]
    funext y
    apply Subtype.ext
    rw [hfpow, hσ]
    rfl
  have h := Equiv.Perm.card_fixedPoints_modEq hf
  have hcard : Fintype.card (Function.fixedPoints f) =
      Fintype.card {x // P x ∧ σ x = x} := by
    apply Fintype.card_congr
    exact
      { toFun := fun y => ⟨(y : {x // P x}), (y : {x // P x}).2,
          congrArg Subtype.val (y.property : f y = y)⟩
        invFun := fun x => ⟨⟨x, x.2.1⟩, Subtype.ext x.2.2⟩
        left_inv := fun y => rfl
        right_inv := fun x => rfl }
  rw [hcard] at h
  exact h

theorem card_eq_one_or_eighty_one_of_modEq {N : Type} [Group N] [Finite N] (hN : IsPGroup 3 N)
    (hcard : Nat.card N ≤ 81) (H : Subgroup N) (hH : Nat.card H ≡ 1 [MOD 5]) :
    Nat.card H = 1 ∨ Nat.card H = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := hN.exists_card_eq
  have hm4 : m ≤ 4 := by
    have h : 3 ^ m ≤ 3 ^ 4 := by rw [← hm]; norm_num; exact hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  obtain ⟨k, hk, hHk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (hm ▸ Subgroup.card_subgroup_dvd_card H)
  rw [hHk] at hH ⊢
  have hk4 : k ≤ 4 := hk.trans hm4
  interval_cases k <;> simp_all [Nat.ModEq]

theorem sum_character_eq_card_mul {N : Type} [Group N] [Fintype N]
    (τ : FiniteComplexRepresentation.{0, 0} N) :
    ∃ m : ℕ, ∑ x : N, τ.character x = (Nat.card N : ℂ) * m := by
  obtain ⟨b⟩ := finiteIrreducibleCharacterBasis_exists (G := N)
  obtain ⟨p0, hp0⟩ := finiteIrreducibleCharacterBasis_contains_irreducible b
    (principalFiniteComplexRepresentation N) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hp0
  obtain ⟨m, hm⟩ := characterPairing_basis_natural b τ p0
  refine ⟨m, ?_⟩
  unfold characterPairing at hm
  rw [hp0] at hm
  simp only [Pi.one_apply, mul_one] at hm
  have hcard : (Nat.card N : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [← hm, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]

theorem order_five_automorphism_small_three_group_rational_character_obstruction {N : Type}
    [Group N] [Fintype N] (hN : IsPGroup 3 N) (hcard : Nat.card N ≤ 81) (α : MulAut N)
    (hα : α ^ 5 = 1) (τ : FiniteComplexRepresentation.{0, 0} N)
    (hfaith : Function.Injective τ.representation) (hrat : ∀ x, ∃ q : ℚ, τ.character x = q)
    (hdeg : Module.finrank ℂ τ.vector < 10) (hinv : ∀ x, τ.character (α x) = τ.character x) :
    α = 1 := by
  classical
  by_contra hα1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hαpow : ∀ (n : ℕ) (x : N), (α ^ n) x = (⇑α)^[n] x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, ih, Function.iterate_succ_apply']
  have hαit : ∀ x, (⇑α)^[5] x = x := fun x => by rw [← hαpow, hα]; rfl
  let F : Subgroup N :=
    { carrier := {x | α x = x}
      mul_mem' := fun {a b} ha hb => by
        change α (a * b) = a * b
        rw [map_mul, show α a = a from ha, show α b = b from hb]
      one_mem' := map_one α
      inv_mem' := fun {a} ha => by
        change α a⁻¹ = a⁻¹
        rw [map_inv, show α a = a from ha] }
  have hF : Nat.card F ≡ Nat.card N [MOD 5] := by
    have h := card_subtype_modEq_fixed (p := 5) α hαit (fun _ => True) (fun _ _ => trivial)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    have h1 : Fintype.card {x : N // True} = Fintype.card N := Fintype.card_congr
      (Equiv.subtypeUnivEquiv (fun _ => trivial))
    have h2 : Fintype.card {x : N // True ∧ α x = x} = Fintype.card F := Fintype.card_congr
      { toFun := fun x => ⟨x.1, x.2.2⟩, invFun := fun x => ⟨x.1, trivial, x.2⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    rw [h1, h2] at h
    exact h.symm
  obtain ⟨m, hm⟩ := hN.exists_card_eq
  have hm4 : m ≤ 4 := by
    have h : 3 ^ m ≤ 3 ^ 4 := by
      calc 3 ^ m = Nat.card N := hm.symm
        _ ≤ 81 := hcard
        _ = 3 ^ 4 := by norm_num
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  obtain ⟨c, hc, hFc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (hm ▸ Subgroup.card_subgroup_dvd_card F)
  rw [hFc, hm] at hF
  have hcases : c = m ∨ (m = 4 ∧ c = 0) := by
    interval_cases m <;> interval_cases c <;> simp_all [Nat.ModEq]
  have hm4' : m = 4 ∧ c = 0 := by
    rcases hcases with h | h
    · exfalso
      apply hα1
      have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [hFc, hm, h])
      ext x
      have hx : x ∈ F := htop ▸ Subgroup.mem_top x
      exact hx
    · exact h
  obtain ⟨rfl, rfl⟩ := hm4'
  have hfix : ∀ x : N, α x = x → x = 1 := by
    intro x hx
    have hxF : x ∈ F := hx
    have hbot : F = ⊥ := (Subgroup.card_eq_one).mp (by rw [hFc, pow_zero])
    rw [hbot] at hxF
    exact hxF
  have horb : ∀ H : Subgroup N, (∀ x ∈ H, α x ∈ H) → Nat.card H ≡ 1 [MOD 5] := by
    intro H hH
    have h := card_subtype_modEq_fixed (p := 5) α hαit (· ∈ H) hH
    have h1 : Fintype.card {x : N // x ∈ H ∧ α x = x} = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨1, H.one_mem, map_one α⟩, fun y => Subtype.ext (hfix y.1 y.2.2)⟩
    rw [h1] at h
    rw [Nat.card_eq_fintype_card]
    exact h
  have hNcard : Nat.card N = 81 := by rw [hm]; norm_num
  have : Nontrivial N := by
    rw [← Finite.one_lt_card_iff_nontrivial, hNcard]
    norm_num
  have hcomm : ∀ a b : N, a * b = b * a := by
    have hZ := horb (Subgroup.center N) (fun x hx => by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro g
      have h := hx (α.symm g)
      have h' := congrArg α h
      simpa [map_mul] using h')
    rcases card_eq_one_or_eighty_one_of_modEq hN hcard _ hZ with h | h
    · exfalso
      have hnt := hN.center_nontrivial
      rw [← Finite.one_lt_card_iff_nontrivial, h] at hnt
      exact absurd hnt (by norm_num)
    · have htop : Subgroup.center N = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h, hNcard])
      intro a b
      have ha : a ∈ Subgroup.center N := htop ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
  let Ω : Subgroup N :=
    { carrier := {x | x ^ 3 = 1}
      mul_mem' := fun {a b} ha hb => by
        change (a * b) ^ 3 = 1
        rw [(show Commute a b from hcomm a b).mul_pow, show a ^ 3 = 1 from ha,
          show b ^ 3 = 1 from hb, one_mul]
      one_mem' := one_pow 3
      inv_mem' := fun {a} ha => by
        change a⁻¹ ^ 3 = 1
        rw [inv_pow, show a ^ 3 = 1 from ha, inv_one] }
  have hcube : ∀ x : N, x ^ 3 = 1 := by
    have hΩ := horb Ω (fun x hx => by
      change (α x) ^ 3 = 1
      rw [← map_pow, show x ^ 3 = 1 from hx, map_one])
    rcases card_eq_one_or_eighty_one_of_modEq hN hcard _ hΩ with h | h
    · exfalso
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hNcard]; norm_num)
      have hyΩ : y ∈ Ω := by
        change y ^ 3 = 1
        rw [← hy]
        exact pow_orderOf_eq_one y
      have hbot : Ω = ⊥ := (Subgroup.card_eq_one).mp h
      rw [hbot, Subgroup.mem_bot] at hyΩ
      rw [hyΩ, orderOf_one] at hy
      norm_num at hy
    · have htop : Ω = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h, hNcard])
      intro x
      have hx : x ∈ Ω := htop ▸ Subgroup.mem_top x
      exact hx
  set f := Module.finrank ℂ τ.vector with hf
  have hex : ∀ x : N, ∃ e : ℕ, (f : ℂ) - τ.character x = 3 * e ∧
      τ.character (x ^ 2) = τ.character x ∧ (e = 0 → x = 1) := by
    intro x
    have hs : τ.representation x ^ 3 = 1 := by rw [← map_pow, hcube x, map_one]
    obtain ⟨q, hq⟩ := hrat x
    obtain ⟨e, h1, h2, h3⟩ := finrank_sub_trace_of_cube_eq_one hs hq
    refine ⟨e, h1, ?_, fun he => hfaith (by rw [h3 he, map_one])⟩
    change LinearMap.trace ℂ _ (τ.representation (x ^ 2)) = _
    rw [map_pow]
    exact h2
  choose d hdval hdsq hd0 using hex
  have hdα : ∀ x, d (α x) = d x := by
    intro x
    have h1 := hdval (α x)
    rw [hinv x] at h1
    have h : (3 : ℂ) * d (α x) = 3 * d x := h1.symm.trans (hdval x)
    exact_mod_cast mul_left_cancel₀ (by norm_num : (3 : ℂ) ≠ 0) h
  have hinvsq : ∀ x : N, x⁻¹ = x ^ 2 := fun x =>
    (eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hcube x])).symm
  have hdinv : ∀ x, d x⁻¹ = d x := by
    intro x
    have h1 := hdval x⁻¹
    have hτ : τ.character x⁻¹ = τ.character x := by rw [hinvsq x, hdsq x]
    rw [hτ] at h1
    have h : (3 : ℂ) * d x⁻¹ = 3 * d x := h1.symm.trans (hdval x)
    exact_mod_cast mul_left_cancel₀ (by norm_num : (3 : ℂ) ≠ 0) h
  have hd1 : d 1 = 0 := by
    have h := hdval 1
    rw [show τ.character 1 = (f : ℂ) from Representation.char_one τ.representation,
      sub_self] at h
    exact_mod_cast (mul_eq_zero.mp h.symm).resolve_left (by norm_num)
  have hdiv : ∀ (p : ℕ) [Fact p.Prime] (σ : N → N), (∀ x, σ^[p] x = x) →
      (∀ x, d (σ x) = d x) → (∀ x, σ x = x → x = 1) → p ∣ ∑ x, d x := by
    intro p _ σ hσ hdσ hσfix
    rw [show ∑ x, d x = ∑ x, id (d x) from rfl, Finset.sum_comp]
    apply Finset.dvd_sum
    intro v _
    by_cases hv0 : v = 0
    · simp [hv0]
    · have h := card_subtype_modEq_fixed σ hσ (fun x => d x = v)
        (fun x hx => by rw [hdσ]; exact hx)
      have h0 : Fintype.card {x // d x = v ∧ σ x = x} = 0 := by
        rw [Fintype.card_eq_zero_iff]
        constructor
        rintro ⟨x, hx, hσx⟩
        rw [hσfix x hσx, hd1] at hx
        exact hv0 hx.symm
      rw [h0, Fintype.card_subtype] at h
      rw [smul_eq_mul]
      exact Dvd.dvd.mul_right (Nat.modEq_zero_iff_dvd.mp h) _
  have h5 : 5 ∣ ∑ x, d x := hdiv 5 α hαit hdα hfix
  have h2 : 2 ∣ ∑ x, d x := hdiv 2 (fun x => x⁻¹) (fun x => by simp) hdinv (fun x hx => by
    have hx2 : x ^ 2 = 1 := by
      calc x ^ 2 = x * x := pow_two x
        _ = x * x⁻¹ := by rw [hx]
        _ = 1 := mul_inv_cancel x
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hcube, hx2, inv_one, one_mul])
  have h10 : 10 ∣ ∑ x, d x :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 5) h2 h5
  obtain ⟨m₀, hm₀⟩ := sum_character_eq_card_mul τ
  have hsum : ((∑ x, d x : ℕ) : ℂ) * 3 = 81 * ((f : ℂ) - m₀) := by
    have h := Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hdval x)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hm₀,
      ← Nat.card_eq_fintype_card, hNcard, ← Finset.mul_sum] at h
    push_cast at h ⊢
    linear_combination -h
  have hsumZ : ((∑ x, d x : ℕ) : ℤ) * 3 = 81 * ((f : ℤ) - m₀) := by exact_mod_cast hsum
  have hsum27 : ((∑ x, d x : ℕ) : ℤ) = 27 * ((f : ℤ) - m₀) := by linarith
  have h10' : (10 : ℤ) ∣ 27 * ((f : ℤ) - m₀) := by
    rw [← hsum27]
    exact_mod_cast h10
  have h10'' : (10 : ℤ) ∣ (f : ℤ) - m₀ :=
    (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)).dvd_of_dvd_mul_left h10'
  have hnonneg : 0 ≤ (f : ℤ) - m₀ := by
    have : (0 : ℤ) ≤ ((∑ x, d x : ℕ) : ℤ) := Nat.cast_nonneg _
    linarith
  have hf10 : (f : ℤ) < 10 := by exact_mod_cast hdeg
  have hzero : (f : ℤ) - m₀ = 0 := by
    obtain ⟨k, hk⟩ := h10''
    have : k = 0 := by
      have hm0 : (0 : ℤ) ≤ m₀ := Nat.cast_nonneg _
      by_contra hk0
      rcases lt_or_gt_of_ne hk0 with hlt | hgt
      · linarith
      · have : (1 : ℤ) ≤ k := hgt
        linarith
    rw [hk, this, mul_zero]
  have hdzero : ∑ x, d x = 0 := by
    have : ((∑ x, d x : ℕ) : ℤ) = 0 := by rw [hsum27, hzero, mul_zero]
    exact_mod_cast this
  obtain ⟨x, hx1⟩ := exists_ne (1 : N)
  have hdx : d x = 0 := (Finset.sum_eq_zero_iff.mp hdzero) x (Finset.mem_univ x)
  exact hx1 (hd0 x hdx)

end CFSG.Semidihedral.Principal
