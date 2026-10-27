module

public import CFSG.LocalAnalysis.SectionRank.OddCover.CubicKernel
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.SectionRank.OddCover

open Matrix CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def u3Mat (a b c : K) : Matrix (Fin 3) (Fin 3) K := !![1, a, c; 0, 1, b; 0, 0, 1]

theorem u3Mat_mul (a b c a' b' c' : K) :
    u3Mat a b c * u3Mat a' b' c' = u3Mat (a + a') (b + b') (c + c' + a * b') := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [u3Mat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring

theorem u3Mat_zero : u3Mat (0 : K) 0 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [u3Mat]

theorem det_u3Mat (a b c : K) : (u3Mat a b c).det = 1 := by simp [u3Mat, det_fin_three]

theorem u3Mat_inv_left (a b c : K) : u3Mat (-a) (-b) (a * b - c) * u3Mat a b c = 1 := by
  rw [u3Mat_mul, ← u3Mat_zero]; congr 1 <;> ring

theorem u3Mat_inv_right (a b c : K) : u3Mat a b c * u3Mat (-a) (-b) (a * b - c) = 1 := by
  rw [u3Mat_mul, ← u3Mat_zero]; congr 1 <;> ring

@[expose] def u3SL (a b c : K) : StatedSL 3 K :=
  ⟨⟨u3Mat a b c, u3Mat (-a) (-b) (a * b - c), u3Mat_inv_right a b c, u3Mat_inv_left a b c⟩,
    Subgroup.subset_closure (det_u3Mat a b c)⟩

theorem coe_u3SL (a b c : K) :
    (((u3SL a b c : StatedSL 3 K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = u3Mat a b c :=
  rfl

theorem u3SL_mul (a b c a' b' c' : K) :
    u3SL a b c * u3SL a' b' c' = u3SL (a + a') (b + b') (c + c' + a * b') :=
  Subtype.ext (Units.ext (u3Mat_mul a b c a' b' c'))

theorem u3SL_zero : u3SL (0 : K) 0 0 = 1 := Subtype.ext (Units.ext u3Mat_zero)

theorem u3SL_inv (a b c : K) : (u3SL a b c)⁻¹ = u3SL (-a) (-b) (a * b - c) :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (Units.ext (u3Mat_inv_right a b c)))

theorem u3SL_inj {a b c a' b' c' : K} (h : u3SL a b c = u3SL a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h' := congrArg (fun g : StatedSL 3 K => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
  simp only [coe_u3SL] at h'
  exact ⟨by simpa [u3Mat] using congrFun (congrFun h' 0) 1,
    by simpa [u3Mat] using congrFun (congrFun h' 1) 2,
    by simpa [u3Mat] using congrFun (congrFun h' 0) 2⟩

theorem u3SL_pow_x (a : K) (n : ℕ) : u3SL a 0 0 ^ n = u3SL ((n : K) * a) 0 0 := by
  induction n with
  | zero => simp [u3SL_zero]
  | succ n ih => rw [pow_succ, ih, u3SL_mul]; congr 1 <;> push_cast <;> ring

theorem u3SL_pow_y (b : K) (n : ℕ) : u3SL 0 b 0 ^ n = u3SL 0 ((n : K) * b) 0 := by
  induction n with
  | zero => simp [u3SL_zero]
  | succ n ih => rw [pow_succ, ih, u3SL_mul]; congr 1 <;> push_cast <;> ring

theorem u3SL_pow_z (c : K) (n : ℕ) : u3SL 0 0 c ^ n = u3SL 0 0 ((n : K) * c) := by
  induction n with
  | zero => simp [u3SL_zero]
  | succ n ih => rw [pow_succ, ih, u3SL_mul]; congr 1 <;> push_cast <;> ring

@[expose] def heisSL : Subgroup (StatedSL 3 K) where
  carrier := {g | ∃ a b c : K, g = u3SL a b c}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨_, _, _, u3SL_mul a b c a' b' c'⟩
  one_mem' := ⟨0, 0, 0, u3SL_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    exact ⟨_, _, _, u3SL_inv a b c⟩

theorem card_heisSL [Finite K] : Nat.card (heisSL (K := K)) = Nat.card K ^ 3 := by
  let φ : K × K × K → heisSL (K := K) := fun v => ⟨u3SL v.1 v.2.1 v.2.2, _, _, _, rfl⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun v w h => ?_, fun g => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := u3SL_inj (congrArg Subtype.val h)
      exact Prod.ext h1 (Prod.ext h2 h3)
    · obtain ⟨a, b, c, hg⟩ := g.2
      exact ⟨(a, b, c), Subtype.ext hg.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod, Nat.card_prod]
  ring

@[expose] def slX : StatedSL 3 K := u3SL 1 0 0

@[expose] def slY : StatedSL 3 K := u3SL 0 1 0

theorem commutator_slX_slY : ⁅(slX : StatedSL 3 K), (slY : StatedSL 3 K)⁆ = u3SL 0 0 1 := by
  rw [commutatorElement_def, slX, slY, u3SL_inv, u3SL_inv, u3SL_mul, u3SL_mul, u3SL_mul]
  congr 1 <;> ring

@[expose] noncomputable def slH : StatedSL 3 K :=
  ⟨diagHom 3 ![-1, 1, -1], monomialData_statedSL.diag_mem _ (fun _ => Subgroup.mem_top _)
    (by simp)⟩

theorem slH_conj_u3SL (a b c : K) : slH * u3SL a b c * slH⁻¹ = u3SL (-a) (-b) c := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, coe_u3SL]
  rw [show ((slH : StatedSL 3 K) : GL (Fin 3) K) = diagHom 3 ![-1, 1, -1] from rfl,
    ← map_inv, coe_diagHom, coe_diagHom]
  ext i j; fin_cases i <;> fin_cases j <;> simp [u3Mat, Matrix.mul_apply, diagonal_apply]

theorem det_ne_zero_of_neg_one {p : ℕ} (hp1 : 1 ≤ p) (h4 : ¬ p ∣ 4) :
    (((1 : ℕ) : ZMod p) * ((p - 1 : ℕ) : ZMod p) - 1) *
        (((1 : ℕ) : ZMod p) * ((p - 1 : ℕ) : ZMod p) - 1) -
      ((1 : ℕ) : ZMod p) ^ 2 * ((0 : ℕ) : ZMod p) * ((0 : ℕ) : ZMod p) ≠ 0 := by
  have h : (((1 : ℕ) : ZMod p) * ((p - 1 : ℕ) : ZMod p) - 1) *
        (((1 : ℕ) : ZMod p) * ((p - 1 : ℕ) : ZMod p) - 1) -
      ((1 : ℕ) : ZMod p) ^ 2 * ((0 : ℕ) : ZMod p) * ((0 : ℕ) : ZMod p) = ((4 : ℕ) : ZMod p) := by
    rw [Nat.cast_sub hp1, ZMod.natCast_self]
    push_cast
    ring
  rw [h, Ne, ZMod.natCast_eq_zero_iff]
  exact h4

section Prime

variable [Finite K] {p : ℕ} [hp : Fact p.Prime]

theorem exists_natCast_eq (hK : Nat.card K = p) (k : K) : ∃ n : ℕ, (n : K) = k := by
  have := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK,
    pow_one])
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hbij : Function.Bijective (ZMod.castHom (dvd_refl p) K) :=
    (ZMod.castHom (dvd_refl p) K).injective.bijective_of_nat_card_le (by rw [hK, Nat.card_zmod])
  obtain ⟨m, rfl⟩ := hbij.2 k
  exact ⟨m.val, by rw [ZMod.castHom_apply, ZMod.natCast_val]⟩

theorem closure_slX_slY (hK : Nat.card K = p) :
    Subgroup.closure ({slX, slY} : Set (StatedSL 3 K)) = heisSL := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨1, 0, 0, rfl⟩
    · exact ⟨0, 1, 0, rfl⟩
  · rintro _ ⟨a, b, c, rfl⟩
    obtain ⟨n₁, rfl⟩ := exists_natCast_eq hK a
    obtain ⟨n₂, rfl⟩ := exists_natCast_eq hK b
    obtain ⟨n₃, hn₃⟩ := exists_natCast_eq hK (c - (n₁ : K) * n₂)
    have hx : slX ∈ Subgroup.closure ({slX, slY} : Set (StatedSL 3 K)) :=
      Subgroup.subset_closure (by simp)
    have hy : slY ∈ Subgroup.closure ({slX, slY} : Set (StatedSL 3 K)) :=
      Subgroup.subset_closure (by simp)
    have hz : u3SL (0 : K) 0 1 ∈ Subgroup.closure ({slX, slY} : Set (StatedSL 3 K)) := by
      rw [← commutator_slX_slY, commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
        (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    have heq : u3SL (n₁ : K) n₂ c = slX ^ n₁ * slY ^ n₂ * u3SL 0 0 1 ^ n₃ := by
      rw [slX, slY, u3SL_pow_x, u3SL_pow_y, u3SL_pow_z, u3SL_mul, u3SL_mul, hn₃]
      congr 1 <;> ring
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hx _)
      (Subgroup.pow_mem _ hy _)) (Subgroup.pow_mem _ hz _)

theorem card_closure_slX_slY (hK : Nat.card K = p) :
    Nat.card (Subgroup.closure ({slX, slY} : Set (StatedSL 3 K))) = p ^ 3 := by
  rw [closure_slX_slY hK, card_heisSL, hK]

theorem not_pow_four_dvd_card_statedSL (hK : Nat.card K = p) :
    ¬ p ^ 4 ∣ Nat.card (StatedSL 3 K) := by
  have hp' := hp.out
  rw [card_statedSL_three, hK]
  intro h
  have h1 : p ^ 3 * p ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
    rw [← pow_succ, ← mul_assoc]; exact h
  have h2 : p ∣ (p ^ 2 - 1) * (p ^ 3 - 1) :=
    Nat.dvd_of_mul_dvd_mul_left (pow_pos hp'.pos 3) h1
  rcases (Nat.Prime.dvd_mul hp').1 h2 with h3 | h3
  · have := Nat.dvd_sub (dvd_pow_self p two_ne_zero) h3
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp'.pos)] at this
    exact hp'.one_lt.ne' (Nat.dvd_one.1 this)
  · have := Nat.dvd_sub (dvd_pow_self p three_ne_zero) h3
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp'.pos)] at this
    exact hp'.one_lt.ne' (Nat.dvd_one.1 this)

theorem charP_of_card_prime (hK : Nat.card K = p) : CharP K p := by
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK, pow_one])

theorem slX_pow_p (hK : Nat.card K = p) : (slX : StatedSL 3 K) ^ p = 1 := by
  have := charP_of_card_prime hK
  rw [slX, u3SL_pow_x, CharP.cast_eq_zero, zero_mul, u3SL_zero]

theorem slY_pow_p (hK : Nat.card K = p) : (slY : StatedSL 3 K) ^ p = 1 := by
  have := charP_of_card_prime hK
  rw [slY, u3SL_pow_y, CharP.cast_eq_zero, zero_mul, u3SL_zero]

theorem slH_conj_slX (hK : Nat.card K = p) :
    slH * slX * slH⁻¹ = (slX : StatedSL 3 K) ^ (p - 1) * (slY : StatedSL 3 K) ^ 0 *
      ⁅(slX : StatedSL 3 K), (slY : StatedSL 3 K)⁆ ^ 0 := by
  have := charP_of_card_prime hK
  rw [slX, slH_conj_u3SL, pow_zero, pow_zero, mul_one, mul_one, u3SL_pow_x,
    Nat.cast_sub hp.out.one_lt.le, CharP.cast_eq_zero, Nat.cast_one, neg_zero]
  congr 1
  ring

theorem slH_conj_slY (hK : Nat.card K = p) :
    slH * slY * slH⁻¹ = (slX : StatedSL 3 K) ^ 0 * (slY : StatedSL 3 K) ^ (p - 1) *
      ⁅(slX : StatedSL 3 K), (slY : StatedSL 3 K)⁆ ^ 0 := by
  have := charP_of_card_prime hK
  rw [slY, slH_conj_u3SL, pow_zero, pow_zero, one_mul, mul_one, u3SL_pow_y,
    Nat.cast_sub hp.out.one_lt.le, CharP.cast_eq_zero, Nat.cast_one, neg_zero]
  congr 1
  ring

omit [Finite K] [hp : Fact p.Prime] in
theorem slH_conj_slZ : slH * ⁅(slX : StatedSL 3 K), (slY : StatedSL 3 K)⁆ * slH⁻¹ =
    ⁅(slX : StatedSL 3 K), (slY : StatedSL 3 K)⁆ ^ 1 := by
  rw [pow_one, commutator_slX_slY, slH_conj_u3SL]
  simp

omit [Finite K] [hp : Fact p.Prime] in
theorem commutator_slX_slY_ne_one : ⁅(slX : StatedSL 3 K), (slY : StatedSL 3 K)⁆ ≠ 1 := by
  rw [commutator_slX_slY, ← u3SL_zero]
  intro h
  exact one_ne_zero (u3SL_inj h).2.2

omit [Finite K] [hp : Fact p.Prime] in
theorem commute_slZ_slX :
    Commute ⁅(slX : StatedSL 3 K), (slY : StatedSL 3 K)⁆ (slX : StatedSL 3 K) := by
  rw [commutator_slX_slY, slX]
  change u3SL 0 0 1 * u3SL 1 0 0 = u3SL 1 0 0 * u3SL 0 0 1
  rw [u3SL_mul, u3SL_mul]; congr 1 <;> ring

omit [Finite K] [hp : Fact p.Prime] in
theorem commute_slZ_slY :
    Commute ⁅(slX : StatedSL 3 K), (slY : StatedSL 3 K)⁆ (slY : StatedSL 3 K) := by
  rw [commutator_slX_slY, slY]
  change u3SL 0 0 1 * u3SL 0 1 0 = u3SL 0 1 0 * u3SL 0 0 1
  rw [u3SL_mul, u3SL_mul]; congr 1 <;> ring

omit [Finite K] [hp : Fact p.Prime] in
theorem u3SL_pow (a b c : K) (n : ℕ) :
    u3SL a b c ^ n =
      u3SL ((n : K) * a) ((n : K) * b) ((n : K) * c + (n.choose 2 : ℕ) * (a * b)) := by
  induction n with
  | zero => simp [u3SL_zero]
  | succ n ih =>
    rw [pow_succ, ih, u3SL_mul, Nat.choose_succ_succ, Nat.choose_one_right]
    congr 1 <;> push_cast <;> ring

theorem u3SL_pow_p (hp2 : p ≠ 2) (hK : Nat.card K = p) (a b c : K) : u3SL a b c ^ p = 1 := by
  have := charP_of_card_prime hK
  rw [u3SL_pow, CharP.cast_eq_zero, zero_mul, zero_mul, zero_mul, zero_add, ← u3SL_zero]
  congr 1
  have hdvd : p ∣ p.choose 2 := hp.out.dvd_choose_self (by norm_num)
    (by have := hp.out.two_le; omega)
  rw [(CharP.cast_eq_zero_iff K p _).2 hdvd, zero_mul]

omit [Finite K] [hp : Fact p.Prime] in
theorem commutator_u3SL (a b c a' b' c' : K) :
    ⁅u3SL a b c, u3SL a' b' c'⁆ = u3SL 0 0 (a * b' - a' * b) := by
  rw [commutatorElement_def, u3SL_inv, u3SL_inv, u3SL_mul, u3SL_mul, u3SL_mul]
  congr 1 <;> ring

theorem prime_linear_three_sylow_normalizer (hp2 : p ≠ 2) (hK : Nat.card K = p) :
    (∃ Q : Sylow p (StatedSL 3 K),
      (Q : Subgroup (StatedSL 3 K)) = Subgroup.closure ({slX, slY} : Set (StatedSL 3 K))) ∧
    Nat.card (Subgroup.closure ({slX, slY} : Set (StatedSL 3 K))) = p ^ 3 ∧
    (∀ g ∈ Subgroup.closure ({slX, slY} : Set (StatedSL 3 K)), g ^ p = 1) ∧
    orderOf ⁅(slX : StatedSL 3 K), (slY : StatedSL 3 K)⁆ = p ∧
    (∀ g ∈ Subgroup.closure ({slX, slY} : Set (StatedSL 3 K)),
      (∀ q ∈ Subgroup.closure ({slX, slY} : Set (StatedSL 3 K)), Commute g q) ↔
        g ∈ Subgroup.zpowers ⁅(slX : StatedSL 3 K), (slY : StatedSL 3 K)⁆) ∧
    (∀ g ∈ Subgroup.closure ({slX, slY} : Set (StatedSL 3 K)),
      ∀ q ∈ Subgroup.closure ({slX, slY} : Set (StatedSL 3 K)),
        ⁅g, q⁆ ∈ Subgroup.zpowers ⁅(slX : StatedSL 3 K), (slY : StatedSL 3 K)⁆) ∧
    slH ∈ Subgroup.normalizer
      (Subgroup.closure ({slX, slY} : Set (StatedSL 3 K)) : Set (StatedSL 3 K)) ∧
    slH * slX * slH⁻¹ = (slX : StatedSL 3 K) ^ (p - 1) ∧
    slH * slY * slH⁻¹ = (slY : StatedSL 3 K) ^ (p - 1) ∧
    slH * ⁅(slX : StatedSL 3 K), (slY : StatedSL 3 K)⁆ * slH⁻¹ =
      ⁅(slX : StatedSL 3 K), (slY : StatedSL 3 K)⁆ := by
  have hc := charP_of_card_prime hK
  rw [closure_slX_slY hK]
  have hzpow : ∀ g : StatedSL 3 K,
      g ∈ Subgroup.zpowers ⁅(slX : StatedSL 3 K), (slY : StatedSL 3 K)⁆ ↔
      ∃ c : K, g = u3SL 0 0 c := by
    intro g
    rw [commutator_slX_slY, ← mem_powers_iff_mem_zpowers]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨_, (u3SL_pow_z 1 n)⟩
    · rintro ⟨c, rfl⟩
      obtain ⟨n, rfl⟩ := exists_natCast_eq hK c
      refine ⟨n, ?_⟩
      show u3SL 0 0 1 ^ n = _
      rw [u3SL_pow_z, mul_one]
  refine ⟨⟨Sylow.ofCard heisSL ?_, rfl⟩, by rw [card_heisSL, hK], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_heisSL, hK]
    have hf : (Nat.card (StatedSL 3 K)).factorization p = 3 := by
      have h3 : p ^ 3 ∣ Nat.card (StatedSL 3 K) := by
        rw [← hK, ← card_heisSL]; exact Subgroup.card_subgroup_dvd_card _
      have h3' := (hp.out.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h3
      have h4 : ¬ 4 ≤ (Nat.card (StatedSL 3 K)).factorization p := fun h4 =>
        not_pow_four_dvd_card_statedSL hK
          ((hp.out.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 h4)
      omega
    rw [hf]
  · rintro _ ⟨a, b, c, rfl⟩
    exact u3SL_pow_p hp2 hK a b c
  · rw [commutator_slX_slY]
    refine orderOf_eq_prime ?_ ?_
    · rw [u3SL_pow_z, CharP.cast_eq_zero, zero_mul, u3SL_zero]
    · rw [← u3SL_zero]
      intro h
      exact one_ne_zero (u3SL_inj h).2.2
  · rintro _ ⟨a, b, c, rfl⟩
    rw [hzpow]
    constructor
    · intro h
      have h1 := commutatorElement_eq_one_iff_commute.2 (h _ ⟨1, 0, 0, rfl⟩)
      have h2 := commutatorElement_eq_one_iff_commute.2 (h _ ⟨0, 1, 0, rfl⟩)
      rw [commutator_u3SL, ← u3SL_zero] at h1 h2
      have hb : b = 0 := by have := (u3SL_inj h1).2.2; linear_combination -this
      have ha : a = 0 := by have := (u3SL_inj h2).2.2; linear_combination this
      exact ⟨c, by rw [ha, hb]⟩
    · rintro ⟨c', hc'⟩ _ ⟨a', b', c'', rfl⟩
      rw [hc']
      apply commutatorElement_eq_one_iff_commute.1
      rw [commutator_u3SL, ← u3SL_zero]
      congr 1
      ring
  · rintro _ ⟨a, b, c, rfl⟩ _ ⟨a', b', c', rfl⟩
    rw [hzpow, commutator_u3SL]
    exact ⟨_, rfl⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨a, b, c, rfl⟩
      exact ⟨_, _, _, slH_conj_u3SL a b c⟩
    · rintro ⟨a, b, c, hg⟩
      refine ⟨-a, -b, c, ?_⟩
      have hinv : (slH : StatedSL 3 K)⁻¹ = slH := by
        apply inv_eq_of_mul_eq_one_left
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_one,
          show ((slH : StatedSL 3 K) : GL (Fin 3) K) = diagHom 3 ![-1, 1, -1] from rfl, ← map_mul,
          ← map_one (diagHom (K := K) 3)]
        congr 1
        funext i
        fin_cases i <;> simp
      calc g = slH⁻¹ * (slH * g * slH⁻¹) * slH := by group
        _ = slH * u3SL a b c * slH⁻¹ := by rw [hg, hinv]
        _ = u3SL (-a) (-b) c := slH_conj_u3SL a b c
  · have := slH_conj_slX hK
    rwa [pow_zero, pow_zero, mul_one, mul_one] at this
  · have := slH_conj_slY hK
    rwa [pow_zero, pow_zero, one_mul, mul_one] at this
  · have := slH_conj_slZ (K := K)
    rwa [pow_one] at this

theorem not_dvd_four_of_odd (hp2 : p ≠ 2) : ¬ p ∣ 4 := by
  intro h
  have : p ∣ 2 := hp.out.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)

theorem statedSL_three_sylow_kernel_eq_bot (hp2 : p ≠ 2) (hK : Nat.card K = p) {E : Type*}
    [Group E] [Finite E] [Group.IsPerfect E] (π : E →* StatedSL 3 K)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (Cp : Sylow p π.ker) :
    (Cp : Subgroup π.ker) = ⊥ :=
  cubic_extraspecial_sylow_central_kernel π hπ hC (slX_pow_p hK) (slY_pow_p hK)
    commutator_slX_slY_ne_one commute_slZ_slX commute_slZ_slY (card_closure_slX_slY hK)
    (not_pow_four_dvd_card_statedSL hK) (slH_conj_slX hK) (slH_conj_slY hK) slH_conj_slZ
    (det_ne_zero_of_neg_one hp.out.one_lt.le (not_dvd_four_of_odd hp2)) Cp

end Prime

end CFSG.SectionRank.OddCover
