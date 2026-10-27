module

public import CFSG.LocalAnalysis.ComponentInitial.CoprimeSeriesCoverTrivial
public import CFSG.LieType.Steinberg.CentralExt.FiniteFieldPairing
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCoverTorus
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LieType.Steinberg.CentralExt.CoprimeSplit
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Open.QuasithinDefs
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec

public noncomputable section

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.BenderSuzuki.PFAppendixIII
  CFSG.ShultStronglyClosedTI

namespace CFSG.LieType.Steinberg.CentralExt.SuzukiClosed

theorem two_pow_mod_eight (x : ℕ) :
    2 ^ x % 8 = if x = 0 then 1 else if x = 1 then 2 else if x = 2 then 4 else 0 := by
  rcases Nat.lt_or_ge x 3 with h | h
  · interval_cases x <;> rfl
  · obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [pow_add]
    have : (2 : ℕ) ^ 3 = 8 := by norm_num
    rw [this, Nat.mul_mod_right]
    split_ifs <;> omega

theorem eq_of_dvd_of_lt_two_mul {N s : ℕ} (hs0 : 0 < s) (hs : s < 2 * N) (h : N ∣ s) : s = N := by
  obtain ⟨c, rfl⟩ := h
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hs0
  have hc2 : c < 2 := by
    by_contra hc
    have := Nat.mul_le_mul_left N (not_lt.1 hc)
    omega
  have : c = 1 := by omega
  subst this
  ring

theorem two_pow_ge (f : ℕ) {n : ℕ} (hf : n ≤ f) : 2 ^ n ≤ 2 ^ f :=
  Nat.pow_le_pow_right (by norm_num) hf

theorem not_dvd_two_pow_add_two {f i j : ℕ} (hf : 3 ≤ f) (hi : i < f) (hj : j < f) :
    ¬ (2 ^ f - 1) ∣ 2 ^ i + 2 ^ j := by
  intro h
  have hi' : 2 ^ i ≤ 2 ^ (f - 1) := two_pow_ge (f - 1) (by omega)
  have hj' : 2 ^ j ≤ 2 ^ (f - 1) := two_pow_ge (f - 1) (by omega)
  have hf2 : 2 ^ f = 2 * 2 ^ (f - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h8 : 8 ≤ 2 ^ f := le_trans (by norm_num) (two_pow_ge f hf)
  have hpos : 0 < 2 ^ i := by positivity
  have hs := eq_of_dvd_of_lt_two_mul (by positivity) (by omega) h
  have hf8 := two_pow_mod_eight f
  have hi8 := two_pow_mod_eight i
  have hj8 := two_pow_mod_eight j
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)] at hf8
  split_ifs at hi8 hj8 <;> omega

theorem not_dvd_two_pow_add_three {f i j k : ℕ} (hf : 4 ≤ f) (hi : i < f) (hj : j < f)
    (hk : k < f) : ¬ (2 ^ f - 1) ∣ 2 ^ i + 2 ^ j + 2 ^ k := by
  intro h
  have hi' : 2 ^ i ≤ 2 ^ (f - 1) := two_pow_ge (f - 1) (by omega)
  have hj' : 2 ^ j ≤ 2 ^ (f - 1) := two_pow_ge (f - 1) (by omega)
  have hk' : 2 ^ k ≤ 2 ^ (f - 1) := two_pow_ge (f - 1) (by omega)
  have hf2 : 2 ^ f = 2 * 2 ^ (f - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h16 : 16 ≤ 2 ^ f := le_trans (by norm_num) (two_pow_ge f hf)
  have hpos : 0 < 2 ^ i := by positivity
  have hs := eq_of_dvd_of_lt_two_mul (by positivity) (by omega) h
  have hf8 := two_pow_mod_eight f
  have hi8 := two_pow_mod_eight i
  have hj8 := two_pow_mod_eight j
  have hk8 := two_pow_mod_eight k
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)] at hf8
  split_ifs at hi8 hj8 hk8 with h1 h2 h3 h4 h5 h6 h7 h8 h9 <;>
    first
    | omega
    | (subst_vars; norm_num at hs; omega)

theorem coprime_tits (m : ℕ) : Nat.Coprime (2 ^ (2 * m + 1) - 1) (1 + 2 ^ (m + 1)) := by
  set g := Nat.gcd (2 ^ (2 * m + 1) - 1) (1 + 2 ^ (m + 1))
  have h1 : g ∣ 2 ^ (2 * m + 1) - 1 := Nat.gcd_dvd_left _ _
  have h2 : g ∣ 1 + 2 ^ (m + 1) := Nat.gcd_dvd_right _ _
  have hp : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  have hq : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  have hsq : (1 + 2 ^ (m + 1)) * (2 ^ (m + 1) - 1) = 2 * (2 ^ (2 * m + 1) - 1) + 1 := by
    have e : (2 : ℕ) ^ (2 * m + 1) * 2 = 2 ^ (m + 1) * 2 ^ (m + 1) := by
      rw [← pow_succ, ← pow_add]
      congr 1
      ring
    zify [hp, hq]
    have e' : (2 : ℤ) ^ (2 * m + 1) * 2 = 2 ^ (m + 1) * 2 ^ (m + 1) := by exact_mod_cast e
    linear_combination (-1 : ℤ) * e'
  have h3 : g ∣ 2 * (2 ^ (2 * m + 1) - 1) + 1 := by
    rw [← hsq]
    exact Dvd.dvd.mul_right h2 _
  have h4 : g ∣ 1 := (Nat.dvd_add_right (Dvd.dvd.mul_left h1 2)).1 h3
  exact Nat.dvd_one.1 h4

theorem weight_not_dvd {m : ℕ} (hm : 2 ≤ m) {e₁ e₂ : ℕ}
    (he₁ : e₁ = 1 ∨ e₁ = 1 + 2 ^ (m + 1)) (he₂ : e₂ = 1 ∨ e₂ = 1 + 2 ^ (m + 1)) :
    ∀ i j : ℕ, i < 2 * m + 1 → j < 2 * m + 1 →
      ¬ (2 ^ (2 * m + 1) - 1) ∣ 2 ^ i * e₁ + 2 ^ j * e₂ := by
  intro i j hi hj
  set f := 2 * m + 1 with hfdef
  have hf5 : 5 ≤ f := by omega
  have hred : ∀ x, x < f → ∃ y, y < f ∧
      ∀ s, (2 ^ f - 1) ∣ s + 2 ^ x * (1 + 2 ^ (m + 1)) → (2 ^ f - 1) ∣ s + 2 ^ x + 2 ^ y := by
    intro x hx
    by_cases hxm : x + (m + 1) < f
    · refine ⟨x + (m + 1), hxm, fun s hs => ?_⟩
      have e : s + 2 ^ x * (1 + 2 ^ (m + 1)) = s + 2 ^ x + 2 ^ (x + (m + 1)) := by
        rw [pow_add]
        ring
      rwa [e] at hs
    · refine ⟨x + (m + 1) - f, by omega, fun s hs => ?_⟩
      have hle : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      have e : s + 2 ^ x * (1 + 2 ^ (m + 1)) =
          s + 2 ^ x + 2 ^ (x + (m + 1) - f) + (2 ^ f - 1) * 2 ^ (x + (m + 1) - f) := by
        have e1 : 2 ^ x * 2 ^ (m + 1) = 2 ^ f * 2 ^ (x + (m + 1) - f) := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
        have e2 : (2 ^ f - 1) * 2 ^ (x + (m + 1) - f) + 2 ^ (x + (m + 1) - f) =
            2 ^ f * 2 ^ (x + (m + 1) - f) := by
          rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel]
          exact Nat.le_mul_of_pos_left _ (by positivity)
        rw [mul_add, mul_one, e1, ← e2]
        ring
      rw [e, add_comm] at hs
      exact (Nat.dvd_add_right (dvd_mul_right _ _)).1 hs
  rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl
  · rw [mul_one, mul_one]
    exact not_dvd_two_pow_add_two (by omega) hi hj
  · intro h
    obtain ⟨y, hy, hy'⟩ := hred j hj
    have := hy' (2 ^ i * 1) h
    rw [mul_one, add_assoc] at this
    exact not_dvd_two_pow_add_three (by omega) hi hj hy (by rwa [← add_assoc] at this)
  · intro h
    obtain ⟨y, hy, hy'⟩ := hred i hi
    have := hy' (2 ^ j * 1) (by rw [add_comm]; exact h)
    rw [mul_one] at this
    exact not_dvd_two_pow_add_three (by omega) hj hi hy this
  · intro h
    rw [← add_mul] at h
    exact not_dvd_two_pow_add_two (by omega) hi hj
      ((Nat.Coprime.dvd_of_dvd_mul_right (coprime_tits m)) h)

variable (m : ℕ)

local notation "K" => BinaryGaloisField (2 * m + 1)

section Root

variable {m} (hm : 0 < m)
include hm

theorem rootGL_mul (a b c d : K) :
    SuzukiRootGL m a b * SuzukiRootGL m c d =
      SuzukiRootGL m (a + c) (b + d + a * suzukiCoverTits m c) := by
  rcases huppert_blackburn_XI_3_1 m hm (suzukiCoverTits m) (suzukiCoverTits_square m) with
    ⟨_, _, _, _, _, _, _, _, hmul, _⟩
  exact hmul a b c d

theorem torusGL_conj (x : Kˣ) (a b : K) :
    SuzukiTorusGL m x * SuzukiRootGL m a b * (SuzukiTorusGL m x)⁻¹ =
      SuzukiRootGL m ((x : K) * a) ((x : K) * suzukiCoverTits m (x : K) * b) := by
  rcases huppert_blackburn_XI_3_1 m hm (suzukiCoverTits m) (suzukiCoverTits_square m) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hconj, _⟩
  exact hconj a b x

omit hm in
theorem rootGL_inj {a b c d : K} (h : SuzukiRootGL m a b = SuzukiRootGL m c d) :
    a = c ∧ b = d :=
  suzukiCoverRootElement_injective m a b c d (Subtype.ext (Subtype.ext h))

theorem rootGL_inv (a b : K) :
    (SuzukiRootGL m a b)⁻¹ = SuzukiRootGL m a (b + a * suzukiCoverTits m a) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [rootGL_mul hm, CharTwo.add_self_eq_zero, ← add_assoc, CharTwo.add_self_eq_zero, zero_add,
    CharTwo.add_self_eq_zero]
  exact suzukiRootGL_zero_zero m

omit hm in
theorem mem_rootGL_iff {A : GL (Fin 4) K} :
    A ∈ suzukiCoverRootGL m ↔ ∃ a b : K, A = SuzukiRootGL m a b :=
  suzukiRootGL_mem_closure_iff m (suzukiCoverTits m) (suzukiCoverTits_square m)
    (suzukiCoverTits_apply m) A

end Root

@[expose] def zGL : Subgroup (GL (Fin 4) K) :=
  Subgroup.closure {A | ∃ b : K, A = SuzukiRootGL m 0 b}

variable {m}

theorem mem_zGL_iff (hm : 0 < m) {A : GL (Fin 4) K} :
    A ∈ zGL m ↔ ∃ b : K, A = SuzukiRootGL m 0 b := by
  constructor
  · intro hA
    induction hA using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨0, (suzukiRootGL_zero_zero m).symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨b, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact ⟨b + d, by rw [rootGL_mul hm, add_zero, zero_mul, add_zero]⟩
    | inv x _ hx =>
      obtain ⟨b, rfl⟩ := hx
      exact ⟨b, by rw [rootGL_inv hm, zero_mul, add_zero]⟩
  · rintro ⟨b, rfl⟩
    exact Subgroup.subset_closure ⟨b, rfl⟩

variable (m) in
@[expose] def series : ℕ → Subgroup (GL (Fin 4) K)
  | 0 => ⊥
  | 1 => zGL m
  | _ => suzukiCoverRootGL m

variable (m) in
@[expose] def torusHomGL : Kˣ →* GL (Fin 4) K where
  toFun := SuzukiTorusGL m
  map_one' := suzukiTorusGL_one m
  map_mul' x y := (suzukiTorusGL_mul m x y).symm

theorem torusHomGL_apply (x : Kˣ) : torusHomGL m x = SuzukiTorusGL m x := rfl

variable (m) in
@[expose] def coord : ℕ → K → GL (Fin 4) K
  | 0 => fun b => SuzukiRootGL m 0 b
  | _ => fun a => SuzukiRootGL m a 0

variable (m) in
@[expose] def weight : ℕ → ℕ
  | 0 => 1 + 2 ^ (m + 1)
  | _ => 1

theorem zGL_le_rootGL (hm : 0 < m) : zGL m ≤ suzukiCoverRootGL m := fun A hA => by
  obtain ⟨b, rfl⟩ := (mem_zGL_iff hm).1 hA
  exact (mem_rootGL_iff).2 ⟨0, b, rfl⟩

theorem series_mono (hm : 0 < m) {i : ℕ} (hi : i < 2) : series m i ≤ series m (i + 1) := by
  interval_cases i
  · exact bot_le
  · exact zGL_le_rootGL hm

theorem coord_mem (hm : 0 < m) {i : ℕ} (hi : i < 2) (u : K) : coord m i u ∈ series m (i + 1) := by
  interval_cases i
  · exact (mem_zGL_iff hm).2 ⟨u, rfl⟩
  · exact (mem_rootGL_iff).2 ⟨u, 0, rfl⟩

theorem exists_coord (hm : 0 < m) {i : ℕ} (hi : i < 2) {x : GL (Fin 4) K}
    (hx : x ∈ series m (i + 1)) : ∃ u, ∃ z ∈ series m i, x = coord m i u * z := by
  interval_cases i
  · obtain ⟨b, rfl⟩ := (mem_zGL_iff hm).1 hx
    exact ⟨b, 1, one_mem _, (mul_one _).symm⟩
  · obtain ⟨a, b, rfl⟩ := (mem_rootGL_iff).1 hx
    refine ⟨a, SuzukiRootGL m 0 b, (mem_zGL_iff hm).2 ⟨b, rfl⟩, ?_⟩
    change SuzukiRootGL m a b = SuzukiRootGL m a 0 * SuzukiRootGL m 0 b
    rw [rootGL_mul hm, add_zero, zero_add, map_zero, mul_zero, add_zero]

theorem coord_add (hm : 0 < m) {i : ℕ} (hi : i < 2) (u u' : K) :
    ∃ z ∈ series m i, coord m i u * coord m i u' = coord m i (u + u') * z := by
  interval_cases i
  · refine ⟨1, one_mem _, ?_⟩
    change SuzukiRootGL m 0 u * SuzukiRootGL m 0 u' = SuzukiRootGL m 0 (u + u') * 1
    rw [rootGL_mul hm, mul_one, add_zero, zero_mul, add_zero]
  · refine ⟨SuzukiRootGL m 0 (u * suzukiCoverTits m u'), (mem_zGL_iff hm).2 ⟨_, rfl⟩, ?_⟩
    change SuzukiRootGL m u 0 * SuzukiRootGL m u' 0 =
      SuzukiRootGL m (u + u') 0 * SuzukiRootGL m 0 (u * suzukiCoverTits m u')
    rw [rootGL_mul hm, rootGL_mul hm]
    simp only [add_zero, zero_add, map_zero, mul_zero]

theorem coord_conj (hm : 0 < m) {i : ℕ} (hi : i < 2) (x : Kˣ) (u : K) :
    torusHomGL m x * coord m i u * (torusHomGL m x)⁻¹ =
      coord m i ((x : K) ^ weight m i * u) := by
  interval_cases i
  · change SuzukiTorusGL m x * SuzukiRootGL m 0 u * (SuzukiTorusGL m x)⁻¹ =
      SuzukiRootGL m 0 ((x : K) ^ (1 + 2 ^ (m + 1)) * u)
    rw [torusGL_conj hm, mul_zero, suzukiCoverTits_apply]
    congr 1
    ring
  · change SuzukiTorusGL m x * SuzukiRootGL m u 0 * (SuzukiTorusGL m x)⁻¹ =
      SuzukiRootGL m ((x : K) ^ 1 * u) 0
    rw [torusGL_conj hm, mul_zero, pow_one]

theorem weight_cases (i : ℕ) : weight m i = 1 ∨ weight m i = 1 + 2 ^ (m + 1) := by
  rcases i with _ | i
  · exact Or.inr rfl
  · exact Or.inl rfl

section Cover

variable (hm : 0 < m)
include hm

theorem series_inv {i : ℕ} (hi : i ≤ 2) (x : Kˣ) {A : GL (Fin 4) K} (hA : A ∈ series m i) :
    torusHomGL m x * A * (torusHomGL m x)⁻¹ ∈ series m i := by
  interval_cases i
  · change A ∈ (⊥ : Subgroup (GL (Fin 4) K)) at hA
    change _ ∈ (⊥ : Subgroup (GL (Fin 4) K))
    rw [Subgroup.mem_bot] at hA ⊢
    rw [hA, mul_one, mul_inv_cancel]
  · obtain ⟨b, rfl⟩ := (mem_zGL_iff hm).1 hA
    exact (mem_zGL_iff hm).2 ⟨_, by rw [torusHomGL_apply, torusGL_conj hm, mul_zero]⟩
  · obtain ⟨a, b, rfl⟩ := (mem_rootGL_iff).1 hA
    exact (mem_rootGL_iff).2 ⟨_, _, by rw [torusHomGL_apply, torusGL_conj hm]⟩

omit hm in
theorem add_add_add_self (a c : K) : a + c + a + c = 0 := by
  have : a + c + a + c = (a + a) + (c + c) := by ring
  rw [this, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]

theorem rootGL_mem_zGL {e : K} (he : e = 0) (X : K) : SuzukiRootGL m e X ∈ zGL m :=
  (mem_zGL_iff hm).2 ⟨X, by rw [he]⟩

theorem series_cent {i : ℕ} (hi : i < 2) {x : GL (Fin 4) K} (hx : x ∈ series m (i + 1))
    {g : GL (Fin 4) K} (hg : g ∈ suzukiCoverRootGL m) : x⁻¹ * g⁻¹ * x * g ∈ series m i := by
  obtain ⟨c, d, rfl⟩ := (mem_rootGL_iff).1 hg
  interval_cases i
  · obtain ⟨b, rfl⟩ := (mem_zGL_iff hm).1 hx
    change _ ∈ (⊥ : Subgroup (GL (Fin 4) K))
    have hc : SuzukiRootGL m 0 b * SuzukiRootGL m c d = SuzukiRootGL m c d * SuzukiRootGL m 0 b := by
      rw [rootGL_mul hm, rootGL_mul hm, map_zero, mul_zero, zero_mul, zero_add, add_zero, add_zero,
        add_zero, add_comm b d]
    rw [Subgroup.mem_bot, mul_assoc, hc]
    group
  · obtain ⟨a, b, rfl⟩ := (mem_rootGL_iff).1 hx
    rw [rootGL_inv hm, rootGL_inv hm, rootGL_mul hm, rootGL_mul hm, rootGL_mul hm]
    exact rootGL_mem_zGL hm (add_add_add_self a c) _

theorem series_sq {i : ℕ} (hi : i < 2) {x : GL (Fin 4) K} (hx : x ∈ series m (i + 1)) :
    x ^ 2 ∈ series m i := by
  interval_cases i
  · obtain ⟨b, rfl⟩ := (mem_zGL_iff hm).1 hx
    change _ ∈ (⊥ : Subgroup (GL (Fin 4) K))
    rw [Subgroup.mem_bot, pow_two, rootGL_mul hm, add_zero, zero_mul, add_zero,
      CharTwo.add_self_eq_zero]
    exact suzukiRootGL_zero_zero m
  · obtain ⟨a, b, rfl⟩ := (mem_rootGL_iff).1 hx
    rw [pow_two, rootGL_mul hm]
    exact rootGL_mem_zGL hm (CharTwo.add_self_eq_zero a) _

theorem exists_generator : ∃ g : Kˣ, orderOf g = 2 ^ (2 * m + 1) - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  exact ⟨g, by rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units,
    GaloisField.card 2 (2 * m + 1) (by omega)]⟩

theorem series_fix {i : ℕ} (hi : i < 2) {x : GL (Fin 4) K} (hx : x ∈ series m (i + 1))
    (hfx : ∀ t : Kˣ, (torusHomGL m t * x * (torusHomGL m t)⁻¹)⁻¹ * x ∈ series m i) :
    x ∈ series m i := by
  obtain ⟨g, hg⟩ := exists_generator hm
  have h7 : 7 ≤ 2 ^ (2 * m + 1) - 1 := by
    have : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hg1 : (g : K) ≠ 1 := by
    intro h
    have : g = 1 := Units.ext h
    rw [this, orderOf_one] at hg
    omega
  interval_cases i
  · obtain ⟨b, rfl⟩ := (mem_zGL_iff hm).1 hx
    have h := hfx g
    change _ ∈ (⊥ : Subgroup (GL (Fin 4) K)) at h
    change _ ∈ (⊥ : Subgroup (GL (Fin 4) K))
    rw [Subgroup.mem_bot, inv_mul_eq_one, torusHomGL_apply, torusGL_conj hm, mul_zero] at h
    have hb := (rootGL_inj h).2
    have hgp : (g : K) * suzukiCoverTits m (g : K) ≠ 1 := by
      intro h1
      have h2 : g ^ (1 + 2 ^ (m + 1)) = 1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_one, pow_add, pow_one, ← suzukiCoverTits_apply]
        exact h1)
      have h3 := Nat.le_of_dvd (by positivity) (hg ▸ orderOf_dvd_of_pow_eq_one h2)
      have h4 : 2 ^ (m + 1) * 2 ^ m = 2 ^ (2 * m + 1) := by
        rw [← pow_add]
        congr 1
        omega
      have h5 : 2 ≤ 2 ^ m := by
        have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
        simpa using this
      have h6 : 2 ^ (m + 1) * 2 ≤ 2 ^ (m + 1) * 2 ^ m := Nat.mul_le_mul_left _ h5
      have h8 : 2 ≤ 2 ^ (m + 1) := by
        have : 2 ^ 1 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        simpa using this
      omega
    have hb0 : b = 0 := by
      have h' : ((g : K) * suzukiCoverTits m (g : K) + 1) * b = 0 := by
        rw [add_mul, one_mul, hb, CharTwo.add_self_eq_zero]
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact absurd ((add_eq_zero_iff_eq_neg.1 h'').trans (CharTwo.neg_eq 1)) hgp
      · exact h''
    rw [Subgroup.mem_bot, hb0]
    exact suzukiRootGL_zero_zero m
  · obtain ⟨a, b, rfl⟩ := (mem_rootGL_iff).1 hx
    have h := hfx g
    rw [torusHomGL_apply, torusGL_conj hm, rootGL_inv hm, rootGL_mul hm] at h
    obtain ⟨b', hb'⟩ := (mem_zGL_iff hm).1 h
    have ha := (rootGL_inj hb').1
    have ha0 : a = 0 := by
      have h' : ((g : K) + 1) * a = 0 := by rw [add_mul, one_mul]; exact ha
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact absurd ((add_eq_zero_iff_eq_neg.1 h'').trans (CharTwo.neg_eq 1)) hg1
      · exact h''
    exact (mem_zGL_iff hm).2 ⟨b, by rw [ha0]⟩

end Cover

section Bilinear

variable (hm : 2 ≤ m)
include hm

theorem series_bil {i : ℕ} (hi : i < 2) {j : ℕ} (hj : j < 2) (bf : GL (Fin 4) K → GL (Fin 4) K → ZMod 2)
    (hb₁ : ∀ x ∈ series m (i + 1), ∀ x' ∈ series m (i + 1), ∀ y ∈ series m (j + 1),
      bf (x * x') y = bf x y + bf x' y)
    (hb₂ : ∀ x ∈ series m (i + 1), ∀ y ∈ series m (j + 1), ∀ y' ∈ series m (j + 1),
      bf x (y * y') = bf x y + bf x y')
    (hv₁ : ∀ x ∈ series m i, ∀ y ∈ series m (j + 1), bf x y = 0)
    (hv₂ : ∀ x ∈ series m (i + 1), ∀ y ∈ series m j, bf x y = 0)
    (hT : ∀ (t : Kˣ), ∀ x ∈ series m (i + 1), ∀ y ∈ series m (j + 1),
      bf (torusHomGL m t * x * (torusHomGL m t)⁻¹) (torusHomGL m t * y * (torusHomGL m t)⁻¹) =
        bf x y) :
    ∀ x ∈ series m (i + 1), ∀ y ∈ series m (j + 1), bf x y = 0 := by
  have hm0 : 0 < m := by omega
  set F : K → K → ZMod 2 := fun u v => bf (coord m i u) (coord m j v) with hFdef
  have hF₁ : ∀ u u' v, F (u + u') v = F u v + F u' v := by
    intro u u' v
    obtain ⟨z, hz, hzeq⟩ := coord_add hm0 hi u u'
    have h1 := hb₁ _ (coord_mem hm0 hi u) _ (coord_mem hm0 hi u') _ (coord_mem hm0 hj v)
    rw [hzeq, hb₁ _ (coord_mem hm0 hi (u + u')) _ (series_mono hm0 hi hz) _ (coord_mem hm0 hj v),
      hv₁ _ hz _ (coord_mem hm0 hj v), add_zero] at h1
    exact h1
  have hF₂ : ∀ u v v', F u (v + v') = F u v + F u v' := by
    intro u v v'
    obtain ⟨z, hz, hzeq⟩ := coord_add hm0 hj v v'
    have h1 := hb₂ _ (coord_mem hm0 hi u) _ (coord_mem hm0 hj v) _ (coord_mem hm0 hj v')
    rw [hzeq, hb₂ _ (coord_mem hm0 hi u) _ (coord_mem hm0 hj (v + v')) _ (series_mono hm0 hj hz),
      hv₂ _ (coord_mem hm0 hi u) _ hz, add_zero] at h1
    exact h1
  have hFT : ∀ (t : Kˣ) u v, F ((t : K) ^ weight m i * u) ((t : K) ^ weight m j * v) = F u v := by
    intro t u v
    simp only [hFdef]
    rw [← coord_conj hm0 hi, ← coord_conj hm0 hj]
    exact hT t _ (coord_mem hm0 hi u) _ (coord_mem hm0 hj v)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF0 := zpow_form_eq_zero (p := 2) (f := 2 * m + 1) (by omega)
    (GaloisField.card 2 (2 * m + 1) (by omega)) (e₁ := (weight m i : ℤ)) (e₂ := (weight m j : ℤ))
    (fun i' j' hi' hj' h => weight_not_dvd hm (weight_cases i) (weight_cases j) i' j' hi' hj'
      (by exact_mod_cast h))
    F hF₁ hF₂ (fun t u v => by
      rw [zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
      exact hFT t u v)
  intro x hx y hy
  obtain ⟨u, z, hz, rfl⟩ := exists_coord hm0 hi hx
  obtain ⟨v, z', hz', rfl⟩ := exists_coord hm0 hj hy
  rw [hb₁ _ (coord_mem hm0 hi u) _ (series_mono hm0 hi hz) _ hy, hv₁ _ hz _ hy, add_zero,
    hb₂ _ (coord_mem hm0 hi u) _ (coord_mem hm0 hj v) _ (series_mono hm0 hj hz'),
    hv₂ _ (coord_mem hm0 hi u) _ hz', add_zero]
  exact hF0 u v

end Bilinear

variable (hm : 2 ≤ m)
include hm

theorem suzuki_two_cover_trivial {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (η : E →* SuzukiMatrixGroup m) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker) : η.ker = ⊥ := by
  have hm0 : 0 < m := by omega
  have hT : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units, GaloisField.card 2 (2 * m + 1) (by omega)]
    have hpos : 0 < 2 ^ (2 * m + 1) := by positivity
    exact Nat.Even.sub_odd hpos (even_two.pow_of_ne_zero (by omega)) odd_one
  exact CFSG.LocalAnalysis.ComponentInitial.ker_eq_bot_of_coprime_central_series η hη hC h2
    (suzukiCoverRootGL_le m) (suzukiCoverRoot_structure m hm0).1
    (suzukiCoverRoot_index_odd m hm0).not_two_dvd_nat hT (torusHomGL m)
    (fun t => Subgroup.subset_closure (Or.inr (Or.inl ⟨t, rfl⟩)))
    (fun t x hx => series_inv hm0 (i := 2) le_rfl t hx) 2 (series m) rfl rfl
    (fun i hi => series_mono hm0 hi) (fun i hi t x hx => series_inv hm0 hi t hx)
    (fun i hi x hx g hg => series_cent hm0 hi hx hg) (fun i hi x hx => series_sq hm0 hi hx)
    (fun i hi x hx hfx => series_fix hm0 hi hx hfx)
    (fun i hi j hj bf hb₁ hb₂ hv₁ hv₂ hT' => series_bil hm hi hj bf hb₁ hb₂ hv₁ hv₂ hT')

theorem suzuki_exists_section {E : Type} [Group E] [Finite E] {π : E →* SuzukiMatrixGroup m}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ s : SuzukiMatrixGroup m →* E, ∀ g, π (s g) = g := by
  have hm0 : 0 < m := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect (SuzukiMatrixGroup m) := CFSG.SectionRank.suzukiMatrixGroup_isPerfect m hm0
  exact CoprimeSplit.exists_section_of_parts (p := 2) hπ hcen
    (fun E' _ _ π' hπ' hcen' hp' => FieldFour.exists_section_of_ker_eq_bot
      (fun P _ _ _ η hη hC h2 => suzuki_two_cover_trivial hm η hη hC h2) E' π' hπ' hcen' hp')
    (fun E' _ _ π' hπ' hcen' hc' => by
      obtain ⟨⟨σ, hσ, -⟩, -⟩ := CFSG.SectionRank.suzuki_odd_central_extension_splitting m hm0 π'
        hπ' hcen' (Nat.coprime_two_left.1 hc')
      exact ⟨σ, fun g => DFunLike.congr_fun hσ g⟩)

theorem suzuki_center_eq_bot : Subgroup.center (SuzukiMatrixGroup m) = ⊥ := by
  have hm0 : 0 < m := by omega
  have hsimp := (huppert_blackburn_XI_3_6 m hm0).1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (SuzukiMatrixGroup m)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := CFSG.SectionRank.suzukiMatrixGroup_nonabelian m hm0
    have hb : b ∈ Subgroup.center (SuzukiMatrixGroup m) := by
      rw [h]
      exact Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)

theorem suzuki_hopfMultiplier :
    commutator (SuzukiMatrixGroup m ⧸ Subgroup.center (SuzukiMatrixGroup m)) = ⊤ ∧
      Subsingleton (CFSG.Open.griessHopfMultiplier
        (SuzukiMatrixGroup m ⧸ Subgroup.center (SuzukiMatrixGroup m))) := by
  have hm0 : 0 < m := by omega
  have : Group.IsPerfect (SuzukiMatrixGroup m) := CFSG.SectionRank.suzukiMatrixGroup_isPerfect m hm0
  exact FieldFour.hopfMultiplier_subsingleton (suzuki_center_eq_bot hm)
    fun E _ _ π hπ hcen => suzuki_exists_section hm hπ hcen

end CFSG.LieType.Steinberg.CentralExt.SuzukiClosed
