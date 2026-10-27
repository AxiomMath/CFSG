module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiEightCoords

public section

namespace CFSG.SeitzReduction.RankOne.UEight

open SzEight

abbrev W : Type := V × V

@[expose] def normW (a : W) : V := mul a.1 a.1 + mul a.1 a.2 + mul a.2 a.2

theorem pow_eight_eq (v : V) : mul (mul (mul v v) (mul v v)) (mul (mul v v) (mul v v)) = v := by
  revert v
  decide +kernel

theorem normW_sqrt (v : V) : normW (mul (mul v v) (mul v v), 0) = v := by
  revert v
  decide +kernel

@[expose] def mulB (v w : B) : B :=
  (((v.1 && w.1) ^^ (v.2.1 && w.2.2)) ^^ (v.2.2 && w.2.1),
    ((((v.1 && w.2.1) ^^ (v.2.1 && w.1)) ^^ (v.2.1 && w.2.2)) ^^ (v.2.2 && w.2.1)) ^^
      (v.2.2 && w.2.2),
    (((v.1 && w.2.2) ^^ (v.2.1 && w.2.1)) ^^ (v.2.2 && w.1)) ^^ (v.2.2 && w.2.2))

@[expose] def addB (v w : B) : B := (v.1 ^^ w.1, v.2.1 ^^ w.2.1, v.2.2 ^^ w.2.2)

@[expose] def normB (a : B × B) : B := addB (addB (mulB a.1 a.1) (mulB a.1 a.2)) (mulB a.2 a.2)

@[expose] def add6B (a b : B × B) : B × B := (addB a.1 b.1, addB a.2 b.2)

@[expose] def toW2 (a : W) : B × B := (toW a.1, toW a.2)

theorem toW_add (v w : V) : toW (v + w) = addB (toW v) (toW w) := by
  simp only [toW, addB, Prod.fst_add, Prod.snd_add, toB_add]

theorem toW_mul (v w : V) : toW (mul v w) = mulB (toW v) (toW w) := by
  simp only [toW, mul, mulB, toB_add, toB_mul]

theorem toW_normW (a : W) : toW (normW a) = normB (toW2 a) := by
  simp only [normW, normB, toW2, toW_add, toW_mul]

theorem toW2_add (a b : W) : toW2 (a + b) = add6B (toW2 a) (toW2 b) := by
  simp only [toW2, add6B, Prod.fst_add, Prod.snd_add, toW_add]

theorem toW2_surjective : Function.Surjective toW2 := by
  rintro ⟨x, y⟩
  obtain ⟨x', rfl⟩ := toW_surjective x
  obtain ⟨y', rfl⟩ := toW_surjective y
  exact ⟨(x', y'), rfl⟩

@[expose] def fibB : B → List (B × B)
  | (false, false, false) => [((false, false, false), (false, false, false))]
  | (true, false, false) => [((false, false, false), (true, false, false)),
      ((true, false, false), (false, false, false)), ((true, false, false), (true, false, false)),
      ((false, true, false), (false, false, true)), ((false, true, false), (false, true, true)),
      ((false, false, true), (false, true, false)), ((false, false, true), (false, true, true)),
      ((false, true, true), (false, true, false)), ((false, true, true), (false, false, true))]
  | (false, true, false) => [((false, false, false), (false, true, true)),
      ((false, true, false), (true, false, true)), ((false, true, false), (true, true, true)),
      ((true, false, true), (false, true, false)), ((true, false, true), (true, true, true)),
      ((false, true, true), (false, false, false)), ((false, true, true), (false, true, true)),
      ((true, true, true), (false, true, false)), ((true, true, true), (true, false, true))]
  | (true, true, false) => [((false, false, false), (true, true, true)),
      ((true, false, false), (false, false, true)), ((true, false, false), (true, false, true)),
      ((false, false, true), (true, false, false)), ((false, false, true), (true, false, true)),
      ((true, false, true), (true, false, false)), ((true, false, true), (false, false, true)),
      ((true, true, true), (false, false, false)), ((true, true, true), (true, true, true))]
  | (false, false, true) => [((false, false, false), (false, true, false)),
      ((false, true, false), (false, false, false)), ((false, true, false), (false, true, false)),
      ((true, true, false), (false, false, true)), ((true, true, false), (true, true, true)),
      ((false, false, true), (true, true, false)), ((false, false, true), (true, true, true)),
      ((true, true, true), (true, true, false)), ((true, true, true), (false, false, true))]
  | (true, false, true) => [((false, false, false), (true, true, false)),
      ((true, false, false), (false, true, true)), ((true, false, false), (true, true, true)),
      ((true, true, false), (false, false, false)), ((true, true, false), (true, true, false)),
      ((false, true, true), (true, false, false)), ((false, true, true), (true, true, true)),
      ((true, true, true), (true, false, false)), ((true, true, true), (false, true, true))]
  | (false, true, true) => [((false, false, false), (false, false, true)),
      ((true, true, false), (true, false, true)), ((true, true, false), (false, true, true)),
      ((false, false, true), (false, false, false)), ((false, false, true), (false, false, true)),
      ((true, false, true), (true, true, false)), ((true, false, true), (false, true, true)),
      ((false, true, true), (true, true, false)), ((false, true, true), (true, false, true))]
  | (true, true, true) => [((false, false, false), (true, false, true)),
      ((true, false, false), (false, true, false)), ((true, false, false), (true, true, false)),
      ((false, true, false), (true, false, false)), ((false, true, false), (true, true, false)),
      ((true, true, false), (true, false, false)), ((true, true, false), (false, true, false)),
      ((true, false, true), (false, false, false)), ((true, false, true), (true, false, true))]

@[expose] def diagB : B → List B
  | (false, false, false) => [(false, false, false)]
  | (true, false, false) => [(false, false, false), (false, false, true), (false, true, false),
      (false, true, true), (true, false, false)]
  | (false, true, false) => [(false, false, false), (false, false, true), (false, true, false),
      (true, true, false), (true, true, true)]
  | (true, true, false) => [(false, false, false), (false, true, true), (true, false, false),
      (true, true, false), (true, true, true)]
  | (false, false, true) => [(false, false, false), (false, false, true), (false, true, true),
      (true, false, true), (true, true, false)]
  | (true, false, true) => [(false, false, false), (false, true, false), (true, false, false),
      (true, false, true), (true, true, false)]
  | (false, true, true) => [(false, false, false), (false, true, false), (false, true, true),
      (true, false, true), (true, true, true)]
  | (true, true, true) => [(false, false, false), (false, false, true), (true, false, false),
      (true, false, true), (true, true, true)]

theorem normB_of_mem_fibB : ∀ c : B, ∀ a ∈ fibB c, normB a = c := by
  decide +kernel

theorem mem_fibB_normB : ∀ a : B × B, a ∈ fibB (normB a) := by
  decide +kernel

theorem normB_add_mem_diagB : ∀ c : B, ∀ a ∈ fibB c, ∀ b ∈ fibB c, normB (add6B a b) ∈ diagB c := by
  decide +kernel

theorem exists_of_mem_diagB :
    ∀ c x : B, x ∈ diagB c → ∃ a ∈ fibB c, ∃ b ∈ fibB c, normB (add6B a b) = x := by
  decide +kernel

@[expose] def diag (c x : V) : Prop := toW x ∈ diagB (toW c)

instance (c x : V) : Decidable (diag c x) := by
  unfold diag
  infer_instance

theorem diag_iff (c x : V) :
    diag c x ↔ ∃ a b : W, normW a = c ∧ normW b = c ∧ normW (a + b) = x := by
  constructor
  · intro h
    obtain ⟨a', ha', b', hb', hab⟩ := exists_of_mem_diagB (toW c) (toW x) h
    obtain ⟨a, rfl⟩ := toW2_surjective a'
    obtain ⟨b, rfl⟩ := toW2_surjective b'
    refine ⟨a, b, toW_injective ?_, toW_injective ?_, toW_injective ?_⟩
    · rw [toW_normW]
      exact normB_of_mem_fibB _ _ ha'
    · rw [toW_normW]
      exact normB_of_mem_fibB _ _ hb'
    · rw [toW_normW, toW2_add]
      exact hab
  · rintro ⟨a, b, rfl, hb, rfl⟩
    have ha' := mem_fibB_normB (toW2 a)
    have hb' := mem_fibB_normB (toW2 b)
    rw [← toW_normW] at ha' hb'
    rw [hb] at hb'
    have h := normB_add_mem_diagB _ _ ha' _ hb'
    rwa [← toW2_add, ← toW_normW] at h

@[expose] def AdmissibleN (t : V × V × V) : Prop :=
  (∀ v, lin t v = 0 → v = 0) ∧ ∀ c x : V, diag c x ↔ diag (lin t c) (lin t x)

@[expose] def AdmissibleNB (t : B × B × B) : Prop :=
  (∀ v, linB t v = (false, false, false) → v = (false, false, false)) ∧
    ∀ c x : B, (x ∈ diagB c ↔ linB t x ∈ diagB (linB t c))

instance : DecidablePred AdmissibleNB := fun t => by
  unfold AdmissibleNB
  infer_instance

theorem admissibleN_iff (t : V × V × V) : AdmissibleN t ↔ AdmissibleNB (toW3 t) := by
  have h₀ : toW (0 : V) = (false, false, false) := by decide +kernel
  refine and_congr ?_ ?_
  · rw [toW_surjective.forall]
    refine forall_congr' fun v => ?_
    rw [← toW_injective.eq_iff, ← toW_injective.eq_iff (b := 0), toW_lin, h₀]
  · rw [toW_surjective.forall]
    refine forall_congr' fun c => ?_
    rw [toW_surjective.forall]
    refine forall_congr' fun x => ?_
    simp only [diag, toW_lin]

instance : DecidablePred AdmissibleN := fun t => decidable_of_iff _ (admissibleN_iff t).symm

theorem card_admissibleN : Fintype.card {t : V × V × V // AdmissibleN t} = 21 := by
  decide +kernel

@[expose] def frob (v : V) : V := mul v v

@[expose] def frob64 (a : W) : W := (frob a.1 + frob a.2, frob a.2)

@[expose] def mulα (v : V) : V := mul (0, 1, 0) v

@[expose] def scal (a : W) : W := (mul (0, 1, 1) a.1, mul (0, 1, 1) a.2)

theorem frob_add (v w : V) : frob (v + w) = frob v + frob w := by
  revert v w
  decide +kernel

theorem mulα_add (v w : V) : mulα (v + w) = mulα v + mulα w := by
  revert v w
  decide +kernel

theorem mul_add_right (c v w : V) : mul c (v + w) = mul c v + mul c w := by
  revert c v w
  decide +kernel

theorem frob64_add (a b : W) : frob64 (a + b) = frob64 a + frob64 b := by
  obtain ⟨x, y⟩ := a
  obtain ⟨x', y'⟩ := b
  simp only [frob64, Prod.mk_add_mk, frob_add, Prod.mk.injEq, and_true]
  abel

theorem scal_add (a b : W) : scal (a + b) = scal a + scal b := by
  obtain ⟨x, y⟩ := a
  obtain ⟨x', y'⟩ := b
  simp only [scal, Prod.mk_add_mk, mul_add_right]

theorem normW_frob64 (a : W) : normW (frob64 a) = frob (normW a) := by
  revert a
  decide +kernel

theorem normW_scal (a : W) : normW (scal a) = mulα (normW a) := by
  revert a
  decide +kernel

theorem frob_eq_zero (v : V) (h : frob v = 0) : v = 0 := by
  revert v
  decide +kernel

theorem mulα_eq_zero (v : V) (h : mulα v = 0) : v = 0 := by
  revert v
  decide +kernel

theorem frob64_eq_zero (a : W) (h : frob64 a = 0) : a = 0 := by
  revert a
  decide +kernel

theorem scal_eq_zero (a : W) (h : scal a = 0) : a = 0 := by
  revert a
  decide +kernel

theorem frob_frob_frob (v : V) : frob (frob (frob v)) = v := by
  revert v
  decide +kernel

theorem mulα_seven (v : V) : mulα (mulα (mulα (mulα (mulα (mulα (mulα v)))))) = v := by
  revert v
  decide +kernel

theorem frob_ne : frob (0, 1, 0) ≠ (0, 1, 0) := by
  decide +kernel

theorem mulα_ne : mulα (1, 0, 0) ≠ (1, 0, 0) := by
  decide +kernel

section Field

variable {F : Type*} [Field F]

theorem charP_two_of_card_eq_sixtyFour [Finite F] (hF : Nat.card F = 64) : CharP F 2 := by
  have : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (p := 2) (f := 6)
    (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)

theorem exists_pow_three_eq_add_one_of_pow_seven [CharP F 2] {g : F} (h7 : g ^ 7 = 1)
    (hg1 : g ≠ 1) : ∃ α : F, α ^ 3 = α + 1 := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    norm_num at h7
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hprod : (g + 1) * ((g ^ 3 + g + 1) * (g ^ 3 + g ^ 2 + 1)) = 0 := by
    linear_combination h7 + (1 + g + g ^ 2 + 2 * g ^ 3 + 2 * g ^ 4 + g ^ 5 + g ^ 6) * h2
  rcases mul_eq_zero.1 hprod with h | h
  · exact absurd (by linear_combination h - h2) hg1
  rcases mul_eq_zero.1 h with h | h
  · exact ⟨g, by linear_combination h - (g + 1) * h2⟩
  · have hgα : g * g⁻¹ = 1 := mul_inv_cancel₀ hg0
    refine ⟨g⁻¹, ?_⟩
    linear_combination (-g⁻¹ ^ 3) * h + g⁻¹ ^ 3 * h2 +
      (g⁻¹ * (g * g⁻¹ + 1) + (g * g⁻¹) ^ 2 + g * g⁻¹ + 1) * hgα

theorem exists_roots [Finite F] (hF : Nat.card F = 64) :
    ∃ α ω : F, α ^ 3 = α + 1 ∧ ω ^ 2 = ω + 1 := by
  have : CharP F 2 := charP_two_of_card_eq_sixtyFour hF
  have hu : Nat.card Fˣ = 63 := by rw [Nat.card_units, hF]
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu7⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 7 (by rw [hu]; norm_num)
  obtain ⟨w, hw3⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rw [hu]; norm_num)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hpow : ∀ (x : Fˣ) (k : ℕ), orderOf x = k → (x : F) ^ k = 1 := fun x k hk => by
    rw [← Units.val_pow_eq_pow_val, ← hk, pow_orderOf_eq_one, Units.val_one]
  have hne : ∀ (x : Fˣ) (k : ℕ), orderOf x = k → k ≠ 1 → (x : F) ≠ 1 := fun x k hk hk1 h => by
    have h1 : x = 1 := Units.ext h
    rw [h1, orderOf_one] at hk
    exact hk1 hk.symm
  obtain ⟨α, hα⟩ :=
    exists_pow_three_eq_add_one_of_pow_seven (hpow u 7 hu7) (hne u 7 hu7 (by norm_num))
  refine ⟨α, w, hα, ?_⟩
  have h : ((w : F) - 1) * ((w : F) ^ 2 + w + 1) = 0 := by linear_combination hpow w 3 hw3
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (sub_eq_zero.1 h) (hne w 3 hw3 (by norm_num))
  · linear_combination h - ((w : F) + 1) * h2

variable [CharP F 2]

@[expose] def coord64 (α ω : F) : W →+ F where
  toFun a := coord α a.1 + coord α a.2 * ω
  map_zero' := by simp
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring

theorem coord64_apply (α ω : F) (a : W) : coord64 α ω a = coord α a.1 + coord α a.2 * ω :=
  rfl

theorem coord_pow_eight {α : F} (hα : α ^ 3 = α + 1) (v : V) : coord α v ^ 8 = coord α v := by
  have h1 : ∀ w : V, coord α (mul w w) = coord α w ^ 2 := fun w => by rw [coord_mul hα, sq]
  calc coord α v ^ 8 = ((coord α v ^ 2) ^ 2) ^ 2 := by ring
    _ = coord α (mul (mul (mul v v) (mul v v)) (mul (mul v v) (mul v v))) := by
      rw [h1, h1, h1]
    _ = coord α v := by rw [pow_eight_eq]

theorem pow_three_eq_one_of_sq {ω : F} (hω : ω ^ 2 = ω + 1) : ω ^ 3 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (ω + 1) * hω + ω * h2

theorem pow_eight_eq_of_sq {ω : F} (hω : ω ^ 2 = ω + 1) : ω ^ 8 = ω + 1 := by
  rw [show ω ^ 8 = (ω ^ 3) ^ 2 * ω ^ 2 by ring, pow_three_eq_one_of_sq hω, hω]
  ring

theorem coord64_injective {α ω : F} (hα : α ^ 3 = α + 1) (hω : ω ^ 2 = ω + 1) :
    Function.Injective (coord64 α ω) := by
  refine (injective_iff_map_eq_zero (coord64 α ω)).2 fun a ha => ?_
  obtain ⟨x, y⟩ := a
  rw [coord64_apply] at ha
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, zero_mul, add_zero] at ha
    rw [(injective_iff_map_eq_zero (coord α)).1 (coord_injective hα) x ha]
    rfl
  · exfalso
    obtain ⟨w, hw⟩ := exists_mul_eq_one y hy
    have hyw : coord α y * coord α w = 1 := by rw [← coord_mul hα, hw, coord_one]
    have hωx : ω = coord α (mul x w) := by
      rw [coord_mul hα]
      linear_combination (-ω) * hyw + coord α w * ha - coord α x * coord α w * h2
    have h8 := coord_pow_eight hα (mul x w)
    rw [← hωx, pow_eight_eq_of_sq hω] at h8
    exact one_ne_zero (by linear_combination h8 : (1 : F) = 0)

theorem coord64_bijective [Finite F] (hF : Nat.card F = 64) {α ω : F} (hα : α ^ 3 = α + 1)
    (hω : ω ^ 2 = ω + 1) : Function.Bijective (coord64 α ω) :=
  (Nat.bijective_iff_injective_and_card _).2 ⟨coord64_injective hα hω, by simp [hF]⟩

theorem coord64_pow_nine {α ω : F} (hα : α ^ 3 = α + 1) (hω : ω ^ 2 = ω + 1) (a : W) :
    coord64 α ω a ^ 9 = coord α (normW a) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨x, y⟩ := a
  have hx := coord_pow_eight hα x
  have hy := coord_pow_eight hα y
  have h8 : (coord α x + coord α y * ω) ^ 8 = coord α x + coord α y * (ω + 1) := by
    have e : ∀ z : F, z ^ 8 = ((z ^ 2) ^ 2) ^ 2 := fun z => by ring
    rw [e, CharTwo.add_sq, CharTwo.add_sq, CharTwo.add_sq, ← e, ← e, mul_pow, hx, hy,
      pow_eight_eq_of_sq hω]
  simp only [coord64_apply, normW, map_add, coord_mul hα]
  linear_combination (coord α x + coord α y * ω) * h8 + coord α y ^ 2 * hω +
    (coord α x * coord α y * ω + ω * coord α y ^ 2) * h2

end Field

end CFSG.SeitzReduction.RankOne.UEight
