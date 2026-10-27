module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group

public section

namespace CFSG.Semidihedral.FourPointPresentation

variable {P : Type*} [Group P]

structure Relations (a b c z : P) : Prop where
  central : z ∈ Subgroup.center P
  a_sq : a ^ 2 = 1
  b_sq : b ^ 2 = 1
  c_sq : c ^ 2 = 1
  z_sq : z ^ 2 = 1
  ab_cube : (a * b) ^ 3 = 1
  bc_cube : (b * c) ^ 3 = 1
  ac_sq : (a * c) ^ 2 = z

theorem inv_eq_self_of_sq (x : P) (hx : x ^ 2 = 1) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx)

theorem braid_of_involutions (x y : P) (hx : x ^ 2 = 1)
    (hy : y ^ 2 = 1) (hxy : (x * y) ^ 3 = 1) :
    x * y * x = y * x * y := by
  have h : (x * y * x) * (y * x * y) = 1 := by
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using hxy
  have h' := inv_eq_of_mul_eq_one_left h
  simpa only [mul_inv_rev, inv_eq_self_of_sq x hx,
    inv_eq_self_of_sq y hy, mul_assoc] using h'.symm

theorem Relations.ac_commute {a b c z : P} (h : Relations a b c z) :
    c * a = z * (a * c) := by
  have h' : a * c = z * (c * a) := by
    calc
      a * c = ((a * c) * (a * c)) * (a * c)⁻¹ := by group
      _ = z * (a * c)⁻¹ := by rw [← pow_two, h.ac_sq]
      _ = z * (c * a) := by
        rw [mul_inv_rev, inv_eq_self_of_sq a h.a_sq, inv_eq_self_of_sq c h.c_sq]
  calc
    c * a = z * (z * (c * a)) := by rw [← mul_assoc, ← pow_two, h.z_sq, one_mul]
    _ = z * (a * c) := by rw [← h']

@[expose] def parabolicWord (a b : P) (i : Fin 6) : P :=
  match i.val with
  | 0 => 1
  | 1 => a
  | 2 => b
  | 3 => a * b
  | 4 => b * a
  | _ => a * b * a

@[expose] def cosetWord (a b c : P) (i : Fin 4) : P :=
  match i.val with
  | 0 => 1
  | 1 => c
  | 2 => c * b
  | _ => c * b * a

@[expose] def normalWord (a b c z : P) (i : Fin 2 × Fin 6 × Fin 4) : P :=
  z ^ i.1.val * parabolicWord a b i.2.1 * cosetWord a b c i.2.2

@[expose] def parabolicRightA (i : Fin 6) : Fin 6 :=
  match i.val with
  | 0 => 1
  | 1 => 0
  | 2 => 4
  | 3 => 5
  | 4 => 2
  | _ => 3

@[expose] def parabolicRightB (i : Fin 6) : Fin 6 :=
  match i.val with
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 5
  | _ => 4

theorem parabolicWord_mul_a (a b : P) (ha : a ^ 2 = 1) (i : Fin 6) :
    parabolicWord a b i * a = parabolicWord a b (parabolicRightA i) := by
  have ha' : a * a = 1 := by simpa only [pow_two] using ha
  fin_cases i <;> simp [parabolicWord, parabolicRightA, mul_assoc, ha']

theorem parabolicWord_mul_b (a b : P) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : (a * b) ^ 3 = 1) (i : Fin 6) :
    parabolicWord a b i * b = parabolicWord a b (parabolicRightB i) := by
  have hb' : b * b = 1 := by simpa only [pow_two] using hb
  have hbraid := braid_of_involutions a b ha hb hab
  fin_cases i
  · simp [parabolicWord, parabolicRightB]
  · simp [parabolicWord, parabolicRightB]
  · simp [parabolicWord, parabolicRightB, hb']
  · simp [parabolicWord, parabolicRightB, mul_assoc, hb']
  · simpa only [parabolicWord, parabolicRightB] using hbraid.symm
  · change a * b * a * b = b * a
    rw [hbraid]
    simp only [mul_assoc, hb', mul_one]

theorem parabolicWord_mul (a b : P) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : (a * b) ^ 3 = 1) (i j : Fin 6) :
    ∃ k : Fin 6, parabolicWord a b k = parabolicWord a b i * parabolicWord a b j := by
  have hA := parabolicWord_mul_a a b ha
  have hB := parabolicWord_mul_b a b ha hb hab
  fin_cases j
  · exact ⟨i, by simp [parabolicWord]⟩
  · exact ⟨parabolicRightA i, (hA i).symm⟩
  · exact ⟨parabolicRightB i, (hB i).symm⟩
  · refine ⟨parabolicRightB (parabolicRightA i), ?_⟩
    rw [← hB, ← hA]
    simp only [parabolicWord, mul_assoc]
  · refine ⟨parabolicRightA (parabolicRightB i), ?_⟩
    rw [← hA, ← hB]
    simp only [parabolicWord, mul_assoc]
  · refine ⟨parabolicRightA (parabolicRightB (parabolicRightA i)), ?_⟩
    rw [← hA, ← hB, ← hA]
    simp only [parabolicWord, mul_assoc]

@[expose] def cosetRightA (i : Fin 4) : Fin 2 × Fin 6 × Fin 4 :=
  match i.val with
  | 0 => (0, 1, 0)
  | 1 => (1, 1, 1)
  | 2 => (0, 0, 3)
  | _ => (0, 0, 2)

@[expose] def cosetRightB (i : Fin 4) : Fin 2 × Fin 6 × Fin 4 :=
  match i.val with
  | 0 => (0, 2, 0)
  | 1 => (0, 0, 2)
  | 2 => (0, 0, 1)
  | _ => (1, 1, 3)

@[expose] def cosetRightC (i : Fin 4) : Fin 2 × Fin 6 × Fin 4 :=
  match i.val with
  | 0 => (0, 0, 1)
  | 1 => (0, 0, 0)
  | 2 => (0, 2, 2)
  | _ => (1, 2, 3)

theorem Relations.ca_commute {a b c z : P} (h : Relations a b c z) :
    a * c = z * (c * a) := by
  calc
    a * c = z * (z * (a * c)) := by rw [← mul_assoc, ← pow_two, h.z_sq, one_mul]
    _ = z * (c * a) := by rw [← h.ac_commute]

theorem cosetWord_mul_a {a b c z : P} (h : Relations a b c z) (i : Fin 4) :
    cosetWord a b c i * a = normalWord a b c z (cosetRightA i) := by
  have ha' : a * a = 1 := by simpa only [pow_two] using h.a_sq
  fin_cases i
  · simp [cosetWord, normalWord, parabolicWord, cosetRightA]
  · simpa [cosetWord, normalWord, parabolicWord, cosetRightA, mul_assoc]
      using h.ac_commute
  · simp [cosetWord, normalWord, parabolicWord, cosetRightA]
  · simp [cosetWord, normalWord, parabolicWord, cosetRightA, mul_assoc, ha']

theorem cosetWord_mul_b {a b c z : P} (h : Relations a b c z) (i : Fin 4) :
    cosetWord a b c i * b = normalWord a b c z (cosetRightB i) := by
  have hb' : b * b = 1 := by simpa only [pow_two] using h.b_sq
  have hbraid := braid_of_involutions a b h.a_sq h.b_sq h.ab_cube
  fin_cases i
  · simp [cosetWord, normalWord, parabolicWord, cosetRightB]
  · simp [cosetWord, normalWord, parabolicWord, cosetRightB]
  · simp [cosetWord, normalWord, parabolicWord, cosetRightB, mul_assoc, hb']
  · suffices hi : c * b * a * b = z * a * (c * b * a) by
      simpa [cosetWord, normalWord, parabolicWord, cosetRightB] using hi
    calc
      c * b * a * b = c * (b * a * b) := by group
      _ = c * (a * b * a) := by rw [← hbraid]
      _ = (c * a) * (b * a) := by group
      _ = (z * (a * c)) * (b * a) := by rw [h.ac_commute]
      _ = z * a * (c * b * a) := by group

theorem cosetWord_mul_c {a b c z : P} (h : Relations a b c z) (i : Fin 4) :
    cosetWord a b c i * c = normalWord a b c z (cosetRightC i) := by
  have hc' : c * c = 1 := by simpa only [pow_two] using h.c_sq
  have hbraid := braid_of_involutions b c h.b_sq h.c_sq h.bc_cube
  fin_cases i
  · simp [cosetWord, normalWord, parabolicWord, cosetRightC]
  · simp [cosetWord, normalWord, parabolicWord, cosetRightC, hc']
  · simpa [cosetWord, normalWord, parabolicWord, cosetRightC, mul_assoc]
      using hbraid.symm
  · suffices hi : c * b * a * c = z * b * (c * b * a) by
      simpa [cosetWord, normalWord, parabolicWord, cosetRightC] using hi
    calc
      c * b * a * c = (c * b) * (a * c) := by group
      _ = (c * b) * (z * (c * a)) := by rw [h.ca_commute]
      _ = z * ((c * b) * (c * a)) := by
        rw [← mul_assoc, Subgroup.mem_center_iff.mp h.central (c * b), mul_assoc]
      _ = z * ((c * b * c) * a) := by group
      _ = z * ((b * c * b) * a) := by rw [← hbraid]
      _ = z * b * (c * b * a) := by group

theorem centralPower_mul (z : P) (hz : z ^ 2 = 1) (e f : Fin 2) :
    z ^ e.val * z ^ f.val = z ^ (e + f).val := by
  have hz' : z * z = 1 := by simpa only [pow_two] using hz
  fin_cases e <;> fin_cases f <;> simp [hz']

theorem Relations.centralPower_commute {a b c z : P} (h : Relations a b c z)
    (e : Fin 2) (x : P) : x * z ^ e.val = z ^ e.val * x := by
  fin_cases e
  · simp
  · simpa using Subgroup.mem_center_iff.mp h.central x

theorem normalWord_mul_of_coset {a b c z : P} (h : Relations a b c z)
    (i j : Fin 2 × Fin 6 × Fin 4) (x : P)
    (hx : cosetWord a b c i.2.2 * x = normalWord a b c z j) :
    ∃ k : Fin 2 × Fin 6 × Fin 4,
      normalWord a b c z k = normalWord a b c z i * x := by
  obtain ⟨k, hk⟩ := parabolicWord_mul a b h.a_sq h.b_sq h.ab_cube i.2.1 j.2.1
  refine ⟨(i.1 + j.1, k, j.2.2), ?_⟩
  symm
  calc
    normalWord a b c z i * x =
        z ^ i.1.val * (parabolicWord a b i.2.1 * (cosetWord a b c i.2.2 * x)) := by
      simp only [normalWord, mul_assoc]
    _ = z ^ i.1.val * (parabolicWord a b i.2.1 * normalWord a b c z j) := by rw [hx]
    _ = z ^ i.1.val * ((parabolicWord a b i.2.1 * z ^ j.1.val) *
        (parabolicWord a b j.2.1 * cosetWord a b c j.2.2)) := by
      simp only [normalWord, mul_assoc]
    _ = z ^ i.1.val * ((z ^ j.1.val * parabolicWord a b i.2.1) *
        (parabolicWord a b j.2.1 * cosetWord a b c j.2.2)) := by
      rw [h.centralPower_commute]
    _ = (z ^ i.1.val * z ^ j.1.val) *
        (parabolicWord a b i.2.1 * parabolicWord a b j.2.1) * cosetWord a b c j.2.2 := by
      group
    _ = z ^ (i.1 + j.1).val * parabolicWord a b k * cosetWord a b c j.2.2 := by
      rw [centralPower_mul z h.z_sq, ← hk]
    _ = normalWord a b c z (i.1 + j.1, k, j.2.2) := rfl

theorem normalWord_mul_a {a b c z : P} (h : Relations a b c z)
    (i : Fin 2 × Fin 6 × Fin 4) :
    ∃ j : Fin 2 × Fin 6 × Fin 4,
      normalWord a b c z j = normalWord a b c z i * a :=
  normalWord_mul_of_coset h i (cosetRightA i.2.2) a (cosetWord_mul_a h i.2.2)

theorem normalWord_mul_b {a b c z : P} (h : Relations a b c z)
    (i : Fin 2 × Fin 6 × Fin 4) :
    ∃ j : Fin 2 × Fin 6 × Fin 4,
      normalWord a b c z j = normalWord a b c z i * b :=
  normalWord_mul_of_coset h i (cosetRightB i.2.2) b (cosetWord_mul_b h i.2.2)

theorem normalWord_mul_c {a b c z : P} (h : Relations a b c z)
    (i : Fin 2 × Fin 6 × Fin 4) :
    ∃ j : Fin 2 × Fin 6 × Fin 4,
      normalWord a b c z j = normalWord a b c z i * c :=
  normalWord_mul_of_coset h i (cosetRightC i.2.2) c (cosetWord_mul_c h i.2.2)

theorem normalWord_mul_z {a b c z : P} (h : Relations a b c z)
    (i : Fin 2 × Fin 6 × Fin 4) :
    ∃ j : Fin 2 × Fin 6 × Fin 4,
      normalWord a b c z j = normalWord a b c z i * z := by
  apply normalWord_mul_of_coset h i (1, 0, i.2.2) z
  simpa [normalWord, parabolicWord] using
    Subgroup.mem_center_iff.mp h.central (cosetWord a b c i.2.2)

theorem normalWord_mul_generator {a b c z : P} (h : Relations a b c z)
    (i : Fin 2 × Fin 6 × Fin 4) {x : P} (hx : x ∈ ({a, b, c, z} : Set P)) :
    ∃ j : Fin 2 × Fin 6 × Fin 4,
      normalWord a b c z j = normalWord a b c z i * x := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact normalWord_mul_a h i
  · exact normalWord_mul_b h i
  · exact normalWord_mul_c h i
  · exact normalWord_mul_z h i

theorem Relations.generator_inv {a b c z : P} (h : Relations a b c z)
    {x : P} (hx : x ∈ ({a, b, c, z} : Set P)) : x⁻¹ = x := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact inv_eq_self_of_sq _ h.a_sq
  · exact inv_eq_self_of_sq _ h.b_sq
  · exact inv_eq_self_of_sq _ h.c_sq
  · exact inv_eq_self_of_sq _ h.z_sq

theorem exists_normalWord_of_mem {a b c z : P} (h : Relations a b c z) {x : P}
    (hx : x ∈ Subgroup.closure ({a, b, c, z} : Set P)) :
    ∃ i : Fin 2 × Fin 6 × Fin 4, normalWord a b c z i = x := by
  refine Subgroup.closure_induction_right
    (p := fun y _ => ∃ i : Fin 2 × Fin 6 × Fin 4, normalWord a b c z i = y)
    ?_ ?_ ?_ hx
  · exact ⟨(0, 0, 0), by simp [normalWord, parabolicWord, cosetWord]⟩
  · intro y hy s hs ih
    obtain ⟨i, hi⟩ := ih
    rw [← hi]
    exact normalWord_mul_generator h i hs
  · intro y hy s hs ih
    rw [h.generator_inv hs]
    obtain ⟨i, hi⟩ := ih
    rw [← hi]
    exact normalWord_mul_generator h i hs

theorem normalWord_surjective {a b c z : P} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set P) = ⊤) :
    Function.Surjective (normalWord a b c z) := by
  intro x
  apply exists_normalWord_of_mem h
  rw [hgen]
  exact Subgroup.mem_top x

theorem finite_card_le {a b c z : P} (h : Relations a b c z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set P) = ⊤) :
    Finite P ∧ Nat.card P ≤ 48 := by
  have hs := normalWord_surjective h hgen
  refine ⟨Finite.of_surjective (normalWord a b c z) hs, ?_⟩
  simpa [Nat.card_prod] using Nat.card_le_card_of_surjective (normalWord a b c z) hs

theorem finite_card_le_48 (a b c z : P) (hz : z ∈ Subgroup.center P)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1) (hzz : z ^ 2 = 1)
    (hab : (a * b) ^ 3 = 1) (hbc : (b * c) ^ 3 = 1) (hac : (a * c) ^ 2 = z)
    (hgen : Subgroup.closure ({a, b, c, z} : Set P) = ⊤) :
    Finite P ∧ Nat.card P ≤ 48 :=
  finite_card_le ⟨hz, ha, hb, hc, hzz, hab, hbc, hac⟩ hgen

theorem finite_card_eq_48_of_surjective {Q : Type*} {a b c z : P}
    (h : Relations a b c z) (hgen : Subgroup.closure ({a, b, c, z} : Set P) = ⊤)
    (f : P → Q) (hf : Function.Surjective f) (hQ : Nat.card Q = 48) :
    Finite P ∧ Nat.card P = 48 ∧ Function.Bijective f := by
  obtain ⟨hfinite, hbound⟩ := finite_card_le h hgen
  let : Finite P := hfinite
  have hlower := Nat.card_le_card_of_surjective f hf
  rw [hQ] at hlower
  have hcard : Nat.card P = 48 := Nat.le_antisymm hbound hlower
  exact ⟨hfinite, hcard, (Nat.bijective_iff_surjective_and_card f).mpr
    ⟨hf, hcard.trans hQ.symm⟩⟩

@[expose] noncomputable def equivOfSurjectiveCard48 {Q : Type*} [Group Q] {a b c z : P}
    (h : Relations a b c z) (hgen : Subgroup.closure ({a, b, c, z} : Set P) = ⊤)
    (f : P →* Q) (hf : Function.Surjective f) (hQ : Nat.card Q = 48) : P ≃* Q :=
  MulEquiv.ofBijective f (finite_card_eq_48_of_surjective h hgen f hf hQ).2.2

theorem equivOfSurjectiveCard48_apply {Q : Type*} [Group Q] {a b c z : P}
    (h : Relations a b c z) (hgen : Subgroup.closure ({a, b, c, z} : Set P) = ⊤)
    (f : P →* Q) (hf : Function.Surjective f) (hQ : Nat.card Q = 48) (x : P) :
    equivOfSurjectiveCard48 h hgen f hf hQ x = f x := rfl

end CFSG.Semidihedral.FourPointPresentation
