module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankTwoShapes

open Matrix
open scoped commutatorElement

noncomputable section

variable {K : Type} [Field K]

omit [Field K] in
theorem finite_of_natCard_eq_sixteen (hK : Nat.card K = 16) : Finite K :=
  Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)

theorem charP_two_of_natCard_eq_sixteen (hK : Nat.card K = 16) : CharP K 2 := by
  have := finite_of_natCard_eq_sixteen hK
  let : Fintype K := Fintype.ofFinite K
  have h16 : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, hK] at h16
  have h2 : (2 : K) ^ 4 = 0 := by
    rw [show (2 : K) ^ 4 = ((16 : ℕ) : K) by norm_num]
    exact h16
  exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
    ((pow_eq_zero_iff (by norm_num)).mp h2)

theorem pow_sixteen_eq_self (hK : Nat.card K = 16) (x : K) : x ^ 16 = x := by
  have := finite_of_natCard_eq_sixteen hK
  let : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card x
  rwa [← Nat.card_eq_fintype_card, hK] at h

theorem natCard_pow_four_eq_self (hK : Nat.card K = 16) :
    Nat.card {t : K // t ^ 4 = t} = 4 := by
  have := finite_of_natCard_eq_sixteen hK
  obtain ⟨σ, hσ, -, hfix⟩ :=
    exists_quadraticFrobenius K 2 (by norm_num) (by rw [hK]; norm_num)
  calc Nat.card {t : K // t ^ 4 = t} = Nat.card {x : K // σ x = x} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [hσ]; norm_num)
    _ = 4 := by rw [hfix]; norm_num

theorem exists_add_pow_four_eq (hK : Nat.card K = 16) {s : K} (hs : s ^ 4 = s) :
    ∃ b : K, b + b ^ 4 = s := by
  have := finite_of_natCard_eq_sixteen hK
  have := charP_two_of_natCard_eq_sixteen hK
  let T : K →+ K :=
    { toFun := fun b => b + b ^ 4
      map_zero' := by simp
      map_add' := fun x y => by
        change x + y + (x + y) ^ 4 = x + x ^ 4 + (y + y ^ 4)
        grind }
  have hker : Nat.card T.ker = 4 := by
    rw [← natCard_pow_four_eq_self hK]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [AddMonoidHom.mem_ker]
      change x + x ^ 4 = 0 ↔ x ^ 4 = x
      grind)
  have hrange : Nat.card T.range = 4 := by
    have h := T.ker.card_mul_index
    rw [AddSubgroup.index_ker, hker, hK] at h
    omega
  have hsub : (T.range : Set K) ⊆ {t | t ^ 4 = t} := by
    rintro _ ⟨b, rfl⟩
    change (b + b ^ 4) ^ 4 = b + b ^ 4
    have := pow_sixteen_eq_self hK b
    grind
  have heq : (T.range : Set K) = {t | t ^ 4 = t} := by
    apply Set.eq_of_subset_of_ncard_le hsub _ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    change Nat.card {t : K // t ^ 4 = t} ≤ Nat.card T.range
    rw [natCard_pow_four_eq_self hK, hrange]
  have hmem : s ∈ (T.range : Set K) := by
    rw [heq]
    exact hs
  obtain ⟨b, hb⟩ := hmem
  exact ⟨b, hb⟩

theorem pow_five_pow_four (hK : Nat.card K = 16) (a : K) : (a ^ 5) ^ 4 = a ^ 5 := by
  have := pow_sixteen_eq_self hK a
  grind

theorem exists_sq_add_self_add_one_eq_zero (hK : Nat.card K = 16) :
    ∃ l : K, l ^ 2 + l + 1 = 0 := by
  have := finite_of_natCard_eq_sixteen hK
  have := charP_two_of_natCard_eq_sixteen hK
  by_contra hne
  push Not at hne
  have hsub : {t : K | t ^ 4 = t} ⊆ {0, 1} := by
    intro t ht
    change t ^ 4 = t at ht
    by_contra h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
    have h3 : t * (t - 1) * (t ^ 2 + t + 1) = 0 := by grind
    rcases mul_eq_zero.mp h3 with h3 | h3
    · rcases mul_eq_zero.mp h3 with h3 | h3
      · exact h.1 h3
      · exact h.2 (sub_eq_zero.mp h3)
    · exact hne t h3
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair zero_ne_one, ← Nat.card_coe_set_eq] at hle
  change Nat.card {t : K // t ^ 4 = t} ≤ 2 at hle
  rw [natCard_pow_four_eq_self hK] at hle
  omega

theorem eq_zero_or_eq_one_or_of_pow_four_eq_self [CharP K 2] {l t : K}
    (hl : l ^ 2 + l + 1 = 0) (ht : t ^ 4 = t) :
    t = 0 ∨ t = 1 ∨ t = l ∨ t = l ^ 2 := by
  have h : t * (t - 1) * (t - l) * (t - l ^ 2) = 0 := by grind
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h)))
  · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.mp h)))

theorem exists_trace_one_norm_sq (hK : Nat.card K = 16) {l : K} (hl : l ^ 2 + l + 1 = 0) :
    ∃ c : K, c + c ^ 4 = 1 ∧ c ^ 5 = l ^ 2 := by
  have := charP_two_of_natCard_eq_sixteen hK
  obtain ⟨c₀, hc₀⟩ := exists_add_pow_four_eq hK (s := (1 : K)) (by norm_num)
  rcases eq_zero_or_eq_one_or_of_pow_four_eq_self hl (pow_five_pow_four hK c₀) with
    h | h | h | h
  · exfalso
    have h0 : c₀ = 0 := (pow_eq_zero_iff (by norm_num)).mp h
    rw [h0] at hc₀
    simp at hc₀
  · exfalso
    grind
  · exact ⟨c₀ + l, by grind, by grind⟩
  · exact ⟨c₀, hc₀, h⟩

theorem exists_eq_add_mul_of_pow_four_ne (hK : Nat.card K = 16) {c : K} (hc : c ^ 4 ≠ c)
    (a : K) : ∃ s t : K, s ^ 4 = s ∧ t ^ 4 = t ∧ a = s + t * c := by
  have := finite_of_natCard_eq_sixteen hK
  have := charP_two_of_natCard_eq_sixteen hK
  let f : {s : K // s ^ 4 = s} × {t : K // t ^ 4 = t} → K := fun p => p.1 + p.2 * c
  have hinj : Function.Injective f := by
    rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ ⟨⟨s', hs'⟩, ⟨t', ht'⟩⟩ h
    change s + t * c = s' + t' * c at h
    have h4 := congrArg (· ^ 4) h
    have htt : t = t' := by
      by_contra htt
      have h1 : (c ^ 4 - c) * (t - t') = 0 := by grind
      rcases mul_eq_zero.mp h1 with h1 | h1
      · exact hc (sub_eq_zero.mp h1)
      · exact htt (sub_eq_zero.mp h1)
    subst htt
    have hss : s = s' := by grind
    subst hss
    rfl
  have hbij := hinj.bijective_of_nat_card_le (by
    rw [Nat.card_prod, natCard_pow_four_eq_self hK, hK])
  obtain ⟨⟨⟨s, hs⟩, ⟨t, ht⟩⟩, hst⟩ := hbij.2 a
  exact ⟨s, t, hs, ht, hst.symm⟩

@[expose] def unitaryFourMatrix (a b : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, a ^ 4, b; 0, 1, a; 0, 0, 1]

@[simp] theorem unitaryFourMatrix_apply_one_two (a b : K) : unitaryFourMatrix a b 1 2 = a := by
  simp [unitaryFourMatrix]

@[simp] theorem unitaryFourMatrix_apply_zero_two (a b : K) : unitaryFourMatrix a b 0 2 = b := by
  simp [unitaryFourMatrix]

theorem unitaryFourMatrix_det (a b : K) : (unitaryFourMatrix a b).det = 1 := by
  simp [unitaryFourMatrix, Matrix.det_fin_three]

theorem unitaryFourMatrix_zero_zero : unitaryFourMatrix (0 : K) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitaryFourMatrix]

theorem unitaryFourMatrix_mul [CharP K 2] (a b c d : K) :
    unitaryFourMatrix a b * unitaryFourMatrix c d =
      unitaryFourMatrix (a + c) (b + d + a ^ 4 * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryFourMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem unitaryFourMatrix_injective {a b c d : K}
    (h : unitaryFourMatrix a b = unitaryFourMatrix c d) : a = c ∧ b = d := by
  constructor
  · simpa using congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 1 2) h
  · simpa using congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 2) h

@[expose] def unitaryFourGL (a b : K) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (unitaryFourMatrix a b)
    (by rw [unitaryFourMatrix_det]; exact one_ne_zero)

@[simp] theorem unitaryFourGL_val (a b : K) :
    ((unitaryFourGL a b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = unitaryFourMatrix a b :=
  rfl

@[expose] def unitaryFourW (K : Type) [Field K] (hK : Nat.card K = 16) :
    Subgroup (GL (Fin 3) K) where
  carrier := {A | ∃ a b : K, b + b ^ 4 = a ^ 5 ∧
    (A : Matrix (Fin 3) (Fin 3) K) = unitaryFourMatrix a b}
  mul_mem' := by
    have := charP_two_of_natCard_eq_sixteen hK
    rintro A B ⟨a, b, hab, hA⟩ ⟨c, d, hcd, hB⟩
    refine ⟨a + c, b + d + a ^ 4 * c, ?_, ?_⟩
    · have := pow_sixteen_eq_self hK a
      have := pow_sixteen_eq_self hK c
      grind
    · rw [Matrix.GeneralLinearGroup.coe_mul, hA, hB, unitaryFourMatrix_mul]
  one_mem' := ⟨0, 0, by simp, by rw [unitaryFourMatrix_zero_zero]; rfl⟩
  inv_mem' := by
    have := charP_two_of_natCard_eq_sixteen hK
    rintro A ⟨a, b, hab, hA⟩
    refine ⟨a, b ^ 4, ?_, ?_⟩
    · have := pow_sixteen_eq_self hK b
      grind
    · rw [Matrix.coe_units_inv, hA]
      apply Matrix.inv_eq_right_inv
      rw [unitaryFourMatrix_mul, ← unitaryFourMatrix_zero_zero]
      congr 1 <;> grind

theorem mem_unitaryFourW_iff {hK : Nat.card K = 16} {A : GL (Fin 3) K} :
    A ∈ unitaryFourW K hK ↔ ∃ a b : K, b + b ^ 4 = a ^ 5 ∧
      (A : Matrix (Fin 3) (Fin 3) K) = unitaryFourMatrix a b :=
  Iff.rfl

namespace UnitaryFourW

variable {hK : Nat.card K = 16}

@[expose] def fst (w : unitaryFourW K hK) : K :=
  ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2

@[expose] def snd (w : unitaryFourW K hK) : K :=
  ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2

theorem coe_eq (w : unitaryFourW K hK) :
    ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = unitaryFourMatrix (fst w) (snd w) := by
  obtain ⟨a, b, -, h⟩ := w.2
  rw [fst, snd, h, unitaryFourMatrix_apply_one_two, unitaryFourMatrix_apply_zero_two]

theorem snd_add_snd_pow_four (w : unitaryFourW K hK) : snd w + snd w ^ 4 = fst w ^ 5 := by
  obtain ⟨a, b, hab, h⟩ := w.2
  rw [fst, snd, h, unitaryFourMatrix_apply_one_two, unitaryFourMatrix_apply_zero_two]
  exact hab

theorem fst_eq_of_coe_eq {w : unitaryFourW K hK} {a b : K}
    (h : ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = unitaryFourMatrix a b) :
    fst w = a := by
  rw [fst, h, unitaryFourMatrix_apply_one_two]

theorem snd_eq_of_coe_eq {w : unitaryFourW K hK} {a b : K}
    (h : ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = unitaryFourMatrix a b) :
    snd w = b := by
  rw [snd, h, unitaryFourMatrix_apply_zero_two]

@[ext] theorem ext {v w : unitaryFourW K hK} (h₁ : fst v = fst w) (h₂ : snd v = snd w) :
    v = w := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_eq v, coe_eq w, h₁, h₂]

@[expose] def mk (hK : Nat.card K = 16) (a b : K) (h : b + b ^ 4 = a ^ 5) : unitaryFourW K hK :=
  ⟨unitaryFourGL a b, a, b, h, rfl⟩

@[simp] theorem coe_mk (a b : K) (h : b + b ^ 4 = a ^ 5) :
    (((mk hK a b h : unitaryFourW K hK) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      unitaryFourMatrix a b :=
  rfl

@[simp] theorem fst_mk (a b : K) (h : b + b ^ 4 = a ^ 5) : fst (mk hK a b h) = a :=
  fst_eq_of_coe_eq (coe_mk a b h)

@[simp] theorem snd_mk (a b : K) (h : b + b ^ 4 = a ^ 5) : snd (mk hK a b h) = b :=
  snd_eq_of_coe_eq (coe_mk a b h)

@[simp] theorem fst_one : fst (1 : unitaryFourW K hK) = 0 := by
  simp [fst]

@[simp] theorem snd_one : snd (1 : unitaryFourW K hK) = 0 := by
  simp [snd]

theorem coe_mul_eq (v w : unitaryFourW K hK) :
    (((v * w : unitaryFourW K hK) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      unitaryFourMatrix (fst v + fst w) (snd v + snd w + fst v ^ 4 * fst w) := by
  have := charP_two_of_natCard_eq_sixteen hK
  rw [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_eq v, coe_eq w,
    unitaryFourMatrix_mul]

@[simp] theorem fst_mul (v w : unitaryFourW K hK) : fst (v * w) = fst v + fst w :=
  fst_eq_of_coe_eq (coe_mul_eq v w)

@[simp] theorem snd_mul (v w : unitaryFourW K hK) :
    snd (v * w) = snd v + snd w + fst v ^ 4 * fst w :=
  snd_eq_of_coe_eq (coe_mul_eq v w)

@[simp] theorem fst_inv (w : unitaryFourW K hK) : fst w⁻¹ = fst w := by
  have := charP_two_of_natCard_eq_sixteen hK
  have h := congrArg fst (inv_mul_cancel w)
  rw [fst_mul, fst_one] at h
  grind

@[simp] theorem snd_inv (w : unitaryFourW K hK) : snd w⁻¹ = snd w + fst w ^ 5 := by
  have := charP_two_of_natCard_eq_sixteen hK
  have h := congrArg snd (inv_mul_cancel w)
  rw [snd_mul, snd_one, fst_inv] at h
  grind

theorem fst_sq (w : unitaryFourW K hK) : fst (w ^ 2) = 0 := by
  have := charP_two_of_natCard_eq_sixteen hK
  rw [pow_two, fst_mul]
  grind

theorem snd_sq (w : unitaryFourW K hK) : snd (w ^ 2) = fst w ^ 5 := by
  have := charP_two_of_natCard_eq_sixteen hK
  rw [pow_two, snd_mul]
  grind

theorem coe_sq (w : unitaryFourW K hK) :
    (((w ^ 2 : unitaryFourW K hK) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      unitaryFourMatrix 0 (fst w ^ 5) := by
  rw [coe_eq, fst_sq, snd_sq]

theorem pow_four_eq_one (w : unitaryFourW K hK) : w ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]
  ext
  · rw [fst_sq, fst_one]
  · rw [snd_sq, fst_sq, snd_one, zero_pow (by norm_num)]

theorem fst_commutatorElement (v w : unitaryFourW K hK) : fst ⁅v, w⁆ = 0 := by
  have := charP_two_of_natCard_eq_sixteen hK
  simp only [commutatorElement_def, fst_mul, fst_inv]
  grind

theorem snd_commutatorElement (v w : unitaryFourW K hK) :
    snd ⁅v, w⁆ = fst v ^ 4 * fst w + fst v * fst w ^ 4 := by
  have := charP_two_of_natCard_eq_sixteen hK
  have hv := snd_add_snd_pow_four v
  have hw := snd_add_snd_pow_four w
  simp only [commutatorElement_def, fst_mul, fst_inv, snd_mul, snd_inv]
  grind

theorem fst_inv_mul_inv_mul_mul (v w : unitaryFourW K hK) : fst (v⁻¹ * w⁻¹ * v * w) = 0 := by
  have := charP_two_of_natCard_eq_sixteen hK
  simp only [fst_mul, fst_inv]
  grind

theorem snd_inv_mul_inv_mul_mul (v w : unitaryFourW K hK) :
    snd (v⁻¹ * w⁻¹ * v * w) = fst v ^ 4 * fst w + fst v * fst w ^ 4 := by
  have := charP_two_of_natCard_eq_sixteen hK
  have hv := snd_add_snd_pow_four v
  have hw := snd_add_snd_pow_four w
  simp only [fst_mul, fst_inv, snd_mul, snd_inv]
  grind

@[expose] def firstCoord (hK : Nat.card K = 16) : unitaryFourW K hK →* Multiplicative K where
  toFun w := Multiplicative.ofAdd (fst w)
  map_one' := by simp
  map_mul' v w := by simp

@[simp] theorem firstCoord_apply (w : unitaryFourW K hK) :
    firstCoord hK w = Multiplicative.ofAdd (fst w) :=
  rfl

theorem exists_fst_eq (a : K) : ∃ w : unitaryFourW K hK, fst w = a := by
  obtain ⟨b, hb⟩ := exists_add_pow_four_eq hK (pow_five_pow_four hK a)
  exact ⟨mk hK a b hb, fst_mk a b hb⟩

theorem firstCoord_surjective : Function.Surjective (firstCoord hK) := by
  intro x
  obtain ⟨w, hw⟩ := exists_fst_eq (hK := hK) x.toAdd
  exact ⟨w, by rw [firstCoord_apply, hw]; rfl⟩

theorem mem_ker_firstCoord {w : unitaryFourW K hK} : w ∈ (firstCoord hK).ker ↔ fst w = 0 := by
  rw [MonoidHom.mem_ker, firstCoord_apply]
  exact ofAdd_eq_one

theorem snd_pow_four_of_fst_eq_zero {w : unitaryFourW K hK} (hw : fst w = 0) :
    snd w ^ 4 = snd w := by
  have := charP_two_of_natCard_eq_sixteen hK
  have h := snd_add_snd_pow_four w
  rw [hw] at h
  grind

theorem natCard_ker_firstCoord : Nat.card (firstCoord hK).ker = 4 := by
  have := charP_two_of_natCard_eq_sixteen hK
  have ht (t : {t : K // t ^ 4 = t}) : (t : K) + (t : K) ^ 4 = 0 ^ 5 := by
    have := t.2
    grind
  rw [← natCard_pow_four_eq_self hK]
  refine Nat.card_congr
    { toFun := fun w => ⟨snd (w : unitaryFourW K hK),
        snd_pow_four_of_fst_eq_zero (mem_ker_firstCoord.mp w.2)⟩
      invFun := fun t => ⟨mk hK 0 t (ht t), mem_ker_firstCoord.mpr (fst_mk _ _ _)⟩
      left_inv := fun w => ?_
      right_inv := fun t => ?_ }
  · apply Subtype.ext
    ext
    · rw [fst_mk, mem_ker_firstCoord.mp w.2]
    · rw [snd_mk]
  · apply Subtype.ext
    exact snd_mk (hK := hK) 0 (t : K) (ht t)

theorem natCard_unitaryFourW : Nat.card (unitaryFourW K hK) = 64 := by
  have := finite_of_natCard_eq_sixteen hK
  rw [← (firstCoord hK).ker.card_mul_index, Subgroup.index_ker, natCard_ker_firstCoord,
    MonoidHom.range_eq_top.mpr firstCoord_surjective, Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, hK]

theorem finite_unitaryFourW : Finite (unitaryFourW K hK) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_unitaryFourW]; norm_num)

theorem mem_center_of_fst_eq_zero {w : unitaryFourW K hK} (hw : fst w = 0) :
    w ∈ Subgroup.center (unitaryFourW K hK) := by
  rw [Subgroup.mem_center_iff]
  intro v
  ext
  · rw [fst_mul, fst_mul, hw, add_zero, zero_add]
  · rw [snd_mul, snd_mul, hw]
    ring

theorem center_eq_ker_firstCoord : Subgroup.center (unitaryFourW K hK) = (firstCoord hK).ker := by
  have := finite_of_natCard_eq_sixteen hK
  have := charP_two_of_natCard_eq_sixteen hK
  apply le_antisymm
  · intro w hw
    rw [mem_ker_firstCoord]
    by_contra ha
    obtain ⟨r, hr⟩ : ∃ r : K, r ^ 4 ≠ r := by
      by_contra hall
      push Not at hall
      have h := natCard_pow_four_eq_self hK
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), hK] at h
      omega
    obtain ⟨v, hv⟩ := exists_fst_eq (hK := hK) (fst w * r)
    have h := congrArg snd ((Subgroup.mem_center_iff.mp hw) v)
    rw [snd_mul, snd_mul, hv] at h
    have h16 := pow_sixteen_eq_self hK (fst w)
    have h' : fst w ^ 5 * (r ^ 4 - r) = 0 := by grind
    rcases mul_eq_zero.mp h' with h' | h'
    · exact ha ((pow_eq_zero_iff (by norm_num)).mp h')
    · exact hr (sub_eq_zero.mp h')
  · intro w hw
    exact mem_center_of_fst_eq_zero (mem_ker_firstCoord.mp hw)

theorem commutator_eq_ker_firstCoord : commutator (unitaryFourW K hK) = (firstCoord hK).ker := by
  have := charP_two_of_natCard_eq_sixteen hK
  apply le_antisymm (Abelianization.commutator_subset_ker _)
  intro w hw
  have hw0 := mem_ker_firstCoord.mp hw
  obtain ⟨r, hr⟩ := exists_add_pow_four_eq hK (snd_pow_four_of_fst_eq_zero hw0)
  obtain ⟨v₁, hv₁⟩ := exists_fst_eq (hK := hK) 1
  obtain ⟨v₂, hv₂⟩ := exists_fst_eq (hK := hK) r
  have hcomm : ⁅v₁, v₂⁆ = w := by
    ext
    · rw [fst_commutatorElement, hw0]
    · rw [snd_commutatorElement, hv₁, hv₂, ← hr]
      ring
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem center_eq_commutator :
    Subgroup.center (unitaryFourW K hK) = commutator (unitaryFourW K hK) :=
  center_eq_ker_firstCoord.trans commutator_eq_ker_firstCoord.symm

theorem mem_center_iff {w : unitaryFourW K hK} :
    w ∈ Subgroup.center (unitaryFourW K hK) ↔
      ∃ t : K, t ^ 4 = t ∧
        ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = unitaryFourMatrix 0 t := by
  rw [center_eq_ker_firstCoord, mem_ker_firstCoord]
  constructor
  · intro hw
    exact ⟨snd w, snd_pow_four_of_fst_eq_zero hw, by rw [coe_eq, hw]⟩
  · rintro ⟨t, -, h⟩
    exact fst_eq_of_coe_eq h

theorem natCard_center : Nat.card (Subgroup.center (unitaryFourW K hK)) = 4 := by
  rw [center_eq_ker_firstCoord]
  exact natCard_ker_firstCoord

theorem sq_eq_one_of_mem_center {w : unitaryFourW K hK}
    (hw : w ∈ Subgroup.center (unitaryFourW K hK)) : w ^ 2 = 1 := by
  rw [center_eq_ker_firstCoord, mem_ker_firstCoord] at hw
  ext
  · rw [fst_sq, fst_one]
  · rw [snd_sq, hw, snd_one, zero_pow (by norm_num)]

end UnitaryFourW

end

end CFSG.RankTwoShapes
