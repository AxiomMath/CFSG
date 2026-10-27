module

public import CFSG.LieType.SeitzGeneration.HeisLinearFourier
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix Fin.NatCast Fin.CommRing

open scoped commutatorElement

theorem mem_of_conj {G : Type*} [Group G] {K : Subgroup G} {g x y : G} (hg : g ∈ K)
    (hx : x ∈ K) (h : g * x = y * g) : y ∈ K := by
  have e : y = g * x * g⁻¹ := by rw [h, mul_inv_cancel_right]
  rw [e]
  exact K.mul_mem (K.mul_mem hg hx) (K.inv_mem hg)

theorem mem_of_mul_eq_mul {G : Type*} [Group G] {K : Subgroup G} {g x y : G} (hg : g ∈ K)
    (hx : x ∈ K) (h : x * g = g * y) : y ∈ K := by
  have e : y = g⁻¹ * (x * g) := by rw [h, inv_mul_cancel_left]
  rw [e, ← mul_assoc]
  exact K.mul_mem (K.mul_mem (K.inv_mem hg) hx) hg

theorem commutator_mem_of_mem {G : Type*} [Group G] {K : Subgroup G} {x y : G} (hx : x ∈ K)
    (hy : y ∈ K) : ⁅x, y⁆ ∈ K := by
  rw [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)

theorem shift_ne {p : ℕ} [NeZero p] {a b : Fin p} (hab : a ≠ b) : a + 1 ≠ b + 1 :=
  fun h => hab (add_right_cancel h)

theorem single_mul_heisShiftMat {F : Type*} [Field F] {p : ℕ} [NeZero p] (a b : Fin p)
    (d : F) :
    Matrix.single a b d * heisShiftMat F p =
      heisShiftMat F p * Matrix.single (a + 1) (b + 1) d := by
  ext x y
  by_cases hx : x = a <;> by_cases hy : y = b + 1
  · subst hx
    subst hy
    simp [single_mul_apply_same, mul_single_apply_same, heisShiftMat_entry, finRotate_apply]
  · subst hx
    simp [single_mul_apply_same, mul_single_apply_of_ne, heisShiftMat_entry, finRotate_apply,
      Ne.symm hy, hy]
  · simp [single_mul_apply_of_ne, mul_single_apply_same, heisShiftMat_entry, finRotate_apply,
      hx, hy]
  · simp [single_mul_apply_of_ne, mul_single_apply_of_ne, hx, hy]

theorem transvection_mul_shift {F : Type*} [Field F] {p : ℕ} [NeZero p]
    {S : Matrix.SpecialLinearGroup (Fin p) F}
    (hS : (S : Matrix (Fin p) (Fin p) F) = heisShiftMat F p)
    {a b : Fin p} (hab : a ≠ b) (d : F) :
    Matrix.SpecialLinearGroup.transvection hab d * S =
      S * Matrix.SpecialLinearGroup.transvection (shift_ne hab) d := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hS,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, single_mul_heisShiftMat]

theorem transvection_congr {F : Type*} [Field F] {p : ℕ} {a b a' b' : Fin p} (ha : a = a')
    (hb : b = b') (hab : a ≠ b) (hab' : a' ≠ b') (d : F) :
    Matrix.SpecialLinearGroup.transvection hab d =
      Matrix.SpecialLinearGroup.transvection hab' d := by
  subst ha
  subst hb
  rfl

theorem exists_ne_ne {p : ℕ} (hp3 : 3 ≤ p) (i j : Fin p) :
    ∃ k : Fin p, k ≠ i ∧ k ≠ j := by
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset (Fin p)) ⊆ {i, j} := by
    intro k _
    by_cases hk : k = i
    · simp [hk]
    · simp [h k hk]
  have h1 := Finset.card_le_card hsub
  have h2 : ({i, j} : Finset (Fin p)).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

@[expose] def rootDiagT {F : Type*} [Field F] {p : ℕ} (i k : Fin p) (a : F) : Fin p → F :=
  fun x => if x = i then a else if x = k then a⁻¹ else 1

theorem det_diagT {F : Type*} [Field F] {p : ℕ} {i k : Fin p} (hik : i ≠ k) (a : F)
    (ha : a ≠ 0) : (Matrix.diagonal (rootDiagT i k a)).det = 1 := by
  have h0 : ∀ c ∈ (Finset.univ : Finset (Fin p)), c ≠ i ∧ c ≠ k → rootDiagT i k a c = 1 := by
    rintro c - ⟨h1, h2⟩
    simp [rootDiagT, h1, h2]
  rw [Matrix.det_diagonal, Finset.prod_eq_mul i k hik h0
    (fun h => absurd (Finset.mem_univ _) h) (fun h => absurd (Finset.mem_univ _) h)]
  simp [rootDiagT, hik, Ne.symm hik, ha]

@[expose] def diagAt {F : Type*} [Field F] {p : ℕ} {i k : Fin p} (hik : i ≠ k) (a : F)
    (ha : a ≠ 0) : Matrix.SpecialLinearGroup (Fin p) F :=
  ⟨Matrix.diagonal (rootDiagT i k a), det_diagT hik a ha⟩

theorem diagonal_mul_transvection_eq {F : Type*} [Field F] {p : ℕ} {i j : Fin p}
    (hij : i ≠ j) (t : Fin p → F) (a c : F) (hti : t i = a) (htj : t j = 1) :
    Matrix.diagonal t * Matrix.transvection i j c =
      Matrix.transvection i j (a * c) * Matrix.diagonal t := by
  ext x y
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transvection, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases h : i = x ∧ j = y
  · obtain ⟨rfl, rfl⟩ := h
    simp [hij, hti, htj]
  · by_cases hxy : x = y
    · subst hxy
      simp [h]
    · simp [hxy, h]

theorem diagAt_mul_transvection {F : Type*} [Field F] {p : ℕ} {i j k : Fin p}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a c : F) (ha : a ≠ 0) :
    diagAt hik a ha * Matrix.SpecialLinearGroup.transvection hij c =
      Matrix.SpecialLinearGroup.transvection hij (a * c) * diagAt hik a ha := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have hti : rootDiagT i k a i = a := by simp [rootDiagT]
  have htj : rootDiagT i k a j = 1 := by simp [rootDiagT, Ne.symm hij, hjk]
  exact diagonal_mul_transvection_eq hij (rootDiagT i k a) a c hti htj

theorem transvection_mem_all_of_torus {F : Type*} [Field F] {p : ℕ}
    {K : Subgroup (Matrix.SpecialLinearGroup (Fin p) F)}
    (hT : ∀ g : Matrix.SpecialLinearGroup (Fin p) F,
      (∃ t : Fin p → F, (g : Matrix (Fin p) (Fin p) F) = Matrix.diagonal t) → g ∈ K)
    (hp3 : 3 ≤ p) {i j : Fin p} (hij : i ≠ j) {c : F} (hc : c ≠ 0)
    (hx : Matrix.SpecialLinearGroup.transvection hij c ∈ K) (d : F) :
    Matrix.SpecialLinearGroup.transvection hij d ∈ K := by
  by_cases hd : d = 0
  · subst hd
    simp
  · obtain ⟨k, hki, hkj⟩ := exists_ne_ne hp3 i j
    have ha : d / c ≠ 0 := div_ne_zero hd hc
    have hD : diagAt hki.symm (d / c) ha ∈ K := hT _ ⟨rootDiagT i k (d / c), rfl⟩
    have hconj := diagAt_mul_transvection hij hki.symm hkj.symm (d / c) c ha
    have hmem := mem_of_conj hD hx hconj
    rwa [div_mul_cancel₀ d hc] at hmem

theorem transvection_mem_shift {F : Type*} [Field F] {p : ℕ} [NeZero p]
    {K : Subgroup (Matrix.SpecialLinearGroup (Fin p) F)}
    {S : Matrix.SpecialLinearGroup (Fin p) F}
    (hS : (S : Matrix (Fin p) (Fin p) F) = heisShiftMat F p)
    (hSK : S ∈ K) {i j : Fin p} (hij : i ≠ j)
    (hx : ∀ d : F, Matrix.SpecialLinearGroup.transvection hij d ∈ K) :
    ∀ (n : ℕ) (a b : Fin p) (hab : a ≠ b), a = i + (n : Fin p) → b = j + (n : Fin p) →
      ∀ d : F, Matrix.SpecialLinearGroup.transvection hab d ∈ K := by
  intro n
  induction n with
  | zero =>
    intro a b hab ha hb d
    simp only [Nat.cast_zero, add_zero] at ha hb
    subst ha
    subst hb
    exact hx d
  | succ n ih =>
    intro a b hab ha hb d
    have hab' : i + (n : Fin p) ≠ j + (n : Fin p) := fun h => hij (add_right_cancel h)
    have h1 := ih (i + (n : Fin p)) (j + (n : Fin p)) hab' rfl rfl d
    have h2 := mem_of_mul_eq_mul hSK h1 (transvection_mul_shift hS hab' d)
    have ea : a = i + (n : Fin p) + 1 := by
      rw [ha, Nat.cast_succ]
      ring
    have eb : b = j + (n : Fin p) + 1 := by
      rw [hb, Nat.cast_succ]
      ring
    rw [transvection_congr ea eb hab (shift_ne hab') d]
    exact h2

theorem transvection_mem_step {F : Type*} [Field F] {p : ℕ} [NeZero p]
    {K : Subgroup (Matrix.SpecialLinearGroup (Fin p) F)}
    {S : Matrix.SpecialLinearGroup (Fin p) F}
    (hS : (S : Matrix (Fin p) (Fin p) F) = heisShiftMat F p)
    (hSK : S ∈ K) {i j : Fin p} (hij : i ≠ j)
    (hx : ∀ d : F, Matrix.SpecialLinearGroup.transvection hij d ∈ K) :
    ∀ (a b : Fin p) (hab : a ≠ b), b = a + (j - i) → ∀ d : F,
      Matrix.SpecialLinearGroup.transvection hab d ∈ K := by
  intro a b hab hb d
  have hn : ((a - i).val : Fin p) = a - i := Fin.cast_val_eq_self _
  exact transvection_mem_shift hS hSK hij hx (a - i).val a b hab
    (by rw [hn]; ring) (by rw [hb, hn]; ring) d

theorem natCast_mul_ne_zero {p : ℕ} [NeZero p] (hp : p.Prime) {δ : Fin p} (hδ : δ ≠ 0)
    {m : ℕ} (hm0 : 0 < m) (hmp : m < p) : (m : Fin p) * δ ≠ 0 := by
  intro h
  have hv : m * δ.val % p = 0 := by
    have h2 := congrArg Fin.val h
    simpa [Fin.val_mul, Nat.mod_eq_of_lt hmp] using h2
  have hdvd : p ∣ m * δ.val := Nat.dvd_of_mod_eq_zero hv
  have hδv : 0 < δ.val := Nat.pos_of_ne_zero (fun h0 => hδ (Fin.ext (by simp [h0])))
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
  · have := Nat.le_of_dvd hm0 h1
    omega
  · have := Nat.le_of_dvd hδv h1
    have := δ.isLt
    omega

theorem exists_mul_eq {p : ℕ} [NeZero p] (hp : p.Prime) {δ : Fin p} (hδ : δ ≠ 0)
    (c : Fin p) : ∃ x : Fin p, x * δ = c := by
  have inj : Function.Injective (fun x : Fin p => x * δ) := by
    intro x y hxy
    by_contra hne
    have h0 : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hz : ((x - y).val : Fin p) * δ = 0 := by
      rw [Fin.cast_val_eq_self, sub_mul]
      exact sub_eq_zero.mpr hxy
    exact natCast_mul_ne_zero hp hδ
      (Nat.pos_of_ne_zero (fun h => h0 (Fin.ext (by simp [h])))) (x - y).isLt hz
  exact Finite.injective_iff_surjective.mp inj c

theorem transvection_mem_progression {F : Type*} [Field F] {p : ℕ} [NeZero p] (hp : p.Prime)
    {K : Subgroup (Matrix.SpecialLinearGroup (Fin p) F)} {δ : Fin p} (hδ : δ ≠ 0)
    (h1 : ∀ (a b : Fin p) (hab : a ≠ b), b = a + δ → ∀ d : F,
      Matrix.SpecialLinearGroup.transvection hab d ∈ K) :
    ∀ (n : ℕ), n + 1 < p → ∀ (a b : Fin p) (hab : a ≠ b),
      b = a + ((n + 1 : ℕ) : Fin p) * δ → ∀ d : F,
      Matrix.SpecialLinearGroup.transvection hab d ∈ K := by
  intro n
  induction n with
  | zero =>
    intro _ a b hab hb d
    refine h1 a b hab ?_ d
    rw [hb]
    simp
  | succ n ih =>
    intro hnp a b hab hb d
    obtain ⟨c, hc⟩ : ∃ c : Fin p, c = a + ((n + 1 : ℕ) : Fin p) * δ := ⟨_, rfl⟩
    have hX : ((n + 1 : ℕ) : Fin p) * δ ≠ 0 :=
      natCast_mul_ne_zero hp hδ (by omega) (by omega)
    have hac : a ≠ c := by
      intro h
      apply hX
      linear_combination -hc - h
    have hb' : b = c + δ := by
      rw [hb, hc]
      push_cast
      ring
    have hcb : c ≠ b := by
      intro h
      apply hδ
      linear_combination -h - hb'
    have e1 := ih (by omega) a c hac hc d
    have e2 := h1 c b hcb hb' 1
    have key := Matrix.SpecialLinearGroup.commutatorElement_transvection hac hcb hab d 1
    rw [mul_one] at key
    rw [← key]
    exact commutator_mem_of_mem e1 e2

theorem transvection_mem_of_progression {F : Type*} [Field F] {p : ℕ} [NeZero p]
    (hp : p.Prime) {K : Subgroup (Matrix.SpecialLinearGroup (Fin p) F)} {δ : Fin p}
    (hδ : δ ≠ 0)
    (h1 : ∀ (a b : Fin p) (hab : a ≠ b), b = a + δ → ∀ d : F,
      Matrix.SpecialLinearGroup.transvection hab d ∈ K)
    (a b : Fin p) (hab : a ≠ b) (d : F) :
    Matrix.SpecialLinearGroup.transvection hab d ∈ K := by
  obtain ⟨x, hx⟩ := exists_mul_eq hp hδ (b - a)
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply sub_ne_zero.mpr (Ne.symm hab)
    rw [← hx, zero_mul]
  have hxv : x.val ≠ 0 := fun h0 => hx0 (Fin.ext (by simp [h0]))
  obtain ⟨n, hn⟩ : ∃ n, x.val = n + 1 := ⟨x.val - 1, by omega⟩
  have hb : b = a + ((n + 1 : ℕ) : Fin p) * δ := by
    rw [← hn, Fin.cast_val_eq_self, hx]
    ring
  exact transvection_mem_progression hp hδ h1 n (by have := x.isLt; omega) a b hab hb d

theorem eq_top_of_torus_shift_root {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    {K : Subgroup (Matrix.SpecialLinearGroup (Fin p) F)}
    (hT : ∀ g : Matrix.SpecialLinearGroup (Fin p) F,
      (∃ t : Fin p → F, (g : Matrix (Fin p) (Fin p) F) = Matrix.diagonal t) → g ∈ K)
    (hS : ∀ g : Matrix.SpecialLinearGroup (Fin p) F,
      (g : Matrix (Fin p) (Fin p) F) = heisShiftMat F p → g ∈ K)
    {i j : Fin p} (hij : i ≠ j) {c : F} (hc : c ≠ 0)
    (hx : Matrix.SpecialLinearGroup.transvection hij c ∈ K) : K = ⊤ := by
  haveI : NeZero p := ⟨by omega⟩
  have hp : p.Prime := Fact.out
  have hodd : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left (by omega))
  obtain ⟨S, hS'⟩ : ∃ S : Matrix.SpecialLinearGroup (Fin p) F,
      (S : Matrix (Fin p) (Fin p) F) = heisShiftMat F p :=
    ⟨⟨heisShiftMat F p, det_heisShiftMat F hodd⟩, rfl⟩
  have hSK : S ∈ K := hS S hS'
  have hall : ∀ d : F, Matrix.SpecialLinearGroup.transvection hij d ∈ K :=
    fun d => transvection_mem_all_of_torus hT hp3 hij hc hx d
  have hδ0 : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
  have hstep := transvection_mem_step hS' hSK hij hall
  have hprog := transvection_mem_of_progression hp hδ0 hstep
  have htop : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup
      (ι := Fin p) (F := F))) = ⊤ :=
    Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  exact hprog t.i t.j t.hij t.c

end CFSG.LieType.SeitzGeneration
