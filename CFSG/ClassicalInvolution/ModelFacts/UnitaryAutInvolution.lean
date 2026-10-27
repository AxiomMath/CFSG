module

public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutBlocks
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Chart
public import CFSG.ClassicalInvolution.Phan.Center

public section

namespace CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

open Matrix CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalInvolution.Models

section Sign

@[expose] def signVal (K : Type) [Field K] (b : ZMod 2) : K := if b = 0 then 1 else -1

theorem signVal_mul_self {K : Type} [Field K] (b : ZMod 2) : signVal K b * signVal K b = 1 := by
  unfold signVal
  split_ifs <;> simp

theorem signVal_mul_signVal_of_ne {K : Type} [Field K] {b c : ZMod 2} (h : b ≠ c) :
    signVal K b * signVal K c = -1 := by
  have hb : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  unfold signVal
  rcases hb b with rfl | rfl <;> rcases hb c with rfl | rfl <;> simp_all

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] noncomputable def negOneN : normOne (unitaryInvolution K p f) :=
  ⟨-1, (mem_normOne _).2 (by simp)⟩

@[expose] noncomputable def signN (b : ZMod 2) : normOne (unitaryInvolution K p f) :=
  if b = 0 then 1 else negOneN

theorem coe_signN (b : ZMod 2) :
    (((signN b : normOne (unitaryInvolution K p f)) : Kˣ) : K) = signVal K b := by
  unfold signN signVal
  split_ifs <;> simp [negOneN]

theorem coe_signN_inv (b : ZMod 2) :
    ((((signN b : normOne (unitaryInvolution K p f)) : Kˣ)⁻¹ : Kˣ) : K) = signVal K b := by
  unfold signN signVal
  split_ifs <;> simp [negOneN]

@[expose] noncomputable def conjSign (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (v : Fin n → ZMod 2) :
    Su K p f n →* Su K p f n :=
  conjDiag hK fun i => signN (v i)

theorem coe_coe_conjSign_apply (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (v : Fin n → ZMod 2)
    (x : Su K p f n) (a b : Fin n) :
    (((conjSign hK v x : Su K p f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b =
      signVal K (v a) * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b * signVal K (v b) := by
  rw [conjSign, coe_conjDiag_apply, coe_signN, coe_signN_inv]

end Sign

section Coordinate

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem mem_LcU_iff {T : Pair n} {x : Su K p f n} :
    x ∈ LcU K p f T ↔ suMat x * zMat K n T.1 = zMat K n T.1 * suMat x ∧
      suMat x * (1 + zMat K n T.1) = 1 + zMat K n T.1 :=
  Iff.rfl

theorem LcU_entry (h2 : (2 : K) ≠ 0) {T : Pair n} {x : Su K p f n} (hx : x ∈ LcU K p f T)
    (a b : Fin n) (hab : ¬ (a ∈ T.1 ∧ b ∈ T.1)) :
    suMat x a b = if a = b then 1 else 0 := by
  obtain ⟨h1, h3⟩ := mem_LcU_iff.mp hx
  have e1 := congrFun (congrFun h1 a) b
  have e3 := congrFun (congrFun h3 a) b
  simp only [zMat, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_add, Matrix.mul_one,
    Matrix.add_apply, Matrix.one_apply, Matrix.diagonal_apply] at e1 e3
  by_cases hb : b ∈ T.1
  · have ha : a ∉ T.1 := fun ha => hab ⟨ha, hb⟩
    have hne : a ≠ b := fun h => ha (h ▸ hb)
    simp only [hb, ha, ite_true, ite_false] at e1
    simp only [hne, ite_false]
    have : (2 : K) * suMat x a b = 0 := by linear_combination -e1
    exact (mul_eq_zero.mp this).resolve_left h2
  · by_cases hab' : a = b
    · subst hab'
      simp only [hb, ite_false, ite_true] at e3 ⊢
      have : (2 : K) * suMat x a a = 2 * 1 := by linear_combination e3
      exact mul_left_cancel₀ h2 this
    · simp only [hb, ite_false, hab'] at e3 ⊢
      have : (2 : K) * suMat x a b = 0 := by linear_combination e3
      exact (mul_eq_zero.mp this).resolve_left h2

theorem conjSign_mem_LcU (hK : Nat.card K = (p ^ f) ^ 2) (v : Fin n → ZMod 2) {T : Pair n}
    {x : Su K p f n} (hx : x ∈ LcU K p f T) : conjSign hK v x ∈ LcU K p f T := by
  obtain ⟨h1, h3⟩ := mem_LcU_iff.mp hx
  refine mem_LcU_iff.mpr ⟨Matrix.ext fun a b => ?_, Matrix.ext fun a b => ?_⟩
  · have e1 := congrFun (congrFun h1 a) b
    simp only [suMat, zMat, Matrix.mul_diagonal, Matrix.diagonal_mul,
      coe_coe_conjSign_apply] at e1 ⊢
    linear_combination (signVal K (v a) * signVal K (v b)) * e1
  · have e3 := congrFun (congrFun h3 a) b
    simp only [suMat, zMat, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_diagonal,
      Matrix.one_apply, Matrix.diagonal_apply, coe_coe_conjSign_apply] at e3 ⊢
    by_cases hab : a = b
    · subst hab
      simp only [ite_true] at e3 ⊢
      have := signVal_mul_self (K := K) (v a)
      linear_combination (signVal K (v a) * signVal K (v a)) * e3 +
        (1 + (if a ∈ T.1 then -1 else 1)) * this
    · simp only [hab, ite_false] at e3 ⊢
      linear_combination (signVal K (v a) * signVal K (v b)) * e3

theorem conjSign_eq_of_const (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0)
    (v : Fin n → ZMod 2) {T : Pair n} (hv : ∀ a ∈ T.1, ∀ b ∈ T.1, v a = v b)
    {x : Su K p f n} (hx : x ∈ LcU K p f T) : conjSign hK v x = x := by
  refine Subtype.ext (Units.ext (Matrix.ext fun a b => ?_))
  have := coe_coe_conjSign_apply hK v x a b
  rw [this]
  by_cases hab : a ∈ T.1 ∧ b ∈ T.1
  · rw [hv a hab.1 b hab.2]
    change signVal K (v b) * suMat x a b * signVal K (v b) = suMat x a b
    linear_combination (suMat x a b) * signVal_mul_self (K := K) (v b)
  · have := LcU_entry h2 hx a b hab
    change signVal K (v a) * suMat x a b * signVal K (v b) = suMat x a b
    rw [this]
    by_cases hab' : a = b
    · subst hab'
      simp only [ite_true]
      linear_combination signVal_mul_self (K := K) (v a)
    · simp [hab']

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem unitSignedSwapMatrix_apply' {i j : Fin n} (a b : Fin n) :
    (unitSignedSwapMatrix i j : Matrix (Fin n) (Fin n) K) a b =
      if Equiv.swap i j a = b then (if a = i then -1 else 1) else 0 := by
  rw [unitSignedSwapMatrix, Matrix.diagonal_mul]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem swap_zdiag_eq {i j : Fin n} (a b : Fin n) (hab : Equiv.swap i j a = b) :
    (if b ∈ ({i, j} : Finset (Fin n)) then (-1 : K) else 1) =
      (if a ∈ ({i, j} : Finset (Fin n)) then (-1 : K) else 1) := by
  subst hab
  by_cases h1 : a = i
  · subst h1; simp
  · by_cases h3 : a = j
    · subst h3; simp
    · simp [Equiv.swap_apply_of_ne_of_ne h1 h3, h1, h3]

theorem exists_swap_mem_LcU (hK : Nat.card K = (p ^ f) ^ 2) (h : UnitaryFieldData p f K)
    {T : Pair n} {i j : Fin n} (hij : i ≠ j) (hT : T.1 = {i, j}) :
    ∃ x ∈ LcU K p f T, ∀ v : Fin n → ZMod 2, v i ≠ v j →
      conjSign hK v x = zEltU K p f T * x := by
  obtain ⟨M, hM, hMmem⟩ := unitSignedSwapMatrix_mem (E := K) (m := n) h hij
  have hMSU : M ∈ SUid (unitaryInvolution K p f) n := by
    have : M ∈ unitarySU p f K n := by rw [unitarySU_eq_gramSU h]; exact hMmem
    rw [SUid_eq_statedSU hK n]
    exact this
  have hxe : ∀ a b, suMat (⟨M, hMSU⟩ : Su K p f n) a b =
      if Equiv.swap i j a = b then (if a = i then -1 else 1) else 0 := fun a b => by
    change (M : Matrix (Fin n) (Fin n) K) a b = _
    rw [hM, unitSignedSwapMatrix_apply']
  refine ⟨⟨M, hMSU⟩, ?_, fun v hv => ?_⟩
  · rw [mem_LcU_iff, hT]
    refine ⟨Matrix.ext fun a b => ?_, Matrix.ext fun a b => ?_⟩
    · simp only [zMat, Matrix.mul_diagonal, Matrix.diagonal_mul, hxe]
      by_cases hab : Equiv.swap i j a = b
      · rw [ite_eq_left hab, swap_zdiag_eq a b hab, mul_comm]
      · simp [hab]
    · simp only [zMat, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_diagonal,
        Matrix.one_apply, Matrix.diagonal_apply, hxe]
      by_cases hab : Equiv.swap i j a = b
      · rw [ite_eq_left hab, swap_zdiag_eq a b hab]
        by_cases ha : a ∈ ({i, j} : Finset (Fin n))
        · have hne : a ≠ b := by
            rw [← hab]
            rcases Finset.mem_insert.mp ha with rfl | ha'
            · simp [hij]
            · rw [Finset.mem_singleton] at ha'
              subst ha'
              simp [hij.symm]
          simp [ha, hne]
        · have hb : b = a := by
            rw [← hab]
            exact Equiv.swap_apply_of_ne_of_ne (fun h' => ha (by simp [h']))
              (fun h' => ha (by simp [h']))
          subst hb
          have hai : b ≠ i := fun h' => ha (by simp [h'])
          simp [ha, hai]
      · rw [ite_eq_right hab]
        by_cases hab' : a = b
        · subst hab'
          have ha : a ∈ ({i, j} : Finset (Fin n)) := by
            by_contra ha
            exact hab (Equiv.swap_apply_of_ne_of_ne (fun h' => ha (by simp [h']))
              (fun h' => ha (by simp [h'])))
          simp [ha]
        · simp [hab']
  · refine Subtype.ext (Units.ext (Matrix.ext fun a b => ?_))
    rw [coe_coe_conjSign_apply]
    change signVal K (v a) * suMat (⟨M, hMSU⟩ : Su K p f n) a b * signVal K (v b) =
      suMat (zEltU K p f T * (⟨M, hMSU⟩ : Su K p f n)) a b
    rw [suMat_mul, suMat_zEltU, hT]
    simp only [zMat, Matrix.diagonal_mul, hxe]
    by_cases hab : Equiv.swap i j a = b
    · rw [ite_eq_left hab]
      by_cases ha : a ∈ ({i, j} : Finset (Fin n))
      · rcases Finset.mem_insert.mp ha with rfl | ha'
        · have hb : b = j := by rw [← hab]; simp
          subst hb
          rw [ite_eq_left ha]
          have := signVal_mul_signVal_of_ne (K := K) hv
          simp only [ite_true]
          linear_combination (-1 : K) * this
        · rw [Finset.mem_singleton] at ha'
          subst ha'
          have hb : b = i := by rw [← hab]; simp
          subst hb
          rw [ite_eq_left ha]
          have := signVal_mul_signVal_of_ne (K := K) hv.symm
          simp [hij.symm]
          linear_combination this
      · have hai : a ≠ i := fun h' => ha (by simp [h'])
        have haj : a ≠ j := fun h' => ha (by simp [h'])
        have hb : b = a := by
          rw [← hab]
          exact Equiv.swap_apply_of_ne_of_ne hai haj
        subst hb
        rw [ite_eq_right ha]
        simp only [hai, ite_false]
        linear_combination (signVal_mul_self (K := K) (v b))
    · simp [hab]

end Coordinate

section Helpers

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_normOne_ne (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    ∃ u : normOne (unitaryInvolution K p f), ((u : Kˣ) : K) ≠ 1 ∧
      (((u : Kˣ)⁻¹ : Kˣ) : K) ≠ ((u : Kˣ) : K) := by
  obtain ⟨c, hcN, hck⟩ := exists_norm_one_not_fixed h hp2
  have hbar : ∀ x, h.bar x = unitaryInvolution K p f x := fun x => by
    rw [UnitaryFieldData.bar_apply, unitaryInvolution_apply]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcN
    exact zero_ne_one hcN
  have hcσ : unitaryInvolution K p f c * c = 1 := by rw [← hbar]; exact hcN
  refine ⟨⟨Units.mk0 c hc0, (mem_normOne _).2 (by simpa using hcσ)⟩, ?_, ?_⟩
  · intro h1
    exact hck (by simp only [Units.val_mk0] at h1; rw [h1]; exact one_mem _)
  · intro h1
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0] at h1
    apply hck
    have h3 : c * c = 1 := by
      calc c * c = c * c⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel₀ hc0
    rcases mul_self_eq_one_iff.mp h3 with h4 | h4
    · rw [h4]; exact one_mem _
    · rw [h4]; exact neg_mem (one_mem _)

theorem lift_matrix_of_fixed (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) {Y : Type}
    [Group Y] {θ : Su K p f n →* Y} (hker : θ.ker ≤ Subgroup.center (Su K p f n)) {σ : Y ≃* Y}
    {α : Su K p f n →* Su K p f n} (hα : ∀ x, θ (α x) = σ (θ x)) {x : Su K p f n}
    (hx : σ (θ x) = θ x) :
    ∃ u : Kˣ, suMat (α x) = (u : K) • suMat x := by
  have hz : x⁻¹ * α x ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hα, hx, inv_mul_cancel]
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) hn (hker hz)
  refine ⟨u, ?_⟩
  have h1 : α x = x * (x⁻¹ * α x) := by group
  have h2 : suMat (α x) = suMat x * Matrix.scalar (Fin n) (u : K) := by
    rw [h1]
    rw [suMat_mul]
    exact congrArg (suMat x * ·) hu
  rw [h2, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

end Helpers

section EntryCases

variable {K : Type} [Field K]

theorem torus_entry_cases_id {m : ℕ} (a : Fin m) (u : K) (hu1 : u ≠ 1) (hu2 : u⁻¹ ≠ u)
    (i j : Fin (m + 1)) (x : K) (hx : x ≠ 0)
    (h : (if i.val = a.val then u else if i.val = a.val + 1 then u⁻¹ else 1) * x =
      x * (if j.val = a.val then u else if j.val = a.val + 1 then u⁻¹ else 1)) :
    i = j ∨ (i.val ≠ a.val ∧ i.val ≠ a.val + 1 ∧ j.val ≠ a.val ∧ j.val ≠ a.val + 1) := by
  have h' : (if i.val = a.val then u else if i.val = a.val + 1 then u⁻¹ else 1) =
      (if j.val = a.val then u else if j.val = a.val + 1 then u⁻¹ else 1) := by
    apply mul_right_cancel₀ hx
    rw [h, mul_comm]
  have hi : i.val = a.val ∨ i.val = a.val + 1 ∨ (i.val ≠ a.val ∧ i.val ≠ a.val + 1) := by omega
  have hj : j.val = a.val ∨ j.val = a.val + 1 ∨ (j.val ≠ a.val ∧ j.val ≠ a.val + 1) := by omega
  have hu1' : u⁻¹ ≠ 1 := fun h0 => hu1 (by simpa using h0)
  rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj
  · exact Or.inl (Fin.ext (by omega))
  · simp [hi, hj] at h'
    exact absurd h' hu2.symm
  · simp [hi, hj.1, hj.2, hu1] at h'
  · simp [hi, hj] at h'
    exact absurd h' hu2
  · exact Or.inl (Fin.ext (by omega))
  · simp [hi, hj.1, hj.2, hu1'] at h'
  · simp [hi.1, hi.2, hj] at h'
    exact absurd h' hu1.symm
  · simp [hi.1, hi.2, hj] at h'
    exact absurd h' hu1
  · exact Or.inr ⟨hi.1, hi.2, hj.1, hj.2⟩

end EntryCases

section Diagonal

variable {K : Type} [Field K]

theorem entry_conj_diag_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] (G Gi : Matrix ι ι K)
    (hGGi : G * Gi = 1) (m : ι → K) (i : ι) (hm : ∀ k, G i k ≠ 0 → m k = 1) :
    (G * diagonal m * Gi) i i = 1 := by
  have h1 : (G * diagonal m * Gi) i i = ∑ k, G i k * m k * Gi k i := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal]
  rw [h1, ← one_apply_eq i, ← hGGi, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : G i k = 0
  · simp [hk]
  · rw [hm k hk, mul_one]

end Diagonal

section Tail

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem coe_coe_blockEmb_tail_diagSU {k : ℕ}
    (d : Fin k → normOne (unitaryInvolution K p f)) (hd : d ∈ detKer (unitaryInvolution K p f) k) :
    (((blockEmb K p f (k + 2) k 2 (by omega) (diagSU (unitaryInvolution K p f) d hd) :
      Su K p f (k + 2)) : GL (Fin (k + 2)) K) : Matrix (Fin (k + 2)) (Fin (k + 2)) K) =
      diagonal fun i : Fin (k + 2) =>
        if h : 2 ≤ i.val then (((d ⟨i.val - 2, by omega⟩ : normOne (unitaryInvolution K p f)) :
          Kˣ) : K) else 1 := by
  change blockMat (k + 2) 2 (((diagSU (unitaryInvolution K p f) d hd : Su K p f k) :
    GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = _
  rw [coe_coe_diagSU]
  ext a b
  rw [blockMat_apply]
  by_cases hblk : (2 ≤ a.val ∧ a.val < 2 + k) ∧ (2 ≤ b.val ∧ b.val < 2 + k)
  · rw [dite_eq_left hblk]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, dite_eq_left hblk.1.1]
    · have hne : (⟨a.val - 2, by omega⟩ : Fin k) ≠ ⟨b.val - 2, by omega⟩ := by
        intro h'
        exact hab (Fin.ext (by have := congrArg Fin.val h'; simp at this; omega))
      rw [Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hab]
  · rw [dite_eq_right hblk]
    by_cases hab : a = b
    · subst hab
      have h1 : ¬ 2 ≤ a.val := fun h' => hblk ⟨⟨h', by omega⟩, h', by omega⟩
      rw [Matrix.one_apply_eq, Matrix.diagonal_apply_eq, dite_eq_right h1]
    · rw [Matrix.one_apply_ne hab, Matrix.diagonal_apply_ne _ hab]

end Tail

section Pattern

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem involution_pattern_standard (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {k : ℕ} (hk : 3 ≤ k) {Y : Type} [Group Y] (θ : Su K p f (k + 2) →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f (k + 2))) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hR : ∀ A : Su K p f 2, σ (θ (blockEmb K p f (k + 2) 2 0 (by omega) A)) =
      θ (blockEmb K p f (k + 2) 2 0 (by omega) A))
    (hT : ∀ t ∈ torus (unitaryInvolution K p f) k,
      σ (θ (blockEmb K p f (k + 2) k 2 (by omega) t)) =
        θ (blockEmb K p f (k + 2) k 2 (by omega) t)) :
    ∃ v : Fin (k + 2) → ZMod 2, v ⟨0, by omega⟩ = 0 ∧ v ⟨1, by omega⟩ = 0 ∧
      ∀ x : Su K p f (k + 2), σ (θ x) = θ (conjSign hK v x) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at hq
    · exact hf
  have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
  have := isPerfect_suTwo_of_card hK hq
  obtain ⟨α, g, φ, hlift, hmat, hiso, hφ, hsq⟩ :=
    unitaryAutClassification_ambient hK hp2 hq (by omega) θ hker σ hσ hstab
  set σ₀ : K ≃+* K := unitaryInvolution K p f with hσ₀
  set G : Matrix (Fin (k + 2)) (Fin (k + 2)) K := (g : Matrix (Fin (k + 2)) (Fin (k + 2)) K)
    with hG
  set Gi : Matrix (Fin (k + 2)) (Fin (k + 2)) K :=
    ((g⁻¹ : GL (Fin (k + 2)) K) : Matrix (Fin (k + 2)) (Fin (k + 2)) K) with hGi
  have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet : G.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det G).mp g.isUnit).ne_zero
  have hα0 : ∀ A : Su K p f 2, α (blockEmb K p f (k + 2) 2 0 (by omega) A) =
      blockEmb K p f (k + 2) 2 0 (by omega) A := fun A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed hker hlift
      (blockEmb K p f (k + 2) 2 0 (by omega)) hR) A
  obtain ⟨u, hu1, hu2⟩ := exists_normOne_ne h hp2
  set c : K := ((u : Kˣ) : K) with hc
  have hcσ : σ₀ c = c⁻¹ := by
    have := (mem_normOne _).1 u.2
    exact eq_inv_of_mul_eq_one_left this
  have hcinv : (((u : Kˣ)⁻¹ : Kˣ) : K) = c⁻¹ := Units.val_inv_eq_inv_val _
  have hc0 : c ≠ 0 := Units.ne_zero _
  set a : Fin (k + 1) := ⟨0, by omega⟩ with ha
  have hα0' : ∀ A : Su K p f 2, α (blockEmb2 K p f (k + 1) a A) = blockEmb2 K p f (k + 1) a A :=
    hα0
  have hrel0 : ∀ i j : Fin (k + 2),
      (if i.val = a.val then c else if i.val = a.val + 1 then c⁻¹ else 1) * G i j =
        G i j * φ (if j.val = a.val then c else if j.val = a.val + 1 then c⁻¹ else 1) := by
    intro i j
    have h1 := hmat (blockEmb2 K p f (k + 1) a (torusTwo σ₀ u))
    rw [hα0' (torusTwo σ₀ u), coe_coe_blockEmb2_torusTwo] at h1
    have h3 := diagonal_relation φ G Gi hGiG _ h1.symm i j
    simpa [hcinv] using h3
  have hu2' : c⁻¹ ≠ c := by rw [← hcinv]; exact hu2
  have hblk : ∀ i j : Fin (k + 2), G i j ≠ 0 → (i.val < 2 ↔ j.val < 2) := by
    intro i j hij
    have h3 := hrel0 i j
    rcases hφ with rfl | rfl
    · simp only [RingEquiv.refl_apply] at h3
      rcases torus_entry_cases_id a c hu1 hu2' i j (G i j) hij h3 with rfl | ⟨h4, h5, h6, h7⟩
      · exact Iff.rfl
      · simp only [ha] at h4 h5 h6 h7
        omega
    · rcases torus_entry_cases σ₀ a c hu1 hu2' hcσ i j (G i j) hij h3 with
        ⟨h4, h5⟩ | ⟨h4, h5⟩ | ⟨h4, h5, h6, h7⟩
      · simp only [ha] at h4 h5
        omega
      · simp only [ha] at h4 h5
        omega
      · simp only [ha] at h4 h5 h6 h7
        omega
  have htail : ∀ (d : Fin k → normOne σ₀) (hd : d ∈ detKer σ₀ k) (i j : Fin (k + 2)),
      (if h : 2 ≤ i.val then (((d ⟨i.val - 2, by omega⟩ : normOne σ₀) : Kˣ) : K) else 1) *
          G i j =
        G i j * φ (if h : 2 ≤ j.val then (((d ⟨j.val - 2, by omega⟩ : normOne σ₀) : Kˣ) : K)
          else 1) := by
    intro d hd i j
    obtain ⟨l, hl⟩ := lift_matrix_of_fixed hK (by omega) hker hlift
      (hT (diagSU σ₀ d hd) (diagSU_mem_torus d hd))
    have h1 := hmat (blockEmb K p f (k + 2) k 2 (by omega) (diagSU σ₀ d hd))
    have hX := coe_coe_blockEmb_tail_diagSU d hd
    obtain ⟨E, hE⟩ : ∃ E : Fin (k + 2) → K, E = fun i : Fin (k + 2) =>
        if h : 2 ≤ i.val then (((d ⟨i.val - 2, by omega⟩ : normOne σ₀) : Kˣ) : K) else 1 :=
      ⟨_, rfl⟩
    rw [← hE] at hX
    rw [hX] at h1
    have hl' : (((α (blockEmb K p f (k + 2) k 2 (by omega) (diagSU σ₀ d hd)) : Su K p f (k + 2)) :
        GL (Fin (k + 2)) K) : Matrix (Fin (k + 2)) (Fin (k + 2)) K) =
          (l : K) • diagonal E := by
      rw [← hX]
      exact hl
    rw [hl'] at h1
    have hmapX : φ.mapMatrix (diagonal E) = diagonal fun i => φ (E i) := by
      rw [RingEquiv.mapMatrix_apply, Matrix.diagonal_map (map_zero φ)]
    have hl1 : (l : K) = 1 := by
      have h4 := entry_conj_diag_eq_one G Gi hGGi (fun i => φ (E i)) ⟨0, by omega⟩
        (fun m hm => by
          have : m.val < 2 := (hblk ⟨0, by omega⟩ m hm).1 (by simp)
          have hE1 : E m = 1 := by rw [hE]; exact dite_eq_right (by omega)
          simp [hE1])
      have h5 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
      rw [hmapX, h4] at h5
      have hE0 : E ⟨0, by omega⟩ = 1 := by rw [hE]; exact dite_eq_right (fun h => by simp at h)
      rw [Matrix.smul_apply, Matrix.diagonal_apply_eq, hE0, smul_eq_mul, mul_one] at h5
      exact h5
    rw [hl1, one_smul] at h1
    have h6 := diagonal_relation φ G Gi hGiG E h1.symm i j
    rw [hE] at h6
    exact h6
  have hdet' : ∀ i' l' : Fin k, i' ≠ l' →
      (fun b : Fin k => if b = i' then u else if b = l' then u⁻¹ else 1 :
        Fin k → normOne σ₀) ∈ detKer σ₀ k := fun i' l' hil => by
    rw [mem_detKer, Finset.prod_eq_mul i' l' hil]
    · simp [hil.symm]
    · intro b _ hb
      simp [hb.1, hb.2]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  have htail' : ∀ (d : Fin k → normOne σ₀) (hd : d ∈ detKer σ₀ k) (i' j' : Fin k),
      (((d i' : normOne σ₀) : Kˣ) : K) * G ⟨i'.val + 2, by omega⟩ ⟨j'.val + 2, by omega⟩ =
        G ⟨i'.val + 2, by omega⟩ ⟨j'.val + 2, by omega⟩ *
          φ (((d j' : normOne σ₀) : Kˣ) : K) := by
    intro d hd i' j'
    have := htail d hd ⟨i'.val + 2, by omega⟩ ⟨j'.val + 2, by omega⟩
    simpa using this
  rcases hφ with rfl | rfl
  ·
    have hdiag : ∀ i j : Fin (k + 2), i ≠ j → G i j = 0 := by
      intro i j hij
      by_contra hne
      by_cases hi : i.val < 2
      · have h3 := hrel0 i j
        simp only [RingEquiv.refl_apply] at h3
        rcases torus_entry_cases_id a c hu1 hu2' i j (G i j) hne h3 with heq | ⟨h4, h5, h6, h7⟩
        · exact hij heq
        · have hj : j.val < 2 := (hblk i j hne).1 hi
          simp only [ha] at h4 h5 h6 h7
          omega
      · have hj : ¬ j.val < 2 := fun hj => hi ((hblk i j hne).2 hj)
        have hi2 : 2 ≤ i.val := by omega
        have hj2 : 2 ≤ j.val := by omega
        have hii : i = ⟨(⟨i.val - 2, by omega⟩ : Fin k).val + 2, by omega⟩ :=
          Fin.ext (by simp only; omega)
        have hjj : j = ⟨(⟨j.val - 2, by omega⟩ : Fin k).val + 2, by omega⟩ :=
          Fin.ext (by simp only; omega)
        have hne' : (⟨i.val - 2, by omega⟩ : Fin k) ≠ ⟨j.val - 2, by omega⟩ := by
          intro h'
          apply hij
          have := congrArg Fin.val h'
          simp only at this
          exact Fin.ext (by omega)
        obtain ⟨d, hd⟩ : ∃ d : Fin k → normOne σ₀, d = fun b =>
            if b = (⟨i.val - 2, by omega⟩ : Fin k) then u
            else if b = (⟨j.val - 2, by omega⟩ : Fin k) then u⁻¹ else 1 := ⟨_, rfl⟩
        have hdd : d ∈ detKer σ₀ k := hd ▸ hdet' _ _ hne'
        have h3 := htail' d hdd ⟨i.val - 2, by omega⟩ ⟨j.val - 2, by omega⟩
        rw [← hii, ← hjj] at h3
        have hdi : (((d ⟨i.val - 2, by omega⟩ : normOne σ₀) : Kˣ) : K) = c := by
          rw [hd]; simp [hc]
        have hdj : (((d ⟨j.val - 2, by omega⟩ : normOne σ₀) : Kˣ) : K) = c⁻¹ := by
          rw [hd]; simp [hne'.symm, hcinv]
        rw [hdi, hdj] at h3
        simp only [RingEquiv.refl_apply] at h3
        have h4 : (c - c⁻¹) * G i j = 0 := by linear_combination h3
        exact hne ((mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hu2'.symm))
    have hGd : G = diagonal fun i => G i i := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · rw [hdiag i j hij, Matrix.diagonal_apply_ne _ hij]
    have hd0 : ∀ i, G i i ≠ 0 := fun i => by
      have h5 := congrFun (congrFun hGGi i) i
      rw [hGd, Matrix.diagonal_mul, Matrix.one_apply_eq] at h5
      exact left_ne_zero_of_mul_eq_one h5
    have hGid : Gi = diagonal fun i => (G i i)⁻¹ := by
      have h5 : G * diagonal (fun i => (G i i)⁻¹) = 1 := by
        rw [hGd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        simp only [diagonal_apply_eq]
        exact mul_inv_cancel₀ (hd0 i)
      calc Gi = Gi * (G * diagonal fun i => (G i i)⁻¹) := by rw [h5, Matrix.mul_one]
        _ = (Gi * G) * diagonal fun i => (G i i)⁻¹ := by rw [Matrix.mul_assoc]
        _ = diagonal fun i => (G i i)⁻¹ := by rw [hGiG, Matrix.one_mul]
    have hconj : ∀ (M : Matrix (Fin (k + 2)) (Fin (k + 2)) K) (i j : Fin (k + 2)),
        (G * M * Gi) i j = G i i * M i j * (G j j)⁻¹ := fun M i j => by
      rw [hGid, hGd]
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
    have hW : G ⟨1, by omega⟩ ⟨1, by omega⟩ = G ⟨0, by omega⟩ ⟨0, by omega⟩ := by
      obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin (k + 2)) (Fin (k + 2)) K,
          X = (((blockEmb2 K p f (k + 1) a (weylElt K p f) : Su K p f (k + 2)) :
            GL (Fin (k + 2)) K) : Matrix (Fin (k + 2)) (Fin (k + 2)) K) := ⟨_, rfl⟩
      have h1 := hmat (blockEmb2 K p f (k + 1) a (weylElt K p f))
      rw [hα0' (weylElt K p f), ← hX] at h1
      have h2 : X * G = G * X := by
        have h5 : G * X = X * G := by
          have := congrArg (· * G) h1.symm
          simpa [RingEquiv.mapMatrix_apply, Matrix.mul_assoc, hGiG] using this
        exact h5.symm
      have h3 := congrFun (congrFun h2 ⟨0, by omega⟩) ⟨1, by omega⟩
      have hX01 : X ⟨0, by omega⟩ ⟨1, by omega⟩ = 1 := by
        rw [hX, coe_coe_blockEmb2_weylElt_row (k + 1) a ⟨0, by omega⟩ ⟨1, by omega⟩ rfl]
        simp [ha]
      rw [hGd] at h3
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, hX01, one_mul, mul_one] at h3
      exact h3
    obtain ⟨c₂, hc₂⟩ : ∃ c₂ : K,
        G * G = c₂ • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) K) := by
      refine eq_smul_one_of_commute h hp2 (by omega) (G * G) fun y hy => ?_
      have hy' : y ∈ SUid σ₀ (k + 2) := by rw [SUid_eq_statedSU hK]; exact hy
      have h1 := DFunLike.congr_fun hsq ⟨y, hy'⟩
      have h2 := congrArg (fun x : Su K p f (k + 2) =>
        ((x : GL (Fin (k + 2)) K) : Matrix (Fin (k + 2)) (Fin (k + 2)) K)) h1
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at h2
      rw [hmat (α ⟨y, hy'⟩), hmat ⟨y, hy'⟩] at h2
      have h3 := commute_of_double_conj (RingEquiv.refl K) (fun _ => rfl) G Gi
        (y : Matrix (Fin (k + 2)) (Fin (k + 2)) K) hGiG h2.symm
      simpa [RingEquiv.mapMatrix_apply] using h3
    have hsqd : ∀ i, G i i * G i i = c₂ := fun i => by
      have := congrFun (congrFun hc₂ i) i
      rw [hGd, Matrix.diagonal_mul_diagonal] at this
      simpa using this
    classical
    obtain ⟨v, hv⟩ : ∃ v : Fin (k + 2) → ZMod 2,
        v = fun i => if G i i = G ⟨0, by omega⟩ ⟨0, by omega⟩ then 0 else 1 := ⟨_, rfl⟩
    have hvG : ∀ i, G i i = G ⟨0, by omega⟩ ⟨0, by omega⟩ * signVal K (v i) := fun i => by
      by_cases hi : G i i = G ⟨0, by omega⟩ ⟨0, by omega⟩
      · simp [hv, hi, signVal]
      · have hsq' : G i i * G i i =
            G ⟨0, by omega⟩ ⟨0, by omega⟩ * G ⟨0, by omega⟩ ⟨0, by omega⟩ := by
          rw [hsqd i, hsqd ⟨0, by omega⟩]
        rcases mul_self_eq_mul_self_iff.mp hsq' with h' | h'
        · exact absurd h' hi
        · simp [hv, signVal, h']
    have hv0 : v ⟨0, by omega⟩ = 0 := by simp [hv]
    have hv1 : v ⟨1, by omega⟩ = 0 := by
      rw [hv]
      exact ite_eq_left hW
    refine ⟨v, hv0, hv1, fun x => ?_⟩
    have hαx : α x = conjSign hK v x := by
      refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
      rw [coe_coe_conjSign_apply]
      have hrefl : ∀ M : Matrix (Fin (k + 2)) (Fin (k + 2)) K,
          (RingEquiv.refl K).mapMatrix M = M := fun M => by ext a b; rfl
      have hs : (signVal K (v j))⁻¹ = signVal K (v j) :=
        inv_eq_of_mul_eq_one_right (signVal_mul_self _)
      rw [hmat x, hrefl, hconj, hvG i, hvG j, mul_inv, hs]
      have hG0 := hd0 ⟨0, by omega⟩
      field_simp
    rw [← hlift x, hαx]
  ·
    exfalso
    obtain ⟨j, hj⟩ : ∃ j : Fin (k + 2), G ⟨2, by omega⟩ j ≠ 0 := by
      by_contra hno
      push Not at hno
      exact hdet (Matrix.det_eq_zero_of_row_eq_zero ⟨2, by omega⟩ hno)
    have hj2 : 2 ≤ j.val := by
      by_contra hlt
      have := (hblk ⟨2, by omega⟩ j hj).2 (by omega)
      simp at this
    have hjj : j = ⟨(⟨j.val - 2, by omega⟩ : Fin k).val + 2, by omega⟩ :=
      Fin.ext (by simp only; omega)
    obtain ⟨l', hl1, hl2⟩ := exists_fin_ne_ne hk (⟨0, by omega⟩ : Fin k) ⟨j.val - 2, by omega⟩
    obtain ⟨d, hd⟩ : ∃ d : Fin k → normOne σ₀, d = fun b => if b = (⟨0, by omega⟩ : Fin k) then u
        else if b = l' then u⁻¹ else 1 := ⟨_, rfl⟩
    have hdd : d ∈ detKer σ₀ k := hd ▸ hdet' ⟨0, by omega⟩ l' (Ne.symm hl1)
    have h3 := htail' d hdd ⟨0, by omega⟩ ⟨j.val - 2, by omega⟩
    rw [← hjj] at h3
    have hd0 : (((d ⟨0, by omega⟩ : normOne σ₀) : Kˣ) : K) = c := by rw [hd]; simp [hc]
    rw [hd0] at h3
    have hx : G ⟨0 + 2, by omega⟩ j ≠ 0 := hj
    by_cases hjj0 : (⟨j.val - 2, by omega⟩ : Fin k) = ⟨0, by omega⟩
    · have hdj : (((d ⟨j.val - 2, by omega⟩ : normOne σ₀) : Kˣ) : K) = c := by
        rw [hd, hjj0]; simp [hc]
      rw [hdj, hcσ] at h3
      exact hu2' (mul_right_cancel₀ hx (by rw [mul_comm c⁻¹]; exact h3.symm))
    · have hdj : (((d ⟨j.val - 2, by omega⟩ : normOne σ₀) : Kˣ) : K) = 1 := by
        rw [hd]; simp [hjj0, hl2.symm]
      rw [hdj, map_one] at h3
      exact hu1 (mul_right_cancel₀ hx (by rw [h3, mul_one, one_mul]))

end Pattern

section Roots

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] def charOfU {n : ℕ} (v : Fin n → ZMod 2) (T : Pair n) : ZMod 2 := ∑ i ∈ T.1, v i

theorem charOfU_eq_zero_iff {n : ℕ} (v : Fin n → ZMod 2) {T : Pair n} {i j : Fin n} (hij : i ≠ j)
    (hT : T.1 = {i, j}) : charOfU v T = 0 ↔ v i = v j := by
  unfold charOfU
  rw [hT, Finset.sum_pair hij]
  have hb : ∀ b : ZMod 2, b + b = 0 := by decide
  constructor
  · intro h
    have h1 : v i = -v j := eq_neg_of_add_eq_zero_left h
    rw [h1]
    have : ∀ b : ZMod 2, -b = b := by decide
    exact this _
  · intro h
    rw [h]
    exact hb _

theorem conjSign_conjSign (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (v : Fin n → ZMod 2)
    (x : Su K p f n) : conjSign hK v (conjSign hK v x) = x := by
  refine Subtype.ext (Units.ext (Matrix.ext fun a b => ?_))
  rw [coe_coe_conjSign_apply, coe_coe_conjSign_apply]
  linear_combination (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b * signVal K (v b) *
      signVal K (v b)) * signVal_mul_self (K := K) (v a) +
    ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b * signVal_mul_self (K := K) (v b)

theorem zEltU_not_mem_center (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0) {n : ℕ}
    (hn : 3 ≤ n) (T : Pair n) : zEltU K p f T ∉ Subgroup.center (Su K p f n) := by
  intro hz
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK) hn hz
  have hcard := T.2
  obtain ⟨i, hi⟩ : ∃ i, i ∈ T.1 := Finset.card_pos.mp (by omega)
  obtain ⟨r, hr⟩ : ∃ r, r ∉ T.1 := by
    by_contra hall
    push Not at hall
    have : T.1 = Finset.univ := Finset.eq_univ_of_forall hall
    rw [this, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  have e1 : zMat K n T.1 i i = (u : K) := by
    have := congrFun (congrFun hu i) i
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
    exact this
  have e2 : zMat K n T.1 r r = (u : K) := by
    have := congrFun (congrFun hu r) r
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
    exact this
  rw [zMat_apply_self, ite_eq_left hi] at e1
  rw [zMat_apply_self, ite_eq_right hr] at e2
  exact h2 (by linear_combination e2 - e1)

theorem root_pattern (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hn : 3 ≤ n) {Y : Type} [Group Y] (θ : Su K p f n →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f n)) (σ : Y ≃* Y) (v : Fin n → ZMod 2)
    (hv : ∀ x, σ (θ x) = θ (conjSign hK v x)) (T : Pair n) :
    ((LcU K p f T).map θ).map σ.toMonoidHom = (LcU K p f T).map θ ∧
      ((∀ x ∈ LcU K p f T, σ (θ x) = θ x) ↔ charOfU v T = 0) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at hq
    · exact hf
  have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
  refine ⟨?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨conjSign hK v x, conjSign_mem_LcU hK v hx, (hv x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨θ (conjSign hK v x), ⟨conjSign hK v x, conjSign_mem_LcU hK v hx, rfl⟩, ?_⟩
      change σ (θ (conjSign hK v x)) = θ x
      rw [hv, conjSign_conjSign]
  · obtain ⟨i, j, hij, hT⟩ := Finset.card_eq_two.mp T.2
    rw [charOfU_eq_zero_iff v hij hT]
    constructor
    · intro hfix
      by_contra hne
      obtain ⟨x, hxL, hxc⟩ := exists_swap_mem_LcU hK h hij hT
      have h1 := hfix x hxL
      rw [hv, hxc v hne, map_mul] at h1
      have h3 : θ (zEltU K p f T) = 1 :=
        mul_right_cancel (h1.trans (one_mul (θ x)).symm)
      exact zEltU_not_mem_center hK h2 hn T (hker (MonoidHom.mem_ker.mpr h3))
    · intro hvij x hx
      have hconst : ∀ a ∈ T.1, ∀ b ∈ T.1, v a = v b := by
        intro a ha b hb
        rw [hT] at ha hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
        · exact hvij
        · exact hvij.symm
      rw [hv, conjSign_eq_of_const hK h2 v hconst hx]

end Roots

section Main

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem unitary_involution_pattern (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {k : ℕ} (hk : 3 ≤ k) {Y : Type} [Group Y] (θ : Su K p f (k + 2) →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f (k + 2))) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range) (k₀ : Su K p f (k + 2))
    (hR : ∀ A : Su K p f 2,
      σ (θ (k₀ * blockEmb K p f (k + 2) 2 0 (by omega) A * k₀⁻¹)) =
        θ (k₀ * blockEmb K p f (k + 2) 2 0 (by omega) A * k₀⁻¹))
    (hT : ∀ t ∈ torus (unitaryInvolution K p f) k,
      σ (θ (k₀ * blockEmb K p f (k + 2) k 2 (by omega) t * k₀⁻¹)) =
        θ (k₀ * blockEmb K p f (k + 2) k 2 (by omega) t * k₀⁻¹)) :
    ∃ v : Fin (k + 2) → ZMod 2, v ⟨0, by omega⟩ = 0 ∧ v ⟨1, by omega⟩ = 0 ∧
      (∀ x : Su K p f (k + 2), σ (θ (k₀ * x * k₀⁻¹)) = θ (k₀ * conjSign hK v x * k₀⁻¹)) ∧
      ∀ T : Pair (k + 2),
        (((LcU K p f T).map (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          ((LcU K p f T).map (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ x ∈ (LcU K p f T).map (MulAut.conj k₀).toMonoidHom, σ (θ x) = θ x) ↔
          charOfU v T = 0) := by
  set θ₀ : Su K p f (k + 2) →* Y := θ.comp (MulAut.conj k₀).toMonoidHom with hθ₀
  have hθ₀x : ∀ x, θ₀ x = θ (k₀ * x * k₀⁻¹) := fun x => rfl
  have hker₀ : θ₀.ker ≤ Subgroup.center (Su K p f (k + 2)) := by
    intro x hx
    have h1 : k₀ * x * k₀⁻¹ ∈ Subgroup.center (Su K p f (k + 2)) :=
      hker (MonoidHom.mem_ker.mpr (by rw [← hθ₀x]; exact MonoidHom.mem_ker.mp hx))
    have h2 := Subgroup.Normal.conj_mem inferInstance _ h1 k₀⁻¹
    simpa [mul_assoc] using h2
  have hstab₀ : ∀ x, σ (θ₀ x) ∈ θ₀.range := fun x => by
    obtain ⟨z, hz⟩ := hstab (k₀ * x * k₀⁻¹)
    refine ⟨k₀⁻¹ * z * k₀, ?_⟩
    change θ (k₀ * (k₀⁻¹ * z * k₀) * k₀⁻¹) = σ (θ (k₀ * x * k₀⁻¹))
    rw [← hz]
    congr 1
    group
  obtain ⟨v, hv0, hv1, hv⟩ :=
    involution_pattern_standard hK hp2 hq hk θ₀ hker₀ σ hσ hstab₀ hR hT
  refine ⟨v, hv0, hv1, hv, fun T => ?_⟩
  obtain ⟨h3, h4⟩ := root_pattern hK hp2 hq (by omega) θ₀ hker₀ σ v hv T
  have hmap : ((LcU K p f T).map (MulAut.conj k₀).toMonoidHom).map θ = (LcU K p f T).map θ₀ :=
    Subgroup.map_map _ _ _
  rw [hmap]
  refine ⟨h3, ?_⟩
  rw [← h4]
  constructor
  · intro hfix x hx
    exact hfix _ ⟨x, hx, rfl⟩
  · intro hfix y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hfix x hx

theorem unitary_involution_inner (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {k : ℕ} (hk : 3 ≤ k) {Y : Type} [Group Y] (θ : Su K p f (k + 2) →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f (k + 2))) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range) (k₀ : Su K p f (k + 2))
    (hR : ∀ A : Su K p f 2,
      σ (θ (k₀ * blockEmb K p f (k + 2) 2 0 (by omega) A * k₀⁻¹)) =
        θ (k₀ * blockEmb K p f (k + 2) 2 0 (by omega) A * k₀⁻¹))
    (hT : ∀ t ∈ torus (unitaryInvolution K p f) k,
      σ (θ (k₀ * blockEmb K p f (k + 2) k 2 (by omega) t * k₀⁻¹)) =
        θ (k₀ * blockEmb K p f (k + 2) k 2 (by omega) t * k₀⁻¹)) :
    ∃ (g : GL (Fin (k + 2)) K) (hg : ∀ x : Su K p f (k + 2),
        g * (x : GL (Fin (k + 2)) K) * g⁻¹ ∈ SUid (unitaryInvolution K p f) (k + 2)),
      ∀ x, σ (θ x) = θ ⟨g * (x : GL (Fin (k + 2)) K) * g⁻¹, hg x⟩ := by
  obtain ⟨v, -, -, hv, -⟩ := unitary_involution_pattern hK hp2 hq hk θ hker σ hσ hstab k₀ hR hT
  set D : GL (Fin (k + 2)) K :=
    diagGL fun i => ((signN (v i) : normOne (unitaryInvolution K p f)) : Kˣ) with hD
  have hg : ∀ x : Su K p f (k + 2), (k₀ : GL (Fin (k + 2)) K) * D * (k₀ : GL (Fin (k + 2)) K)⁻¹ *
      (x : GL (Fin (k + 2)) K) * ((k₀ : GL (Fin (k + 2)) K) * D * (k₀ : GL (Fin (k + 2)) K)⁻¹)⁻¹ =
        ((k₀ * conjSign hK v (k₀⁻¹ * x * k₀) * k₀⁻¹ : Su K p f (k + 2)) : GL (Fin (k + 2)) K) :=
    fun x => by
      have : ((conjSign hK v (k₀⁻¹ * x * k₀) : Su K p f (k + 2)) : GL (Fin (k + 2)) K) =
          D * ((k₀⁻¹ * x * k₀ : Su K p f (k + 2)) : GL (Fin (k + 2)) K) * D⁻¹ := rfl
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, this]
      group
  refine ⟨(k₀ : GL (Fin (k + 2)) K) * D * (k₀ : GL (Fin (k + 2)) K)⁻¹,
    fun x => by rw [hg x]; exact (k₀ * conjSign hK v (k₀⁻¹ * x * k₀) * k₀⁻¹).2, fun x => ?_⟩
  have h1 := hv (k₀⁻¹ * x * k₀)
  have h2 : k₀ * (k₀⁻¹ * x * k₀) * k₀⁻¹ = x := by group
  rw [h2] at h1
  rw [h1]
  exact congrArg θ (Subtype.ext (hg x)).symm

theorem unitary_involution_pattern_of_surjective (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {k : ℕ} (hk : 3 ≤ k) {X : Type} [Group X] (θ : Su K p f (k + 2) →* X)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center (Su K p f (k + 2)))
    (σ : X ≃* X) (hσ : ∀ y, σ (σ y) = y) (k₀ : Su K p f (k + 2))
    (hR : ∀ A : Su K p f 2,
      σ (θ (k₀ * blockEmb K p f (k + 2) 2 0 (by omega) A * k₀⁻¹)) =
        θ (k₀ * blockEmb K p f (k + 2) 2 0 (by omega) A * k₀⁻¹))
    (hT : ∀ t ∈ torus (unitaryInvolution K p f) k,
      σ (θ (k₀ * blockEmb K p f (k + 2) k 2 (by omega) t * k₀⁻¹)) =
        θ (k₀ * blockEmb K p f (k + 2) k 2 (by omega) t * k₀⁻¹)) :
    ∃ v : Fin (k + 2) → ZMod 2, v ⟨0, by omega⟩ = 0 ∧ v ⟨1, by omega⟩ = 0 ∧
      (∀ x : Su K p f (k + 2), σ (θ (k₀ * x * k₀⁻¹)) = θ (k₀ * conjSign hK v x * k₀⁻¹)) ∧
      ∀ T : Pair (k + 2),
        (((LcU K p f T).map (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          ((LcU K p f T).map (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ x ∈ (LcU K p f T).map (MulAut.conj k₀).toMonoidHom, σ (θ x) = θ x) ↔
          charOfU v T = 0) :=
  unitary_involution_pattern hK hp2 hq hk θ hker σ hσ (fun x => hθ (σ (θ x))) k₀ hR hT

theorem unitary_involution_pattern_of_longRoot (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {k : ℕ} (hk : 3 ≤ k) {Y : Type} [Group Y] (θ : Su K p f (k + 2) →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f (k + 2))) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range) {R_M T' : Subgroup (Su K p f (k + 2))}
    (hk₀ : ∃ k₀ : Su K p f (k + 2),
      R_M = (rootSU2 K p f (by omega : 2 ≤ k + 2)).map (MulAut.conj k₀).toMonoidHom ∧
      T' = ((torus (unitaryInvolution K p f) k).map
        (blockEmb K p f (k + 2) k 2 (by omega))).map (MulAut.conj k₀).toMonoidHom)
    (hR : ∀ x ∈ R_M, σ (θ x) = θ x) (hT : ∀ x ∈ T', σ (θ x) = θ x) :
    ∃ (k₀ : Su K p f (k + 2)) (v : Fin (k + 2) → ZMod 2),
      R_M = (rootSU2 K p f (by omega : 2 ≤ k + 2)).map (MulAut.conj k₀).toMonoidHom ∧
      v ⟨0, by omega⟩ = 0 ∧ v ⟨1, by omega⟩ = 0 ∧
      (∀ x : Su K p f (k + 2), σ (θ (k₀ * x * k₀⁻¹)) = θ (k₀ * conjSign hK v x * k₀⁻¹)) ∧
      ∀ T : Pair (k + 2),
        (((LcU K p f T).map (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          ((LcU K p f T).map (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ x ∈ (LcU K p f T).map (MulAut.conj k₀).toMonoidHom, σ (θ x) = θ x) ↔
          charOfU v T = 0) := by
  obtain ⟨k₀, hRk, hTk⟩ := hk₀
  obtain ⟨v, hv0, hv1, hv, hroots⟩ := unitary_involution_pattern hK hp2 hq hk θ hker σ hσ hstab k₀
    (fun A => hR _ (by
      rw [hRk]
      exact ⟨blockEmb K p f (k + 2) 2 0 (by omega) A, ⟨A, rfl⟩, rfl⟩))
    (fun t ht => hT _ (by
      rw [hTk]
      exact ⟨blockEmb K p f (k + 2) k 2 (by omega) t, ⟨t, ht, rfl⟩, rfl⟩))
  exact ⟨k₀, v, hRk, hv0, hv1, hv, hroots⟩

end Main

end CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
