module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Frame
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Basic

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.L52

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement

variable {K : Type} [Field K]

section Q2

variable (K)

theorem blockLeft_q2a : BlockLeft (flagStabilizer 5 K {2, 3}) 0 2 := blockLeft_zero _ 2

theorem blockRight_q2a : BlockRight (flagStabilizer 5 K {2, 3}) 0 2 :=
  blockRight_of_cut (Or.inr (by simp))

theorem blockLeft_q2c : BlockLeft (flagStabilizer 5 K {2, 3}) 3 2 :=
  blockLeft_of_cut 2 (Or.inr (by simp))

theorem blockRight_q2c : BlockRight (flagStabilizer 5 K {2, 3}) 3 2 :=
  blockRight_top _ (by norm_num)

theorem blockLeft_q2b : BlockLeft (flagStabilizer 5 K {2, 3}) 2 1 :=
  blockLeft_of_cut 1 (Or.inr (by simp))

theorem blockRight_q2b : BlockRight (flagStabilizer 5 K {2, 3}) 2 1 :=
  blockRight_of_cut (Or.inr (by simp))

@[expose] noncomputable def R2 : Subgroup (SpecialLinearGroup (Fin 5) K) :=
  ((blkMon (flagStabilizer 5 K {2, 3}) 0 2 (by norm_num) (blockLeft_q2a K) (blockRight_q2a K)).ker ⊓
    (blkMon (flagStabilizer 5 K {2, 3}) 3 2 (by norm_num) (blockLeft_q2c K)
      (blockRight_q2c K)).ker).map (flagStabilizer 5 K {2, 3}).subtype

variable {K}

theorem mem_R2_iff {x : SpecialLinearGroup (Fin 5) K} :
    x ∈ R2 K ↔ ∃ _ : x ∈ flagStabilizer 5 K {2, 3},
      blkAt 0 2 (by norm_num) (x : Matrix (Fin 5) (Fin 5) K) = 1 ∧
        blkAt 3 2 (by norm_num) (x : Matrix (Fin 5) (Fin 5) K) = 1 := by
  constructor
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    exact ⟨y.2, h1, h2⟩
  · rintro ⟨hx, h1, h2⟩
    exact ⟨⟨x, hx⟩, ⟨h1, h2⟩, rfl⟩

theorem R2_le_q2 : R2 K ≤ flagStabilizer 5 K {2, 3} := fun _ hx => (mem_R2_iff.1 hx).1

theorem conj_mem_R2 {g x : SpecialLinearGroup (Fin 5) K} (hg : g ∈ flagStabilizer 5 K {2, 3})
    (hx : x ∈ R2 K) : g * x * g⁻¹ ∈ R2 K := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' := Subgroup.mem_inf.1 hy
  refine ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, Subgroup.mem_inf.2 ⟨?_, ?_⟩, rfl⟩
  · rw [MonoidHom.mem_ker, map_mul, map_mul, MonoidHom.mem_ker.1 hy'.1, mul_one, ← map_mul,
      mul_inv_cancel, map_one]
  · rw [MonoidHom.mem_ker, map_mul, map_mul, MonoidHom.mem_ker.1 hy'.2, mul_one, ← map_mul,
      mul_inv_cancel, map_one]

theorem q2_le_normalizer_R2 :
    flagStabilizer 5 K {2, 3} ≤ Subgroup.normalizer (R2 K : Set (SpecialLinearGroup (Fin 5) K)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_R2 hg hx, fun hx => ?_⟩
  have := conj_mem_R2 ((flagStabilizer 5 K {2, 3}).inv_mem hg) hx
  simpa [mul_assoc] using this

theorem maxBlock_cases {a m : ℕ} (ha : a = 0 ∨ a ∈ ({2, 3} : Set ℕ))
    (hb : a + m = 5 ∨ a + m ∈ ({2, 3} : Set ℕ)) (hno : ∀ c ∈ ({2, 3} : Set ℕ), ¬ (a < c ∧ c < a + m)) :
    m = 0 ∨ (a = 0 ∧ m = 2) ∨ (a = 2 ∧ m = 1) ∨ (a = 3 ∧ m = 2) := by
  have h2 := hno 2 (by simp)
  have h3 := hno 3 (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  omega

theorem transvection_mem_R2 {i j : Fin 5} (hij : i < j) (hA : ¬ ((i : ℕ) < 2 ∧ (j : ℕ) < 2))
    (hC : ¬ (3 ≤ (i : ℕ) ∧ 3 ≤ (j : ℕ))) (c : K) :
    SpecialLinearGroup.transvection hij.ne c ∈ R2 K :=
  mem_R2_iff.2 ⟨transvection_mem_flagStabilizer hij c _,
    blkAt_transvection hij.ne c 0 2 (by norm_num) (by omega),
    blkAt_transvection hij.ne c 3 2 (by norm_num) (by omega)⟩

variable [Finite K]

theorem R2_unitriangular (hK : Nat.card K = 2) {x : SpecialLinearGroup (Fin 5) K} (hx : x ∈ R2 K) :
    x ∈ unitriangular 5 K := by
  obtain ⟨hxQ, h1, h2⟩ := mem_R2_iff.1 hx
  refine mem_unitriangular_of_blocks hxQ ?_
  intro a m h ha hb hno
  rcases maxBlock_cases ha hb hno with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact blkAt_zero a h _
  · exact h1
  · exact blkAt_one_eq_one hK _ 2 h (blockLeft_q2b K) (blockRight_q2b K) ⟨x, hxQ⟩
  · exact h2

theorem R2_isPGroup [CharP K 2] (hK : Nat.card K = 2) : IsPGroup 2 (R2 K) :=
  (isPGroup_unitriangular_charTwo (K := K) (by norm_num : 1 ≤ 5)).to_le
    (fun _ hx => R2_unitriangular hK hx)

theorem q2_x22 (hK : Nat.card K = 2) {x : SpecialLinearGroup (Fin 5) K}
    (hx : x ∈ flagStabilizer 5 K {2, 3}) : (x : Matrix (Fin 5) (Fin 5) K) 2 2 = 1 :=
  congrFun (congrFun (blkAt_one_eq_one hK _ 2 (by norm_num) (blockLeft_q2b K) (blockRight_q2b K)
    ⟨x, hx⟩) 0) 0

omit [Finite K] in
theorem q2_lower {x : SpecialLinearGroup (Fin 5) K} (hx : x ∈ flagStabilizer 5 K {2, 3}) :
    (x : Matrix (Fin 5) (Fin 5) K) 2 0 = 0 ∧ (x : Matrix (Fin 5) (Fin 5) K) 2 1 = 0 ∧
      (x : Matrix (Fin 5) (Fin 5) K) 3 0 = 0 ∧ (x : Matrix (Fin 5) (Fin 5) K) 3 1 = 0 ∧
      (x : Matrix (Fin 5) (Fin 5) K) 3 2 = 0 ∧ (x : Matrix (Fin 5) (Fin 5) K) 4 0 = 0 ∧
      (x : Matrix (Fin 5) (Fin 5) K) 4 1 = 0 ∧ (x : Matrix (Fin 5) (Fin 5) K) 4 2 = 0 := by
  have h2 := mem_flagStabilizer.1 hx 2 (by simp)
  have h3 := mem_flagStabilizer.1 hx 3 (by simp)
  exact ⟨stabilizer_entries h2 (by decide) (by decide), stabilizer_entries h2 (by decide) (by decide),
    stabilizer_entries h3 (by decide) (by decide), stabilizer_entries h3 (by decide) (by decide),
    stabilizer_entries h3 (by decide) (by decide), stabilizer_entries h3 (by decide) (by decide),
    stabilizer_entries h3 (by decide) (by decide), stabilizer_entries h3 (by decide) (by decide)⟩

omit [Finite K] in
theorem tce_diag {n : ℕ} {x : SpecialLinearGroup (Fin n) K} {i j : Fin n} {hij : i ≠ j}
    (h : x * SpecialLinearGroup.transvection hij (1 : K) =
      SpecialLinearGroup.transvection hij (1 : K) * x) :
    (x : Matrix (Fin n) (Fin n) K) i i = (x : Matrix (Fin n) (Fin n) K) j j := by
  have := transvection_commute_entry hij (1 : K) h i j
  simpa using this

omit [Finite K] in
theorem tce_col {n : ℕ} {x : SpecialLinearGroup (Fin n) K} {i j : Fin n} {hij : i ≠ j}
    (h : x * SpecialLinearGroup.transvection hij (1 : K) =
      SpecialLinearGroup.transvection hij (1 : K) * x) {a : Fin n} (ha : i ≠ a) :
    (x : Matrix (Fin n) (Fin n) K) a i = 0 := by
  have := transvection_commute_entry hij (1 : K) h a j
  simpa [ha] using this

omit [Finite K] in
theorem tce_row {n : ℕ} {x : SpecialLinearGroup (Fin n) K} {i j : Fin n} {hij : i ≠ j}
    (h : x * SpecialLinearGroup.transvection hij (1 : K) =
      SpecialLinearGroup.transvection hij (1 : K) * x) {b : Fin n} (hb : j ≠ b) :
    (x : Matrix (Fin n) (Fin n) K) j b = 0 := by
  have := transvection_commute_entry hij (1 : K) h i b
  simpa [hb] using this.symm

omit [Finite K] in
theorem q2_cent {x : SpecialLinearGroup (Fin 5) K} (hc : ∀ r ∈ R2 K, r * x = x * r) :
    (x : Matrix (Fin 5) (Fin 5) K) 0 0 = (x : Matrix (Fin 5) (Fin 5) K) 2 2 ∧
      (x : Matrix (Fin 5) (Fin 5) K) 1 0 = 0 ∧ (x : Matrix (Fin 5) (Fin 5) K) 0 1 = 0 ∧
      (x : Matrix (Fin 5) (Fin 5) K) 1 1 = (x : Matrix (Fin 5) (Fin 5) K) 2 2 ∧
      (x : Matrix (Fin 5) (Fin 5) K) 3 3 = (x : Matrix (Fin 5) (Fin 5) K) 2 2 ∧
      (x : Matrix (Fin 5) (Fin 5) K) 3 4 = 0 ∧ (x : Matrix (Fin 5) (Fin 5) K) 4 3 = 0 ∧
      (x : Matrix (Fin 5) (Fin 5) K) 4 4 = (x : Matrix (Fin 5) (Fin 5) K) 2 2 ∧
      (x : Matrix (Fin 5) (Fin 5) K) 0 2 = 0 ∧ (x : Matrix (Fin 5) (Fin 5) K) 1 2 = 0 ∧
      (x : Matrix (Fin 5) (Fin 5) K) 2 3 = 0 ∧ (x : Matrix (Fin 5) (Fin 5) K) 2 4 = 0 := by
  have t02 := (hc _ (transvection_mem_R2 (K := K) (i := 0) (j := 2) (by decide) (by decide)
    (by decide) 1)).symm
  have t12 := (hc _ (transvection_mem_R2 (K := K) (i := 1) (j := 2) (by decide) (by decide)
    (by decide) 1)).symm
  have t23 := (hc _ (transvection_mem_R2 (K := K) (i := 2) (j := 3) (by decide) (by decide)
    (by decide) 1)).symm
  have t24 := (hc _ (transvection_mem_R2 (K := K) (i := 2) (j := 4) (by decide) (by decide)
    (by decide) 1)).symm
  exact ⟨tce_diag t02, tce_col t02 (a := 1) (by decide), tce_col t12 (a := 0) (by decide),
    tce_diag t12, (tce_diag t23).symm, tce_row t23 (b := 4) (by decide),
    tce_row t24 (b := 3) (by decide), (tce_diag t24).symm,
    tce_col t23 (a := 0) (by decide), tce_col t23 (a := 1) (by decide),
    tce_row t02 (b := 3) (by decide), tce_row t12 (b := 4) (by decide)⟩

omit [Finite K] in
theorem corner_prod (c₁ c₂ c₃ c₄ : K) :
    (1 + single (0 : Fin 5) (3 : Fin 5) c₁) * ((1 + single (0 : Fin 5) (4 : Fin 5) c₂) *
      ((1 + single (1 : Fin 5) (3 : Fin 5) c₃) * (1 + single (1 : Fin 5) (4 : Fin 5) c₄))) =
      1 + single (0 : Fin 5) (3 : Fin 5) c₁ + single (0 : Fin 5) (4 : Fin 5) c₂ +
        single (1 : Fin 5) (3 : Fin 5) c₃ + single (1 : Fin 5) (4 : Fin 5) c₄ := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
  simp

theorem entries_of_center (hK : Nat.card K = 2) {x : SpecialLinearGroup (Fin 5) K}
    (hxQ : x ∈ flagStabilizer 5 K {2, 3}) (hc : ∀ r ∈ R2 K, r * x = x * r) :
    (x : Matrix (Fin 5) (Fin 5) K) =
      1 + single (0 : Fin 5) (3 : Fin 5) ((x : Matrix (Fin 5) (Fin 5) K) 0 3) +
      single (0 : Fin 5) (4 : Fin 5) ((x : Matrix (Fin 5) (Fin 5) K) 0 4) +
      single (1 : Fin 5) (3 : Fin 5) ((x : Matrix (Fin 5) (Fin 5) K) 1 3) +
      single (1 : Fin 5) (4 : Fin 5) ((x : Matrix (Fin 5) (Fin 5) K) 1 4) := by
  obtain ⟨l20, l21, l30, l31, l32, l40, l41, l42⟩ := q2_lower hxQ
  obtain ⟨c00, c10, c01, c11, c33, c34, c43, c44, c02, c12, c23, c24⟩ := q2_cent hc
  have x22 := q2_x22 hK hxQ
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [l20, l21, l30, l31, l32, l40, l41, l42, c00, c10, c01, c11, c33, c34, c43, c44, c02,
      c12, c23, c24, x22]

theorem center_eq_prod (hK : Nat.card K = 2) {x : SpecialLinearGroup (Fin 5) K}
    (hxQ : x ∈ flagStabilizer 5 K {2, 3}) (hc : ∀ r ∈ R2 K, r * x = x * r) :
    x = SpecialLinearGroup.transvection (show (0 : Fin 5) < 3 by decide).ne
          ((x : Matrix (Fin 5) (Fin 5) K) 0 3) *
        (SpecialLinearGroup.transvection (show (0 : Fin 5) < 4 by decide).ne
            ((x : Matrix (Fin 5) (Fin 5) K) 0 4) *
          (SpecialLinearGroup.transvection (show (1 : Fin 5) < 3 by decide).ne
              ((x : Matrix (Fin 5) (Fin 5) K) 1 3) *
            SpecialLinearGroup.transvection (show (1 : Fin 5) < 4 by decide).ne
              ((x : Matrix (Fin 5) (Fin 5) K) 1 4))) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe, corner_prod]
  exact entries_of_center hK hxQ hc

omit [Finite K] in
theorem corner_mem_commutator {i j : Fin 5} (hi : (i : ℕ) < 2) (hj : 3 ≤ (j : ℕ)) (c : K) :
    SpecialLinearGroup.transvection (show i ≠ j from fun h => by subst h; omega) c ∈
      ⁅R2 K, R2 K⁆ := by
  have hi2 : i < (2 : Fin 5) := by
    rw [Fin.lt_def]
    simpa using hi
  have h2j : (2 : Fin 5) < j := by
    rw [Fin.lt_def]
    simpa using (show 2 < (j : ℕ) by omega)
  have hij : i < j := hi2.trans h2j
  have h1 := Subgroup.commutator_mem_commutator
    (transvection_mem_R2 (K := K) hi2 (by simp) (by simp) c)
    (transvection_mem_R2 (K := K) h2j (by simp) (by simp) 1)
  rw [Matrix.SpecialLinearGroup.commutatorElement_transvection hi2.ne h2j.ne hij.ne, mul_one]
    at h1
  exact h1

theorem q2_center_le (hK : Nat.card K = 2) :
    R2 K ⊓ Subgroup.centralizer (R2 K : Set (SpecialLinearGroup (Fin 5) K)) ≤ ⁅R2 K, R2 K⁆ := by
  rintro x ⟨hx, hxc⟩
  have hc : ∀ r ∈ R2 K, r * x = x * r := Subgroup.mem_centralizer_iff.1 hxc
  rw [center_eq_prod hK (R2_le_q2 hx) hc]
  exact mul_mem (corner_mem_commutator (by decide) (by decide) _)
    (mul_mem (corner_mem_commutator (by decide) (by decide) _)
      (mul_mem (corner_mem_commutator (by decide) (by decide) _)
        (corner_mem_commutator (by decide) (by decide) _)))

theorem q2_selfCentralizing (hK : Nat.card K = 2) :
    flagStabilizer 5 K {2, 3} ⊓ Subgroup.centralizer (R2 K : Set (SpecialLinearGroup (Fin 5) K)) ≤
      R2 K := by
  rintro x ⟨hxQ, hxc⟩
  have hc : ∀ r ∈ R2 K, r * x = x * r := Subgroup.mem_centralizer_iff.1 hxc
  obtain ⟨c00, c10, c01, c11, c33, c34, c43, c44, -, -, -, -⟩ := q2_cent hc
  have x22 := q2_x22 hK hxQ
  refine mem_R2_iff.2 ⟨hxQ, ?_, ?_⟩
  · ext p q
    fin_cases p <;> fin_cases q <;> simp [blkAt_apply, c00, c10, c01, c11, x22]
  · ext p q
    fin_cases p <;> fin_cases q <;> simp [blkAt_apply, c33, c34, c43, c44, x22]

omit [Finite K] in
theorem q2_nonabelian : ∃ x ∈ R2 K, ∃ y ∈ R2 K, x * y ≠ y * x := by
  have h02 : (0 : Fin 5) < 2 := by decide
  have h23 : (2 : Fin 5) < 3 := by decide
  have h03 : (0 : Fin 5) < 3 := by decide
  refine ⟨SpecialLinearGroup.transvection h02.ne (1 : K),
    transvection_mem_R2 h02 (by decide) (by decide) 1, SpecialLinearGroup.transvection h23.ne 1,
    transvection_mem_R2 h23 (by decide) (by decide) 1, fun h => ?_⟩
  have h1 := Matrix.SpecialLinearGroup.commutatorElement_transvection h02.ne h23.ne h03.ne
    (1 : K) 1
  rw [commutatorElement_eq_one_iff_mul_comm.2 h, mul_one] at h1
  have h2 := congrArg (fun z : SpecialLinearGroup (Fin 5) K => (z : Matrix (Fin 5) (Fin 5) K) 0 3) h1
  simp [SpecialLinearGroup.transvection_coe] at h2

theorem q2_perfectCore [CharP K 2] (hK : Nat.card K = 2) :
    CFSG.Quasithin.perfectCore (flagStabilizer 5 K {2, 3}) = ⊥ :=
  perfectCore_eq_bot_of_small hK (by norm_num) (fun a m _ ha hb hno => by
    rcases maxBlock_cases ha hb hno with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num)

theorem parabolicFacts_q2 [CharP K 2] (hK : Nat.card K = 2) :
    Lie.ParabolicFacts (flagStabilizer 5 K {2, 3}) (R2 K) where
  le := R2_le_q2
  normalizes := q2_le_normalizer_R2
  pGroup := R2_isPGroup hK
  selfCentralizing := q2_selfCentralizing hK
  center_le := q2_center_le hK
  nonabelian := q2_nonabelian
  levi := Or.inl (by rw [q2_perfectCore hK]; exact bot_le)

theorem goodSub_q2 [CharP K 2] (hK : Nat.card K = 2) : GoodSub (flagStabilizer 5 K {2, 3}) :=
  GoodSub.of_parabolicFacts (parabolicFacts_q2 hK)

end Q2

end CFSG.QuasithinUnique.Vol2Native.L239.L52
