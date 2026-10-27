module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import all CFSG.Fischer.F4

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

namespace U52Layer

open CFSG.Fischer CFSG.Open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo Matrix
  CFSG.Yardstones.Md0ec50421ce4

abbrev M5 : Type := StatedSU 5 (2 ^ 1) F4

theorem hF4card : Nat.card F4 = (2 ^ 1) ^ 2 := by
  rw [Nat.card_eq_fintype_card, F4.card]; norm_num

theorem mem_M5_iff {g : GL (Fin 5) F4} : g ∈ StatedSU 5 (2 ^ 1) F4 ↔
    (g : Matrix (Fin 5) (Fin 5) F4).det = 1 ∧
      ((g : Matrix (Fin 5) (Fin 5) F4).map (· ^ 2 ^ 1))ᵀ * (g : Matrix (Fin 5) (Fin 5) F4) = 1 := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel (K := F4) (p := 2) (f := 1) Nat.prime_two
    hF4card (n := 5) (by norm_num)).1
  have := Set.ext_iff.1 h g
  simpa using this

theorem mem_M4_iff {g : GL (Fin 4) F4} : g ∈ StatedSU 4 (2 ^ 1) F4 ↔
    (g : Matrix (Fin 4) (Fin 4) F4).det = 1 ∧
      ((g : Matrix (Fin 4) (Fin 4) F4).map (· ^ 2 ^ 1))ᵀ * (g : Matrix (Fin 4) (Fin 4) F4) = 1 := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel (K := F4) (p := 2) (f := 1) Nat.prime_two
    hF4card (n := 4) (by norm_num)).1
  have := Set.ext_iff.1 h g
  simpa using this

noncomputable def equivM5 : SU52 ≃* M5 :=
  (statedProjEquiv (K := F4) hF4card).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_eq_bot hF4card)).trans
      QuotientGroup.quotientBot)

theorem bridge_u5two_stated {S : Type} [Group S] (h : catalogIs S S9.isU5two) :
    Nonempty (S ≃* M5) :=
  (bridge_u5two h).map fun e => e.trans equivM5

@[expose] def Em (A : Matrix (Fin 4) (Fin 4) F4) : Matrix (Fin 5) (Fin 5) F4 :=
  !![A 0 0, A 0 1, A 0 2, A 0 3, 0; A 1 0, A 1 1, A 1 2, A 1 3, 0; A 2 0, A 2 1, A 2 2, A 2 3, 0;
    A 3 0, A 3 1, A 3 2, A 3 3, 0; 0, 0, 0, 0, 1]

@[expose] def blk (M : Matrix (Fin 5) (Fin 5) F4) : Matrix (Fin 4) (Fin 4) F4 :=
  !![M 0 0, M 0 1, M 0 2, M 0 3; M 1 0, M 1 1, M 1 2, M 1 3; M 2 0, M 2 1, M 2 2, M 2 3;
    M 3 0, M 3 1, M 3 2, M 3 3]

theorem Em_mul (A B : Matrix (Fin 4) (Fin 4) F4) : Em (A * B) = Em A * Em B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Em, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_four]

theorem Em_one : Em 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em]

theorem blk_Em (A : Matrix (Fin 4) (Fin 4) F4) : blk (Em A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em, blk]

theorem Em_blk {M : Matrix (Fin 5) (Fin 5) F4} (h4 : ∀ i : Fin 5, i ≠ 4 → M i 4 = 0)
    (h4' : ∀ j : Fin 5, j ≠ 4 → M 4 j = 0) (h44 : M 4 4 = 1) : Em (blk M) = M := by
  have e0 := h4 0 (by decide)
  have e1 := h4 1 (by decide)
  have e2 := h4 2 (by decide)
  have e3 := h4 3 (by decide)
  have f0 := h4' 0 (by decide)
  have f1 := h4' 1 (by decide)
  have f2 := h4' 2 (by decide)
  have f3 := h4' 3 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em, blk, e0, e1, e2, e3, f0, f1, f2, f3, h44]

theorem Em_transpose (A : Matrix (Fin 4) (Fin 4) F4) : (Em A)ᵀ = Em Aᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em]

theorem Em_map (f : F4 → F4) (hf0 : f 0 = 0) (hf1 : f 1 = 1) (A : Matrix (Fin 4) (Fin 4) F4) :
    (Em A).map f = Em (A.map f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Em, hf0, hf1]

theorem det_Em (A : Matrix (Fin 4) (Fin 4) F4) : (Em A).det = A.det := by
  have h := Matrix.det_succ_row (Em A) (Fin.last 4)
  rw [h, Fin.sum_univ_castSucc]
  have hz : ∀ j : Fin 4, Em A (Fin.last 4) (Fin.castSucc j) = 0 := fun j => by
    fin_cases j <;> simp [Em]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  have hl : Em A (Fin.last 4) (Fin.last 4) = 1 := by simp [Em]
  rw [hl]
  simp only [Fin.succAbove_last]
  have : (Em A).submatrix Fin.castSucc Fin.castSucc = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Em]
  rw [this]
  have h8 : ((-1 : F4)) ^ 8 = 1 := by decide
  simp [h8]

theorem Em_injective {A B : Matrix (Fin 4) (Fin 4) F4} (h : Em A = Em B) : A = B := by
  rw [← blk_Em A, h, blk_Em]

@[expose] def Emon : Matrix (Fin 4) (Fin 4) F4 →* Matrix (Fin 5) (Fin 5) F4 where
  toFun := Em
  map_one' := Em_one
  map_mul' := Em_mul

@[expose] def Eu : GL (Fin 4) F4 →* GL (Fin 5) F4 := Units.map Emon

theorem coe_Eu (a : GL (Fin 4) F4) : ((Eu a : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) =
    Em (a : Matrix (Fin 4) (Fin 4) F4) := rfl

theorem sq_zero_one : ((0 : F4) ^ 2 ^ 1 = 0) ∧ ((1 : F4) ^ 2 ^ 1 = 1) := by decide

theorem Eu_mem {a : GL (Fin 4) F4} (ha : a ∈ StatedSU 4 (2 ^ 1) F4) :
    Eu a ∈ StatedSU 5 (2 ^ 1) F4 := by
  obtain ⟨hdet, hunit⟩ := mem_M4_iff.1 ha
  rw [mem_M5_iff, coe_Eu, det_Em]
  refine ⟨hdet, ?_⟩
  rw [Em_map _ sq_zero_one.1 sq_zero_one.2, Em_transpose, ← Em_mul, hunit, Em_one]

@[expose] def Phi : ↥(StatedSU 4 (2 ^ 1) F4) →* M5 :=
  MonoidHom.codRestrict (Eu.comp (StatedSU 4 (2 ^ 1) F4).subtype) (StatedSU 5 (2 ^ 1) F4)
    (fun a => Eu_mem a.2)

theorem Phi_injective : Function.Injective Phi := by
  intro a b h
  have h1 : ((Phi a : M5) : GL (Fin 5) F4) = ((Phi b : M5) : GL (Fin 5) F4) := congrArg Subtype.val h
  have h2 : ((a : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) =
      ((b : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) := by
    apply Em_injective
    exact congrArg (fun g : GL (Fin 5) F4 => (g : Matrix (Fin 5) (Fin 5) F4)) h1
  exact Subtype.ext (Units.ext h2)

@[expose] def Dm : Matrix (Fin 5) (Fin 5) F4 :=
  Matrix.diagonal ![F4.ω, F4.ω, F4.ω, F4.ω, F4.ω + 1]

@[expose] def Dm' : Matrix (Fin 5) (Fin 5) F4 :=
  Matrix.diagonal ![F4.ω + 1, F4.ω + 1, F4.ω + 1, F4.ω + 1, F4.ω]

theorem Dm_mul_Dm' : Dm * Dm' = 1 := by decide
theorem Dm'_mul_Dm : Dm' * Dm = 1 := by decide
theorem Dm_unitary : (Dm.map (· ^ 2 ^ 1))ᵀ * Dm = 1 := by decide
theorem Dm_det : Dm.det = 1 := by
  rw [Dm, Matrix.det_diagonal, Fin.prod_univ_five]
  decide

@[expose] def yG : GL (Fin 5) F4 := ⟨Dm, Dm', Dm_mul_Dm', Dm'_mul_Dm⟩

theorem yG_mem : yG ∈ StatedSU 5 (2 ^ 1) F4 := mem_M5_iff.2 ⟨Dm_det, Dm_unitary⟩

@[expose] def yM5 : M5 := ⟨yG, yG_mem⟩

theorem yM5_pow_three : yM5 ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp only [pow_succ, pow_zero, one_mul, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one,
    Units.val_one]
  show Dm * Dm * Dm = 1
  decide

theorem yM5_ne_one : yM5 ≠ 1 := by
  intro h
  have := congrArg (fun g : M5 => ((g : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4)) h
  change Dm = 1 at this
  revert this
  decide

abbrev mt (g : M5) : Matrix (Fin 5) (Fin 5) F4 := ((g : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4)

theorem mt_mul (g h : M5) : mt (g * h) = mt g * mt h := rfl

theorem mt_one : mt (1 : M5) = 1 := rfl

theorem aux_a : ∀ x : F4, x * (F4.ω + 1) = F4.ω * x → x = 0 := by decide
theorem aux_b : ∀ x : F4, x * F4.ω = (F4.ω + 1) * x → x = 0 := by decide

theorem block_zero {g : M5} (hg : g ∈ Subgroup.centralizer ({yM5} : Set M5)) :
    (∀ i : Fin 5, i ≠ 4 → mt g i 4 = 0) ∧ (∀ j : Fin 5, j ≠ 4 → mt g 4 j = 0) := by
  have h : g * yM5 = yM5 * g := Subgroup.mem_centralizer_singleton_iff.1 hg
  have hm : mt g * Dm = Dm * mt g := congrArg mt h
  constructor
  · intro i hi
    have key := congrFun (congrFun hm i) 4
    fin_cases i
    all_goals first
      | exact absurd rfl hi
      | (simp [Dm, Matrix.mul_diagonal, Matrix.diagonal_mul] at key
         exact aux_a _ key)
  · intro j hj
    have key := congrFun (congrFun hm 4) j
    fin_cases j
    all_goals first
      | exact absurd rfl hj
      | (simp [Dm, Matrix.mul_diagonal, Matrix.diagonal_mul] at key
         exact aux_b _ key)

def IsBlk0 (g : M5) : Prop := (∀ i : Fin 5, i ≠ 4 → mt g i 4 = 0) ∧ (∀ j : Fin 5, j ≠ 4 → mt g 4 j = 0)

def IsBlk1 (g : M5) : Prop := IsBlk0 g ∧ mt g 4 4 = 1

theorem Em_col (A : Matrix (Fin 4) (Fin 4) F4) (i : Fin 5) (hi : i ≠ 4) : Em A i 4 = 0 := by
  fin_cases i <;> simp_all [Em]

theorem Em_row (A : Matrix (Fin 4) (Fin 4) F4) (j : Fin 5) (hj : j ≠ 4) : Em A 4 j = 0 := by
  fin_cases j <;> simp_all [Em]

theorem Em_last (A : Matrix (Fin 4) (Fin 4) F4) : Em A 4 4 = 1 := by simp [Em]

theorem mt_Phi (a : StatedSU 4 (2 ^ 1) F4) :
    mt (Phi a) = Em ((a : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) := rfl

theorem isBlk1_Phi (a : StatedSU 4 (2 ^ 1) F4) : IsBlk1 (Phi a) := by
  rw [IsBlk1, IsBlk0, mt_Phi]
  exact ⟨⟨Em_col _, Em_row _⟩, Em_last _⟩

theorem isBlk1_inv {g : M5} (h : IsBlk1 g) : IsBlk1 g⁻¹ := by
  obtain ⟨⟨hc, hr⟩, h44⟩ := h
  have hgg : mt g⁻¹ * mt g = 1 := by
    have := congrArg mt (inv_mul_cancel g)
    rwa [mt_mul, mt_one] at this
  have hgg' : mt g * mt g⁻¹ = 1 := by
    have := congrArg mt (mul_inv_cancel g)
    rwa [mt_mul, mt_one] at this
  have c0 := hc 0 (by decide)
  have c1 := hc 1 (by decide)
  have c2 := hc 2 (by decide)
  have c3 := hc 3 (by decide)
  have r0 := hr 0 (by decide)
  have r1 := hr 1 (by decide)
  have r2 := hr 2 (by decide)
  have r3 := hr 3 (by decide)
  have col : ∀ i : Fin 5, i ≠ 4 → mt g⁻¹ i 4 = 0 := by
    intro i hi
    have := congrFun (congrFun hgg i) 4
    simp only [Matrix.mul_apply, Fin.sum_univ_five, c0, c1, c2, c3, h44, mul_zero, mul_one,
      zero_add, add_zero] at this
    rw [this]
    simp [Matrix.one_apply, hi]
  have row : ∀ j : Fin 5, j ≠ 4 → mt g⁻¹ 4 j = 0 := by
    intro j hj
    have := congrFun (congrFun hgg' 4) j
    simp only [Matrix.mul_apply, Fin.sum_univ_five, r0, r1, r2, r3, h44, zero_mul, one_mul,
      zero_add, add_zero] at this
    rw [this]
    simp [Matrix.one_apply, Ne.symm hj]
  refine ⟨⟨col, row⟩, ?_⟩
  have := congrFun (congrFun hgg 4) 4
  simp only [Matrix.mul_apply, Fin.sum_univ_five, c0, c1, c2, c3, h44, mul_zero, mul_one,
    zero_add, add_zero] at this
  rw [this]
  simp

theorem exists_Phi_of_isBlk1 {g : M5} (h : IsBlk1 g) : ∃ a : StatedSU 4 (2 ^ 1) F4, Phi a = g := by
  have h' := isBlk1_inv h
  have hmul : mt g * mt g⁻¹ = 1 := by
    have := congrArg mt (mul_inv_cancel g)
    rwa [mt_mul, mt_one] at this
  have hmul' : mt g⁻¹ * mt g = 1 := by
    have := congrArg mt (inv_mul_cancel g)
    rwa [mt_mul, mt_one] at this
  have hEg : Em (blk (mt g)) = mt g := Em_blk h.1.1 h.1.2 h.2
  have hEg' : Em (blk (mt g⁻¹)) = mt g⁻¹ := Em_blk h'.1.1 h'.1.2 h'.2
  have e1 : blk (mt g) * blk (mt g⁻¹) = 1 := by
    apply Em_injective
    rw [Em_mul, hEg, hEg', hmul, Em_one]
  have e2 : blk (mt g⁻¹) * blk (mt g) = 1 := by
    apply Em_injective
    rw [Em_mul, hEg, hEg', hmul', Em_one]
  have hmem : (⟨blk (mt g), blk (mt g⁻¹), e1, e2⟩ : GL (Fin 4) F4) ∈ StatedSU 4 (2 ^ 1) F4 := by
    rw [mem_M4_iff]
    have hg := (mem_M5_iff.1 g.2)
    refine ⟨?_, ?_⟩
    · show (blk (mt g)).det = 1
      rw [← det_Em, hEg]
      exact hg.1
    · show ((blk (mt g)).map (· ^ 2 ^ 1))ᵀ * blk (mt g) = 1
      apply Em_injective
      rw [Em_mul, ← Em_transpose, ← Em_map _ sq_zero_one.1 sq_zero_one.2, hEg]
      rw [Em_one]
      exact hg.2
  refine ⟨⟨_, hmem⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hEg

theorem mem_range_Phi_iff {g : M5} : g ∈ Phi.range ↔ IsBlk1 g := by
  constructor
  · rintro ⟨a, rfl⟩
    exact isBlk1_Phi a
  · intro h
    obtain ⟨a, ha⟩ := exists_Phi_of_isBlk1 h
    exact ⟨a, ha⟩

theorem mt_yM5 : mt yM5 = Dm := rfl
theorem mt_yM5_inv : mt yM5⁻¹ = Dm' := rfl

theorem isBlk0_mul_y {g : M5} (h : IsBlk0 g) :
    IsBlk0 (g * yM5) ∧ mt (g * yM5) 4 4 = mt g 4 4 * (F4.ω + 1) := by
  rw [mt_mul, mt_yM5, Dm]
  refine ⟨⟨fun i hi => ?_, fun j hj => ?_⟩, ?_⟩
  · rw [mt_mul, mt_yM5, Dm, Matrix.mul_diagonal, h.1 i hi, zero_mul]
  · rw [mt_mul, mt_yM5, Dm, Matrix.mul_diagonal, h.2 j hj, zero_mul]
  · rw [Matrix.mul_diagonal]
    simp

theorem isBlk0_mul_yinv {g : M5} (h : IsBlk0 g) :
    IsBlk0 (g * yM5⁻¹) ∧ mt (g * yM5⁻¹) 4 4 = mt g 4 4 * F4.ω := by
  rw [mt_mul, mt_yM5_inv, Dm']
  refine ⟨⟨fun i hi => ?_, fun j hj => ?_⟩, ?_⟩
  · rw [mt_mul, mt_yM5_inv, Dm', Matrix.mul_diagonal, h.1 i hi, zero_mul]
  · rw [mt_mul, mt_yM5_inv, Dm', Matrix.mul_diagonal, h.2 j hj, zero_mul]
  · rw [Matrix.mul_diagonal]
    simp

theorem last_ne_zero {g : M5} (h : IsBlk0 g) : mt g 4 4 ≠ 0 := by
  intro h0
  have := congrFun (congrFun (congrArg mt (mul_inv_cancel g)) 4) 4
  rw [mt_mul, mt_one] at this
  simp only [Matrix.mul_apply, Fin.sum_univ_five, h.2 0 (by decide), h.2 1 (by decide),
    h.2 2 (by decide), h.2 3 (by decide), h0, zero_mul, add_zero] at this
  simp at this

theorem F4_cases_ne_zero : ∀ x : F4, x ≠ 0 → x = 1 ∨ x = F4.ω ∨ x = F4.ω + 1 := by decide
theorem F4_ω_mul : F4.ω * (F4.ω + 1) = 1 := by decide
theorem F4_ω_mul' : (F4.ω + 1) * F4.ω = 1 := by decide

theorem centralizer_le_sup {g : M5} (hg : g ∈ Subgroup.centralizer ({yM5} : Set M5)) :
    g ∈ Phi.range ⊔ Subgroup.zpowers yM5 := by
  have hb0 : IsBlk0 g := block_zero hg
  rcases F4_cases_ne_zero _ (last_ne_zero hb0) with h1 | h1 | h1
  · exact Subgroup.mem_sup_left (mem_range_Phi_iff.2 ⟨hb0, h1⟩)
  · obtain ⟨h0', h44⟩ := isBlk0_mul_y hb0
    have hm : g * yM5 ∈ Phi.range := mem_range_Phi_iff.2 ⟨h0', by rw [h44, h1, F4_ω_mul]⟩
    have : g = (g * yM5) * yM5⁻¹ := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hm)
      (Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers _)))
  · obtain ⟨h0', h44⟩ := isBlk0_mul_yinv hb0
    have hm : g * yM5⁻¹ ∈ Phi.range := mem_range_Phi_iff.2 ⟨h0', by rw [h44, h1, F4_ω_mul']⟩
    have : g = (g * yM5⁻¹) * yM5 := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem mem_centralizer_of_isBlk0 {g : M5} (h : IsBlk0 g) :
    g ∈ Subgroup.centralizer ({yM5} : Set M5) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  show mt g * Dm = Dm * mt g
  have c0 := h.1 0 (by decide)
  have c1 := h.1 1 (by decide)
  have c2 := h.1 2 (by decide)
  have c3 := h.1 3 (by decide)
  have r0 := h.2 0 (by decide)
  have r1 := h.2 1 (by decide)
  have r2 := h.2 2 (by decide)
  have r3 := h.2 3 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dm, Matrix.mul_diagonal, Matrix.diagonal_mul, c0, c1, c2, c3, r0, r1, r2, r3, mul_comm]

theorem mem_zpowers_cases {M : Type*} [Group M] {y : M} (h : y ^ 3 = 1) {z : M}
    (hz : z ∈ Subgroup.zpowers y) : z = 1 ∨ z = y ∨ z = y ^ 2 := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hn : y ^ n = y ^ (n % 3) := by
    calc y ^ n = y ^ (n % 3 + 3 * (n / 3)) := by rw [Int.emod_add_mul_ediv]
      _ = y ^ (n % 3) := by
        rw [_root_.zpow_add, _root_.zpow_mul]
        have : y ^ (3 : ℤ) = 1 := by exact_mod_cast h
        rw [this, _root_.one_zpow, mul_one]
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h0 | h0 | h0
  · left; rw [hn, h0]; simp
  · right; left; rw [hn, h0]; simp
  · right; right; rw [hn, h0]; simp

theorem range_inf_zpowers : Phi.range ⊓ Subgroup.zpowers yM5 = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzr, hzp⟩
  rw [Subgroup.mem_bot]
  have hz1 := (mem_range_Phi_iff.1 hzr).2
  rcases mem_zpowers_cases yM5_pow_three hzp with h | h | h
  · exact h
  · exfalso
    rw [h] at hz1
    revert hz1
    show Dm 4 4 ≠ 1
    decide
  · exfalso
    rw [h, pow_two, mt_mul] at hz1
    revert hz1
    show (Dm * Dm) 4 4 ≠ 1
    decide

theorem statedScalars4_eq_bot :
    (StatedScalars (Fin 4) F4).subgroupOf (StatedSU 4 (2 ^ 1) F4) = ⊥ := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF4card (n := 4)
    (by norm_num)).2.2
  rw [← Subgroup.card_eq_one, h]
  norm_num

noncomputable def equivM4 : StatedProj (StatedSU 4 (2 ^ 1) F4) ≃* StatedSU 4 (2 ^ 1) F4 :=
  (QuotientGroup.quotientMulEquivOfEq statedScalars4_eq_bot).trans QuotientGroup.quotientBot

theorem isSimple_M4 : IsSimpleGroup (StatedSU 4 (2 ^ 1) F4) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F4 2 1 hF4card 4
    (by norm_num) (by norm_num)
  exact equivM4.symm.isSimpleGroup

noncomputable def PhiEquiv : StatedSU 4 (2 ^ 1) F4 ≃* ↥(Phi.range) :=
  MonoidHom.ofInjective Phi_injective

theorem isSimple_range : IsSimpleGroup ↥(Phi.range) := by
  haveI := isSimple_M4
  exact PhiEquiv.symm.isSimpleGroup

theorem catalogIs_range : catalogIs ↥(Phi.range) S9.isU4two :=
  catalogIs_u4two_of_statedProj (K := F4) (by simpa using hF4card)
    (PhiEquiv.symm.trans equivM4.symm)

@[expose] def invol (A : Matrix (Fin 5) (Fin 5) F4) (h : A * A = 1) (hd : A.det = 1)
    (hu : (A.map (· ^ 2 ^ 1))ᵀ * A = 1) : M5 :=
  ⟨⟨A, A, h, h⟩, mem_M5_iff.2 ⟨hd, hu⟩⟩

@[expose] def Sw : Matrix (Fin 5) (Fin 5) F4 :=
  !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def Sw' : Matrix (Fin 5) (Fin 5) F4 :=
  !![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

theorem Sw_sq : Sw * Sw = 1 := by decide
theorem Sw'_sq : Sw' * Sw' = 1 := by decide
theorem Sw_det : Sw.det = 1 := by decide +kernel
theorem Sw'_det : Sw'.det = 1 := by decide +kernel
theorem Sw_unitary : (Sw.map (· ^ 2 ^ 1))ᵀ * Sw = 1 := by decide
theorem Sw'_unitary : (Sw'.map (· ^ 2 ^ 1))ᵀ * Sw' = 1 := by decide

@[expose] def sM5 : M5 := invol Sw Sw_sq Sw_det Sw_unitary
@[expose] def uM5 : M5 := invol Sw' Sw'_sq Sw'_det Sw'_unitary

theorem sM5_isBlk1 : IsBlk1 sM5 := by
  show (IsBlk0 sM5) ∧ _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show ∀ i : Fin 5, i ≠ 4 → Sw i 4 = 0
    decide
  · show ∀ j : Fin 5, j ≠ 4 → Sw 4 j = 0
    decide
  · show Sw 4 4 = 1
    decide

theorem uM5_isBlk1 : IsBlk1 uM5 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show ∀ i : Fin 5, i ≠ 4 → Sw' i 4 = 0
    decide
  · show ∀ j : Fin 5, j ≠ 4 → Sw' 4 j = 0
    decide
  · show Sw' 4 4 = 1
    decide

theorem sM5_mem : sM5 ∈ Phi.range := mem_range_Phi_iff.2 sM5_isBlk1
theorem uM5_mem : uM5 ∈ Phi.range := mem_range_Phi_iff.2 uM5_isBlk1

theorem su_ne_us : sM5 * uM5 ≠ uM5 * sM5 := by
  intro h
  have := congrArg mt h
  rw [mt_mul, mt_mul] at this
  revert this
  show Sw * Sw' = Sw' * Sw → False
  decide

theorem su_pow_three : (sM5 * uM5) ^ 3 = 1 := by
  have : (sM5 * uM5) ^ 3 = sM5 * uM5 * (sM5 * uM5) * (sM5 * uM5) := by
    rw [pow_succ, pow_two]
  rw [this]
  apply Subtype.ext
  apply Units.ext
  show Sw * Sw' * (Sw * Sw') * (Sw * Sw') = 1
  decide

theorem su_ne_one : sM5 * uM5 ≠ 1 := by
  intro h
  have := congrArg mt h
  rw [mt_mul, mt_one] at this
  revert this
  show Sw * Sw' = 1 → False
  decide

theorem not_comm_range : ¬ IsMulCommutative ↥(Phi.range) := by
  intro hc
  have := hc.1
  apply su_ne_us
  have h := mul_comm' (⟨sM5, sM5_mem⟩ : ↥(Phi.range)) ⟨uM5, uM5_mem⟩
  exact congrArg Subtype.val h

theorem three_dvd_range : 3 ∣ Nat.card ↥(Phi.range) := by
  have hmem : sM5 * uM5 ∈ Phi.range := mul_mem sM5_mem uM5_mem
  have hord : orderOf (sM5 * uM5) = 3 := orderOf_eq_prime su_pow_three su_ne_one
  have := orderOf_dvd_natCard (⟨sM5 * uM5, hmem⟩ : ↥(Phi.range))
  rwa [Subgroup.orderOf_mk, hord] at this

theorem m5_u4_layer : ∃ Kb : Subgroup M5,
    Kb ≤ Subgroup.centralizer ({yM5} : Set M5) ∧
    Subgroup.centralizer ({yM5} : Set M5) = Kb ⊔ Subgroup.zpowers yM5 ∧
    Kb ⊓ Subgroup.zpowers yM5 = ⊥ ∧ IsSimpleGroup ↥Kb ∧ ¬ IsMulCommutative ↥Kb ∧
    3 ∣ Nat.card Kb ∧ catalogIs ↥Kb S9.isU4two := by
  refine ⟨Phi.range, ?_, ?_, range_inf_zpowers, isSimple_range, not_comm_range, three_dvd_range,
    catalogIs_range⟩
  · intro g hg
    exact mem_centralizer_of_isBlk0 (mem_range_Phi_iff.1 hg).1
  · apply le_antisymm
    · intro g hg
      exact centralizer_le_sup hg
    · refine sup_le ?_ ?_
      · intro g hg
        exact mem_centralizer_of_isBlk0 (mem_range_Phi_iff.1 hg).1
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.2 rfl

end U52Layer

end CFSG.LocalAnalysis.GLTheoremA.CatB
