module

public import Mathlib.Algebra.CharP.CharAndCard
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherInvariant
public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.QuasithinUnique

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace SteinbergCH

variable {K : Type*} [Field K] {n : ℕ}

theorem eq_one_of_ne_zero_of_card_two [Finite K] (hK : Nat.card K = 2) {x : K} (hx : x ≠ 0) :
    x = 1 := by
  have : Subsingleton Kˣ := by
    have hcard : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
    exact (Nat.card_eq_one_iff_unique.1 hcard).1
  exact congrArg Units.val (Subsingleton.elim (Units.mk0 x hx) 1)

theorem charP_two_of_card_two [Finite K] (hK : Nat.card K = 2) : CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])

theorem upperTriangular_eq_unitriangular_of_card_two [Finite K] (hK : Nat.card K = 2) :
    upperTriangular n K = unitriangular n K := by
  refine le_antisymm (fun A hA => ⟨hA, fun i => ?_⟩) (unitriangular_le_upperTriangular n K)
  have hA' : (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular :=
    mem_upperTriangular_iff_isUpperTriangular.mp hA
  have hdet : (A : Matrix (Fin n) (Fin n) K).det = ∏ j, (A : Matrix (Fin n) (Fin n) K) j j :=
    det_of_isUpperTriangular hA'
  rw [A.prop] at hdet
  refine eq_one_of_ne_zero_of_card_two hK fun h0 => ?_
  rw [Finset.prod_eq_zero (f := fun j => (A : Matrix (Fin n) (Fin n) K) j j)
    (Finset.mem_univ i) h0] at hdet
  exact one_ne_zero hdet

theorem apply_eq_zero_of_mem_stabilizer {c : ℕ} {A : SpecialLinearGroup (Fin n) K}
    (hA : A ∈ stabilizer (flagSpace n K c)) {i k : Fin n} (hk : (k : ℕ) < c)
    (hi : c ≤ (i : ℕ)) : (A : Matrix (Fin n) (Fin n) K) i k = 0 := by
  have h1 : (Pi.single k 1 : Fin n → K) ∈ flagSpace n K c :=
    mem_flagSpace.mpr fun j hj => Pi.single_eq_of_ne (fun h => by subst h; omega) _
  have h2 : (A : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single k 1 ∈ flagSpace n K c := by
    rw [← mem_stabilizer.mp hA]
    exact Submodule.mem_map.mpr ⟨_, h1, rfl⟩
  have h3 := mem_flagSpace.mp h2 i hi
  rwa [mulVec_single_one, col_apply] at h3

@[expose] def SameBlock (I : Set ℕ) (i j : ℕ) : Prop := ∀ c ∈ I, (c ≤ i ↔ c ≤ j)

theorem sameBlock_refl (I : Set ℕ) (i : ℕ) : SameBlock I i i := fun _ _ => Iff.rfl

theorem mul_apply_of_sameBlock {I : Set ℕ} {A B : SpecialLinearGroup (Fin n) K}
    (hA : A ∈ flagStabilizer n K I) (hB : B ∈ flagStabilizer n K I) {i j : Fin n}
    (hij : SameBlock I i j) {s : Finset (Fin n)} (hs : ∀ k : Fin n, SameBlock I i k → k ∈ s) :
    ((A * B : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
      ∑ k ∈ s, (A : Matrix (Fin n) (Fin n) K) i k * (B : Matrix (Fin n) (Fin n) K) k j := by
  rw [SpecialLinearGroup.coe_mul, mul_apply]
  refine (Finset.sum_subset (Finset.subset_univ s) fun k _ hk => ?_).symm
  obtain ⟨c, hc, hck⟩ : ∃ c ∈ I, ¬ (c ≤ (i : ℕ) ↔ c ≤ (k : ℕ)) := by
    by_contra h
    exact hk (hs k fun c hc => by
      by_contra h'
      exact h ⟨c, hc, h'⟩)
  by_cases hci : c ≤ (i : ℕ)
  · have hkc : (k : ℕ) < c := by
      by_contra h
      exact hck (iff_of_true hci (by omega))
    rw [apply_eq_zero_of_mem_stabilizer (mem_flagStabilizer.mp hA c hc) hkc hci, zero_mul]
  · have hck' : c ≤ (k : ℕ) := by
      by_contra h
      exact hck (iff_of_false hci h)
    have hjc : (j : ℕ) < c := by
      have := (hij c hc).not.mp hci
      omega
    rw [apply_eq_zero_of_mem_stabilizer (mem_flagStabilizer.mp hB c hc) hjc hck', mul_zero]

@[expose] def blockRadical (n : ℕ) (K : Type*) [Field K] (I : Set ℕ) :
    Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {A | A ∈ flagStabilizer n K I ∧ ∀ i j : Fin n, SameBlock I i j →
    (A : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j}
  one_mem' := ⟨one_mem _, fun _ _ _ => rfl⟩
  mul_mem' := by
    classical
    rintro A B ⟨hA, hA'⟩ ⟨hB, hB'⟩
    refine ⟨mul_mem hA hB, fun i j hij => ?_⟩
    rw [mul_apply_of_sameBlock hA hB hij (s := Finset.univ.filter fun k : Fin n => SameBlock I i k)
      fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩,
      Finset.sum_eq_single_of_mem i
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, sameBlock_refl I i⟩)]
    · rw [hA' i i (sameBlock_refl I i), hB' i j hij, one_apply_eq, one_mul]
    · intro k hk hki
      rw [hA' i k (Finset.mem_filter.mp hk).2, one_apply_ne (Ne.symm hki), zero_mul]
  inv_mem' := by
    classical
    rintro A ⟨hA, hA'⟩
    refine ⟨inv_mem hA, fun i j hij => ?_⟩
    have h1 := mul_apply_of_sameBlock hA (inv_mem hA) hij
      (s := Finset.univ.filter fun k : Fin n => SameBlock I i k)
      fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    rw [mul_inv_cancel, Finset.sum_eq_single_of_mem i
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, sameBlock_refl I i⟩)] at h1
    · rw [hA' i i (sameBlock_refl I i), one_apply_eq, one_mul] at h1
      exact h1.symm
    · intro k hk hki
      rw [hA' i k (Finset.mem_filter.mp hk).2, one_apply_ne (Ne.symm hki), zero_mul]

theorem blockRadical_le_flagStabilizer (I : Set ℕ) :
    blockRadical n K I ≤ flagStabilizer n K I := fun _ hA => hA.1

theorem blockRadical_le_unitriangular (I : Set ℕ) : blockRadical n K I ≤ unitriangular n K := by
  rintro A ⟨hA, hA'⟩
  refine ⟨fun i k hki => ?_, fun i => by rw [hA' i i (sameBlock_refl I i), one_apply_eq]⟩
  by_cases h : SameBlock I i k
  · rw [hA' i k h, one_apply_ne (ne_of_gt hki)]
  · obtain ⟨c, hc, hck⟩ : ∃ c ∈ I, ¬ (c ≤ (i : ℕ) ↔ c ≤ (k : ℕ)) := by
      by_contra h'
      exact h fun c hc => by
        by_contra h''
        exact h' ⟨c, hc, h''⟩
    have hki' : (k : ℕ) < i := hki
    have hci : c ≤ (i : ℕ) := by
      by_contra h1
      exact hck (iff_of_false h1 (by omega))
    have hkc : (k : ℕ) < c := by
      by_contra h1
      exact hck (iff_of_true hci (by omega))
    exact apply_eq_zero_of_mem_stabilizer (mem_flagStabilizer.mp hA c hc) hkc hci

@[expose] def joinCuts (n : ℕ) (J : Set ℕ) : Set ℕ := {c | 1 ≤ c ∧ c < n ∧ c ∉ J}

theorem sameBlock_joinCuts_iff {J : Set ℕ} (hJ : ∀ x ∈ J, x + 1 ∉ J) {i k : ℕ} (hi : i < n)
    (hk : k < n) :
    SameBlock (joinCuts n J) i k ↔ i = k ∨ (k = i + 1 ∧ k ∈ J) ∨ (i = k + 1 ∧ i ∈ J) := by
  constructor
  · intro h
    have key : ∀ c, 1 ≤ c → c < n → c ∉ J → (c ≤ i ↔ c ≤ k) :=
      fun c h1 h2 h3 => h c ⟨h1, h2, h3⟩
    rcases lt_trichotomy i k with hik | rfl | hki
    · right; left
      by_cases hk1 : k = i + 1
      · refine ⟨hk1, ?_⟩
        by_contra hkJ
        have := (key k (by omega) hk hkJ).mpr le_rfl
        omega
      · exfalso
        by_cases hJ1 : i + 1 ∈ J
        · have := (key (i + 1 + 1) (by omega) (by omega) (hJ _ hJ1)).mpr (by omega)
          omega
        · have := (key (i + 1) (by omega) (by omega) hJ1).mpr (by omega)
          omega
    · left; rfl
    · right; right
      by_cases hi1 : i = k + 1
      · refine ⟨hi1, ?_⟩
        by_contra hiJ
        have := (key i (by omega) hi hiJ).mp le_rfl
        omega
      · exfalso
        by_cases hJ1 : k + 1 ∈ J
        · have := (key (k + 1 + 1) (by omega) (by omega) (hJ _ hJ1)).mp (by omega)
          omega
        · have := (key (k + 1) (by omega) (by omega) hJ1).mp (by omega)
          omega
  · rintro (rfl | ⟨rfl, hkJ⟩ | ⟨rfl, hiJ⟩) c ⟨-, -, hcJ⟩
    · exact Iff.rfl
    · have : c ≠ i + 1 := fun h => hcJ (h ▸ hkJ)
      constructor <;> intro <;> omega
    · have : c ≠ k + 1 := fun h => hcJ (h ▸ hiJ)
      constructor <;> intro <;> omega

@[expose] def blockMat (p : ℕ) (hp : p + 2 ≤ n) (A : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun a b => A ⟨p + a, by have := a.isLt; omega⟩ ⟨p + b, by have := b.isLt; omega⟩

omit [Field K] in
theorem blockMat_apply_of_eq {p : ℕ} {hp : p + 2 ≤ n} {A : Matrix (Fin n) (Fin n) K}
    {a b : Fin 2} {i j : Fin n} (hi : (i : ℕ) = p + a) (hj : (j : ℕ) = p + b) :
    blockMat p hp A a b = A i j := by
  rw [blockMat, of_apply]
  congr 1 <;> exact Fin.ext (by simp [hi, hj])

theorem blockMat_one (p : ℕ) (hp : p + 2 ≤ n) :
    blockMat p hp (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  ext a b
  simp [blockMat, one_apply, Fin.ext_iff]

theorem sameBlock_pair_iff {J : Set ℕ} (hJ : ∀ x ∈ J, x + 1 ∉ J) {p : ℕ} (hpJ : p + 1 ∈ J)
    (hp : p + 2 ≤ n) {a : ℕ} (ha : a < 2) {k : ℕ} (hk : k < n) :
    SameBlock (joinCuts n J) (p + a) k ↔ k = p ∨ k = p + 1 := by
  have hpJ' : p ∉ J := fun h => hJ p h hpJ
  have hp2 : p + 1 + 1 ∉ J := hJ (p + 1) hpJ
  rw [sameBlock_joinCuts_iff hJ (by omega) hk]
  constructor
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · omega
    · by_cases ha0 : a = 0
      · omega
      · exfalso
        apply hp2
        rwa [show p + 1 + 1 = k by omega]
    · by_cases ha0 : a = 0
      · exfalso
        apply hpJ'
        rwa [show p = p + a by omega]
      · omega
  · rintro (rfl | rfl)
    · by_cases ha0 : a = 0
      · left; omega
      · right; right
        exact ⟨by omega, by rwa [show k + a = k + 1 by omega]⟩
    · by_cases ha0 : a = 0
      · right; left
        exact ⟨by omega, hpJ⟩
      · left; omega

theorem blockMat_mul {J : Set ℕ} (hJ : ∀ x ∈ J, x + 1 ∉ J) {p : ℕ} (hpJ : p + 1 ∈ J)
    (hp : p + 2 ≤ n) {A B : SpecialLinearGroup (Fin n) K}
    (hA : A ∈ flagStabilizer n K (joinCuts n J)) (hB : B ∈ flagStabilizer n K (joinCuts n J)) :
    blockMat p hp ((A * B : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      blockMat p hp (A : Matrix (Fin n) (Fin n) K) *
        blockMat p hp (B : Matrix (Fin n) (Fin n) K) := by
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  set x : Fin n := ⟨p, by omega⟩ with hx
  set y : Fin n := ⟨p + 1, by omega⟩ with hy
  have hxy : x ≠ y := fun h => by simpa [hx, hy] using congrArg Fin.val h
  have hab : SameBlock (joinCuts n J) (p + a) (p + b) :=
    (sameBlock_pair_iff hJ hpJ hp ha (by omega)).mpr (by omega)
  have hs : ∀ k : Fin n, SameBlock (joinCuts n J) (p + a) k → k ∈ ({x, y} : Finset (Fin n)) := by
    intro k hk
    rw [sameBlock_pair_iff hJ hpJ hp ha k.isLt] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton, hx, hy, Fin.ext_iff]
    exact hk
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  rw [show blockMat p hp ((A * B : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) a b =
    ((A * B : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
      ⟨p + a, by omega⟩ ⟨p + b, by omega⟩ from rfl]
  rw [mul_apply_of_sameBlock (i := ⟨p + a, by omega⟩) (j := ⟨p + b, by omega⟩) hA hB hab hs,
    Finset.sum_pair hxy]
  rw [blockMat_apply_of_eq (i := ⟨p + a, by omega⟩) (j := x) rfl (by simp [hx]),
    blockMat_apply_of_eq (i := x) (j := ⟨p + b, by omega⟩) (by simp [hx]) rfl,
    blockMat_apply_of_eq (i := ⟨p + a, by omega⟩) (j := y) rfl (by simp [hy]),
    blockMat_apply_of_eq (i := y) (j := ⟨p + b, by omega⟩) (by simp [hy]) rfl]

variable (K) in
@[expose] noncomputable def blockHom {J : Set ℕ} (hJ : ∀ x ∈ J, x + 1 ∉ J) {p : ℕ}
    (hpJ : p + 1 ∈ J) (hp : p + 2 ≤ n) :
    flagStabilizer n K (joinCuts n J) →* GL (Fin 2) K where
  toFun A :=
    { val := blockMat p hp ((A : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
      inv := blockMat p hp (((A⁻¹ : flagStabilizer n K (joinCuts n J)) :
        SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
      val_inv := by
        rw [← blockMat_mul hJ hpJ hp A.2 (A⁻¹).2, ← Subgroup.coe_mul, mul_inv_cancel,
          Subgroup.coe_one, SpecialLinearGroup.coe_one, blockMat_one]
      inv_val := by
        rw [← blockMat_mul hJ hpJ hp (A⁻¹).2 A.2, ← Subgroup.coe_mul, inv_mul_cancel,
          Subgroup.coe_one, SpecialLinearGroup.coe_one, blockMat_one] }
  map_one' := Units.ext (by
    change blockMat p hp (((1 : flagStabilizer n K (joinCuts n J)) :
      SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [Subgroup.coe_one, SpecialLinearGroup.coe_one, blockMat_one])
  map_mul' A B := Units.ext (by
    change blockMat p hp ((((A * B : flagStabilizer n K (joinCuts n J)) :
      SpecialLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) = _
    rw [Subgroup.coe_mul, blockMat_mul hJ hpJ hp A.2 B.2]
    rfl)

theorem coe_blockHom {J : Set ℕ} (hJ : ∀ x ∈ J, x + 1 ∉ J) {p : ℕ} (hpJ : p + 1 ∈ J)
    (hp : p + 2 ≤ n) (A : flagStabilizer n K (joinCuts n J)) :
    ((blockHom K hJ hpJ hp A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      blockMat p hp ((A : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  rfl

theorem apply_self_eq_one_of_singleton [Finite K] (hK : Nat.card K = 2) {J : Set ℕ}
    (hJ : ∀ x ∈ J, x + 1 ∉ J) {A : SpecialLinearGroup (Fin n) K}
    (hA : A ∈ flagStabilizer n K (joinCuts n J)) (i : Fin n) (hi : (i : ℕ) ∉ J)
    (hi1 : (i : ℕ) + 1 ∉ J) : (A : Matrix (Fin n) (Fin n) K) i i = 1 := by
  refine eq_one_of_ne_zero_of_card_two hK fun h0 => ?_
  have h1 := mul_apply_of_sameBlock hA (inv_mem hA) (sameBlock_refl _ i) (s := {i})
    fun k hk => by
      rw [sameBlock_joinCuts_iff hJ i.isLt k.isLt] at hk
      rcases hk with h | ⟨h1, h2⟩ | ⟨-, h2⟩
      · exact Finset.mem_singleton.mpr (Fin.ext h.symm)
      · rw [h1] at h2
        exact absurd h2 hi1
      · exact absurd h2 hi
  rw [mul_inv_cancel, Finset.sum_singleton, h0, zero_mul] at h1
  simp at h1

theorem mem_blockRadical_joinCuts_iff [Finite K] (hK : Nat.card K = 2) {J : Set ℕ}
    (hJ : ∀ x ∈ J, x + 1 ∉ J) (hJn : ∀ x ∈ J, 1 ≤ x ∧ x < n) {A : SpecialLinearGroup (Fin n) K}
    (hA : A ∈ flagStabilizer n K (joinCuts n J)) :
    A ∈ blockRadical n K (joinCuts n J) ↔ ∀ (p : ℕ) (hpJ : p + 1 ∈ J),
      blockMat p (by have := (hJn _ hpJ).2; omega) (A : Matrix (Fin n) (Fin n) K) = 1 := by
  constructor
  · rintro ⟨-, hA'⟩ p hpJ
    have hp : p + 2 ≤ n := by have := (hJn _ hpJ).2; omega
    ext a b
    have ha := a.isLt
    have hb := b.isLt
    have hab : SameBlock (joinCuts n J) (p + a) (p + b) :=
      (sameBlock_pair_iff hJ hpJ hp ha (by omega)).mpr (by omega)
    have h := hA' ⟨p + a, by omega⟩ ⟨p + b, by omega⟩ hab
    rw [blockMat_apply_of_eq (i := ⟨p + a, by omega⟩) (j := ⟨p + b, by omega⟩) rfl rfl, h]
    simp [one_apply, Fin.ext_iff]
  · intro h
    refine ⟨hA, fun i k hik => ?_⟩
    rw [sameBlock_joinCuts_iff hJ i.isLt k.isLt] at hik
    rcases hik with hik | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain rfl : i = k := Fin.ext hik
      rw [one_apply_eq]
      by_cases hiJ : (i : ℕ) ∈ J
      · have hi1 : 1 ≤ (i : ℕ) := (hJn _ hiJ).1
        have hJ' : (i : ℕ) - 1 + 1 ∈ J := by rwa [Nat.sub_add_cancel hi1]
        have := congrFun (congrFun (h (i - 1) hJ') 1) 1
        rwa [blockMat_apply_of_eq (i := i) (j := i) (by simp; omega) (by simp; omega),
          one_apply_eq] at this
      · by_cases hi1 : (i : ℕ) + 1 ∈ J
        · have := congrFun (congrFun (h i hi1) 0) 0
          rwa [blockMat_apply_of_eq (i := i) (j := i) (by simp) (by simp), one_apply_eq] at this
        · exact apply_self_eq_one_of_singleton hK hJ hA i hiJ hi1
    · have hJ' : (i : ℕ) + 1 ∈ J := by rwa [← h1]
      have := congrFun (congrFun (h i hJ') 0) 1
      rw [blockMat_apply_of_eq (i := i) (j := k) (by simp) (by simp [h1]),
        one_apply_ne (by decide)] at this
      rw [this, one_apply_ne (Fin.ne_of_val_ne (by omega))]
    · have hJ' : (k : ℕ) + 1 ∈ J := by rwa [← h1]
      have := congrFun (congrFun (h k hJ') 1) 0
      rw [blockMat_apply_of_eq (i := i) (j := k) (by simp [h1]) (by simp),
        one_apply_ne (by decide)] at this
      rw [this, one_apply_ne (Fin.ne_of_val_ne (by omega))]

theorem mul_apply_superdiag {A B : SpecialLinearGroup (Fin n) K} (hA : A ∈ unitriangular n K)
    (hB : B ∈ unitriangular n K) (p : ℕ) (hp : p + 1 < n) :
    ((A * B : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨p, by omega⟩
        ⟨p + 1, hp⟩ =
      (A : Matrix (Fin n) (Fin n) K) ⟨p, by omega⟩ ⟨p + 1, hp⟩ +
        (B : Matrix (Fin n) (Fin n) K) ⟨p, by omega⟩ ⟨p + 1, hp⟩ := by
  have hne : (⟨p, by omega⟩ : Fin n) ≠ ⟨p + 1, hp⟩ := fun h => by
    simpa using congrArg Fin.val h
  rw [SpecialLinearGroup.coe_mul, mul_apply, Fintype.sum_eq_add _ _ hne fun k hk => ?_]
  · rw [hA.2, hB.2, one_mul, mul_one, add_comm]
  · rcases lt_or_gt_of_ne hk.1 with h | h
    · rw [hA.1 _ _ h, zero_mul]
    · have h' : (⟨p + 1, hp⟩ : Fin n) < k := by
        have h1 : p < (k : ℕ) := h
        have h2 : (k : ℕ) ≠ p + 1 := fun e => hk.2 (Fin.ext e)
        exact Fin.lt_def.mpr (by simp only; omega)
      rw [hB.1 _ _ h', mul_zero]

theorem card_center_unitriangular [Finite K] (hK : Nat.card K = 2) (hn : 2 ≤ n) :
    Nat.card (Subgroup.center (unitriangular n K)) = 2 := by
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin n := ⟨n - 1, by omega⟩ with hi₁
  have h01 : i₀ < i₁ := Fin.lt_def.mpr (by simp only [hi₀, hi₁]; omega)
  have hcomm : ∀ x ∈ Subgroup.center (unitriangular n K), ∀ (i : ℕ) (hi : i + 1 < n),
      single (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩ (1 : K) *
          (((x : unitriangular n K) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (((x : unitriangular n K) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          single (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩ (1 : K) := by
    intro x hx i hi
    have hlt : (⟨i, by omega⟩ : Fin n) < ⟨i + 1, hi⟩ := Fin.lt_def.mpr (by simp)
    have hc := Subgroup.mem_center_iff.mp hx ⟨_, transvection_mem_unitriangular hlt 1⟩
    have hm := congrArg (fun y : unitriangular n K =>
      ((y : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) hc
    simp only [Subgroup.coe_mul, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.transvection_coe, add_mul, mul_add, one_mul, mul_one] at hm
    exact add_left_cancel hm
  have hentry : ∀ x ∈ Subgroup.center (unitriangular n K), ∀ a b : Fin n, a ≠ b →
      ¬ (a = i₀ ∧ b = i₁) →
      (((x : unitriangular n K) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) a b =
        0 := by
    intro x hx a b hab hab'
    rcases lt_or_gt_of_ne hab with h | h
    · have hab'' : (a : ℕ) < b := h
      by_cases ha : (a : ℕ) = 0
      · have hb : (b : ℕ) + 1 < n := by
          have hb1 : (b : ℕ) ≠ n - 1 := fun e => hab' ⟨Fin.ext ha, Fin.ext e⟩
          have := b.isLt
          omega
        have h1 := congrFun (congrFun (hcomm x hx b hb) a) ⟨b + 1, hb⟩
        have hane : a ≠ (⟨b, by omega⟩ : Fin n) := fun e => by
          have := congrArg Fin.val e
          simp only at this
          omega
        rw [single_mul_apply_of_ne _ _ _ _ _ hane, mul_single_apply_same, mul_one] at h1
        rw [← h1]
      · have h1 := congrFun (congrFun (hcomm x hx (a - 1) (by omega)) ⟨a - 1, by omega⟩) b
        have hbne : b ≠ (⟨a - 1 + 1, by omega⟩ : Fin n) := fun e => by
          have := congrArg Fin.val e
          simp only at this
          omega
        rw [single_mul_apply_same, one_mul, mul_single_apply_of_ne _ _ _ _ _ hbne] at h1
        rw [show a = (⟨a - 1 + 1, by omega⟩ : Fin n) from Fin.ext (by simp only; omega)]
        exact h1
    · exact (x : unitriangular n K).2.1 a b h
  let χ : Subgroup.center (unitriangular n K) → K := fun x =>
    ((((x : unitriangular n K)) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i₀ i₁
  have hinj : Function.Injective χ := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [(x : unitriangular n K).2.2 a, (y : unitriangular n K).2.2 a]
    · by_cases hab' : a = i₀ ∧ b = i₁
      · obtain ⟨rfl, rfl⟩ := hab'
        exact hxy
      · rw [hentry x x.2 a b hab hab', hentry y y.2 a b hab hab']
  have hsurj : Function.Surjective χ := by
    intro c
    refine ⟨⟨⟨SpecialLinearGroup.transvection h01.ne c, transvection_mem_unitriangular h01 c⟩,
      ?_⟩, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul, SpecialLinearGroup.coe_mul,
        SpecialLinearGroup.transvection_coe, add_mul, mul_add, one_mul, mul_one]
      congr 1
      ext a b
      have hy := (y : unitriangular n K).2
      by_cases hb : b = i₁
      · subst hb
        rw [mul_single_apply_same]
        by_cases ha : a = i₀
        · subst ha
          rw [single_mul_apply_same, hy.2, hy.2, one_mul, mul_one]
        · rw [single_mul_apply_of_ne _ _ _ _ _ ha]
          have hlt : i₀ < a := by
            have : (a : ℕ) ≠ 0 := fun e => ha (Fin.ext e)
            exact Fin.lt_def.mpr (by simp only [hi₀]; omega)
          rw [hy.1 _ _ hlt, zero_mul]
      · rw [mul_single_apply_of_ne _ _ _ _ _ hb]
        by_cases ha : a = i₀
        · subst ha
          rw [single_mul_apply_same]
          have hlt : b < i₁ := by
            have : (b : ℕ) ≠ n - 1 := fun e => hb (Fin.ext e)
            have := b.isLt
            exact Fin.lt_def.mpr (by simp only [hi₁]; omega)
          rw [hy.1 _ _ hlt, mul_zero]
        · rw [single_mul_apply_of_ne _ _ _ _ _ ha]
    · simp [χ, SpecialLinearGroup.transvection_coe, one_apply_ne h01.ne]
  rw [Nat.card_congr (Equiv.ofBijective χ ⟨hinj, hsurj⟩), hK]

end SteinbergCH

end CFSG.QuasithinUnique
