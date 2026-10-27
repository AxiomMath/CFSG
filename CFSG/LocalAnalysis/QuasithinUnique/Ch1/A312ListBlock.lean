module

import CFSG.LocalAnalysis.QuasithinUnique.SteinbergCHBinaryFlagBlocks
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Block

variable {n : ℕ} {K : Type*} [Semiring K]

theorem sum_block {a m : ℕ} (h : a + m ≤ n) {M : Type*} [AddCommMonoid M] (f : Fin n → M)
    (hf : ∀ k : Fin n, ((k : ℕ) < a ∨ a + m ≤ (k : ℕ)) → f k = 0) :
    ∑ k : Fin n, f k = ∑ i : Fin m, f ⟨a + i, by have := i.isLt; omega⟩ := by
  classical
  have h1 : ∑ k : Fin n, f k =
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => a ≤ (k : ℕ) ∧ (k : ℕ) < a + m), f k := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · rfl
    · exact hf k (by omega)
  rw [h1]
  symm
  refine Finset.sum_bij' (fun i _ => (⟨a + i, by have := i.isLt; omega⟩ : Fin n))
    (fun k hk => (⟨k - a, by simp at hk; omega⟩ : Fin m)) ?_ ?_ ?_ ?_ ?_
  · intro i _
    simp
  · intro k hk
    simp
  · intro i _
    ext
    simp
  · intro k hk
    simp at hk
    ext
    simp
    omega
  · intro i _
    rfl

@[expose] def blkAt (a m : ℕ) (h : a + m ≤ n) (A : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin m) (Fin m) K :=
  Matrix.of fun i j => A ⟨a + i, by have := i.isLt; omega⟩ ⟨a + j, by have := j.isLt; omega⟩

omit [Semiring K] in
theorem blkAt_apply (a m : ℕ) (h : a + m ≤ n) (A : Matrix (Fin n) (Fin n) K) (i j : Fin m) :
    blkAt a m h A i j = A ⟨a + i, by have := i.isLt; omega⟩ ⟨a + j, by have := j.isLt; omega⟩ :=
  rfl

theorem blkAt_one (a m : ℕ) (h : a + m ≤ n) : blkAt a m h (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  ext i j
  simp only [blkAt_apply, Matrix.one_apply, Fin.mk.injEq, Nat.add_left_cancel_iff, Fin.val_inj]

theorem blkAt_mul (a m : ℕ) (h : a + m ≤ n) (A B : Matrix (Fin n) (Fin n) K)
    (hA : ∀ r l : Fin n, a ≤ (r : ℕ) → (r : ℕ) < a + m → (l : ℕ) < a → A r l = 0)
    (hB : ∀ k c : Fin n, a + m ≤ (k : ℕ) → a ≤ (c : ℕ) → (c : ℕ) < a + m → B k c = 0) :
    blkAt a m h (A * B) = blkAt a m h A * blkAt a m h B := by
  ext i j
  simp only [blkAt_apply, Matrix.mul_apply]
  have hi := i.isLt
  have hj := j.isLt
  rw [sum_block h (fun k => A ⟨a + i, by omega⟩ k * B k ⟨a + j, by omega⟩)]
  intro k hk
  rcases hk with hk | hk
  · rw [hA _ _ (by show a ≤ a + (i : ℕ); omega) (by show a + (i : ℕ) < a + m; omega) hk,
      zero_mul]
  · rw [hB _ _ hk (by show a ≤ a + (j : ℕ); omega) (by show a + (j : ℕ) < a + m; omega),
      mul_zero]

end Block

section Hom

variable {n : ℕ} {K : Type*} [Field K]

@[expose] def BlockLeft (H : Subgroup (SpecialLinearGroup (Fin n) K)) (a m : ℕ) : Prop :=
  ∀ g ∈ H, ∀ r l : Fin n, a ≤ (r : ℕ) → (r : ℕ) < a + m → (l : ℕ) < a →
    (g : Matrix (Fin n) (Fin n) K) r l = 0

@[expose] def BlockRight (H : Subgroup (SpecialLinearGroup (Fin n) K)) (a m : ℕ) : Prop :=
  ∀ g ∈ H, ∀ k c : Fin n, a + m ≤ (k : ℕ) → a ≤ (c : ℕ) → (c : ℕ) < a + m →
    (g : Matrix (Fin n) (Fin n) K) k c = 0

theorem stabilizer_entries {i : ℕ} {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ stabilizer (flagSpace n K i)) {k l : Fin n} (hl : (l : ℕ) < i) (hk : i ≤ (k : ℕ)) :
    (g : Matrix (Fin n) (Fin n) K) k l = 0 :=
  CFSG.QuasithinUnique.SteinbergCH.apply_eq_zero_of_mem_stabilizer hg hl hk

theorem blockLeft_zero (H : Subgroup (SpecialLinearGroup (Fin n) K)) (m : ℕ) : BlockLeft H 0 m :=
  fun _ _ _ _ _ _ hl => absurd hl (Nat.not_lt_zero _)

theorem blockRight_top (H : Subgroup (SpecialLinearGroup (Fin n) K)) {a m : ℕ} (h : a + m = n) :
    BlockRight H a m := fun _ _ k _ hk _ _ => absurd k.isLt (by omega)

theorem blockLeft_of_stabilizer {H : Subgroup (SpecialLinearGroup (Fin n) K)} {a m : ℕ}
    (h : ∀ g ∈ H, g ∈ stabilizer (flagSpace n K a)) : BlockLeft H a m :=
  fun g hg _ _ hr _ hl => stabilizer_entries (h g hg) hl hr

theorem blockRight_of_stabilizer {H : Subgroup (SpecialLinearGroup (Fin n) K)} {a m : ℕ}
    (h : ∀ g ∈ H, g ∈ stabilizer (flagSpace n K (a + m))) : BlockRight H a m :=
  fun g hg _ _ hk _ hc => stabilizer_entries (h g hg) hc hk

@[expose] noncomputable def blkMon (H : Subgroup (SpecialLinearGroup (Fin n) K)) (a m : ℕ)
    (h : a + m ≤ n) (hL : BlockLeft H a m) (hR : BlockRight H a m) :
    ↥H →* Matrix (Fin m) (Fin m) K where
  toFun g := blkAt a m h (g.1 : Matrix (Fin n) (Fin n) K)
  map_one' := by
    simp only [Subgroup.coe_one]
    exact blkAt_one a m h
  map_mul' g g' := by
    simp only [Subgroup.coe_mul]
    exact blkAt_mul a m h _ _ (hL g.1 g.2) (hR g'.1 g'.2)

theorem blkMon_apply (H : Subgroup (SpecialLinearGroup (Fin n) K)) (a m : ℕ) (h : a + m ≤ n)
    (hL : BlockLeft H a m) (hR : BlockRight H a m) (g : ↥H) :
    blkMon H a m h hL hR g = blkAt a m h (g.1 : Matrix (Fin n) (Fin n) K) := rfl

theorem det_blkMon_eq_one (H : Subgroup (SpecialLinearGroup (Fin n) K)) (a m : ℕ) (h : a + m ≤ n)
    (hL : BlockLeft H a m) (hR : BlockRight H a m) {N : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hNH : N ≤ H) (hN : Group.IsPerfect ↥N) (g : ↥N) :
    (blkMon H a m h hL hR (Subgroup.inclusion hNH g)).det = 1 := by
  let φ : ↥N →* K :=
    (Matrix.detMonoidHom).comp ((blkMon H a m h hL hR).comp (Subgroup.inclusion hNH))
  have hker : (φ.toHomUnits).ker = ⊤ := by
    rw [eq_top_iff, ← hN.commutator_eq_top]
    exact Abelianization.commutator_subset_ker _
  have hg : φ.toHomUnits g = 1 := by
    have : g ∈ (φ.toHomUnits).ker := by rw [hker]; exact Subgroup.mem_top g
    exact this
  have := congrArg Units.val hg
  simpa [φ] using this

@[expose] noncomputable def blkSL (H : Subgroup (SpecialLinearGroup (Fin n) K)) (a m : ℕ)
    (h : a + m ≤ n) (hL : BlockLeft H a m) (hR : BlockRight H a m)
    {N : Subgroup (SpecialLinearGroup (Fin n) K)} (hNH : N ≤ H) (hN : Group.IsPerfect ↥N) :
    ↥N →* SpecialLinearGroup (Fin m) K where
  toFun g := ⟨blkMon H a m h hL hR (Subgroup.inclusion hNH g),
    det_blkMon_eq_one H a m h hL hR hNH hN g⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g g' := Subtype.ext (by
    show blkMon H a m h hL hR (Subgroup.inclusion hNH (g * g')) =
      blkMon H a m h hL hR (Subgroup.inclusion hNH g) *
        blkMon H a m h hL hR (Subgroup.inclusion hNH g')
    rw [map_mul, map_mul])

theorem blkSL_coe (H : Subgroup (SpecialLinearGroup (Fin n) K)) (a m : ℕ) (h : a + m ≤ n)
    (hL : BlockLeft H a m) (hR : BlockRight H a m)
    {N : Subgroup (SpecialLinearGroup (Fin n) K)} (hNH : N ≤ H) (hN : Group.IsPerfect ↥N)
    (g : ↥N) :
    ((blkSL H a m h hL hR hNH hN g : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      blkAt a m h (g.1 : Matrix (Fin n) (Fin n) K) := rfl

end Hom

end CFSG.QuasithinUnique.Vol2Native.A312L
