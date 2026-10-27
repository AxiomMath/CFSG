module

public import CFSG.LieType.Universal.Unitary.Roots.Generation
public import CFSG.ClassicalGroups.Unitary.Form
public import CFSG.HardMathSupport.Lang.AlphaThree.UnitarySupport
public import CFSG.HardMathSupport.Lang.AlphaThree.UnitaryBlocks

public section

namespace CFSG.HardMathSupport.Lang.AlphaThree

open Matrix CFSG.LieType.Universal.Unitary

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [CharP F 2] {σ : F ≃+* F} {n : ℕ}

theorem one_add_one_eq_zero : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1

theorem one_mem_traceZero : (1 : F) ∈ traceZero σ := by
  rw [mem_traceZero, map_one, one_add_one_eq_zero]

variable (σ) in
@[expose] def eOne : traceZero σ := ⟨1, one_mem_traceZero⟩

theorem eOne_add_eOne : eOne σ + eOne σ = 0 := Subtype.ext one_add_one_eq_zero

theorem single_add_self (i j : Fin n) : single i j (1 : F) + single i j 1 = 0 := by
  rw [← Matrix.single_add, one_add_one_eq_zero, Matrix.single_zero]

variable (σ) in
@[expose] noncomputable def sEl (hn : 9 ≤ n) (l : Fin 4) : SU σ n :=
  longRootHom σ (lo_ne_rev_lo hn l) (Multiplicative.ofAdd (eOne σ))

variable (σ) in
@[expose] noncomputable def tEl (hn : 9 ≤ n) (l : Fin 4) : SU σ n :=
  longRootHom σ (hi_ne_rev_hi hn l) (Multiplicative.ofAdd (eOne σ))

variable (σ) in
@[expose] noncomputable def hEl (hn : 9 ≤ n) (l : Fin 4) : SU σ n := sEl σ hn l * tEl σ hn l

@[expose] def aMat (hn : 9 ≤ n) (l : Fin 4) : Matrix (Fin n) (Fin n) F :=
  single (lo hn l) (hi hn l) 1

@[expose] def bMat (hn : 9 ≤ n) (l : Fin 4) : Matrix (Fin n) (Fin n) F :=
  single (hi hn l) (lo hn l) 1

theorem sEl_mat (hn : 9 ≤ n) (l : Fin 4) :
    (((sEl σ hn l : SU σ n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + aMat hn l := rfl

theorem tEl_mat (hn : 9 ≤ n) (l : Fin 4) :
    (((tEl σ hn l : SU σ n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + bMat hn l := by
  change longRootMatrix (hi hn l) (1 : F) = _
  rw [longRootMatrix, rev_hi]
  rfl

theorem aMat_mul_aMat (hn : 9 ≤ n) (l : Fin 4) : aMat (F := F) hn l * aMat hn l = 0 := by
  simp only [aMat]
  rw [single_mul_single_of_ne _ _ _ _ (hi_ne_lo hn l)]

theorem bMat_mul_bMat (hn : 9 ≤ n) (l : Fin 4) : bMat (F := F) hn l * bMat hn l = 0 := by
  simp only [bMat]
  rw [single_mul_single_of_ne _ _ _ _ (lo_ne_hi hn l l)]

theorem aMat_mul_bMat (hn : 9 ≤ n) (l : Fin 4) :
    aMat (F := F) hn l * bMat hn l = single (lo hn l) (lo hn l) 1 := by
  simp only [aMat, bMat]
  rw [single_mul_single_same, mul_one]

theorem bMat_mul_aMat (hn : 9 ≤ n) (l : Fin 4) :
    bMat (F := F) hn l * aMat hn l = single (hi hn l) (hi hn l) 1 := by
  simp only [aMat, bMat]
  rw [single_mul_single_same, mul_one]

theorem aba (hn : 9 ≤ n) (l : Fin 4) :
    aMat (F := F) hn l * bMat hn l * aMat hn l = aMat hn l := by
  rw [aMat_mul_bMat]
  simp only [aMat]
  rw [single_mul_single_same, mul_one]

theorem bab (hn : 9 ≤ n) (l : Fin 4) :
    bMat (F := F) hn l * aMat hn l * bMat hn l = bMat hn l := by
  rw [bMat_mul_aMat]
  simp only [bMat]
  rw [single_mul_single_same, mul_one]

theorem sEl_mul_self (hn : 9 ≤ n) (l : Fin 4) : sEl σ hn l * sEl σ hn l = 1 := by
  rw [sEl, ← map_mul, ← ofAdd_add, eOne_add_eOne, ofAdd_zero, map_one]

theorem tEl_mul_self (hn : 9 ≤ n) (l : Fin 4) : tEl σ hn l * tEl σ hn l = 1 := by
  rw [tEl, ← map_mul, ← ofAdd_add, eOne_add_eOne, ofAdd_zero, map_one]

theorem braid_SU (hn : 9 ≤ n) (l : Fin 4) :
    sEl σ hn l * tEl σ hn l * sEl σ hn l = tEl σ hn l * sEl σ hn l * tEl σ hn l := by
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, sEl_mat, tEl_mat]
  exact braid_of_rel _ _ (single_add_self _ _) (single_add_self _ _) (aMat_mul_aMat hn l)
    (bMat_mul_bMat hn l) (aba hn l) (bab hn l)

theorem hEl_pow_three (hn : 9 ≤ n) (l : Fin 4) : hEl σ hn l ^ 3 = 1 := by
  have hs := sEl_mul_self (σ := σ) hn l
  have ht := tEl_mul_self (σ := σ) hn l
  have hb := braid_SU (σ := σ) hn l
  set s := sEl σ hn l
  set t := tEl σ hn l
  rw [hEl]
  calc (s * t) ^ 3 = (s * t * s) * (t * s * t) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (s * t * s) * (s * t * s) := by rw [hb]
    _ = s * t * (s * s) * t * s := by simp only [mul_assoc]
    _ = s * (t * t) * s := by rw [hs, mul_one]; simp only [mul_assoc]
    _ = 1 := by rw [ht, mul_one, hs]

@[expose] def mMat (hn : 9 ≤ n) (l : Fin 4) : Matrix (Fin n) (Fin n) F :=
  aMat hn l + bMat hn l + single (lo hn l) (lo hn l) 1

theorem hEl_mat (hn : 9 ≤ n) (l : Fin 4) :
    (((hEl σ hn l : SU σ n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + mMat hn l := by
  rw [hEl]
  simp only [Subgroup.coe_mul, Units.val_mul, sEl_mat, tEl_mat]
  have : (1 + aMat (F := F) hn l) * (1 + bMat hn l) = 1 + (aMat hn l + bMat hn l + aMat hn l * bMat hn l) := by
    noncomm_ring
  rw [this, aMat_mul_bMat]
  rfl

theorem suppIn_aMat (hn : 9 ≤ n) (l : Fin 4) : SuppIn (Bset hn l) (aMat (F := F) hn l) :=
  suppIn_single (Or.inl rfl) (Or.inr rfl) _

theorem suppIn_mMat (hn : 9 ≤ n) (l : Fin 4) : SuppIn (Bset hn l) (mMat (F := F) hn l) :=
  ((suppIn_aMat hn l).add (suppIn_single (Or.inr rfl) (Or.inl rfl) _)).add
    (suppIn_single (Or.inl rfl) (Or.inl rfl) _)

theorem commute_of_mat {x y : SU σ n}
    (h : Commute ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) : Commute x y := by
  change x * y = y * x
  refine Subtype.ext (Units.ext ?_)
  simpa only [Subgroup.coe_mul, Units.val_mul] using h.eq

theorem commute_sEl_hEl (hn : 9 ≤ n) {l j : Fin 4} (h : l ≠ j) :
    Commute (sEl σ hn l) (hEl σ hn j) := by
  refine commute_of_mat ?_
  rw [sEl_mat, hEl_mat]
  exact commute_one_add_of_disjoint (disjoint_Bset hn h) (suppIn_aMat hn l) (suppIn_mMat hn j)

theorem commute_hEl_hEl (hn : 9 ≤ n) (l j : Fin 4) : Commute (hEl σ hn l) (hEl σ hn j) := by
  by_cases h : l = j
  · subst h
    exact Commute.refl _
  · refine commute_of_mat ?_
    rw [hEl_mat, hEl_mat]
    exact commute_one_add_of_disjoint (disjoint_Bset hn h) (suppIn_mMat hn l) (suppIn_mMat hn j)

theorem sEl_inv (hn : 9 ≤ n) (l : Fin 4) : (sEl σ hn l)⁻¹ = sEl σ hn l :=
  inv_eq_of_mul_eq_one_right (sEl_mul_self hn l)

theorem tEl_inv (hn : 9 ≤ n) (l : Fin 4) : (tEl σ hn l)⁻¹ = tEl σ hn l :=
  inv_eq_of_mul_eq_one_right (tEl_mul_self hn l)

theorem sEl_hEl_inv (hn : 9 ≤ n) (l : Fin 4) :
    sEl σ hn l * hEl σ hn l * (sEl σ hn l)⁻¹ = (hEl σ hn l)⁻¹ := by
  rw [hEl, _root_.mul_inv_rev, sEl_inv, tEl_inv]
  have hs := sEl_mul_self (σ := σ) hn l
  simp only [mul_assoc]
  rw [← mul_assoc (sEl σ hn l) (sEl σ hn l), hs, one_mul]

theorem sEl_hEl_fix (hn : 9 ≤ n) {l j : Fin 4} (h : l ≠ j) :
    sEl σ hn l * hEl σ hn j * (sEl σ hn l)⁻¹ = hEl σ hn j := by
  rw [(commute_sEl_hEl hn h).eq, mul_assoc, mul_inv_cancel, mul_one]

theorem hEl_ne_one (hn : 9 ≤ n) (l : Fin 4) : hEl σ hn l ≠ 1 := by
  intro h
  have h1 := congrArg (fun x : SU σ n => ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    (hi hn l) (lo hn l)) h
  simp only [hEl_mat, OneMemClass.coe_one, Units.val_one, mMat, aMat, bMat, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply] at h1
  have e1 := hi_ne_lo hn l
  have e2 := lo_ne_hi hn l l
  simp [e1, e2] at h1

theorem commute_pair_of_supp (hn : 9 ≤ n) {x : SU σ n} {N : Matrix (Fin n) (Fin n) F} {a b : Fin n}
    (hx : ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + N)
    (hN : SuppIn {a, Fin.rev a, b, Fin.rev b} N) :
    ∃ j k : Fin 4, j ≠ k ∧ Commute x (hEl σ hn j) ∧ Commute x (hEl σ hn k) := by
  obtain ⟨l₁, l₂, hne, g₁, g₂⟩ := exists_two_good hn a b
  have key : ∀ l, (a ∉ Bset hn l ∧ b ∉ Bset hn l) → Commute x (hEl σ hn l) := by
    intro l hl
    refine commute_of_mat ?_
    rw [hx, hEl_mat]
    refine commute_one_add_of_disjoint ?_ hN (suppIn_mMat hn l)
    rw [Set.disjoint_left]
    intro c hc hcB
    rcases hc with rfl | rfl | rfl | rfl
    · exact hl.1 hcB
    · exact hl.1 ((rev_mem_Bset hn).1 hcB)
    · exact hl.2 hcB
    · exact hl.2 ((rev_mem_Bset hn).1 hcB)
  exact ⟨l₁, l₂, hne, key _ g₁, key _ g₂⟩

theorem closure_pairCentralizing_eq_top (hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ)
    (hn : 9 ≤ n) :
    Subgroup.closure {x : SU σ n | ∃ j k : Fin 4, j ≠ k ∧ Commute x (hEl σ hn j) ∧
      Commute x (hEl σ hn k)} = ⊤ := by
  refine eq_top_of_rootElements_le hσ.invol hσ.exists_traceZero hσ.trace_surj
    (fun x hx => hσ.exists_norm hx) (by omega) _ ?_ ?_ ?_
  · intro i j hij hi hj hji c
    refine Subgroup.subset_closure (commute_pair_of_supp hn (a := i) (b := j)
      (N := single i j (c.toAdd) - single (Fin.rev j) (Fin.rev i) (σ c.toAdd)) ?_ ?_)
    · rw [coe_rootHom]
      exact add_sub_assoc _ _ _
    · exact (suppIn_single (by simp) (by simp) _).sub (suppIn_single (by simp) (by simp) _)
  · intro i hi c
    refine Subgroup.subset_closure (commute_pair_of_supp hn (a := i) (b := i)
      (N := single i (Fin.rev i) (c.toAdd : F)) ?_ ?_)
    · rw [coe_longRootHom]
      rfl
    · exact suppIn_single (by simp) (by simp) _
  · intro i k hi hik hk g hg
    obtain ⟨a, b, -, hgm⟩ := hg
    refine Subgroup.subset_closure (commute_pair_of_supp hn (a := i) (b := k)
      (N := single i k a - single k (Fin.rev i) (σ a) + single i (Fin.rev i) b) ?_ ?_)
    · rw [hgm, heisenbergMatrix]
      abel
    · refine ((suppIn_single (by simp) (by simp) _).sub (suppIn_single (by simp) (by simp) _)).add
        (suppIn_single (by simp) (by simp) _)

end CFSG.HardMathSupport.Lang.AlphaThree
