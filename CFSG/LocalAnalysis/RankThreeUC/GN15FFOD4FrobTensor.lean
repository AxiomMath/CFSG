module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.Quasithin.Background.SmithCurtisBasic

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.Quasithin.SmithCurtis
open scoped Matrix

section FrobTensor

variable {G : Type*} [Group G] {K : Type*} [Field K] (k : Type*) [Field k] [Algebra K k]
  [CharP k 2] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def frobHom (b : ℕ) : K →+* k := (iterateFrobenius k 2 b).comp (algebraMap K k)

theorem frobHom_apply (b : ℕ) (x : K) : frobHom k b x = (algebraMap K k x) ^ 2 ^ b := by
  simp [frobHom, iterateFrobenius_def]

@[expose] def frobTensorMat (M : G →* Matrix ι ι K) (S : Finset ℕ) (g : G) :
    Matrix (S → ι) (S → ι) k :=
  fun x' x => ∏ b : S, frobHom k b (M g (x' b) (x b))

theorem frobTensorMat_one (M : G →* Matrix ι ι K) (S : Finset ℕ) :
    frobTensorMat k M S 1 = 1 := by
  ext x' x
  simp only [frobTensorMat, map_one, Matrix.one_apply]
  by_cases h : x' = x
  · subst h; simp
  · obtain ⟨b, hb⟩ := Function.ne_iff.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [hb])

theorem frobTensorMat_mul (M : G →* Matrix ι ι K) (S : Finset ℕ) (g h : G) :
    frobTensorMat k M S (g * h) = frobTensorMat k M S g * frobTensorMat k M S h := by
  ext x'' x
  simp only [frobTensorMat, Matrix.mul_apply]
  have hL : (∏ b : S, frobHom k b (M (g * h) (x'' b) (x b))) =
      ∑ y : S → ι, ∏ b : S, frobHom k b (M g (x'' b) (y b)) *
        frobHom k b (M h (y b) (x b)) := by
    rw [show (∏ b : S, frobHom k b (M (g * h) (x'' b) (x b))) =
        ∏ b : S, ∑ j : ι, frobHom k b (M g (x'' b) j) * frobHom k b (M h j (x b)) by
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [map_mul, Matrix.mul_apply, map_sum]
      simp only [map_mul]]
    rw [Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ]
  rw [hL]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib]

@[expose] def frobTensorRep (M : G →* Matrix ι ι K) (S : Finset ℕ) :
    Representation k G ((S → ι) → k) where
  toFun g := Matrix.toLin' (frobTensorMat k M S g)
  map_one' := by rw [frobTensorMat_one]; exact Matrix.toLin'_one
  map_mul' g h := by rw [frobTensorMat_mul, Matrix.toLin'_mul]; rfl

theorem frobTensorRep_apply (M : G →* Matrix ι ι K) (S : Finset ℕ) (g : G) (v : (S → ι) → k)
    (x' : S → ι) :
    frobTensorRep k M S g v x' = ∑ x, frobTensorMat k M S g x' x * v x := by
  simp [frobTensorRep, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

theorem finrank_frobTensor (S : Finset ℕ) :
    Module.finrank k ((S → ι) → k) = Fintype.card ι ^ S.card := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fun]
  simp

private def kronMat (S : Finset ℕ) (T : Finset S) (A : Matrix ι ι k) :
    Matrix (S → ι) (S → ι) k :=
  fun x' x => ∏ b : S, if b ∈ T then A (x' b) (x b) else if x' b = x b then 1 else 0

private theorem kronMat_empty (S : Finset ℕ) (A : Matrix ι ι k) : kronMat k S ∅ A = 1 := by
  ext x' x
  simp only [kronMat, Finset.notMem_empty, ↓reduceIte, Matrix.one_apply]
  by_cases h : x' = x
  · subst h; simp
  · obtain ⟨b, hb⟩ := Function.ne_iff.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [hb])

private theorem kronMat_singleton_apply (S : Finset ℕ) (b : S) (A : Matrix ι ι k)
    (y x : S → ι) :
    kronMat k S ({b} : Finset S) A y x =
      A (y b) (x b) * ∏ b' ∈ (Finset.univ.erase b), (if y b' = x b' then 1 else 0) := by
  rw [kronMat, Finset.prod_eq_mul_prod_diff_singleton b]
  · rw [Finset.sdiff_singleton_eq_erase]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun b' hb' => ?_
      rw [Finset.mem_erase] at hb'
      simp [hb'.1]
  · intro hb
    exact absurd (Finset.mem_univ b) hb

private theorem kronMat_singleton_mulVec_apply (S : Finset ℕ) (b : S) (A : Matrix ι ι k)
    (w : (S → ι) → k) (z : S → ι) :
    (kronMat k S ({b} : Finset S) A *ᵥ w) z =
      ∑ j : ι, A (z b) j * w (Function.update z b j) := by
  classical
  rw [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_equiv (Equiv.funSplitAt b ι)
    (fun x => kronMat k S ({b} : Finset S) A z x * w x)
    (fun p => kronMat k S ({b} : Finset S) A z ((Equiv.funSplitAt b ι).symm p) *
      w ((Equiv.funSplitAt b ι).symm p)) (fun x => by rw [Equiv.symm_apply_apply])]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (fun b' : {b' : S // b' ≠ b} => z (b' : S))]
  · rw [kronMat_singleton_apply]
    have h1 : (Equiv.funSplitAt b ι).symm (j, fun b' : {b' : S // b' ≠ b} => z (b' : S)) =
        Function.update z b j := by
      funext b'
      by_cases hb' : b' = b
      · subst hb'; simp [Equiv.funSplitAt]
      · simp [Equiv.funSplitAt, hb']
    rw [h1]
    rw [Finset.prod_eq_one]
    · simp
    · intro b' hb'
      rw [Finset.mem_erase] at hb'
      simp [hb'.1]
  · intro off hoff hne
    rw [kronMat_singleton_apply]
    have hzero : ∃ (b' : S) (hb' : b' ≠ b), off ⟨b', hb'⟩ ≠ z b' := by
      by_contra hcon
      push Not at hcon
      exact hne (funext fun b' => hcon b'.1 b'.2)
    obtain ⟨b', hb', hb'ne⟩ := hzero
    have hb'mem : b' ∈ Finset.univ.erase b := Finset.mem_erase.mpr ⟨hb', Finset.mem_univ _⟩
    have hfac : (if z b' = (Equiv.funSplitAt b ι).symm (j, off) b' then (1 : k) else 0) = 0 := by
      have hsymm : (Equiv.funSplitAt b ι).symm (j, off) b' = off ⟨b', hb'⟩ := by
        simp [Equiv.funSplitAt, hb']
      rw [hsymm]
      exact if_neg (fun hh => hb'ne hh.symm)
    rw [Finset.prod_eq_zero hb'mem hfac]
    simp
  · intro hb
    exact absurd (Finset.mem_univ _) hb

private def subsetExp (S : Finset ℕ) (T : Finset S) : ℕ := ∑ b ∈ T, 2 ^ b.1

private theorem subsetExp_injective (S : Finset ℕ) : Function.Injective (subsetExp S) := by
  intro T T' h
  have h' : ∑ j ∈ T.map (Function.Embedding.subtype (fun x : ℕ => x ∈ S)), 2 ^ j =
      ∑ j ∈ T'.map (Function.Embedding.subtype (fun x : ℕ => x ∈ S)), 2 ^ j := by
    simpa [subsetExp, Finset.sum_map] using h
  exact Finset.map_injective _ (Finset.geomSum_injective (le_refl 2) h')

private theorem subsetExp_lt {n : ℕ} {S : Finset ℕ} (hS : ∀ b ∈ S, b < n) (T : Finset S) :
    subsetExp S T < 2 ^ n := by
  calc subsetExp S T ≤ subsetExp S Finset.univ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
          (by intro x _ _; positivity)
    _ = ∑ b : S, 2 ^ b.1 := by simp [subsetExp]
    _ = ∑ b ∈ S, 2 ^ b := Finset.sum_coe_sort S (fun b => 2 ^ b)
    _ < 2 ^ n := Nat.geomSum_lt (le_refl 2) hS

private theorem sum_pow_two_eq_pred {n : ℕ} {T : Finset ℕ} (hT : ∀ b ∈ T, b < n) :
    (∑ b ∈ T, 2 ^ b = 2 ^ n - 1) ↔ T = Finset.range n := by
  have hrange : ∑ b ∈ Finset.range n, 2 ^ b = 2 ^ n - 1 := by
    have := Nat.geomSum_eq (le_refl 2) n
    simpa using this
  constructor
  · intro h
    refine Finset.geomSum_injective (le_refl 2) ?_
    show (∑ b ∈ T, 2 ^ b) = ∑ b ∈ Finset.range n, 2 ^ b
    rw [h, hrange]
  · rintro rfl
    exact hrange

private def sliceVec (S : Finset ℕ) (b : S) (z : S → ι) (v : ι → k) : (S → ι) → k :=
  ∑ j : ι, v j • Pi.single (Function.update z b j) 1

private theorem pi_single_update_left (S : Finset ℕ) (b : S) (z y : S → ι) (j j' : ι) :
    (Pi.single (Function.update z b j) (1 : k) : (S → ι) → k) (Function.update y b j') =
      if j' = j ∧ (∀ b' : S, b' ≠ b → y b' = z b') then (1 : k) else 0 := by
  rw [Pi.single_apply]
  by_cases hjj : j' = j
  · rw [hjj]
    by_cases hzy : ∀ b' : S, b' ≠ b → y b' = z b'
    · have heq : Function.update y b j = Function.update z b j := by
        funext b'
        by_cases hb' : b' = b
        · subst hb'; simp
        · rw [Function.update_apply, if_neg hb', Function.update_apply, if_neg hb']
          exact hzy b' hb'
      rw [if_pos heq, if_pos ⟨rfl, hzy⟩]
    · have heq : Function.update y b j ≠ Function.update z b j := by
        intro heq
        apply hzy
        intro b' hb'
        have := congrFun heq b'
        simpa [Function.update_apply, hb'] using this
      rw [if_neg heq, if_neg (fun h => hzy h.2)]
  · have heq : Function.update y b j' ≠ Function.update z b j := by
      intro heq
      exact hjj (by simpa using congrFun heq b)
    rw [if_neg heq, if_neg (fun h => hjj h.1)]

private theorem pi_single_update_right (S : Finset ℕ) (b : S) (z y : S → ι) (j : ι) :
    (Pi.single (Function.update z b j) (1 : k) : (S → ι) → k) y =
      if j = y b ∧ (∀ b' : S, b' ≠ b → y b' = z b') then (1 : k) else 0 := by
  have h := pi_single_update_left k S b z y j (y b)
  rw [Function.update_eq_self] at h
  simpa [eq_comm] using h

private theorem sliceVec_single (S : Finset ℕ) (b : S) (z : S → ι) (j : ι) :
    sliceVec k S b z (Pi.single j 1) = Pi.single (Function.update z b j) 1 := by
  rw [sliceVec, Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    rw [Pi.single_eq_of_ne hj']
    simp
  · simp

private theorem sliceVec_add (S : Finset ℕ) (b : S) (z : S → ι) (v w : ι → k) :
    sliceVec k S b z (v + w) = sliceVec k S b z v + sliceVec k S b z w := by
  funext x
  simp only [sliceVec, Pi.add_apply, Pi.add_apply, add_smul, Finset.sum_add_distrib]

private theorem sliceVec_smul (S : Finset ℕ) (b : S) (z : S → ι) (a : k) (v : ι → k) :
    sliceVec k S b z (a • v) = a • sliceVec k S b z v := by
  funext x
  simp only [sliceVec, Pi.smul_apply, Finset.sum_apply]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_eq_mul]
  ring

private theorem kronMat_singleton_mulVec_single (S : Finset ℕ) (b : S) (A : Matrix ι ι k)
    (z y : S → ι) (j : ι) :
    (kronMat k S ({b} : Finset S) A *ᵥ Pi.single (Function.update z b j) 1) y =
      ∑ j' : ι, A j' j *
        ((Pi.single (Function.update z b j') (1 : k) : (S → ι) → k) y) := by
  rw [kronMat_singleton_mulVec_apply]
  by_cases hzy : ∀ b' : S, b' ≠ b → y b' = z b'
  · have hL : ∀ j' : ι,
        (Pi.single (Function.update z b j) (1 : k) : (S → ι) → k) (Function.update y b j') =
        if j' = j then (1 : k) else 0 := by
      intro j'
      rw [pi_single_update_left k S b z y j j']
      by_cases h : j' = j
      · rw [if_pos ⟨h, hzy⟩, if_pos h]
      · rw [if_neg (fun hh => h hh.1), if_neg h]
    have hR : ∀ j' : ι,
        (Pi.single (Function.update z b j') (1 : k) : (S → ι) → k) y =
        if j' = y b then (1 : k) else 0 := by
      intro j'
      rw [pi_single_update_right k S b z y j']
      by_cases h : j' = y b
      · rw [if_pos ⟨h, hzy⟩, if_pos h]
      · rw [if_neg (fun hh => h hh.1), if_neg h]
    simp only [hL, hR]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl, mul_one]
      rw [Finset.sum_eq_single (y b)]
      · rw [if_pos rfl, mul_one]
      · intro j' _ hj'
        rw [if_neg hj', mul_zero]
      · simp
    · intro j' _ hj'
      rw [if_neg hj', mul_zero]
    · simp
  · have hL : ∀ j' : ι,
        (Pi.single (Function.update z b j) (1 : k) : (S → ι) → k) (Function.update y b j') = 0 := by
      intro j'
      rw [pi_single_update_left k S b z y j j']
      rw [if_neg (fun hh => hzy hh.2)]
    have hR : ∀ j' : ι,
        (Pi.single (Function.update z b j') (1 : k) : (S → ι) → k) y = 0 := by
      intro j'
      rw [pi_single_update_right k S b z y j']
      rw [if_neg (fun hh => hzy hh.2)]
    simp only [hL, hR, mul_zero, Finset.sum_const_zero]

private theorem kronMat_singleton_mulVec_sliceVec (S : Finset ℕ) (b : S) (A : Matrix ι ι k)
    (z : S → ι) (v : ι → k) :
    kronMat k S ({b} : Finset S) A *ᵥ sliceVec k S b z v = sliceVec k S b z (A *ᵥ v) := by
  have hsingle : ∀ j : ι, kronMat k S ({b} : Finset S) A *ᵥ
      Pi.single (Function.update z b j) 1 =
      ∑ j' : ι, A j' j • Pi.single (Function.update z b j') (1 : k) := by
    intro j
    funext y
    rw [kronMat_singleton_mulVec_single k S b A z y j, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
  calc kronMat k S ({b} : Finset S) A *ᵥ sliceVec k S b z v
      = kronMat k S ({b} : Finset S) A *ᵥ
          (∑ j, v j • Pi.single (Function.update z b j) (1 : k)) := by rw [sliceVec]
    _ = ∑ j, v j • (kronMat k S ({b} : Finset S) A *ᵥ
          Pi.single (Function.update z b j) (1 : k)) := by
        rw [Matrix.mulVec_sum]
        simp only [Matrix.mulVec_smul]
    _ = ∑ j, v j • ∑ j', A j' j • Pi.single (Function.update z b j') (1 : k) := by
        simp only [hsingle]
    _ = ∑ j', (∑ j, v j * A j' j) • Pi.single (Function.update z b j') (1 : k) := by
        simp_rw [Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul]
    _ = ∑ j', (A *ᵥ v) j' • Pi.single (Function.update z b j') (1 : k) := by
        refine Finset.sum_congr rfl fun j' _ => ?_
        congr 1
        rw [Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = sliceVec k S b z (A *ᵥ v) := by rw [sliceVec]

private theorem kronMat_apply_eq_prod (S : Finset ℕ) (T : Finset S) (A : Matrix ι ι k)
    (x' x : S → ι) :
    kronMat k S T A x' x =
      (∏ b ∈ T, A (x' b) (x b)) * ∏ b ∈ Tᶜ, (if x' b = x b then 1 else 0) := by
  rw [kronMat, ← Finset.prod_mul_prod_compl T]
  congr 1
  · refine Finset.prod_congr rfl fun b hb => ?_
    simp [hb]
  · refine Finset.prod_congr rfl fun b hb => ?_
    have hb' : b ∉ T := Finset.mem_compl.mp hb
    simp [hb']

private theorem matrix_map_apply_algebraMap (A : Matrix ι ι K) (i j : ι) :
    (A.map (algebraMap K k)) i j = algebraMap K k (A i j) := rfl

private theorem frobTensorMat_eq_sum (M : G →* Matrix ι ι K) (S : Finset ℕ)
    (A : Matrix ι ι K) (hA : ∀ a b, A a b = 0 ∨ A a b = 1)
    (l : K → G) (hl : ∀ c, M (l c) = 1 + c • A) (c : K) (x' x : S → ι) :
    frobTensorMat k M S (l c) x' x =
      ∑ T : Finset S, (algebraMap K k c) ^ subsetExp S T *
        kronMat k S T (A.map (algebraMap K k)) x' x := by
  rw [frobTensorMat, hl]
  have hfac : ∀ b : S,
      frobHom k b ((1 + c • A : Matrix ι ι K) (x' b) (x b)) =
        (algebraMap K k c) ^ 2 ^ (b : ℕ) * (A.map (algebraMap K k)) (x' b) (x b) +
          (if x' b = x b then 1 else 0) := by
    intro b
    have hA' : frobHom k b (A (x' b) (x b)) = algebraMap K k (A (x' b) (x b)) := by
      rcases hA (x' b) (x b) with h0 | h1
      · rw [h0]; simp [frobHom]
      · rw [h1]; simp [frobHom]
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_add, map_mul,
      frobHom_apply, hA']
    by_cases h : x' b = x b
    · rw [if_pos h, map_one, if_pos h, frobHom_apply, matrix_map_apply_algebraMap]
      ring
    · rw [if_neg h, map_zero, if_neg h, frobHom_apply, matrix_map_apply_algebraMap]
      ring
  rw [Finset.prod_congr rfl fun b _ => hfac b]
  rw [Fintype.prod_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [kronMat_apply_eq_prod, subsetExp]
  ring

private theorem frobTensorRep_eq_sum (M : G →* Matrix ι ι K) (S : Finset ℕ)
    (A : Matrix ι ι K) (hA : ∀ a b, A a b = 0 ∨ A a b = 1)
    (l : K → G) (hl : ∀ c, M (l c) = 1 + c • A) (w : (S → ι) → k) (c : K) :
    frobTensorRep k M S (l c) w =
      ∑ T : Finset S, (algebraMap K k c) ^ subsetExp S T •
        (kronMat k S T (A.map (algebraMap K k)) *ᵥ w) := by
  funext x'
  rw [frobTensorRep_apply]
  have hR : (∑ T : Finset S, (algebraMap K k c) ^ subsetExp S T •
      (kronMat k S T (A.map (algebraMap K k)) *ᵥ w)) x'
      = ∑ T : Finset S, (algebraMap K k c) ^ subsetExp S T *
        ∑ x, kronMat k S T (A.map (algebraMap K k)) x' x * w x := by
    simp [Finset.sum_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
  rw [hR]
  have hL : (∑ x : S → ι, frobTensorMat k M S (l c) x' x * w x)
      = ∑ x : S → ι, (∑ T : Finset S, (algebraMap K k c) ^ subsetExp S T *
        kronMat k S T (A.map (algebraMap K k)) x' x) * w x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [frobTensorMat_eq_sum (k := k) (M := M) (S := S) (A := A) hA l hl c x' x]
  rw [hL]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

private theorem kronMat_mem_of_fixed_mod [Fintype K] {n : ℕ} (hK : Fintype.card K = 2 ^ n)
    (M : G →* Matrix ι ι K) (S : Finset ℕ) (hS : ∀ b ∈ S, b < n)
    (A : Matrix ι ι K) (hA : ∀ a b, A a b = 0 ∨ A a b = 1)
    (l : K → G) (hl : ∀ c, M (l c) = 1 + c • A)
    (W : Submodule k ((S → ι) → k)) (w : (S → ι) → k)
    (hW : ∀ c, frobTensorRep k M S (l c) w - w ∈ W) :
    ∀ T : Finset S, T.Nonempty → kronMat k S T (A.map (algebraMap K k)) *ᵥ w ∈ W := by
  classical
  intro T hT
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  have hpoly : ∀ c : K, ∑ U : Finset S, (algebraMap K k c) ^ subsetExp S U *
      φ (kronMat k S U (A.map (algebraMap K k)) *ᵥ w) = φ w := by
    intro c
    have h1 : φ (frobTensorRep k M S (l c) w) = φ w := by
      have h2 := hφ (frobTensorRep k M S (l c) w - w) (hW c)
      rw [map_sub, sub_eq_zero] at h2
      exact h2
    rw [frobTensorRep_eq_sum (k := k) (M := M) (S := S) (A := A) hA l hl w c,
      map_sum] at h1
    simp only [map_smul, smul_eq_mul] at h1
    exact h1
  have hzero : ∀ c : K, ∑ U : Finset S, (algebraMap K k c) ^ subsetExp S U *
      (if U.Nonempty then φ (kronMat k S U (A.map (algebraMap K k)) *ᵥ w) else 0) = 0 := by
    intro c
    set F : Finset S → k := fun U => (algebraMap K k c) ^ subsetExp S U *
      φ (kronMat k S U (A.map (algebraMap K k)) *ᵥ w) with hF
    have hempty : F ∅ = φ w := by
      simp [hF, subsetExp, kronMat_empty]
    have hsum : ∑ U ∈ Finset.univ.erase (∅ : Finset S), F U + F ∅ = φ w := by
      have h:= Finset.sum_erase_add (Finset.univ : Finset (Finset S)) F
        (Finset.mem_univ (∅ : Finset S))
      rw [h, hpoly c]
    have hzero' : ∑ U ∈ Finset.univ.erase (∅ : Finset S), F U = 0 := by
      rw [hempty] at hsum
      exact add_right_cancel (by rw [hsum, zero_add])
    have hconv : ∑ U : Finset S, (algebraMap K k c) ^ subsetExp S U *
        (if U.Nonempty then φ (kronMat k S U (A.map (algebraMap K k)) *ᵥ w) else 0) =
        ∑ U ∈ Finset.univ.erase (∅ : Finset S), F U := by
      rw [← Finset.sum_erase (s := Finset.univ) (a := (∅ : Finset S)) (f := fun U =>
        (algebraMap K k c) ^ subsetExp S U *
          (if U.Nonempty then φ (kronMat k S U (A.map (algebraMap K k)) *ᵥ w) else 0))]
      · refine Finset.sum_congr rfl fun U hU => ?_
        rw [Finset.mem_erase] at hU
        have hne : U ≠ ∅ := hU.1
        simp [hF, Finset.nonempty_iff_ne_empty, hne]
      · simp
    rw [hconv, hzero']
  have hzero' : ∀ c : K, ∑ U : Finset S,
      (if U.Nonempty then φ (kronMat k S U (A.map (algebraMap K k)) *ᵥ w) else 0) *
        (algebraMap K k c) ^ subsetExp S U = 0 := by
    intro c
    exact (Finset.sum_congr rfl fun U _ => mul_comm _ _).trans (hzero c)
  have hcoef := CFSG.QuasithinUnique.Setup.SL2Modules.eq_zero_of_sum_pow_eq_zero
    (F := K) (k := k) (a := subsetExp S) (subsetExp_injective S)
    (fun U => by rw [hK]; exact subsetExp_lt hS U)
    (fun U => if U.Nonempty then φ (kronMat k S U (A.map (algebraMap K k)) *ᵥ w) else 0)
    hzero' T
  simpa [hT] using hcoef

private theorem sum_pow_algebraMap_eq [Fintype K] [DecidableEq K] {n a : ℕ}
    (hK : Fintype.card K = 2 ^ n) (ha : a < 2 ^ n) :
    ∑ c : K, (algebraMap K k c) ^ a = if a = 2 ^ n - 1 then 1 else 0 := by
  by_cases h : a = 2 ^ n - 1
  · rw [if_pos h]
    have ha0 : a ≠ 0 := by
      have h1 : 1 < 2 ^ n := by rw [← hK]; exact Fintype.one_lt_card
      omega
    rw [← Finset.sum_erase_add (Finset.univ : Finset K) (fun c => (algebraMap K k c) ^ a)
      (Finset.mem_univ 0)]
    rw [show (algebraMap K k (0 : K)) ^ a = 0 by simp [ha0], add_zero]
    have h1 : ∑ x ∈ Finset.univ.erase (0 : K), (algebraMap K k x) ^ a =
        ∑ x : Kˣ, (algebraMap K k (x : K)) ^ a := by
      refine Finset.sum_bij
        (fun x hx => (Units.mk0 x (by rw [Finset.mem_erase] at hx; exact hx.1) : Kˣ))
        (fun x _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro x _ y _ hxy
        exact Units.ext_iff.mp hxy
      · intro y _
        exact ⟨(y : K), Finset.mem_erase.mpr ⟨y.ne_zero, Finset.mem_univ _⟩, Units.ext rfl⟩
      · intro x _
        rfl
    rw [h1]
    have h2 : ∑ x : Kˣ, (algebraMap K k (x : K)) ^ a =
        algebraMap K k (∑ x : Kˣ, ((x : K) ^ a)) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun x _ => (map_pow (algebraMap K k) (x : K) a).symm
    have hdvd : Fintype.card K - 1 ∣ a := by
      simp [hK, h]
    rw [h2, FiniteField.sum_pow_units K a, if_pos hdvd, map_neg, map_one, CharTwo.neg_eq]
  · rw [if_neg h]
    have hlt : a < Fintype.card K - 1 := by
      rw [hK]
      omega
    have h0 := FiniteField.sum_pow_lt_card_sub_one K a hlt
    have h1 := congrArg (algebraMap K k) h0
    simpa only [map_sum, map_pow, map_zero] using h1

private theorem frobTensor_support_of_fixed [Fintype K] {n : ℕ} (hK : Fintype.card K = 2 ^ n)
    (M : G →* Matrix ι ι K) (S : Finset ℕ) (hS : ∀ b ∈ S, b < n)
    {I : Type*} (E : I → Matrix ι ι K) (u : I → K → G)
    (hu : ∀ i c, M (u i c) = 1 + c • E i)
    (hE01 : ∀ i a b, E i a b = 0 ∨ E i a b = 1) (v₀ : ι)
    (hker : ∀ w : ι → k, (∀ i, (E i).map (algebraMap K k) *ᵥ w = 0) →
      ∀ j, j ≠ v₀ → w j = 0)
    (x : (S → ι) → k) (hfix : ∀ i c, frobTensorRep k M S (u i c) x = x) :
    ∀ y : S → ι, y ≠ (fun _ => v₀) → x y = 0 := by
  intro y hy
  obtain ⟨b, hb⟩ : ∃ b : S, y b ≠ v₀ := by
    by_contra hcon
    push Not at hcon
    exact hy (funext fun b => hcon b)
  let uvec : ι → k := fun j => x (Function.update y b j)
  have huvec : ∀ i, (E i).map (algebraMap K k) *ᵥ uvec = 0 := by
    intro i
    have hbot : kronMat k S ({b} : Finset S) ((E i).map (algebraMap K k)) *ᵥ x ∈
        (⊥ : Submodule k ((S → ι) → k)) :=
      kronMat_mem_of_fixed_mod (k := k) hK M S hS (E i) (hE01 i) (u i) (hu i)
        (⊥ : Submodule k ((S → ι) → k)) x
        (fun c => by rw [Submodule.mem_bot]; exact sub_eq_zero.mpr (hfix i c))
        ({b} : Finset S) (by simp)
    have hzero : kronMat k S ({b} : Finset S) ((E i).map (algebraMap K k)) *ᵥ x = 0 :=
      (Submodule.mem_bot k).mp hbot
    funext j0
    have h1 : (kronMat k S ({b} : Finset S) ((E i).map (algebraMap K k)) *ᵥ x)
        (Function.update y b j0) = 0 := by rw [hzero]; rfl
    rw [kronMat_singleton_mulVec_apply k S b ((E i).map (algebraMap K k)) x
      (Function.update y b j0)] at h1
    simpa [uvec, Matrix.mulVec, dotProduct, Function.update_apply, Function.update_idem]
      using h1
  have hji := hker uvec huvec (y b) hb
  simpa [uvec, Function.update_eq_self] using hji

private theorem frobTensor_basis_mem
    {I' : Type*} (F : I' → Matrix ι ι K)
    (v₀ : ι) (S : Finset ℕ)
    (W : Submodule k ((S → ι) → k))
    (hstep : ∀ (b : S) (i : I'), ∀ w ∈ W,
      kronMat k S ({b} : Finset S) ((F i).map (algebraMap K k)) *ᵥ w ∈ W)
    (hgen : ∀ U : Submodule k (ι → k), Pi.single v₀ 1 ∈ U →
      (∀ i, ∀ w ∈ U, (F i).map (algebraMap K k) *ᵥ w ∈ U) → U = ⊤)
    (hbase : (Pi.single (fun _ => v₀) 1 : (S → ι) → k) ∈ W) :
    ∀ y : S → ι, Pi.single y 1 ∈ W := by
  have hmain : ∀ D : Finset S, ∀ y : S → ι,
      (∀ b : S, b ∈ D ↔ y b ≠ v₀) → Pi.single y 1 ∈ W := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      intro y hy
      have hyv : y = fun _ => v₀ := by
        funext b
        by_contra h
        exact absurd ((hy b).mpr h) (Finset.notMem_empty b)
      rw [hyv]
      exact hbase
    | insert b D hb ih =>
      intro y hy
      let y' : S → ι := Function.update y b v₀
      have hy'supp : ∀ b' : S, b' ∈ D ↔ y' b' ≠ v₀ := by
        intro b'
        by_cases hb' : b' = b
        · rw [hb']
          simp [y', hb]
        · have hmem : b' ∈ insert b D ↔ b' ∈ D := by simp [hb']
          rw [← hmem, hy b']
          simp [y', hb']
      have hy'mem : Pi.single y' 1 ∈ W := ih y' hy'supp
      let U : Submodule k (ι → k) :=
        { carrier := {v | sliceVec k S b y' v ∈ W}
          zero_mem' := by
            show sliceVec k S b y' 0 ∈ W
            rw [show sliceVec k S b y' 0 = 0 from by funext z; simp [sliceVec]]
            exact W.zero_mem
          add_mem' := fun {v w} hv hw => by
            show sliceVec k S b y' (v + w) ∈ W
            rw [sliceVec_add]
            exact W.add_mem hv hw
          smul_mem' := fun a {v} hv => by
            show sliceVec k S b y' (a • v) ∈ W
            rw [sliceVec_smul]
            exact W.smul_mem a hv }
      have hbaseU : (Pi.single v₀ 1 : ι → k) ∈ U := by
        show sliceVec k S b y' (Pi.single v₀ 1) ∈ W
        rw [sliceVec_single]
        have hy'b : y' b = v₀ := by simp [y']
        rw [← hy'b, Function.update_eq_self]
        exact hy'mem
      have hstableU : ∀ i, ∀ v ∈ U, (F i).map (algebraMap K k) *ᵥ v ∈ U := by
        intro i v hv
        show sliceVec k S b y' ((F i).map (algebraMap K k) *ᵥ v) ∈ W
        rw [← kronMat_singleton_mulVec_sliceVec k S b ((F i).map (algebraMap K k)) y' v]
        exact hstep b i _ hv
      have hUtop : U = ⊤ := hgen U hbaseU hstableU
      have hmem : (Pi.single (y b) 1 : ι → k) ∈ U := by
        rw [hUtop]
        exact Submodule.mem_top
      have hmemW : sliceVec k S b y' (Pi.single (y b) 1) ∈ W := hmem
      rw [sliceVec_single] at hmemW
      have hyeq : Function.update y' b (y b) = y := by
        funext b'
        by_cases hb' : b' = b
        · subst hb'; simp [y']
        · simp [y', hb']
      rwa [hyeq] at hmemW
  intro y
  exact hmain (Finset.univ.filter (fun b : S => y b ≠ v₀)) y (by intro b; simp)

theorem isSimpleRep_frobTensorRep [Fintype K] {n : ℕ} (hK : Fintype.card K = 2 ^ n)
    (M : G →* Matrix ι ι K) (S : Finset ℕ) (hS : ∀ b ∈ S, b < n)
    {I : Type*} (E : I → Matrix ι ι K) (u : I → K → G) (hu : ∀ i c, M (u i c) = 1 + c • E i)
    {I' : Type*} (F : I' → Matrix ι ι K) (l : I' → K → G) (hl : ∀ i c, M (l i c) = 1 + c • F i)
    (hE01 : ∀ i a b, E i a b = 0 ∨ E i a b = 1) (hF01 : ∀ i a b, F i a b = 0 ∨ F i a b = 1)
    (v₀ : ι)
    (hker : ∀ w : ι → k, (∀ i, (E i).map (algebraMap K k) *ᵥ w = 0) → ∀ j, j ≠ v₀ → w j = 0)
    (hgen : ∀ W : Submodule k (ι → k), Pi.single v₀ 1 ∈ W →
      (∀ i, ∀ w ∈ W, (F i).map (algebraMap K k) *ᵥ w ∈ W) → W = ⊤)
    (P : Subgroup G) [Finite P] (hP : IsPGroup 2 P) (huP : ∀ i c, u i c ∈ P) :
    IsSimpleRep (frobTensorRep k M S) := by
  classical
  refine ⟨?_, ?_⟩
  · refine ⟨Pi.single (fun _ => v₀) (1 : k), 0, ?_⟩
    intro h
    have := congrFun h (fun _ => v₀)
    simp at this
  · intro W hW
    by_cases hWbot : W = ⊥
    · exact Or.inl hWbot
    · right
      obtain ⟨x, hxW, hx_ne, hxfix⟩ :=
        exists_fixed_mem (p := 2) (ρ := frobTensorRep k M S) (S := P) hP hW hWbot
      have hxfix' := (mem_fixSub (ρ := frobTensorRep k M S) (S := P)).mp hxfix
      have hfixU : ∀ i (c : K), frobTensorRep k M S (u i c) x = x :=
        fun i c => hxfix' (u i c) (huP i c)
      have hsupp := frobTensor_support_of_fixed (k := k) (hK := hK) M S hS E u hu hE01 v₀
        hker x hfixU
      let base : (S → ι) → k := Pi.single (fun _ => v₀) 1
      have hxbase : x = x (fun _ => v₀) • base := by
        funext y
        by_cases hy : y = (fun _ => v₀)
        · subst hy; simp [base]
        · rw [hsupp y hy]
          simp [base, hy]
      have hx0 : x (fun _ => v₀) ≠ 0 := by
        intro h0
        apply hx_ne
        rw [hxbase, h0, zero_smul]
      have hbase : base ∈ W := by
        set a := x (fun _ => v₀) with ha
        have hxbase' : x = a • base := by simpa [ha] using hxbase
        have ha0 : a ≠ 0 := by simpa [ha] using hx0
        have h1 : a⁻¹ • x ∈ W := W.smul_mem a⁻¹ hxW
        have h2 : a⁻¹ • x = base := by
          rw [hxbase', smul_smul, inv_mul_cancel₀ ha0, one_smul]
        rwa [h2] at h1
      have hstep : ∀ (b : S) (i : I'), ∀ w ∈ W,
          kronMat k S ({b} : Finset S) ((F i).map (algebraMap K k)) *ᵥ w ∈ W := by
        intro b i w hw
        exact kronMat_mem_of_fixed_mod (k := k) hK M S hS (F i) (hF01 i) (l i) (hl i) W w
          (fun c => W.sub_mem (hW (l i c) w hw) hw) ({b} : Finset S) (by simp)
      have hall := frobTensor_basis_mem (k := k) F v₀ S W hstep hgen hbase
      rw [Submodule.eq_top_iff']
      intro v
      have hv : v = ∑ y : S → ι, v y • Pi.single y 1 := by
        funext z
        rw [Finset.sum_apply, Finset.sum_eq_single z]
        · simp
        · intro y _ hy
          rw [Pi.smul_apply, Pi.single_eq_of_ne hy.symm]
          simp
        · simp
      rw [hv]
      exact W.sum_mem fun y _ => W.smul_mem (v y) (hall y)

theorem frobTensorRep_single_of_col (M : G →* Matrix ι ι K) (S : Finset ℕ) (g : G) (v : ι)
    (hcol : ∀ j, j ≠ v → M g j v = 0) :
    frobTensorRep k M S g (Pi.single (fun _ => v) 1) =
      (∏ b : S, frobHom k b (M g v v)) • Pi.single (fun _ => v) 1 := by
  funext x'
  rw [frobTensorRep_apply, Finset.sum_eq_single (fun _ => v)]
  · rw [Pi.single_eq_same, mul_one, frobTensorMat, Pi.smul_apply]
    by_cases h : x' = fun _ => v
    · subst h
      simp
    · have hsingle : (Pi.single (fun _ => v) (1 : k) : (S → ι) → k) x' = 0 := by
        rw [Pi.single_apply, if_neg h]
      have hzero : (∏ b : S, frobHom k b (M g (x' b) (v))) = 0 := by
        obtain ⟨b, hb⟩ : ∃ b : S, x' b ≠ v := by
          by_contra hcon
          push Not at hcon
          exact h (funext hcon)
        exact Finset.prod_eq_zero (Finset.mem_univ b) (by rw [hcol (x' b) hb]; simp [frobHom])
      rw [hzero, hsingle, smul_zero]
  · intro x _ hx
    have hsingle : (Pi.single (fun _ => v) (1 : k) : (S → ι) → k) x = 0 := by
      rw [Pi.single_apply, if_neg hx]
    rw [hsingle, mul_zero]
  · simp

theorem frobTensorRep_single_of_col_single (M : G →* Matrix ι ι K) (S : Finset ℕ) (g : G)
    (v v' : ι) (hcol : ∀ j, M g j v = if j = v' then 1 else 0) :
    frobTensorRep k M S g (Pi.single (fun _ => v) 1) = Pi.single (fun _ => v') 1 := by
  funext x'
  rw [frobTensorRep_apply, Finset.sum_eq_single (fun _ => v)]
  · rw [Pi.single_eq_same, mul_one, frobTensorMat, Pi.single_apply]
    have hprod : (∏ b : S, frobHom k b (M g (x' b) v)) =
        ∏ b : S, (if x' b = v' then (1 : k) else 0) := by
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [hcol (x' b)]
      simp [frobHom]
    rw [hprod, Finset.prod_boole]
    by_cases h : x' = fun _ => v'
    · subst h
      simp
    · have hforall : ¬ ∀ i ∈ (Finset.univ : Finset S), x' i = v' := fun hh =>
        h (funext fun i => hh i (Finset.mem_univ i))
      rw [if_neg hforall, if_neg h]
  · intro x _ hx
    have hsingle : (Pi.single (fun _ => v) (1 : k) : (S → ι) → k) x = 0 := by
      rw [Pi.single_apply, if_neg hx]
    rw [hsingle, mul_zero]
  · simp

end FrobTensor

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
