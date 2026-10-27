module

public import CFSG.Assembly.E6FourCentBits
public import CFSG.Assembly.E6FourCentMask

public section

namespace CFSG.Assembly

open CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration CFSG.Assembly.E6FourCentChk
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
open scoped Matrix

private theorem rtsLit_length (k : ℕ) (hk : k < 72) : (rtsLit.getD k []).length = 6 := by
  have h : ∀ k : Fin 72, (rtsLit.getD (k : ℕ) []).length = 6 := by decide +kernel
  exact h ⟨k, hk⟩

private theorem rtsLit_getD_inj {k k' : ℕ} (hk : k < 72) (hk' : k' < 72)
    (h : rtsLit.getD k [] = rtsLit.getD k' []) : k = k' := by
  have hchk : ∀ k k' : Fin 72,
      rtsLit.getD (k : ℕ) [] = rtsLit.getD (k' : ℕ) [] → k = k' := by decide +kernel
  have := hchk ⟨k, hk⟩ ⟨k', hk'⟩ h
  simpa using this

private theorem cartLit_length : cartLit.length = Tag.E6.rank := by
  decide +kernel

private theorem cartLit_entry (i j : Fin Tag.E6.rank) :
    (cartLit.getD (i : ℕ) []).getD (j : ℕ) 0 = Tag.E6.symmetrizedCartan i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem matLit_eq : matLit = e6TwoMat := by
  decide +kernel

private theorem matLit_length : matLit.length = Tag.E6.rank := by
  rw [matLit_eq]
  decide +kernel

private theorem rtsLit_cert (k : ℕ) (hk : k < 72) (i : Fin Tag.E6.rank) :
    (rtsLit.getD k []).getD (i : ℕ) 0 = Tag.E6.rootCertificate.root k i := by
  have h : ∀ k : Fin 72, ∀ i : Fin Tag.E6.rank,
      (rtsLit.getD (k : ℕ) []).getD (i : ℕ) 0 = Tag.E6.rootCertificate.root (k : ℕ) i := by
    decide +kernel
  exact h ⟨k, hk⟩ i

private theorem adjLit_check (a b : Fin 72) :
    adjLit.testBit (72 * (a : ℕ) + (b : ℕ)) =
      (iformI (rt (a : ℕ)) (rt (b : ℕ)) != 0) := by
  have h : ∀ a b : Fin 72,
      adjLit.testBit (72 * (a : ℕ) + (b : ℕ)) =
        (iformI (rt (a : ℕ)) (rt (b : ℕ)) != 0) := by
    decide +kernel
  exact h a b

private theorem permLit_check (j : Fin 72) :
    permAt permLit (j : ℕ) < 72 ∧
      rt (permAt permLit (j : ℕ)) = mulVecI matLit (rt (j : ℕ)) := by
  have h : ∀ j : Fin 72,
      permAt permLit (j : ℕ) < 72 ∧
        rt (permAt permLit (j : ℕ)) = mulVecI matLit (rt (j : ℕ)) := by
    decide +kernel
  exact h j

private theorem dotI_eq_sum_zipWith (x y : List ℤ) :
    E6FourCentChk.dotI x y = (List.zipWith (· * ·) x y).sum := by
  rw [E6FourCentChk.dotI, List.sum_eq_foldl]

private theorem dotI_cons_cons (a b : ℤ) (as bs : List ℤ) :
    E6FourCentChk.dotI (a :: as) (b :: bs) = a * b + E6FourCentChk.dotI as bs := by
  rw [dotI_eq_sum_zipWith, dotI_eq_sum_zipWith, List.zipWith_cons_cons, List.sum_cons]

private theorem dotI_ofFn_aux : ∀ (n : ℕ) (x : Fin n → ℤ) (l : List ℤ),
    E6FourCentChk.dotI (List.ofFn x) l = ∑ i : Fin n, x i * l.getD (i : ℕ) 0
  | 0, x, l => by simp [E6FourCentChk.dotI]
  | n + 1, x, l => by
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    cases l with
    | nil => simp [E6FourCentChk.dotI]
    | cons b bs =>
      rw [dotI_cons_cons, dotI_ofFn_aux n (fun i => x i.succ) bs]
      simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ]

private theorem dotI_ofFn_right_aux : ∀ (n : ℕ) (l : List ℤ) (y : Fin n → ℤ),
    E6FourCentChk.dotI l (List.ofFn y) = ∑ j : Fin n, l.getD (j : ℕ) 0 * y j
  | 0, l, y => by simp [E6FourCentChk.dotI]
  | n + 1, l, y => by
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    cases l with
    | nil => simp [E6FourCentChk.dotI]
    | cons a as =>
      rw [dotI_cons_cons, dotI_ofFn_right_aux n as (fun i => y i.succ)]
      simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ]

private theorem getD_ofFn {n : ℕ} (f : Fin n → ℤ) (j : ℕ) (d : ℤ) (hj : j < n) :
    (List.ofFn f).getD j d = f ⟨j, hj⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa [List.length_ofFn] using hj), List.getElem_ofFn]

private theorem mulVecI_ofFn_map (A : List (List ℤ)) (n : ℕ) (hA : A.length = n)
    (y : Fin n → ℤ) :
    E6FourCentChk.mulVecI A (List.ofFn y) = List.ofFn (fun i : Fin n =>
      ∑ j : Fin n, (A.getD (i : ℕ) []).getD (j : ℕ) 0 * y j) := by
  apply List.ext_getElem
  · simp [E6FourCentChk.mulVecI, hA, List.length_ofFn]
  · intro i hi _
    simp only [E6FourCentChk.mulVecI, List.getElem_map]
    have hiA : i < A.length := by simpa [E6FourCentChk.mulVecI] using hi
    rw [← List.getD_eq_getElem A [] hiA]
    rw [dotI_ofFn_right_aux n (A.getD i []) y, List.getElem_ofFn]

private theorem rt_ofFn_priv {k : ℕ} (hk : k < 72) :
    E6FourCentChk.rt k = List.ofFn (e6RootVec k) := by
  have hlen := rtsLit_length k hk
  apply List.ext_getElem
  · rw [E6FourCentChk.rt]
    rw [show (rtsLit.getD k []).length = 6 from hlen, List.length_ofFn]
    rfl
  · intro i hi _
    have hi' : i < (rtsLit.getD k []).length := by
      simpa [E6FourCentChk.rt] using hi
    rw [List.getElem_ofFn]
    simp only [E6FourCentChk.rt, e6RootVec, List.getD_eq_getElem _ _ hi']

theorem e6RootVec_injOn {k k' : ℕ} (hk : k < 72) (hk' : k' < 72)
    (h : e6RootVec k = e6RootVec k') : k = k' := by
  apply rtsLit_getD_inj hk hk'
  have h' : List.ofFn (e6RootVec k) = List.ofFn (e6RootVec k') := by rw [h]
  rw [← rt_ofFn_priv hk, ← rt_ofFn_priv hk'] at h'
  simpa [E6FourCentChk.rt] using h'

theorem rt_eq_ofFn {k : ℕ} (hk : k < 72) : E6FourCentChk.rt k = List.ofFn (e6RootVec k) :=
  rt_ofFn_priv hk

theorem dotI_ofFn (x : Fin Tag.E6.rank → ℤ) (l : List ℤ) :
    E6FourCentChk.dotI (List.ofFn x) l = ∑ i, x i * l.getD i 0 := by
  simpa using dotI_ofFn_aux Tag.E6.rank x l

theorem iformI_ofFn (x y : Fin Tag.E6.rank → ℤ) :
    E6FourCentChk.iformI (List.ofFn x) (List.ofFn y) =
      CFSG.LieType.Steinberg.Adjoint.iform (τ := Tag.E6) x y := by
  rw [E6FourCentChk.iformI, mulVecI_ofFn_map cartLit Tag.E6.rank cartLit_length y,
    dotI_ofFn]
  simp only [CFSG.LieType.Steinberg.Adjoint.iform]
  apply Finset.sum_congr rfl
  intro i _
  rw [getD_ofFn _ (i : ℕ) 0 i.2]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [cartLit_entry i j]
  ring

theorem mulVecI_matLit_ofFn (y : Fin Tag.E6.rank → ℤ) :
    E6FourCentChk.mulVecI E6FourCentChk.matLit (List.ofFn y) =
      List.ofFn ((wordMat Tag.E6 e6TwoWord) *ᵥ y) := by
  rw [matLit_eq]
  rw [mulVecI_ofFn_map e6TwoMat Tag.E6.rank (by simpa [matLit_eq] using matLit_length) y]
  rw [e6Two_wordMat, List.ofFn_injective.eq_iff]
  funext i
  simp [Matrix.mulVec, dotProduct, toMat, lget, List.getD_eq_getElem]


theorem e6RootVec_eq_cert {k : ℕ} (hk : k < 72) :
    e6RootVec k = Tag.E6.rootCertificate.root k := by
  funext i
  exact rtsLit_cert k hk i

theorem isRoot_e6RootVec {k : ℕ} (hk : k < 72) : IsRoot Tag.E6 (e6RootVec k) := by
  rw [e6RootVec_eq_cert hk]
  refine RootCertificate.isRoot_root Tag.E6.rootCertificate_check k ?_
  rw [Tag.rootCertificate_length]
  simpa [Tag.rootCount] using hk

theorem exists_e6RootVec {γ : Fin Tag.E6.rank → ℤ} (h : IsRoot Tag.E6 γ) :
    ∃ k, k < 72 ∧ e6RootVec k = γ := by
  obtain ⟨k, hk, hkroot⟩ :=
    RootCertificate.exists_root_eq Tag.E6.rootCertificate_check h
  have hk72 : k < 72 := by
    rw [Tag.rootCertificate_length] at hk
    simpa [Tag.rootCount] using hk
  exact ⟨k, hk72, by rw [e6RootVec_eq_cert hk72, hkroot]⟩

theorem adjLit_iff {a b : ℕ} (ha : a < 72) (hb : b < 72) :
    adjLit.testBit (72 * a + b) = true ↔
      e6RootVec a ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ e6RootVec b) ≠ 0 := by
  rw [adjLit_check ⟨a, ha⟩ ⟨b, hb⟩]
  rw [bne_iff_ne]
  rw [rt_eq_ofFn ha, rt_eq_ofFn hb, iformI_ofFn]
  rw [← CFSG.LieType.Chevalley.dotProduct_mulVec_eq_iform]

theorem permAt_permLit {j : ℕ} (hj : j < 72) :
    permAt permLit j < 72 ∧
      e6RootVec (permAt permLit j) = (wordMat Tag.E6 e6TwoWord) *ᵥ e6RootVec j := by
  obtain ⟨hlt, heq⟩ := permLit_check ⟨j, hj⟩
  refine ⟨hlt, ?_⟩
  rw [rt_eq_ofFn hlt, rt_eq_ofFn hj, mulVecI_matLit_ofFn] at heq
  exact List.ofFn_injective heq

end CFSG.Assembly

end
