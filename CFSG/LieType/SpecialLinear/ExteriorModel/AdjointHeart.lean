module

public import CFSG.LieType.SpecialLinear.ExteriorModel.Binary
public import CFSG.HardMathSupport.GuralnickMalle.AdjointHeart
public import CFSG.HardMathSupport.GuralnickMalle.BasicGeneral

public section

open Matrix

namespace CFSG.LieType.SpecialLinear.ExteriorModel

open CFSG.HardMathSupport.GuralnickMalle

variable {k : Type} [Field k] {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]
  {ε : τ → Finset (Fin n)} {r₀ : τ}

namespace AdjointHeartModel

@[expose]
def idxOne (hn : 3 ≤ n) : Fin n := ⟨1, by omega⟩

@[expose]
def idxLast (hn : 3 ≤ n) : Fin n := ⟨n - 1, by omega⟩

@[simp]
theorem idxOne_val (hn : 3 ≤ n) : (idxOne hn : ℕ) = 1 := rfl

@[simp]
theorem idxLast_val (hn : 3 ≤ n) : (idxLast hn : ℕ) = n - 1 := rfl

@[expose]
def idxZero (hn : 3 ≤ n) : Fin n := ⟨0, by omega⟩

@[simp]
theorem idxZero_val (hn : 3 ≤ n) : (idxZero hn : ℕ) = 0 := rfl

theorem idxOne_ne_idxLast (hn : 3 ≤ n) : idxOne hn ≠ idxLast hn := by
  intro h
  have := congrArg Fin.val h
  rw [idxOne_val, idxLast_val] at this
  omega

@[simp]
theorem idxLast_ne_idxOne (hn : 3 ≤ n) : idxLast hn ≠ idxOne hn :=
  (idxOne_ne_idxLast hn).symm

omit [Fintype τ] [DecidableEq τ] in
theorem bdeg_idxOne (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn}) :
    bdeg ε (r₀, idxOne hn) = 1 := by
  have hmem : idxOne hn ∈ ε r₀ := by rw [hε]; simp
  simp only [bdeg]
  rw [if_pos hmem, idxOne_val]

omit [Fintype τ] [DecidableEq τ] in
theorem bdeg_idxLast (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn}) :
    bdeg ε (r₀, idxLast hn) = n - 1 := by
  have hmem : idxLast hn ∈ ε r₀ := by rw [hε]; simp
  simp only [bdeg]
  rw [if_pos hmem, idxLast_val]

omit [Fintype τ] in
theorem bdeg_eq_zero_of_ne (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) {p : τ × Fin n}
    (h1 : p ≠ (r₀, idxOne hn)) (h2 : p ≠ (r₀, idxLast hn)) : bdeg ε p = 0 := by
  rcases p with ⟨r, j⟩
  by_cases hr : r = r₀
  · rw [hr] at h1 h2 ⊢
    have hj1 : j ≠ idxOne hn := fun h => h1 (by rw [h])
    have hj2 : j ≠ idxLast hn := fun h => h2 (by rw [h])
    have hnot : j ∉ ε r₀ := by
      rw [hε]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨hj1, hj2⟩
    simp only [bdeg]
    rw [if_neg hnot]
  · have hnot : j ∉ ε r := by
      rw [hε' r hr]
      simp
    simp only [bdeg]
    rw [if_neg hnot]

omit [Fintype τ] [DecidableEq τ] in
theorem idxOne_exists_singleton (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (s : BIdx ε) :
    ∃ a : Fin n,
      ((s (r₀, idxOne hn) : Set.powersetCard (Fin n) (bdeg ε (r₀, idxOne hn))) :
        Finset (Fin n)) = {a} :=
  Finset.card_eq_one.mp (by rw [Set.powersetCard.card_eq, bdeg_idxOne hn hε])

@[expose]
noncomputable def bFst (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn}) (s : BIdx ε) :
    Fin n :=
  Classical.choose (idxOne_exists_singleton hn hε s)

omit [Fintype τ] [DecidableEq τ] in
theorem bFst_spec (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn}) (s : BIdx ε) :
    ((s (r₀, idxOne hn) : Set.powersetCard (Fin n) (bdeg ε (r₀, idxOne hn))) :
        Finset (Fin n)) = {bFst hn hε s} :=
  Classical.choose_spec (idxOne_exists_singleton hn hε s)

omit [Fintype τ] [DecidableEq τ] in
theorem idxLast_exists_compl_singleton (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (s : BIdx ε) :
    ∃ b : Fin n,
      (((s (r₀, idxLast hn) : Set.powersetCard (Fin n) (bdeg ε (r₀, idxLast hn))) :
        Finset (Fin n))ᶜ) = {b} := by
  refine Finset.card_eq_one.mp ?_
  rw [Finset.card_compl, Set.powersetCard.card_eq, bdeg_idxLast hn hε, Fintype.card_fin]
  omega

@[expose]
noncomputable def bSnd (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn}) (s : BIdx ε) :
    Fin n :=
  Classical.choose (idxLast_exists_compl_singleton hn hε s)

omit [Fintype τ] [DecidableEq τ] in
theorem bSnd_spec (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn}) (s : BIdx ε) :
    (((s (r₀, idxLast hn) : Set.powersetCard (Fin n) (bdeg ε (r₀, idxLast hn))) :
        Finset (Fin n))ᶜ) = {bSnd hn hε s} :=
  Classical.choose_spec (idxLast_exists_compl_singleton hn hε s)

omit [Fintype τ] [DecidableEq τ] in
theorem bSnd_spec' (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn}) (s : BIdx ε) :
    ((s (r₀, idxLast hn) : Set.powersetCard (Fin n) (bdeg ε (r₀, idxLast hn))) :
        Finset (Fin n)) = {bSnd hn hε s}ᶜ := by
  have h := congrArg (fun t : Finset (Fin n) => tᶜ) (bSnd_spec hn hε s)
  simpa using h

omit [Fintype τ] [DecidableEq τ] in
theorem bFst_eq_of_eq (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn}) {s t : BIdx ε}
    (h : s = t) : bFst hn hε s = bFst hn hε t := by rw [h]

omit [Fintype τ] [DecidableEq τ] in
theorem bSnd_eq_of_eq (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn}) {s t : BIdx ε}
    (h : s = t) : bSnd hn hε s = bSnd hn hε t := by rw [h]

@[expose]
noncomputable def bIdxOf (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (x y : Fin n) : BIdx ε :=
  fun p =>
    Set.powersetCard.ofCard (n := bdeg ε p)
      (s := if p = (r₀, idxOne hn) then ({x} : Finset (Fin n))
        else if p = (r₀, idxLast hn) then ({y}ᶜ : Finset (Fin n)) else ∅)
      (by
        split_ifs with h1 h2
        · rw [h1, Finset.card_singleton]
          exact (bdeg_idxOne hn hε).symm
        · rw [h2, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
          exact (bdeg_idxLast hn hε).symm
        · rw [Finset.card_empty]
          exact (bdeg_eq_zero_of_ne hn hε hε' h1 h2).symm)

omit [Fintype τ] in
@[simp]
theorem bIdxOf_apply_first (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (x y : Fin n) :
    ((bIdxOf hn hε hε' x y (r₀, idxOne hn) :
        Set.powersetCard (Fin n) (bdeg ε (r₀, idxOne hn))) : Finset (Fin n)) = {x} := by
  simp [bIdxOf]

omit [Fintype τ] in
@[simp]
theorem bIdxOf_apply_second (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (x y : Fin n) :
    ((bIdxOf hn hε hε' x y (r₀, idxLast hn) :
        Set.powersetCard (Fin n) (bdeg ε (r₀, idxLast hn))) : Finset (Fin n)) = {y}ᶜ := by
  simp [bIdxOf]

omit [Fintype τ] in
theorem bFst_bIdxOf (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (x y : Fin n) :
    bFst hn hε (bIdxOf hn hε hε' x y) = x := by
  have h := bFst_spec hn hε (bIdxOf hn hε hε' x y)
  rw [bIdxOf_apply_first hn hε hε'] at h
  exact (Finset.singleton_inj.mp h).symm

omit [Fintype τ] in
theorem bSnd_bIdxOf (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (x y : Fin n) :
    bSnd hn hε (bIdxOf hn hε hε' x y) = y := by
  have h := bSnd_spec hn hε (bIdxOf hn hε hε' x y)
  rw [bIdxOf_apply_second hn hε hε'] at h
  have h' : ({y} : Finset (Fin n)) = {bSnd hn hε (bIdxOf hn hε hε' x y)} := by
    simpa using h
  exact (Finset.singleton_inj.mp h').symm

omit [Fintype τ] in
theorem bIdxOf_bFst_bSnd (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (s : BIdx ε) :
    bIdxOf hn hε hε' (bFst hn hε s) (bSnd hn hε s) = s := by
  funext p
  by_cases h1 : p = (r₀, idxOne hn)
  · rw [h1]
    apply Subtype.ext
    rw [bIdxOf_apply_first hn hε hε']
    exact (bFst_spec hn hε s).symm
  by_cases h2 : p = (r₀, idxLast hn)
  · rw [h2]
    apply Subtype.ext
    rw [bIdxOf_apply_second hn hε hε']
    exact (bSnd_spec' hn hε s).symm
  · apply Subtype.ext
    have hzero : bdeg ε p = 0 := bdeg_eq_zero_of_ne hn hε hε' h1 h2
    have hs : (s p : Finset (Fin n)) = ∅ :=
      Finset.card_eq_zero.mp (by rw [Set.powersetCard.card_eq, hzero])
    have hL : ((bIdxOf hn hε hε' (bFst hn hε s) (bSnd hn hε s) p :
        Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) = ∅ := by
      simp [bIdxOf, h1, h2]
    rw [hL, hs]

@[expose]
noncomputable def bIdxEquiv (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) : BIdx ε ≃ Fin n × Fin n where
  toFun s := (bFst hn hε s, bSnd hn hε s)
  invFun p := bIdxOf hn hε hε' p.1 p.2
  left_inv s := bIdxOf_bFst_bSnd hn hε hε' s
  right_inv p := by
    obtain ⟨x, y⟩ := p
    ext <;> simp [bFst_bIdxOf hn hε hε', bSnd_bIdxOf hn hε hε']

omit [Fintype τ] in
@[simp]
theorem bIdxEquiv_apply (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (s : BIdx ε) :
    bIdxEquiv hn hε hε' s = (bFst hn hε s, bSnd hn hε s) := rfl

omit [Fintype τ] in
@[simp]
theorem bIdxEquiv_symm_apply (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (p : Fin n × Fin n) :
    (bIdxEquiv hn hε hε').symm p = bIdxOf hn hε hε' p.1 p.2 := rfl

@[expose]
noncomputable def bPsi (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    (BIdx ε → k) ≃ₗ[k] Matrix (Fin n) (Fin n) k where
  toFun v := Matrix.of fun x y => v (bIdxOf hn hε hε' x y)
  invFun X := fun s => X (bFst hn hε s) (bSnd hn hε s)
  map_add' v w := by
    ext x y
    rfl
  map_smul' c v := by
    ext x y
    rfl
  left_inv v := by
    funext s
    show v (bIdxOf hn hε hε' (bFst hn hε s) (bSnd hn hε s)) = v s
    rw [bIdxOf_bFst_bSnd hn hε hε' s]
  right_inv X := by
    ext x y
    simp [bFst_bIdxOf hn hε hε', bSnd_bIdxOf hn hε hε']

omit [Fintype τ] in
@[simp]
theorem bPsi_apply (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (v : BIdx ε → k) (x y : Fin n) :
    bPsi hn hε hε' v x y = v (bIdxOf hn hε hε' x y) := rfl

omit [Fintype τ] in
@[simp]
theorem bPsi_symm_apply (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (X : Matrix (Fin n) (Fin n) k) (s : BIdx ε) :
    (bPsi hn hε hε').symm X s = X (bFst hn hε s) (bSnd hn hε s) := rfl

@[expose]
def matDot (X Y : Matrix (Fin n) (Fin n) k) : k := ∑ i, ∑ j, X i j * Y i j

theorem bPsi_dotProduct (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (v w : BIdx ε → k) :
    matDot (k := k) (bPsi hn hε hε' v) (bPsi hn hε hε' w) = v ⬝ᵥ w := by
  rw [matDot, dotProduct]
  simp only [bPsi_apply]
  rw [← Equiv.sum_comp (bIdxEquiv hn hε hε').symm
    (fun s => v s * w s)]
  rw [Fintype.sum_prod_type]
  rfl


theorem minor_singleton {m : ℕ} (hm : m = 1) (H : Matrix (Fin n) (Fin n) k)
    (s t : Set.powersetCard (Fin n) m) {x x' : Fin n}
    (hs : (s : Finset (Fin n)) = {x}) (ht : (t : Finset (Fin n)) = {x'}) :
    minor H s t = H x x' := by
  subst hm
  rw [minor]
  have h1 : (Set.powersetCard.ofFinEmbEquiv.symm s : Fin 1 → Fin n) = fun _ => x := by
    funext i
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    have hs' : s = (⟨{x}, by simp⟩ : Set.powersetCard (Fin n) 1) := Subtype.ext hs
    rw [hs']
    exact Finset.orderEmbOfFin_singleton x i
  have h2 : (Set.powersetCard.ofFinEmbEquiv.symm t : Fin 1 → Fin n) = fun _ => x' := by
    funext i
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    have ht' : t = (⟨{x'}, by simp⟩ : Set.powersetCard (Fin n) 1) := Subtype.ext ht
    rw [ht']
    exact Finset.orderEmbOfFin_singleton x' i
  rw [h1, h2, Matrix.det_fin_one]
  rfl

theorem minor_of_degree_zero (H : Matrix (Fin n) (Fin n) k) {m : ℕ} (hm : m = 0)
    (s t : Set.powersetCard (Fin n) m) : minor H s t = 1 := by
  subst hm
  have hs : s = (⟨∅, by simp⟩ : Set.powersetCard (Fin n) 0) :=
    Subtype.ext (Finset.card_eq_zero.mp s.prop)
  have ht : t = (⟨∅, by simp⟩ : Set.powersetCard (Fin n) 0) :=
    Subtype.ext (Finset.card_eq_zero.mp t.prop)
  rw [hs, ht, minor, Matrix.det_fin_zero]


theorem minor_compl_eq_adjugate [CharP k 2] (hn : 1 ≤ n) (H : Matrix (Fin n) (Fin n) k)
    (y y' : Fin n) :
    minor H (⟨{y}ᶜ, by simp [Finset.card_compl]⟩ : Set.powersetCard (Fin n) (n - 1))
      (⟨{y'}ᶜ, by simp [Finset.card_compl]⟩) = adjugate H y' y := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hm
  let Y : Set.powersetCard (Fin (m + 1)) m := ⟨{y}ᶜ, by simp [Finset.card_compl]⟩
  let Y' : Set.powersetCard (Fin (m + 1)) m := ⟨{y'}ᶜ, by simp [Finset.card_compl]⟩
  have hY : (Set.powersetCard.ofFinEmbEquiv.symm Y : Fin m → Fin (m + 1)) = y.succAbove := by
    have h := Finset.orderEmbOfFin_unique (s := ({y}ᶜ : Finset (Fin (m + 1)))) Y.prop
      (f := y.succAbove) (fun i => by
        rw [Finset.mem_compl, Finset.mem_singleton]
        exact Fin.succAbove_ne y i) (Fin.strictMono_succAbove y)
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    dsimp only [Y]
    exact h.symm
  have hY' : (Set.powersetCard.ofFinEmbEquiv.symm Y' : Fin m → Fin (m + 1)) = y'.succAbove := by
    have h := Finset.orderEmbOfFin_unique (s := ({y'}ᶜ : Finset (Fin (m + 1)))) Y'.prop
      (f := y'.succAbove) (fun i => by
        rw [Finset.mem_compl, Finset.mem_singleton]
        exact Fin.succAbove_ne y' i) (Fin.strictMono_succAbove y')
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    dsimp only [Y']
    exact h.symm
  have hminor : minor H Y Y' = (H.submatrix y.succAbove y'.succAbove).det := by
    rw [minor, hY, hY']
  rw [Matrix.adjugate_apply, hminor]
  have hM : (H.updateRow y (Pi.single y' 1)).submatrix y.succAbove y'.succAbove =
      H.submatrix y.succAbove y'.succAbove := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply, Matrix.updateRow_ne]
    exact Fin.succAbove_ne y i
  rw [Matrix.det_succ_row (H.updateRow y (Pi.single y' 1)) y]
  rw [Finset.sum_eq_single y'
    (fun j _ hjy => by
      rw [Matrix.updateRow_self, Pi.single_eq_of_ne hjy]
      simp)
    (fun hy => absurd (Finset.mem_univ y') hy)]
  rw [Matrix.updateRow_self, Pi.single_eq_same, hM, CharTwo.neg_eq, one_pow]
  simp


theorem minor_compl_singleton [CharP k 2] (hn : 1 ≤ n) (H : Matrix (Fin n) (Fin n) k)
    {m : ℕ} (hm : m = n - 1) (s t : Set.powersetCard (Fin n) m) {y y' : Fin n}
    (hs : (s : Finset (Fin n)) = {y}ᶜ) (ht : (t : Finset (Fin n)) = {y'}ᶜ) :
    minor H s t = adjugate H y' y := by
  subst hm
  have hs' : s = (⟨{y}ᶜ, by simp [Finset.card_compl]⟩ : Set.powersetCard (Fin n) (n - 1)) :=
    Subtype.ext hs
  have ht' : t = (⟨{y'}ᶜ, by simp [Finset.card_compl]⟩ : Set.powersetCard (Fin n) (n - 1)) :=
    Subtype.ext ht
  rw [hs', ht']
  exact minor_compl_eq_adjugate hn H y y'

omit [Fintype τ] [DecidableEq τ] in
theorem btop_apply_first (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn}) :
    ((btop ε (r₀, idxOne hn) :
        Set.powersetCard (Fin n) (bdeg ε (r₀, idxOne hn))) : Finset (Fin n)) = {idxZero hn} := by
  apply Finset.ext
  intro a
  rw [btop, ktop, mem_initSeg, bdeg_idxOne hn hε, Finset.mem_singleton]
  constructor
  · intro h
    exact Fin.ext (by rw [idxZero_val]; omega)
  · intro h
    rw [h]
    simp

omit [Fintype τ] [DecidableEq τ] in
theorem btop_apply_second (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn}) :
    ((btop ε (r₀, idxLast hn) :
        Set.powersetCard (Fin n) (bdeg ε (r₀, idxLast hn))) : Finset (Fin n)) =
      {idxLast hn}ᶜ := by
  apply Finset.ext
  intro a
  rw [btop, ktop, mem_initSeg, bdeg_idxLast hn hε, Finset.mem_compl, Finset.mem_singleton]
  constructor
  · intro h ha
    have h' : (a : ℕ) = n - 1 := by rw [ha, idxLast_val]
    omega
  · intro h
    have hlt := a.isLt
    have hne : (a : ℕ) ≠ n - 1 := fun h' => h (Fin.ext (by rw [h', idxLast_val]))
    omega

omit [Fintype τ] [DecidableEq τ] in
theorem bFst_btop (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn}) :
    bFst hn hε (btop ε) = idxZero hn := by
  have h := bFst_spec hn hε (btop ε)
  rw [btop_apply_first hn hε] at h
  exact (Finset.singleton_inj.mp h).symm

omit [Fintype τ] [DecidableEq τ] in
theorem bSnd_btop (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn}) :
    bSnd hn hε (btop ε) = idxLast hn := by
  have h := bSnd_spec hn hε (btop ε)
  rw [btop_apply_second hn hε] at h
  have h' : ({idxLast hn} : Finset (Fin n)) = {bSnd hn hε (btop ε)} := by
    simpa using h
  exact (Finset.singleton_inj.mp h').symm

omit [Fintype τ] in
theorem bIdxEquiv_btop (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    bIdxEquiv hn hε hε' (btop ε) = (idxZero hn, idxLast hn) := by
  rw [bIdxEquiv_apply, bFst_btop hn hε, bSnd_btop hn hε]

theorem bPsi_bvec (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    bPsi hn hε hε' (bvec ε) = Matrix.single (idxZero hn) (idxLast hn) (1 : k) := by
  ext x y
  rw [bPsi_apply, bvec, Pi.single_apply, Matrix.single_apply]
  have hiff : bIdxOf hn hε hε' x y = btop ε ↔ x = idxZero hn ∧ y = idxLast hn := by
    rw [← (bIdxEquiv hn hε hε').injective.eq_iff]
    have hcoord : bIdxEquiv hn hε hε' (bIdxOf hn hε hε' x y) = (x, y) := by
      simpa using (bIdxEquiv hn hε hε').apply_symm_apply (x, y)
    rw [hcoord, bIdxEquiv_btop hn hε hε']
    simp
  by_cases hxy : x = idxZero hn ∧ y = idxLast hn
  · have hxy' : idxZero hn = x ∧ idxLast hn = y := ⟨hxy.1.symm, hxy.2.symm⟩
    rw [if_pos (hiff.mpr hxy), if_pos hxy']
  · have hxy' : ¬ (idxZero hn = x ∧ idxLast hn = y) := fun h => hxy ⟨h.1.symm, h.2.symm⟩
    rw [if_neg (fun h => hxy (hiff.mp h)), if_neg hxy']

theorem bMat_apply [CharP k 2] (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (H : τ → Matrix (Fin n) (Fin n) k)
    (x y x' y' : Fin n) :
    bMat ε H (bIdxOf hn hε hε' x y) (bIdxOf hn hε hε' x' y') =
      H r₀ x x' * adjugate (H r₀) y' y := by
  rw [bMat, kronMinor_apply]
  let F : τ × Fin n → k := fun p =>
    minor (H p.1) ((bIdxOf hn hε hε' x y) p) ((bIdxOf hn hε hε' x' y') p)
  change (∏ p, F p) = H r₀ x x' * adjugate (H r₀) y' y
  have hne : (r₀, idxLast hn) ≠ (r₀, idxOne hn) := by
    intro h
    exact idxLast_ne_idxOne hn (Prod.mk.inj h).2
  have hprod : (∏ p, F p) = F (r₀, idxOne hn) * F (r₀, idxLast hn) := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (τ × Fin n)) F
      (Finset.mem_univ (r₀, idxOne hn))]
    rw [← Finset.mul_prod_erase ((Finset.univ : Finset (τ × Fin n)).erase (r₀, idxOne hn)) F
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)]
    have hinner : (∏ p ∈ ((Finset.univ : Finset (τ × Fin n)).erase (r₀, idxOne hn)).erase
        (r₀, idxLast hn), F p) = 1 := by
      refine Finset.prod_eq_one ?_
      intro p hp
      rw [Finset.mem_erase] at hp
      obtain ⟨hp2, hp1⟩ := hp
      rw [Finset.mem_erase] at hp1
      obtain ⟨hp1, -⟩ := hp1
      dsimp only [F]
      exact minor_of_degree_zero (H p.1) (bdeg_eq_zero_of_ne hn hε hε' hp1 hp2) _ _
    rw [hinner, mul_one]
  have hF1 : F (r₀, idxOne hn) = H r₀ x x' := by
    dsimp only [F]
    exact minor_singleton (bdeg_idxOne hn hε) (H r₀) _ _
      (bIdxOf_apply_first hn hε hε' x y) (bIdxOf_apply_first hn hε hε' x' y')
  have hF2 : F (r₀, idxLast hn) = adjugate (H r₀) y' y := by
    dsimp only [F]
    exact minor_compl_singleton (by omega : 1 ≤ n) (H r₀) (bdeg_idxLast hn hε) _ _
      (bIdxOf_apply_second hn hε hε' x y) (bIdxOf_apply_second hn hε hε' x' y')
  rw [hprod, hF1, hF2]

theorem bPsi_bMat_mulVec [CharP k 2] (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (H : τ → Matrix (Fin n) (Fin n) k)
    (v : BIdx ε → k) :
    bPsi hn hε hε' (bMat ε H *ᵥ v) =
      H r₀ * bPsi hn hε hε' v * adjugate (H r₀) := by
  ext x y
  have hL : (bMat ε H *ᵥ v) (bIdxOf hn hε hε' x y) =
      ∑ x' : Fin n, ∑ y' : Fin n,
        H r₀ x x' * adjugate (H r₀) y' y * v (bIdxOf hn hε hε' x' y') := by
    rw [Matrix.mulVec, dotProduct]
    rw [← Equiv.sum_comp (bIdxEquiv hn hε hε').symm
      (fun t => bMat ε H (bIdxOf hn hε hε' x y) t * v t)]
    rw [Fintype.sum_prod_type]
    simp only [bIdxEquiv_symm_apply, bMat_apply hn hε hε']
  have hR : (H r₀ * bPsi hn hε hε' v * adjugate (H r₀)) x y =
      ∑ x' : Fin n, ∑ y' : Fin n,
        H r₀ x x' * v (bIdxOf hn hε hε' x' y') * adjugate (H r₀) y' y := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [bPsi_apply]
  rw [bPsi_apply, hL, hR]
  refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => ?_
  ring

theorem bPsi_bMat_mulVec_inv [CharP k 2] (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (H : τ → Matrix (Fin n) (Fin n) k)
    (hH : (H r₀).det = 1) (v : BIdx ε → k) :
    bPsi hn hε hε' (bMat ε H *ᵥ v) = H r₀ * bPsi hn hε hε' v * (H r₀)⁻¹ := by
  rw [bPsi_bMat_mulVec hn hε hε' H v, Matrix.inv_def, hH, Ring.inverse_one, one_smul]


omit [Fintype τ] in
theorem bIdxOf_apply_of_ne (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (x y : Fin n) {p : τ × Fin n}
    (h1 : p ≠ (r₀, idxOne hn)) (h2 : p ≠ (r₀, idxLast hn)) :
    ((bIdxOf hn hε hε' x y p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) = ∅ := by
  simp [bIdxOf, h1, h2]

theorem insert_erase_compl_singleton {a b : Fin n} (hab : a ≠ b) :
    insert a ((({a} : Finset (Fin n))ᶜ).erase b) = ({b} : Finset (Fin n))ᶜ := by
  ext c
  by_cases hca : c = a
  · subst hca
    simp [hab]
  · by_cases hcb : c = b
    · subst hcb
      simp [hca]
    · simp [hca, hcb]

theorem bDer_eq_zero_of_twist_ne [CharP k 2] (_hn : 3 ≤ n)
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅)
    {r : τ} (hr : r ≠ r₀) (a b : Fin n) :
    bDer ε (r, a, b) = (0 : Matrix (BIdx ε) (BIdx ε) k) := by
  have hdeg : ∀ p : τ × Fin n, p.1 = r → bdeg ε p = 0 := by
    intro p hp
    simp only [bdeg]
    rw [hp, hε' r hr]
    simp
  by_cases hab : a = b
  · subst hab
    ext s t
    rw [bDer, kronDer_single_self_apply]
    have hcount : (Finset.univ.filter fun i : τ × Fin n =>
        ((fun p : τ × Fin n => p.1 = r) i ∧
          a ∈ ((t i : Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n)))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨-, hiP, hai⟩ := hi
      have hcard : ((t i : Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n)).card = 0 := by
        rw [Set.powersetCard.card_eq, hdeg i hiP]
      rw [Finset.card_eq_zero] at hcard
      rw [hcard] at hai
      exact Finset.notMem_empty a hai
    rw [hcount]
    simp
  · ext s t
    rw [bDer, kronDer_single_apply (CharTwo.two_eq_zero) (fun p : τ × Fin n => p.1 = r) hab]
    have hno : ¬ ∃ i : τ × Fin n, (i.1 = r) ∧ (∀ j, j ≠ i → s j = t j) ∧
        b ∈ ((t i : Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n)) ∧
        a ∉ ((t i : Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n)) ∧
        ((s i : Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n)) =
          insert a (((t i : Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n)).erase b) := by
      rintro ⟨i, hiP, -, hbi, -⟩
      have hcard : ((t i : Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n)).card = 0 := by
        rw [Set.powersetCard.card_eq, hdeg i hiP]
      rw [Finset.card_eq_zero] at hcard
      rw [hcard] at hbi
      exact Finset.notMem_empty b hbi
    rw [if_neg hno]
    simp

theorem bDer_apply_off [CharP k 2] (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) {a b : Fin n} (hab : a ≠ b) (x y x' y' : Fin n) :
    bDer ε (r₀, a, b) (bIdxOf hn hε hε' x y) (bIdxOf hn hε hε' x' y') =
      if (x = a ∧ x' = b ∧ y' = y) ∨ (y = b ∧ y' = a ∧ x' = x) then (1 : k) else 0 := by
  rw [bDer, kronDer_single_apply (CharTwo.two_eq_zero) (fun p : τ × Fin n => p.1 = r₀) hab]
  have hcond : (∃ i : τ × Fin n, (i.1 = r₀) ∧
        (∀ j, j ≠ i → (bIdxOf hn hε hε' x y) j = (bIdxOf hn hε hε' x' y') j) ∧
        b ∈ (((bIdxOf hn hε hε' x' y') i :
          Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n)) ∧
        a ∉ (((bIdxOf hn hε hε' x' y') i :
          Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n)) ∧
        (((bIdxOf hn hε hε' x y) i : Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n)) =
          insert a ((((bIdxOf hn hε hε' x' y') i :
            Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n)).erase b)) ↔
      ((x = a ∧ x' = b ∧ y' = y) ∨ (y = b ∧ y' = a ∧ x' = x)) := by
    constructor
    · rintro ⟨i, hiP, hst, hbi, hai, hsi⟩
      have hpos : bdeg ε i ≠ 0 := by
        intro h0
        have hcard : (((bIdxOf hn hε hε' x' y') i :
            Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n)).card = 0 := by
          rw [Set.powersetCard.card_eq, h0]
        rw [Finset.card_eq_zero] at hcard
        rw [hcard] at hbi
        exact Finset.notMem_empty b hbi
      have hi : i = (r₀, idxOne hn) ∨ i = (r₀, idxLast hn) := by
        by_contra h
        push Not at h
        exact hpos (bdeg_eq_zero_of_ne hn hε hε' h.1 h.2)
      rcases hi with hi | hi
      · subst hi
        have hy : y' = y := by
          have h := hst (r₀, idxLast hn) (by simp)
          have h' := congrArg
            (fun u : Set.powersetCard (Fin n) (bdeg ε (r₀, idxLast hn)) =>
              (u : Finset (Fin n))) h
          rw [bIdxOf_apply_second hn hε hε' x y,
            bIdxOf_apply_second hn hε hε' x' y'] at h'
          have h'' : ({y} : Finset (Fin n)) = {y'} := by
            simpa using congrArg (fun u : Finset (Fin n) => uᶜ) h'
          exact (Finset.singleton_inj.mp h'').symm
        have hxb : x' = b := by
          rw [bIdxOf_apply_first hn hε hε' x' y'] at hbi
          exact (Finset.mem_singleton.mp hbi).symm
        have hxa : x = a := by
          have h' : ({x} : Finset (Fin n)) = {a} := by
            simpa [hxb] using hsi
          exact Finset.singleton_inj.mp h'
        exact Or.inl ⟨hxa, hxb, hy⟩
      · subst hi
        have hx : x' = x := by
          have h := hst (r₀, idxOne hn) (by simp [idxOne_ne_idxLast hn])
          have h' := congrArg
            (fun u : Set.powersetCard (Fin n) (bdeg ε (r₀, idxOne hn)) =>
              (u : Finset (Fin n))) h
          rw [bIdxOf_apply_first hn hε hε' x y,
            bIdxOf_apply_first hn hε hε' x' y'] at h'
          exact (Finset.singleton_inj.mp h').symm
        have hby : b ≠ y' := by
          intro h
          rw [bIdxOf_apply_second hn hε hε' x' y', h] at hbi
          simp at hbi
        have hay : a = y' := by
          by_contra h
          apply hai
          rw [bIdxOf_apply_second hn hε hε' x' y']
          simp [h]
        have hyb : y = b := by
          have hs2 := bIdxOf_apply_second hn hε hε' x y
          have ht2 := bIdxOf_apply_second hn hε hε' x' y'
          have h' : ({y} : Finset (Fin n))ᶜ = ({b} : Finset (Fin n))ᶜ := by
            rw [← hs2, hsi, ht2, hay]
            exact insert_erase_compl_singleton (a := y') (b := b) hby.symm
          have h'' : ({y} : Finset (Fin n)) = {b} := by
            simpa using h'
          exact Finset.singleton_inj.mp h''
        exact Or.inr ⟨hyb, hay.symm, hx⟩
    · rintro (⟨hxa, hxb, hy⟩ | ⟨hyb, hya, hx⟩)
      · refine ⟨(r₀, idxOne hn), rfl, ?_, ?_, ?_, ?_⟩
        · intro j hj
          by_cases hj2 : j = (r₀, idxLast hn)
          · subst hj2
            apply Subtype.ext
            rw [bIdxOf_apply_second hn hε hε' x y,
              bIdxOf_apply_second hn hε hε' x' y', hy]
          · apply Subtype.ext
            rw [bIdxOf_apply_of_ne hn hε hε' x y hj hj2,
              bIdxOf_apply_of_ne hn hε hε' x' y' hj hj2]
        · rw [bIdxOf_apply_first hn hε hε' x' y', hxb]
          simp
        · rw [bIdxOf_apply_first hn hε hε' x' y', hxb]
          simp [Finset.mem_singleton, hab]
        · rw [bIdxOf_apply_first hn hε hε' x y,
            bIdxOf_apply_first hn hε hε' x' y', hxa, hxb]
          simp
      · refine ⟨(r₀, idxLast hn), rfl, ?_, ?_, ?_, ?_⟩
        · intro j hj
          by_cases hj1 : j = (r₀, idxOne hn)
          · subst hj1
            apply Subtype.ext
            rw [bIdxOf_apply_first hn hε hε' x y,
              bIdxOf_apply_first hn hε hε' x' y', hx]
          · apply Subtype.ext
            rw [bIdxOf_apply_of_ne hn hε hε' x y hj1 hj,
              bIdxOf_apply_of_ne hn hε hε' x' y' hj1 hj]
        · rw [bIdxOf_apply_second hn hε hε' x' y', hya]
          simp [Finset.mem_compl, Finset.mem_singleton, Ne.symm hab]
        · rw [bIdxOf_apply_second hn hε hε' x' y', hya]
          simp
        · rw [bIdxOf_apply_second hn hε hε' x y,
            bIdxOf_apply_second hn hε hε' x' y', hyb, hya]
          exact (insert_erase_compl_singleton hab).symm
  exact if_congr hcond rfl rfl


theorem bPsi_bDer_mulVec_off [CharP k 2] (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅)
    {a b : Fin n} (hab : a ≠ b) (v : BIdx ε → k) :
    bPsi hn hε hε' (bDer ε (r₀, a, b) *ᵥ v) =
      Matrix.single a b (1 : k) * bPsi hn hε hε' v +
        bPsi hn hε hε' v * Matrix.single a b (1 : k) := by
  ext x y
  have hL : (bDer ε (r₀, a, b) *ᵥ v) (bIdxOf hn hε hε' x y) =
      ∑ p : Fin n × Fin n,
        (if (x = a ∧ p.1 = b ∧ p.2 = y) ∨ (y = b ∧ p.2 = a ∧ p.1 = x) then
          (1 : k) else 0) * v (bIdxOf hn hε hε' p.1 p.2) := by
    rw [Matrix.mulVec, dotProduct]
    rw [← Equiv.sum_comp (bIdxEquiv hn hε hε').symm
      (fun t => bDer ε (r₀, a, b) (bIdxOf hn hε hε' x y) t * v t)]
    simp only [bIdxEquiv_symm_apply, bDer_apply_off hn hε hε' hab]
  have hR : (Matrix.single a b (1 : k) * bPsi hn hε hε' v +
        bPsi hn hε hε' v * Matrix.single a b (1 : k)) x y =
      (if x = a then v (bIdxOf hn hε hε' b y) else 0) +
        (if y = b then v (bIdxOf hn hε hε' x a) else 0) := by
    have h1 : (∑ z : Fin n, Matrix.single a b (1 : k) x z *
        bPsi hn hε hε' v z y) =
        if x = a then v (bIdxOf hn hε hε' b y) else 0 := by
      rw [Finset.sum_eq_single b]
      · rw [bPsi_apply, Matrix.single_apply]
        by_cases hxa : x = a
        · rw [if_pos ⟨hxa.symm, rfl⟩, if_pos hxa]
          simp
        · rw [if_neg (fun h : a = x ∧ b = b => hxa h.1.symm), if_neg hxa]
          simp
      · intro z _ hz
        have h : ¬ (a = x ∧ b = z) := fun h => hz h.2.symm
        rw [Matrix.single_apply, if_neg h, zero_mul]
      · intro hb
        exact absurd (Finset.mem_univ b) hb
    have h2 : (∑ z : Fin n, bPsi hn hε hε' v x z *
        Matrix.single a b (1 : k) z y) =
        if y = b then v (bIdxOf hn hε hε' x a) else 0 := by
      rw [Finset.sum_eq_single a]
      · rw [bPsi_apply, Matrix.single_apply]
        by_cases hyb : y = b
        · rw [if_pos ⟨rfl, hyb.symm⟩, if_pos hyb]
          simp
        · rw [if_neg (fun h : a = a ∧ b = y => hyb h.2.symm), if_neg hyb]
          simp
      · intro z _ hz
        have h : ¬ (a = z ∧ b = y) := fun h => hz h.1.symm
        rw [Matrix.single_apply, if_neg h, mul_zero]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, h1, h2]
  rw [bPsi_apply, hL, hR]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  by_cases hx : x = a
  · rw [hx]
    by_cases hy : y = b
    · rw [hy]
      simp only [true_and, if_true]
      have hf : (Finset.univ.filter fun p : Fin n × Fin n =>
          (p.1 = b ∧ p.2 = b) ∨ (p.2 = a ∧ p.1 = a)) =
          ({(b, b), (a, a)} : Finset (Fin n × Fin n)) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Prod.ext_iff]
        tauto
      rw [hf, Finset.sum_pair (by exact fun h => hab (congrArg Prod.fst h.symm))]
    · simp only [hy, true_and, false_and, or_false, if_false, add_zero]
      have hf : (Finset.univ.filter fun p : Fin n × Fin n =>
          p.1 = b ∧ p.2 = y) = ({(b, y)} : Finset (Fin n × Fin n)) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Prod.ext_iff]
      rw [hf, Finset.sum_singleton]
      simp
  · by_cases hy : y = b
    · rw [hy]
      simp only [hx, false_and, false_or, true_and, if_false, zero_add]
      have hf : (Finset.univ.filter fun p : Fin n × Fin n =>
          p.2 = a ∧ p.1 = x) = ({(x, a)} : Finset (Fin n × Fin n)) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Prod.ext_iff]
        tauto
      rw [hf, Finset.sum_singleton]
      simp
    · simp only [hx, hy, false_and, false_or, if_false, add_zero]
      rw [Finset.filter_false, Finset.sum_empty]


theorem bDer_apply_self_diag [CharP k 2] (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅)
    (a x : Fin n) :
    bDer ε (r₀, a, a) (bIdxOf hn hε hε' x x) (bIdxOf hn hε hε' x x) = (1 : k) := by
  rw [bDer, kronDer_single_self_apply, if_pos rfl]
  have hf : (Finset.univ.filter fun i : τ × Fin n =>
      ((fun p : τ × Fin n => p.1 = r₀) i ∧
        a ∈ (((bIdxOf hn hε hε' x x) i : Set.powersetCard (Fin n) (bdeg ε i)) :
          Finset (Fin n)))) =
      ({if a = x then (r₀, idxOne hn) else (r₀, idxLast hn)} : Finset (τ × Fin n)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    have hvanish : ∀ (h : (((bIdxOf hn hε hε' x x) i :
        Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n)) = ∅),
        ¬ (a ∈ (((bIdxOf hn hε hε' x x) i :
          Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n))) := by
      intro h ha
      rw [h] at ha
      exact Finset.notMem_empty a ha
    by_cases hx : a = x
    · rw [if_pos hx]
      constructor
      · rintro ⟨-, ha⟩
        by_cases h1 : i = (r₀, idxOne hn)
        · exact h1
        · by_cases h2 : i = (r₀, idxLast hn)
          · subst h2
            rw [bIdxOf_apply_second hn hε hε' x x] at ha
            exact absurd hx (by simpa using ha)
          · exact absurd ha (hvanish (bIdxOf_apply_of_ne hn hε hε' x x h1 h2))
      · rintro rfl
        refine ⟨rfl, ?_⟩
        rw [bIdxOf_apply_first hn hε hε' x x]
        simp [hx]
    · rw [if_neg hx]
      constructor
      · rintro ⟨-, ha⟩
        by_cases h1 : i = (r₀, idxOne hn)
        · subst h1
          rw [bIdxOf_apply_first hn hε hε' x x] at ha
          exact absurd hx (by simpa using ha)
        · by_cases h2 : i = (r₀, idxLast hn)
          · exact h2
          · exact absurd ha (hvanish (bIdxOf_apply_of_ne hn hε hε' x x h1 h2))
      · rintro rfl
        refine ⟨rfl, ?_⟩
        rw [bIdxOf_apply_second hn hε hε' x x]
        simp [hx]
  rw [hf, Finset.card_singleton, Nat.cast_one]

theorem trace_bPsi_bDer_self [CharP k 2] (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅)
    (a : Fin n) (w : BIdx ε → k) :
    Matrix.trace (bPsi hn hε hε' (bDer ε (r₀, a, a) *ᵥ w)) =
      Matrix.trace (bPsi hn hε hε' w) := by
  simp only [Matrix.trace, Matrix.diag_apply, bPsi_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single (bIdxOf hn hε hε' x x)]
  · rw [bDer_apply_self_diag hn hε hε', one_mul]
  · intro t _ ht
    rw [bDer, kronDer_single_self_apply,
      if_neg (fun h => ht h.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h


theorem idxZero_ne_idxLast (hn : 3 ≤ n) : idxZero hn ≠ idxLast hn := by
  intro h
  have := congrArg Fin.val h
  rw [idxZero_val, idxLast_val] at this
  omega

theorem bPsi_bvec_mem_sl (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    bPsi hn hε hε' (bvec ε) ∈ slMatrices n k := by
  rw [slMatrices, LinearMap.mem_ker, Matrix.traceLinearMap_apply, bPsi_bvec]
  simp only [Matrix.trace, Matrix.diag_apply]
  apply Finset.sum_eq_zero
  intro x _
  rw [Matrix.single_apply, if_neg]
  rintro ⟨h1, h2⟩
  exact idxZero_ne_idxLast hn (h1.trans h2.symm)

theorem bPsi_bDer_mulVec_off_mem_sl [CharP k 2] (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅)
    {a b : Fin n} (hab : a ≠ b) (w : BIdx ε → k)
    (_hw : bPsi hn hε hε' w ∈ slMatrices n k) :
    bPsi hn hε hε' (bDer ε (r₀, a, b) *ᵥ w) ∈ slMatrices n k := by
  rw [bPsi_bDer_mulVec_off hn hε hε' hab]
  rw [slMatrices, LinearMap.mem_ker, Matrix.traceLinearMap_apply]
  rw [Matrix.trace_add, Matrix.trace_mul_comm, CharTwo.add_self_eq_zero]

theorem bPsi_bDer_mulVec_self_mem_sl [CharP k 2] (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅)
    (a : Fin n) (w : BIdx ε → k) (hw : bPsi hn hε hε' w ∈ slMatrices n k) :
    bPsi hn hε hε' (bDer ε (r₀, a, a) *ᵥ w) ∈ slMatrices n k := by
  rw [slMatrices, LinearMap.mem_ker, Matrix.traceLinearMap_apply] at hw ⊢
  rw [trace_bPsi_bDer_self hn hε hε']
  exact hw

theorem bCyc_map_bPsi_le_sl [CharP k 2] (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    (bCyc (k := k) ε).map (bPsi hn hε hε').toLinearMap ≤ slMatrices n k := by
  rw [Submodule.map_le_iff_le_comap]
  refine cyclicSub_le (D := bDer ε) (v := bvec ε) (bPsi_bvec_mem_sl hn hε hε') ?_
  intro x w hw
  rcases x with ⟨r, a, b⟩
  by_cases hr : r = r₀
  · subst hr
    by_cases hab : a = b
    · subst hab
      exact bPsi_bDer_mulVec_self_mem_sl hn hε hε' a w hw
    · exact bPsi_bDer_mulVec_off_mem_sl hn hε hε' hab w hw
  · rw [bDer_eq_zero_of_twist_ne hn hε' hr a b, Matrix.zero_mulVec]
    exact Submodule.zero_mem _


theorem idxOne_ne_idxZero (hn : 3 ≤ n) : idxOne hn ≠ idxZero hn := by
  intro h
  have := congrArg Fin.val h
  rw [idxOne_val, idxZero_val] at this
  omega

theorem idxLast_ne_idxZero (hn : 3 ≤ n) : idxLast hn ≠ idxZero hn := by
  intro h
  have := congrArg Fin.val h
  rw [idxLast_val, idxZero_val] at this
  omega

theorem bPsi_bDer_bvec_second [CharP k 2] (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅)
    (j : Fin n) (hj0 : j ≠ idxZero hn) (hjs : j ≠ idxLast hn) :
    bPsi hn hε hε' (bDer ε (r₀, idxLast hn, j) *ᵥ bvec ε) =
      Matrix.single (idxZero hn) j (1 : k) := by
  rw [bPsi_bDer_mulVec_off hn hε hε' (fun h : idxLast hn = j => hjs h.symm), bPsi_bvec]
  rw [Matrix.single_mul_single_of_ne (h := hj0), Matrix.single_mul_single_same, zero_add]
  simp

theorem bPsi_bDer_bvec_D [CharP k 2] (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    bPsi hn hε hε' (bDer ε (r₀, idxLast hn, idxZero hn) *ᵥ bvec ε) =
      Matrix.single (idxLast hn) (idxLast hn) (1 : k) +
        Matrix.single (idxZero hn) (idxZero hn) (1 : k) := by
  rw [bPsi_bDer_mulVec_off hn hε hε' (idxLast_ne_idxZero hn), bPsi_bvec]
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same]
  simp

@[expose] noncomputable def uE0 (hn : 3 ≤ n)
    (_hε : ε r₀ = {idxOne hn, idxLast hn}) (_hε' : ∀ r, r ≠ r₀ → ε r = ∅)
    (i j : Fin n) : BIdx ε → k :=
  if j = idxLast hn then bDer ε (r₀, i, idxZero hn) *ᵥ bvec ε
  else bDer ε (r₀, i, idxZero hn) *ᵥ (bDer ε (r₀, idxLast hn, j) *ᵥ bvec ε)

theorem uE0_mem [CharP k 2] (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (i j : Fin n) :
    uE0 hn hε hε' i j ∈ bCyc (k := k) ε := by
  unfold uE0
  split
  · exact mulVec_mem_cyclicSub _ (mem_cyclicSub_self _ _)
  · exact mulVec_mem_cyclicSub _ (mulVec_mem_cyclicSub _ (mem_cyclicSub_self _ _))

theorem bPsi_uE0 [CharP k 2] (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) {i j : Fin n}
    (hi0 : i ≠ idxZero hn) (hij : i ≠ j) (hj0 : j ≠ idxZero hn) :
    bPsi hn hε hε' (uE0 hn hε hε' i j) = Matrix.single i j (1 : k) := by
  unfold uE0
  by_cases hjs : j = idxLast hn
  · rw [if_pos hjs]
    subst hjs
    rw [bPsi_bDer_mulVec_off hn hε hε' hi0, bPsi_bvec]
    rw [Matrix.single_mul_single_same,
      Matrix.single_mul_single_of_ne (h := hij.symm), add_zero]
    simp
  · rw [if_neg hjs]
    rw [bPsi_bDer_mulVec_off hn hε hε' hi0]
    rw [bPsi_bDer_bvec_second hn hε hε' j hj0 hjs]
    rw [Matrix.single_mul_single_same,
      Matrix.single_mul_single_of_ne (h := hij.symm), add_zero]
    simp

@[expose] noncomputable def uE1 (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅)
    (i : Fin n) : BIdx ε → k :=
  bDer ε (r₀, (if i = idxOne hn then idxLast hn else idxOne hn), idxZero hn) *ᵥ
    uE0 hn hε hε' i (if i = idxOne hn then idxLast hn else idxOne hn)

theorem uE1_mem [CharP k 2] (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (i : Fin n) :
    uE1 hn hε hε' i ∈ bCyc (k := k) ε := by
  unfold uE1
  exact mulVec_mem_cyclicSub _ (uE0_mem hn hε hε' i _)

theorem bPsi_uE1 [CharP k 2] (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) {i : Fin n} (hi0 : i ≠ idxZero hn) :
    bPsi hn hε hε' (uE1 hn hε hε' i) = Matrix.single i (idxZero hn) (1 : k) := by
  unfold uE1
  by_cases hi1 : i = idxOne hn
  · rw [if_pos hi1]
    have hjs : idxLast hn ≠ idxZero hn := idxLast_ne_idxZero hn
    have hij : i ≠ idxLast hn := by rw [hi1]; exact idxOne_ne_idxLast hn
    rw [bPsi_bDer_mulVec_off hn hε hε' hjs,
      bPsi_uE0 hn hε hε' hi0 hij (idxLast_ne_idxZero hn)]
    rw [Matrix.single_mul_single_of_ne
        (h := hi0.symm), Matrix.single_mul_single_same, zero_add]
    simp
  · rw [if_neg hi1]
    have hj0 : idxOne hn ≠ idxZero hn := idxOne_ne_idxZero hn
    have hij : i ≠ idxOne hn := hi1
    rw [bPsi_bDer_mulVec_off hn hε hε' hj0,
      bPsi_uE0 hn hε hε' hi0 hij hj0]
    rw [Matrix.single_mul_single_of_ne
        (h := hi0.symm), Matrix.single_mul_single_same, zero_add]
    simp

@[expose] noncomputable def uD (hn : 3 ≤ n)
    (_hε : ε r₀ = {idxOne hn, idxLast hn}) (_hε' : ∀ r, r ≠ r₀ → ε r = ∅)
    (i : Fin n) : BIdx ε → k :=
  if i = idxLast hn then bDer ε (r₀, idxLast hn, idxZero hn) *ᵥ bvec ε
  else bDer ε (r₀, i, idxZero hn) *ᵥ (bDer ε (r₀, idxLast hn, i) *ᵥ bvec ε)

theorem uD_mem [CharP k 2] (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) (i : Fin n) :
    uD hn hε hε' i ∈ bCyc (k := k) ε := by
  unfold uD
  split
  · exact mulVec_mem_cyclicSub _ (mem_cyclicSub_self _ _)
  · exact mulVec_mem_cyclicSub _ (mulVec_mem_cyclicSub _ (mem_cyclicSub_self _ _))

theorem bPsi_uD [CharP k 2] (hn : 3 ≤ n) (hε : ε r₀ = {idxOne hn, idxLast hn})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) {i : Fin n} (hi0 : i ≠ idxZero hn) :
    bPsi hn hε hε' (uD hn hε hε' i) =
      Matrix.single i i (1 : k) + Matrix.single (idxZero hn) (idxZero hn) (1 : k) := by
  unfold uD
  by_cases his : i = idxLast hn
  · rw [if_pos his]
    subst his
    exact bPsi_bDer_bvec_D hn hε hε'
  · rw [if_neg his]
    rw [bPsi_bDer_mulVec_off hn hε hε' hi0]
    rw [bPsi_bDer_bvec_second hn hε hε' i hi0 his]
    rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same]
    simp


lemma sum_offdiag_single_apply (X : Matrix (Fin n) (Fin n) k) (p q : Fin n) :
    (∑ i, ∑ j, (if i = j then (0 : k) else X i j) •
        Matrix.single i j (1 : k)) p q =
      if p = q then 0 else X p q := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · simp
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_univ q) h
  · intro i _ hi
    rw [Finset.sum_eq_zero]
    intro j _
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ p) h

lemma sum_D_single_apply (hn : 3 ≤ n) {X : Matrix (Fin n) (Fin n) k}
    (hX : Matrix.trace X = 0) (p q : Fin n) :
    (∑ i ∈ Finset.univ.erase (idxZero hn), X i i •
        (Matrix.single i i (1 : k) -
          Matrix.single (idxZero hn) (idxZero hn) (1 : k))) p q =
      if p = q then X p p else 0 := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
    Matrix.single_apply]
  by_cases hpq : p = q
  · subst hpq
    by_cases hp0 : p = idxZero hn
    · subst hp0
      have htr : X (idxZero hn) (idxZero hn) +
          ∑ i ∈ Finset.univ.erase (idxZero hn), X i i = 0 := by
        rw [Finset.add_sum_erase (Finset.univ) (fun i => X i i) (Finset.mem_univ _)]
        exact hX
      have hsummand : ∀ i ∈ Finset.univ.erase (idxZero hn),
          X i i * ((if i = idxZero hn ∧ i = idxZero hn then (1 : k) else 0) -
            (if idxZero hn = idxZero hn ∧ idxZero hn = idxZero hn then (1 : k) else 0)) =
            - X i i := by
        intro i hi
        rw [Finset.mem_erase] at hi
        simp [hi.1]
      rw [Finset.sum_congr rfl hsummand, Finset.sum_neg_distrib]
      have hS : ∑ i ∈ Finset.univ.erase (idxZero hn), X i i =
          - X (idxZero hn) (idxZero hn) := by
        linear_combination htr
      rw [hS, neg_neg]
      simp
    · rw [Finset.sum_eq_single p]
      · simp [Ne.symm hp0]
      · intro i hi hip
        have hbp : ¬ idxZero hn = p := fun h => hp0 h.symm
        simp [hip, hbp]
      · intro hp
        exact absurd (Finset.mem_erase.mpr ⟨hp0, Finset.mem_univ p⟩) hp
  · rw [Finset.sum_eq_zero]
    · simp [hpq]
    · intro i _
      have hp : ¬ (i = p ∧ i = q) := fun h => hpq (h.1.symm.trans h.2)
      have hbq : ¬ (idxZero hn = p ∧ idxZero hn = q) :=
        fun h => hpq (h.1.symm.trans h.2)
      simp [hp, hbq]

theorem matrix_eq_offdiag_add_D (hn : 3 ≤ n) {X : Matrix (Fin n) (Fin n) k}
    (hX : Matrix.trace X = 0) :
    X = (∑ i, ∑ j, (if i = j then (0 : k) else X i j) •
        Matrix.single i j (1 : k))
      + ∑ i ∈ Finset.univ.erase (idxZero hn), X i i •
          (Matrix.single i i (1 : k) -
            Matrix.single (idxZero hn) (idxZero hn) (1 : k)) := by
  ext p q
  rw [Matrix.add_apply, sum_offdiag_single_apply, sum_D_single_apply hn hX]
  by_cases h : p = q <;> simp [h]


theorem matDot_smul_one (c : k) (Y : Matrix (Fin n) (Fin n) k) :
    matDot (c • (1 : Matrix (Fin n) (Fin n) k)) Y = c * Matrix.trace Y := by
  rw [matDot, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji.symm]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem matDot_single_right (X : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    matDot X (Matrix.single i j (1 : k)) = X i j := by
  rw [matDot]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      simp [hj'.symm]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · intro i' _ hi'
    rw [Finset.sum_eq_zero]
    intro j' _
    simp [hi'.symm]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem matDot_comm (X Y : Matrix (Fin n) (Fin n) k) : matDot X Y = matDot Y X := by
  rw [matDot, matDot]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem matDot_sub (X Y Z : Matrix (Fin n) (Fin n) k) :
    matDot X (Y - Z) = matDot X Y - matDot X Z := by
  simp [matDot, mul_sub, Finset.sum_sub_distrib]

theorem mem_span_one_of_forall_matDot_eq_zero (hn : 3 ≤ n)
    {X : Matrix (Fin n) (Fin n) k}
    (horth : ∀ Y ∈ slMatrices n k, matDot X Y = 0) :
    X ∈ Submodule.span k {(1 : Matrix (Fin n) (Fin n) k)} := by
  have hoff : ∀ i j : Fin n, i ≠ j → X i j = 0 := by
    intro i j hij
    have hsingle : Matrix.single i j (1 : k) ∈ slMatrices n k := by
      rw [slMatrices, LinearMap.mem_ker, Matrix.traceLinearMap_apply]
      exact Matrix.trace_single_eq_of_ne i j (1 : k) hij
    have h := horth _ hsingle
    rwa [matDot_single_right] at h
  have hdiag : ∀ i : Fin n, i ≠ idxZero hn → X i i = X (idxZero hn) (idxZero hn) := by
    intro i hi0
    have hsingle : Matrix.single i i (1 : k) - Matrix.single (idxZero hn) (idxZero hn) (1 : k) ∈
        slMatrices n k := by
      rw [slMatrices, LinearMap.mem_ker, Matrix.traceLinearMap_apply, Matrix.trace_sub,
        Matrix.trace_single_eq_same, Matrix.trace_single_eq_same, sub_self]
    have h := horth _ hsingle
    rw [matDot_sub, matDot_single_right, matDot_single_right] at h
    exact sub_eq_zero.mp h
  rw [Submodule.mem_span_singleton]
  refine ⟨X (idxZero hn) (idxZero hn), ?_⟩
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hi0 : i = idxZero hn
    · subst hi0
      simp
    · rw [hdiag i hi0]
      simp
  · rw [hoff i j hij]
    simp [hij]

theorem sl_le_bCyc_map [CharP k 2] (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    slMatrices n k ≤ (bCyc (k := k) ε).map (bPsi hn hε hε').toLinearMap := by
  let C := (bCyc (k := k) ε).map (bPsi hn hε hε').toLinearMap
  change slMatrices n k ≤ C
  have memC : ∀ w ∈ bCyc (k := k) ε, bPsi hn hε hε' w ∈ C := fun w hw =>
    Submodule.mem_map.mpr ⟨w, hw, rfl⟩
  have hE : ∀ i j : Fin n, i ≠ j → Matrix.single i j (1 : k) ∈ C := by
    intro i j hij
    by_cases hj0 : j = idxZero hn
    · subst hj0
      have hi0 : i ≠ idxZero hn := fun h => hij h
      rw [← bPsi_uE1 hn hε hε' hi0]
      exact memC _ (uE1_mem hn hε hε' i)
    · by_cases hi0 : i = idxZero hn
      · subst hi0
        by_cases hjs : j = idxLast hn
        · subst hjs
          rw [← bPsi_bvec hn hε hε']
          exact memC _ (mem_cyclicSub_self _ _)
        · rw [← bPsi_bDer_bvec_second hn hε hε' j hj0 hjs]
          exact memC _ (mulVec_mem_cyclicSub _ (mem_cyclicSub_self _ _))
      · rw [← bPsi_uE0 hn hε hε' hi0 hij hj0]
        exact memC _ (uE0_mem hn hε hε' i j)
  have hD : ∀ i : Fin n, i ≠ idxZero hn →
      Matrix.single i i (1 : k) - Matrix.single (idxZero hn) (idxZero hn) (1 : k) ∈ C := by
    intro i hi0
    have h := memC _ (uD_mem hn hε hε' i)
    rw [bPsi_uD hn hε hε' hi0] at h
    rwa [matrix_sub_eq_add]
  intro X hX
  have hXtrace : Matrix.trace X = 0 := by
    rw [slMatrices, LinearMap.mem_ker, Matrix.traceLinearMap_apply] at hX
    exact hX
  rw [matrix_eq_offdiag_add_D hn hXtrace]
  apply Submodule.add_mem
  · apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro j _
    by_cases hij : i = j
    · rw [if_pos hij, zero_smul]
      exact Submodule.zero_mem C
    · rw [if_neg hij]
      exact Submodule.smul_mem C _ (hE i j hij)
  · apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem C _ (hD i (Finset.mem_erase.mp hi).1)

theorem bPsi_bCyc_eq [CharP k 2] (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    (bCyc (k := k) ε).map (bPsi hn hε hε').toLinearMap = slMatrices n k :=
  le_antisymm (bCyc_map_bPsi_le_sl hn hε hε') (sl_le_bCyc_map hn hε hε')

theorem bPsi_bRad_le_slScalars [CharP k 2] (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    (bRad (k := k) ε).map (bPsi hn hε hε').toLinearMap ≤
      (slScalars n k).map (slMatrices n k).subtype := by
  intro X hX
  rw [Submodule.mem_map] at hX
  obtain ⟨x, hx, rfl⟩ := hX
  have hxcyc : x ∈ bCyc (k := k) ε := (mem_dotRad.mp hx).1
  have hspan : bPsi hn hε hε' x ∈
      Submodule.span k {(1 : Matrix (Fin n) (Fin n) k)} := by
    refine mem_span_one_of_forall_matDot_eq_zero hn ?_
    intro Y hY
    rw [← bPsi_bCyc_eq hn hε hε'] at hY
    rw [Submodule.mem_map] at hY
    obtain ⟨y, hy, hyY⟩ := hY
    rw [← hyY]
    change matDot (bPsi hn hε hε' x) (bPsi hn hε hε' y) = 0
    rw [bPsi_dotProduct]
    exact (mem_dotRad.mp hx).2 y hy
  exact Submodule.mem_map.mpr
    ⟨⟨bPsi hn hε hε' x, bCyc_map_bPsi_le_sl hn hε hε'
        (Submodule.mem_map.mpr ⟨x, hxcyc, rfl⟩)⟩,
      Submodule.mem_comap.mpr hspan, rfl⟩

theorem slScalars_le_bPsi_bRad [CharP k 2] (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    (slScalars n k).map (slMatrices n k).subtype ≤
      (bRad (k := k) ε).map (bPsi hn hε hε').toLinearMap := by
  intro X hX
  rw [Submodule.mem_map] at hX
  obtain ⟨z, hz, rfl⟩ := hX
  have hzspan : (z : Matrix (Fin n) (Fin n) k) ∈
      Submodule.span k {(1 : Matrix (Fin n) (Fin n) k)} :=
    Submodule.mem_comap.mp hz
  rw [Submodule.mem_span_singleton] at hzspan
  obtain ⟨c, hc⟩ := hzspan
  have hzcyc : (z : Matrix (Fin n) (Fin n) k) ∈
      (bCyc (k := k) ε).map (bPsi hn hε hε').toLinearMap := by
    rw [bPsi_bCyc_eq hn hε hε']
    exact z.2
  rw [Submodule.mem_map] at hzcyc
  obtain ⟨w, hw, hwz⟩ := hzcyc
  have hwrad : w ∈ bRad (k := k) ε := by
    refine mem_dotRad.mpr ⟨hw, ?_⟩
    intro y hy
    have hysl : bPsi hn hε hε' y ∈ slMatrices n k :=
      bCyc_map_bPsi_le_sl hn hε hε' (Submodule.mem_map.mpr ⟨y, hy, rfl⟩)
    have hytrace : Matrix.trace (bPsi hn hε hε' y) = 0 := by
      rw [slMatrices, LinearMap.mem_ker, Matrix.traceLinearMap_apply] at hysl
      exact hysl
    calc w ⬝ᵥ y = matDot (bPsi hn hε hε' w) (bPsi hn hε hε' y) :=
          (bPsi_dotProduct hn hε hε' w y).symm
      _ = matDot (z : Matrix (Fin n) (Fin n) k) (bPsi hn hε hε' y) := by
            show matDot ((bPsi hn hε hε').toLinearMap w)
                ((bPsi hn hε hε').toLinearMap y) =
              matDot (z : Matrix (Fin n) (Fin n) k) ((bPsi hn hε hε').toLinearMap y)
            rw [hwz]
      _ = matDot (c • (1 : Matrix (Fin n) (Fin n) k)) (bPsi hn hε hε' y) := by rw [hc]
      _ = c * Matrix.trace (bPsi hn hε hε' y) := matDot_smul_one c _
      _ = 0 := by rw [hytrace, mul_zero]
  exact Submodule.mem_map.mpr ⟨w, hwrad, hwz⟩

theorem bRad_map_bPsi_eq_slScalars [CharP k 2] (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    (bRad (k := k) ε).map (bPsi hn hε hε').toLinearMap =
      (slScalars n k).map (slMatrices n k).subtype :=
  le_antisymm (bPsi_bRad_le_slScalars hn hε hε') (slScalars_le_bPsi_bRad hn hε hε')

@[expose]
noncomputable def bPsiCyc [CharP k 2] (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    (bCyc (k := k) ε) ≃ₗ[k] slMatrices n k :=
  (bPsi hn hε hε').ofSubmodules (bCyc (k := k) ε) (slMatrices n k)
    (bPsi_bCyc_eq hn hε hε')

@[simp]
theorem bPsiCyc_apply_coe [CharP k 2] (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅)
    (w : bCyc (k := k) ε) :
    ((bPsiCyc hn hε hε' w : slMatrices n k) : Matrix (Fin n) (Fin n) k) =
      bPsi hn hε hε' (w : BIdx ε → k) := rfl

theorem bRad_map_bPsiCyc_eq_slScalars [CharP k 2] (hn : 3 ≤ n)
    (hε : ε r₀ = {idxOne hn, idxLast hn}) (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    ((bRad (k := k) ε).comap (bCyc (k := k) ε).subtype).map
        (bPsiCyc hn hε hε').toLinearMap =
      slScalars n k := by
  ext z
  constructor
  · intro hz
    rw [Submodule.mem_map] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    have hwrad : (w : BIdx ε → k) ∈ bRad (k := k) ε := Submodule.mem_comap.mp hw
    have hwzmat : bPsi hn hε hε' (w : BIdx ε → k) =
        (z : Matrix (Fin n) (Fin n) k) := by
      simpa [bPsiCyc_apply_coe] using
        congrArg (fun t : slMatrices n k => (t : Matrix (Fin n) (Fin n) k)) hwz
    have hzmat : (z : Matrix (Fin n) (Fin n) k) ∈
        (bRad (k := k) ε).map (bPsi hn hε hε').toLinearMap := by
      rw [← hwzmat]
      exact Submodule.mem_map.mpr ⟨(w : BIdx ε → k), hwrad, rfl⟩
    rw [bRad_map_bPsi_eq_slScalars hn hε hε'] at hzmat
    rw [Submodule.mem_map] at hzmat
    obtain ⟨z', hz', hz'eq⟩ := hzmat
    have hzz' : z' = z := Subtype.ext hz'eq
    rwa [hzz'] at hz'
  · intro hz
    have hzmap : (z : Matrix (Fin n) (Fin n) k) ∈
        (bRad (k := k) ε).map (bPsi hn hε hε').toLinearMap := by
      rw [bRad_map_bPsi_eq_slScalars hn hε hε']
      exact Submodule.mem_map.mpr ⟨z, hz, rfl⟩
    rw [Submodule.mem_map] at hzmap
    obtain ⟨w, hwrad, hwz⟩ := hzmap
    have hwcyc : w ∈ bCyc (k := k) ε := (mem_dotRad.mp hwrad).1
    have hwP : (⟨w, hwcyc⟩ : bCyc (k := k) ε) ∈
        (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype :=
      Submodule.mem_comap.mpr hwrad
    refine Submodule.mem_map.mpr ⟨⟨w, hwcyc⟩, hwP, ?_⟩
    apply Subtype.ext
    simpa [bPsiCyc_apply_coe] using hwz

end AdjointHeartModel

open AdjointHeartModel in
theorem exists_bModel_equiv_adjointHeart [CharP k 2] (hn : 3 ≤ n)
    (ε : τ → Finset (Fin n)) (r₀ : τ)
    (hε : ε r₀ = {⟨1, by omega⟩, ⟨n - 1, by omega⟩})
    (hε' : ∀ r, r ≠ r₀ → ε r = ∅) :
    ∃ Φ : BModel k ε ≃ₗ[k] CFSG.HardMathSupport.GuralnickMalle.AdjointHeart n k,
      ∀ (h : τ → Matrix.SpecialLinearGroup (Fin n) k) (x : BModel k ε),
        Φ (bRep ε h x) =
          CFSG.HardMathSupport.GuralnickMalle.adjointHeartRep n k
            (Matrix.SpecialLinearGroup.toGL (h r₀)) (Φ x) := by
  have hεb : ε r₀ = {idxOne hn, idxLast hn} := by
    simpa [idxOne, idxLast] using hε
  let Φ : BModel k ε ≃ₗ[k] CFSG.HardMathSupport.GuralnickMalle.AdjointHeart n k :=
    Submodule.Quotient.equiv
      ((bRad (k := k) ε).comap (bCyc (k := k) ε).subtype)
      (slScalars n k) (bPsiCyc hn hεb hε')
      (bRad_map_bPsiCyc_eq_slScalars hn hεb hε')
  have hΦ : ∀ w : bCyc (k := k) ε,
      Φ (Submodule.Quotient.mk w) =
        Submodule.Quotient.mk (bPsiCyc hn hεb hε' w) := by
    intro w
    simp [Φ, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  refine ⟨Φ, ?_⟩
  intro h x
  induction x using Submodule.Quotient.induction_on with
  | H w =>
    rw [hΦ w]
    rw [bRep_mk]
    rw [hΦ]
    rw [adjointHeartRep_mk]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    simp only [bPsiCyc_apply_coe]
    rw [bPsi_bMat_mulVec_inv hn hεb hε'
      (fun r => (h r : Matrix (Fin n) (Fin n) k)) (h r₀).2]
    simp [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

end CFSG.LieType.SpecialLinear.ExteriorModel
