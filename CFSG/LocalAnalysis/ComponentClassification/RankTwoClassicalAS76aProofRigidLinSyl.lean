module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalModelFactsPrimary
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourRoots

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ABGLocalTools
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Root

variable {K : Type} [Field K] {k : ℕ}

variable (K) in
@[expose] def stdCen (hk : 2 ≤ k) : Subgroup (SpecialLinearGroup (Fin (2 + k)) K) :=
  centralizer ({trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) (1 : K)} :
    Set (SpecialLinearGroup (Fin (2 + k)) K))

theorem trSL_mem_stdCen (hk : 2 ≤ k) {i j : Fin (2 + k)} (hij : i ≠ j) (hiv : i ≠ idxV hk)
    (hju : j ≠ idxU hk) (a : K) : trSL i j hij a ∈ stdCen K hk := by
  rw [stdCen, mem_centralizer_singleton_iff]
  exact trSL_commute hij (idxU_ne_idxV hk) hju (Ne.symm hiv) a 1

theorem blkSL₁_range_le_perfectCore (hk : 2 ≤ k) (h4 : 4 ≤ Nat.card K) :
    (blkSL₁ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin (2 + k)) K).range ≤
      perfectCore (stdCen K hk) := by
  have hmat : ((trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) (1 : K) :
      SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      blk 1 (1 + single ⟨0, by omega⟩ ⟨1, by omega⟩ 1) := by
    rw [← one_add_smul_stdE hk, one_smul, stdE_eq_single]
    rfl
  have hL : (blkSL₁ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin (2 + k)) K).range ≤
      stdCen K hk := by
    rintro _ ⟨X, rfl⟩
    rw [stdCen, mem_centralizer_singleton_iff]
    apply Subtype.ext
    change blk (X : Matrix (Fin 2) (Fin 2) K) 1 *
        ((trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) (1 : K) :
          SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      ((trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) (1 : K) :
        SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
        blk (X : Matrix (Fin 2) (Fin 2) K) 1
    rw [hmat, blk_mul, blk_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul]
  have hperf : ⁅(blkSL₁ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin (2 + k)) K).range,
      (blkSL₁ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin (2 + k)) K).range⁆ =
      (blkSL₁ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin (2 + k)) K).range := by
    have hP := (CFSG.RankThree.PartOne.KCOrthogonal.sl2_isPerfect h4).commutator_eq_top
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def, hP]
  exact CFSG.Quasithin.le_perfectCore_of_perfect hL hperf

@[expose] def trTwo (i j : Fin 2) (hij : i ≠ j) (a : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨1 + single i j a, det_transvection_of_ne i j hij a⟩

theorem blkSL₁_trTwo (i j : Fin 2) (hij : i ≠ j) (a : K) :
    (blkSL₁ (trTwo i j hij a) : SpecialLinearGroup (Fin (2 + k)) K) =
      trSL (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))
        (finSumFinEquiv.injective.ne (by simpa using hij)) a := by
  apply Subtype.ext
  rw [coe_blkSL₁, coe_trSL]
  change blk (1 + single i j a) 1 = 1 + single _ _ a
  rw [← blk_single_zero, ← blk_one, blk_add, add_zero]

theorem trSL_inl_mem_perfectCore (hk : 2 ≤ k) (h4 : 4 ≤ Nat.card K) (a : K) :
    trSL (idxW k) (idxW' k) (idxW_ne_idxW' k) a ∈ perfectCore (stdCen K hk) ∧
      trSL (idxW' k) (idxW k) (idxW_ne_idxW' k).symm a ∈ perfectCore (stdCen K hk) := by
  constructor
  · have h := blkSL₁_range_le_perfectCore hk h4 ⟨trTwo 0 1 (by decide) a, rfl⟩
    rwa [blkSL₁_trTwo] at h
  · have h := blkSL₁_range_le_perfectCore hk h4 ⟨trTwo 1 0 (by decide) a, rfl⟩
    rwa [blkSL₁_trTwo] at h

theorem trSL_mem_of_comm_left (hk : 2 ≤ k) {i l j : Fin (2 + k)} (hil : i ≠ l) (hlj : l ≠ j)
    (hij : i ≠ j) {a : K} (h₁ : trSL i l hil 1 ∈ perfectCore (stdCen K hk))
    (h₂ : trSL l j hlj a ∈ stdCen K hk) : trSL i j hij a ∈ perfectCore (stdCen K hk) := by
  have h := commutatorElement_mem_perfectCore' h₂ h₁
  rwa [trSL_comm hil hlj hij, one_mul] at h

theorem trSL_mem_of_comm_right (hk : 2 ≤ k) {i l j : Fin (2 + k)} (hil : i ≠ l) (hlj : l ≠ j)
    (hij : i ≠ j) {a : K} (h₁ : trSL i l hil a ∈ stdCen K hk)
    (h₂ : trSL l j hlj 1 ∈ perfectCore (stdCen K hk)) :
    trSL i j hij a ∈ perfectCore (stdCen K hk) := by
  have h := commutatorElement_mem_perfectCore h₁ h₂
  rwa [trSL_comm hil hlj hij, mul_one] at h

theorem trSL_inl_left_mem_perfectCore (hk : 2 ≤ k) (h4 : 4 ≤ Nat.card K) {i j : Fin (2 + k)}
    (hi : i = idxW k ∨ i = idxW' k) (hij : i ≠ j) (hju : j ≠ idxU hk) (hjv : j ≠ idxV hk)
    (a : K) : trSL i j hij a ∈ perfectCore (stdCen K hk) := by
  rcases hi with rfl | rfl
  · by_cases hj : j = idxW' k
    · subst hj
      exact (trSL_inl_mem_perfectCore hk h4 a).1
    · exact trSL_mem_of_comm_left hk (idxW_ne_idxW' k) (Ne.symm hj) hij
        (trSL_inl_mem_perfectCore hk h4 1).1
        (trSL_mem_stdCen hk _ (idxW'_ne_idxV hk) hju a)
  · by_cases hj : j = idxW k
    · subst hj
      exact (trSL_inl_mem_perfectCore hk h4 a).2
    · exact trSL_mem_of_comm_left hk (idxW_ne_idxW' k).symm (Ne.symm hj) hij
        (trSL_inl_mem_perfectCore hk h4 1).2
        (trSL_mem_stdCen hk _ (idxW_ne_idxV hk) hju a)

theorem trSL_mid_mem_perfectCore (hk : 2 ≤ k) (h4 : 4 ≤ Nat.card K) {i j : Fin (2 + k)}
    (hij : i ≠ j) (hiv : i ≠ idxV hk) (hju : j ≠ idxU hk) (hjv : j ≠ idxV hk) (a : K) :
    trSL i j hij a ∈ perfectCore (stdCen K hk) := by
  by_cases hi : i = idxW k ∨ i = idxW' k
  · exact trSL_inl_left_mem_perfectCore hk h4 hi hij hju hjv a
  push Not at hi
  obtain ⟨l, hl, hlj⟩ : ∃ l, (l = idxW k ∨ l = idxW' k) ∧ l ≠ j := by
    by_cases hj : j = idxW k
    · exact ⟨idxW' k, .inr rfl, hj ▸ (idxW_ne_idxW' k).symm⟩
    · exact ⟨idxW k, .inl rfl, Ne.symm hj⟩
  have hil : i ≠ l := by rcases hl with rfl | rfl <;> [exact hi.1; exact hi.2]
  have hlu : l ≠ idxU hk := by
    rcases hl with rfl | rfl <;> [exact idxW_ne_idxU hk; exact idxW'_ne_idxU hk]
  have hlv : l ≠ idxV hk := by
    rcases hl with rfl | rfl <;> [exact idxW_ne_idxV hk; exact idxW'_ne_idxV hk]
  exact trSL_mem_of_comm_right hk hil hlj hij (trSL_mem_stdCen hk hil hiv hlu a)
    (trSL_inl_left_mem_perfectCore hk h4 hl hlj hju hjv 1)

theorem trSL_mem_perfectCore_stdCen (hk : 2 ≤ k) (h4 : 4 ≤ Nat.card K) {i j : Fin (2 + k)}
    (hij : i ≠ j) (hiv : i ≠ idxV hk) (hju : j ≠ idxU hk) (a : K) :
    trSL i j hij a ∈ perfectCore (stdCen K hk) := by
  by_cases hjv : j = idxV hk
  · subst hjv
    obtain ⟨l, hl, hil⟩ : ∃ l, (l = idxW k ∨ l = idxW' k) ∧ i ≠ l := by
      by_cases hi : i = idxW k
      · exact ⟨idxW' k, .inr rfl, hi ▸ idxW_ne_idxW' k⟩
      · exact ⟨idxW k, .inl rfl, hi⟩
    have hlu : l ≠ idxU hk := by
      rcases hl with rfl | rfl <;> [exact idxW_ne_idxU hk; exact idxW'_ne_idxU hk]
    have hlv : l ≠ idxV hk := by
      rcases hl with rfl | rfl <;> [exact idxW_ne_idxV hk; exact idxW'_ne_idxV hk]
    exact trSL_mem_of_comm_left hk hil hlv hij
      (trSL_mid_mem_perfectCore hk h4 hil hiv hlu hlv 1)
      (trSL_mem_stdCen hk hlv hlv (idxU_ne_idxV hk).symm a)
  · exact trSL_mid_mem_perfectCore hk h4 hij hiv hju hjv a

end Root

section Reindex

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def reindexAutSL (σ : Equiv.Perm (Fin n)) :
    MulAut (SpecialLinearGroup (Fin n) K) where
  toFun g := ⟨(g : Matrix (Fin n) (Fin n) K).submatrix σ.symm σ.symm, by
    rw [det_submatrix_equiv_self]
    exact g.2⟩
  invFun g := ⟨(g : Matrix (Fin n) (Fin n) K).submatrix σ σ, by
    rw [det_submatrix_equiv_self]
    exact g.2⟩
  left_inv g := Subtype.ext (by simp [Matrix.submatrix_submatrix])
  right_inv g := Subtype.ext (by simp [Matrix.submatrix_submatrix])
  map_mul' g h := Subtype.ext (by
    change ((g : Matrix (Fin n) (Fin n) K) * h).submatrix σ.symm σ.symm =
      (g : Matrix (Fin n) (Fin n) K).submatrix σ.symm σ.symm *
        (h : Matrix (Fin n) (Fin n) K).submatrix σ.symm σ.symm
    rw [Matrix.submatrix_mul_equiv])

theorem reindexAutSL_trSL (σ : Equiv.Perm (Fin n)) {i j : Fin n} (hij : i ≠ j) (a : K) :
    reindexAutSL σ (trSL i j hij a) = trSL (σ i) (σ j) (σ.injective.ne hij) a := by
  apply Subtype.ext
  change (1 + single i j a : Matrix (Fin n) (Fin n) K).submatrix σ.symm σ.symm =
    1 + single (σ i) (σ j) a
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply, single_apply,
    Equiv.eq_symm_apply, Equiv.apply_symm_apply]

omit [Field K] in
theorem rootElt_eq_trSL [Field K] {i j : Fin n} (hij : i ≠ j) (a : K) :
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.rootElt i j a = trSL i j hij a :=
  Subtype.ext (CFSG.LocalAnalysis.ComponentInitial.LinearCover.coe_rootElt_of_ne hij a)

end Reindex

section Sylow

variable {K : Type} [Field K] {k : ℕ}

theorem exists_perm_first_last (hk : 2 ≤ k) : ∃ σ : Equiv.Perm (Fin (2 + k)),
    σ ⟨0, by omega⟩ = idxU hk ∧ σ ⟨1 + k, by omega⟩ = idxV hk := by
  set o : Fin (2 + k) := ⟨0, by omega⟩
  set l : Fin (2 + k) := ⟨1 + k, by omega⟩
  have hol : o ≠ l := by
    simp only [o, l, ne_eq, Fin.mk.injEq]
    omega
  set τ := Equiv.swap o (idxU hk)
  refine ⟨τ.trans (Equiv.swap (τ l) (idxV hk)), ?_, ?_⟩
  · have hτo : τ o = idxU hk := Equiv.swap_apply_left _ _
    rw [Equiv.trans_apply, hτo, Equiv.swap_apply_of_ne_of_ne _ (idxU_ne_idxV hk)]
    intro h
    exact hol (τ.injective (hτo.trans h))
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]

theorem reindex_unitriangular_le_perfectCore (hk : 2 ≤ k) (h4 : 4 ≤ Nat.card K)
    {σ : Equiv.Perm (Fin (2 + k))} (hσ0 : σ ⟨0, by omega⟩ = idxU hk)
    (hσl : σ ⟨1 + k, by omega⟩ = idxV hk) :
    (unitriangular (2 + k) K).map (reindexAutSL σ).toMonoidHom ≤ perfectCore (stdCen K hk) := by
  refine (map_mono
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.unitriangular_le_closure_rootElt).trans ?_
  rw [MonoidHom.map_closure, closure_le]
  rintro _ ⟨g, ⟨i, j, a, hij, rfl⟩, rfl⟩
  rw [MulEquiv.coe_toMonoidHom, rootElt_eq_trSL hij.ne, reindexAutSL_trSL]
  refine trSL_mem_perfectCore_stdCen hk h4 _ ?_ ?_ a
  · rw [← hσl]
    refine σ.injective.ne fun h => ?_
    have := j.2
    rw [h] at hij
    simp only [Fin.lt_def] at hij
    omega
  · rw [← hσ0]
    refine σ.injective.ne fun h => ?_
    rw [h] at hij
    simp only [Fin.lt_def] at hij
    omega

theorem isSylowOf_reindex_unitriangular [Finite K] [CharP K 2] (hk : 2 ≤ k)
    (σ : Equiv.Perm (Fin (2 + k))) :
    IsSylowOf 2 ((unitriangular (2 + k) K).map (reindexAutSL σ).toMonoidHom) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := 2 + k) (by omega)
  refine isSylowOf_of_card le_top ?_
  rw [Subgroup.card_map_of_injective (reindexAutSL σ).injective, card_top, ← hP,
    P.card_eq_multiplicity]

theorem exists_isSylowOf_le_perfectCore_stdCen [Finite K] [CharP K 2] (hk : 2 ≤ k)
    (h4 : 4 ≤ Nat.card K) : ∃ S : Subgroup (SpecialLinearGroup (Fin (2 + k)) K),
      IsSylowOf 2 S ⊤ ∧ S ≤ perfectCore (stdCen K hk) := by
  obtain ⟨σ, hσ0, hσl⟩ := exists_perm_first_last hk
  exact ⟨_, isSylowOf_reindex_unitriangular hk σ,
    reindex_unitriangular_le_perfectCore hk h4 hσ0 hσl⟩

theorem isSylowOf_map_top {G H : Type*} [Group G] [Group H] [Finite G] [Finite H] {p : ℕ}
    [Fact p.Prime] {S : Subgroup G} (hS : IsSylowOf p S ⊤) {f : G →* H}
    (hf : Function.Surjective f) : IsSylowOf p (S.map f) ⊤ := by
  rw [isSylowOf_iff] at hS ⊢
  obtain ⟨-, hP, hdvd⟩ := hS
  refine ⟨le_top, hP.map f, fun h => hdvd ?_⟩
  rw [Subgroup.relIndex_top_right] at h ⊢
  exact h.trans (Subgroup.index_map_dvd _ hf)

theorem exists_isSylowOf_le_perfectCore_proj [Finite K] [CharP K 2] (hk : 2 ≤ k)
    (h4 : 4 ≤ Nat.card K) : ∃ S : Subgroup (projectiveSL (2 + k) K), IsSylowOf 2 S ⊤ ∧
      S ≤ perfectCore (centralizer ({(proj (2 + k) K
        (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) (1 : K)))} :
          Set (projectiveSL (2 + k) K))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hSle⟩ := exists_isSylowOf_le_perfectCore_stdCen hk h4
  refine ⟨S.map (proj (2 + k) K), isSylowOf_map_top hS (proj_surjective _ _), ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  exact map_mem_perfectCore_of_le _ (map_centralizer_le _ _) (hSle hg)

end Sylow

section Commutant

variable {K : Type} [Field K]

theorem eq_smul_one_add_single_of_commute_simple {n : ℕ} (hn : 0 < n)
    {g : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (h : ∀ i : Fin n, g * single i.castSucc i.succ 1 = single i.castSucc i.succ 1 * g) :
    ∃ a b : K, g = a • 1 + single 0 (Fin.last n) b := by
  have hcol : ∀ (i : Fin n) (x : Fin (n + 1)), x ≠ i.castSucc → g x i.castSucc = 0 := by
    intro i x hx
    have := congrFun (congrFun (h i) x) i.succ
    rwa [mul_single_apply_same, mul_one, single_mul_apply_of_ne _ _ _ _ _ hx] at this
  have hrow : ∀ (i : Fin n) (y : Fin (n + 1)), y ≠ i.succ → g i.succ y = 0 := by
    intro i y hy
    have := congrFun (congrFun (h i) i.castSucc) y
    rwa [mul_single_apply_of_ne _ _ _ _ _ hy, single_mul_apply_same, one_mul, eq_comm] at this
  have hdiag : ∀ i : Fin n, g i.castSucc i.castSucc = g i.succ i.succ := by
    intro i
    have := congrFun (congrFun (h i) i.castSucc) i.succ
    rwa [mul_single_apply_same, mul_one, single_mul_apply_same, one_mul] at this
  have hd : ∀ x : Fin (n + 1), g x x = g 0 0 := by
    intro x
    induction x using Fin.induction with
    | zero => rfl
    | succ i ih => rw [← hdiag i, ih]
  have h0l : (0 : Fin (n + 1)) ≠ Fin.last n := by
    rw [ne_eq, Fin.ext_iff]
    simp only [Fin.val_zero, Fin.val_last]
    omega
  refine ⟨g 0 0, g 0 (Fin.last n), ?_⟩
  ext x y
  rw [Matrix.add_apply, Matrix.smul_apply, single_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [one_apply_eq, smul_eq_mul, mul_one, hd x]
    split_ifs with h0
    · exact absurd (h0.1.trans h0.2.symm) h0l
    · rw [add_zero]
  rw [one_apply_ne hxy, smul_zero, zero_add]
  split_ifs with h0
  · rw [← h0.1, ← h0.2]
  · by_cases hy : y = Fin.last n
    · subst hy
      have hx : x ≠ 0 := fun hx => h0 ⟨hx.symm, rfl⟩
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr hx
      exact hrow i _ (Ne.symm hxy)
    · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hy
      exact hcol i x hxy

theorem eq_smul_one_add_single_of_commute_equiv {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (hn : 0 < n) (σ : Fin (n + 1) ≃ ι) {g : Matrix ι ι K}
    (h : ∀ i : Fin n, g * single (σ i.castSucc) (σ i.succ) 1 =
      single (σ i.castSucc) (σ i.succ) 1 * g) :
    ∃ a b : K, g = a • 1 + single (σ 0) (σ (Fin.last n)) b := by
  have hs : ∀ x y : Fin (n + 1), (single (σ x) (σ y) (1 : K)).submatrix σ σ = single x y 1 := by
    intro x y
    ext i j
    simp only [submatrix_apply, single_apply, Equiv.apply_eq_iff_eq]
  obtain ⟨a, b, hab⟩ := eq_smul_one_add_single_of_commute_simple hn (g := g.submatrix σ σ)
    fun i => by
      rw [← hs, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h i]
  refine ⟨a, b, ?_⟩
  have hg : g = (g.submatrix σ σ).submatrix σ.symm σ.symm := by
    simp [Matrix.submatrix_submatrix]
  rw [hg, hab]
  ext x y
  simp only [submatrix_apply, Matrix.add_apply, Matrix.smul_apply, one_apply, single_apply,
    Equiv.eq_symm_apply, Equiv.apply_symm_apply]

theorem trSL_mul_self_charTwo [CharP K 2] {n : ℕ} {x y : Fin n} (hxy : x ≠ y) :
    trSL x y hxy (1 : K) * trSL x y hxy 1 = 1 := by
  rw [trSL_mul, CharTwo.add_self_eq_zero]
  exact Subtype.ext (transvection_zero x y)

theorem commute_of_proj_commute_trSL [CharP K 2] {n : ℕ} {z : SpecialLinearGroup (Fin n) K}
    {x y : Fin n} (hxy : x ≠ y)
    (h : proj n K z * proj n K (trSL x y hxy 1) = proj n K (trSL x y hxy 1) * proj n K z) :
    z * trSL x y hxy 1 = trSL x y hxy 1 * z := by
  set t := trSL x y hxy (1 : K)
  rw [← map_mul, ← map_mul, proj_eq_proj_iff] at h
  set w := (z * t)⁻¹ * (t * z) with hwdef
  have hwc : w ∈ Subgroup.center _ := scalars_le_center n K h
  have htz : t * z = z * t * w := by rw [hwdef]; group
  have hcomm : Commute t w := Subgroup.mem_center_iff.mp hwc t
  have hw2 : w ^ 2 = 1 := by
    have h1 : (z⁻¹ * t * z) ^ 2 = 1 := by
      rw [sq, show z⁻¹ * t * z * (z⁻¹ * t * z) = z⁻¹ * (t * t) * z by group,
        trSL_mul_self_charTwo, mul_one, inv_mul_cancel]
    have h2 : z⁻¹ * t * z = t * w := by
      rw [mul_assoc, htz]
      group
    rw [h2, hcomm.mul_pow, sq t, trSL_mul_self_charTwo, one_mul] at h1
    exact h1
  obtain ⟨c, -, hc⟩ := h
  have hc2 : (c : K) ^ 2 = 1 := by
    have hm : ((w : Matrix (Fin n) (Fin n) K) ^ 2) x x = 1 := by
      have := congrArg (fun M : SpecialLinearGroup (Fin n) K =>
        (M : Matrix (Fin n) (Fin n) K) x x) hw2
      simpa [SpecialLinearGroup.coe_pow] using this
    rw [hc, ← map_pow, scalar_apply, diagonal_apply_eq] at hm
    exact hm
  have hw1 : w = 1 := by
    apply Subtype.ext
    rw [hc, eq_one_of_sq_eq_one_of_charTwo hc2, map_one]
    rfl
  rw [hw1, mul_one] at htz
  exact htz.symm

end Commutant

section Centralizer

variable {K : Type} [Field K] {k : ℕ}

theorem exists_eq_proj_trSL_of_commute [CharP K 2] (hk : 2 ≤ k)
    {σ : Equiv.Perm (Fin (2 + k))} (hσ0 : σ ⟨0, by omega⟩ = idxU hk)
    (hσl : σ ⟨1 + k, by omega⟩ = idxV hk) {z : projectiveSL (2 + k) K}
    (hz : ∀ s ∈ (unitriangular (2 + k) K).map (reindexAutSL σ).toMonoidHom,
      z * proj (2 + k) K s = proj (2 + k) K s * z) :
    ∃ β : K, z = proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) β) := by
  obtain ⟨z, rfl⟩ := proj_surjective _ _ z
  set σ' : Fin (k + 1 + 1) ≃ Fin (2 + k) := (finCongr (by omega)).trans σ
  have hσ'0 : σ' 0 = idxU hk := by
    rw [← hσ0]
    rfl
  have hσ'l : σ' (Fin.last (k + 1)) = idxV hk := by
    rw [← hσl]
    simp only [σ', Equiv.trans_apply, finCongr_apply]
    congr 1
    ext
    simp only [Fin.val_cast, Fin.val_last]
    omega
  have hcomm : ∀ i : Fin (k + 1), z * trSL (σ' i.castSucc) (σ' i.succ)
      (σ'.injective.ne (Fin.castSucc_lt_succ (i := i)).ne) 1 =
      trSL (σ' i.castSucc) (σ' i.succ)
        (σ'.injective.ne (Fin.castSucc_lt_succ (i := i)).ne) 1 * z := by
    intro i
    refine commute_of_proj_commute_trSL _ (hz _ ?_)
    have hlt : finCongr (by omega : k + 1 + 1 = 2 + k) i.castSucc <
        finCongr (by omega : k + 1 + 1 = 2 + k) i.succ := by
      simp only [finCongr_apply, Fin.lt_def, Fin.val_cast, Fin.val_castSucc, Fin.val_succ]
      omega
    refine ⟨CFSG.LocalAnalysis.ComponentInitial.LinearCover.rootElt _ _ 1,
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.rootElt_mem_unitriangular hlt 1, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, rootElt_eq_trSL hlt.ne, reindexAutSL_trSL]
    rfl
  have hmat : ∀ i : Fin (k + 1), (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *
      single (σ' i.castSucc) (σ' i.succ) 1 =
      single (σ' i.castSucc) (σ' i.succ) 1 * (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) := by
    intro i
    have h := congrArg (fun g : SpecialLinearGroup (Fin (2 + k)) K =>
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K)) (hcomm i)
    change (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * (1 + single _ _ 1) =
      (1 + single _ _ 1) * (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) at h
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact add_left_cancel h
  obtain ⟨a, b, hab⟩ := eq_smul_one_add_single_of_commute_equiv (by omega) σ' hmat
  rw [hσ'0, hσ'l] at hab
  have huv := idxU_ne_idxV hk
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at hab
    have h1 : ((z * z : SpecialLinearGroup (Fin (2 + k)) K) : Matrix (Fin (2 + k)) (Fin (2 + k)) K)
        = 0 := by
      change (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * z = 0
      rw [hab, single_mul_single_of_ne _ _ _ _ huv.symm]
    have : Nonempty (Fin (2 + k)) := ⟨idxU hk⟩
    have h2 := (z * z).2
    rw [h1, det_zero] at h2
    exact zero_ne_one h2
  have hz : (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      scalar (Fin (2 + k)) a * (1 + single (idxU hk) (idxV hk) (a⁻¹ * b)) := by
    rw [hab, scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, smul_add,
      smul_single, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  have hds : det (scalar (Fin (2 + k)) a) = a ^ (2 + k) := by
    rw [scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hdet : a ^ (2 + k) = 1 := by
    have h := z.2
    rw [hz, det_mul, hds, ← transvection, det_transvection_of_ne _ _ huv, mul_one] at h
    exact h
  set c : SpecialLinearGroup (Fin (2 + k)) K := ⟨scalar (Fin (2 + k)) a, by rw [hds, hdet]⟩
  have hc : c ∈ scalars (2 + k) K :=
    ⟨Units.mk0 a ha, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hdet,
      Units.val_one]), rfl⟩
  have hzc : z = c * trSL (idxU hk) (idxV hk) huv (a⁻¹ * b) := by
    apply Subtype.ext
    rw [hz]
    rfl
  refine ⟨a⁻¹ * b, ?_⟩
  rw [hzc, map_mul, proj_eq_one_iff.mpr hc, one_mul]

theorem exists_eq_proj_trSL_of_mem_centralizer [CharP K 2] (hk : 2 ≤ k) (h4 : 4 ≤ Nat.card K)
    {z : projectiveSL (2 + k) K}
    (hz : z ∈ centralizer (perfectCore (centralizer ({(proj (2 + k) K
      (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) (1 : K)))} : Set (projectiveSL (2 + k) K))) :
        Set (projectiveSL (2 + k) K))) :
    ∃ β : K, z = proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) β) := by
  obtain ⟨σ, hσ0, hσl⟩ := exists_perm_first_last hk
  refine exists_eq_proj_trSL_of_commute hk hσ0 hσl fun s hs => ?_
  have hmem := map_mem_perfectCore_of_le (proj (2 + k) K) (map_centralizer_le _ _)
    (reindex_unitriangular_le_perfectCore hk h4 hσ0 hσl hs)
  exact (mem_centralizer_iff.mp hz _ hmem).symm

theorem exists_conj_eq_proj_stdT [Finite K] [CharP K 2] (hk : 2 ≤ k) {z : projectiveSL (2 + k) K}
    (hz2 : orderOf z = 2) (hS : ∃ S : Subgroup (projectiveSL (2 + k) K), IsSylowOf 2 S ⊤ ∧
      S ≤ centralizer ({z} : Set (projectiveSL (2 + k) K))) :
    ∃ a : projectiveSL (2 + k) K,
      a * z * a⁻¹ = proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) (1 : K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hSz⟩ := hS
  obtain ⟨σ, hσ0, hσl⟩ := exists_perm_first_last hk
  have hS₀ := isSylowOf_map_top (isSylowOf_reindex_unitriangular (K := K) hk σ)
    (proj_surjective (2 + k) K)
  obtain ⟨y, -, hy⟩ := CFSG.ComponentClassification.AS76b.Lemma22.exists_conj_eq_of_isSylowOf
    hS hS₀
  have hz' : ∀ s ∈ (unitriangular (2 + k) K).map (reindexAutSL σ).toMonoidHom,
      y * z * y⁻¹ * proj (2 + k) K s = proj (2 + k) K s * (y * z * y⁻¹) := by
    intro s hs
    have h1 : proj (2 + k) K s ∈ CFSG.ComponentClassification.AS76b.Lemma34.conj S y := by
      rw [← hy]
      exact mem_map_of_mem _ hs
    rw [CFSG.ComponentClassification.AS76b.Lemma34.mem_conj_iff] at h1
    have h2 := mem_centralizer_singleton_iff.mp (hSz h1)
    calc y * z * y⁻¹ * proj (2 + k) K s
        = y * (z * (y⁻¹ * proj (2 + k) K s * y)) * y⁻¹ := by group
      _ = y * (y⁻¹ * proj (2 + k) K s * y * z) * y⁻¹ := by rw [h2]
      _ = proj (2 + k) K s * (y * z * y⁻¹) := by group
  obtain ⟨β, hβ⟩ := exists_eq_proj_trSL_of_commute hk hσ0 hσl hz'
  have huv := idxU_ne_idxV hk
  have hβ0 : β ≠ 0 := by
    rintro rfl
    have h0 : trSL (idxU hk) (idxV hk) huv (0 : K) = 1 :=
      Subtype.ext (transvection_zero (idxU hk) (idxV hk))
    rw [h0, map_one, mul_inv_eq_one, mul_eq_left] at hβ
    rw [hβ, orderOf_one] at hz2
    exact absurd hz2 (by decide)
  set d := CFSG.LocalAnalysis.ComponentInitial.LinearCover.diagElt
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.corootVec (idxU hk) (idxW k) β⁻¹)
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.prod_corootVec _ _ (inv_ne_zero hβ0))
  have hd : d * trSL (idxU hk) (idxV hk) huv β * d⁻¹ = trSL (idxU hk) (idxV hk) huv 1 := by
    rw [← rootElt_eq_trSL huv, ← rootElt_eq_trSL huv,
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.diagElt_conj_rootElt,
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.corootVec_apply_left
        (idxW_ne_idxU hk).symm,
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.corootVec_apply_of_ne huv.symm
        (idxW_ne_idxV hk).symm, inv_one, mul_one, inv_mul_cancel₀ hβ0]
  refine ⟨proj (2 + k) K d * y, ?_⟩
  rw [show proj (2 + k) K d * y * z * (proj (2 + k) K d * y)⁻¹ =
      proj (2 + k) K d * (y * z * y⁻¹) * (proj (2 + k) K d)⁻¹ by group, hβ, ← map_inv,
    ← map_mul, ← map_mul, hd]

end Centralizer

end CFSG.ComponentClassification.RankTwoClassical
