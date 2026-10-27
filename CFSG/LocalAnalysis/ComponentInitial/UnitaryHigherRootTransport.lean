module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRootData
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherDescents

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (IsLinePerm epsAct epsAct_one
  isLinePerm_signedPerm)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (rootVec posRoots simpleRefl
  simpleRefl_mem simpleSnd inl_ne_simpleSnd epsAct_rootVec epsAct_inv_epsAct
  rootVec_mem_posRoots_iff flagOrder_swap)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (flagOrder flagOrder_inl flagOrder_inr)
open CFSG.LieType.Universal.SpecialLinear (signedPerm)

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

section Monomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem monomial_mul_single {σ : Equiv.Perm ι} {M : Matrix ι ι K} (hM : IsLinePerm σ M)
    (a b : ι) (c : K) : M * single a b c = single (σ a) b (M (σ a) a * c) := by
  ext y z
  rw [mul_apply, Finset.sum_eq_single a, single_apply, single_apply]
  · by_cases hy : y = σ a
    · subst hy
      simp
    · rw [hM.apply_eq_zero hy, zero_mul]
      simp [Ne.symm hy]
  · intro u _ hu
    rw [single_apply, ite_eq_right (fun h => hu h.1.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem single_mul_monomial {τ : Equiv.Perm ι} {N : Matrix ι ι K} (hN : IsLinePerm τ N)
    (a b : ι) (c : K) : single a b c * N = single a (τ⁻¹ b) (c * N b (τ⁻¹ b)) := by
  ext y z
  rw [mul_apply, Finset.sum_eq_single b, single_apply, single_apply]
  · by_cases hz : z = τ⁻¹ b
    · subst hz
      simp
    · have : N b z = 0 := hN.apply_eq_zero (fun h => hz (by rw [h]; simp))
      rw [this, mul_zero, ite_eq_right (fun h => hz h.2.symm)]
  · intro u _ hu
    rw [single_apply, ite_eq_right (fun h => hu h.2.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem monomial_mul_inv_apply {g : GL ι K} {σ : Equiv.Perm ι}
    (h : IsLinePerm σ (g : Matrix ι ι K)) (x : ι) :
    (g : Matrix ι ι K) (σ x) x * ((g⁻¹ : GL ι K) : Matrix ι ι K) x (σ x) = 1 := by
  have hmul : (((g⁻¹ : GL ι K) : Matrix ι ι K) * (g : Matrix ι ι K)) x x = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq]
  rw [mul_apply, Finset.sum_eq_single (σ x)] at hmul
  · rw [mul_comm]
    exact hmul
  · intro z _ hz
    rw [h.apply_eq_zero hz, mul_zero]
  · simp

theorem monomial_mulVec_single {σ : Equiv.Perm ι} {M : Matrix ι ι K} (hM : IsLinePerm σ M)
    (x : ι) : M *ᵥ Pi.single x 1 = M (σ x) x • Pi.single (σ x) 1 := by
  funext y
  rw [mulVec_single_one, col_apply]
  by_cases hy : y = σ x
  · subst hy
    simp
  · rw [hM.apply_eq_zero hy]
    simp [hy]

theorem isLinePerm_of_mulVec {σ : Equiv.Perm ι} {M : Matrix ι ι K}
    (hM : ∀ x, ∃ c : K, c ≠ 0 ∧ M *ᵥ Pi.single x 1 = c • Pi.single (σ x) 1) :
    IsLinePerm σ M := by
  intro x y
  obtain ⟨c, hc0, hc⟩ := hM x
  have := congrFun hc y
  rw [mulVec_single_one, col_apply] at this
  rw [this]
  by_cases hy : y = σ x
  · subst hy
    simp [hc0]
  · simp [hy]

theorem single_mulVec_single (a b x : ι) (c : K) :
    single a b c *ᵥ Pi.single x 1 = if x = b then c • Pi.single a 1 else 0 := by
  funext y
  rw [mulVec_single_one, col_apply, single_apply]
  by_cases hx : x = b
  · subst hx
    by_cases hy : a = y
    · subst hy
      simp
    · simp [hy, Ne.symm hy]
  · simp [hx, Ne.symm hx]

end Monomial

section Isometry

variable (h : UnitaryFieldData p f K)

theorem weylPerm_lineCoord (w : Equiv.Perm (Fin r ⊕ Fin r)) (x : Fin r ⊕ Fin r) :
    weylPerm (ε := ε) w (lineCoord x) = lineCoord (w x) := by
  rcases x with i | i
  · exact weylPerm_inl w i
  · exact weylPerm_inr_inr w i

theorem weylPerm_one : weylPerm (ε := ε) (1 : Equiv.Perm (Fin r ⊕ Fin r)) = 1 := by
  ext x
  rcases x with i | k | i <;> simp [lineCoord]

theorem bar_monomial_mul {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r)
    {M : Matrix (HypIndex r ε) (HypIndex r ε) K} (hM : IsLinePerm (weylPerm w) M)
    (hJ : (M.map h.bar)ᵀ * hypGram r ε K * M = hypGram r ε K) (x : HypIndex r ε) :
    h.bar (M (weylPerm w x) x) * M (weylPerm w (hypPartner x)) (hypPartner x) = 1 := by
  have key := congrFun (congrFun hJ x) (hypPartner x)
  rw [← gramForm_single h ((M.map h.bar)ᵀ * hypGram r ε K * M) x (hypPartner x),
    ← gramForm_mulVec, monomial_mulVec_single hM, monomial_mulVec_single hM] at key
  rw [mul_comm]
  simpa [gramForm_single, hypGram_apply, ← weylPerm_hypPartner hw] using key

theorem isLinePerm_weylMat {c : K} (hc0 : c ≠ 0) (w : Equiv.Perm (Fin r ⊕ Fin r)) :
    IsLinePerm (weylPerm (ε := ε) w) (weylMat h c w) := by
  refine isLinePerm_signedPerm _ fun x => ?_
  have hbc : h.bar c ≠ 0 := (map_ne_zero h.bar).mpr hc0
  rcases x with i | k | i
  · rcases hwi : w (.inl i) with j | j <;> simp [weylCoeff, hwi, hc0]
  · simp [weylCoeff]
  · rcases hwi : w (.inl i) with j | j <;> simp [weylCoeff, hwi, hbc]

variable {h}

theorem monomial_line_rels {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r)
    {g : GL (HypIndex r ε) K} (hg : IsLinePerm (weylPerm w) (g : Matrix (HypIndex r ε)
      (HypIndex r ε) K))
    (hJ : ((g : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K *
      (g : Matrix (HypIndex r ε) (HypIndex r ε) K) = hypGram r ε K) (x : Fin r ⊕ Fin r) :
    (g : Matrix (HypIndex r ε) (HypIndex r ε) K) (lineCoord (w x)) (lineCoord x) *
        ((g⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) (lineCoord x)
          (lineCoord (w x)) = 1 ∧
      h.bar ((g : Matrix (HypIndex r ε) (HypIndex r ε) K) (lineCoord (w x)) (lineCoord x)) =
        ((g⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
          (lineCoord x.swap) (lineCoord (w x).swap) ∧
      h.bar (((g⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
          (lineCoord x) (lineCoord (w x))) =
        (g : Matrix (HypIndex r ε) (HypIndex r ε) K) (lineCoord (w x).swap) (lineCoord x.swap) := by
  set M := (g : Matrix (HypIndex r ε) (HypIndex r ε) K)
  set N := ((g⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
  have hR1 : ∀ y : Fin r ⊕ Fin r, M (lineCoord (w y)) (lineCoord y) *
      N (lineCoord y) (lineCoord (w y)) = 1 := fun y => by
    have := monomial_mul_inv_apply hg (lineCoord y)
    rwa [weylPerm_lineCoord] at this
  have hR2 : ∀ y : Fin r ⊕ Fin r, h.bar (M (lineCoord (w y)) (lineCoord y)) *
      M (lineCoord (w y).swap) (lineCoord y.swap) = 1 := fun y => by
    have := bar_monomial_mul h hw hg hJ (lineCoord y)
    rwa [← lineCoord_swap, weylPerm_lineCoord, weylPerm_lineCoord, hw y] at this
  have hm0 : ∀ y : Fin r ⊕ Fin r, M (lineCoord (w y)) (lineCoord y) ≠ 0 := fun y h0 => by
    have := hR1 y
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hn0 : ∀ y : Fin r ⊕ Fin r, N (lineCoord y) (lineCoord (w y)) ≠ 0 := fun y h0 => by
    have := hR1 y
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have hbm : h.bar (M (lineCoord (w x)) (lineCoord x)) =
      N (lineCoord x.swap) (lineCoord (w x).swap) := by
    have h1 := hR1 x.swap
    rw [hw x] at h1
    refine mul_right_cancel₀ (hm0 x.swap) ?_
    rw [hw x, hR2 x, mul_comm, h1]
  refine ⟨hR1 x, hbm, ?_⟩
  have h1 := hR1 x.swap
  rw [hw x] at h1
  have h2 := congrArg h.bar (hR1 x)
  rw [map_mul, map_one, hbm] at h2
  have hn0' := hn0 x.swap
  rw [hw x] at hn0'
  refine mul_left_cancel₀ hn0' ?_
  rw [h2, mul_comm, h1]

theorem conj_uRootMat {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r)
    {g : GL (HypIndex r ε) K}
    (hg : IsLinePerm (weylPerm w) (g : Matrix (HypIndex r ε) (HypIndex r ε) K))
    (hJ : ((g : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K *
      (g : Matrix (HypIndex r ε) (HypIndex r ε) K) = hypGram r ε K) (a b : Fin r ⊕ Fin r)
    (t : K) :
    (g : Matrix (HypIndex r ε) (HypIndex r ε) K) * uRootMat ε h a b t *
        ((g⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      uRootMat ε h (w a) (w b) ((g : Matrix (HypIndex r ε) (HypIndex r ε) K)
        (lineCoord (w a)) (lineCoord a) *
        ((g⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) (lineCoord b)
          (lineCoord (w b)) * t) := by
  have hN := hg.inv
  have hMN : (g : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      ((g⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hconj : ∀ (x y : HypIndex r ε) (c : K),
      (g : Matrix (HypIndex r ε) (HypIndex r ε) K) * single x y c *
          ((g⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        single (weylPerm w x) (weylPerm w y) ((g : Matrix (HypIndex r ε) (HypIndex r ε) K)
          (weylPerm w x) x * c * ((g⁻¹ : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K) y (weylPerm w y)) := by
    intro x y c
    rw [monomial_mul_single hg, single_mul_monomial hN, inv_inv]
  rw [uRootMat, uRootMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hMN]
  congr 1
  unfold uRootNil
  by_cases hb : b = a.swap
  · have hb' : w b = (w a).swap := by rw [hb, hw a]
    rw [ite_eq_left hb, ite_eq_left hb', hconj]
    simp only [weylPerm_lineCoord]
    congr 1
    ring
  · have hb' : ¬w b = (w a).swap := fun e => hb (w.injective (by rw [e, hw a]))
    obtain ⟨-, hbm, -⟩ := monomial_line_rels hw hg hJ a
    obtain ⟨-, -, hbn⟩ := monomial_line_rels hw hg hJ b
    rw [ite_eq_right hb, ite_eq_right hb', Matrix.mul_sub, Matrix.sub_mul, hconj, hconj]
    simp only [weylPerm_lineCoord, hw a, hw b]
    congr 1
    · congr 1
      ring
    · congr 1
      rw [map_mul, map_mul, hbm, hbn]
      ring

end Isometry

section Conj

variable {h : UnitaryFieldData p f K}

theorem mem_traceZero_mul_iff {c : K} (hc : h.bar c = c) (hc0 : c ≠ 0) (s : K) :
    c * s ∈ h.traceZero ↔ s ∈ h.traceZero := by
  rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace,
    UnitaryFieldData.trace, map_mul, hc, ← mul_add]
  exact ⟨fun h0 => (mul_eq_zero.mp h0).resolve_left hc0, fun h0 => by rw [h0, mul_zero]⟩

theorem range_uRootHom_congr {a b a' b' : Fin r ⊕ Fin r} (ha : a = a') (hb : b = b')
    (hab : a ≠ b) (hab' : a' ≠ b') :
    (uRootHom (ε := ε) h hab).range = (uRootHom h hab').range := by
  subst ha
  subst hb
  rfl

theorem map_conj_range_uRootHom {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r)
    (g : hypSU h r ε)
    (hg : IsLinePerm (weylPerm w) ((g : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K)) {a b : Fin r ⊕ Fin r} (hab : a ≠ b) :
    (uRootHom (ε := ε) h hab).range.map (MulAut.conj g).toMonoidHom =
      (uRootHom h (w.injective.ne hab)).range := by
  have hJ := (mem_hypSU.mp g.2).1
  set lam := ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
      (lineCoord (w a)) (lineCoord a) *
    (((g : GL (HypIndex r ε) K)⁻¹ : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) (lineCoord b) (lineCoord (w b)) with hlam
  obtain ⟨ha1, hbm, -⟩ := monomial_line_rels hw hg hJ a
  obtain ⟨hb1, -, hbn⟩ := monomial_line_rels hw hg hJ b
  have hlam0 : lam ≠ 0 := by
    refine mul_ne_zero (fun h0 => ?_) (fun h0 => ?_)
    · rw [h0, zero_mul] at ha1
      exact zero_ne_one ha1
    · rw [h0, mul_zero] at hb1
      exact zero_ne_one hb1
  have hdom : ∀ s : K, s ∈ uRootDom h a b ↔ lam * s ∈ uRootDom h (w a) (w b) := by
    intro s
    by_cases hb : b = a.swap
    · have hlamF : h.bar lam = lam := by
        rw [hlam, map_mul, hbm, hbn, hb, hw a, Sum.swap_swap, Sum.swap_swap, mul_comm]
      rw [hb, hw a, uRootDom_swap, uRootDom_swap]
      exact (mem_traceZero_mul_iff hlamF hlam0 s).symm
    · have hb' : w b ≠ (w a).swap := fun e => hb (w.injective (by rw [e, hw a]))
      rw [uRootDom_of_ne h hb, uRootDom_of_ne h hb']
      exact ⟨fun _ => trivial, fun _ => trivial⟩
  have hconj : ∀ t : uRootDom h a b, g * uRootElt h hab t * g⁻¹ =
      uRootElt h (w.injective.ne hab) ⟨lam * t, (hdom t).mp t.2⟩ := fun t =>
    Subtype.ext (Units.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_uRootElt,
        coe_uRootElt, Subgroup.coe_inv]
      exact conj_uRootMat hw hg hJ a b t))
  ext x
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨Multiplicative.ofAdd ⟨lam * t.toAdd, (hdom t.toAdd).mp t.toAdd.2⟩,
      (hconj t.toAdd).symm⟩
  · rintro ⟨s, rfl⟩
    have hs : lam⁻¹ * s.toAdd ∈ uRootDom h a b := by
      rw [hdom, ← mul_assoc, mul_inv_cancel₀ hlam0, one_mul]
      exact s.toAdd.2
    refine ⟨uRootElt h hab ⟨lam⁻¹ * s.toAdd, hs⟩, ⟨Multiplicative.ofAdd ⟨_, hs⟩, rfl⟩, ?_⟩
    change g * uRootElt h hab ⟨lam⁻¹ * s.toAdd, hs⟩ * g⁻¹ = uRootHom h _ s
    rw [hconj]
    congr 1
    exact Subtype.ext (by simp only [← mul_assoc, mul_inv_cancel₀ hlam0, one_mul])

theorem map_conj_uRootSubgroup {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r)
    (g : hypSU h r ε)
    (hg : IsLinePerm (weylPerm w) ((g : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K)) (α : Fin r → ℤ) :
    (uRootSubgroup ε h α).map (MulAut.conj g).toMonoidHom = uRootSubgroup ε h (epsAct w α) := by
  rw [uRootSubgroup, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun q => ?_
    obtain ⟨⟨a, b⟩, hab, hroot⟩ := q
    rw [map_conj_range_uRootHom hw g hg hab]
    refine le_iSup_of_le ⟨(w a, w b), w.injective.ne hab, ?_⟩ le_rfl
    rw [← epsAct_rootVec hw, ← hroot]
  · refine iSup_le fun q => ?_
    obtain ⟨⟨c, d⟩, hcd, hroot⟩ := q
    have hab : w⁻¹ c ≠ w⁻¹ d := w⁻¹.injective.ne hcd
    have hroot' : rootVec (w⁻¹ c) (w⁻¹ d) = α := by
      have := epsAct_rootVec (inv_mem hw) c d
      rw [hroot, epsAct_inv_epsAct hw] at this
      exact this.symm
    have hc : w (w⁻¹ c) = c := by simp
    have hd : w (w⁻¹ d) = d := by simp
    rw [range_uRootHom_congr hc.symm hd.symm hcd (w.injective.ne hab),
      ← map_conj_range_uRootHom hw g hg hab]
    exact le_iSup_of_le
      (ι := {q : (Fin r ⊕ Fin r) × (Fin r ⊕ Fin r) // q.1 ≠ q.2 ∧ rootVec q.1 q.2 = α})
      ⟨(w⁻¹ c, w⁻¹ d), hab, hroot'⟩ le_rfl

end Conj

section Torus

variable {h : UnitaryFieldData p f K}

theorem isLinePerm_torus {t : hypSU h r ε} (ht : t ∈ hypTorus h r ε) :
    IsLinePerm (weylPerm (ε := ε) 1) ((t : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  obtain ⟨a, d, -, -, hg⟩ := ht
  rw [hg, weylPerm_one]
  intro x y
  rw [diagonal_apply, Equiv.Perm.one_apply]
  by_cases hyx : y = x
  · subst hyx
    rcases y with i | k | i <;> simp [torusEntries]
  · simp [hyx]

theorem mem_hypTorus_of_isLinePerm {t : hypSU h r ε}
    (ht : IsLinePerm 1 ((t : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) :
    t ∈ hypTorus h r ε := by
  set D := ((t : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) with hD
  have hd0 : ∀ x, D x x ≠ 0 := fun x => ht.apply_ne_zero x
  have hdiag : D = diagonal fun x => D x x := by
    ext x y
    by_cases hxy : x = y
    · subst hxy
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hxy]
      exact ht.apply_eq_zero hxy
  have ht' : IsLinePerm (weylPerm (ε := ε) (1 : Equiv.Perm (Fin r ⊕ Fin r))) D := by
    rw [weylPerm_one]
    exact ht
  have hrel := bar_monomial_mul h (one_mem _) ht' (mem_hypSU.mp t.2).1
  simp only [weylPerm_one, Equiv.Perm.one_apply] at hrel
  let a : Fin r → Kˣ := fun i => Units.mk0 (D (.inl i) (.inl i)) (hd0 _)
  let d : Fin ε → Kˣ := fun k => Units.mk0 (D (.inr (.inl k)) (.inr (.inl k))) (hd0 _)
  have hent : torusEntries h a d = fun x => D x x := by
    funext x
    rcases x with i | k | i
    · rfl
    · rfl
    · change (h.bar (D (.inl i) (.inl i)))⁻¹ = D (.inr (.inr i)) (.inr (.inr i))
      exact (eq_inv_of_mul_eq_one_right (hrel (.inl i))).symm
  refine ⟨a, d, fun k => ?_, ?_, ?_⟩
  · change D (.inr (.inl k)) (.inr (.inl k)) * h.bar (D (.inr (.inl k)) (.inr (.inl k))) = 1
    rw [mul_comm]
    exact hrel (.inr (.inl k))
  · rw [← det_diagonal_torusEntries, hent, ← hdiag]
    exact (mem_hypSU.mp t.2).2
  · rw [hent]
    exact hdiag

theorem exists_torus_of_isLinePerm {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
    {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r) {g : hypSU h r ε}
    (hg : IsLinePerm (weylPerm w) ((g : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K)) :
    ∃ t ∈ hypTorus h r ε, g = weylElt h hc hc0 hw * t := by
  refine ⟨(weylElt h hc hc0 hw)⁻¹ * g, mem_hypTorus_of_isLinePerm ?_, by
    rw [mul_inv_cancel_left]⟩
  have hdot : IsLinePerm (weylPerm (ε := ε) w)
      (((weylElt (ε := ε) h hc hc0 hw : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    rw [coe_weylElt]
    exact isLinePerm_weylMat h hc0 w
  have := hdot.inv.mul hg
  rw [inv_mul_cancel] at this
  rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
  exact this

end Torus

section Weyl

variable (h : UnitaryFieldData p f K)

theorem uRootMat_mulVec_single {a b : Fin r ⊕ Fin r} (hb : b ≠ a.swap) (t : K)
    (x : HypIndex r ε) :
    uRootMat ε h a b t *ᵥ Pi.single x 1 = Pi.single x 1 +
      (if x = lineCoord b then t • Pi.single (lineCoord a) 1 else 0) -
      (if x = lineCoord a.swap then h.bar t • Pi.single (lineCoord b.swap) 1 else 0) := by
  rw [uRootMat, uRootNil, ite_eq_right hb, add_mulVec, one_mulVec, sub_mulVec,
    single_mulVec_single, single_mulVec_single, add_sub_assoc]

theorem uRootMat_swap_mulVec_single (a : Fin r ⊕ Fin r) (t : K) (x : HypIndex r ε) :
    uRootMat ε h a a.swap t *ᵥ Pi.single x 1 = Pi.single x 1 +
      (if x = lineCoord a.swap then t • Pi.single (lineCoord a) 1 else 0) := by
  rw [uRootMat, uRootNil, ite_eq_left rfl, add_mulVec, one_mulVec, single_mulVec_single]

theorem isLinePerm_uWeylRepShort (k : Fin r) (hk : (k : ℕ) + 1 < r) :
    IsLinePerm (weylPerm (ε := ε) (simpleRefl r k))
      (((uWeylRepShort ε h k hk : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  set k' : Fin r := ⟨k + 1, hk⟩ with hk'
  have hkk' : k ≠ k' := fun e => by
    have := congrArg Fin.val e
    simp [k'] at this
  have hsnd : simpleSnd k = .inl k' := simpleSnd_of_lt hk
  have hrefl : simpleRefl r k = Equiv.sumCongr (Equiv.swap k k') (Equiv.swap k k') := by
    unfold simpleRefl
    rw [dite_eq_left hk]
  have hmat : (((uWeylRepShort ε h k hk : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = uRootMat ε h (.inl k) (.inl k') 1 *
        uRootMat ε h (.inl k') (.inl k) (-1) * uRootMat ε h (.inl k) (.inl k') 1 := by
    change uRootMat ε h (.inl k) (simpleSnd k) 1 * uRootMat ε h (simpleSnd k) (.inl k) (-1) *
      uRootMat ε h (.inl k) (simpleSnd k) 1 = _
    rw [hsnd]
  have hb1 : (Sum.inl k' : Fin r ⊕ Fin r) ≠ (Sum.inl k).swap := by simp
  have hb2 : (Sum.inl k : Fin r ⊕ Fin r) ≠ (Sum.inl k').swap := by simp
  set X := uRootMat ε h (.inl k) (.inl k') 1 with hXdef
  set Y := uRootMat ε h (.inl k') (.inl k) (-1) with hYdef
  have hX : ∀ x : HypIndex r ε, X *ᵥ Pi.single x 1 = Pi.single x 1 +
      (if x = .inl k' then (1 : K) • Pi.single (.inl k) 1 else 0) -
      (if x = .inr (.inr k) then h.bar 1 • Pi.single (.inr (.inr k')) 1 else 0) :=
    fun x => uRootMat_mulVec_single h hb1 1 x
  have hY : ∀ x : HypIndex r ε, Y *ᵥ Pi.single x 1 = Pi.single x 1 +
      (if x = .inl k then (-1 : K) • Pi.single (.inl k') 1 else 0) -
      (if x = .inr (.inr k') then h.bar (-1) • Pi.single (.inr (.inr k)) 1 else 0) :=
    fun x => uRootMat_mulVec_single h hb2 (-1) x
  set ek : HypIndex r ε → K := Pi.single (.inl k) 1 with hek
  set ek' : HypIndex r ε → K := Pi.single (.inl k') 1 with hek'
  set fk : HypIndex r ε → K := Pi.single (.inr (.inr k)) 1 with hfk
  set fk' : HypIndex r ε → K := Pi.single (.inr (.inr k')) 1 with hfk'
  have hne1 : (Sum.inl k : HypIndex r ε) ≠ .inl k' := fun e => hkk' (Sum.inl_injective e)
  have hne2 : (Sum.inr (Sum.inr k) : HypIndex r ε) ≠ .inr (.inr k') := fun e =>
    hkk' (Sum.inr_injective (Sum.inr_injective e))
  have n1 : ∀ i j : Fin r, (Sum.inl i : HypIndex r ε) ≠ .inr (.inr j) := fun _ _ => by simp
  have n2 : ∀ i j : Fin r, (Sum.inr (Sum.inr i) : HypIndex r ε) ≠ .inl j := fun _ _ => by simp
  have cXk : X *ᵥ ek = ek := by rw [hX, ite_eq_right hne1, ite_eq_right (n1 _ _), add_zero,
    sub_zero]
  have cXk' : X *ᵥ ek' = ek' + ek := by rw [hX, ite_eq_left rfl, ite_eq_right (n1 _ _),
    sub_zero, one_smul]
  have cXf : X *ᵥ fk = fk - fk' := by rw [hX, ite_eq_right (n2 _ _), ite_eq_left rfl, add_zero,
    map_one, one_smul]
  have cXf' : X *ᵥ fk' = fk' := by rw [hX, ite_eq_right (n2 _ _), ite_eq_right hne2.symm,
    add_zero, sub_zero]
  have cYk : Y *ᵥ ek = ek - ek' := by rw [hY, ite_eq_left rfl, ite_eq_right (n1 _ _), sub_zero,
    neg_one_smul, ← sub_eq_add_neg]
  have cYk' : Y *ᵥ ek' = ek' := by rw [hY, ite_eq_right hne1.symm, ite_eq_right (n1 _ _),
    add_zero, sub_zero]
  have cYf : Y *ᵥ fk = fk := by rw [hY, ite_eq_right (n2 _ _), ite_eq_right hne2, add_zero,
    sub_zero]
  have cYf' : Y *ᵥ fk' = fk' + fk := by rw [hY, ite_eq_right (n2 _ _), ite_eq_left rfl,
    add_zero, map_neg, map_one, neg_one_smul, sub_neg_eq_add]
  have cXo : ∀ x : HypIndex r ε, x ≠ .inl k' → x ≠ .inr (.inr k) →
      X *ᵥ Pi.single x 1 = Pi.single x 1 := fun x h1 h2 => by
    rw [hX, ite_eq_right h1, ite_eq_right h2, add_zero, sub_zero]
  have cYo : ∀ x : HypIndex r ε, x ≠ .inl k → x ≠ .inr (.inr k') →
      Y *ᵥ Pi.single x 1 = Pi.single x 1 := fun x h1 h2 => by
    rw [hY, ite_eq_right h1, ite_eq_right h2, add_zero, sub_zero]
  refine isLinePerm_of_mulVec fun x => ?_
  rw [hmat, ← mulVec_mulVec, ← mulVec_mulVec]
  rcases x with i | l | i
  · by_cases hik : i = k
    · subst hik
      have hσ : weylPerm (ε := ε) (simpleRefl r i) (.inl i) = .inl k' := by
        rw [weylPerm_inl, hrefl, Equiv.sumCongr_apply, Sum.map_inl, Equiv.swap_apply_left]
        rfl
      refine ⟨-1, by norm_num, ?_⟩
      rw [hσ, cXk, cYk, mulVec_sub, cXk, cXk', neg_one_smul]
      abel
    · by_cases hik' : i = k'
      · subst hik'
        have hσ : weylPerm (ε := ε) (simpleRefl r k) (.inl k') = .inl k := by
          rw [weylPerm_inl, hrefl, Equiv.sumCongr_apply, Sum.map_inl, Equiv.swap_apply_right]
          rfl
        refine ⟨1, one_ne_zero, ?_⟩
        rw [hσ, cXk', mulVec_add, cYk', cYk, show ek' + (ek - ek') = ek by abel, cXk, one_smul]
      · have h1 : (Sum.inl i : HypIndex r ε) ≠ .inl k := fun e => hik (Sum.inl_injective e)
        have h2 : (Sum.inl i : HypIndex r ε) ≠ .inl k' := fun e => hik' (Sum.inl_injective e)
        have hσ : weylPerm (ε := ε) (simpleRefl r k) (.inl i) = .inl i := by
          rw [weylPerm_inl, hrefl, Equiv.sumCongr_apply, Sum.map_inl,
            Equiv.swap_apply_of_ne_of_ne hik hik']
          rfl
        refine ⟨1, one_ne_zero, ?_⟩
        rw [hσ, cXo _ h2 (n1 _ _), cYo _ h1 (n1 _ _), cXo _ h2 (n1 _ _), one_smul]
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [weylPerm_inr_inl, cXo _ (by simp) (by simp), cYo _ (by simp) (by simp),
      cXo _ (by simp) (by simp), one_smul]
  · by_cases hik : i = k
    · subst hik
      have hσ : weylPerm (ε := ε) (simpleRefl r i) (.inr (.inr i)) = .inr (.inr k') := by
        rw [weylPerm_inr_inr, hrefl, Equiv.sumCongr_apply, Sum.map_inr, Equiv.swap_apply_left]
        rfl
      refine ⟨-1, by norm_num, ?_⟩
      rw [hσ, cXf, mulVec_sub, cYf, cYf', show fk - (fk' + fk) = -fk' by abel, mulVec_neg, cXf',
        neg_one_smul]
    · by_cases hik' : i = k'
      · subst hik'
        have hσ : weylPerm (ε := ε) (simpleRefl r k) (.inr (.inr k')) = .inr (.inr k) := by
          rw [weylPerm_inr_inr, hrefl, Equiv.sumCongr_apply, Sum.map_inr, Equiv.swap_apply_right]
          rfl
        refine ⟨1, one_ne_zero, ?_⟩
        rw [hσ, cXf', cYf', mulVec_add, cXf', cXf, show fk' + (fk - fk') = fk by abel, one_smul]
      · have h1 : (Sum.inr (Sum.inr i) : HypIndex r ε) ≠ .inr (.inr k) := fun e =>
          hik (Sum.inr_injective (Sum.inr_injective e))
        have h2 : (Sum.inr (Sum.inr i) : HypIndex r ε) ≠ .inr (.inr k') := fun e =>
          hik' (Sum.inr_injective (Sum.inr_injective e))
        have hσ : weylPerm (ε := ε) (simpleRefl r k) (.inr (.inr i)) = .inr (.inr i) := by
          rw [weylPerm_inr_inr, hrefl, Equiv.sumCongr_apply, Sum.map_inr,
            Equiv.swap_apply_of_ne_of_ne hik hik']
          rfl
        refine ⟨1, one_ne_zero, ?_⟩
        rw [hσ, cXo _ (n2 _ _) h1, cYo _ (n2 _ _) h2, cXo _ (n2 _ _) h1, one_smul]

theorem uWeylRepLong_eq_weylElt {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) (k : Fin r)
    (hk : ¬(k : ℕ) + 1 < r) :
    uWeylRepLong ε h k c hc = weylElt h hc hc0 (simpleRefl_mem k) := by
  have hrefl : simpleRefl r k = Equiv.swap (Sum.inl k) (Sum.inr k) := by
    unfold simpleRefl
    rw [dite_eq_right hk]
  have hbar : h.bar c = -c := by
    have := mem_traceZero_add hc
    linear_combination this
  refine Subtype.ext (Units.ext ?_)
  change uRootMat ε h (.inl k) (Sum.inl k).swap (-c⁻¹) * uRootMat ε h (.inr k) (Sum.inr k).swap c *
    uRootMat ε h (.inl k) (Sum.inl k).swap (-c⁻¹) = weylMat h c (simpleRefl r k)
  set X := uRootMat ε h (.inl k) (Sum.inl k).swap (-c⁻¹) with hXdef
  set Y := uRootMat ε h (.inr k) (Sum.inr k).swap c with hYdef
  have hX : ∀ x : HypIndex r ε, X *ᵥ Pi.single x 1 =
      Pi.single x 1 + (if x = .inr (.inr k) then (-c⁻¹) • Pi.single (.inl k) 1 else 0) :=
    fun x => uRootMat_swap_mulVec_single h (.inl k) (-c⁻¹) x
  have hY : ∀ x : HypIndex r ε, Y *ᵥ Pi.single x 1 =
      Pi.single x 1 + (if x = .inl k then c • Pi.single (.inr (.inr k)) 1 else 0) :=
    fun x => uRootMat_swap_mulVec_single h (.inr k) c x
  set ek : HypIndex r ε → K := Pi.single (.inl k) 1 with hek
  set fk : HypIndex r ε → K := Pi.single (.inr (.inr k)) 1 with hfk
  have hne : (Sum.inl k : HypIndex r ε) ≠ .inr (.inr k) := by simp
  have cXk : X *ᵥ ek = ek := by rw [hX, ite_eq_right hne, add_zero]
  have cXf : X *ᵥ fk = fk + (-c⁻¹) • ek := by rw [hX, ite_eq_left rfl]
  have cYk : Y *ᵥ ek = ek + c • fk := by rw [hY, ite_eq_left rfl]
  have cYf : Y *ᵥ fk = fk := by rw [hY, ite_eq_right hne.symm, add_zero]
  have cXo : ∀ x : HypIndex r ε, x ≠ .inr (.inr k) → X *ᵥ Pi.single x 1 = Pi.single x 1 :=
    fun x h1 => by rw [hX, ite_eq_right h1, add_zero]
  have cYo : ∀ x : HypIndex r ε, x ≠ .inl k → Y *ᵥ Pi.single x 1 = Pi.single x 1 :=
    fun x h1 => by rw [hY, ite_eq_right h1, add_zero]
  refine ext_of_mulVec_single fun x => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, weylMat_mulVec_single, hrefl]
  rcases x with i | l | i
  · by_cases hik : i = k
    · subst hik
      have hσ : weylPerm (ε := ε) (Equiv.swap (Sum.inl i) (Sum.inr i)) (.inl i) =
          .inr (.inr i) := by
        rw [weylPerm_inl, Equiv.swap_apply_left]
        rfl
      have hκ : weylCoeff (ε := ε) h c (Equiv.swap (Sum.inl i) (Sum.inr i)) (.inl i) = c := by
        simp [weylCoeff]
      rw [hσ, hκ, cXk, cYk, mulVec_add, mulVec_smul, cXk, cXf, smul_add, smul_smul, mul_neg,
        mul_inv_cancel₀ hc0, neg_one_smul]
      abel
    · have h1 : (Sum.inl i : HypIndex r ε) ≠ .inl k := fun e => hik (Sum.inl_injective e)
      have hw : Equiv.swap (Sum.inl k) (Sum.inr k) (Sum.inl i : Fin r ⊕ Fin r) = .inl i :=
        Equiv.swap_apply_of_ne_of_ne (by simpa using hik) (by simp)
      have hσ : weylPerm (ε := ε) (Equiv.swap (Sum.inl k) (Sum.inr k)) (.inl i) = .inl i := by
        rw [weylPerm_inl, hw]
        rfl
      have hκ : weylCoeff (ε := ε) h c (Equiv.swap (Sum.inl k) (Sum.inr k)) (.inl i) = 1 := by
        simp [weylCoeff, hw]
      rw [hσ, hκ, cXo _ (by simp), cYo _ h1, cXo _ (by simp), one_smul]
  · rw [weylPerm_inr_inl, show weylCoeff (ε := ε) h c (Equiv.swap (Sum.inl k) (Sum.inr k))
      (.inr (.inl l)) = 1 from rfl, cXo _ (by simp), cYo _ (by simp), cXo _ (by simp), one_smul]
  · by_cases hik : i = k
    · subst hik
      have hσ : weylPerm (ε := ε) (Equiv.swap (Sum.inl i) (Sum.inr i)) (.inr (.inr i)) =
          .inl i := by
        rw [weylPerm_inr_inr, Equiv.swap_apply_right]
        rfl
      have hκ : weylCoeff (ε := ε) h c (Equiv.swap (Sum.inl i) (Sum.inr i)) (.inr (.inr i)) =
          -c⁻¹ := by
        simp [weylCoeff, hbar]
      rw [hσ, hκ, cXf, mulVec_add, mulVec_smul, cYf, cYk, smul_add, smul_smul, neg_mul,
        inv_mul_cancel₀ hc0, neg_one_smul, show fk + ((-c⁻¹) • ek + -fk) = (-c⁻¹) • ek by abel,
        mulVec_smul, cXk]
    · have h1 : (Sum.inr (Sum.inr i) : HypIndex r ε) ≠ .inr (.inr k) := fun e =>
        hik (Sum.inr_injective (Sum.inr_injective e))
      have hw : Equiv.swap (Sum.inl k) (Sum.inr k) (Sum.inr i : Fin r ⊕ Fin r) = .inr i :=
        Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hik)
      have hw' : Equiv.swap (Sum.inl k) (Sum.inr k) (Sum.inl i : Fin r ⊕ Fin r) = .inl i :=
        Equiv.swap_apply_of_ne_of_ne (by simpa using hik) (by simp)
      have hσ : weylPerm (ε := ε) (Equiv.swap (Sum.inl k) (Sum.inr k)) (.inr (.inr i)) =
          .inr (.inr i) := by
        rw [weylPerm_inr_inr, hw]
        rfl
      have hκ : weylCoeff (ε := ε) h c (Equiv.swap (Sum.inl k) (Sum.inr k)) (.inr (.inr i)) =
          1 := by
        simp [weylCoeff, hw']
      rw [hσ, hκ, cXo _ h1, cYo _ (by simp), cXo _ h1, one_smul]

end Weyl

theorem fullPos_lineCoord_lt_iff {x y : Fin r ⊕ Fin r} :
    fullPos (lineCoord (ε := ε) x) < fullPos (lineCoord (ε := ε) y) ↔
      (flagOrder r x : ℕ) < flagOrder r y := by
  rcases x with ⟨i, hi⟩ | ⟨i, hi⟩ <;> rcases y with ⟨j, hj⟩ | ⟨j, hj⟩ <;>
    simp only [lineCoord, fullPos_inl, fullPos_inr_inr, flagOrder_inl, flagOrder_inr] <;> omega

theorem uRootMat_blockTriangular (h : UnitaryFieldData p f K) {a b : Fin r ⊕ Fin r}
    (hab : (flagOrder r a : ℕ) < flagOrder r b) (t : K) :
    (uRootMat ε h a b t).BlockTriangular fullPos := by
  intro x y hxy
  have hne : x ≠ y := fun e => by rw [e] at hxy; exact lt_irrefl _ hxy
  have h1 : ¬(lineCoord (ε := ε) a = x ∧ lineCoord b = y) := by
    rintro ⟨rfl, rfl⟩
    exact lt_asymm (fullPos_lineCoord_lt_iff.mpr hab) hxy
  have h2 : ¬(lineCoord (ε := ε) b.swap = x ∧ lineCoord a.swap = y) := by
    rintro ⟨rfl, rfl⟩
    have := fullPos_lineCoord_lt_iff.mp hxy
    have e1 := flagOrder_swap a
    have e2 := flagOrder_swap b
    omega
  rw [uRootMat, Matrix.add_apply, one_apply_ne hne, zero_add]
  unfold uRootNil
  split_ifs
  · rw [single_apply, ite_eq_right h1]
  · rw [Matrix.sub_apply, single_apply, single_apply, ite_eq_right h1, ite_eq_right h2,
      sub_zero]

theorem uRootSubgroup_le_hypBorel (h : UnitaryFieldData p f K) {α : Fin r → ℤ}
    (hα : α ∈ posRoots r) : uRootSubgroup ε h α ≤ hypBorel h r ε := by
  refine iSup_le fun q => ?_
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := q
  rintro _ ⟨t, rfl⟩
  refine mem_hypBorel_of_blockTriangular h ?_
  change (uRootMat ε h a b t.toAdd).BlockTriangular fullPos
  exact uRootMat_blockTriangular h ((rootVec_mem_posRoots_iff hab).mp hα) _

theorem unitary_hyperbolic_root_transport (h : UnitaryFieldData p f K) {c : K}
    (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) :
    (∀ (w : Equiv.Perm (Fin r ⊕ Fin r)) (hw : w ∈ hypWeyl r) (α : Fin r → ℤ),
      (uRootSubgroup ε h α).map (MulAut.conj (weylElt (ε := ε) h hc hc0 hw)).toMonoidHom =
        uRootSubgroup ε h (epsAct w α)) ∧
    (∀ t ∈ hypTorus h r ε, ∀ α : Fin r → ℤ,
      (uRootSubgroup ε h α).map (MulAut.conj t).toMonoidHom = uRootSubgroup ε h α) ∧
    (∀ (w : Equiv.Perm (Fin r ⊕ Fin r)) (hw : w ∈ hypWeyl r) (g : hypSU h r ε),
      IsLinePerm (weylPerm w) ((g : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) →
      ∃ t ∈ hypTorus h r ε, g = weylElt h hc hc0 hw * t) ∧
    (∀ (k : Fin r) (hk : (k : ℕ) + 1 < r), IsLinePerm (weylPerm (simpleRefl r k))
      (((uWeylRepShort ε h k hk : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K)) ∧
    (∀ k : Fin r, ¬(k : ℕ) + 1 < r →
      uWeylRepLong ε h k c hc = weylElt h hc hc0 (simpleRefl_mem k) ∧
      IsLinePerm (weylPerm (simpleRefl r k))
        (((uWeylRepLong ε h k c hc : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K)) ∧
    ∀ α ∈ posRoots r, uRootSubgroup ε h α ≤ hypBorel h r ε := by
  refine ⟨fun w hw α => map_conj_uRootSubgroup hw _ (by
      rw [coe_weylElt]
      exact isLinePerm_weylMat h hc0 w) α,
    fun t ht α => (map_conj_uRootSubgroup (one_mem _) t (isLinePerm_torus ht) α).trans
      (by rw [epsAct_one]),
    fun w hw g hg => exists_torus_of_isLinePerm hc hc0 hw hg,
    fun k hk => isLinePerm_uWeylRepShort h k hk,
    fun k hk => ⟨uWeylRepLong_eq_weylElt h hc hc0 k hk, ?_⟩,
    fun α hα => uRootSubgroup_le_hypBorel h hα⟩
  rw [uWeylRepLong_eq_weylElt h hc hc0 k hk, coe_weylElt]
  exact isLinePerm_weylMat h hc0 _

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
