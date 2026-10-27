module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Core

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

section Prelim

variable {K : Type} [Field K] {n : ℕ}

theorem isSimpleGroup_projectiveSL (hn : 3 ≤ n) : IsSimpleGroup (projectiveSL n K) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := K) (n := n) (by omega)
    (Or.inl hn)).2.1
  exact (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
    n K).symm.isSimpleGroup

theorem exists_noncomm_projectiveSL (hn : 3 ≤ n) :
    ∃ a b : projectiveSL n K, a * b ≠ b * a := by
  let x := SpecialLinearGroup.transvection
    (show (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ by simp) (1 : K)
  let y := SpecialLinearGroup.transvection
    (show (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ by simp) (1 : K)
  refine ⟨proj n K x, proj n K y, fun h => ?_⟩
  have h1 : proj n K ⁅x, y⁆ = 1 := by
    simp only [commutatorElement_def, map_mul, map_inv]
    rw [h]
    group
  rw [SpecialLinearGroup.commutatorElement_transvection
    (show (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ by simp)
    (show (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ by simp)
    (show (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ by simp), proj_eq_one_iff,
    scalars_eq_center, Matrix.SpecialLinearGroup.mem_center_iff] at h1
  obtain ⟨r, -, hr⟩ := h1
  have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M ⟨0, by omega⟩ ⟨2, by omega⟩) hr
  simp [CFSG.LinearGroups.coe_transvection, Matrix.scalar_apply] at h2

end Prelim

section Root

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def rootElt (B : GL (Fin n) K) {i j : Fin n} (hij : i ≠ j) (t : K) :
    projectiveSL n K :=
  conjAut n K B (proj n K (SpecialLinearGroup.transvection hij t))

theorem rootElt_def (B : GL (Fin n) K) {i j : Fin n} (hij : i ≠ j) (t : K) :
    rootElt B hij t = conjAut n K B (proj n K (SpecialLinearGroup.transvection hij t)) :=
  rfl

theorem rootElt_injective (B : GL (Fin n) K) {i j : Fin n} (hij : i ≠ j) :
    Function.Injective (rootElt B hij) := by
  intro s t h
  have h1 : proj n K (SpecialLinearGroup.transvection hij s) =
      proj n K (SpecialLinearGroup.transvection hij t) := (conjAut n K B).injective h
  have h2 := proj_eq_proj_iff.mp h1
  rw [scalars_eq_center] at h2
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h2
  have hB : ((SpecialLinearGroup.transvection hij t : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      ((SpecialLinearGroup.transvection hij s : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *
      (((SpecialLinearGroup.transvection hij s)⁻¹ * SpecialLinearGroup.transvection hij t :
        SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  rw [← hr] at hB
  have e1 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i i) hB
  have e2 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j) hB
  simp [CFSG.LinearGroups.coe_transvection, Matrix.mul_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, Matrix.single_apply, hij, hij.symm, Matrix.add_apply, Matrix.one_apply] at e1 e2
  have hr1 : r = 1 := e1.symm
  rw [hr1, mul_one] at e2
  exact e2.symm

@[expose] noncomputable def diagGLK (d : Fin n → K) (hd : ∀ k, d k ≠ 0) : GL (Fin n) K :=
  GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d)
    (by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun k _ => hd k)

theorem coe_diagGLK (d : Fin n → K) (hd : ∀ k, d k ≠ 0) :
    ((diagGLK d hd : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d := rfl

theorem conjAut_diagGLK_proj_transvection {i j : Fin n} (hij : i ≠ j) (d : Fin n → K)
    (hd : ∀ k, d k ≠ 0) (t : K) :
    conjAut n K (diagGLK d hd) (proj n K (SpecialLinearGroup.transvection hij t)) =
      proj n K (SpecialLinearGroup.transvection hij (d i / d j * t)) := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
    Units.mul_inv_eq_iff_eq_mul]
  show _ = _ * ((diagGLK d hd : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [coe_diagGLK, CFSG.LinearGroups.coe_transvection, CFSG.LinearGroups.coe_transvection]
  ext a b
  have hdj := hd j
  by_cases hc : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := hc
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.single_apply, Matrix.add_apply,
      Matrix.one_apply, hij]
    field_simp
  · by_cases hab : a = b
    · subst hab
      simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.single_apply, Matrix.add_apply,
        Matrix.one_apply, hc]
    · simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.single_apply, Matrix.add_apply,
        Matrix.one_apply, hab, hc]

theorem conjAut_rootElt {B x : GL (Fin n) K} {d : Fin n → K} (hd : ∀ k, d k ≠ 0)
    (hxd : (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d) {i j : Fin n} (hij : i ≠ j) (t : K) :
    conjAut n K x (rootElt B hij t) = rootElt B hij (d i / d j * t) := by
  have hGL : x * B = B * diagGLK d hd := Units.ext (by
    rw [Units.val_mul, Units.val_mul, coe_diagGLK]; exact hxd)
  unfold rootElt
  rw [← MulAut.mul_apply, ← map_mul, hGL, map_mul, MulAut.mul_apply,
    conjAut_diagGLK_proj_transvection hij d hd t]

theorem diag_ne_zero_of_mul_eq {B x : GL (Fin n) K} {d : Fin n → K}
    (hxd : (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d) : ∀ k, d k ≠ 0 := by
  have h1 := congrArg Matrix.det hxd
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at h1
  have hB := GeneralLinearGroup.det_ne_zero B
  have hx := GeneralLinearGroup.det_ne_zero x
  have h2 : (x : Matrix (Fin n) (Fin n) K).det = ∏ k, d k := by
    apply mul_right_cancel₀ hB
    rw [h1, mul_comm]
  intro k hk
  apply hx
  rw [h2]
  exact Finset.prod_eq_zero (Finset.mem_univ k) hk

end Root

section Gen

variable {K : Type} [Field K] [Finite K] {n : ℕ}

omit [Finite K] in
theorem eq_top_of_rootElt_mem (B : GL (Fin n) K) (T : Subgroup (projectiveSL n K))
    (h : ∀ (i j : Fin n) (hij : i ≠ j) (t : K), rootElt B hij t ∈ T) : T = ⊤ := by
  let S : Subgroup (SpecialLinearGroup (Fin n) K) :=
    T.comap ((conjAut n K B).toMonoidHom.comp (proj n K))
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (K := K) (n := n),
      Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, rfl⟩
    exact h i j hij c
  rw [eq_top_iff]
  intro y _
  obtain ⟨g, hg⟩ := proj_surjective n K ((conjAut n K B).symm y)
  have hgS : g ∈ S := hS ▸ Subgroup.mem_top g
  have e : conjAut n K B (proj n K g) = y := by rw [hg]; simp
  rw [← e]
  exact hgS

omit [Finite K] in
theorem pow_apply_rootElt {v : MulAut (projectiveSL n K)} {B : GL (Fin n) K} {i j : Fin n}
    (hij : i ≠ j) {l : K} (hl : ∀ s, v (rootElt B hij s) = rootElt B hij (l * s)) (k : ℕ) (t : K) :
    (v ^ k) (rootElt B hij t) = rootElt B hij (l ^ k * t) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih => rw [pow_succ, MulAut.mul_apply, hl, ih]; congr 1; ring

theorem exists_ne_one_fix_rootElt {r : ℕ} (hr : 1 < r)
    {V : Subgroup (MulAut (projectiveSL n K))} (hVc : Nat.card V = r ^ 2)
    (hVe : ∀ v ∈ V, v ^ r = 1) (B : GL (Fin n) K)
    (hV : ∀ v ∈ V, ∃ (x : GL (Fin n) K) (d : Fin n → K), v = conjAut n K x ∧
      (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d) {i j : Fin n} (hij : i ≠ j) :
    ∃ w ∈ V, w ≠ 1 ∧ (∀ t : K, w (rootElt B hij t) = rootElt B hij t) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hdata : ∀ v ∈ V, ∃ l : K, ∀ s, v (rootElt B hij s) = rootElt B hij (l * s) := by
    intro v hv
    obtain ⟨x, d, rfl, hxd⟩ := hV v hv
    have hd := diag_ne_zero_of_mul_eq hxd
    exact ⟨d i / d j, fun s => conjAut_rootElt hd hxd hij s⟩
  have hroot : ∀ v ∈ V, ∀ l : K, (∀ s, v (rootElt B hij s) = rootElt B hij (l * s)) → l ^ r = 1 := by
    intro v hv l hl
    have h1 := pow_apply_rootElt hij hl r 1
    rw [hVe v hv, MulAut.one_apply, mul_one] at h1
    exact (rootElt_injective B hij h1).symm
  let y₁ : projectiveSL n K := rootElt B hij 1
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (projectiveSL n K),
      S = (Polynomial.nthRootsFinset r (1 : K)).image (fun μ => rootElt B hij μ) := ⟨_, rfl⟩
  have hS : S.card ≤ r := by
    rw [hSdef]
    refine Finset.card_image_le.trans ?_
    unfold Polynomial.nthRootsFinset
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots r 1)
  have hmaps : Set.MapsTo (fun v : V => (v : MulAut (projectiveSL n K)) y₁)
      ((Finset.univ : Finset V) : Set V) (S : Set (projectiveSL n K)) := by
    intro v _
    obtain ⟨l, hl⟩ := hdata v v.2
    have hlr := hroot v v.2 l hl
    rw [Finset.mem_coe, hSdef, Finset.mem_image]
    refine ⟨l, ?_, ?_⟩
    · rw [Polynomial.mem_nthRootsFinset (by omega)]
      exact hlr
    · show rootElt B hij l = (v : MulAut (projectiveSL n K)) (rootElt B hij 1)
      rw [hl 1, mul_one]
  have hcard : S.card < (Finset.univ : Finset V).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hVc]
    calc S.card ≤ r := hS
      _ < r ^ 2 := by nlinarith
  obtain ⟨v₁, -, v₂, -, hne, hfeq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  let w : MulAut (projectiveSL n K) := (v₁ : MulAut (projectiveSL n K))⁻¹ * (v₂ : MulAut (projectiveSL n K))
  have hwV : w ∈ V := V.mul_mem (V.inv_mem v₁.2) v₂.2
  have hw1 : w ≠ 1 := by
    intro h
    apply hne
    have : (v₁ : MulAut (projectiveSL n K)) = v₂ := by
      have h' := congrArg (fun a => (v₁ : MulAut (projectiveSL n K)) * a) h
      simpa [w] using h'.symm
    exact Subtype.ext this
  have hwy : w y₁ = y₁ := by
    calc w y₁ = (v₁ : MulAut (projectiveSL n K))⁻¹ ((v₂ : MulAut (projectiveSL n K)) y₁) := rfl
      _ = (v₁ : MulAut (projectiveSL n K))⁻¹ ((v₁ : MulAut (projectiveSL n K)) y₁) := by
        rw [show (v₂ : MulAut (projectiveSL n K)) y₁ = (v₁ : MulAut (projectiveSL n K)) y₁ from hfeq.symm]
      _ = y₁ := by simp
  obtain ⟨l, hl⟩ := hdata w hwV
  have hl1 : l = 1 := by
    have h1 : rootElt B hij (l * 1) = rootElt B hij 1 := by rw [← hl 1]; exact hwy
    have := rootElt_injective B hij h1
    simpa using this
  exact ⟨w, hwV, hw1, fun t => by rw [hl t, hl1, one_mul]⟩

theorem generation_of_toral {r : ℕ} (hr : 1 < r)
    {V : Subgroup (MulAut (projectiveSL n K))} (hVc : Nat.card V = r ^ 2)
    (hVe : ∀ v ∈ V, v ^ r = 1) (B : GL (Fin n) K)
    (hV : ∀ v ∈ V, ∃ (x : GL (Fin n) K) (d : Fin n → K), v = conjAut n K x ∧
      (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d) :
    (⨆ v ∈ V, ⨆ (_ : v ≠ 1), fixSub v) = ⊤ := by
  apply eq_top_of_rootElt_mem B
  intro i j hij t
  obtain ⟨w, hwV, hw1, hwt⟩ := exists_ne_one_fix_rootElt hr hVc hVe B hV hij
  have hle : fixSub w ≤ ⨆ v ∈ V, ⨆ (_ : v ≠ 1), fixSub v :=
    le_iSup₂_of_le w hwV (le_iSup (fun _ : w ≠ 1 => fixSub w) hw1)
  exact hle (mem_fixSub.2 (hwt t))

end Gen

section Main

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem false_of_toral (hn : 3 ≤ n) {r : ℕ} {V Z : Subgroup (MulAut (projectiveSL n K))}
    (h2 : N2Cfg (projectiveSL n K) r V Z) (h3 : N3Full (projectiveSL n K) V Z) (B : GL (Fin n) K)
    (hV : ∀ v ∈ V, ∃ (x : GL (Fin n) K) (d : Fin n → K), v = conjAut n K x ∧
      (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d) : False := by
  have h2' := h2
  obtain ⟨hr, -, hVe, hVc, -⟩ := h2'
  have : IsElementaryAbelian r ↥V := hVe
  have hVe' : ∀ v ∈ V, v ^ r = 1 := fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv
  exact false_of_generation (isSimpleGroup_projectiveSL hn) (exists_noncomm_projectiveSL hn) h2 h3
    (generation_of_toral hr.one_lt hVc hVe' B hV)

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln
