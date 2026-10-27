module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.ConjugacyBasics

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section MatrixFacts

variable {F : Type} [Field F]

theorem cayley_hamilton_two (A : Matrix (Fin 2) (Fin 2) F) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

variable [Fintype F] {E : Type} [Field E] [Algebra F E] (basis : Module.Basis (Fin 2) F E)

omit [Fintype F] in
theorem eq_algebraMap_of_mulVec (s : E) {v : Fin 2 → F} (hv : v ≠ 0) {lam : F}
    (h : (mulMatrix F E basis s) *ᵥ v = lam • v) : s = algebraMap F E lam := by
  set e := basis.equivFun.symm v with he
  have hrepr : (basis.repr e : Fin 2 → F) = v := by
    rw [he, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have he0 : e ≠ 0 := by
    intro h0
    apply hv
    rw [← hrepr, h0, map_zero]
    rfl
  have h1 := Algebra.leftMulMatrix_mulVec_repr basis s e
  rw [hrepr] at h1
  change (mulMatrix F E basis s) *ᵥ v = _ at h1
  rw [h] at h1
  have h2 : basis.repr (s * e) = basis.repr (lam • e) := by
    ext i
    have := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ← this, hrepr]
  have h3 := basis.repr.injective h2
  rw [Algebra.smul_def] at h3
  exact mul_right_cancel₀ he0 h3

omit [Fintype F] in
theorem coordinateGLAction_mulGL_ne (s : Eˣ) (hs : (s : E) ∉ Set.range (algebraMap F E))
    (p : Omega F) : coordinateGLAction F (mulGL F E basis s) p ≠ p := by
  intro hp
  apply hs
  cases p with
  | none =>
    rw [coordinateGLAction_none_eq_none_iff, mulGL_val] at hp
    refine ⟨(mulMatrix F E basis s) 0 0, (eq_algebraMap_of_mulVec basis s
      (v := ![1, 0]) (by simp) ?_).symm⟩
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hp]
  | some y =>
    rw [coordinateGLAction_some_eq_some_iff, mulGL_val] at hp
    refine ⟨(mulMatrix F E basis s) 1 0 * y + (mulMatrix F E basis s) 1 1,
      (eq_algebraMap_of_mulVec basis s (v := ![y, 1]) (by simp) ?_).symm⟩
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination -hp
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem algebraMap_trace_mulMatrix (e : E) :
    algebraMap F E (mulMatrix F E basis e).trace = e + e ^ Nat.card F := by
  by_cases he : e = 0
  · subst he
    simp [mulMatrix]
  · have hCH := cayley_hamilton_two (mulMatrix F E basis e)
    have h1 : Algebra.leftMulMatrix basis (e * e) = Algebra.leftMulMatrix basis
        (algebraMap F E (mulMatrix F E basis e).trace * e -
          algebraMap F E (mulMatrix F E basis e).det) := by
      rw [map_mul, map_sub, map_mul, AlgHom.commutes, AlgHom.commutes]
      rw [show Algebra.leftMulMatrix basis e * Algebra.leftMulMatrix basis e = _ from hCH]
      rw [← Algebra.smul_def, Algebra.algebraMap_eq_smul_one]
    have h2 := Algebra.leftMulMatrix_injective basis h1
    have hdet := algebraMap_det_mulMatrix F E basis e
    rw [hdet] at h2
    have h3 : e * (e + e ^ Nat.card F - algebraMap F E (mulMatrix F E basis e).trace) = 0 := by
      linear_combination h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h he
    · linear_combination -h

end MatrixFacts

section Centralizer

variable {F : Type} [Field F] [Fintype F] {E : Type} [Field E] [Algebra F E]
  (basis : Module.Basis (Fin 2) F E)

omit [Fintype F] in
include basis in
theorem exists_eq_add_mul_of_not_mem {s : E} (hs : s ∉ Set.range (algebraMap F E)) (x : E) :
    ∃ c d : F, x = algebraMap F E c + algebraMap F E d * s := by
  have hli : LinearIndependent F ![(1 : E), s] := by
    rw [LinearIndependent.pair_iff]
    intro c d h
    by_cases hd : d = 0
    · subst hd
      rw [zero_smul, add_zero, smul_eq_zero] at h
      exact ⟨h.resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply hs
      refine ⟨-c / d, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
      have hd' : algebraMap F E d ≠ 0 := by simpa using hd
      rw [map_div₀, map_neg]
      field_simp
      linear_combination -h
  let b' := basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Fintype.card_fin, finrank_eq_two F E basis])
  refine ⟨b'.repr x 0, b'.repr x 1, ?_⟩
  have h := b'.sum_repr x
  rw [Fin.sum_univ_two, coe_basisOfLinearIndependentOfCardEqFinrank] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one] at h
  exact h.symm

omit [Fintype F] in
theorem eq_mulMatrix_of_commute {s : E} (hs : s ∉ Set.range (algebraMap F E))
    {P : Matrix (Fin 2) (Fin 2) F} (hP : P * mulMatrix F E basis s = mulMatrix F E basis s * P) :
    ∃ e : E, P = mulMatrix F E basis e := by
  set L := (LinearMap.toMatrix basis basis).symm P with hLdef
  have hPL : P = LinearMap.toMatrix basis basis L := by rw [hLdef, LinearEquiv.apply_symm_apply]
  have hL : ∀ x, L (s * x) = s * L x := by
    rw [hPL, mulMatrix, Algebra.leftMulMatrix_apply, ← LinearMap.toMatrix_mul,
      ← LinearMap.toMatrix_mul] at hP
    have h' := (LinearMap.toMatrix basis basis).injective hP
    intro x
    have := LinearMap.congr_fun h' x
    simpa [Module.End.mul_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] using this
  refine ⟨L 1, ?_⟩
  rw [hPL, mulMatrix, Algebra.leftMulMatrix_apply]
  congr 1
  ext x
  obtain ⟨c, d, rfl⟩ := exists_eq_add_mul_of_not_mem basis hs x
  have hx : algebraMap F E c + algebraMap F E d * s = c • (1 : E) + d • s := by
    simp [Algebra.smul_def]
  have hs1 : L s = s * L 1 := by rw [← hL 1, mul_one]
  rw [hx, map_add, map_smul, map_smul, hs1]
  simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', Algebra.smul_def, mul_one]
  ring

omit [Fintype F] in
theorem eq_mulGL_of_commute {s : Eˣ} (hs : (s : E) ∉ Set.range (algebraMap F E))
    {P : GL (Fin 2) F} (hP : P * mulGL F E basis s = mulGL F E basis s * P) :
    ∃ e : Eˣ, P = mulGL F E basis e := by
  have hP' := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) hP
  simp only [Units.val_mul, mulGL_val] at hP'
  obtain ⟨e, he⟩ := eq_mulMatrix_of_commute basis hs hP'
  have he0 : e ≠ 0 := by
    rintro rfl
    have hdet := P.det_ne_zero
    rw [he, mulMatrix, map_zero, Matrix.det_zero] at hdet
    exact hdet rfl
  refine ⟨Units.mk0 e he0, Units.ext ?_⟩
  rw [mulGL_val, Units.val_mk0]
  exact he

theorem conj_mulGL_cases {s s' : Eˣ} (hs : (s : E) ∉ Set.range (algebraMap F E))
    {P : GL (Fin 2) F}
    (h : ProjGenLinGroup.mk (P * mulGL F E basis s * P⁻¹) =
      ProjGenLinGroup.mk (mulGL F E basis s')) :
    (∃ e : Eˣ, P = mulGL F E basis e) ∨ (∃ e : Eˣ, P = frobGL F E basis * mulGL F E basis e) := by
  rw [ProjGenLinGroup.mk_eq_mk_iff] at h
  obtain ⟨c, hc⟩ := h
  set s'' := s' * (unitE F E c)⁻¹ with hs''
  have hconj : P * mulGL F E basis s * P⁻¹ = mulGL F E basis s'' := by
    rw [hs'', map_mul, map_inv, mulGL_unitE, ← hc, mul_inv_cancel_right]
  have htr : (mulMatrix F E basis (s'' : E)).trace = (mulMatrix F E basis (s : E)).trace := by
    have h1 := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F).trace) hconj
    simp only [Units.val_mul, mulGL_val] at h1
    rw [← h1, Matrix.trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
  have hdt : (mulMatrix F E basis (s'' : E)).det = (mulMatrix F E basis (s : E)).det := by
    have h1 := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F).det) hconj
    simp only [Units.val_mul, mulGL_val, Matrix.det_mul] at h1
    rw [← h1, mul_comm (P : Matrix (Fin 2) (Fin 2) F).det, mul_assoc, ← Matrix.det_mul,
      Units.mul_inv, Matrix.det_one, mul_one]
  have htrE := congrArg (algebraMap F E) htr
  rw [algebraMap_trace_mulMatrix, algebraMap_trace_mulMatrix] at htrE
  have hdtE := congrArg (algebraMap F E) hdt
  rw [algebraMap_det_mulMatrix, algebraMap_det_mulMatrix] at hdtE
  have hroot : ((s'' : E) - s) * ((s'' : E) - (s : E) ^ Nat.card F) = 0 := by
    linear_combination (s'' : E) * htrE - hdtE
  rcases mul_eq_zero.mp hroot with h1 | h1
  ·
    left
    have hss : s'' = s := Units.ext (sub_eq_zero.mp h1)
    rw [hss] at hconj
    exact eq_mulGL_of_commute basis hs (mul_inv_eq_iff_eq_mul.mp hconj)
  ·
    right
    have hss : s'' = s ^ Nat.card F := Units.ext (by
      rw [Units.val_pow_eq_pow_val]
      exact sub_eq_zero.mp h1)
    rw [hss] at hconj
    have hfrob : (frobGL F E basis)⁻¹ * P * mulGL F E basis s =
        mulGL F E basis s * ((frobGL F E basis)⁻¹ * P) := by
      have hf := frobGL_mul_mulGL F E basis s
      calc (frobGL F E basis)⁻¹ * P * mulGL F E basis s
          = (frobGL F E basis)⁻¹ * (P * mulGL F E basis s * P⁻¹) * P := by group
        _ = (frobGL F E basis)⁻¹ * (frobGL F E basis * mulGL F E basis s *
              (frobGL F E basis)⁻¹) * P := by
            rw [hconj, hf, mul_inv_cancel_right]
        _ = mulGL F E basis s * ((frobGL F E basis)⁻¹ * P) := by group
    obtain ⟨e, he⟩ := eq_mulGL_of_commute basis hs hfrob
    exact ⟨e, by rw [← he, mul_inv_cancel_left]⟩

end Centralizer

section NonsplitClasses

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {E : Type} [Field E] [Algebra F E] {basis : Module.Basis (Fin 2) F E}

omit [Fintype F] in
theorem not_mem_range_of_mulGL (hb : ¬ IsSquare b) {t : CentralExtension F b m hm heven}
    {s : Eˣ} (hs : ProjGenLinGroup.mk (mulGL F E basis s) = projectiveMap F b m hm heven t)
    (htA : t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    (s : E) ∉ Set.range (algebraMap F E) := by
  rintro ⟨c, hc⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact s.ne_zero hc.symm
  apply htA
  rw [← projectiveMap_eq_one_iff hb, ← hs]
  have hsu : s = unitE F E (Units.mk0 c hc0) := Units.ext (by rw [unitE_val, Units.val_mk0, hc])
  rw [hsu, mulGL_unitE, ProjGenLinGroup.mk_scalar]

omit [Fintype F] in
theorem nonsplitTorus_smul_ne (hb : ¬ IsSquare b) {t : CentralExtension F b m hm heven}
    (ht : t ∈ nonsplitTorus F b m hm heven E basis)
    (htA : t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) (p : Omega F) :
    t • p ≠ p := by
  obtain ⟨s, hs⟩ := (mem_nonsplitTorus_iff t).mp ht
  rw [smul_eq_coordinateGLAction hs.symm]
  exact coordinateGLAction_mulGL_ne basis s (not_mem_range_of_mulGL hb hs htA) p

omit [Fintype F] in
theorem card_fixed_nonsplitTorus (hb : ¬ IsSquare b) {t : CentralExtension F b m hm heven}
    (ht : t ∈ nonsplitTorus F b m hm heven E basis)
    (htA : t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    Nat.card {p : Omega F // t • p = p} = 0 := by
  rw [Nat.card_eq_zero]
  left
  exact ⟨fun p => nonsplitTorus_smul_ne hb ht htA p.1 p.2⟩

variable (y : Eˣ) (hy : (y : E) * (y : E) ^ Nat.card F = -1) (h2 : (2 : F) ≠ 0)

theorem projectiveMap_nonsplitWeyl :
    projectiveMap F b m hm heven (nonsplitWeyl F b m hm heven E basis h2 y hy) =
      ProjGenLinGroup.mk (mulGL F E basis y * frobGL F E basis) := by
  rw [nonsplitWeyl, projectiveMap_specialInclusion, toGL_wMatrix]

theorem frobGL_inv_conj_mulGL (t : Eˣ) :
    (frobGL F E basis)⁻¹ * mulGL F E basis t * frobGL F E basis =
      mulGL F E basis (t ^ Nat.card F) := by
  rw [frobGL_inv, frobGL_mul_mulGL, mul_assoc, frobGL_mul_self, mul_one]

theorem nonsplitTorus_conj_cases (hb : ¬ IsSquare b) {t : CentralExtension F b m hm heven}
    (ht : t ∈ nonsplitTorus F b m hm heven E basis)
    (htA : t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2))
    {g : CentralExtension F b m hm heven}
    (hg : g * t * g⁻¹ ∈ nonsplitTorus F b m hm heven E basis) :
    g ∈ nonsplitTorus F b m hm heven E basis ∨
      (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g ∈
        nonsplitTorus F b m hm heven E basis := by
  obtain ⟨s, hs⟩ := (mem_nonsplitTorus_iff t).mp ht
  obtain ⟨s', hs'⟩ := (mem_nonsplitTorus_iff _).mp hg
  obtain ⟨P, hP⟩ := ProjGenLinGroup.mk_surjective (projectiveMap F b m hm heven g)
  have hsF := not_mem_range_of_mulGL hb hs htA
  have hconj : ProjGenLinGroup.mk (P * mulGL F E basis s * P⁻¹) =
      ProjGenLinGroup.mk (mulGL F E basis s') := by
    rw [hs']
    simp only [map_mul, map_inv]
    rw [hP, hs]
  rcases conj_mulGL_cases basis hsF hconj with ⟨e, he⟩ | ⟨e, he⟩
  · left
    rw [mem_nonsplitTorus_iff]
    exact ⟨e, by rw [← hP, he]⟩
  · right
    rw [mem_nonsplitTorus_iff]
    refine ⟨y⁻¹ ^ Nat.card F * e, ?_⟩
    have hκ : projectiveMap F b m hm heven ((nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g) =
        ProjGenLinGroup.mk ((mulGL F E basis y * frobGL F E basis)⁻¹ *
          (frobGL F E basis * mulGL F E basis e)) := by
      rw [map_mul, map_inv, projectiveMap_nonsplitWeyl y hy h2, ← hP, he]
      simp only [map_mul, map_inv]
    rw [hκ]
    congr 1
    rw [map_mul, ← frobGL_inv_conj_mulGL, map_inv]
    group

end NonsplitClasses

section NonsplitFusion

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {E : Type} [Field E] [Algebra F E] {basis : Module.Basis (Fin 2) F E}
  (y : Eˣ) (hy : (y : E) * (y : E) ^ Nat.card F = -1) (h2 : (2 : F) ≠ 0)

theorem not_mem_range_of_norm_eq (hb : ¬ IsSquare b) {z : Eˣ}
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) :
    (z : E) ∉ Set.range (algebraMap F E) := by
  rintro ⟨c, hc⟩
  rw [← hc, pow_card_algebraMap, ← map_mul] at hz
  have hbc := (algebraMap F E).injective hz
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hbc
    exact b.ne_zero hbc.symm
  exact hb ⟨Units.mk0 c hc0, Units.ext (by rw [Units.val_mul, Units.val_mk0, hbc])⟩

theorem nonsplitGenerator_not_mem (hb : ¬ IsSquare b) {z : Eˣ}
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) :
    nonsplitGenerator F b m hm heven E basis z hz ∉
      Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
  intro h
  have h1 := zpowers_cyclicGenerator_sq_smul F b m hm heven h none
  rw [smul_eq_coordinateGLAction (projectiveMap_nonsplitGenerator z hz)] at h1
  exact coordinateGLAction_mulGL_ne basis z (not_mem_range_of_norm_eq hb hz) none h1

include y hy h2 in
theorem centralizer_nonsplitTorus (hb : ¬ IsSquare b) {t : CentralExtension F b m hm heven}
    (ht : t ∈ nonsplitTorus F b m hm heven E basis)
    (htA : t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    Subgroup.centralizer {t} = nonsplitTorus F b m hm heven E basis := by
  obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have hconj : g * t * g⁻¹ = t := by rw [hg, mul_inv_cancel_right]
    rcases nonsplitTorus_conj_cases y hy h2 hb ht htA (hconj ▸ ht) with h | h
    · exact h
    · exfalso
      apply htA
      rw [← nonsplitTorus_fixed_iff z hz y hy h2 hb ht]
      have hτ : t * ((nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g) =
          ((nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g) * t :=
        nonsplitTorus_mul_comm z hz ht h
      have hτt : ((nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g) * t *
          ((nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g)⁻¹ = t := by
        rw [← hτ, mul_inv_cancel_right]
      calc nonsplitWeyl F b m hm heven E basis h2 y hy * t *
            (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹
          = nonsplitWeyl F b m hm heven E basis h2 y hy *
              (((nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g) * t *
                ((nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g)⁻¹) *
              (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ := by rw [hτt]
        _ = g * t * g⁻¹ := by group
        _ = t := hconj
  · intro hg
    exact nonsplitTorus_mul_comm z hz hg ht

theorem isConj_nonsplitTorus_iff (hb : ¬ IsSquare b) {t t' : CentralExtension F b m hm heven}
    (ht : t ∈ nonsplitTorus F b m hm heven E basis)
    (htA : t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2))
    (ht' : t' ∈ nonsplitTorus F b m hm heven E basis) :
    IsConj t t' ↔ t' = t ∨ t' = nonsplitWeyl F b m hm heven E basis h2 y hy * t *
      (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ := by
  obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := isConj_iff.mp h
    rcases nonsplitTorus_conj_cases y hy h2 hb ht htA ht' with hg | hg
    · left
      rw [nonsplitTorus_mul_comm z hz hg ht, mul_inv_cancel_right]
    · right
      have hτ : t * ((nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g) =
          ((nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g) * t :=
        nonsplitTorus_mul_comm z hz ht hg
      calc g * t * g⁻¹ = nonsplitWeyl F b m hm heven E basis h2 y hy *
            (((nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g) * t) *
            ((nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g)⁻¹ *
            (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ := by group
        _ = _ := by rw [← hτ]; group
  · rintro (rfl | rfl)
    · exact IsConj.refl _
    · exact isConj_iff.mpr ⟨_, rfl⟩

theorem nonsplitWeyl_conj_ne (hb : ¬ IsSquare b) {t : CentralExtension F b m hm heven}
    (ht : t ∈ nonsplitTorus F b m hm heven E basis)
    (htA : t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    nonsplitWeyl F b m hm heven E basis h2 y hy * t *
      (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ ≠ t := by
  obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
  exact fun h => htA ((nonsplitTorus_fixed_iff z hz y hy h2 hb ht).mp h)

theorem mem_normalizer_nonsplitTorus_iff (hb : ¬ IsSquare b)
    (g : CentralExtension F b m hm heven) :
    g ∈ Subgroup.normalizer
        (nonsplitTorus F b m hm heven E basis : Set (CentralExtension F b m hm heven)) ↔
      g ∈ nonsplitTorus F b m hm heven E basis ∨
        (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g ∈
          nonsplitTorus F b m hm heven E basis := by
  obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hg
    exact nonsplitTorus_conj_cases y hy h2 hb (nonsplitGenerator_mem z hz)
      (nonsplitGenerator_not_mem hb hz) ((hg _).mp (nonsplitGenerator_mem z hz))
  · rintro (hg | hg) h
    · constructor
      · intro hh
        exact (nonsplitTorus F b m hm heven E basis).mul_mem
          ((nonsplitTorus F b m hm heven E basis).mul_mem hg hh)
          ((nonsplitTorus F b m hm heven E basis).inv_mem hg)
      · intro hh
        have := (nonsplitTorus F b m hm heven E basis).mul_mem
          ((nonsplitTorus F b m hm heven E basis).mul_mem
            ((nonsplitTorus F b m hm heven E basis).inv_mem hg) hh) hg
        simpa [mul_assoc] using this
    · set τ := (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g with hτ
      have hgw : g = nonsplitWeyl F b m hm heven E basis h2 y hy * τ := by
        rw [hτ, mul_inv_cancel_left]
      constructor
      · intro hh
        have h1 : τ * h * τ⁻¹ ∈ nonsplitTorus F b m hm heven E basis :=
          (nonsplitTorus F b m hm heven E basis).mul_mem
            ((nonsplitTorus F b m hm heven E basis).mul_mem hg hh)
            ((nonsplitTorus F b m hm heven E basis).inv_mem hg)
        have h3 := nonsplitWeyl_conj_mem z hz y hy h2 h1
        rw [hgw]
        simpa [mul_assoc] using h3
      · intro hh
        rw [hgw] at hh
        have h1 := nonsplitWeyl_inv_conj_mem z hz y hy h2 hh
        have h3 : τ * h * τ⁻¹ ∈ nonsplitTorus F b m hm heven E basis := by
          have : (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ *
              (nonsplitWeyl F b m hm heven E basis h2 y hy * τ * h *
                (nonsplitWeyl F b m hm heven E basis h2 y hy * τ)⁻¹) *
                nonsplitWeyl F b m hm heven E basis h2 y hy = τ * h * τ⁻¹ := by group
          rwa [this] at h1
        have h4 := (nonsplitTorus F b m hm heven E basis).mul_mem
          ((nonsplitTorus F b m hm heven E basis).mul_mem
            ((nonsplitTorus F b m hm heven E basis).inv_mem hg) h3) hg
        simpa [mul_assoc] using h4

end NonsplitFusion

end CFSG.Wreathed.CentralSL2
