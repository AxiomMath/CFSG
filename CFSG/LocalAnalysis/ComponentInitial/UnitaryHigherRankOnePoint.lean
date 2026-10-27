module

public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.ClassicalGroups.UnitaryFlag.Triangular
public import CFSG.LinearAlgebra.LinearGroups.UnitaryHeisenberg

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def hypIndexFin3 : HypIndex 1 1 ≃ Fin 3 where
  toFun
    | .inl _ => 0
    | .inr (.inl _) => 1
    | .inr (.inr _) => 2
  invFun i := if i = 0 then .inl 0 else if i = 1 then .inr (.inl 0) else .inr (.inr 0)
  left_inv x := by
    rcases x with i | i | i <;> obtain rfl := Fin.fin_one_eq_zero i <;> rfl
  right_inv i := by
    fin_cases i <;> rfl

theorem hypForm_eq_heisenbergForm (h : UnitaryFieldData p f K) (x y : HypIndex 1 1 → K) :
    hypForm h 1 1 x y =
      heisenbergForm h (x ∘ hypIndexFin3.symm) (y ∘ hypIndexFin3.symm) := by
  have e0 : hypIndexFin3.symm 0 = .inl 0 := rfl
  have e1 : hypIndexFin3.symm 1 = .inr (.inl 0) := rfl
  have e2 : hypIndexFin3.symm 2 = .inr (.inr 0) := rfl
  rw [hypForm_apply, heisenbergForm_apply]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton, hypPartner_inl,
    hypPartner_inr_inl, hypPartner_inr_inr, Function.comp_apply, e0, e1, e2, Fin.default_eq_zero]
  ring

@[expose] noncomputable def rkOneQ (h : UnitaryFieldData p f K) (a b : K) :
    Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
  (heisenbergMatrix h a b).submatrix hypIndexFin3 hypIndexFin3

theorem rkOneQ_gram (h : UnitaryFieldData p f K) {a b : K} (hab : h.norm a + h.trace b = 0) :
    ((rkOneQ h a b).map h.bar)ᵀ * hypGram 1 1 K * rkOneQ h a b = hypGram 1 1 K := by
  rw [← gramForm_isometry_iff]
  intro x y
  change hypForm h 1 1 _ _ = hypForm h 1 1 _ _
  rw [hypForm_eq_heisenbergForm, hypForm_eq_heisenbergForm, rkOneQ,
    submatrix_mulVec_equiv, submatrix_mulVec_equiv, Function.comp_assoc, Function.comp_assoc,
    Equiv.self_comp_symm, Function.comp_id, Function.comp_id]
  exact ((unitary_heisenberg_identities h).1 a b hab).2 _ _

theorem det_rkOneQ (h : UnitaryFieldData p f K) {a b : K} (hab : h.norm a + h.trace b = 0) :
    (rkOneQ h a b).det = 1 := by
  rw [rkOneQ, det_submatrix_equiv_self]
  exact ((unitary_heisenberg_identities h).1 a b hab).1

@[expose] noncomputable def rkOneQElt (h : UnitaryFieldData p f K) (a b : K)
    (hab : h.norm a + h.trace b = 0) : hypSU h 1 1 :=
  mkHypSU h (rkOneQ h a b) (rkOneQ_gram h hab) (det_rkOneQ h hab)

@[expose] noncomputable def rkOneU (h : UnitaryFieldData p f K) (a b : K)
    (hab : h.norm a + h.trace b = 0) : Equiv.Perm (hypIsotropicLines h 1 1) :=
  hypProjLineAction h 1 1 (hypProj h 1 1 (rkOneQElt h a b hab))

theorem norm_zero_add_trace {h : UnitaryFieldData p f K} {t : K} (ht : t ∈ h.traceZero) :
    h.norm 0 + h.trace t = 0 := by
  rw [UnitaryFieldData.norm, zero_mul, zero_add]
  exact (UnitaryFieldData.mem_traceZero h).mp ht

theorem rkOneQ_mul_zero (h : UnitaryFieldData p f K) (s t : K) :
    rkOneQ h 0 s * rkOneQ h 0 t = rkOneQ h 0 (s + t) := by
  rw [rkOneQ, rkOneQ, rkOneQ, submatrix_mul_equiv, heisenbergMatrix_mul]
  simp

@[expose] noncomputable def rkOneCHomSU (h : UnitaryFieldData p f K) :
    Multiplicative h.traceZero →* hypSU h 1 1 where
  toFun t := rkOneQElt h 0 t.toAdd (norm_zero_add_trace t.toAdd.2)
  map_one' := Subtype.ext (Units.ext (by
    change rkOneQ h 0 0 = 1
    rw [rkOneQ, heisenbergMatrix_zero_zero]
    exact submatrix_one_equiv _))
  map_mul' s t := Subtype.ext (Units.ext (by
    change rkOneQ h 0 (s.toAdd + t.toAdd : h.traceZero) = rkOneQ h 0 s.toAdd * rkOneQ h 0 t.toAdd
    rw [rkOneQ_mul_zero, AddSubgroup.coe_add]))

@[expose] noncomputable def rkOneDiag (h : UnitaryFieldData p f K) (s : K) : HypIndex 1 1 → K
  | .inl _ => s
  | .inr (.inl _) => h.bar s / s
  | .inr (.inr _) => (h.bar s)⁻¹

@[expose] noncomputable def rkOneD (h : UnitaryFieldData p f K) (s : K) :
    Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
  diagonal (rkOneDiag h s)

theorem diagonal_gram (h : UnitaryFieldData p f K) {r ε : ℕ} (d : HypIndex r ε → K)
    (hd : ∀ x, h.bar (d x) * d (hypPartner x) = 1) :
    ((diagonal d).map h.bar)ᵀ * hypGram r ε K * diagonal d = hypGram r ε K := by
  ext x y
  rw [mul_diagonal, diagonal_map (map_zero h.bar), diagonal_transpose, diagonal_mul,
    hypGram_apply]
  split_ifs with hxy
  · rw [hxy, mul_one, hd x]
  · rw [mul_zero, zero_mul]

theorem rkOneD_gram (h : UnitaryFieldData p f K) {s : K} (hs : s ≠ 0) :
    ((rkOneD h s).map h.bar)ᵀ * hypGram 1 1 K * rkOneD h s = hypGram 1 1 K := by
  have hbs : h.bar s ≠ 0 := (map_ne_zero h.bar).mpr hs
  refine diagonal_gram h _ fun x => ?_
  rcases x with i | k | i
  · change h.bar s * (h.bar s)⁻¹ = 1
    exact mul_inv_cancel₀ hbs
  · change h.bar (h.bar s / s) * (h.bar s / s) = 1
    rw [map_div₀, h.bar_bar]
    field_simp
  · change h.bar (h.bar s)⁻¹ * s = 1
    rw [map_inv₀, h.bar_bar, inv_mul_cancel₀ hs]

theorem det_rkOneD (h : UnitaryFieldData p f K) {s : K} (hs : s ≠ 0) : (rkOneD h s).det = 1 := by
  have hbs : h.bar s ≠ 0 := (map_ne_zero h.bar).mpr hs
  rw [rkOneD, det_diagonal, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Finset.univ_unique, Finset.prod_singleton, rkOneDiag]
  field_simp

theorem rkOneD_mul (h : UnitaryFieldData p f K) {s t : K} (hs : s ≠ 0) (ht : t ≠ 0) :
    rkOneD h s * rkOneD h t = rkOneD h (s * t) := by
  rw [rkOneD, rkOneD, rkOneD, diagonal_mul_diagonal]
  congr 1
  funext x
  rcases x with i | k | i <;> simp only [rkOneDiag, map_mul]
  · field_simp
  · rw [mul_inv]

@[expose] noncomputable def rkOneDHomSU (h : UnitaryFieldData p f K) : Kˣ →* hypSU h 1 1 where
  toFun s := mkHypSU h (rkOneD h s) (rkOneD_gram h s.ne_zero) (det_rkOneD h s.ne_zero)
  map_one' := Subtype.ext (Units.ext (by
    change rkOneD h 1 = 1
    rw [rkOneD, ← diagonal_one]
    congr 1
    funext x
    rcases x with i | k | i <;> simp [rkOneDiag]))
  map_mul' s t := Subtype.ext (Units.ext (by
    change rkOneD h (s * t : Kˣ) = rkOneD h s * rkOneD h t
    rw [rkOneD_mul h s.ne_zero t.ne_zero, Units.val_mul]))

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def infPt : Submodule K (HypIndex 1 1 → K) :=
  K ∙ (Pi.single (.inl 0) 1 : HypIndex 1 1 → K)

@[expose] noncomputable def zeroPt : Submodule K (HypIndex 1 1 → K) :=
  K ∙ (Pi.single (.inr (.inr 0)) 1 : HypIndex 1 1 → K)

@[expose] noncomputable def rkOneG : Subgroup (Equiv.Perm (hypIsotropicLines h 1 1)) :=
  (hypProjLineAction h 1 1).range

@[expose] noncomputable def rkOneUStar : Subgroup (Equiv.Perm (hypIsotropicLines h 1 1)) :=
  ((hypUnitriangular h 1 1).map (hypProj h 1 1)).map (hypProjLineAction h 1 1)

@[expose] noncomputable def rkOneC : Subgroup (Equiv.Perm (hypIsotropicLines h 1 1)) :=
  ((hypProjLineAction h 1 1).comp ((hypProj h 1 1).comp (rkOneCHomSU h))).range

@[expose] noncomputable def rkOneTElt (s : Kˣ) : Equiv.Perm (hypIsotropicLines h 1 1) :=
  hypProjLineAction h 1 1 (hypProj h 1 1 (rkOneDHomSU h s))

@[expose] noncomputable def rkOneT : Subgroup (Equiv.Perm (hypIsotropicLines h 1 1)) :=
  ((hypProjLineAction h 1 1).comp ((hypProj h 1 1).comp (rkOneDHomSU h))).range

@[expose] noncomputable def rkOneChi : Kˣ →* Kˣ where
  toFun s := Units.map (h.bar : K →* K) s ^ 2 * s⁻¹
  map_one' := by simp
  map_mul' s t := by
    rw [map_mul, mul_pow, mul_inv]
    ac_rfl

@[expose] noncomputable def rkOneM : Subgroup Kˣ :=
  (rkOneChi h).range

variable (p f) in
@[expose] def rkOneDelta : ℕ :=
  Nat.gcd 3 (p ^ f + 1)

variable {h}

theorem span_single_mem_hypIsotropicLines {a : HypIndex 1 1} (ha : hypPartner a ≠ a) :
    K ∙ (Pi.single a 1 : HypIndex 1 1 → K) ∈ hypIsotropicLines h 1 1 := by
  refine mem_hypIsotropicLines.mpr ⟨finrank_span_singleton (by simp), fun x hx => ?_⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  change gramForm h (hypGram 1 1 K) (c • Pi.single a 1) (c • Pi.single a 1) = 0
  simp [gramForm_single, hypGram_apply, Ne.symm ha]

theorem unitary_rank_one_point_data :
    infPt ∈ hypIsotropicLines h 1 1 ∧ zeroPt ∈ hypIsotropicLines h 1 1 ∧
    (infPt : Submodule K (HypIndex 1 1 → K)) ≠ zeroPt ∧
    (∀ a b : K, h.norm a + h.trace b = 0 →
      ((rkOneQ h a b).map h.bar)ᵀ * hypGram 1 1 K * rkOneQ h a b = hypGram 1 1 K ∧
        (rkOneQ h a b).det = 1) ∧
    (∀ a b : K, rkOneQ h a b =
      (!![1, -h.bar a, b; 0, 1, a; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K).submatrix hypIndexFin3
        hypIndexFin3) ∧
    (∀ s : K, s ≠ 0 →
      ((rkOneD h s).map h.bar)ᵀ * hypGram 1 1 K * rkOneD h s = hypGram 1 1 K ∧
        (rkOneD h s).det = 1) ∧
    (∀ s : K, rkOneD h s = diagonal (rkOneDiag h s) ∧ rkOneDiag h s (.inl 0) = s ∧
      rkOneDiag h s (.inr (.inl 0)) = h.bar s / s ∧ rkOneDiag h s (.inr (.inr 0)) = (h.bar s)⁻¹) ∧
    rkOneC h ≤ rkOneG h ∧ rkOneT h ≤ rkOneG h ∧ rkOneUStar h ≤ rkOneG h ∧
    (∀ x, x ∈ rkOneC h ↔
      ∃ (t : K) (ht : t ∈ h.traceZero), rkOneU h 0 t (norm_zero_add_trace ht) = x) ∧
    (∀ x, x ∈ rkOneT h ↔ ∃ s : Kˣ, rkOneTElt h s = x) ∧
    (∀ s : Kˣ, (rkOneChi h s : K) = h.bar s ^ 2 / s) ∧
    rkOneDelta p f = Nat.gcd 3 (p ^ f + 1) := by
  have hne : (Pi.single (.inl 0) 1 : HypIndex 1 1 → K) ∉ zeroPt := fun hmem => by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have := congrFun hc (.inl 0)
    simp at this
  refine ⟨span_single_mem_hypIsotropicLines (by simp), span_single_mem_hypIsotropicLines
    (by simp), fun heq => hne (heq ▸ Submodule.mem_span_singleton_self _),
    fun a b hab => ⟨rkOneQ_gram h hab, det_rkOneQ h hab⟩, fun a b => rfl,
    fun s hs => ⟨rkOneD_gram h hs, det_rkOneD h hs⟩, fun s => ⟨rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_,
    fun x => ?_, fun x => ⟨fun ⟨s, hs⟩ => ⟨s, hs⟩, fun ⟨s, hs⟩ => ⟨s, hs⟩⟩, fun s => ?_, rfl⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨hypProj h 1 1 (rkOneCHomSU h t), rfl⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨hypProj h 1 1 (rkOneDHomSU h t), rfl⟩
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  · constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t.toAdd, t.toAdd.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨Multiplicative.ofAdd ⟨t, ht⟩, rfl⟩
  · change ((Units.map (h.bar : K →* K) s ^ 2 * s⁻¹ : Kˣ) : K) = _
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_inv_eq_inv_val,
      div_eq_mul_inv]
    rfl

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
