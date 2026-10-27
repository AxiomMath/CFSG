module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.ConjugacyBasics

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section Diagonal

variable (F : Type) [Field F]

@[expose] noncomputable def diagGL : Fˣ × Fˣ →* GL (Fin 2) F where
  toFun p := ⟨diagonal ![(p.1 : F), (p.2 : F)], diagonal ![((p.1⁻¹ : Fˣ) : F), ((p.2⁻¹ : Fˣ) : F)],
    by rw [diagonal_mul_diagonal]; ext i j; fin_cases i <;> fin_cases j <;> simp,
    by rw [diagonal_mul_diagonal]; ext i j; fin_cases i <;> fin_cases j <;> simp⟩
  map_one' := Units.ext (by ext i j; fin_cases i <;> fin_cases j <;> simp)
  map_mul' p q := Units.ext (by
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp)

theorem diagGL_val (c d : Fˣ) :
    ((diagGL F (c, d) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      diagonal ![(c : F), (d : F)] := rfl

@[expose] noncomputable def projectiveDiagonal : Subgroup (ProjGenLinGroup (Fin 2) F) :=
  (ProjGenLinGroup.mk.comp (diagGL F)).range

end Diagonal

section SplitTorus

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

omit [Fintype F] in
theorem splitTorus_eq_comap :
    splitTorus F b m hm heven =
      (projectiveDiagonal F).comap (projectiveMap F b m hm heven) := by
  ext g
  rw [Subgroup.mem_comap, projectiveDiagonal, MonoidHom.mem_range, mem_splitTorus_iff]
  obtain ⟨M, hM⟩ := ProjGenLinGroup.mk_surjective (projectiveMap F b m hm heven g)
  rw [smul_eq_coordinateGLAction hM.symm, smul_eq_coordinateGLAction hM.symm,
    coordinateGLAction_none_eq_none_iff, coordinateGLAction_some_eq_some_iff]
  simp only [mul_zero, add_zero, zero_add]
  constructor
  · rintro ⟨h10, h01⟩
    have h01' : M.val 0 1 = 0 := neg_eq_zero.mp h01
    have hdet := M.det_ne_zero
    rw [det_fin_two, h10, h01', mul_zero, sub_zero] at hdet
    refine ⟨(Units.mk0 _ (left_ne_zero_of_mul hdet), Units.mk0 _ (right_ne_zero_of_mul hdet)),
      ?_⟩
    rw [← hM, MonoidHom.comp_apply]
    congr 1
    apply Units.ext
    rw [diagGL_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h01']
  · rintro ⟨⟨c, d⟩, hcd⟩
    rw [MonoidHom.comp_apply, ← hM, ProjGenLinGroup.mk_eq_mk_iff] at hcd
    obtain ⟨u, hu⟩ := hcd
    have hval := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) hu
    simp only [Units.val_mul, diagGL_val, GeneralLinearGroup.coe_scalar] at hval
    constructor
    · have h := congrFun (congrFun hval 1) 0
      simp [Matrix.mul_apply, Fin.sum_univ_two] at h
      exact h.symm
    · have h := congrFun (congrFun hval 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two] at h
      rw [← h, neg_zero]

omit [Fintype F] in
theorem splitTorus_fixed_iff_points (hb : ¬ IsSquare b) {t : CentralExtension F b m hm heven}
    (ht : t ∈ splitTorus F b m hm heven)
    (htA : t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) (p : Omega F) :
    t • p = p ↔ p = none ∨ p = some 0 := by
  obtain ⟨h1, h2⟩ := (mem_splitTorus_iff F b m hm heven t).mp ht
  constructor
  · intro hp
    cases p with
    | none => exact Or.inl rfl
    | some y =>
      by_cases hy : y = 0
      · exact Or.inr (by rw [hy])
      · exact absurd hp (splitTorus_smul_some_ne F b m hm heven hb ht htA hy)
  · rintro (rfl | rfl)
    · exact h1
    · exact h2

omit [Fintype F] in
theorem weylElement_conj_torusGenerator' :
    weylElement F b m hm heven * torusGenerator F b m hm heven * (weylElement F b m hm heven)⁻¹ =
      torusDiag F b m hm heven b * torusGenerator F b m hm heven := by
  rw [← weylElement_inv_conj, weylElement_inv_conj_torusGenerator]
  have hc := torusGenerator_mul_torusDiag F b m hm heven (-1)
  have hc2 : torusGenerator F b m hm heven ^ 2 * torusDiag F b m hm heven (-1) =
      torusDiag F b m hm heven (-1) * torusGenerator F b m hm heven ^ 2 :=
    (Commute.pow_left hc 2).eq
  have hb' : torusDiag F b m hm heven (-b) * torusDiag F b m hm heven (-1) =
      torusDiag F b m hm heven b := by rw [← torusDiag_mul, neg_mul_neg, mul_one]
  calc torusDiag F b m hm heven (-b) * torusGenerator F b m hm heven ^ 2 *
        torusDiag F b m hm heven (-1) * (torusGenerator F b m hm heven)⁻¹
      = torusDiag F b m hm heven (-b) * (torusGenerator F b m hm heven ^ 2 *
          torusDiag F b m hm heven (-1)) * (torusGenerator F b m hm heven)⁻¹ := by group
    _ = _ := by rw [hc2, ← hb']; group

omit [Fintype F] in
theorem weylElement_conj_normalForm (c : Fˣ) (k : ℕ) :
    weylElement F b m hm heven * (torusDiag F b m hm heven c * torusGenerator F b m hm heven ^ k) *
        (weylElement F b m hm heven)⁻¹ =
      torusDiag F b m hm heven (c⁻¹ * b ^ k) * torusGenerator F b m hm heven ^ k := by
  have hconj : weylElement F b m hm heven *
      (torusDiag F b m hm heven c * torusGenerator F b m hm heven ^ k) *
        (weylElement F b m hm heven)⁻¹ =
      (weylElement F b m hm heven * torusDiag F b m hm heven c * (weylElement F b m hm heven)⁻¹) *
        (weylElement F b m hm heven * torusGenerator F b m hm heven *
          (weylElement F b m hm heven)⁻¹) ^ k := by
    rw [conj_pow]
    group
  have hc : Commute (torusDiag F b m hm heven b) (torusGenerator F b m hm heven) :=
    (torusGenerator_mul_torusDiag F b m hm heven b).symm
  rw [hconj, weylElement_conj_torusDiag, weylElement_conj_torusGenerator', hc.mul_pow,
    ← mul_assoc, ← torusDiag_pow, ← torusDiag_mul]

omit [Fintype F] in
theorem splitTorus_weyl_fixed_iff (hb : ¬ IsSquare b) {g : CentralExtension F b m hm heven}
    (hg : g ∈ splitTorus F b m hm heven) :
    weylElement F b m hm heven * g * (weylElement F b m hm heven)⁻¹ = g ↔
      g ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
  constructor
  · intro hfix
    obtain ⟨c, k, rfl⟩ := splitTorus_normalForm F b m hm heven g hg
    rw [weylElement_conj_normalForm] at hfix
    obtain ⟨hc, -⟩ := splitTorus_normalForm_unique F b m hm heven hfix
    have hsq : b ^ (k : ℕ) = c * c := by
      calc b ^ (k : ℕ) = c * (c⁻¹ * b ^ (k : ℕ)) := by group
        _ = c * c := by rw [hc]
    have hsqF : (b : F) ^ (k : ℕ) = (c : F) * c := by
      have h := congrArg (fun s : Fˣ => (s : F)) hsq
      simpa using h
    have hb0 : (b : F) ≠ 0 := b.ne_zero
    rcases Nat.even_or_odd' (k : ℕ) with ⟨i, hi | hi⟩
    ·
      have hone : ((c * (-b⁻¹) ^ i : Fˣ) : F) * ((c * (-b⁻¹) ^ i : Fˣ) : F) = 1 := by
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg,
          Units.val_inv_eq_inv_val]
        rw [hi] at hsqF
        calc (c : F) * (-(b : F)⁻¹) ^ i * ((c : F) * (-(b : F)⁻¹) ^ i)
            = ((c : F) * (c : F)) * (((b : F)⁻¹) ^ 2) ^ i := by
              rw [neg_pow]; ring_nf; rw [show (-1 : F) ^ (i * 2) = 1 by
                rw [pow_mul']; simp]; ring
          _ = (b : F) ^ (2 * i) * (((b : F)⁻¹) ^ 2) ^ i := by rw [← hsqF]
          _ = 1 := by rw [pow_mul, ← mul_pow, ← mul_pow, mul_inv_cancel₀ hb0, one_pow, one_pow]
      have hcases : c * (-b⁻¹) ^ i = 1 ∨ c * (-b⁻¹) ^ i = -1 := by
        rcases mul_self_eq_one_iff.mp hone with h1 | h1
        · exact Or.inl (Units.ext h1)
        · exact Or.inr (Units.ext (by rw [h1]; simp))
      have hcomm : Commute (torusDiag F b m hm heven (-b⁻¹)) (cyclicGenerator F b m hm heven ^ 2) :=
        (cyclicGenerator_sq_comm F b m hm heven _).symm
      have hv : torusGenerator F b m hm heven ^ (k : ℕ) =
          torusDiag F b m hm heven ((-b⁻¹) ^ i) * (cyclicGenerator F b m hm heven ^ 2) ^ i := by
        rw [hi, pow_mul, torusGenerator_sq, hcomm.mul_pow, torusDiag_pow]
      rw [hv, ← mul_assoc, ← torusDiag_mul]
      refine Subgroup.mul_mem _ ?_ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
      rcases hcases with h1 | h1
      · rw [h1, torusDiag_one]
        exact Subgroup.one_mem _
      · rw [h1, torusDiag_neg_one]
        obtain ⟨l, hl⟩ := id heven
        refine ⟨l, ?_⟩
        simp only [zpow_natCast]
        rw [← pow_mul]
        congr 1
        omega
    ·
      exfalso
      apply hb
      refine ⟨c * (b ^ i)⁻¹, Units.ext ?_⟩
      rw [hi] at hsqF
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
      have hbi : (b : F) ^ i ≠ 0 := pow_ne_zero _ hb0
      field_simp
      linear_combination hsqF
  · intro hg'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg'
    rw [(Commute.zpow_left (cyclicGenerator_sq_comm F b m hm heven
      (weylElement F b m hm heven)) k).eq.symm, mul_inv_cancel_right]

omit [Fintype F] in
theorem weylElement_conj_mem_splitTorus {t : CentralExtension F b m hm heven}
    (ht : t ∈ splitTorus F b m hm heven) :
    weylElement F b m hm heven * t * (weylElement F b m hm heven)⁻¹ ∈
      splitTorus F b m hm heven := by
  rw [← weylElement_inv_conj]
  exact weyl_conj_mem_splitTorus F b m hm heven ht

omit [Fintype F] in
theorem splitTorus_conj_cases (hb : ¬ IsSquare b) {t : CentralExtension F b m hm heven}
    (ht : t ∈ splitTorus F b m hm heven)
    (htA : t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2))
    {g : CentralExtension F b m hm heven} (hg : g * t * g⁻¹ ∈ splitTorus F b m hm heven) :
    g ∈ splitTorus F b m hm heven ∨
      (weylElement F b m hm heven)⁻¹ * g ∈ splitTorus F b m hm heven := by
  obtain ⟨h1, h2⟩ := (mem_splitTorus_iff F b m hm heven _).mp hg
  have hfix : ∀ p : Omega F, (g * t * g⁻¹) • p = p → g⁻¹ • p = none ∨ g⁻¹ • p = some 0 := by
    intro p hp
    apply (splitTorus_fixed_iff_points hb ht htA _).mp
    rw [mul_smul, mul_smul] at hp
    exact (eq_inv_smul_iff.mpr hp).symm ▸ rfl
  rcases hfix none h1 with hinf | hinf <;> rcases hfix (some 0) h2 with hz | hz
  · exact absurd (smul_left_cancel g⁻¹ (hinf.trans hz.symm)) (by simp)
  · left
    refine (splitTorus F b m hm heven).inv_mem_iff.mp ?_
    exact (mem_splitTorus_iff F b m hm heven _).mpr ⟨hinf, hz⟩
  · right
    refine (mem_splitTorus_iff F b m hm heven _).mpr ⟨?_, ?_⟩
    · rw [mul_smul, (inv_smul_eq_iff.mp hz).symm, weylElement_inv_smul_zero]
    · rw [mul_smul, (inv_smul_eq_iff.mp hinf).symm, weylElement_inv_smul_none]
  · exact absurd (smul_left_cancel g⁻¹ (hinf.trans hz.symm)) (by simp)

end SplitTorus

section SplitClasses

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

theorem centralizer_splitTorus (hb : ¬ IsSquare b) {t : CentralExtension F b m hm heven}
    (ht : t ∈ splitTorus F b m hm heven)
    (htA : t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    Subgroup.centralizer {t} = splitTorus F b m hm heven := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have hconj : g * t * g⁻¹ = t := by rw [hg, mul_inv_cancel_right]
    rcases splitTorus_conj_cases hb ht htA (hconj ▸ ht) with h | h
    · exact h
    · exfalso
      apply htA
      rw [← splitTorus_weyl_fixed_iff hb ht]
      have hτ : t * ((weylElement F b m hm heven)⁻¹ * g) =
          ((weylElement F b m hm heven)⁻¹ * g) * t := splitTorus_mul_comm F b m hm heven ht h
      have hτt : ((weylElement F b m hm heven)⁻¹ * g) * t *
          ((weylElement F b m hm heven)⁻¹ * g)⁻¹ = t := by rw [← hτ, mul_inv_cancel_right]
      calc weylElement F b m hm heven * t * (weylElement F b m hm heven)⁻¹
          = weylElement F b m hm heven * (((weylElement F b m hm heven)⁻¹ * g) * t *
              ((weylElement F b m hm heven)⁻¹ * g)⁻¹) * (weylElement F b m hm heven)⁻¹ := by
            rw [hτt]
        _ = g * t * g⁻¹ := by group
        _ = t := hconj
  · intro hg
    exact splitTorus_mul_comm F b m hm heven hg ht

theorem isConj_splitTorus_iff (hb : ¬ IsSquare b) {t t' : CentralExtension F b m hm heven}
    (ht : t ∈ splitTorus F b m hm heven)
    (htA : t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2))
    (ht' : t' ∈ splitTorus F b m hm heven) :
    IsConj t t' ↔
      t' = t ∨ t' = weylElement F b m hm heven * t * (weylElement F b m hm heven)⁻¹ := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := isConj_iff.mp h
    rcases splitTorus_conj_cases hb ht htA ht' with hg | hg
    · left
      rw [splitTorus_mul_comm F b m hm heven hg ht, mul_inv_cancel_right]
    · right
      have hτ : t * ((weylElement F b m hm heven)⁻¹ * g) =
          ((weylElement F b m hm heven)⁻¹ * g) * t := splitTorus_mul_comm F b m hm heven ht hg
      calc g * t * g⁻¹ = weylElement F b m hm heven * (((weylElement F b m hm heven)⁻¹ * g) * t) *
            ((weylElement F b m hm heven)⁻¹ * g)⁻¹ * (weylElement F b m hm heven)⁻¹ := by group
        _ = _ := by rw [← hτ]; group
  · rintro (rfl | rfl)
    · exact IsConj.refl _
    · exact isConj_iff.mpr ⟨_, rfl⟩

theorem weylElement_conj_ne (hb : ¬ IsSquare b) {t : CentralExtension F b m hm heven}
    (ht : t ∈ splitTorus F b m hm heven)
    (htA : t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    weylElement F b m hm heven * t * (weylElement F b m hm heven)⁻¹ ≠ t :=
  fun h => htA ((splitTorus_weyl_fixed_iff hb ht).mp h)

theorem torusGenerator_not_mem_zpowers (hb : ¬ IsSquare b) :
    torusGenerator F b m hm heven ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
  intro h
  have h1 := zpowers_cyclicGenerator_sq_smul F b m hm heven h (some 1)
  rw [torusGenerator_smul_some, Option.some.injEq, one_div] at h1
  apply hb
  refine ⟨1, Units.ext ?_⟩
  have := inv_eq_one.mp h1
  simp [this]

theorem mem_normalizer_splitTorus_iff (hb : ¬ IsSquare b) (g : CentralExtension F b m hm heven) :
    g ∈ Subgroup.normalizer (splitTorus F b m hm heven : Set (CentralExtension F b m hm heven)) ↔
      g ∈ splitTorus F b m hm heven ∨
        (weylElement F b m hm heven)⁻¹ * g ∈ splitTorus F b m hm heven := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hg
    exact splitTorus_conj_cases hb (torusGenerator_mem_splitTorus F b m hm heven)
      (torusGenerator_not_mem_zpowers hb)
      ((hg _).mp (torusGenerator_mem_splitTorus F b m hm heven))
  · rintro (hg | hg) h
    · constructor
      · intro hh
        exact (splitTorus F b m hm heven).mul_mem ((splitTorus F b m hm heven).mul_mem hg hh)
          ((splitTorus F b m hm heven).inv_mem hg)
      · intro hh
        have := (splitTorus F b m hm heven).mul_mem
          ((splitTorus F b m hm heven).mul_mem ((splitTorus F b m hm heven).inv_mem hg) hh) hg
        simpa [mul_assoc] using this
    · set τ := (weylElement F b m hm heven)⁻¹ * g with hτ
      have hgw : g = weylElement F b m hm heven * τ := by rw [hτ, mul_inv_cancel_left]
      constructor
      · intro hh
        have h1 : τ * h * τ⁻¹ ∈ splitTorus F b m hm heven :=
          (splitTorus F b m hm heven).mul_mem ((splitTorus F b m hm heven).mul_mem hg hh)
            ((splitTorus F b m hm heven).inv_mem hg)
        have h2 := weylElement_conj_mem_splitTorus h1
        rw [hgw]
        simpa [mul_assoc] using h2
      · intro hh
        rw [hgw] at hh
        have h1 : (weylElement F b m hm heven)⁻¹ *
            (weylElement F b m hm heven * τ * h * (weylElement F b m hm heven * τ)⁻¹) *
              weylElement F b m hm heven ∈ splitTorus F b m hm heven :=
          weyl_conj_mem_splitTorus F b m hm heven hh
        have h2 : τ * h * τ⁻¹ ∈ splitTorus F b m hm heven := by
          have : (weylElement F b m hm heven)⁻¹ *
              (weylElement F b m hm heven * τ * h * (weylElement F b m hm heven * τ)⁻¹) *
                weylElement F b m hm heven = τ * h * τ⁻¹ := by group
          rwa [this] at h1
        have h3 := (splitTorus F b m hm heven).mul_mem
          ((splitTorus F b m hm heven).mul_mem ((splitTorus F b m hm heven).inv_mem hg) h2) hg
        simpa [mul_assoc] using h3

end SplitClasses

section UnipotentClasses

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

theorem cyclicGenerator_sq_zpowers_comm {α : CentralExtension F b m hm heven}
    (hα : α ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2))
    (g : CentralExtension F b m hm heven) : α * g = g * α := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hα
  exact (Commute.zpow_left (cyclicGenerator_sq_comm F b m hm heven g) k).eq

theorem unipotentElement_injective :
    Function.Injective (unipotentElement F b m hm heven) := by
  intro s t h
  have h0 := congrArg (fun g : CentralExtension F b m hm heven => g • (some 0 : Omega F)) h
  simp only [unipotentElement_smul_some, zero_add, Option.some.injEq] at h0
  exact h0

theorem unipotentElement_pow (s : F) (n : ℕ) :
    unipotentElement F b m hm heven s ^ n = unipotentElement F b m hm heven (n * s) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, unipotentElement_zero]
  | succ n ih => rw [pow_succ, ih, ← unipotentElement_add]; push_cast; ring_nf

theorem splitTorus_conj_unipotent_eq {τ : CentralExtension F b m hm heven}
    (hτ : τ ∈ splitTorus F b m hm heven) {α : F}
    (hα : ∀ y : F, τ • (some y : Omega F) = some (α * y)) (s : F) :
    τ * unipotentElement F b m hm heven s * τ⁻¹ = unipotentElement F b m hm heven (α * s) := by
  obtain ⟨s', hs'⟩ := splitTorus_conj_unipotent F b m hm heven τ hτ s
  rw [hs']
  congr 1
  have h0 := congrArg (fun g : CentralExtension F b m hm heven => g • (some 0 : Omega F)) hs'
  simp only [mul_smul] at h0
  have hτ0 : τ⁻¹ • (some 0 : Omega F) = some 0 := by
    rw [inv_smul_eq_iff]
    exact ((mem_splitTorus_iff F b m hm heven τ).mp hτ).2.symm
  rw [hτ0, unipotentElement_smul_some, zero_add, hα, unipotentElement_smul_some, zero_add,
    Option.some.injEq] at h0
  exact h0.symm

theorem exists_splitTorus_multiplier [Finite F] (hb : ¬ IsSquare b) (α : Fˣ) :
    ∃ τ ∈ splitTorus F b m hm heven, ∀ y : F, τ • (some y : Omega F) = some ((α : F) * y) := by
  by_cases hα : IsSquare α
  · obtain ⟨c, rfl⟩ := hα
    refine ⟨torusDiag F b m hm heven c, torusDiag_mem_splitTorus F b m hm heven c, fun y => ?_⟩
    rw [torusDiag_smul_some]
    congr 1
    push_cast
    ring
  · obtain ⟨r, hr⟩ := isSquare_mul_inv_of_not_isSquare F hα hb
    refine ⟨torusDiag F b m hm heven (r * b) * torusGenerator F b m hm heven,
      (splitTorus F b m hm heven).mul_mem (torusDiag_mem_splitTorus F b m hm heven _)
        (torusGenerator_mem_splitTorus F b m hm heven), fun y => ?_⟩
    rw [mul_smul, torusGenerator_smul_some, torusDiag_smul_some]
    congr 1
    have hαr : (α : F) = (r : F) * r * b := by
      have h := congrArg (fun u : Fˣ => (u : F)) hr
      simp only [Units.val_mul, Units.val_inv_eq_inv_val] at h
      have hb0 : (b : F) ≠ 0 := b.ne_zero
      field_simp at h
      linear_combination h
    rw [hαr]
    have hb0 : (b : F) ≠ 0 := b.ne_zero
    push_cast
    field_simp

theorem isConj_unipotent [Finite F] (hb : ¬ IsSquare b) {t : F} (ht : t ≠ 0) :
    IsConj (unipotentElement F b m hm heven 1) (unipotentElement F b m hm heven t) := by
  obtain ⟨τ, hτ, hα⟩ := exists_splitTorus_multiplier (hm := hm) (heven := heven) hb
    (Units.mk0 t ht)
  refine isConj_iff.mpr ⟨τ, ?_⟩
  rw [splitTorus_conj_unipotent_eq hτ hα, Units.val_mk0, mul_one]

theorem mem_centralizer_unipotent_iff (hb : ¬ IsSquare b) (g : CentralExtension F b m hm heven) :
    g ∈ Subgroup.centralizer {unipotentElement F b m hm heven 1} ↔
      ∃ α ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2), ∃ t : F,
        g = α * unipotentElement F b m hm heven t := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have hinf : g • (none : Omega F) = none := by
      have hfix : unipotentElement F b m hm heven 1 • (g • (none : Omega F)) =
          g • (none : Omega F) := by
        rw [← mul_smul, ← hg, mul_smul, unipotentElement_smul_none]
      cases h : g • (none : Omega F) with
      | none => rfl
      | some y =>
        rw [h] at hfix
        exact absurd hfix (unipotentElement_smul_some_ne F b m hm heven one_ne_zero y)
    obtain ⟨β, hβ⟩ := borel_decomposition F b m hm heven g hinf
    set τ := (unipotentElement F b m hm heven β)⁻¹ * g with hτ
    obtain ⟨α, -, hα⟩ := splitTorus_smul_some F b m hm heven hβ
    have hgτ : g = unipotentElement F b m hm heven β * τ := by rw [hτ, mul_inv_cancel_left]
    have hconj := splitTorus_conj_unipotent_eq hβ hα 1
    have hα1 : α = 1 := by
      have h1 : g * unipotentElement F b m hm heven 1 * g⁻¹ =
          unipotentElement F b m hm heven 1 := by
        rw [hg, mul_inv_cancel_right]
      rw [hgτ] at h1
      have h3 : unipotentElement F b m hm heven β * (τ * unipotentElement F b m hm heven 1 * τ⁻¹) *
          (unipotentElement F b m hm heven β)⁻¹ = unipotentElement F b m hm heven 1 := by
        calc unipotentElement F b m hm heven β * (τ * unipotentElement F b m hm heven 1 * τ⁻¹) *
              (unipotentElement F b m hm heven β)⁻¹
            = unipotentElement F b m hm heven β * τ * unipotentElement F b m hm heven 1 *
                (unipotentElement F b m hm heven β * τ)⁻¹ := by group
          _ = _ := h1
      rw [hconj, unipotentElement_neg_eq, ← unipotentElement_add, ← unipotentElement_add] at h3
      have := unipotentElement_injective h3
      linear_combination this
    have hτA : τ ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
      rw [← fixes_all_iff F b m hm heven hb]
      intro p
      cases p with
      | none => exact ((mem_splitTorus_iff F b m hm heven τ).mp hβ).1
      | some y => rw [hα, hα1, one_mul]
    refine ⟨τ, hτA, β, ?_⟩
    rw [hgτ]
    exact (cyclicGenerator_sq_zpowers_comm hτA _).symm
  · rintro ⟨α, hα, t, rfl⟩
    rw [mul_assoc, ← unipotentElement_add, add_comm, unipotentElement_add, ← mul_assoc,
      cyclicGenerator_sq_zpowers_comm hα, mul_assoc]

end UnipotentClasses

end CFSG.Wreathed.CentralSL2
