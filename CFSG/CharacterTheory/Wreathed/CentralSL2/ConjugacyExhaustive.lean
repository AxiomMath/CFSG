module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.ConjugacyNonsplit
public import CFSG.CharacterTheory.Wreathed.CentralSL2.ConjugacyUnipotent

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section Companion

variable {F : Type} [Field F]

theorem companion_conj (A : Matrix (Fin 2) (Fin 2) F) :
    A * !![1, A 0 0; 0, A 1 0] = !![1, A 0 0; 0, A 1 0] * !![0, -A.det; 1, A.trace] := by
  rw [Matrix.det_fin_two, Matrix.trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

variable [Fintype F] {E : Type} [Field E] [Algebra F E] (basis : Module.Basis (Fin 2) F E)

theorem exists_conj_mulGL (h2 : (2 : F) ≠ 0) {M : GL (Fin 2) F}
    (hfix : ∀ p : Omega F, coordinateGLAction F M p ≠ p) :
    ∃ Q : GL (Fin 2) F, ∃ s : Eˣ, Q * M * Q⁻¹ = mulGL F E basis s := by
  set τ := (M : Matrix (Fin 2) (Fin 2) F).trace with hτ
  set d := (M : Matrix (Fin 2) (Fin 2) F).det with hd
  have hd0 : d ≠ 0 := M.det_ne_zero
  have h10 : (M : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 :=
    fun h => hfix none ((coordinateGLAction_none_eq_none_iff M).mpr h)
  have hscalar : ¬ ∃ c : Fˣ, M = GeneralLinearGroup.scalar (Fin 2) c := by
    rintro ⟨c, rfl⟩
    exact hfix none (by rw [coordinateGLAction_scalar]; rfl)
  have hcount := card_fixed_coordinateGLAction h2 M hscalar
  have hzero : Nat.card {x : Omega F // coordinateGLAction F M x = x} = 0 := by
    rw [Nat.card_eq_zero]
    left
    exact ⟨fun x => hfix x.1 x.2⟩
  rw [hzero, sqrtCount_eq h2] at hcount
  set D := τ ^ 2 - 4 * d with hD
  have hD0 : D ≠ 0 := by
    intro h
    rw [ite_eq_left h] at hcount
    exact one_ne_zero hcount.symm
  have hDsq : ¬ IsSquare D := by
    intro h
    rw [ite_eq_right hD0, ite_eq_left h] at hcount
    exact two_ne_zero hcount.symm
  obtain ⟨e, he⟩ := exists_norm_eq F E basis (Units.mk0 D hD0)
  have hqodd := odd_card F h2
  obtain ⟨k, hk⟩ := hqodd
  set δ : E := (e : E) ^ (k + 1) with hδ
  have hδsq : δ * δ = algebraMap F E D := by
    rw [hδ, ← pow_add, show k + 1 + (k + 1) = Nat.card F + 1 by omega, pow_succ', he,
      Units.val_mk0]
  have h2E : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (map_ne_zero _).mpr h2
  set s : E := (algebraMap F E τ + δ) / 2 with hs
  have hroot : s * s - algebraMap F E τ * s + algebraMap F E d = 0 := by
    rw [hs]
    field_simp
    have : δ * δ = algebraMap F E τ ^ 2 - 4 * algebraMap F E d := by
      rw [hδsq, hD, map_sub, map_mul, map_pow, map_ofNat]
    linear_combination this
  have hsF : s ∉ Set.range (algebraMap F E) := by
    rintro ⟨c, hc⟩
    apply hDsq
    have hδc : δ = algebraMap F E (2 * c - τ) := by
      have h2s : 2 * s = algebraMap F E τ + δ := by rw [hs]; field_simp
      rw [map_sub, map_mul, map_ofNat, hc]
      linear_combination -h2s
    refine ⟨2 * c - τ, (algebraMap F E).injective ?_⟩
    rw [← hδsq, hδc, map_mul]
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hroot
    have h1 : algebraMap F E d = 0 := by linear_combination hroot
    exact hd0 ((map_eq_zero_iff _ (algebraMap F E).injective).mp h1)
  set su : Eˣ := Units.mk0 s hs0 with hsu
  set C := mulMatrix F E basis (su : E) with hC
  have hCH := cayley_hamilton_two C
  have hCC : C * C = τ • C - d • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h1 : Algebra.leftMulMatrix basis (s * s) = Algebra.leftMulMatrix basis
        (algebraMap F E τ * s - algebraMap F E d) := by
      congr 1
      linear_combination hroot
    rw [map_mul, map_sub, map_mul, AlgHom.commutes, AlgHom.commutes, ← Algebra.smul_def,
      Algebra.algebraMap_eq_smul_one] at h1
    exact h1
  have htr : C.trace = τ ∧ C.det = d := by
    have hdiff : (C.trace - τ) • C = (C.det - d) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      have h := hCH.symm.trans hCC
      rw [sub_smul, sub_smul]
      calc C.trace • C - τ • C = (C.trace • C - C.det • (1 : Matrix (Fin 2) (Fin 2) F)) -
            τ • C + C.det • (1 : Matrix (Fin 2) (Fin 2) F) := by abel
        _ = (τ • C - d • (1 : Matrix (Fin 2) (Fin 2) F)) - τ • C +
            C.det • (1 : Matrix (Fin 2) (Fin 2) F) := by rw [h]
        _ = _ := by abel
    by_cases ht : C.trace - τ = 0
    · refine ⟨sub_eq_zero.mp ht, ?_⟩
      rw [ht, zero_smul] at hdiff
      have h00 := congrFun (congrFun hdiff 0) 0
      simp only [Matrix.zero_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at h00
      exact sub_eq_zero.mp h00.symm
    · exfalso
      apply hsF
      obtain ⟨c, hc⟩ : ∃ c : F, c = (C.trace - τ)⁻¹ * (C.det - d) := ⟨_, rfl⟩
      refine ⟨c, ?_⟩
      apply mulMatrix_injective F E basis
      rw [mulMatrix_algebraMap]
      have h1 : C = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [hc, mul_smul, ← hdiff, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [show mulMatrix F E basis s = C from rfl, h1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  have hC10 : C 1 0 ≠ 0 := by
    intro h
    exact coordinateGLAction_mulGL_ne basis su hsF none
      ((coordinateGLAction_none_eq_none_iff _).mpr (by rw [mulGL_val]; exact h))
  have hP₁ : (!![1, (M : Matrix (Fin 2) (Fin 2) F) 0 0; 0, (M : Matrix (Fin 2) (Fin 2) F) 1 0] :
      Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simpa using h10
  have hP₂ : (!![1, C 0 0; 0, C 1 0] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simpa using hC10
  have hK : (!![0, -d; 1, τ] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simpa using hd0
  set P₁ := GeneralLinearGroup.mkOfDetNeZero _ hP₁
  set P₂ := GeneralLinearGroup.mkOfDetNeZero _ hP₂
  set K := GeneralLinearGroup.mkOfDetNeZero _ hK
  have hM : M * P₁ = P₁ * K := by
    apply Units.ext
    simp only [Units.val_mul, P₁, K, GeneralLinearGroup.val_mkOfDetNeZero]
    exact companion_conj _
  have hCK : mulGL F E basis su * P₂ = P₂ * K := by
    apply Units.ext
    simp only [Units.val_mul, P₂, K, GeneralLinearGroup.val_mkOfDetNeZero, mulGL_val]
    rw [← htr.1, ← htr.2]
    exact companion_conj _
  refine ⟨P₂ * P₁⁻¹, su, ?_⟩
  calc P₂ * P₁⁻¹ * M * (P₂ * P₁⁻¹)⁻¹ = P₂ * (P₁⁻¹ * (M * P₁)) * P₂⁻¹ := by group
    _ = P₂ * K * P₂⁻¹ := by rw [hM]; group
    _ = mulGL F E basis su := by rw [← hCK, mul_inv_cancel_right]

end Companion

section Types

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {E : Type} [Field E] [Algebra F E]

omit [Fintype F] in
theorem conj_not_mem_zpowers {g : CentralExtension F b m hm heven}
    (hg : g ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2))
    (k : CentralExtension F b m hm heven) :
    k * g * k⁻¹ ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
  intro h
  apply hg
  have hc := cyclicGenerator_sq_zpowers_comm h k
  have h1 : k * g * k⁻¹ * k = k * g := by group
  rw [hc] at h1
  rw [(mul_left_cancel h1).symm]
  exact h

theorem conjugacy_type_exists (basis : Module.Basis (Fin 2) F E) (hb : ¬ IsSquare b)
    (g : CentralExtension F b m hm heven) :
    g ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) ∨
      (∃ α ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2),
        IsConj g (α * unipotentElement F b m hm heven 1)) ∨
      (∃ t ∈ splitTorus F b m hm heven,
        t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) ∧ IsConj g t) ∨
      (∃ t ∈ nonsplitTorus F b m hm heven E basis,
        t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) ∧ IsConj g t) := by
  by_cases hgA : g ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)
  · exact Or.inl hgA
  right
  have h2 := two_ne_zero_of_not_isSquare hb
  rcases card_fixed_le_two hb hgA with h0 | h1 | h2'
  ·
    right
    right
    obtain ⟨M, hM⟩ := ProjGenLinGroup.mk_surjective (projectiveMap F b m hm heven g)
    have hempty : IsEmpty {p : Omega F // g • p = p} := by
      rcases Nat.card_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h (not_infinite_iff_finite.mpr inferInstance)
    have hfix : ∀ p : Omega F, coordinateGLAction F M p ≠ p := by
      intro p hp
      rw [← smul_eq_coordinateGLAction hM.symm] at hp
      exact hempty.elim ⟨p, hp⟩
    obtain ⟨Q, s, hQ⟩ := exists_conj_mulGL basis h2 hfix
    obtain ⟨k, hk⟩ := projectiveMap_surjective F b m hm heven hb (ProjGenLinGroup.mk Q)
    refine ⟨k * g * k⁻¹, (mem_nonsplitTorus_iff _).mpr ⟨s, ?_⟩, conj_not_mem_zpowers hgA k,
      isConj_iff.mpr ⟨k, rfl⟩⟩
    rw [← hQ]
    simp only [map_mul, map_inv]
    rw [hk, hM]
  ·
    left
    obtain ⟨⟨p₀, hp₀⟩, huniq⟩ : ∃ x : {p : Omega F // g • p = p}, ∀ y, y = x := by
      have := Nat.card_eq_one_iff_unique.mp h1
      exact ⟨this.2.some, fun y => this.1.elim y _⟩
    have h2t := centralExtension_isMultiplyPretransitive F b m hm heven
    have htrans : MulAction.IsPretransitive (CentralExtension F b m hm heven) (Omega F) :=
      MulAction.isPretransitive_of_is_two_pretransitive
    obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (CentralExtension F b m hm heven)
      (none : Omega F) p₀
    set g' := k⁻¹ * g * k with hg'
    have hfix' : ∀ p : Omega F, g' • p = p → p = none := by
      intro p hp
      have hp' : g • (k • p) = k • p := by
        rw [hg', mul_smul, mul_smul, inv_smul_eq_iff] at hp
        exact hp
      have := congrArg Subtype.val (huniq ⟨k • p, hp'⟩)
      simp only at this
      rw [← hk] at this
      exact smul_left_cancel k this
    have hinf : g' • (none : Omega F) = none := by
      rw [hg', mul_smul, mul_smul, hk, hp₀, inv_smul_eq_iff, hk]
    obtain ⟨β, hβ⟩ := borel_decomposition F b m hm heven g' hinf
    set τ := (unipotentElement F b m hm heven β)⁻¹ * g' with hτ
    have hgτ : g' = unipotentElement F b m hm heven β * τ := by rw [hτ, mul_inv_cancel_left]
    obtain ⟨α, -, hα⟩ := splitTorus_smul_some F b m hm heven hβ
    have hα1 : α = 1 := by
      by_contra hα1
      have h1α : 1 - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα1)
      have hy0 : g' • (some (β / (1 - α)) : Omega F) = some (β / (1 - α)) := by
        rw [hgτ, mul_smul, hα, unipotentElement_smul_some, Option.some.injEq]
        field_simp
        ring
      exact absurd (hfix' _ hy0) (by simp)
    have hτA : τ ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
      rw [← fixes_all_iff F b m hm heven hb]
      intro p
      cases p with
      | none => exact ((mem_splitTorus_iff F b m hm heven τ).mp hβ).1
      | some y => rw [hα, hα1, one_mul]
    have hβ0 : β ≠ 0 := by
      rintro rfl
      rw [unipotentElement_zero, one_mul] at hgτ
      apply hgA
      have h' : g = k * g' * k⁻¹ := by rw [hg']; group
      rw [h', hgτ, ← cyclicGenerator_sq_zpowers_comm hτA k, mul_inv_cancel_right]
      exact hτA
    refine ⟨τ, hτA, ?_⟩
    have hconj1 : IsConj g g' := isConj_iff.mpr ⟨k⁻¹, by rw [hg', inv_inv]⟩
    have hconj2 : IsConj g' (τ * unipotentElement F b m hm heven 1) := by
      rw [hgτ, ← cyclicGenerator_sq_zpowers_comm hτA]
      exact isConj_mul_central hτA (isConj_unipotent (hm := hm) (heven := heven) hb hβ0).symm
    exact hconj1.trans hconj2
  ·
    right
    left
    obtain ⟨⟨p₁, hp₁⟩, ⟨p₂, hp₂⟩, hne, -⟩ := Nat.card_eq_two_iff.mp h2'
    have hne' : p₁ ≠ p₂ := fun h => hne (Subtype.ext h)
    obtain ⟨k, hk1, hk2⟩ := MulAction.is_two_pretransitive_iff.mp
      (centralExtension_isMultiplyPretransitive F b m hm heven)
      (show (none : Omega F) ≠ some 0 by simp) hne'
    have ht : k⁻¹ * g * k ∈ splitTorus F b m hm heven := by
      rw [mem_splitTorus_iff, mul_smul, mul_smul, mul_smul, mul_smul, hk1, hk2, hp₁, hp₂,
        inv_smul_eq_iff, inv_smul_eq_iff, hk1, hk2]
      exact ⟨rfl, rfl⟩
    refine ⟨k⁻¹ * g * k, ht, ?_, isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv]⟩⟩
    have := conj_not_mem_zpowers hgA k⁻¹
    rwa [inv_inv] at this

end Types

end CFSG.Wreathed.CentralSL2
