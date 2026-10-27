module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6Hom

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Chevalley (baseChangeGL baseChangeGL_pinnedX baseChangeGL_injective)

section SLDescent

variable {n : Type} [Fintype n] [DecidableEq n] {K₀ K : Type} [Field K₀] [Field K]

theorem exists_specialLinearGroup_map_eq_of_map_eq (ι : K₀ →+* K) (σ : K →+* K)
    (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) (B : Matrix.SpecialLinearGroup n K)
    (hB : Matrix.SpecialLinearGroup.map σ B = B) :
    ∃ B₀ : Matrix.SpecialLinearGroup n K₀, Matrix.SpecialLinearGroup.map ι B₀ = B := by
  have hent : ∀ i j, ∃ b : K₀, ι b = (B : Matrix n n K) i j := fun i j => by
    refine (hfix _).1 ?_
    have h := congrArg (fun g : Matrix.SpecialLinearGroup n K => (g : Matrix n n K) i j) hB
    simpa [Matrix.SpecialLinearGroup.map_apply_coe] using h
  choose b hb using hent
  have hmap : ι.mapMatrix (Matrix.of b) = (B : Matrix n n K) := by
    ext i j
    simp [hb]
  have hdet : (Matrix.of b).det = 1 := by
    apply ι.injective
    rw [RingHom.map_det, hmap, map_one]
    exact B.2
  set B₀ : Matrix.SpecialLinearGroup n K₀ := ⟨Matrix.of b, hdet⟩ with hB₀
  have hB₀coe : (B₀ : Matrix n n K₀) = Matrix.of b := rfl
  refine ⟨B₀, Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_⟩
  rw [Matrix.SpecialLinearGroup.map_apply_coe, hB₀coe, hmap]

theorem specialLinearGroup_map_map {K₁ : Type} [Field K₁] (ι : K₀ →+* K₁) (σ : K₁ →+* K)
    (A : Matrix.SpecialLinearGroup n K₀) :
    Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.map ι A) =
      Matrix.SpecialLinearGroup.map (σ.comp ι) A := by
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

end SLDescent

section Levi


variable {K M : Type} [Field K] [Field M]

theorem baseChangeGL_mem_rootSpan_a5LeviRoots (ι : K →+* M) (g : a5Levi K) :
    baseChangeGL ι ((g : adjointGroup .E6 K) : ModGL .E6 K) ∈ rootSpan .E6 M a5LeviRoots :=
  F4Pilot.map_rootSpan_baseChangeGL_le ι a5LeviRoots ⟨_, mem_a5Levi_iff.1 g.2, rfl⟩

@[expose] noncomputable def a5LeviBaseChange (ι : K →+* M) : ↥(a5Levi K) →* ↥(a5Levi M) :=
  (((baseChangeGL ι).comp ((adjointGroup .E6 K).subtype.comp (a5Levi K).subtype)).codRestrict
      (adjointGroup .E6 M) fun g => rootSpan_le_adjointGroup_E6 _
        (baseChangeGL_mem_rootSpan_a5LeviRoots ι g)).codRestrict
    (a5Levi M) fun g => mem_a5Levi_iff.2 (baseChangeGL_mem_rootSpan_a5LeviRoots ι g)

theorem coe_a5LeviBaseChange (ι : K →+* M) (g : a5Levi K) :
    (((a5LeviBaseChange ι g : a5Levi M) : adjointGroup .E6 M) : ModGL .E6 M) =
      baseChangeGL ι ((g : adjointGroup .E6 K) : ModGL .E6 K) :=
  rfl

theorem a5LeviBaseChange_injective (ι : K →+* M) : Function.Injective (a5LeviBaseChange ι) :=
  fun _ _ hgh => Subtype.ext (Subtype.ext (baseChangeGL_injective ι
    (congrArg (fun x : a5Levi M => ((x : adjointGroup .E6 M) : ModGL .E6 M)) hgh)))

theorem a5LeviBaseChange_comp {N : Type} [Field N] (ι : K →+* M) (κ : M →+* N) (g : a5Levi K) :
    a5LeviBaseChange κ (a5LeviBaseChange ι g) = a5LeviBaseChange (κ.comp ι) g := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [coe_a5LeviBaseChange, coe_a5LeviBaseChange, coe_a5LeviBaseChange,
    F4Pilot.baseChangeGL_baseChangeGL]

end Levi

section LangMap

variable {K : Type} [Field K] [CharP K 2]

theorem pow_three_eq_one_of_mem_center {Z : Matrix.SpecialLinearGroup (Fin 6) K}
    (hZ : Z ∈ center (Matrix.SpecialLinearGroup (Fin 6) K)) : Z ^ 3 = 1 := by
  obtain ⟨r, hr, hrZ⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hZ
  rw [Fintype.card_fin] at hr
  have hr3 : r ^ 3 = 1 := charTwo_eq_one_of_mul_self_eq_one (by rw [← pow_add]; exact hr)
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrZ, ← map_pow, hr3, map_one,
    Matrix.SpecialLinearGroup.coe_one]

omit [CharP K 2] in
theorem specialLinearGroup_map_map_of_involutive {n : Type} [Fintype n] [DecidableEq n]
    (σ : K →+* K) (hσ : ∀ x : K, σ (σ x) = x) (A : Matrix.SpecialLinearGroup n K) :
    Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.map σ A) = A := by
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe, hσ]

theorem map_mul_inv_eq_of_map_eq_mul (σ : K →+* K) (hσ : ∀ x : K, σ (σ x) = x)
    {A Z : Matrix.SpecialLinearGroup (Fin 6) K}
    (hZ : Z ∈ center (Matrix.SpecialLinearGroup (Fin 6) K))
    (hA : Matrix.SpecialLinearGroup.map σ A = A * Z) :
    Matrix.SpecialLinearGroup.map σ (A * Z⁻¹) = A * Z⁻¹ := by
  have hZ3 : Z ^ 3 = 1 := pow_three_eq_one_of_mem_center hZ
  have h2 : A * Z * Matrix.SpecialLinearGroup.map σ Z = A := by
    have h := specialLinearGroup_map_map_of_involutive σ hσ A
    rwa [hA, map_mul, hA] at h
  have hsZ : Matrix.SpecialLinearGroup.map σ Z = Z⁻¹ := by
    have h3 : Z * Matrix.SpecialLinearGroup.map σ Z = 1 := by
      have h4 := congrArg (A⁻¹ * ·) h2
      simpa [mul_assoc] using h4
    exact eq_inv_of_mul_eq_one_right h3
  rw [map_mul, map_inv, hA, hsZ, inv_inv]
  calc A * Z * Z = A * Z ^ 2 := by rw [mul_assoc, sq]
    _ = A * Z⁻¹ := by
      rw [eq_inv_of_mul_eq_one_left (show Z ^ 2 * Z = 1 by rw [← pow_succ]; exact hZ3)]

end LangMap

section Naturality


variable {K M : Type} [Field K] [Finite K] [CharP K 2] [Field M] [Finite M] [CharP M 2]

theorem a5LeviBaseChange_slToA5Levi (ι : K →+* M) (A : Matrix.SpecialLinearGroup (Fin 6) K) :
    a5LeviBaseChange ι (slToA5Levi A) = slToA5Levi (Matrix.SpecialLinearGroup.map ι A) := by
  have hle : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 6) K)) ≤
      MonoidHom.eqLocus ((a5LeviBaseChange ι).comp slToA5Levi)
        (slToA5Levi.comp (Matrix.SpecialLinearGroup.map ι)) := by
    rw [← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
      closure_le]
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    refine Subtype.ext (Subtype.ext ?_)
    simp only [MonoidHom.comp_apply, Matrix.TransvectionStruct.toSpecialLinearGroup_mk,
      Matrix.SpecialLinearGroup.map_transvection]
    rw [coe_a5LeviBaseChange]
    change baseChangeGL ι ((slToAdjointE6 K (Matrix.SpecialLinearGroup.transvection hij c) :
        adjointGroup .E6 K) : ModGL .E6 K) =
      ((slToAdjointE6 M (Matrix.SpecialLinearGroup.transvection hij (ι c)) :
        adjointGroup .E6 M) : ModGL .E6 M)
    rw [coe_slToAdjointE6_transvection, coe_slToAdjointE6_transvection, baseChangeGL_pinnedX]
  exact hle (mem_top A)

theorem map_a5LeviBaseChange_eq (ι : K →+* M) :
    (⊤ : Subgroup (a5Levi K)).map (a5LeviBaseChange ι) =
      ((Matrix.SpecialLinearGroup.map ι).range).map slToA5Levi := by
  ext y
  constructor
  · rintro ⟨x, -, rfl⟩
    obtain ⟨A, rfl⟩ := slToA5Levi_surjective x
    exact ⟨Matrix.SpecialLinearGroup.map ι A, ⟨A, rfl⟩, (a5LeviBaseChange_slToA5Levi ι A).symm⟩
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨slToA5Levi A, mem_top _, a5LeviBaseChange_slToA5Levi ι A⟩

theorem map_a5LeviBaseChange_eq_eqLocus {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2]
    (ι : K₀ →+* K) (σ : K →+* K) (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι)
    (hσ : ∀ x : K, σ (σ x) = x) :
    (⊤ : Subgroup (a5Levi K₀)).map (a5LeviBaseChange ι) =
      MonoidHom.eqLocus (a5LeviBaseChange σ) (MonoidHom.id _) := by
  have hσι : σ.comp ι = ι := RingHom.ext fun x => (hfix (ι x)).2 ⟨x, rfl⟩
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, -, rfl⟩
    change a5LeviBaseChange σ (a5LeviBaseChange ι x) = a5LeviBaseChange ι x
    rw [a5LeviBaseChange_comp, hσι]
  · intro y hy
    change a5LeviBaseChange σ y = y at hy
    obtain ⟨A, rfl⟩ := slToA5Levi_surjective y
    rw [a5LeviBaseChange_slToA5Levi] at hy
    set Z := A⁻¹ * Matrix.SpecialLinearGroup.map σ A with hZdef
    have hZker : Z ∈ (slToA5Levi (K := K)).ker := by
      rw [MonoidHom.mem_ker, hZdef, map_mul, map_inv, hy, inv_mul_cancel]
    have hZ : Z ∈ center (Matrix.SpecialLinearGroup (Fin 6) K) := by
      rwa [← ker_slToA5Levi]
    have hA : Matrix.SpecialLinearGroup.map σ A = A * Z := by
      rw [hZdef, mul_inv_cancel_left]
    obtain ⟨B₀, hB₀⟩ := exists_specialLinearGroup_map_eq_of_map_eq ι σ hfix (A * Z⁻¹)
      (map_mul_inv_eq_of_map_eq_mul σ hσ hZ hA)
    refine ⟨slToA5Levi B₀, mem_top _, ?_⟩
    rw [a5LeviBaseChange_slToA5Levi, hB₀, map_mul, map_inv,
      (MonoidHom.mem_ker).1 hZker, inv_one, mul_one]

theorem exists_baseChangeGL_eq_of_mem_rootSpan_a5LeviRoots {K₀ : Type} [Field K₀] [Finite K₀]
    [CharP K₀ 2] (ι : K₀ →+* K) (σ : K →+* K) (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι)
    (hσ : ∀ x : K, σ (σ x) = x) {d : ModGL .E6 K} (hd : d ∈ rootSpan .E6 K a5LeviRoots)
    (hσd : baseChangeGL σ d = d) :
    ∃ d₀ ∈ rootSpan .E6 K₀ a5LeviRoots, baseChangeGL ι d₀ = d := by
  have hdC : d ∈ adjointGroup .E6 K := rootSpan_le_adjointGroup_E6 _ hd
  set d' : a5Levi K := ⟨⟨d, hdC⟩, mem_a5Levi_iff.2 hd⟩ with hd'
  have hfixd : d' ∈ (a5LeviBaseChange σ).eqLocus (MonoidHom.id _) :=
    Subtype.ext (Subtype.ext (by rw [coe_a5LeviBaseChange]; exact hσd))
  rw [← map_a5LeviBaseChange_eq_eqLocus ι σ hfix hσ] at hfixd
  obtain ⟨d₀, -, hd₀⟩ := hfixd
  refine ⟨((d₀ : adjointGroup .E6 K₀) : ModGL .E6 K₀), mem_a5Levi_iff.1 d₀.2, ?_⟩
  rw [← coe_a5LeviBaseChange, hd₀]

theorem slToA5Levi_mem_eqLocus_not_mem_map {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2]
    (ι : K₀ →+* K) (σ : K →+* K) (hσι : σ.comp ι = ι)
    (hcent : ∀ W ∈ center (Matrix.SpecialLinearGroup (Fin 6) K),
      Matrix.SpecialLinearGroup.map σ W = W)
    {A Z : Matrix.SpecialLinearGroup (Fin 6) K}
    (hZ : Z ∈ center (Matrix.SpecialLinearGroup (Fin 6) K)) (hZ1 : Z ≠ 1)
    (hA : Matrix.SpecialLinearGroup.map σ A = A * Z) :
    slToA5Levi A ∈ MonoidHom.eqLocus (a5LeviBaseChange σ) (MonoidHom.id _) ∧
      slToA5Levi A ∉ (⊤ : Subgroup (a5Levi K₀)).map (a5LeviBaseChange ι) := by
  have hZker : Z ∈ (slToA5Levi (K := K)).ker := by rw [ker_slToA5Levi]; exact hZ
  refine ⟨?_, ?_⟩
  · change a5LeviBaseChange σ (slToA5Levi A) = slToA5Levi A
    rw [a5LeviBaseChange_slToA5Levi, hA, map_mul, (MonoidHom.mem_ker).1 hZker, mul_one]
  · rintro ⟨x, -, hx⟩
    obtain ⟨B₀, rfl⟩ := slToA5Levi_surjective x
    rw [a5LeviBaseChange_slToA5Levi] at hx
    have hWker : A⁻¹ * Matrix.SpecialLinearGroup.map ι B₀ ∈ (slToA5Levi (K := K)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hx, inv_mul_cancel]
    have hWc : A⁻¹ * Matrix.SpecialLinearGroup.map ι B₀ ∈
        center (Matrix.SpecialLinearGroup (Fin 6) K) := by
      rwa [← ker_slToA5Levi]
    have hfixB : Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.map ι B₀) =
        Matrix.SpecialLinearGroup.map ι B₀ := by
      rw [specialLinearGroup_map_map, hσι]
    have hAW : Matrix.SpecialLinearGroup.map ι B₀ =
        A * (A⁻¹ * Matrix.SpecialLinearGroup.map ι B₀) := by
      rw [mul_inv_cancel_left]
    rw [hAW, map_mul, hA, hcent _ hWc, mul_assoc] at hfixB
    exact hZ1 (mul_right_cancel ((mul_left_cancel hfixB).trans (one_mul _).symm))

end Naturality

end CFSG.SeitzReduction.E6Pilot
