module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCoresAbstract
import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section ProjMap

variable {n : ℕ} {K F : Type*} [Field K] [Field F]

theorem map_mem_scalars (ι : K →+* F) {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ scalars n K) : SpecialLinearGroup.map ι g ∈ scalars n F := by
  obtain ⟨c, hc, hgc⟩ := mem_scalars.mp hg
  refine mem_scalars.mpr ⟨Units.map ι.toMonoidHom c, ?_, ?_⟩
  · rw [← map_pow, hc, map_one]
  · ext i j
    rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, hgc]
    by_cases hij : i = j
    · simp [scalar_apply, hij]
    · simp [scalar_apply, hij]

theorem mem_scalars_of_map_mem_scalars (hn : 0 < n) (ι : K →+* F)
    {g : SpecialLinearGroup (Fin n) K} (hg : SpecialLinearGroup.map ι g ∈ scalars n F) :
    g ∈ scalars n K := by
  obtain ⟨c, hc, hgc⟩ := mem_scalars.mp hg
  set i₀ : Fin n := ⟨0, hn⟩
  have hent : ∀ i j : Fin n, ι ((g : Matrix (Fin n) (Fin n) K) i j) =
      if i = j then (c : F) else 0 := by
    intro i j
    have := congrFun (congrFun hgc i) j
    rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at this
    rw [this, scalar_apply, diagonal_apply]
  set a := (g : Matrix (Fin n) (Fin n) K) i₀ i₀ with ha
  have hιa : ι a = c := by rw [ha, hent, ite_eq_left rfl]
  have ha0 : a ≠ 0 := fun h => c.ne_zero (by rw [← hιa, h, map_zero])
  have hdiag : ∀ i, (g : Matrix (Fin n) (Fin n) K) i i = a :=
    fun i => ι.injective (by rw [hent, ite_eq_left rfl, hιa])
  have hoff : ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) K) i j = 0 :=
    fun i j hij => ι.injective (by rw [hent, ite_eq_right hij, map_zero])
  refine mem_scalars.mpr ⟨Units.mk0 a ha0, ?_, ?_⟩
  · apply Units.ext
    apply ι.injective
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, hιa, Units.val_one, map_one,
      ← Units.val_pow_eq_pow_val, hc, Units.val_one]
  · ext i j
    rw [Units.val_mk0, scalar_apply, diagonal_apply]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, hdiag]
    · rw [ite_eq_right hij, hoff i j hij]

variable (n) in
@[expose] noncomputable def projMap (ι : K →+* F) : projectiveSL n K →* projectiveSL n F :=
  QuotientGroup.lift (scalars n K) ((proj n F).comp (SpecialLinearGroup.map ι))
    (fun _ hg => proj_eq_one_iff.mpr (map_mem_scalars ι hg))

theorem projMap_proj (ι : K →+* F) (g : SpecialLinearGroup (Fin n) K) :
    projMap n ι (proj n K g) = proj n F (SpecialLinearGroup.map ι g) :=
  rfl

theorem projMap_injective (hn : 0 < n) (ι : K →+* F) : Function.Injective (projMap n ι) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  rw [projMap_proj, proj_eq_one_iff] at hx
  exact proj_eq_one_iff.mpr (mem_scalars_of_map_mem_scalars hn ι hx)

theorem mem_range_projMap (ι : K →+* F) {x : projectiveSL n F} :
    x ∈ (projMap n ι).range ↔ ∃ g : SpecialLinearGroup (Fin n) F,
      (∀ i j, (g : Matrix (Fin n) (Fin n) F) i j ∈ Set.range ι) ∧ proj n F g = x := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨h, rfl⟩ := proj_surjective n K y
    refine ⟨SpecialLinearGroup.map ι h, fun i j => ⟨(h : Matrix (Fin n) (Fin n) K) i j, ?_⟩, rfl⟩
    rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  · rintro ⟨g, hg, rfl⟩
    choose a ha using hg
    have hmap : ι.mapMatrix (Matrix.of a) = (g : Matrix (Fin n) (Fin n) F) := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, ha]
    have hA : (Matrix.of a).det = 1 := by
      apply ι.injective
      rw [map_one, RingHom.map_det, hmap]
      exact g.2
    obtain ⟨h, hh⟩ : ∃ h : SpecialLinearGroup (Fin n) K,
        (h : Matrix (Fin n) (Fin n) K) = Matrix.of a := ⟨⟨Matrix.of a, hA⟩, rfl⟩
    refine ⟨proj n K h, ?_⟩
    rw [projMap_proj]
    congr 1
    exact Subtype.ext (by rw [SpecialLinearGroup.map_apply_coe, hh]; exact hmap)

theorem fieldAut_projMap (ι : K →+* F) {σ : F ≃+* F} (hσ : ∀ c, σ (ι c) = ι c)
    (x : projectiveSL n K) : fieldAut n F σ (projMap n ι x) = projMap n ι x := by
  obtain ⟨h, rfl⟩ := proj_surjective n K x
  rw [projMap_proj, fieldAut_proj]
  congr 1
  apply Subtype.ext
  ext i j
  simp [SpecialLinearGroup.map_apply_coe, hσ]

end ProjMap

section FixedPoints

variable {n : ℕ} {K F : Type*} [Field K] [Field F]

theorem mem_fixedSubgroup_iff_apply_eq {X : Type*} [Group X] {α : MulAut X} {x : X} :
    x ∈ fixedSubgroup α ↔ α x = x :=
  Iff.rfl

theorem commutator_projectiveSL_eq_top (hn : 3 ≤ n) :
    ⁅(⊤ : Subgroup (projectiveSL n K)), (⊤ : Subgroup (projectiveSL n K))⁆ = ⊤ := by
  have hSL := CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (K := K) hn
  rw [commutator_def] at hSL
  rw [← MonoidHom.range_eq_top.mpr (proj_surjective n K), MonoidHom.range_eq_map,
    ← map_commutator, hSL]

theorem commutator_range_projMap (hn : 3 ≤ n) (ι : K →+* F) :
    ⁅(projMap n ι).range, (projMap n ι).range⁆ = (projMap n ι).range := by
  rw [MonoidHom.range_eq_map, ← map_commutator, commutator_projectiveSL_eq_top hn]

theorem exists_mem_center_map_eq_mul_of_fieldAut {σ : F ≃+* F}
    {g : SpecialLinearGroup (Fin n) F} (hg : fieldAut n F σ (proj n F g) = proj n F g) :
    ∃ z ∈ center (SpecialLinearGroup (Fin n) F),
      SpecialLinearGroup.map σ.toRingHom g = z * g := by
  rw [fieldAut_proj, proj_eq_proj_iff] at hg
  have hz := Subgroup.inv_mem _ (scalars_le_center n F hg)
  refine ⟨_, hz, ?_⟩
  rw [← mem_center_iff.mp hz g]
  group

theorem commutator_fixedSubgroup_fieldAut_le (ι : K →+* F) {σ : F ≃+* F}
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    ⁅fixedSubgroup (fieldAut n F σ), fixedSubgroup (fieldAut n F σ)⁆ ≤ (projMap n ι).range := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨g, rfl⟩ := proj_surjective n F x
  obtain ⟨h, rfl⟩ := proj_surjective n F y
  obtain ⟨z, hz, hgz⟩ :=
    exists_mem_center_map_eq_mul_of_fieldAut (mem_fixedSubgroup_iff_apply_eq.mp hx)
  obtain ⟨w, hw, hhw⟩ :=
    exists_mem_center_map_eq_mul_of_fieldAut (mem_fixedSubgroup_iff_apply_eq.mp hy)
  have hc : SpecialLinearGroup.map σ.toRingHom ⁅g, h⁆ = ⁅g, h⁆ := by
    rw [map_commutatorElement, hgz, hhw]
    exact CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hz hw g h
  rw [← map_commutatorElement]
  refine (mem_range_projMap ι).mpr ⟨⁅g, h⁆, fun i j => (hfix _).mp ?_, rfl⟩
  have := congrFun (congrFun (congrArg Subtype.val hc) i) j
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at this
  exact this

theorem perfectCore_fixedSubgroup_fieldAut [Finite F] (hn : 3 ≤ n) (ι : K →+* F)
    {σ : F ≃+* F} (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    perfectCore (fixedSubgroup (fieldAut n F σ)) = (projMap n ι).range := by
  have hle : (projMap n ι).range ≤ fixedSubgroup (fieldAut n F σ) := by
    rintro _ ⟨x, rfl⟩
    exact fieldAut_projMap ι (fun c => (hfix _).mpr ⟨c, rfl⟩) x
  rw [perfectCore_eq_of_le_of_commutator_le hle (commutator_fixedSubgroup_fieldAut_le ι hfix),
    CFSG.Quasithin.perfectCore_eq_self_of_perfect (commutator_range_projMap hn ι)]

end FixedPoints

section Extension

variable {n : ℕ} {K F : Type*} [Field K] [Field F]

theorem entrywise_slConjugation (ι : K →+* F) (A : GL (Fin n) K)
    (g : SpecialLinearGroup (Fin n) K) :
    SpecialLinearGroup.map ι (CatalogueBHigherLinearAction.slConjugation n K A g) =
      CatalogueBHigherLinearAction.slConjugation n F (Matrix.GeneralLinearGroup.map ι A)
        (SpecialLinearGroup.map ι g) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, CatalogueBHigherLinearAction.slConjugation_matrix,
    CatalogueBHigherLinearAction.slConjugation_matrix, ← map_inv, RingHom.mapMatrix_apply,
    Matrix.map_mul, Matrix.map_mul, SpecialLinearGroup.map_apply_coe]
  rfl

theorem entrywise_slFieldAut (ι : K →+* F) {ρ : K ≃+* K} {ρ' : F ≃+* F}
    (h : ∀ c, ρ' (ι c) = ι (ρ c)) (g : SpecialLinearGroup (Fin n) K) :
    SpecialLinearGroup.map ι (CatalogueBHigherLinearField.slFieldAut (Fin n) K ρ g) =
      CatalogueBHigherLinearField.slFieldAut (Fin n) F ρ' (SpecialLinearGroup.map ι g) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe]
  change ι (CatalogueBHigherLinearField.slFieldEquiv (Fin n) ρ g i j) =
    CatalogueBHigherLinearField.slFieldEquiv (Fin n) ρ' (SpecialLinearGroup.map ι g) i j
  rw [CatalogueBHigherLinearField.slFieldEquiv_entry,
    CatalogueBHigherLinearField.slFieldEquiv_entry, SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, h]

theorem entrywise_slGraphAut (ι : K →+* F) (g : SpecialLinearGroup (Fin n) K) :
    SpecialLinearGroup.map ι (CatalogueBGraphForm.slGraphAut n K g) =
      CatalogueBGraphForm.slGraphAut n F (SpecialLinearGroup.map ι g) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, CatalogueBGraphForm.slGraphAut_matrix,
    CatalogueBGraphForm.slGraphAut_matrix, ← map_inv, SpecialLinearGroup.map_apply_coe]
  rfl

theorem std_eq_descendAut (A : GL (Fin n) K) (ρ : K ≃+* K) (ε : ℕ) :
    conjAut n K A * fieldAut n K ρ * dualAut n K ^ ε =
      descendAut n K (CatalogueBHigherLinearAction.slConjugation n K A *
        CatalogueBHigherLinearField.slFieldAut (Fin n) K ρ *
          CatalogueBGraphForm.slGraphAut n K ^ ε) := by
  simp only [LinearFlag.conjAut, LinearFlag.fieldAut, LinearFlag.dualAut, map_mul, map_pow,
    MonoidHom.comp_apply]

theorem projMap_std_apply (ι : K →+* F) (A : GL (Fin n) K) {ρ : K ≃+* K} {ρ' : F ≃+* F}
    (h : ∀ c, ρ' (ι c) = ι (ρ c)) {ε : ℕ} (hε : ε ≤ 1) (x : projectiveSL n K) :
    (conjAut n F (Matrix.GeneralLinearGroup.map ι A) * fieldAut n F ρ' * dualAut n F ^ ε)
        (projMap n ι x) =
      projMap n ι ((conjAut n K A * fieldAut n K ρ * dualAut n K ^ ε) x) := by
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  rw [std_eq_descendAut, std_eq_descendAut, projMap_proj, descendAut_proj, descendAut_proj,
    projMap_proj]
  congr 1
  interval_cases ε
  · simp only [pow_zero, mul_one, MulAut.mul_apply]
    rw [entrywise_slConjugation, entrywise_slFieldAut ι h]
  · simp only [pow_one, MulAut.mul_apply]
    rw [entrywise_slConjugation, entrywise_slFieldAut ι h, entrywise_slGraphAut]

theorem exists_natCard_eq_two_pow_of_charP (L : Type*) [Field L] [Finite L] [CharP L 2] :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card L = 2 ^ f := by
  have := Fintype.ofFinite L
  obtain ⟨m, -, hm⟩ := FiniteField.card L 2
  exact ⟨m, m.pos, by rw [Nat.card_eq_fintype_card, hm]⟩

theorem exists_frobenius_and_pow_eq (L : Type*) [Field L] [Finite L] [CharP L 2] :
    (∃ φ : L ≃+* L, ∀ c, φ c = c ^ 2) ∧ ∀ ρ : L ≃+* L, ∃ m : ℕ, ∀ c, ρ c = c ^ 2 ^ m := by
  obtain ⟨f, hf, hL⟩ := exists_natCard_eq_two_pow_of_charP L
  obtain ⟨φ, hφ, hord, hzp, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hL
  refine ⟨⟨φ, hφ⟩, fun ρ => ?_⟩
  have hfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; omega)
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp
    (hfin.mem_powers_iff_mem_zpowers.mpr (hzp ▸ Subgroup.mem_top ρ))
  exact ⟨m, fun c => by rw [← hm, LinearFlag.pow_apply_of_sq hφ]⟩

theorem exists_mulAut_projMap_comm [Finite K] [CharP K 2] [Finite F] [CharP F 2] (hn : 3 ≤ n)
    (ι : K →+* F) {σ : F ≃+* F} (hσ : ∀ c, σ (ι c) = ι c) (δ : MulAut (projectiveSL n K)) :
    ∃ δ' : MulAut (projectiveSL n F), (∀ x, δ' (projMap n ι x) = projMap n ι (δ x)) ∧
      Commute δ' (fieldAut n F σ) := by
  obtain ⟨A, ρ, ε, hε, hδ⟩ := (automorphism_generation (K := K) hn).2 δ
  obtain ⟨m, hm⟩ := (exists_frobenius_and_pow_eq K).2 ρ
  obtain ⟨⟨φ, hφ⟩, -⟩ := exists_frobenius_and_pow_eq F
  have hρ' : ∀ c, (φ ^ m) c = c ^ 2 ^ m := LinearFlag.pow_apply_of_sq hφ m
  have hρι : ∀ c, (φ ^ m) (ι c) = ι (ρ c) := fun c => by rw [hρ', hm, map_pow]
  refine ⟨conjAut n F (Matrix.GeneralLinearGroup.map ι A) * fieldAut n F (φ ^ m) *
    dualAut n F ^ ε, fun x => by rw [hδ]; exact projMap_std_apply ι A hρι hε x, ?_⟩
  have htrans := standard_automorphism_transport (K := F) (n := n)
  have h1 : Commute (fieldAut n F σ) (conjAut n F (Matrix.GeneralLinearGroup.map ι A)) := by
    have hX : Matrix.GeneralLinearGroup.map (σ : F →+* F)
        (Matrix.GeneralLinearGroup.map ι A) = Matrix.GeneralLinearGroup.map ι A := by
      ext i j
      simp [hσ]
    have h := htrans.2.2.1 σ (Matrix.GeneralLinearGroup.map ι A)
    rw [hX, mul_inv_eq_iff_eq_mul] at h
    exact h
  have h2 : Commute (fieldAut n F σ) (fieldAut n F (φ ^ m)) := by
    change fieldAut n F σ * fieldAut n F (φ ^ m) = fieldAut n F (φ ^ m) * fieldAut n F σ
    rw [← map_mul, ← map_mul]
    congr 1
    ext c
    rw [RingAut.mul_apply, RingAut.mul_apply, hρ', hρ', map_pow]
  have h3 : Commute (fieldAut n F σ) (dualAut n F ^ ε) := by
    refine Commute.pow_right ?_ ε
    have hδδ : dualAut n F * dualAut n F = 1 := htrans.2.2.2.1
    have h := htrans.2.2.2.2.2.1 σ
    change fieldAut n F σ * dualAut n F = dualAut n F * fieldAut n F σ
    calc fieldAut n F σ * dualAut n F
        = dualAut n F * fieldAut n F σ * dualAut n F * dualAut n F := by rw [h]
      _ = dualAut n F * fieldAut n F σ * (dualAut n F * dualAut n F) := by
          rw [mul_assoc (dualAut n F * fieldAut n F σ)]
      _ = dualAut n F * fieldAut n F σ := by rw [hδδ, mul_one]
  exact ((h1.mul_right h2).mul_right h3).symm

end Extension

end CFSG.SeitzReduction.LinearPilot
