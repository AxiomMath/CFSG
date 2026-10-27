module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZLevi
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviKer

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.Timmesfeld.LieEmbed CFSG.LieType.Chevalley

section Block

variable {K : Type} [Field K]

@[expose] def zDiagIdx : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv

@[expose] def zDiagMat (A : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.reindexAlgEquiv K K zDiagIdx (Matrix.fromBlocks A 0 0 A)

theorem zDiagMat_apply (A : Matrix (Fin 3) (Fin 3) K) (p q : Fin 3 ⊕ Fin 3) :
    zDiagMat A (zDiagIdx p) (zDiagIdx q) = Matrix.fromBlocks A 0 0 A p q := by
  simp [zDiagMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]

omit [Field K] in
theorem ext_zDiagIdx {R : Type*} {M N : Matrix (Fin 6) (Fin 6) R}
    (h : ∀ p q, M (zDiagIdx p) (zDiagIdx q) = N (zDiagIdx p) (zDiagIdx q)) : M = N := by
  ext a b
  obtain ⟨p, rfl⟩ := zDiagIdx.surjective a
  obtain ⟨q, rfl⟩ := zDiagIdx.surjective b
  exact h p q

theorem zDiagMat_mul (A B : Matrix (Fin 3) (Fin 3) K) :
    zDiagMat (A * B) = zDiagMat A * zDiagMat B := by
  rw [zDiagMat, zDiagMat, zDiagMat, ← map_mul, Matrix.fromBlocks_multiply]
  simp

theorem zDiagMat_one : zDiagMat (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [zDiagMat, Matrix.fromBlocks_one, map_one]

theorem zDiagMat_add (A B : Matrix (Fin 3) (Fin 3) K) :
    zDiagMat (A + B) = zDiagMat A + zDiagMat B := by
  rw [zDiagMat, zDiagMat, zDiagMat, ← map_add, Matrix.fromBlocks_add]
  simp

theorem det_zDiagMat (A : Matrix (Fin 3) (Fin 3) K) : (zDiagMat A).det = A.det * A.det := by
  rw [zDiagMat, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁]

theorem zDiagMat_single (i j : Fin 3) (c : K) :
    zDiagMat (Matrix.single i j c) =
      Matrix.single (zDiagIdx (Sum.inl i)) (zDiagIdx (Sum.inl j)) c +
        Matrix.single (zDiagIdx (Sum.inr i)) (zDiagIdx (Sum.inr j)) c := by
  refine ext_zDiagIdx fun p q => ?_
  rw [zDiagMat_apply, Matrix.add_apply]
  rcases p with x | x <;> rcases q with y | y <;> simp [Matrix.single_apply, zDiagIdx.injective.eq_iff]

theorem zDiagMat_transvection (i j : Fin 3) (c : K) :
    zDiagMat (Matrix.transvection i j c) =
      Matrix.transvection (zDiagIdx (Sum.inl i)) (zDiagIdx (Sum.inl j)) c *
        Matrix.transvection (zDiagIdx (Sum.inr i)) (zDiagIdx (Sum.inr j)) c := by
  have hne : zDiagIdx (Sum.inl j) ≠ zDiagIdx (Sum.inr i) := zDiagIdx.injective.ne Sum.inl_ne_inr
  have h0 : Matrix.single (zDiagIdx (Sum.inl i)) (zDiagIdx (Sum.inl j)) c *
      Matrix.single (zDiagIdx (Sum.inr i)) (zDiagIdx (Sum.inr j)) c = 0 :=
    Matrix.single_mul_single_of_ne (h := hne) ..
  rw [Matrix.transvection, zDiagMat_add, zDiagMat_one, zDiagMat_single, Matrix.transvection,
    Matrix.transvection, add_mul, one_mul, mul_add, mul_one, h0, add_zero]
  abel

variable (K) in
@[expose] def zDiagHom : Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.SpecialLinearGroup (Fin 6) K
    where
  toFun A := ⟨zDiagMat (A : Matrix (Fin 3) (Fin 3) K), by rw [det_zDiagMat, A.2, mul_one]⟩
  map_one' := Subtype.ext (by
    change zDiagMat ((1 : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, zDiagMat_one])
  map_mul' A B := Subtype.ext (by
    change zDiagMat ((A * B : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      zDiagMat (A : Matrix (Fin 3) (Fin 3) K) * zDiagMat (B : Matrix (Fin 3) (Fin 3) K)
    rw [Matrix.SpecialLinearGroup.coe_mul, zDiagMat_mul])

theorem coe_zDiagHom (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((zDiagHom K A : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      zDiagMat (A : Matrix (Fin 3) (Fin 3) K) :=
  rfl

theorem zDiagHom_transvection {i j : Fin 3} (hij : i ≠ j) (c : K) :
    zDiagHom K (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection (zDiagIdx.injective.ne (Sum.inl_injective.ne hij)) c *
        Matrix.SpecialLinearGroup.transvection (zDiagIdx.injective.ne (Sum.inr_injective.ne hij)) c :=
  Subtype.ext (zDiagMat_transvection i j c)

theorem zDiagHom_mem_center {A : Matrix.SpecialLinearGroup (Fin 3) K}
    (hA : A ∈ center (Matrix.SpecialLinearGroup (Fin 3) K)) :
    zDiagHom K A ∈ center (Matrix.SpecialLinearGroup (Fin 6) K) := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  refine Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨r, ?_, ?_⟩
  · rw [Fintype.card_fin, show 6 = 3 * 2 by rfl, pow_mul, hr, one_pow]
  · rw [coe_zDiagHom, ← hrA]
    refine ext_zDiagIdx fun p q => ?_
    rw [zDiagMat_apply]
    rcases p with x | x <;> rcases q with y | y <;>
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, zDiagIdx.injective.eq_iff]

end Block

theorem zSL3_pair_check :
    (∀ i j : Fin 3, i ≠ j →
      (a5Root (zDiagIdx (Sum.inl i)) (zDiagIdx (Sum.inl j)), a5Root (zDiagIdx (Sum.inr i)) (zDiagIdx (Sum.inr j)))
        ∈ zSPairs) ∧
    ∀ p ∈ zSPairs, ∃ i j : Fin 3, i ≠ j ∧
      (a5Root (zDiagIdx (Sum.inl i)) (zDiagIdx (Sum.inl j)),
        a5Root (zDiagIdx (Sum.inr i)) (zDiagIdx (Sum.inr j))) = p := by
  decide +kernel

theorem zSL3_root01_check :
    a5Root (zDiagIdx (Sum.inl (0 : Fin 3))) (zDiagIdx (Sum.inl (1 : Fin 3))) ≠
        a5Root (zDiagIdx (Sum.inr (0 : Fin 3))) (zDiagIdx (Sum.inr (1 : Fin 3))) ∧
      0 < height (a5Root (zDiagIdx (Sum.inl (0 : Fin 3))) (zDiagIdx (Sum.inl (1 : Fin 3)))) ∧
      0 < height (a5Root (zDiagIdx (Sum.inr (0 : Fin 3))) (zDiagIdx (Sum.inr (1 : Fin 3)))) := by
  decide +kernel

section Le

variable {K : Type} [Field K]

theorem zS_le_adjointGroup : zS K ≤ adjointGroup .E6 K :=
  zS_le_parabolicLevi.trans (parabolicLevi_le_adjointGroup .E6 K zNodes)

end Le

section Hom

variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def zSL3Hom : Matrix.SpecialLinearGroup (Fin 3) K →* adjointGroup .E6 K :=
  (slToAdjointE6 K).comp (zDiagHom K)

variable {K}

theorem coe_zSL3Hom_transvection {i j : Fin 3} (hij : i ≠ j) (c : K) :
    ((zSL3Hom K (Matrix.SpecialLinearGroup.transvection hij c) : adjointGroup .E6 K) :
        ModGL .E6 K) =
      pinnedX .E6 K (a5Root (zDiagIdx (Sum.inl i)) (zDiagIdx (Sum.inl j))) c *
        pinnedX .E6 K (a5Root (zDiagIdx (Sum.inr i)) (zDiagIdx (Sum.inr j))) c := by
  rw [zSL3Hom, MonoidHom.comp_apply, zDiagHom_transvection, map_mul, Subgroup.coe_mul,
    coe_slToAdjointE6_transvection, coe_slToAdjointE6_transvection]

theorem map_range_zSL3Hom : (zSL3Hom K).range.map (adjointGroup .E6 K).subtype = zS K := by
  rw [← MonoidHom.range_comp, MonoidHom.range_eq_map,
    ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    MonoidHom.map_closure, zS]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨⟨i, j, hij, c⟩, rfl⟩, rfl⟩
    refine ⟨_, zSL3_pair_check.1 i j hij, c, ?_⟩
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk, MonoidHom.comp_apply, coe_subtype,
      coe_zSL3Hom_transvection]
  · rintro ⟨p, hp, t, rfl⟩
    obtain ⟨i, j, hij, hpij⟩ := zSL3_pair_check.2 p hp
    refine ⟨_, ⟨⟨i, j, hij, t⟩, rfl⟩, ?_⟩
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk, MonoidHom.comp_apply, coe_subtype,
      coe_zSL3Hom_transvection, ← hpij]

theorem zSL3Hom_transvection_ne_one :
    zSL3Hom K (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1) ≠ 1 := by
  intro h
  have h' := congrArg (fun g : adjointGroup .E6 K => (g : ModGL .E6 K)) h
  simp only [coe_zSL3Hom_transvection, OneMemClass.coe_one] at h'
  obtain ⟨hab, ha, hb⟩ := zSL3_root01_check
  have hra : IsRoot .E6 (a5Root (zDiagIdx (Sum.inl (0 : Fin 3))) (zDiagIdx (Sum.inl (1 : Fin 3)))) :=
    isRoot_a5Root (zDiagIdx.injective.ne (Sum.inl_injective.ne (by decide)))
  have hrb : IsRoot .E6 (a5Root (zDiagIdx (Sum.inr (0 : Fin 3))) (zDiagIdx (Sum.inr (1 : Fin 3)))) :=
    isRoot_a5Root (zDiagIdx.injective.ne (Sum.inr_injective.ne (by decide)))
  have hnd : [a5Root (zDiagIdx (Sum.inl (0 : Fin 3))) (zDiagIdx (Sum.inl (1 : Fin 3))),
      a5Root (zDiagIdx (Sum.inr (0 : Fin 3))) (zDiagIdx (Sum.inr (1 : Fin 3)))].Nodup := by
    simp [hab]
  have hinj := pinnedX_list_prod_injective (R := K) _ hnd
    (fun β hβ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hβ
      rcases hβ with rfl | rfl
      · exact ⟨hra, ha⟩
      · exact ⟨hrb, hb⟩)
    (fun _ => (1 : K)) (fun _ => (0 : K)) (by simpa [pinnedX_zero] using h')
  exact one_ne_zero (hinj _ List.mem_cons_self)

theorem ker_zSL3Hom : (zSL3Hom K).ker = center (Matrix.SpecialLinearGroup (Fin 3) K) := by
  refine le_antisymm (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K (by norm_num))
    ⟨_, zSL3Hom_transvection_ne_one⟩) fun A hA => ?_
  rw [zSL3Hom, MonoidHom.mem_ker, MonoidHom.comp_apply]
  exact center_le_ker_slToAdjointE6 (zDiagHom_mem_center hA)

@[expose] noncomputable def zSL3HomGL : Matrix.SpecialLinearGroup (Fin 3) K →* ModGL .E6 K :=
  (adjointGroup .E6 K).subtype.comp (zSL3Hom K)

theorem ker_zSL3HomGL : (zSL3HomGL (K := K)).ker = center (Matrix.SpecialLinearGroup (Fin 3) K) := by
  rw [← ker_zSL3Hom]
  ext A
  simp only [zSL3HomGL, MonoidHom.mem_ker, MonoidHom.comp_apply, coe_subtype,
    OneMemClass.coe_eq_one]

theorem range_zSL3HomGL : (zSL3HomGL (K := K)).range = zS K := by
  rw [zSL3HomGL, MonoidHom.range_comp, map_range_zSL3Hom]

variable (K) in
@[expose] noncomputable def zSEquiv : Matrix.ProjectiveSpecialLinearGroup (Fin 3) K ≃* ↥(zS K) :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_zSL3HomGL (K := K)).symm).trans
    (QuotientGroup.quotientKerEquivRange (zSL3HomGL (K := K)))).trans
    (MulEquiv.subgroupCongr range_zSL3HomGL)

@[expose] noncomputable def zSL3ToZS : Matrix.SpecialLinearGroup (Fin 3) K →* ↥(zS K) :=
  (zSL3HomGL (K := K)).codRestrict (zS K) fun A => by
    rw [← range_zSL3HomGL (K := K)]
    exact ⟨A, rfl⟩

theorem zSL3ToZS_surjective : Function.Surjective (zSL3ToZS (K := K)) := by
  rintro ⟨g, hg⟩
  rw [← range_zSL3HomGL] at hg
  obtain ⟨A, rfl⟩ := hg
  exact ⟨A, rfl⟩

theorem ker_zSL3ToZS : (zSL3ToZS (K := K)).ker = center (Matrix.SpecialLinearGroup (Fin 3) K) := by
  rw [← ker_zSL3HomGL]
  ext A
  simp only [zSL3ToZS, MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem isSimpleGroup_zS : IsSimpleGroup (zS K) := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 3 (by norm_num) (.inl (by norm_num))
      (.inl (by norm_num))
  exact (zSEquiv K).symm.isSimpleGroup

theorem isQuasisimple_zS : CFSG.IsQuasisimple (zS K) := by
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective
    (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K (by norm_num))
    zSL3ToZS_surjective
    ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1, fun h =>
      zSL3Hom_transvection_ne_one (K := K) (Subtype.ext (congrArg (fun g : zS K => (g : ModGL .E6 K)) h))⟩

theorem center_zS_eq_bot : center (zS K) = ⊥ := by
  rw [CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple
    (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K (by norm_num))
    zSL3ToZS_surjective ker_zSL3ToZS.le, ← ker_zSL3ToZS, eq_bot_iff]
  rintro _ ⟨A, hA, rfl⟩
  exact hA

theorem commutator_zS_eq : ⁅zS K, zS K⁆ = zS K := by
  rw [← Subgroup.map_subtype_commutator, (isQuasisimple_zS (K := K)).1.commutator_eq_top,
    ← MonoidHom.range_eq_map, range_subtype]

end Hom

section Model

variable {K : Type} [Field K] {f : ℕ}

theorem lieModel_zS (hK : Nat.card K = 2 ^ f) :
    CFSG.Blueprint.LieModel (zS K) .PSL 3 2 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hf := F4Pilot.one_le_of_natCard_eq_two_pow hK
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL (2 + 1) 2 f :=
    ⟨Nat.prime_two, hf, by norm_num, by simp, by simp⟩
  have hmodel :
      CFSG.Blueprint.LieModel (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) .PSL 3 2 f :=
    Or.inl ⟨by decide,
      CFSG.LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient 2 K hadm hK⟩
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (zSEquiv K) hmodel

end Model

end CFSG.SeitzReduction.E6Pilot
