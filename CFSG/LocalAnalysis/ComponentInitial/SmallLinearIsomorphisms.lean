module

public import CFSG.LocalAnalysis.ComponentInitial.CertSmallLinear
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalModels

theorem PSL2_four_alternating_five_model (X : Type) [Group X]
    (hX : CFSG.Blueprint.LieModel X .PSL 2 2 2) : Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  rcases hX with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hc
    obtain ⟨e5⟩ := nonempty_statedLinearModel_equiv_alternating_five K
      (Or.inl (by rw [hK]; norm_num))
    exact ⟨e.trans e5⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem bijective_of_card_range {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hA : Nat.card f.range = Nat.card A) (hB : Nat.card f.range = Nat.card B) :
    Function.Bijective f := by
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hA] at h1
    refine Subgroup.eq_bot_of_card_eq _ ?_
    have hpos : 0 < Nat.card A := Nat.card_pos
    nlinarith
  · rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ hB

theorem card_GL_three_zmod_two : Nat.card (GL (Fin 3) (ZMod 2)) = 168 :=
  CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.card_GL3

theorem card_PSL_two_zmod_seven :
    Nat.card (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) = 168 := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hSL : Nat.card (SpecialLinearGroup (Fin 2) (ZMod 7)) = 336 := by
    rw [Matrix.card_SL_field, ZMod.card, Fin.prod_univ_two]
    norm_num
  have hZ : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod 7))) = 2 := by
    rw [← SetLike.coe_sort_coe, (small_linear_paired_generator_certificate).1, Nat.card_eq_card_toFinset]
    decide
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod 7)))
  rw [hSL, hZ] at h
  change Nat.card (SpecialLinearGroup (Fin 2) (ZMod 7) ⧸
    Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod 7))) = 168
  omega

theorem nonempty_GL_three_two_equiv_PSL_two_seven :
    Nonempty (GL (Fin 3) (ZMod 2) ≃* ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) := by
  obtain ⟨-, hP, hfst, hsnd, -⟩ := small_linear_paired_generator_certificate
  set P := Subgroup.closure {smallLinearGenA, smallLinearGenB} with hPdef
  set f := (MonoidHom.fst (GL (Fin 3) (ZMod 2)) (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7))).comp
    P.subtype with hf
  set g := (MonoidHom.snd (GL (Fin 3) (ZMod 2)) (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7))).comp
    P.subtype with hg
  have hfr : f.range = P.map (MonoidHom.fst _ _) := by rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hgr : g.range = P.map (MonoidHom.snd _ _) := by rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
  have hfb : Function.Bijective f := bijective_of_card_range f (by rw [hfr, hfst, hP])
    (by rw [hfr, hfst, card_GL_three_zmod_two])
  have hgb : Function.Bijective g := bijective_of_card_range g (by rw [hgr, hsnd, hP])
    (by rw [hgr, hsnd, card_PSL_two_zmod_seven])
  exact ⟨(MulEquiv.ofBijective f hfb).symm.trans (MulEquiv.ofBijective g hgb)⟩

theorem center_SL_three_zmod_two_eq_bot :
    Subgroup.center (SpecialLinearGroup (Fin 3) (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Subgroup.mem_bot]
  have key : ∀ s : ZMod 2, s ^ 3 = 1 → s = 1 := by decide
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := key r hr
  rw [hr1, map_one] at hA'
  exact Subtype.ext hA'.symm

theorem bijective_toGL_three_zmod_two :
    Function.Bijective (Matrix.SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 3) (ZMod 2) →*
      GL (Fin 3) (ZMod 2)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL_injective, fun g => ?_⟩
  have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
    have hu : IsUnit (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det := g.isUnit.map Matrix.detMonoidHom
    obtain ⟨u, hu⟩ := hu
    rw [← hu]
    have : u = 1 := Subsingleton.elim _ _
    rw [this, Units.val_one]
  exact ⟨⟨g, hdet⟩, Units.ext rfl⟩

theorem PSL3_two_PSL2_seven_paired_isomorphism (X : Type) [Group X]
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 1) : CFSG.Blueprint.LieModel X .PSL 2 7 1 := by
  have h7 : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  rcases hX with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hc
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = Fintype.card (ZMod 2) := by
      rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one]
    let φ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard
    let e₁ : StatedProj (StatedSL 3 K) ≃* ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
      (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
        (projectiveSpecialLinearFieldEquiv φ (Fin 3))
    let e₂ : ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃* SpecialLinearGroup (Fin 3) (ZMod 2) :=
      (QuotientGroup.quotientMulEquivOfEq center_SL_three_zmod_two_eq_bot).trans
        QuotientGroup.quotientBot
    let e₃ : SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
      MulEquiv.ofBijective _ bijective_toGL_three_zmod_two
    obtain ⟨e₄⟩ := nonempty_GL_three_two_equiv_PSL_two_seven
    have e₅ : ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) ≃* StatedProj (StatedSL 2 (ZMod 7)) :=
      projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod 7)
    have hadm : StatedLieAdmissible .PSL 2 7 1 :=
      ⟨Nat.prime_seven, le_rfl, le_rfl, by decide, by decide⟩
    have hmem : (StatedLieTag.PSL) ∈ CFSG.Blueprint.classicalTags := by decide
    exact Or.inl ⟨hmem, hadm, ZMod 7, inferInstance, inferInstance,
      by rw [Nat.card_zmod, pow_one], ⟨((((e.trans e₁).trans e₂).trans e₃).trans e₄).trans e₅⟩⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.LocalAnalysis.ComponentInitial
