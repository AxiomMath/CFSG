module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.ComponentClassification.CatLeaf CFSG.RankThree.PartOne.Sec66T
open CFSG.Open (StatedLieAdmissible StatedSL StatedSU StatedProj StatedScalars)

section Models

theorem lieModel_centerQuotient_of_equiv_SL {G : Type} [Group G] {m : ℕ} {E : Type} [Field E]
    [Finite E] {p f : ℕ} (hadm : StatedLieAdmissible .PSL m p f) (hE : Nat.card E = p ^ f)
    (e : G ≃* Matrix.SpecialLinearGroup (Fin m) E) :
    CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) .PSL m p f := by
  refine (lieModel_classical_iff (by decide)).mpr ⟨hadm, E, inferInstance, inferInstance, hE, ?_⟩
  exact ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m E)⟩

theorem lieModel_centerQuotient_of_equiv_SU {G : Type} [Group G] {m : ℕ} {E : Type} [Field E]
    {ℓ f : ℕ} (hE : UnitaryFieldData ℓ f E) (hq : 5 ≤ ℓ ^ f) (hm : 3 ≤ m)
    (e : G ≃* ↥(StatedSU m (ℓ ^ f) E)) :
    CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) .PSU m ℓ f := by
  haveI := hE.finite
  have hadm : StatedLieAdmissible .PSU m ℓ f :=
    ⟨hE.prime, hE.one_le, hm, fun hc => by have := congrArg Prod.snd hc; simp only at this; omega⟩
  refine (lieModel_classical_iff (by decide)).mpr ⟨hadm, E, inferInstance, inferInstance,
    hE.card_eq_sq, ?_⟩
  have hcen := (CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.isPerfect_and_center_unitarySU
    hE hq hm).2
  exact ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
    (QuotientGroup.quotientMulEquivOfEq (hcen.trans (unitaryScalars_eq hE (by omega))))⟩

end Models

section Block

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K}
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

theorem specialBlock_eq_kerImage {a : K[X]} {Ω : Type*} [Group Ω]
    (φ : orbitFactor B x a ≃* Ω) (ι : Ω →* blockGL (x : Module.End K V) a)
    (D : Ω →* (AdjoinRoot a)ˣ) (hD : ∀ w, D w = blockGLDet (x : Module.End K V) a (ι w))
    (hcompat : ∀ s : orbitFactor B x a,
      ι (φ s) = blockRestrict x a ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩) :
    specialBlock B x a = kerImage (orbitFactor B x a) φ D := by
  ext g
  rw [mem_specialBlock, mem_kerImage]
  constructor
  · rintro ⟨hs, hg, h⟩
    refine ⟨hs, ?_⟩
    rw [hD, hcompat ⟨g, hs⟩]
    exact h
  · rintro ⟨hs, h⟩
    refine ⟨hs, orbitFactor_le_gl_centralizer hs, ?_⟩
    rw [hD, hcompat ⟨g, hs⟩] at h
    exact h

theorem nonempty_specialBlock_mulEquiv_SL {a : primaryFactors (x : Module.End K V)}
    (hP : PairedPrimaryBlock hK B x a) :
    Nonempty (↥(specialBlock B x (a : K[X])) ≃*
      Matrix.SpecialLinearGroup (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
        (AdjoinRoot (a : K[X]))) := by
  obtain ⟨φ, hφ, -⟩ := exists_pairedFactor hP
  have hspec := specialBlock_eq_kerImage φ (MonoidHom.id _)
    (blockGLDet (x : Module.End K V) (a : K[X])) (fun _ => rfl)
    (fun s => blockGL_ext fun v hv => hφ s v hv)
  obtain ⟨e1⟩ := nonempty_kerImage_mulEquiv (orbitFactor B x (a : K[X])) φ
    (blockGLDet (x : Module.End K V) (a : K[X]))
  obtain ⟨e2⟩ := nonempty_specialLinearGroup_mulEquiv_ker_det (E := AdjoinRoot (a : K[X]))
    (W := primaryComponent (x : Module.End K V) (a : K[X]))
  exact ⟨((MulEquiv.subgroupCongr hspec).trans e1).trans e2.symm⟩

theorem nonempty_specialBlock_mulEquiv_sesqSU {a : primaryFactors (x : Module.End K V)}
    (hself : dualPoly hK.bar (a : K[X]) = a) (hS : SelfDualPrimaryBlock hK B x a) :
    ∃ (hE : UnitaryFieldData ℓ (f * (a : K[X]).natDegree) (AdjoinRoot (a : K[X])))
      (Hf : primaryComponent (x : Module.End K V) (a : K[X]) →ₛₗ[hE.bar]
        primaryComponent (x : Module.End K V) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])]
          AdjoinRoot (a : K[X])),
      Hf.IsSymm ∧ Hf.SeparatingLeft ∧
        Nonempty (↥(specialBlock B x (a : K[X])) ≃* ↥(sesqSpecialUnitaryGroup Hf)) := by
  obtain ⟨hE, Hf, hHf, hHfl, φ, hφ, -⟩ := exists_selfDualFactor hself hS
  refine ⟨hE, Hf, hHf, hHfl, ?_⟩
  let D : sesqUnitaryGroup Hf →* (AdjoinRoot (a : K[X]))ˣ :=
    (blockGLDet (x : Module.End K V) (a : K[X])).comp (sesqUnitaryGroup Hf).subtype
  have hspec := specialBlock_eq_kerImage φ (sesqUnitaryGroup Hf).subtype D (fun _ => rfl)
    (fun s => blockGL_ext fun v hv => hφ s v hv)
  have hker : D.ker = (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
    ext δ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
    constructor
    · intro h
      refine ⟨δ.2, ?_⟩
      have := congrArg Units.val h
      simpa [D, blockGLDet] using this
    · rintro ⟨-, h⟩
      apply Units.ext
      simpa [D, blockGLDet] using h
  obtain ⟨e1⟩ := nonempty_kerImage_mulEquiv (orbitFactor B x (a : K[X])) φ D
  exact ⟨((MulEquiv.subgroupCongr hspec).trans e1).trans
    ((MulEquiv.subgroupCongr hker).trans
      (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)))⟩

theorem not_isLThreeFour_specialBlock_of_good (hO : LieOrderFormulasInput) (hℓ : 5 ≤ ℓ)
    (H : UnitaryPrimaryData hK.bar B x) (a : primaryFactors (x : Module.End K V))
    (ha : IsGoodBlock hK x a) :
    ¬ IsLThreeFour (↥(specialBlock B x (a : K[X])) ⧸
      Subgroup.center ↥(specialBlock B x (a : K[X]))) := by
  have hp2 : ℓ ≠ 2 := by omega
  have hprime : ℓ.Prime := hK.prime
  have hm2 : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) := ha.1
  haveI := hK.finite
  haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  have hd : 1 ≤ (a : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
  have hfd : 1 ≤ f * (a : K[X]).natDegree := Nat.mul_pos hK.one_le hd
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · obtain ⟨hE, Hf, hHf, hHfl, ⟨e⟩⟩ :=
      nonempty_specialBlock_mulEquiv_sesqSU hself (selfDualPrimaryBlock H a hself)
    have hq5 : 5 ≤ ℓ ^ (f * (a : K[X]).natDegree) := hℓ.trans (Nat.le_self_pow (by omega) ℓ)
    rcases Nat.lt_or_ge (primaryMultiplicity (x : Module.End K V) (a : K[X])) 3 with hm | hm
    · have hV : Module.finrank (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X])) = 2 := by
        have : primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 := by omega
        exact this
      obtain ⟨e2⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf
        hHfl hV
      haveI : Finite hE.fixedField := inferInstance
      have hadm : StatedLieAdmissible .PSL 2 ℓ (f * (a : K[X]).natDegree) :=
        ⟨hprime, hfd, le_rfl, fun hc => by have := (Prod.mk.inj hc).2; omega,
          fun hc => by have := (Prod.mk.inj hc).2; omega⟩
      exact not_isLThreeFour_of_lieModel_odd hO hp2
        (lieModel_centerQuotient_of_equiv_SL hadm hE.card_fixedField (e.trans e2))
    · obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
      obtain ⟨e2⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
        (G := (1 : Matrix (Fin (Module.finrank (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X]))))
          (Fin (Module.finrank (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X])))) (AdjoinRoot (a : K[X]))))
        (fun i j => by rw [hb i j, Matrix.one_apply])
      exact not_isLThreeFour_of_lieModel_odd hO hp2
        (lieModel_centerQuotient_of_equiv_SU hE hq5 hm
          ((e.trans e2).trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hE _).symm)))
  · obtain ⟨e⟩ := nonempty_specialBlock_mulEquiv_SL (pairedPrimaryBlock H a (Ne.symm hself))
    have hcard : Nat.card (AdjoinRoot (a : K[X])) = ℓ ^ (2 * (f * (a : K[X]).natDegree)) :=
      natCard_adjoinRoot hK
    have hq5 : 5 ≤ ℓ ^ (2 * (f * (a : K[X]).natDegree)) :=
      hℓ.trans (Nat.le_self_pow (by omega) ℓ)
    have hadm : StatedLieAdmissible .PSL (primaryMultiplicity (x : Module.End K V) (a : K[X])) ℓ
        (2 * (f * (a : K[X]).natDegree)) :=
      ⟨hprime, by omega, hm2, fun hc => by have := (Prod.mk.inj hc).2; omega,
        fun hc => by have := (Prod.mk.inj hc).2; omega⟩
    exact not_isLThreeFour_of_lieModel_odd hO hp2
      (lieModel_centerQuotient_of_equiv_SL hadm hcard e)

end Block

end CFSG.HardMathSupport.Dickson.Sec6
