module

public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenterUnitary
public import CFSG.CharacterTheory.Wreathed.ReducedCentralizerInclusion

public noncomputable section

namespace CFSG.Wreathed.DegreeThreeModelFullCenter

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CatalogueBUnitaryIsometry CatalogueBUnitaryTwo
open OddUnitaryThreeCentralizerCore

universe u v

@[expose] def originalCentralizerEquiv {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (t : G) :
    Subgroup.centralizer ({t} : Set G) ≃* Subgroup.centralizer ({e t} : Set H) where
  toFun g := ⟨e g, by
    have hg := g.property
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    simpa only [map_mul] using congrArg e hg⟩
  invFun h := ⟨e.symm h, by
    have hh := h.property
    rw [Subgroup.mem_centralizer_singleton_iff] at hh ⊢
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hh⟩
  left_inv g := Subtype.ext (e.symm_apply_apply g.val)
  right_inv h := Subtype.ext (e.apply_symm_apply h.val)
  map_mul' g h := Subtype.ext (e.map_mul g.val h.val)

theorem originalCentralizerEquiv_coe {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (t : G) (g : Subgroup.centralizer ({t} : Set G)) :
    (originalCentralizerEquiv e t g : H) = e g := rfl

@[expose] def reducedFullCenterEquivOfEquiv {G H : Type}
    [Group G] [Group H] [Finite G] [Finite H] (e : G ≃* H) :
    reducedFullCenter G ≃* reducedFullCenter H := by
  have hker : Odd (Nat.card e.toMonoidHom.ker) := by
    rw [e.toMonoidHom.ker_eq_bot e.injective, Subgroup.card_bot]
    decide
  let theta := ReducedCentralizerInclusion.reducedSurjectionEquiv e.toMonoidHom e.surjective hker
  exact QuotientGroup.congr _ _ theta (Subgroup.map_center_eq theta)

theorem reducedFullCenterEquivOfEquiv_mk {G H : Type}
    [Group G] [Group H] [Finite G] [Finite H] (e : G ≃* H) (g : G) :
    reducedFullCenterEquivOfEquiv e
      (QuotientGroup.mk' (Subgroup.center (G ⧸ CFSG.oddCore G))
        (QuotientGroup.mk' (CFSG.oddCore G) g)) =
      QuotientGroup.mk' (Subgroup.center (H ⧸ CFSG.oddCore H))
        (QuotientGroup.mk' (CFSG.oddCore H) (e g)) := rfl

theorem localQuotientConclusions_of_equiv {G H : Type}
    [Group G] [Group H] [Finite H] (e : G ≃* H) (p f : ℕ)
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hG : localQuotientConclusions p f G) : localQuotientConclusions p f H := by
  constructor
  · intro hthree
    obtain ⟨hsolv, hcard⟩ := hG.1 hthree
    let : Group.IsSolvable G := hsolv
    exact ⟨Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective,
      (Nat.card_congr e.symm.toEquiv).trans hcard⟩
  · intro hlarge
    have hg := hG.2 hlarge
    exact full_large_conclusions_of_equiv e p f hp hpodd hf hlarge
      ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1⟩

theorem stated_linear_three_full_center_quotient_conclusions
    (G : Type) [Group G] [Finite G] (p f : ℕ)
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : StatedClassicalModel G .PSL 3 p f) (v : G) (hv : orderOf v = 2) :
    localQuotientConclusions p f (reducedFullCenter (Subgroup.centralizer ({v} : Set G))) := by
  obtain ⟨_, F, hfield, hfinite, hcard, ⟨eModel⟩⟩ := hmodel
  let e := eModel.trans (projectiveSpecialLinearGroupEquivStatedProj 3 F).symm
  have ht : orderOf (e v) = 2 := (orderOf_injective e.toMonoidHom e.injective v).trans hv
  have hc := linear_three_target_full_center_quotient_conclusions F p f hp hpodd hf hcard
    (Subgroup.center (SpecialLinearGroup (Fin 3) F)) le_rfl (e v) ht
  let theta := reducedFullCenterEquivOfEquiv (originalCentralizerEquiv e v)
  exact localQuotientConclusions_of_equiv theta.symm p f hp hpodd hf hc

section OriginalSpecialScalars

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]
variable [FiniteDimensional E V] {sigma : E ≃+* E}
variable (h : V →ₛₗ[sigma.toRingHom] V →ₗ[E] E)

omit [FiniteDimensional E V] in
theorem originalBasisMatrixEquiv_scalar (b : Module.Basis (Fin 3) E V) (c : Eˣ) :
    CatalogueBAlternatingIsometry.basisMatrixEquiv b (scalarAction (V := V) c) =
      GeneralLinearGroup.scalar (Fin 3) c := by
  apply Units.ext
  rw [CatalogueBAlternatingIsometry.basisMatrixEquiv_val]
  have he : (scalarAction (V := V) c).toLinearMap = (c : E) • LinearMap.id := by
    apply LinearMap.ext
    intro x
    rfl
  rw [he, map_smul, LinearMap.toMatrix_id, GeneralLinearGroup.coe_scalar]
  ext i j
  simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

theorem originalSpecialMatrixEquiv_scalar (hdim : Module.finrank E V = 3)
    (b : Module.Basis (Fin 3) E V)
    (hb : ∀ i j, h (b i) (b j) = if i = j then 1 else 0)
    (c : cubicUnits (sigma := sigma)) :
    (specialIsometryMatrixEquiv h b hb (scalarSpecial h hdim c)).val =
      GeneralLinearGroup.scalar (Fin 3) c.val.val :=
  originalBasisMatrixEquiv_scalar b c.val.val

theorem originalSpecialMatrixEquiv_map_scalars (hnd : h.Nondegenerate)
    (hdim : Module.finrank E V = 3) (b : Module.Basis (Fin 3) E V)
    (hb : ∀ i j, h (b i) (b j) = if i = j then 1 else 0) :
    (scalarCenter h hdim).map (specialIsometryMatrixEquiv h b hb).toMonoidHom =
      (StatedScalars (Fin 3) E).subgroupOf
        (CFSG.LieType.Universal.Unitary.SUid sigma 3) := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := E) (by rw [hdim]; decide)
  let theta := specialIsometryMatrixEquiv h b hb
  ext g
  constructor
  · rintro ⟨a, ⟨c, rfl⟩, rfl⟩
    exact ⟨c.val.val, (originalSpecialMatrixEquiv_scalar h hdim b hb c).symm⟩
  · intro hg
    obtain ⟨a, rfl⟩ := theta.surjective g
    obtain ⟨c, hc⟩ := hg
    have hscalar : a.val.val = scalarAction (V := V) c := by
      apply (CatalogueBAlternatingIsometry.basisMatrixEquiv b).injective
      exact hc.symm.trans (originalBasisMatrixEquiv_scalar b c).symm
    have hiso : scalarAction (V := V) c ∈ isometryGroup h := by
      rw [← hscalar]
      exact a.val.property
    have hcnorm := scalar_norm_one_of_isometry h hnd c hiso
    let cN : normOneUnits (sigma := sigma) := ⟨c, hcnorm⟩
    have hc3 : cN ^ 3 = 1 := by
      apply Subtype.ext
      have ha := a.property
      change isometryDeterminant h a.val = 1 at ha
      change LinearEquiv.det a.val.val = 1 at ha
      rw [hscalar, scalarAction_determinant, hdim] at ha
      exact ha
    let c3 : cubicUnits (sigma := sigma) := ⟨cN, hc3⟩
    refine ⟨scalarSpecial h hdim c3, ⟨c3, rfl⟩, ?_⟩
    change theta (scalarSpecial h hdim c3) = theta a
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    exact hscalar.symm

end OriginalSpecialScalars

section OriginalIdentityUnitary

variable {E : Type} [Field E] [Finite E] (p f : ℕ) [Fact p.Prime]
variable (hE : Nat.card E = (p ^ f) ^ 2)

theorem originalConjugation_eq_unitaryInvolution :
    letI : CharP E p := unitaryFieldCharP p f hE
    unitaryFieldConjugation p f hE = CFSG.LieType.BorelTits.unitaryInvolution E p f := by
  let : CharP E p := unitaryFieldCharP p f hE
  ext x
  rw [unitaryFieldConjugation_apply, CFSG.LieType.BorelTits.unitaryInvolution_apply]

theorem originalSUid_eq_statedSU :
    CFSG.LieType.Universal.Unitary.SUid (unitaryFieldConjugation p f hE) 3 =
      StatedSU 3 (p ^ f) E := by
  let : CharP E p := unitaryFieldCharP p f hE
  rw [originalConjugation_eq_unitaryInvolution p f hE]
  exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hE 3

@[expose] def originalIdentityForm :
    (Fin 3 → E) →ₛₗ[(unitaryFieldConjugation p f hE).toRingHom] (Fin 3 → E) →ₗ[E] E :=
  CatalogueBHermitian.matrixForm (unitaryFieldConjugation p f hE) 1

theorem originalIdentityForm_nondegenerate : (originalIdentityForm p f hE).Nondegenerate :=
  CatalogueBHermitian.matrixForm_nondegenerate (unitaryFieldConjugation p f hE)
    (1 : GeneralLinearGroup (Fin 3) E)

theorem originalIdentityForm_isSymm : (originalIdentityForm p f hE).IsSymm :=
  CatalogueBHermitian.matrixForm_isSymm (unitaryFieldConjugation p f hE)
    (unitaryFieldConjugation_data p f hE).1 1
    (CFSG.LieType.Universal.Unitary.conjTr_one (unitaryFieldConjugation p f hE))

theorem originalIdentityForm_gram (i j : Fin 3) :
    originalIdentityForm p f hE ((Pi.basisFun E (Fin 3)) i) ((Pi.basisFun E (Fin 3)) j) =
      if i = j then 1 else 0 := by
  rw [originalIdentityForm, Pi.basisFun_apply, Pi.basisFun_apply]
  rw [CatalogueBHermitian.matrixForm_apply, Matrix.one_mulVec]
  simp [CFSG.ClassicalGroups.Unitary.herm_single_left, Pi.single_apply]

@[expose] def originalIdentitySpecialEquiv :
    specialIsometry (originalIdentityForm p f hE) ≃* StatedSU 3 (p ^ f) E :=
  (specialIsometryMatrixEquiv (originalIdentityForm p f hE) (Pi.basisFun E (Fin 3))
    (originalIdentityForm_gram p f hE)).trans
      (MulEquiv.subgroupCongr (originalSUid_eq_statedSU p f hE))

theorem originalIdentitySpecialEquiv_map_scalars :
    (scalarCenter (originalIdentityForm p f hE) (Module.finrank_fin_fun E)).map
      (originalIdentitySpecialEquiv p f hE).toMonoidHom =
        (StatedScalars (Fin 3) E).subgroupOf (StatedSU 3 (p ^ f) E) := by
  rw [originalIdentitySpecialEquiv]
  change (scalarCenter (originalIdentityForm p f hE) (Module.finrank_fin_fun E)).map
    ((MulEquiv.subgroupCongr (originalSUid_eq_statedSU p f hE)).toMonoidHom.comp
      (specialIsometryMatrixEquiv (originalIdentityForm p f hE) (Pi.basisFun E (Fin 3))
        (originalIdentityForm_gram p f hE)).toMonoidHom) = _
  rw [← Subgroup.map_map]
  rw [
    originalSpecialMatrixEquiv_map_scalars (originalIdentityForm p f hE)
      (originalIdentityForm_nondegenerate p f hE) (Module.finrank_fin_fun E)
      (Pi.basisFun E (Fin 3)) (originalIdentityForm_gram p f hE)]
  ext a
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro ha
    refine ⟨(MulEquiv.subgroupCongr (originalSUid_eq_statedSU p f hE)).symm a, ha, ?_⟩
    exact MulEquiv.apply_symm_apply _ a

end OriginalIdentityUnitary

section OriginalUnitaryModel

variable {E : Type} [Field E] [Finite E] (p f : ℕ) [Fact p.Prime]
variable (hE : Nat.card E = (p ^ f) ^ 2)

@[expose] def originalIdentityProjectiveEquiv :
    let h := originalIdentityForm p f hE
    let D := scalarCenter h (Module.finrank_fin_fun E)
    letI : D.Normal := scalar_subgroup_normal h (Module.finrank_fin_fun E) D le_rfl
    specialIsometry h ⧸ D ≃* StatedProj (StatedSU 3 (p ^ f) E) := by
  dsimp only
  let h := originalIdentityForm p f hE
  let D := scalarCenter h (Module.finrank_fin_fun E)
  let : D.Normal := scalar_subgroup_normal h (Module.finrank_fin_fun E) D le_rfl
  exact QuotientGroup.congr _ _ (originalIdentitySpecialEquiv p f hE)
    (originalIdentitySpecialEquiv_map_scalars p f hE)

theorem originalIdentityProjectiveEquiv_mk
    (g : specialIsometry (originalIdentityForm p f hE)) :
    let h := originalIdentityForm p f hE
    let D := scalarCenter h (Module.finrank_fin_fun E)
    letI : D.Normal := scalar_subgroup_normal h (Module.finrank_fin_fun E) D le_rfl
    originalIdentityProjectiveEquiv p f hE (QuotientGroup.mk' D g) =
      QuotientGroup.mk' ((StatedScalars (Fin 3) E).subgroupOf (StatedSU 3 (p ^ f) E))
        (originalIdentitySpecialEquiv p f hE g) := rfl

end OriginalUnitaryModel

theorem stated_unitary_three_full_center_quotient_conclusions
    (G : Type) [Group G] [Finite G] (p f : ℕ)
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : StatedClassicalModel G .PSU 3 p f) (v : G) (hv : orderOf v = 2) :
    localQuotientConclusions p f (reducedFullCenter (Subgroup.centralizer ({v} : Set G))) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨_, E, hfield, hfinite, hcard, ⟨eModel⟩⟩ := hmodel
  let h := originalIdentityForm p f hcard
  let : Finite (isometryGroup h) := isometryGroup_finite h
  let D := scalarCenter h (Module.finrank_fin_fun E)
  let : D.Normal := scalar_subgroup_normal h (Module.finrank_fin_fun E) D le_rfl
  let e := eModel.trans (originalIdentityProjectiveEquiv p f hcard).symm
  have ht : orderOf (e v) = 2 := (orderOf_injective e.toMonoidHom e.injective v).trans hv
  have hc := unitary_three_target_full_center_quotient_conclusions p f hpodd hf hcard h
    (originalIdentityForm_isSymm p f hcard) (originalIdentityForm_nondegenerate p f hcard)
    (Module.finrank_fin_fun E) D le_rfl (e v) ht
  let theta := reducedFullCenterEquivOfEquiv (originalCentralizerEquiv e v)
  exact localQuotientConclusions_of_equiv theta.symm p f hp hpodd hf hc

theorem originalDegreeThreeModel_finite (G : Type) [Group G] (p f : ℕ)
    (tau : StatedLieTag) (htau : tau = .PSL ∨ tau = .PSU)
    (hmodel : StatedClassicalModel G tau 3 p f) : Finite G := by
  rcases htau with rfl | rfl
  · obtain ⟨_, E, hfield, hfinite, _, ⟨e⟩⟩ := hmodel
    exact Finite.of_equiv _ e.symm.toEquiv
  · obtain ⟨_, E, hfield, hfinite, _, ⟨e⟩⟩ := hmodel
    exact Finite.of_equiv _ e.symm.toEquiv

theorem degree_three_model_full_center_local_quotient_parameter
    (G : Type) [Group G] (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (tau : StatedLieTag) (htau : tau = .PSL ∨ tau = .PSU)
    (hmodel : StatedClassicalModel G tau 3 p f) (v : G) (hv : orderOf v = 2) :
    let q := p ^ f
    let C := Subgroup.centralizer ({v} : Set G)
    let R := CFSG.oddCore C
    let H := C ⧸ R
    let Gamma := H ⧸ Subgroup.center H
    (q = 3 → Group.IsSolvable Gamma ∧ Nat.card Gamma = 24) ∧
    (5 ≤ q →
      let L := CFSG.generalizedFitting Gamma
      IsSimpleGroup L ∧ (∃ x y : L, x * y ≠ y * x) ∧
        Subgroup.centralizer (L : Set Gamma) = ⊥ ∧ L.index = 2 ∧
        StatedClassicalModel L .PSL 2 p f ∧ Nat.card L = q * (q ^ 2 - 1) / 2 ∧
        ∀ (r a : ℕ), r.Prime → Odd r → 1 ≤ a → StatedClassicalModel L .PSL 2 r a →
          r ^ a = q ∧ r = p ∧ a = f) := by
  let : Finite G := originalDegreeThreeModel_finite G p f tau htau hmodel
  rcases htau with rfl | rfl
  · exact stated_linear_three_full_center_quotient_conclusions G p f hp hpodd hf hmodel v hv
  · exact stated_unitary_three_full_center_quotient_conclusions G p f hp hpodd hf hmodel v hv

end CFSG.Wreathed.DegreeThreeModelFullCenter
