module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverLevi
public import CFSG.LieType.TitsSimplicity.Core
public import CFSG.LieType.Chevalley.C2E6A5ExteriorCubeModel
public import CFSG.LieType.Chevalley.C2E6D4NaturalOrthogonal
public import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
public import CFSG.LieType.Chevalley.C2E6FourthResidueMinusEight
public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoRelativeData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.Timmesfeld.ARS.Sec5Ten
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Chevalley.C2E6Std
open scoped commutatorElement

section Center

open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6

theorem units_pow_three (t : (GaloisField 2 (2 * 1))ˣ) : t ^ 3 = 1 := by
  classical
  have h : Nat.card (GaloisField 2 (2 * 1)) = 4 := by
    rw [GaloisField.card 2 (2 * 1) (by norm_num)]
    norm_num
  have : Fintype (GaloisField 2 (2 * 1)) := Fintype.ofFinite _
  have h3 : Fintype.card (GaloisField 2 (2 * 1))ˣ = 3 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, h]
  rw [← h3]
  exact pow_card_eq_one

theorem pow_three_eq_one_of_mem_center
    {z : twistedE6Group 2 1}
    (hz : z ∈ center (twistedE6Group 2 1)) : z ^ 3 = 1 := by
  have hθ := frobQ_frobQ 2 1 le_rfl
  have hct := twistedDatum_isCTGroupDatum (frobQ 2 1) hθ (iSup_twistedDatum_rootGroup _ hθ)
  have hext := twistedDatum_steinbergExtras (frobQ 2 1) hθ
  have hBU := twistedDatum_bruhatExtras (frobQ 2 1)
  rw [CFSG.LieType.TitsSimplicity.center_eq_normalCore_borel hct hext hBU] at hz
  have hT := CFSG.LieType.TitsSimplicity.normalCore_borel_le_iSup hct hBU hz
  have hle : (⨆ i, hHat (GaloisField 2 (2 * 1)) (frobQ 2 1) i) ≤
      (torusHom (GaloisField 2 (2 * 1))).range.comap
        (fixedGroup (GaloisField 2 (2 * 1)) (frobQ 2 1)).subtype := by
    refine iSup_le fun i x hx => ?_
    have hx' : (x : e6Data_valid.minGroup _) ∈ hHatE (GaloisField 2 (2 * 1)) (frobQ 2 1) i := hx
    rw [mem_comap]
    refine (iSup_le fun a => ?_ : ⨆ a, e6Data_valid.torus (GaloisField 2 (2 * 1)) a ≤ _)
      (hHatE_le_iSup_torus (frobQ 2 1) i hx')
    rintro _ ⟨t, rfl⟩
    exact ⟨Pi.mulSingle a t, torusHom_mulSingle a t⟩
  obtain ⟨v, hv⟩ := hle hT
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← coe_subtype, ← hv, ← map_pow]
  rw [show v ^ 3 = 1 from funext fun a => units_pow_three (v a), map_one]

theorem pow_three_eq_one_of_mem_ker_isogenyStd
    {n : twistedE6Group 2 1}
    (hn : n ∈ isogenyStd.ker) : n ^ 3 = 1 :=
  pow_three_eq_one_of_mem_center (ker_isogenyStd_le_center hn)

theorem finite_twistedE6Group
    : Finite (twistedE6Group 2 1) := by
  have : Finite (Module.End (GaloisField 2 (2 * 1)) (Fin e6Data.d →₀ GaloisField 2 (2 * 1))) :=
    Module.finite_of_finite (GaloisField 2 (2 * 1))
  infer_instance

theorem isPerfect_twistedE6Group
    : Group.IsPerfect (twistedE6Group 2 1) :=
  fixedGroup_isPerfect_of_four_le_card (frobQ 2 1) (frobQ_frobQ 2 1 le_rfl)
    (CFSG.LieType.Steinberg.Isogeny.four_le_card_galoisField 2 1 le_rfl)

end Center

section Fibre

variable {X : Type} [Group X]

structure IsDoubleCover (π : X →* stdGroup) : Prop where
  surjective : Function.Surjective π
  ker_le_center : π.ker ≤ center X
  card_ker : Nat.card π.ker = 2

@[expose] noncomputable def fibre
    (π : X →* stdGroup) : Subgroup (X × twistedE6Group 2 1) :=
  MonoidHom.eqLocus (π.comp (MonoidHom.fst _ _)) (isogenyStd.comp (MonoidHom.snd _ _))

theorem mem_fibre
    {π : X →* stdGroup} {x : X × twistedE6Group 2 1} :
    x ∈ fibre π ↔ π x.1 = isogenyStd x.2 :=
  Iff.rfl

@[expose] noncomputable def fibreHom
    (π : X →* stdGroup) : fibre π →* twistedE6Group 2 1 :=
  (MonoidHom.snd _ _).comp (fibre π).subtype

theorem fibreHom_apply
    {π : X →* stdGroup} (x : fibre π) :
    fibreHom π x = (x : X × twistedE6Group 2 1).2 :=
  rfl

@[expose] noncomputable def fibreFst
    (π : X →* stdGroup) : fibre π →* X :=
  (MonoidHom.fst _ _).comp (fibre π).subtype

theorem fibreFst_apply
    {π : X →* stdGroup} (x : fibre π) :
    fibreFst π x = (x : X × twistedE6Group 2 1).1 :=
  rfl

variable {π : X →* stdGroup}

theorem IsDoubleCover.sq_eq_one
    (hπ : IsDoubleCover π) {z : X} (hz : z ∈ π.ker) : z ^ 2 = 1 := by
  have h := pow_card_eq_one' (G := π.ker) (x := ⟨z, hz⟩)
  rw [hπ.card_ker] at h
  exact congrArg Subtype.val h

theorem eq_one_of_pow_two_of_pow_three {G : Type*} [Group G] {z : G} (h2 : z ^ 2 = 1)
    (h3 : z ^ 3 = 1) : z = 1 := by
  rw [show z = z ^ 3 * (z ^ 2)⁻¹ by group, h2, h3, inv_one, mul_one]

theorem map_fst_fibre
    : (fibre π).map (MonoidHom.fst _ _) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨u, hu⟩ := isogenyStd_surjective (π x)
  exact ⟨(x, u), hu.symm, rfl⟩

theorem map_snd_fibre
    (hπ : IsDoubleCover π) : (fibre π).map (MonoidHom.snd _ _) = ⊤ := by
  refine eq_top_iff.2 fun u _ => ?_
  obtain ⟨x, hx⟩ := hπ.surjective (isogenyStd u)
  exact ⟨(x, u), hx, rfl⟩

theorem commutator_top_eq_top (G : Type*) [Group G] [Group.IsPerfect G] :
    ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
  rw [← commutator_def, Group.IsPerfect.commutator_eq_top]

theorem commutator_fibre
    [Group.IsPerfect X] (hπ : IsDoubleCover π) :
    ⁅fibre π, fibre π⁆ = fibre π := by
  have := isPerfect_twistedE6Group
  refine le_antisymm (commutator_self_le _) fun x hx => ?_
  have hfst : (⁅fibre π, fibre π⁆).map (MonoidHom.fst _ _) = ⊤ := by
    rw [map_commutator, map_fst_fibre, commutator_top_eq_top]
  have hsnd : (⁅fibre π, fibre π⁆).map (MonoidHom.snd _ _) = ⊤ := by
    rw [map_commutator, map_snd_fibre hπ, commutator_top_eq_top]
  obtain ⟨y, hy, hyx⟩ : x.2 ∈ (⁅fibre π, fibre π⁆).map (MonoidHom.snd _ _) := hsnd ▸ mem_top _
  change y.2 = x.2 at hyx
  have hyP : y ∈ fibre π := commutator_self_le _ hy
  set z := x.1 * y.1⁻¹
  have hz : z ∈ π.ker := by
    have h1 : π x.1 = isogenyStd x.2 := hx
    have h2 : π y.1 = isogenyStd y.2 := hyP
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, h2, hyx, mul_inv_cancel]
  obtain ⟨w, hw, hwz⟩ : z ∈ (⁅fibre π, fibre π⁆).map (MonoidHom.fst _ _) := hfst ▸ mem_top _
  change w.1 = z at hwz
  have hwP : w ∈ fibre π := commutator_self_le _ hw
  have hn : w.2 ∈ isogenyStd.ker := by
    have h : π w.1 = isogenyStd w.2 := hwP
    rw [hwz, show π z = 1 from hz] at h
    exact h.symm
  have hw3 : w ^ 3 = (z, 1) := Prod.ext (by
    rw [Prod.pow_fst, hwz]
    rw [show z ^ 3 = z * z ^ 2 by group, hπ.sq_eq_one hz, mul_one]) (by
    rw [Prod.pow_snd, pow_three_eq_one_of_mem_ker_isogenyStd hn])
  have hx' : x = (z, 1) * y := Prod.ext (by simp [z]) (by
    change x.2 = 1 * y.2
    rw [one_mul, hyx])
  rw [hx', ← hw3]
  exact mul_mem (pow_mem hw 3) hy

theorem isPerfect_fibre
    [Group.IsPerfect X] (hπ : IsDoubleCover π) :
    Group.IsPerfect (fibre π) :=
  Subgroup.isPerfect_iff.2 (commutator_fibre hπ)

theorem finite_fibre
    [Finite X] : Finite (fibre π) := by
  have := finite_twistedE6Group
  infer_instance

theorem fibreHom_surjective
    (hπ : IsDoubleCover π) : Function.Surjective (fibreHom π) := by
  intro u
  obtain ⟨x, hx⟩ := hπ.surjective (isogenyStd u)
  exact ⟨⟨(x, u), hx⟩, rfl⟩

theorem fibreFst_surjective
    : Function.Surjective (fibreFst π) := by
  intro x
  obtain ⟨u, hu⟩ := isogenyStd_surjective (π x)
  exact ⟨⟨(x, u), hu.symm⟩, rfl⟩

theorem mem_ker_fibreHom
    {x : fibre π} :
    x ∈ (fibreHom π).ker ↔ (x : X × twistedE6Group 2 1).2 = 1 :=
  Iff.rfl

theorem fst_mem_ker_of_mem_ker_fibreHom
    {x : fibre π} (hx : x ∈ (fibreHom π).ker) :
    (x : X × twistedE6Group 2 1).1 ∈ π.ker := by
  have h : π (x : X × twistedE6Group 2 1).1 = isogenyStd (x : X × twistedE6Group 2 1).2 := x.2
  rw [MonoidHom.mem_ker, h, show (x : X × twistedE6Group 2 1).2 = 1 from hx, map_one]

theorem ker_fibreHom_le_center
    (hπ : IsDoubleCover π) : (fibreHom π).ker ≤ center (fibre π) := by
  intro x hx
  have hc : (x : X × twistedE6Group 2 1) ∈ center (X × twistedE6Group 2 1) := by
    rw [Subgroup.center_prod]
    refine ⟨hπ.ker_le_center (fst_mem_ker_of_mem_ker_fibreHom hx), ?_⟩
    rw [show (x : X × twistedE6Group 2 1).2 = 1 from hx]
    exact one_mem _
  rw [mem_center_iff]
  intro y
  exact Subtype.ext (mem_center_iff.1 hc y)

@[expose] noncomputable def kerFibreHomEquiv
    (π : X →* stdGroup) : (fibreHom π).ker ≃ π.ker where
  toFun x := ⟨((x : fibre π) : X × twistedE6Group 2 1).1, fst_mem_ker_of_mem_ker_fibreHom x.2⟩
  invFun z := ⟨⟨((z : X), 1), by
    rw [mem_fibre, map_one]
    exact z.2⟩, rfl⟩
  left_inv x := Subtype.ext (Subtype.ext (Prod.ext rfl x.2.symm))
  right_inv z := rfl

theorem card_ker_fibreHom
    (hπ : IsDoubleCover π) : Nat.card (fibreHom π).ker = 2 := by
  rw [Nat.card_congr (kerFibreHomEquiv π), hπ.card_ker]

theorem isPGroup_ker_fibreHom
    (hπ : IsDoubleCover π) : IsPGroup 2 (fibreHom π).ker :=
  IsPGroup.of_card (n := 1) (by rw [card_ker_fibreHom hπ, pow_one])

theorem fst_eq_one_iff
    (hπ : IsDoubleCover π) (x : fibre π) :
    (x : X × twistedE6Group 2 1).1 = 1 ↔ isogenyStd (fibreHom π x) = 1 ∧ x ^ 3 = 1 := by
  have h : π (x : X × twistedE6Group 2 1).1 = isogenyStd (x : X × twistedE6Group 2 1).2 := x.2
  constructor
  · intro h1
    rw [h1, map_one] at h
    refine ⟨h.symm, Subtype.ext (Prod.ext ?_ ?_)⟩
    · rw [SubgroupClass.coe_pow, Prod.pow_fst, h1, one_pow]; rfl
    · rw [SubgroupClass.coe_pow, Prod.pow_snd,
        pow_three_eq_one_of_mem_ker_isogenyStd (MonoidHom.mem_ker.2 h.symm)]; rfl
  · rintro ⟨h1, h3⟩
    have hz : (x : X × twistedE6Group 2 1).1 ∈ π.ker := by
      rw [MonoidHom.mem_ker, h]
      exact h1
    refine eq_one_of_pow_two_of_pow_three (hπ.sq_eq_one hz) ?_
    have := congrArg (fun y : fibre π => (y : X × twistedE6Group 2 1).1) h3
    simpa using this

theorem nonempty_mulEquiv_of_fibre
    {X₁ X₂ : Type} [Group X₁] [Group X₂] {π₁ : X₁ →* stdGroup}
    {π₂ : X₂ →* stdGroup} (h₁ : IsDoubleCover π₁) (h₂ : IsDoubleCover π₂)
    (ψ : fibre π₁ ≃* fibre π₂) (hψ : ∀ x, fibreHom π₂ (ψ x) = fibreHom π₁ x) :
    Nonempty (X₁ ≃* X₂) := by
  set f : fibre π₁ →* X₂ := (fibreFst π₂).comp ψ.toMonoidHom
  have hf : Function.Surjective f := fibreFst_surjective.comp ψ.surjective
  have hker : (fibreFst π₁).ker = f.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, fibreFst_apply]
    change _ ↔ ((ψ x : fibre π₂) : X₂ × twistedE6Group 2 1).1 = 1
    rw [fst_eq_one_iff h₁, fst_eq_one_iff h₂, hψ]
    refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
    · rw [← map_pow, h, map_one]
    · exact ψ.injective (by rw [map_pow, h, map_one])
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective _ fibreFst_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf))⟩

noncomputable abbrev fibre34
    (π : X →* stdGroup) : Subgroup (fibre π) :=
  ((twistedE6Datum 2 1).levi levi34).comap (fibreHom π)

@[expose] noncomputable def fibre34Hom
    (π : X →* stdGroup) :
    fibre34 π →* (twistedE6Datum 2 1).levi levi34 :=
  ((fibreHom π).comp (fibre34 π).subtype).codRestrict _ fun x => x.2

theorem coe_fibre34Hom
    (x : fibre34 π) :
    (fibre34Hom π x : twistedE6Group 2 1) = fibreHom π x :=
  rfl

theorem fibre34Hom_surjective
    (hπ : IsDoubleCover π) : Function.Surjective (fibre34Hom π) := by
  intro v
  obtain ⟨x, hx⟩ := fibreHom_surjective hπ (v : twistedE6Group 2 1)
  exact ⟨⟨x, show fibreHom π x ∈ _ from hx ▸ v.2⟩, Subtype.ext hx⟩

theorem ker_fibreHom_le_fibre34
    : (fibreHom π).ker ≤ fibre34 π := fun x hx => by
  rw [mem_comap, show fibreHom π x = 1 from hx]
  exact one_mem _

theorem mem_ker_fibre34Hom
    {x : fibre34 π} :
    x ∈ (fibre34Hom π).ker ↔ (x : fibre π) ∈ (fibreHom π).ker := by
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← coe_fibre34Hom]
  exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩

theorem ker_fibre34Hom_le_center
    (hπ : IsDoubleCover π) :
    (fibre34Hom π).ker ≤ center (fibre34 π) := by
  intro x hx
  have hc := ker_fibreHom_le_center hπ (mem_ker_fibre34Hom.1 hx)
  rw [mem_center_iff]
  intro y
  exact Subtype.ext (mem_center_iff.1 hc y)

@[expose] noncomputable def kerFibre34HomEquiv
    (π : X →* stdGroup) :
    (fibre34Hom π).ker ≃ (fibreHom π).ker where
  toFun x := ⟨x, mem_ker_fibre34Hom.1 x.2⟩
  invFun x := ⟨⟨x, ker_fibreHom_le_fibre34 x.2⟩, mem_ker_fibre34Hom.2 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_ker_fibre34Hom
    (hπ : IsDoubleCover π) : Nat.card (fibre34Hom π).ker = 2 := by
  rw [Nat.card_congr (kerFibre34HomEquiv π), card_ker_fibreHom hπ]

theorem commutator_fibre34
    [Finite X] [Group.IsPerfect X] (hπ : IsDoubleCover π) :
    ⁅fibre34 π, fibre34 π⁆ = fibre34 π := by
  have := isPerfect_fibre hπ
  have := finite_fibre (π := π)
  have hle := ker_le_commutator_comap_levi34 (fibreHom π) (fibreHom_surjective hπ)
    (ker_fibreHom_le_center hπ) (isPGroup_ker_fibreHom hπ)
  have hmap := map_commutator_comap_levi34 (fibreHom π) (fibreHom_surjective hπ)
  refine le_antisymm (commutator_self_le _) fun y hy => ?_
  obtain ⟨w, hw, hwy⟩ : fibreHom π y ∈ (⁅fibre34 π, fibre34 π⁆).map (fibreHom π) :=
    hmap ▸ hy
  have hk : w⁻¹ * y ∈ (fibreHom π).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hwy, inv_mul_cancel]
  rw [show y = w * (w⁻¹ * y) by group]
  exact mul_mem hw (hle hk)

theorem isPerfect_fibre34
    [Finite X] [Group.IsPerfect X] (hπ : IsDoubleCover π) :
    Group.IsPerfect (fibre34 π) :=
  Subgroup.isPerfect_iff.2 (commutator_fibre34 hπ)

variable
    {X' : Type} [Group X'] {π' : X' →* stdGroup}

@[expose] noncomputable def fibre34Map
    (ρ : X →* X')
    (γ : (twistedE6Datum 2 1).levi levi34 →* (twistedE6Datum 2 1).levi levi34)
    (h : ∀ x (v : (twistedE6Datum 2 1).levi levi34), π x = isogenyStd v →
      π' (ρ x) = isogenyStd (γ v)) :
    fibre34 π →* fibre34 π' :=
  ((((ρ.comp ((fibreFst π).comp (fibre34 π).subtype)).prod
      (((twistedE6Datum 2 1).levi levi34).subtype.comp (γ.comp (fibre34Hom π)))).codRestrict
        (fibre π') fun x => h ((x : fibre π) : X × twistedE6Group 2 1).1 (fibre34Hom π x)
          (x : fibre π).2).codRestrict (fibre34 π') fun x => (γ (fibre34Hom π x)).2)

theorem fibre34Hom_fibre34Map
    (ρ : X →* X')
    (γ : (twistedE6Datum 2 1).levi levi34 →* (twistedE6Datum 2 1).levi levi34)
    (h : ∀ x (v : (twistedE6Datum 2 1).levi levi34), π x = isogenyStd v →
      π' (ρ x) = isogenyStd (γ v)) (x : fibre34 π) :
    fibre34Hom π' (fibre34Map ρ γ h x) = γ (fibre34Hom π x) :=
  rfl

theorem fst_fibre34Map
    (ρ : X →* X')
    (γ : (twistedE6Datum 2 1).levi levi34 →* (twistedE6Datum 2 1).levi levi34)
    (h : ∀ x (v : (twistedE6Datum 2 1).levi levi34), π x = isogenyStd v →
      π' (ρ x) = isogenyStd (γ v)) (x : fibre34 π) :
    (((fibre34Map ρ γ h x : fibre34 π') : fibre π') : X' × twistedE6Group 2 1).1 =
      ρ (((x : fibre π) : X × twistedE6Group 2 1).1) :=
  rfl

@[expose] noncomputable def fibre34Equiv
    (ρ : X ≃* X')
    (γ : (twistedE6Datum 2 1).levi levi34 ≃* (twistedE6Datum 2 1).levi levi34)
    (h₁ : ∀ x (v : (twistedE6Datum 2 1).levi levi34), π x = isogenyStd v →
      π' (ρ x) = isogenyStd (γ v))
    (h₂ : ∀ x (v : (twistedE6Datum 2 1).levi levi34), π' x = isogenyStd v →
      π (ρ.symm x) = isogenyStd (γ.symm v)) :
    fibre34 π ≃* fibre34 π' :=
  MonoidHom.toMulEquiv (fibre34Map ρ.toMonoidHom γ.toMonoidHom h₁)
    (fibre34Map ρ.symm.toMonoidHom γ.symm.toMonoidHom h₂)
    (MonoidHom.ext fun x => Subtype.ext (Subtype.ext (Prod.ext (ρ.symm_apply_apply _)
      (congrArg Subtype.val (γ.symm_apply_apply (fibre34Hom π x))))))
    (MonoidHom.ext fun x => Subtype.ext (Subtype.ext (Prod.ext (ρ.apply_symm_apply _)
      (congrArg Subtype.val (γ.apply_symm_apply (fibre34Hom π' x))))))

theorem fibre34Hom_fibre34Equiv
    (ρ : X ≃* X')
    (γ : (twistedE6Datum 2 1).levi levi34 ≃* (twistedE6Datum 2 1).levi levi34)
    (h₁ : ∀ x (v : (twistedE6Datum 2 1).levi levi34), π x = isogenyStd v →
      π' (ρ x) = isogenyStd (γ v))
    (h₂ : ∀ x (v : (twistedE6Datum 2 1).levi levi34), π' x = isogenyStd v →
      π (ρ.symm x) = isogenyStd (γ.symm v)) (x : fibre34 π) :
    fibre34Hom π' (fibre34Equiv ρ γ h₁ h₂ x) = γ (fibre34Hom π x) :=
  rfl

end Fibre

end CFSG.EvenSmallLie.TwoE6
