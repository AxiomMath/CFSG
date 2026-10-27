module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverLevi
import all CFSG.Fischer.F4
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

public noncomputable section

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Timmesfeld CFSG.Timmesfeld.LieEmbed
  CFSG.LieType.Steinberg.Minuscule
open scoped commutatorElement

section Generation

variable {F : Type*} [Field F]

@[expose] def sl3SimpleTvSet (F : Type*) [Field F] : Set (Matrix.SpecialLinearGroup (Fin 3) F) :=
  {g | ∃ c : F, g = tv 0 1 c ∨ g = tv 1 0 c ∨ g = tv 1 2 c ∨ g = tv 2 1 c}

theorem closure_sl3SimpleTvSet : closure (sl3SimpleTvSet F) = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := F),
    closure_le]
  have h01 : ∀ c : F, tv 0 1 c ∈ closure (sl3SimpleTvSet F) := fun c =>
    subset_closure ⟨c, Or.inl rfl⟩
  have h10 : ∀ c : F, tv 1 0 c ∈ closure (sl3SimpleTvSet F) := fun c =>
    subset_closure ⟨c, Or.inr (Or.inl rfl)⟩
  have h12 : ∀ c : F, tv 1 2 c ∈ closure (sl3SimpleTvSet F) := fun c =>
    subset_closure ⟨c, Or.inr (Or.inr (Or.inl rfl))⟩
  have h21 : ∀ c : F, tv 2 1 c ∈ closure (sl3SimpleTvSet F) := fun c =>
    subset_closure ⟨c, Or.inr (Or.inr (Or.inr rfl))⟩
  rintro _ ⟨i, j, hij, c, rfl⟩
  rw [SetLike.mem_coe, ← tv_of_ne hij]
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact h01 c
  · have e := Matrix.SpecialLinearGroup.commutatorElement_transvection
      (by decide : (0 : Fin 3) ≠ 1) (by decide : (1 : Fin 3) ≠ 2) hij c 1
    rw [mul_one] at e
    rw [tv_of_ne hij, ← e, ← tv_of_ne, ← tv_of_ne]
    exact commutatorElement_mem _ (h01 c) (h12 1)
  · exact h10 c
  · exact absurd rfl hij
  · exact h12 c
  · have e := Matrix.SpecialLinearGroup.commutatorElement_transvection
      (by decide : (2 : Fin 3) ≠ 1) (by decide : (1 : Fin 3) ≠ 0) hij c 1
    rw [mul_one] at e
    rw [tv_of_ne hij, ← e, ← tv_of_ne, ← tv_of_ne]
    exact commutatorElement_mem _ (h21 c) (h10 1)
  · exact h21 c
  · exact absurd rfl hij

theorem sl3_mem_of_simpleTv {G : Type*} [Group G] (φ : Matrix.SpecialLinearGroup (Fin 3) F →* G)
    {H : Subgroup G} (h01 : ∀ c, φ (tv 0 1 c) ∈ H) (h10 : ∀ c, φ (tv 1 0 c) ∈ H)
    (h12 : ∀ c, φ (tv 1 2 c) ∈ H) (h21 : ∀ c, φ (tv 2 1 c) ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin 3) F) : φ g ∈ H := by
  have hle : closure (sl3SimpleTvSet F) ≤ H.comap φ := by
    rw [closure_le]
    rintro _ ⟨c, rfl | rfl | rfl | rfl⟩
    exacts [h01 c, h10 c, h12 c, h21 c]
  rw [closure_sl3SimpleTvSet] at hle
  exact hle (mem_top g)

theorem sl3_hom_ext {G : Type*} [Group G] {φ ψ : Matrix.SpecialLinearGroup (Fin 3) F →* G}
    (h01 : ∀ c, φ (tv 0 1 c) = ψ (tv 0 1 c)) (h10 : ∀ c, φ (tv 1 0 c) = ψ (tv 1 0 c))
    (h12 : ∀ c, φ (tv 1 2 c) = ψ (tv 1 2 c)) (h21 : ∀ c, φ (tv 2 1 c) = ψ (tv 2 1 c)) :
    φ = ψ := by
  refine MonoidHom.eq_of_eqOn_dense closure_sl3SimpleTvSet ?_
  rintro _ ⟨c, rfl | rfl | rfl | rfl⟩
  exacts [h01 c, h10 c, h12 c, h21 c]

end Generation

local notation "𝔽" => GaloisField 2 (2 * 1)

local notation "σ₀" => sigma (GaloisField 2 (2 * 1)) (frobQ 2 1)

@[expose] def levi34Psi
    : Matrix.SpecialLinearGroup (Fin 3) 𝔽 →* e6Data_valid.minGroup 𝔽 :=
  Classical.choose ((simplyLacedLevis_e6 𝔽).sl3 (e6n 0) (e6n 2) (by decide))

theorem levi34Psi_spec
    : Function.Injective levi34Psi ∧ ∀ c : 𝔽,
    levi34Psi (tv 0 1 c) = e6Data_valid.xm 𝔽 (sroot (e6n 0)) c ∧
    levi34Psi (tv 1 0 c) = e6Data_valid.xm 𝔽 (-sroot (e6n 0)) c ∧
    levi34Psi (tv 1 2 c) = e6Data_valid.xm 𝔽 (sroot (e6n 2)) c ∧
    levi34Psi (tv 2 1 c) = e6Data_valid.xm 𝔽 (-sroot (e6n 2)) c ∧
    levi34Psi (tv 0 2 c) = e6Data_valid.xm 𝔽 (sroot (e6n 0) + sroot (e6n 2)) c ∧
    levi34Psi (tv 2 0 c) = e6Data_valid.xm 𝔽 (-(sroot (e6n 0) + sroot (e6n 2))) c :=
  Classical.choose_spec ((simplyLacedLevis_e6 𝔽).sl3 (e6n 0) (e6n 2) (by decide))

set_option maxRecDepth 100000 in
theorem e6_levi34_orth_check : ∀ a ∈ ({e6n 0, e6n 2} : Finset (Fin (Tag.rank .E6))),
    ∀ b ∈ ({e6n 4, e6n 5} : Finset (Fin (Tag.rank .E6))),
    ∀ s ∈ ({1, -1} : Finset ℤ), ∀ s' ∈ ({1, -1} : Finset ℤ),
      s • sroot a + s' • sroot b ≠ 0 ∧ s • sroot a + s' • sroot b ∉ rootFinset .E6 := by
  decide +kernel

@[expose] def levi34RootSet :
    Set (e6Data_valid.minGroup 𝔽) :=
  {g | ∃ a ∈ ({e6n 0, e6n 2} : Finset (Fin (Tag.rank .E6))), ∃ s ∈ ({1, -1} : Finset ℤ),
    ∃ c : 𝔽, g = e6Data_valid.xm 𝔽 (s • sroot a) c}

@[expose] def levi34RootSetTwist :
    Set (e6Data_valid.minGroup 𝔽) :=
  {g | ∃ b ∈ ({e6n 4, e6n 5} : Finset (Fin (Tag.rank .E6))), ∃ s ∈ ({1, -1} : Finset ℤ),
    ∃ c : 𝔽, g = e6Data_valid.xm 𝔽 (s • sroot b) c}

theorem isRoot_smul_sroot {s : ℤ} (hs : s ∈ ({1, -1} : Finset ℤ)) (a : Fin (Tag.rank .E6)) :
    IsRoot .E6 (s • sroot a) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · rw [one_smul]; exact isRoot_single _ _
  · rw [neg_one_smul]; exact isRoot_neg_single _ _

theorem closure_levi34RootSet_le_centralizer
    : closure levi34RootSet ≤
    centralizer (closure levi34RootSetTwist : Set (e6Data_valid.minGroup 𝔽)) := by
  rw [centralizer_closure, closure_le]
  rintro _ ⟨a, ha, s, hs, c, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_iff]
  rintro _ ⟨b, hb, s', hs', d, rfl⟩
  obtain ⟨hne, hnr⟩ := e6_levi34_orth_check a ha b hb s hs s' hs'
  exact ((commutatorElement_eq_one_iff_commute.1 ((e6Data_valid.commutator_xm 𝔽
    (isRoot_smul_sroot hs a) (isRoot_smul_sroot hs' b) hne).2
      (fun h => hnr (mem_rootFinset.2 h)) c d)).eq).symm

theorem levi34Psi_mem_closure
    (g : Matrix.SpecialLinearGroup (Fin 3) 𝔽) :
    levi34Psi g ∈ closure levi34RootSet := by
  have h1 : (1 : ℤ) ∈ ({1, -1} : Finset ℤ) := by decide
  have h2 : (-1 : ℤ) ∈ ({1, -1} : Finset ℤ) := by decide
  have h0 : e6n 0 ∈ ({e6n 0, e6n 2} : Finset (Fin (Tag.rank .E6))) := by decide
  have h2' : e6n 2 ∈ ({e6n 0, e6n 2} : Finset (Fin (Tag.rank .E6))) := by decide
  refine sl3_mem_of_simpleTv levi34Psi (fun c => subset_closure ?_) (fun c => subset_closure ?_)
    (fun c => subset_closure ?_) (fun c => subset_closure ?_) g
  · exact ⟨_, h0, 1, h1, c, by rw [(levi34Psi_spec.2 c).1, one_smul]⟩
  · exact ⟨_, h0, -1, h2, c, by rw [(levi34Psi_spec.2 c).2.1, neg_one_smul]⟩
  · exact ⟨_, h2', 1, h1, c, by rw [(levi34Psi_spec.2 c).2.2.1, one_smul]⟩
  · exact ⟨_, h2', -1, h2, c, by rw [(levi34Psi_spec.2 c).2.2.2.1, neg_one_smul]⟩

theorem sigma_levi34Psi_mem_closure
    (g : Matrix.SpecialLinearGroup (Fin 3) 𝔽) :
    σ₀ (levi34Psi g) ∈ closure levi34RootSetTwist := by
  have h1 : (1 : ℤ) ∈ ({1, -1} : Finset ℤ) := by decide
  have h2 : (-1 : ℤ) ∈ ({1, -1} : Finset ℤ) := by decide
  have h5 : e6n 5 ∈ ({e6n 4, e6n 5} : Finset (Fin (Tag.rank .E6))) := by decide
  have h4 : e6n 4 ∈ ({e6n 4, e6n 5} : Finset (Fin (Tag.rank .E6))) := by decide
  refine sl3_mem_of_simpleTv ((sigma 𝔽 (frobQ 2 1)).comp levi34Psi)
    (fun c => subset_closure ?_) (fun c => subset_closure ?_) (fun c => subset_closure ?_)
    (fun c => subset_closure ?_) g
  · refine ⟨_, h5, 1, h1, frobQ 2 1 c, ?_⟩
    rw [MonoidHom.comp_apply, (levi34Psi_spec.2 c).1, sigma_xm_single, one_smul]
    rfl
  · refine ⟨_, h5, -1, h2, frobQ 2 1 c, ?_⟩
    rw [MonoidHom.comp_apply, (levi34Psi_spec.2 c).2.1, sigma_xm_neg_single, neg_one_smul]
    rfl
  · refine ⟨_, h4, 1, h1, frobQ 2 1 c, ?_⟩
    rw [MonoidHom.comp_apply, (levi34Psi_spec.2 c).2.2.1, sigma_xm_single, one_smul]
    rfl
  · refine ⟨_, h4, -1, h2, frobQ 2 1 c, ?_⟩
    rw [MonoidHom.comp_apply, (levi34Psi_spec.2 c).2.2.2.1, sigma_xm_neg_single, neg_one_smul]
    rfl

theorem commute_levi34Psi_sigma
    (g h : Matrix.SpecialLinearGroup (Fin 3) 𝔽) :
    Commute (levi34Psi g) (σ₀ (levi34Psi h)) :=
  ((mem_centralizer_iff.1 (closure_levi34RootSet_le_centralizer (levi34Psi_mem_closure g)))
    _ (sigma_levi34Psi_mem_closure h)).symm

@[expose] def levi34Hom₀
    : Matrix.SpecialLinearGroup (Fin 3) 𝔽 →* e6Data_valid.minGroup 𝔽 :=
  (levi34Psi.noncommCoprod ((sigma 𝔽 (frobQ 2 1)).comp levi34Psi)
    commute_levi34Psi_sigma).comp ((MonoidHom.id _).prod (MonoidHom.id _))

theorem levi34Hom₀_apply
    (g : Matrix.SpecialLinearGroup (Fin 3) 𝔽) :
    levi34Hom₀ g = levi34Psi g * σ₀ (levi34Psi g) :=
  rfl

theorem levi34Hom₀_mem
    (g : Matrix.SpecialLinearGroup (Fin 3) 𝔽) :
    levi34Hom₀ g ∈ fixedGroup 𝔽 (frobQ 2 1) := by
  rw [mem_fixedGroup, levi34Hom₀_apply, map_mul,
    sigma_sigma (frobQ 2 1) (frobQ_frobQ 2 1 le_rfl)]
  exact (commute_levi34Psi_sigma g g).symm.eq

@[expose] def levi34Hom
    : Matrix.SpecialLinearGroup (Fin 3) 𝔽 →* twistedE6Group 2 1 :=
  levi34Hom₀.codRestrict _ levi34Hom₀_mem

theorem coe_levi34Hom
    (g : Matrix.SpecialLinearGroup (Fin 3) 𝔽) :
    (levi34Hom g : e6Data_valid.minGroup 𝔽) = levi34Psi g * σ₀ (levi34Psi g) :=
  rfl

theorem levi34Hom_tv01
    (c : 𝔽) : (levi34Hom (tv 0 1 c) : e6Data_valid.minGroup 𝔽) =
    e6Data_valid.xm 𝔽 (sroot (e6n 0)) c * e6Data_valid.xm 𝔽 (sroot (e6n 5)) (frobQ 2 1 c) := by
  rw [coe_levi34Hom, (levi34Psi_spec.2 c).1, sigma_xm_single]
  rfl

theorem levi34Hom_tv10
    (c : 𝔽) : (levi34Hom (tv 1 0 c) : e6Data_valid.minGroup 𝔽) =
    e6Data_valid.xm 𝔽 (-sroot (e6n 0)) c * e6Data_valid.xm 𝔽 (-sroot (e6n 5)) (frobQ 2 1 c) := by
  rw [coe_levi34Hom, (levi34Psi_spec.2 c).2.1, sigma_xm_neg_single]
  rfl

theorem levi34Hom_tv12
    (c : 𝔽) : (levi34Hom (tv 1 2 c) : e6Data_valid.minGroup 𝔽) =
    e6Data_valid.xm 𝔽 (sroot (e6n 2)) c * e6Data_valid.xm 𝔽 (sroot (e6n 4)) (frobQ 2 1 c) := by
  rw [coe_levi34Hom, (levi34Psi_spec.2 c).2.2.1, sigma_xm_single]
  rfl

theorem levi34Hom_tv21
    (c : 𝔽) : (levi34Hom (tv 2 1 c) : e6Data_valid.minGroup 𝔽) =
    e6Data_valid.xm 𝔽 (-sroot (e6n 2)) c * e6Data_valid.xm 𝔽 (-sroot (e6n 4)) (frobQ 2 1 c) := by
  rw [coe_levi34Hom, (levi34Psi_spec.2 c).2.2.2.1, sigma_xm_neg_single]
  rfl

theorem rho_sroot_ne_self
    {a : Fin (Tag.rank .E6)} (ha : rhoPerm a ≠ a) :
    rho (sroot a) ≠ sroot a := by
  rw [rho_single]
  intro h
  have := congrFun h (rhoPerm a)
  rw [Pi.single_eq_same, sroot_of_ne ha] at this
  exact one_ne_zero this

theorem rho_neg_sroot_ne_self
    {a : Fin (Tag.rank .E6)} (ha : rhoPerm a ≠ a) :
    rho (-sroot a) ≠ -sroot a := by
  rw [rho_neg_single]
  intro h
  have := congrFun h (rhoPerm a)
  rw [Pi.neg_apply, Pi.neg_apply, Pi.single_eq_same, sroot_of_ne ha] at this
  norm_num at this

theorem mem_twistedE6Datum_rootGroup_iff
    {β : Fin (Tag.rank .F4) → ℤ}
    {α₀ : Fin (Tag.rank .E6) → ℤ} (hα₀ : IsRoot .E6 α₀) (hp : proj α₀ = β)
    (hne : rho α₀ ≠ α₀) {i j : Fin 3}
    (hij : ∀ c, (levi34Hom (tv i j c) : e6Data_valid.minGroup 𝔽) =
      e6Data_valid.xm 𝔽 α₀ c * e6Data_valid.xm 𝔽 (rho α₀) ((twistSign α₀ : 𝔽) * frobQ 2 1 c))
    (g : twistedE6Group 2 1) :
    g ∈ (twistedE6Datum 2 1).rootGroup β ↔ ∃ c, g = levi34Hom (tv i j c) := by
  change g ∈ twistedRootGroup 𝔽 (frobQ 2 1) β ↔ _
  rw [mem_twistedRootGroup_iff_of_pair (frobQ 2 1) hα₀ hp hne g]
  refine exists_congr fun c => ⟨fun h => Subtype.ext (h.trans (hij c).symm), fun h => ?_⟩
  rw [h, hij c]

local instance :
    NeZero (twistedE6Datum 2 1).rank :=
  ⟨by show (4 : ℕ) ≠ 0; decide⟩

local instance : NeZero (Tag.rank .F4) := ⟨by decide⟩

theorem rhoPerm_e6n_zero : rhoPerm (e6n 0) = e6n 5 := by decide

theorem rhoPerm_e6n_two : rhoPerm (e6n 2) = e6n 4 := by decide

theorem proj_sroot_e6n_zero : proj (sroot (e6n 0)) = Pi.single 3 1 := by
  funext i; fin_cases i <;> rfl

theorem proj_neg_sroot_e6n_zero : proj (-sroot (e6n 0)) = -Pi.single 3 1 := by
  funext i; fin_cases i <;> rfl

theorem proj_sroot_e6n_two : proj (sroot (e6n 2)) = Pi.single 2 1 := by
  funext i; fin_cases i <;> rfl

theorem proj_neg_sroot_e6n_two : proj (-sroot (e6n 2)) = -Pi.single 2 1 := by
  funext i; fin_cases i <;> rfl

theorem mem_rootGroup_three_iff
    (g : twistedE6Group 2 1) :
    g ∈ (twistedE6Datum 2 1).rootGroup (Pi.single 3 1) ↔ ∃ c, g = levi34Hom (tv 0 1 c) :=
  mem_twistedE6Datum_rootGroup_iff (isRoot_single _ _) proj_sroot_e6n_zero
    (rho_sroot_ne_self (by decide)) (fun c => by
      rw [levi34Hom_tv01, rho_single, twistSign_single, Int.cast_one, one_mul,
        rhoPerm_e6n_zero]) g

theorem mem_rootGroup_neg_three_iff
    (g : twistedE6Group 2 1) :
    g ∈ (twistedE6Datum 2 1).rootGroup (-Pi.single 3 1) ↔ ∃ c, g = levi34Hom (tv 1 0 c) :=
  mem_twistedE6Datum_rootGroup_iff (isRoot_neg_single _ _) proj_neg_sroot_e6n_zero
    (rho_neg_sroot_ne_self (by decide)) (fun c => by
      rw [levi34Hom_tv10, rho_neg_single, twistSign_neg_single, Int.cast_one, one_mul,
        rhoPerm_e6n_zero]) g

theorem mem_rootGroup_two_iff
    (g : twistedE6Group 2 1) :
    g ∈ (twistedE6Datum 2 1).rootGroup (Pi.single 2 1) ↔ ∃ c, g = levi34Hom (tv 1 2 c) :=
  mem_twistedE6Datum_rootGroup_iff (isRoot_single _ _) proj_sroot_e6n_two
    (rho_sroot_ne_self (by decide)) (fun c => by
      rw [levi34Hom_tv12, rho_single, twistSign_single, Int.cast_one, one_mul,
        rhoPerm_e6n_two]) g

theorem mem_rootGroup_neg_two_iff
    (g : twistedE6Group 2 1) :
    g ∈ (twistedE6Datum 2 1).rootGroup (-Pi.single 2 1) ↔ ∃ c, g = levi34Hom (tv 2 1 c) :=
  mem_twistedE6Datum_rootGroup_iff (isRoot_neg_single _ _) proj_neg_sroot_e6n_two
    (rho_neg_sroot_ne_self (by decide)) (fun c => by
      rw [levi34Hom_tv21, rho_neg_single, twistSign_neg_single, Int.cast_one, one_mul,
        rhoPerm_e6n_two]) g

theorem range_levi34Hom
    : levi34Hom.range = (twistedE6Datum 2 1).levi levi34 := by
  have h2 : (2 : Fin (twistedE6Datum 2 1).rank) ∈ levi34 := by
    have key : (2 : Fin 4) ∈ ({2, 3} : Finset (Fin 4)) := by decide
    exact key
  have h3 : (3 : Fin (twistedE6Datum 2 1).rank) ∈ levi34 := by
    have key : (3 : Fin 4) ∈ ({2, 3} : Finset (Fin 4)) := by decide
    exact key
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    refine sl3_mem_of_simpleTv levi34Hom (fun c => ?_) (fun c => ?_) (fun c => ?_)
      (fun c => ?_) g
    · exact CFSG.LieType.CurtisTits.rankOne_le_levi _ h3
        (mem_sup_left ((mem_rootGroup_three_iff _).2 ⟨c, rfl⟩))
    · exact CFSG.LieType.CurtisTits.rankOne_le_levi _ h3
        (mem_sup_right ((mem_rootGroup_neg_three_iff _).2 ⟨c, rfl⟩))
    · exact CFSG.LieType.CurtisTits.rankOne_le_levi _ h2
        (mem_sup_left ((mem_rootGroup_two_iff _).2 ⟨c, rfl⟩))
    · exact CFSG.LieType.CurtisTits.rankOne_le_levi _ h2
        (mem_sup_right ((mem_rootGroup_neg_two_iff _).2 ⟨c, rfl⟩))
  · refine iSup₂_le fun j hj => ?_
    rcases (by simpa [levi34] using hj : j = 2 ∨ j = 3) with rfl | rfl
    · refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨c, rfl⟩ := (mem_rootGroup_two_iff x).1 hx
        exact ⟨_, rfl⟩
      · obtain ⟨c, rfl⟩ := (mem_rootGroup_neg_two_iff x).1 hx
        exact ⟨_, rfl⟩
    · refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨c, rfl⟩ := (mem_rootGroup_three_iff x).1 hx
        exact ⟨_, rfl⟩
      · obtain ⟨c, rfl⟩ := (mem_rootGroup_neg_three_iff x).1 hx
        exact ⟨_, rfl⟩

theorem hElt_tv01_eq {F : Type} [Field F] {t : F} (ht : t ≠ 0) :
    LevisExtras.hElt (tv 0 1) (tv 1 0) t =
      (tv 0 1 t * tv 1 0 (-t⁻¹) * tv 0 1 t * (tv 0 1 (-1) * tv 1 0 1 * tv 0 1 (-1)) :
        Matrix.SpecialLinearGroup (Fin 3) F) := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  rw [LevisExtras.cm_h01 ht]
  simp only [map_mul, LevisExtras.cm_tv01, LevisExtras.cm_tv10, Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [ht]

theorem hElt_tv12_eq {F : Type} [Field F] {t : F} (ht : t ≠ 0) :
    LevisExtras.hElt (tv 1 2) (tv 2 1) t =
      (tv 1 2 t * tv 2 1 (-t⁻¹) * tv 1 2 t * (tv 1 2 (-1) * tv 2 1 1 * tv 1 2 (-1)) :
        Matrix.SpecialLinearGroup (Fin 3) F) := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  rw [LevisExtras.cm_h12 ht]
  simp only [map_mul, LevisExtras.cm_tv12, LevisExtras.cm_tv21, Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [ht]

theorem hm_mk0_eq
    (i : Fin (Tag.rank .E6)) {t : 𝔽} (ht : t ≠ 0) :
    e6Data_valid.hm 𝔽 i (Units.mk0 t ht) =
      e6Data_valid.xm 𝔽 (Pi.single i 1) t * e6Data_valid.xm 𝔽 (-Pi.single i 1) (-t⁻¹) *
        e6Data_valid.xm 𝔽 (Pi.single i 1) t * (e6Data_valid.xm 𝔽 (Pi.single i 1) (-1) *
          e6Data_valid.xm 𝔽 (-Pi.single i 1) 1 * e6Data_valid.xm 𝔽 (Pi.single i 1) (-1)) := by
  simp only [MinData.Valid.hm, MinData.Valid.nt, mul_inv_rev, MinData.Valid.xm_neg, Units.val_mk0,
    Units.val_inv_eq_inv_val, inv_one, Units.val_one, neg_neg, mul_assoc]

abbrev e6TopWeight : Fin e6Data.d := ⟨0, by decide⟩

theorem wt_e6TopWeight : e6Data.wt (e6TopWeight : ℕ) (e6n 0) = 1 ∧
    e6Data.wt (e6TopWeight : ℕ) (e6n 2) = 0 ∧ e6Data.wt (e6TopWeight : ℕ) (e6n 4) = 0 ∧
      e6Data.wt (e6TopWeight : ℕ) (e6n 5) = 0 := by
  decide

theorem levi34Psi_hElt01
    {t : 𝔽} (ht : t ≠ 0) :
    levi34Psi (LevisExtras.hElt (tv 0 1) (tv 1 0) t) =
      e6Data_valid.hm 𝔽 (e6n 0) (Units.mk0 t ht) := by
  have p01 := fun c => (levi34Psi_spec.2 c).1
  have p10 := fun c => (levi34Psi_spec.2 c).2.1
  rw [hElt_tv01_eq ht, hm_mk0_eq _ ht]
  simp only [map_mul, p01, p10]

theorem levi34Psi_hElt12
    {t : 𝔽} (ht : t ≠ 0) :
    levi34Psi (LevisExtras.hElt (tv 1 2) (tv 2 1) t) =
      e6Data_valid.hm 𝔽 (e6n 2) (Units.mk0 t ht) := by
  have p12 := fun c => (levi34Psi_spec.2 c).2.2.1
  have p21 := fun c => (levi34Psi_spec.2 c).2.2.2.1
  rw [hElt_tv12_eq ht, hm_mk0_eq _ ht]
  simp only [map_mul, p12, p21]

theorem levi34Hom₀_hElt
    {t : 𝔽} (ht : t ≠ 0) :
    levi34Hom₀ (LevisExtras.hElt (tv 0 1) (tv 1 0) t *
        LevisExtras.hElt (tv 1 2) (tv 2 1) (t ^ 2)) =
      e6Data_valid.hm 𝔽 (e6n 0) (Units.mk0 t ht) *
          e6Data_valid.hm 𝔽 (e6n 2) (Units.mk0 (t ^ 2) (pow_ne_zero 2 ht)) *
        (e6Data_valid.hm 𝔽 (e6n 5) (Units.map (frobQ 2 1) (Units.mk0 t ht)) *
          e6Data_valid.hm 𝔽 (e6n 4)
            (Units.map (frobQ 2 1) (Units.mk0 (t ^ 2) (pow_ne_zero 2 ht)))) := by
  rw [levi34Hom₀_apply, map_mul, levi34Psi_hElt01 ht, levi34Psi_hElt12 (pow_ne_zero 2 ht),
    map_mul, sigma_hm, sigma_hm, rhoPerm_e6n_zero, rhoPerm_e6n_two]

theorem endo_levi34Hom₀_hElt
    {t : 𝔽} (ht : t ≠ 0) :
    e6Data_valid.endo 𝔽 (levi34Hom₀ (LevisExtras.hElt (tv 0 1) (tv 1 0) t *
      LevisExtras.hElt (tv 1 2) (tv 2 1) (t ^ 2))) (Finsupp.single e6TopWeight 1) =
        t • Finsupp.single e6TopWeight 1 := by
  obtain ⟨w0, w2, w4, w5⟩ := wt_e6TopWeight
  rw [levi34Hom₀_hElt ht]
  simp only [MinData.Valid.endo_mul, MinData.Valid.endo_hm, Module.End.mul_apply,
    MinData.hDiag_single, w0, w2, w4, w5, zpow_zero, zpow_one, Units.val_one, one_smul,
    Units.val_mk0]

theorem eq_one_of_smul_e6TopWeight {t : 𝔽}
    (h : t • Finsupp.single e6TopWeight (1 : 𝔽) = Finsupp.single e6TopWeight 1) : t = 1 := by
  have := congrArg (fun v : Fin e6Data.d →₀ 𝔽 => v e6TopWeight) h
  simpa using this

theorem exists_galoisField_ne_zero_ne_one : ∃ t : 𝔽, t ≠ 0 ∧ t ≠ 1 := by
  refine ⟨fieldEquiv.symm CFSG.LieType.Chevalley.C2E6Overlap.ω, ?_, ?_⟩
  · rw [Ne, map_eq_zero_iff _ fieldEquiv.symm.injective]
    decide
  · rw [Ne, ← map_one fieldEquiv.symm, fieldEquiv.symm.injective.eq_iff]
    decide

theorem levi34Hom₀_injective
    : Function.Injective levi34Hom₀ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hnt : ∃ g, levi34Hom₀ g ≠ 1 := by
    obtain ⟨t, ht0, ht1⟩ := exists_galoisField_ne_zero_ne_one
    refine ⟨LevisExtras.hElt (tv 0 1) (tv 1 0) t * LevisExtras.hElt (tv 1 2) (tv 2 1) (t ^ 2),
      fun h => ht1 (eq_one_of_smul_e6TopWeight ?_)⟩
    rw [← endo_levi34Hom₀_hElt ht0, h, MinData.Valid.endo_one, Module.End.one_apply]
  have hker : g ∈ center (Matrix.SpecialLinearGroup (Fin 3) 𝔽) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 𝔽 le_rfl) hnt hg
  obtain ⟨t, ht0, -, rfl, h1⟩ := LevisExtras.exists_eq_of_mem_center hker
  refine h1 (eq_one_of_smul_e6TopWeight ?_)
  rw [← endo_levi34Hom₀_hElt ht0, hg, MinData.Valid.endo_one, Module.End.one_apply]

theorem levi34Hom_injective
    : Function.Injective levi34Hom :=
  fun _ _ h => levi34Hom₀_injective (congrArg Subtype.val h)

set_option maxRecDepth 100000 in
theorem e6_center_weight_check : ∀ γ ∈ rootFinset .E6,
    (3 : ℤ) ∣ MinData.toWeight γ (e6n 0) + 2 * MinData.toWeight γ (e6n 2) +
      2 * MinData.toWeight γ (e6n 5) + MinData.toWeight γ (e6n 4) := by
  decide +kernel

theorem hm_prod_mem_center
    {u : 𝔽ˣ} (hu : u ^ 3 = 1) :
    e6Data_valid.hm 𝔽 (e6n 0) u * e6Data_valid.hm 𝔽 (e6n 2) (u ^ 2) *
        (e6Data_valid.hm 𝔽 (e6n 5) (u ^ 2) * e6Data_valid.hm 𝔽 (e6n 4) u) ∈
      center (e6Data_valid.minGroup 𝔽) := by
  set z := e6Data_valid.hm 𝔽 (e6n 0) u * e6Data_valid.hm 𝔽 (e6n 2) (u ^ 2) *
    (e6Data_valid.hm 𝔽 (e6n 5) (u ^ 2) * e6Data_valid.hm 𝔽 (e6n 4) u) with hz
  have key : ∀ γ, IsRoot .E6 γ → ∀ c,
      z * e6Data_valid.xm 𝔽 γ c * z⁻¹ = e6Data_valid.xm 𝔽 γ c := by
    intro γ hγ c
    obtain ⟨m, hm⟩ := e6_center_weight_check γ (mem_rootFinset.2 hγ)
    have e : z * e6Data_valid.xm 𝔽 γ c * z⁻¹ =
        e6Data_valid.hm 𝔽 (e6n 0) u * (e6Data_valid.hm 𝔽 (e6n 2) (u ^ 2) *
          (e6Data_valid.hm 𝔽 (e6n 5) (u ^ 2) * (e6Data_valid.hm 𝔽 (e6n 4) u *
            e6Data_valid.xm 𝔽 γ c * (e6Data_valid.hm 𝔽 (e6n 4) u)⁻¹) *
              (e6Data_valid.hm 𝔽 (e6n 5) (u ^ 2))⁻¹) *
                (e6Data_valid.hm 𝔽 (e6n 2) (u ^ 2))⁻¹) * (e6Data_valid.hm 𝔽 (e6n 0) u)⁻¹ := by
      rw [hz]; group
    rw [e, MinData.Valid.hm_conj_xm _ _ hγ, MinData.Valid.hm_conj_xm _ _ hγ,
      MinData.Valid.hm_conj_xm _ _ hγ, MinData.Valid.hm_conj_xm _ _ hγ, ← mul_assoc, ← mul_assoc,
      ← mul_assoc, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, ← zpow_add, ← zpow_add, ← zpow_add]
    have hexp : MinData.toWeight γ (e6n 0) + (2 : ℕ) * MinData.toWeight γ (e6n 2) +
        (2 : ℕ) * MinData.toWeight γ (e6n 5) + MinData.toWeight γ (e6n 4) = 3 * m := by
      push_cast; linarith
    rw [hexp, zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hu, one_zpow,
      Units.val_one, one_mul]
  have hle : (⊤ : Subgroup (e6Data_valid.minGroup 𝔽)) ≤ centralizer {z} := by
    rw [← e6Data_valid.iSup_rootGroup]
    refine iSup₂_le fun γ hγ x hx => ?_
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup 𝔽).1 hx
    rw [mem_centralizer_singleton_iff]
    have := key γ hγ c
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  exact mem_center_iff.2 fun g => mem_centralizer_singleton_iff.1 (hle (mem_top g))

theorem units_map_frobQ
    (u : 𝔽ˣ) : Units.map (frobQ 2 1 : 𝔽 →* 𝔽) u = u ^ 2 :=
  Units.ext (by
    rw [Units.coe_map, MonoidHom.coe_ofClass, frobQ_apply, pow_one, Units.val_pow_eq_pow_val])

theorem levi34Hom₀_mem_center
    {A : Matrix.SpecialLinearGroup (Fin 3) 𝔽}
    (hA : A ∈ center (Matrix.SpecialLinearGroup (Fin 3) 𝔽)) :
    levi34Hom₀ A ∈ center (e6Data_valid.minGroup 𝔽) := by
  obtain ⟨t, ht0, ht3, rfl, -⟩ := LevisExtras.exists_eq_of_mem_center hA
  set u : 𝔽ˣ := Units.mk0 t ht0
  have hu3 : u ^ 3 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, ht3, Units.val_one])
  have hu2 : Units.mk0 (t ^ 2) (pow_ne_zero 2 ht0) = u ^ 2 :=
    Units.ext (by rw [Units.val_mk0, Units.val_pow_eq_pow_val, Units.val_mk0])
  have hu4 : (u ^ 2) ^ 2 = u := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hu3, one_mul]
  rw [levi34Hom₀_hElt ht0, hu2, units_map_frobQ, units_map_frobQ, hu4]
  exact hm_prod_mem_center hu3

theorem levi34Hom_mem_center
    {A : Matrix.SpecialLinearGroup (Fin 3) 𝔽}
    (hA : A ∈ center (Matrix.SpecialLinearGroup (Fin 3) 𝔽)) :
    levi34Hom A ∈ center (twistedE6Group 2 1) :=
  mem_center_iff.2 fun g => Subtype.ext ((mem_center_iff.1 (levi34Hom₀_mem_center hA)) g)

end CFSG.EvenSmallLie.TwoE6
