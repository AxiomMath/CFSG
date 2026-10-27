module

public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalSocleSelector
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearTwoSocle
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoModelMatrix
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedReverse
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUSp6LagrangianStatements
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.Blueprint.EvenStandardExact
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
import CFSG.Blueprint.LieModelAPI
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SteinbergBK.Sp6AlternatingExclusion

open Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.SymmetricLocal
  (faithful_alternating_socle_small_standard_source_selector_of_psl_two_or_alt_seven
    faithful_projective_linear_two_socle_involution_component_model)
open CFSG.ComponentClassification.CatalogueBLinearTwoModel (pslModelEquivCoordinateG)
open CFSG.ComponentClassification.ClassicalModelStatedBridge (classicalModel_psl_of_stated)

theorem classicalModel_psl_two_seven_of_mulEquiv {J : Type} [Group J] [Fact (Nat.Prime 7)]
    (ψ : J ≃* GL (Fin 3) (ZMod 2)) :
    center J = ⊥ ∧ Assembly.ComponentType.ClassicalModel (J ⧸ center J) .PSL 2 7 1 := by
  let e₃ : SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ bijective_toGL_three_zmod_two
  let ε : J ≃* SpecialLinearGroup (Fin 3) (ZMod 2) := ψ.trans e₃.symm
  have hcJ : center J = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : ε x ∈ center (SpecialLinearGroup (Fin 3) (ZMod 2)) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := ε.surjective g
      rw [← map_mul, ← map_mul, mem_center_iff.mp hx y]
    rw [center_SL_three_zmod_two_eq_bot, mem_bot] at h1
    rw [mem_bot]
    simpa using h1
  let e₂ : ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃* SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  let eq : J ⧸ center J ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hcJ).trans QuotientGroup.quotientBot
  let e : J ⧸ center J ≃* StatedProj (StatedSL 3 (ZMod 2)) :=
    eq.trans (ε.trans (e₂.symm.trans (projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 2))))
  have hlie : CFSG.Blueprint.LieModel (J ⧸ center J) .PSL 3 2 1 :=
    Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2,
      inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one], ⟨e⟩⟩
  rcases PSL3_two_PSL2_seven_paired_isomorphism _ hlie with ⟨-, hc⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨hcJ, classicalModel_psl_of_stated hc⟩
  all_goals exact absurd h (by norm_num)

theorem false_of_alternating_of_psl_two_seven_source {A : Type} [Group A] [Finite A]
    {W : Subgroup A} [W.Normal] (hWsimple : IsSimpleGroup W) (hWnonab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    (hstd : CFSG.Assembly.ComponentType.IsStandardSubgroup L) [Fact (Nat.Prime 7)]
    (hsrc : Assembly.ComponentType.ClassicalModel (L ⧸ center L) .PSL 2 7 1) {n : ℕ}
    (hn : 5 ≤ n) (φ : W ≃* alternatingGroup (Fin n)) : False := by
  have hsel := faithful_alternating_socle_small_standard_source_selector_of_psl_two_or_alt_seven
    hWsimple hWnonab hCW ha hLW hL hstd (Or.inl ⟨7, 1, inferInstance, by norm_num, hsrc⟩) hn φ
  by_cases h6 : n = 6
  · rcases hsel.1 with ⟨-, hW32⟩ | ⟨h7n, -⟩
    · have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨-, ⟨e⟩⟩ := hW32
      have hK : Nat.card (GaloisField 3 2) = 3 ^ 2 := GaloisField.card 3 2 (by norm_num)
      have hproj := faithful_projective_linear_two_socle_involution_component_model
        hWsimple hWnonab hCW ha hLW hL (ℓ := 3) (e := 2) (by norm_num) hK (by norm_num)
        (e.trans (pslModelEquivCoordinateG 3 2))
      exact absurd hproj.2.1 (by norm_num)
    · omega
  · obtain ⟨β, -, -, -, -, -, -, -, hpsl, -⟩ := hsel.2 h6
    rcases hpsl 7 1 (by norm_num) hsrc with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> exact absurd h (by norm_num)

theorem isEmpty_alternating_of_GL3_component {Y : Type} [Group Y] [Finite Y] {D : Subgroup Y}
    [D.Normal] (hDsimple : IsSimpleGroup D) (hDnonab : ∃ x y : D, x * y ≠ y * x)
    (hCD : centralizer (D : Set Y) = ⊥) {a : Y} (ha : orderOf a = 2) {J : Subgroup Y}
    (hJD : J ≤ D) (hJ : CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set Y)))
    (hstd : CFSG.Assembly.ComponentType.IsStandardSubgroup J) (ψ : J ≃* GL (Fin 3) (ZMod 2)) :
    ∀ n : ℕ, 5 ≤ n → IsEmpty (D ≃* alternatingGroup (Fin n)) := by
  have h7 : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  intro n hn
  refine ⟨fun φ => ?_⟩
  exact false_of_alternating_of_psl_two_seven_source hDsimple hDnonab hCD ha hJD hJ hstd
    (classicalModel_psl_two_seven_of_mulEquiv ψ).2 hn φ

theorem isComponentOf_of_normal_of_standard {Y : Type*} [Group Y] {J C : Subgroup Y}
    (hJC : J ≤ C) (hnorm : (J.subgroupOf C).Normal)
    (hstd : CFSG.Assembly.ComponentType.IsStandardSubgroup J) :
    CFSG.Assembly.IsComponentOf J C :=
  ⟨hJC, .step hJC hnorm (.refl C), hstd.1⟩

noncomputable def mulEquivOfInjective {Y : Type*} [Group Y] {J : Subgroup Y}
    (f : GL (Fin 3) (ZMod 2) →* Y) (hf : Function.Injective f) (hJ : f.range = J) :
    J ≃* GL (Fin 3) (ZMod 2) :=
  ((MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hJ)).symm

theorem componentType_isStandardSubgroup {Y : Type*} [Group Y] {J : Subgroup Y}
    (h : CFSG.IsStandardSubgroup J) : Assembly.ComponentType.IsStandardSubgroup J :=
  CFSG.StandardSubgroupAPI.isStandardSubgroup_iff_assembly.1 h

theorem oddCore_eq_bot_of_orderOf_eq_two {G : Type} [Group G] [Finite G] (hG : IsSimpleGroup G)
    {z : G} (hz : orderOf z = 2) : CFSG.oddCore G = ⊥ := by
  rw [CFSG.oddCore, sSup_eq_bot]
  rintro N ⟨hNn, hNodd⟩
  refine (@Subgroup.Normal.eq_bot_or_eq_top G _ hG N hNn).resolve_right fun h => ?_
  rw [h, Subgroup.card_top] at hNodd
  have h2 : 2 ∣ Nat.card G := hz ▸ orderOf_dvd_natCard z
  exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2)

theorem not_normal_of_isStandardSubgroup {G : Type} [Group G] (hG : IsSimpleGroup G)
    (hGn : ∃ x y : G, x * y ≠ y * x) {L : Subgroup G}
    (hL : Assembly.ComponentType.IsStandardSubgroup L) : ¬ L.Normal :=
  CFSG.Open.standardComponentIsStandard.not_normal hL hG hGn

theorem lieModel_of_center_eq_bot {X : Type} [Group X] (hX : center X = ⊥)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel (X ⧸ center X) t n p f) : CFSG.Blueprint.LieModel X t n p f :=
  CFSG.Blueprint.LieModel.of_quotient_center hX h

end CFSG.LocalAnalysis.ComponentInitial.SteinbergBK.Sp6AlternatingExclusion

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBK.Sp6AlternatingExclusion

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
  (he : IsSymplecticBasis b e) (z : G)

namespace SteinbergBK

omit [Finite G] in
theorem sp6A₂_eq_range_tauHom : sp6A₂ φ e = (tauHom φ he).range := by
  rw [sp6A₂, pullSub_eq_map, tauHom, MonoidHom.range_comp, ← map_spCoord_pointwiseStabilizer he,
    Subgroup.map_map]
  congr 1
  ext g
  simp [spHom]

theorem sp6Dstar_isEmpty_alternating {V₁ : Subgroup G}
    (hconc : Sp6LagrangianLayerConclusion φ he z V₁) (hDs : IsSimpleGroup (sp6Dstar φ he z))
    (hDnab : ∃ x y : sp6Dstar φ he z, x * y ≠ y * x) :
    ∀ n : ℕ, 5 ≤ n → IsEmpty (sp6Dstar φ he z ≃* alternatingGroup (Fin n)) := by
  obtain ⟨-, -, -, -, ⟨ι, -, hιinj, hιrange⟩, -, -, -, -, -, -, hθinj, -, -, -, -, -, -,
    haBar2, hJC, -, hCaBar, -, -, -, -, -, -, hJstd, -, -, -, -, hCD, -⟩ := hconc
  have hψinj : Function.Injective ((sp6θ φ he z).comp ι) := by
    intro g g' hgg
    apply hιinj
    refine hθinj ?_ ?_ hgg
    · rw [← hιrange]
      exact ⟨g, rfl⟩
    · rw [← hιrange]
      exact ⟨g', rfl⟩
  have hψrange : ((sp6θ φ he z).comp ι).range = sp6JLBar φ he z := by
    rw [MonoidHom.range_comp, hιrange]
    rfl
  have hstd := componentType_isStandardSubgroup hJstd
  have haN : sp6aBar φ he z ∈ normalizer (sp6JLBar φ he z : Set (Sp6Y φ he z)) :=
    centralizer_le_normalizer _ (mem_centralizer_iff.2 fun j hj =>
      mem_centralizer_singleton_iff.1 (hJC hj))
  have hJn : ((sp6JLBar φ he z).subgroupOf (centralizer {sp6aBar φ he z})).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hJC, ← hCaBar]
    exact sup_le (zpowers_le.2 haN) le_normalizer
  have hJD : sp6JLBar φ he z ≤ sp6Dstar φ he z := le_normalClosure
  have : (sp6Dstar φ he z).Normal := normalClosure_normal
  exact isEmpty_alternating_of_GL3_component hDs hDnab hCD haBar2 hJD
    (isComponentOf_of_normal_of_standard hJC hJn hstd) hstd (mulEquivOfInjective _ hψinj hψrange)

theorem sp6_kappa_exists (hG : CFSG.oddCore G = ⊥)
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    [FiniteDimensional (ZMod 2) V] (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6)
    (hfull : conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G)) :
    ∃ κ₂ : ZMod 2, ∀ d ∈ sp6D₂ φ e z, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * z * d = tauHom φ he (Multiplicative.ofAdd C) * z ^ (1 : ZMod 2).val →
      d⁻¹ * (tauHom φ he (Multiplicative.ofAdd B) * z ^ ε.val) * d =
        tauHom φ he (Multiplicative.ofAdd (B + κ₂ • symThreePolarSym (symThreeDiag (C : M₃))
          (symThreeDiag (B : M₃)) + ε • C)) * z ^ ε.val := by
  obtain ⟨-, hzC, -, hinf, hrest⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths hG hL hLn hZ hmodel T hT hzT hz hH
  obtain ⟨-, hW⟩ := hrest hb hnd hV φ
  obtain ⟨-, -, -, -, -, -, -, -, -, hker, -, -, -, ⟨σ, -, -, -, hσ⟩, -⟩ :=
    hW (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf e he rfl
  obtain ⟨κ₂, D₂, -, ν₂, hD₂, -, -, -, -, -, -, -, hzν, -, -, hact, -⟩ :=
    degree64_lagrangian_two_group φ he hzC hz hinf hker σ hσ hfull
  have hθ : ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      tauHom φ he (Multiplicative.ofAdd B) * z ^ ε.val =
        radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) := fun B ε => rfl
  refine ⟨κ₂, fun d hd C B ε hdC => ?_⟩
  have hd' : d ∈ D₂ := by
    rw [hD₂]
    exact hd
  have hC : C = ν₂ d := by
    have h1 := (hzν d hd').symm.trans (hdC.trans (hθ C 1))
    have h2 := radHom_injective φ he hzC hz hinf h1
    exact (congrArg Prod.fst (Multiplicative.ofAdd.injective h2)).symm
  rw [hθ, hθ, hC]
  exact hact d hd' B ε

include he in
theorem sp6_lam_exists (hG : CFSG.oddCore G = ⊥)
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    [FiniteDimensional (ZMod 2) V] (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6)
    (hfull : conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G)) :
    let u := e (Sum.inl 0)
    let f := e (Sum.inr 0)
    let E := pairOrth b u f
    let n : E → ZMod 2 → bilinIsometryGroup b := fun w c => pointElt hb (mem_pairOrth_left w.2) c
    let Q : E → ZMod 2 := fun w =>
      e.repr w (Sum.inl 1) * e.repr w (Sum.inr 1) + e.repr w (Sum.inl 2) * e.repr w (Sum.inr 2)
    let r : E × ZMod 2 := (0, 1)
    let θ₁ : (E × ZMod 2) × ZMod 2 → G := fun x =>
      ((φ.symm (n x.1.1 (x.1.2 + Q x.1.1)) : L) : G) * z ^ x.2.val
    let A₁ := pullSub φ (pointRadical b hb u f)
    let B₁ := A₁ ⊔ zpowers z
    let N₁ := normalizer (B₁ : Set G)
    let D₁ := CFSG.Assembly.pCoreOf 2 N₁
    ∃ lam : ZMod 2, ∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
      d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (lam * b (a.1 : V) (v.1 : V)) • r + ε • a, ε) := by
  intro u f E n Q r θ₁ A₁ B₁ N₁ D₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ψ, θ₁', hψ, hθ₁', lam, D₁', -, ν₁, hD₁',
      -, -, -, -, -, -, -, -, -, -, hzν₁, -, -, hact₁, -⟩ :=
    standard_binary_symplectic_six_degree64_other_parabolic_normalizer hG hL hLn hZ hmodel T hT
      hzT hz hH hb hnd hV φ e he hfull
  have hθeq : ∀ (v : E × ZMod 2) (ε : ZMod 2),
      θ₁ (v, ε) = ((θ₁'.symm (Multiplicative.ofAdd (v, ε)) : B₁) : G) := by
    rintro ⟨w, c⟩ ε
    rw [hθ₁']
    have h1 := hψ w (c + Q w)
    have h2 : c + Q w + Q w = c := by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [h2] at h1
    rw [h1]
  have hθinj : ∀ v v' : E × ZMod 2, θ₁ (v, 1) = θ₁ (v', 1) → v = v' := by
    intro v v' h
    rw [hθeq, hθeq] at h
    have h1 := θ₁'.symm.injective (Subtype.ext h)
    exact congrArg Prod.fst (Multiplicative.ofAdd.injective h1)
  refine ⟨lam, fun d hd a v ε hda => ?_⟩
  have hd' : d ∈ D₁' := by
    rw [hD₁']
    exact hd
  have ha : a = ν₁ d := hθinj _ _ (hda.symm.trans ((hzν₁ d hd').trans (hθeq _ _).symm))
  rw [hθeq, hθeq, ha]
  exact hact₁ d hd' v ε

theorem sp6_eps_eq_zero {E₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)} {ε : ZMod 2}
    (hE₂card : Nat.card E₂ = 512)
    (hC₂card : Nat.card (sp6D₂ φ e z ⊓ centralizer (E₂ : Set G) : Subgroup G) = 4096)
    (hC₂F : ((sp6D₂ φ e z ⊓ centralizer (E₂ : Set G) : Subgroup G) : Set G) ∩ sp6F₂ φ he z =
      (E₂ : Set G))
    (hν₂ : ∀ d ∈ sp6D₂ φ e z, z⁻¹ * (d⁻¹ * z * d) = tauHom φ he (Multiplicative.ofAdd (ν₂ d)))
    (hsq : ∀ c ∈ sp6D₂ φ e z ⊓ centralizer (E₂ : Set G), c ^ 2 =
      tauHom φ he (Multiplicative.ofAdd (symThreeSquare ε (symThreeDiag (ν₂ c : M₃)))) *
        z ^ (0 : ZMod 2).val)
    (hel : IsElementaryAbelian 2 (sp6D₂ φ e z ⊓ centralizer (E₂ : Set G) : Subgroup G)) :
    ε = 0 := by
  obtain ⟨c, hcC, hcE⟩ : ∃ c ∈ sp6D₂ φ e z ⊓ centralizer (E₂ : Set G), c ∉ E₂ := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (show sp6D₂ φ e z ⊓ centralizer (E₂ : Set G) ≤ E₂ from
      fun c hc => hcon c hc)
    rw [hC₂card, hE₂card] at hle
    norm_num at hle
  have hcF : c ∉ sp6F₂ φ he z := by
    intro hcF
    have hmem : c ∈ ((sp6D₂ φ e z ⊓ centralizer (E₂ : Set G) : Subgroup G) : Set G) ∩
        sp6F₂ φ he z := ⟨hcC, hcF⟩
    rw [hC₂F] at hmem
    exact hcE hmem
  have hcD : c ∈ sp6D₂ φ e z := (mem_inf.mp hcC).1
  have hw : symThreeDiag (ν₂ c : M₃) ≠ 0 := fun hw => hcF ⟨hcD, ν₂ c, hw, (hν₂ c hcD).symm⟩
  have hc2 : c ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian c hcC
  have hS : symThreeSquare ε (symThreeDiag (ν₂ c : M₃)) = 0 := by
    have h := (hsq c hcC).symm.trans hc2
    rw [ZMod.val_zero, pow_zero, mul_one, ← map_one (tauHom φ he)] at h
    exact Multiplicative.ofAdd.injective (tauHom_injective φ he h)
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) ε with h0 | rfl
  · exact h0
  · exfalso
    apply hw
    have hv := congrArg Subtype.val hS
    rw [coe_symThreeSquare, one_smul, ZeroMemClass.coe_zero] at hv
    exact (vecMulVec_self_eq_zero_iff _).mp hv

end SteinbergBK

theorem standard_binary_symplectic_six_elementary_lagrangian_alternating_layer_exclusion
    (hF : Sp6LagrangianFullOddCoreStmt) (hGs : IsSimpleGroup G) (hGn : ∃ x y : G, x * y ≠ y * x)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hcore : ∀ t : G, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set G)) = ⊥)
    (_hcyc : ∃ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (_htype : CFSG.Blueprint.Recognition.Exact.EvenStandardType (L ⧸ center L))
    (_hexc : ¬ CFSG.Blueprint.Recognition.Exact.EvenStandardException (L ⧸ center L))
    (_hres : CFSG.Blueprint.Recognition.Exact.EvenStandardResidual L)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel (L ⧸ center L) .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) [FiniteDimensional (ZMod 2) V] (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6)
    (hfull : conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G)) :
    (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype = zpowers z ∧
      z ∈ centralizer (L : Set G) ∧ L ⊔ zpowers z = centralizer ({z} : Set G) ∧
      L ⊓ zpowers z = ⊥ ∧
      (sp6E₂ φ he z : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative (sp6E₂ φ he z) ∧
      Nat.card (sp6E₂ φ he z) = 512 ∧
      (∀ E' : Subgroup G, (E' : Set G) ⊆ sp6F₂ φ he z → IsMulCommutative E' →
        Nat.card E' = 512 → E' = sp6E₂ φ he z) ∧
      IsElementaryAbelian 2 (sp6E₂ φ he z) ∧
      sp6C₂ φ he z ≤ sp6N₂ φ e z ∧ ((sp6C₂ φ he z).subgroupOf (sp6N₂ φ e z)).Normal ∧
      Nat.card (sp6C₂ φ he z) = 4096 ∧
      (IsElementaryAbelian 2 (sp6C₂ φ he z) → IsSimpleGroup (sp6Dstar φ he z) →
        (∃ x y : sp6Dstar φ he z, x * y ≠ y * x) →
        ∀ n : ℕ, 5 ≤ n → IsEmpty (sp6Dstar φ he z ≃* alternatingGroup (Fin n))) := by
  have hzC : z ∈ centralizer (L : Set G) := by
    obtain ⟨t, -, rfl⟩ := hzT
    exact t.2
  have hG : CFSG.oddCore G = ⊥ := oddCore_eq_bot_of_orderOf_eq_two hGs hz
  have hLn : ¬ L.Normal := not_normal_of_isStandardSubgroup hGs hGn hL
  have hmodelL : CFSG.Blueprint.LieModel L .PSp 3 2 1 := lieModel_of_center_eq_bot hZ hmodel
  have hH := hcore z hz
  obtain ⟨hTz, -, hsup, hinf, -⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths.{0} hG hL hLn hZ hmodelL T hT hzT hz hH
  obtain ⟨κ, hκ⟩ :=
    SteinbergBK.sp6_kappa_exists φ he z hG hL hLn hZ hmodelL T hT hzT hz hH hb hnd hV hfull
  obtain ⟨lam, hlam⟩ :=
    SteinbergBK.sp6_lam_exists φ he z hG hL hLn hZ hmodelL T hT hzT hz hH hb hnd hV hfull
  obtain ⟨-, _, E₂, hE₂eq, hC₂eq, -, -, -, -, -, -, -, -, -, -, -, -, hE₂F, hE₂c, hE₂card, hE₂u,
      hE₂el, hC₂n, hC₂card, -, -, hC₂F, -, -, -, -, -, ν₂, ε, hν₂, hsq, hε⟩ :=
    hF G hGs hGn hK hG L hL hLn hZ hmodelL T hT z hzT hz hH V b hb hnd hV φ e he hfull κ lam
      hκ hlam
  have hEeq : sp6E₂ φ he z = E₂ := hE₂eq.symm
  have hCeq : sp6C₂ φ he z = sp6D₂ φ e z ⊓ centralizer (E₂ : Set G) := hC₂eq.symm
  refine ⟨hTz, hzC, hsup, hinf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hEeq]
    exact hE₂F
  · rw [hEeq]
    exact hE₂c
  · rw [hEeq]
    exact hE₂card
  · rw [hEeq]
    exact hE₂u
  · rw [hEeq]
    exact hE₂el
  · rw [hCeq]
    exact inf_le_left.trans (map_subtype_le _)
  · rw [hCeq]
    refine ⟨fun c hc m => ?_⟩
    rw [mem_subgroupOf] at hc ⊢
    simpa only [coe_mul, coe_inv] using hC₂n m m.2 c hc
  · rw [hCeq]
    exact hC₂card
  intro hC₂el hDs hDn
  have hε0 : ε = 0 :=
    SteinbergBK.sp6_eps_eq_zero φ he z hE₂card hC₂card hC₂F hν₂ hsq (hCeq ▸ hC₂el)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, hconc⟩ := hε hε0
  exact SteinbergBK.sp6Dstar_isEmpty_alternating φ he z hconc hDs hDn

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
