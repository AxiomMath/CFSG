module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUSp6LagrangianStatements
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCHSp6SuzukiLayerCore
public import CFSG.Blueprint.EvenStandardExact
public import Certificates.Certificate113
import CFSG.Blueprint.LieModelAPI
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentInitial.BlockNormalizerControl
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

namespace SteinbergCH

theorem lieModel_of_center_eq_bot {X : Type} [Group X] (hX : center X = ⊥) {t : StatedLieTag}
    {n p f : ℕ} (h : CFSG.Blueprint.LieModel (X ⧸ center X) t n p f) :
    CFSG.Blueprint.LieModel X t n p f :=
  CFSG.Blueprint.LieModel.of_quotient_center hX h

theorem oddCore_eq_bot_of_involution {G : Type} [Group G] [Finite G] (hG : IsSimpleGroup G)
    {z : G} (hz : orderOf z = 2) : CFSG.oddCore G = ⊥ := by
  rw [CFSG.oddCore, sSup_eq_bot]
  rintro N ⟨hNn, hNodd⟩
  rcases @Subgroup.Normal.eq_bot_or_eq_top G _ hG N hNn with h | h
  · exact h
  · exfalso
    rw [h, Subgroup.card_top] at hNodd
    have h2 : 2 ∣ Nat.card G := hz ▸ orderOf_dvd_natCard z
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2)

theorem not_normal_of_mem_centralizer {G : Type} [Group G] (hG : IsSimpleGroup G)
    (hGn : ∃ x y : G, x * y ≠ y * x) {L : Subgroup G} (hLq : CFSG.Assembly.IsQuasisimple L)
    {z : G} (hzC : z ∈ centralizer (L : Set G)) (hz1 : z ≠ 1) : ¬ L.Normal := by
  intro hLn
  rcases @Subgroup.Normal.eq_bot_or_eq_top G _ hG L hLn with h | h
  · have hsub : Subsingleton (L ⧸ center L) := by
      constructor
      intro a c
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c
      have ha : (a : G) ∈ (⊥ : Subgroup G) := by
        rw [← h]
        exact a.2
      have hc : (c : G) ∈ (⊥ : Subgroup G) := by
        rw [← h]
        exact c.2
      rw [mem_bot] at ha hc
      rw [Subtype.ext (ha.trans hc.symm)]
    exact (not_nontrivial_iff_subsingleton.mpr hsub) hLq.2.toNontrivial
  · rw [h, coe_top, centralizer_univ] at hzC
    rcases @Subgroup.Normal.eq_bot_or_eq_top G _ hG (center G) inferInstance with hc | hc
    · rw [hc, mem_bot] at hzC
      exact hz1 hzC
    · obtain ⟨x, y, hxy⟩ := hGn
      have hx : x ∈ center G := hc ▸ mem_top x
      exact hxy (mem_center_iff.mp hx y).symm

theorem kappa_action {G : Type} [Group G] {L : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V} (φ : L ≃* bilinIsometryGroup b)
    {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) {z : G}
    (hzC : z ∈ centralizer (L : Set G)) (hz : orderOf z = 2) (hinf : L ⊓ zpowers z = ⊥)
    {D : Subgroup G} {κ : ZMod 2} {ν : G → ↥(binarySymMatrices 3)}
    (hν : ∀ d ∈ D, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν d, 1)))
    (hact : ∀ d ∈ D, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ • symThreePolarSym
          (symThreeDiag (ν d : M₃)) (symThreeDiag (B : M₃)) + ε • ν d, ε))) :
    ∀ d ∈ D, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * z * d = tauHom φ he (Multiplicative.ofAdd C) * z ^ (1 : ZMod 2).val →
      d⁻¹ * (tauHom φ he (Multiplicative.ofAdd B) * z ^ ε.val) * d =
        tauHom φ he (Multiplicative.ofAdd (B + κ • symThreePolarSym (symThreeDiag (C : M₃))
          (symThreeDiag (B : M₃)) + ε • C)) * z ^ ε.val := by
  intro d hd C B ε hC
  have h1 : radHom φ he hzC hz (Multiplicative.ofAdd (ν d, 1)) =
      radHom φ he hzC hz (Multiplicative.ofAdd (C, 1)) := (hν d hd).symm.trans hC
  have h2 : ν d = C :=
    congrArg Prod.fst (Multiplicative.ofAdd.injective (radHom_injective φ he hzC hz hinf h1))
  rw [← h2]
  exact hact d hd B ε

theorem lam_action {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    {A₁ B₁ D₁ : Subgroup G} {z : G} (ψ : A₁ ≃* Multiplicative (E × ZMod 2))
    (θ₁ : B₁ ≃* Multiplicative ((E × ZMod 2) × ZMod 2)) (m : E → ZMod 2 → G) (Q : E → ZMod 2)
    (β : E → E → ZMod 2) (lam : ZMod 2) (ν₁ : G → E × ZMod 2)
    (hψ : ∀ (w : E) (c : ZMod 2), ((ψ.symm (Multiplicative.ofAdd (w, c + Q w)) : A₁) : G) = m w c)
    (hθ₁ : ∀ (v : E × ZMod 2) (ε : ZMod 2), ((θ₁.symm (Multiplicative.ofAdd (v, ε)) : B₁) : G) =
      ((ψ.symm (Multiplicative.ofAdd v) : A₁) : G) * z ^ ε.val)
    (hν₁ : ∀ d ∈ D₁, d⁻¹ * z * d = ((θ₁.symm (Multiplicative.ofAdd (ν₁ d, 1)) : B₁) : G))
    (hact : ∀ d ∈ D₁, ∀ (v : E × ZMod 2) (ε : ZMod 2),
      d⁻¹ * ((θ₁.symm (Multiplicative.ofAdd (v, ε)) : B₁) : G) * d =
        ((θ₁.symm (Multiplicative.ofAdd
          (v + (lam * β (ν₁ d).1 v.1) • ((0 : E), (1 : ZMod 2)) + ε • ν₁ d, ε)) : B₁) : G)) :
    ∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2),
      d⁻¹ * z * d = m a.1 (a.2 + Q a.1) * z ^ (1 : ZMod 2).val →
      d⁻¹ * (m v.1 (v.2 + Q v.1) * z ^ ε.val) * d =
        m (v + (lam * β a.1 v.1) • ((0 : E), (1 : ZMod 2)) + ε • a).1
          ((v + (lam * β a.1 v.1) • ((0 : E), (1 : ZMod 2)) + ε • a).2 +
            Q (v + (lam * β a.1 v.1) • ((0 : E), (1 : ZMod 2)) + ε • a).1) * z ^ ε.val := by
  have key : ∀ (v : E × ZMod 2) (ε : ZMod 2), m v.1 (v.2 + Q v.1) * z ^ ε.val =
      ((θ₁.symm (Multiplicative.ofAdd (v, ε)) : B₁) : G) := by
    rintro ⟨w, c⟩ ε
    have hc : c + Q w + Q w = c := by
      generalize Q w = q
      revert c q
      decide
    rw [hθ₁, ← hψ w (c + Q w), hc]
  intro d hd a v ε h
  rw [key a 1] at h
  have h2 : a = ν₁ d := congrArg Prod.fst (Multiplicative.ofAdd.injective
    (θ₁.symm.injective (Subtype.ext (h.symm.trans (hν₁ d hd)))))
  rw [key v ε, key _ ε, h2]
  exact hact d hd v ε

end SteinbergCH

theorem standard_binary_symplectic_six_elementary_lagrangian_Suzuki_ambient_exclusion
    (hF : Sp6LagrangianFullOddCoreStmt) {G : Type} [Group G] [Finite G]
    (hGs : IsSimpleGroup G) (hGn : ∃ x y : G, x * y ≠ y * x)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hcore : ∀ t : G, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set G)) = ⊥)
    (_hcyc : ∃ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (_htype : CFSG.Blueprint.Recognition.Exact.EvenStandardType (L ⧸ center L))
    (_hexc : ¬ CFSG.Blueprint.Recognition.Exact.EvenStandardException (L ⧸ center L))
    (_hres : CFSG.Blueprint.Recognition.Exact.EvenStandardResidual L)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel (L ⧸ center L) .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
    (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (he : IsSymplecticBasis b e)
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
        ∀ p f : ℕ, ¬ CFSG.Blueprint.SuzukiModel (sp6Dstar φ he z) p f ∧
          ¬ CFSG.Blueprint.LieModel (sp6Dstar φ he z) .twistedB2 0 p f) := by
  have hzC : z ∈ centralizer (L : Set G) := by
    obtain ⟨t, -, rfl⟩ := hzT
    exact t.2
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hG : CFSG.oddCore G = ⊥ := SteinbergCH.oddCore_eq_bot_of_involution hGs hz
  have hLn : ¬ L.Normal := SteinbergCH.not_normal_of_mem_centralizer hGs hGn hL.1 hzC hz1
  have hmodelL : CFSG.Blueprint.LieModel L .PSp 3 2 1 :=
    SteinbergCH.lieModel_of_center_eq_bot hZ hmodel
  have hH := hcore z hz
  obtain ⟨hTz, -, hsup, hinf, hrest⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths hG hL hLn hZ hmodelL T hT hzT hz hH
  obtain ⟨-, hW⟩ := hrest hb hnd hV φ
  obtain ⟨-, -, -, -, -, -, -, -, -, hker, -, -, -, ⟨σ, -, -, -, hσ⟩, -⟩ :=
    hW (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf e he rfl
  obtain ⟨κ, D₂, _, ν₂', hD₂, -, -, -, -, -, -, -, hν₂z, -, -, hact₂, -⟩ :=
    degree64_lagrangian_two_group φ he hzC hz hinf hker σ hσ hfull
  subst hD₂
  have hκ := SteinbergCH.kappa_action φ he hzC hz hinf hν₂z hact₂
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ψ, θ₁, hψ, hθ₁, lam, D₁, _, ν₁, hD₁, -, -,
      -, -, -, -, -, -, -, -, hν₁z, -, -, hact₁, -⟩ :=
    standard_binary_symplectic_six_degree64_other_parabolic_normalizer hG hL hLn hZ hmodelL T hT
      hzT hz hH hb hnd hV φ e he hfull
  subst hD₁
  have hlam := SteinbergCH.lam_action ψ θ₁
    (fun w c => ((φ.symm (pointElt hb (mem_pairOrth_left w.2) c) : L) : G))
    (fun w => e.repr w (Sum.inl 1) * e.repr w (Sum.inr 1) +
      e.repr w (Sum.inl 2) * e.repr w (Sum.inr 2))
    (fun w w' => b (w : V) (w' : V)) lam ν₁ hψ hθ₁ hν₁z hact₁
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
  intro hC₂el hDs hDn p f
  have hε0 : ε = 0 := by
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
    have hw : symThreeDiag (ν₂ c : M₃) ≠ 0 := by
      intro hw
      apply hcF
      refine ⟨hcD, ν₂ c, hw, ?_⟩
      exact (hν₂ c hcD).symm
    have hc2 : c ^ 2 = 1 :=
      CFSG.elemPow_eq_one_of_isElementaryAbelian (A := sp6C₂ φ he z) c (by rw [hCeq]; exact hcC)
    have hS : symThreeSquare ε (symThreeDiag (ν₂ c : M₃)) = 0 := by
      have h : tauHom φ he (Multiplicative.ofAdd (symThreeSquare ε (symThreeDiag (ν₂ c : M₃)))) *
          z ^ (0 : ZMod 2).val = 1 := (hsq c hcC).symm.trans hc2
      rw [ZMod.val_zero, pow_zero, mul_one, ← map_one (tauHom φ he)] at h
      exact Multiplicative.ofAdd.injective (tauHom_injective φ he h)
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) ε with h0 | h1
    · exact h0
    · exfalso
      subst h1
      apply hw
      have hv := congrArg Subtype.val hS
      rw [coe_symThreeSquare, one_smul, ZeroMemClass.coe_zero] at hv
      exact (vecMulVec_self_eq_zero_iff _).mp hv
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, hconc⟩ := hε hε0
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, haBar2, hJC, -, hCaBar, -, -, -,
      -, -, -, hJstd, -, -, -, -, hCD, -⟩ := hconc
  have : (sp6Dstar φ he z).Normal := Subgroup.normalClosure_normal
  exact CFSG.LocalAnalysis.ComponentInitial.SteinbergCH.layer_not_suzukiModel hDs hDn hCD haBar2
    (fun x hx => Subgroup.subset_normalClosure hx) ⟨hJstd.1.1.commutator_eq_top, hJstd.1.2.1⟩ hJC
    hCaBar.symm p f

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
