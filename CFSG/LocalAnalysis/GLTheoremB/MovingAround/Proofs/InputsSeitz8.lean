module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz7b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.ClassicalEA
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.OrthCentGen
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import Certificates.Certificate9415
public import Certificates.Certificate19954
import CFSG.GF2Type.Smith1980Orth.TriD4Rank
import CFSG.HardMathSupport.Seitz.TrialityEven.TwoThree
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellG2
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.D44Outer
import CFSG.Adapters.TauCetiLieModels
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.RankCube
public import CFSG.HardMathSupport.Dickson.I271.SporGenBM
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.RkBM
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveHN
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveShape
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3All
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26AutMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Easy
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCheck
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporThreeSmall
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1113
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
public import CFSG.Quasithin.SteinbergCBGDTrace
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
import CFSG.Quasithin.Recognition.CertTriality
import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
import CFSG.Quasithin.Recognition.CertTrialityFaithful
import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicOpen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz8

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration (fixSub polarNondegOn_fixSub)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalEA (Nondeg IsBlock HasBlocks ptw mem_ptw
  hasBlocks_of_max nondeg_top orth_orth isRestrClosed_orthogonalGroup polarBilin_symm orbitSum_eq_zero)

set_option linter.unusedSectionVars false

section Geom

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem zmodTwo_eq_zero_or_one_orthF2 (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem map_add_eq_zero_orthF2 {a c : V} (ha : Q a ≠ 0) (hc : Q c ≠ 0) (hac : polar Q a c = 0) :
    Q (a + c) = 0 := by
  rw [QuadraticMap.map_add Q a c, (zmodTwo_eq_zero_or_one_orthF2 _).resolve_left ha,
    (zmodTwo_eq_zero_or_one_orthF2 _).resolve_left hc, hac]
  decide

theorem exists_hypPair_fixed_orthF2 (hQ : (polarBilin Q).Nondegenerate) {F : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hFO : F ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hodd : Odd (Nat.card F)) {e : V} (he0 : e ≠ 0)
    (heQ : Q e = 0) (heF : ∀ g ∈ F, g e = e) :
    ∃ P : HypPair Q, ∀ g ∈ F, g P.e = P.e ∧ g P.f = P.f := by
  have hW := polarNondegOn_fixSub hQ hFO hodd
  obtain ⟨h, hhW, hh⟩ := hW.exists_polar_ne_zero
    (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.mem_fixSub.2 heF) he0
  have h1 : polar Q e h = 1 := (zmodTwo_eq_zero_or_one_orthF2 _).resolve_left hh
  refine ⟨HypPair.ofPolarEqOne heQ h1, fun g hg => ⟨heF g hg, ?_⟩⟩
  rw [HypPair.ofPolarEqOne_f, map_sub, map_smul, heF g hg,
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.mem_fixSub.1 hhW g hg]

theorem add_self_orthF2 (x : V) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x]
  have : (2 : ZMod 2) = 0 := rfl
  rw [this, zero_smul]

theorem neg_eq_self_orthF2 (x : V) : -x = x :=
  neg_eq_of_add_eq_zero_left (add_self_orthF2 x)

theorem polar_self_orthF2 (x : V) : polar Q x x = 0 := by
  rw [polar_self_eq_two_mul]
  have : (2 : ZMod 2) = 0 := rfl
  rw [this, zero_mul]

theorem sq_apply_orthF2 {b : V ≃ₗ[ZMod 2] V} (hb3 : b ^ 3 = 1) {W : Submodule (ZMod 2) V}
    (hbW : ∀ w ∈ W, b w ∈ W) (hfpf : ∀ w ∈ W, b w = w → w = 0) {a : V} (haW : a ∈ W) :
    (b ^ 2) a = a + b a := by
  have h := orbitSum_eq_zero hb3 hbW hfpf haW
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    LinearEquiv.coe_one, id_eq] at h
  rw [← neg_eq_self_orthF2 (a + b a)]
  exact eq_neg_of_add_eq_zero_right h

theorem block_eq_span_pair_orthF2 {b : V ≃ₗ[ZMod 2] V} (hbO : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hb3 : b ^ 3 = 1) {W : Submodule (ZMod 2) V} (hW : IsBlock (polarBilin Q) b W)
    (haniso : ∀ w ∈ W, w ≠ 0 → Q w ≠ 0) {a : V} (haW : a ∈ W) (ha0 : a ≠ 0) :
    W = Submodule.span (ZMod 2) {a, b a} := by
  obtain ⟨-, -, hbW, -, hfpf, hmin⟩ := hW
  have hb2 := sq_apply_orthF2 hb3 hbW hfpf haW
  have hQa : Q a = 1 := (zmodTwo_eq_zero_or_one_orthF2 _).resolve_left (haniso a haW ha0)
  have hpol : polar Q a (b a) = 1 := by
    have h1 : polar Q a (b a) = Q ((b ^ 2) a) - Q a - Q (b a) := by
      rw [hb2]
      rfl
    rw [h1, map_of_mem (pow_mem hbO 2), map_of_mem hbO, hQa]
    decide
  have hpol' : polar Q (b a) a = 1 := by rw [polar_comm, hpol]
  symm
  refine hmin _ ?_ ?_ ?_ ?_
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact haW
    · exact hbW _ haW
  · intro h
    apply ha0
    have : a ∈ Submodule.span (ZMod 2) {a, b a} := Submodule.subset_span (Set.mem_insert _ _)
    rw [h, Submodule.mem_bot] at this
    exact this
  · rw [ClassicalEA.nondeg_iff]
    intro w hw hperp
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hw
    have h1 := hperp a (Submodule.subset_span (Set.mem_insert _ _))
    have h2 := hperp (b a) (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
    rw [polarBilin_apply_apply, polar_add_right, polar_smul_right, polar_smul_right,
      polar_self_orthF2, hpol] at h1
    rw [polarBilin_apply_apply, polar_add_right, polar_smul_right, polar_smul_right,
      polar_self_orthF2, hpol'] at h2
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, add_zero] at h1 h2
    rw [h1, h2, zero_smul, zero_smul, add_zero]
  · have hle : Submodule.span (ZMod 2) {a, b a} ≤
        (Submodule.span (ZMod 2) {a, b a}).comap b.toLinearMap := by
      rw [Submodule.span_le]
      rintro x (rfl | rfl)
      · exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
      · show b (b a) ∈ Submodule.span (ZMod 2) {a, b a}
        rw [← LinearEquiv.mul_apply, ← pow_two, hb2]
        exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_insert _ _))
          (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
    exact fun w hw => hle hw

theorem card_sup_le_mul_orthF2 {G : Type*} [Group G] [Finite G] {A C : Subgroup G}
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) : Nat.card ↥(A ⊔ C) ≤ Nat.card A * Nat.card C := by
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A C hAC).1
  have h1 : 1 ≤ Nat.card ↥(A ⊓ C) := Nat.card_pos
  calc Nat.card ↥(A ⊔ C) = Nat.card ↥(A ⊔ C) * 1 := (mul_one _).symm
    _ ≤ Nat.card ↥(A ⊔ C) * Nat.card ↥(A ⊓ C) := Nat.mul_le_mul_left _ h1
    _ = Nat.card A * Nat.card C := h

theorem card_zpowers_le_three_orthF2 {G : Type*} [Group G] {g : G} (hg : g ^ 3 = 1) :
    Nat.card (Subgroup.zpowers g) ≤ 3 := by
  rw [Nat.card_zpowers]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg)

theorem polar_apply_eq_one_orthF2 {b : V ≃ₗ[ZMod 2] V} (hbO : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hb3 : b ^ 3 = 1) {W : Submodule (ZMod 2) V} (hbW : ∀ w ∈ W, b w ∈ W)
    (hfpf : ∀ w ∈ W, b w = w → w = 0) (haniso : ∀ w ∈ W, w ≠ 0 → Q w ≠ 0) {a : V} (haW : a ∈ W)
    (ha0 : a ≠ 0) : polar Q a (b a) = 1 := by
  have hb2 := sq_apply_orthF2 hb3 hbW hfpf haW
  have hQa : Q a = 1 := (zmodTwo_eq_zero_or_one_orthF2 _).resolve_left (haniso a haW ha0)
  have h1 : polar Q a (b a) = Q ((b ^ 2) a) - Q a - Q (b a) := by
    rw [hb2]
    rfl
  rw [h1, map_of_mem (pow_mem hbO 2), map_of_mem hbO, hQa]
  decide

theorem exists_swap_eichler_orthF2 {b₀ b₁ : V ≃ₗ[ZMod 2] V}
    (hb₀O : b₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hb₁O : b₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hb₀3 : b₀ ^ 3 = 1) (hb₁3 : b₁ ^ 3 = 1) {W₀ W₁ : Submodule (ZMod 2) V}
    (hb₀W : ∀ w ∈ W₀, b₀ w ∈ W₀) (hb₁W : ∀ w ∈ W₁, b₁ w ∈ W₁)
    (hfpf₀ : ∀ w ∈ W₀, b₀ w = w → w = 0) (hfpf₁ : ∀ w ∈ W₁, b₁ w = w → w = 0)
    (hfix₀ : ∀ w ∈ W₀, b₁ w = w) (hfix₁ : ∀ w ∈ W₁, b₀ w = w)
    (horth : ∀ x ∈ W₀, ∀ y ∈ W₁, polar Q x y = 0)
    (haniso₀ : ∀ w ∈ W₀, w ≠ 0 → Q w ≠ 0) (haniso₁ : ∀ w ∈ W₁, w ≠ 0 → Q w ≠ 0)
    {a₀ a₁ : V} (ha₀W : a₀ ∈ W₀) (ha₁W : a₁ ∈ W₁) (ha₀0 : a₀ ≠ 0) (ha₁0 : a₁ ≠ 0) :
    ∃ u ∈ elementaryGroup Q, u ≠ 1 ∧ u * u = 1 ∧ (b₀ * b₁) * u = u * (b₀ * b₁) ∧
      ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, (∀ x ∈ W₀, g x = x) → (∀ x ∈ W₁, g x = x) →
        g * u = u * g := by
  set e := a₀ + a₁ with he
  set w := b₀ a₀ + b₁ a₁ with hw
  clear_value e w
  have hba₀ : b₀ a₀ ∈ W₀ := hb₀W _ ha₀W
  have hba₁ : b₁ a₁ ∈ W₁ := hb₁W _ ha₁W
  have hQa₀ : Q a₀ = 1 := (zmodTwo_eq_zero_or_one_orthF2 _).resolve_left (haniso₀ a₀ ha₀W ha₀0)
  have hQa₁ : Q a₁ = 1 := (zmodTwo_eq_zero_or_one_orthF2 _).resolve_left (haniso₁ a₁ ha₁W ha₁0)
  have hp₀ := polar_apply_eq_one_orthF2 hb₀O hb₀3 hb₀W hfpf₀ haniso₀ ha₀W ha₀0
  have hp₁ := polar_apply_eq_one_orthF2 hb₁O hb₁3 hb₁W hfpf₁ haniso₁ ha₁W ha₁0
  have hp₀' : polar Q (b₀ a₀) a₀ = 1 := by rw [polar_comm, hp₀]
  have hp₁' : polar Q (b₁ a₁) a₁ = 1 := by rw [polar_comm, hp₁]
  have hx01 : ∀ x ∈ W₀, ∀ y ∈ W₁, polar Q y x = 0 := fun x hx y hy => by rw [polar_comm, horth x hx y hy]
  have heQ : Q e = 0 := by
    rw [he, QuadraticMap.map_add Q, hQa₀, hQa₁, horth _ ha₀W _ ha₁W]
    decide
  have hwQ : Q w = 0 := by
    rw [hw, QuadraticMap.map_add Q, map_of_mem hb₀O, map_of_mem hb₁O, hQa₀, hQa₁,
      horth _ hba₀ _ hba₁]
    decide
  have hew : polar Q e w = 0 := by
    rw [he, hw, polar_add_left, polar_add_right, polar_add_right, hp₀, hp₁, horth _ ha₀W _ hba₁,
      hx01 _ hba₀ _ ha₁W]
    decide
  have hwe : polar Q w e = 0 := by rw [polar_comm, hew]
  set u := eichler Q e w with hu
  refine ⟨u, eichler_mem_elementaryGroup Q e w, ?_,
    CFSG.HardMathSupport.Timmesfeld.Coordinator.eichler_mul_self_of_two_eq_zero (by decide) e w, ?_, ?_⟩
  ·
    intro h1
    have hua : u a₀ = a₁ := by
      have h1 : polar Q a₀ e = 0 := by
        rw [he, polar_add_right, polar_self_orthF2, horth _ ha₀W _ ha₁W, add_zero]
      have h2 : polar Q a₀ w = 1 := by
        rw [hw, polar_add_right, hp₀, horth _ ha₀W _ hba₁, add_zero]
      rw [hu, eichler_apply heQ hew, h1, h2, hwQ, zero_smul, add_zero, zero_mul, add_zero, one_smul, he,
        sub_eq_add_neg, neg_eq_self_orthF2, ← add_assoc, add_self_orthF2, zero_add]
    rw [h1] at hua
    have h01 : a₁ ∈ W₀ := hua ▸ ha₀W
    exact ha₁0 (hfpf₁ a₁ ha₁W (hfix₀ a₁ h01))
  ·
    have hg : b₀ * b₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem hb₀O hb₁O
    have hge : (b₀ * b₁) e = w := by
      rw [LinearEquiv.mul_apply, he, map_add, map_add, hfix₀ a₀ ha₀W, hfix₁ _ hba₁, hw]
    have hgw : (b₀ * b₁) w = e + w := by
      rw [LinearEquiv.mul_apply, hw, map_add, map_add, hfix₀ _ hba₀, hfix₁ _ (hb₁W _ hba₁)]
      have h0 : b₀ (b₀ a₀) = a₀ + b₀ a₀ := by
        rw [← LinearEquiv.mul_apply, ← pow_two]
        exact sq_apply_orthF2 hb₀3 hb₀W hfpf₀ ha₀W
      have h1 : b₁ (b₁ a₁) = a₁ + b₁ a₁ := by
        rw [← LinearEquiv.mul_apply, ← pow_two]
        exact sq_apply_orthF2 hb₁3 hb₁W hfpf₁ ha₁W
      rw [h0, h1, he]
      abel
    have hconj := eichler_conj hg e w
    rw [hge, hgw] at hconj
    have hEq : eichler Q w (e + w) = u := by
      have hwew : polar Q w (e + w) = 0 := by rw [polar_add_right, hwe, polar_self_orthF2, add_zero]
      have hQew : Q (e + w) = 0 := by
        rw [QuadraticMap.map_add Q, heQ, hwQ, hew]
        decide
      refine LinearEquiv.ext fun x => ?_
      rw [hu, eichler_apply hwQ hwew, eichler_apply heQ hew, hQew, hwQ, zero_mul, zero_mul, add_zero,
        add_zero]
      rw [polar_add_right, smul_add, add_smul, sub_eq_add_neg, sub_eq_add_neg, neg_eq_self_orthF2,
        neg_eq_self_orthF2]
      have h2 : polar Q x w • w + polar Q x w • w = 0 := add_self_orthF2 _
      calc x + (polar Q x w • e + polar Q x w • w) + (polar Q x e • w + polar Q x w • w) =
            x + polar Q x e • w + polar Q x w • e + (polar Q x w • w + polar Q x w • w) := by abel
        _ = x + polar Q x e • w + polar Q x w • e := by rw [h2, add_zero]
    rw [hEq] at hconj
    calc b₀ * b₁ * u = b₀ * b₁ * u * (b₀ * b₁)⁻¹ * (b₀ * b₁) := by group
      _ = u * (b₀ * b₁) := by rw [hconj]
  · intro g hg hg₀ hg₁
    have hconj := eichler_conj hg e w
    have hge : g e = e := by rw [he, map_add, hg₀ a₀ ha₀W, hg₁ a₁ ha₁W]
    have hgw : g w = w := by rw [hw, map_add, hg₀ _ hba₀, hg₁ _ hba₁]
    rw [hge, hgw] at hconj
    calc g * u = g * u * g⁻¹ * g := by group
      _ = u * g := by rw [← hu] at hconj; rw [hconj]

theorem exists_fixed_hypPair_or_swap_of_maxEA_orthF2 (hQ : (polarBilin Q).Nondegenerate)
    {D : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hDO : D ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hD : IsElemAbelian 3 D) {r : ℕ}
    (hDc : Nat.card D = 3 ^ r) (hr : 4 ≤ r)
    (hmax : ∀ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      IsElemAbelian 3 F → Nat.card F ≤ Nat.card D) :
    (∃ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ D ∧ 27 ≤ Nat.card F ∧
      ∃ P : HypPair Q, ∀ g ∈ F, g P.e = P.e ∧ g P.f = P.f) ∨
    (finrank (ZMod 2) V ≤ 8 ∧ ∃ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ D ∧ 27 ≤ Nat.card F ∧
      ∃ u ∈ elementaryGroup Q, u ≠ 1 ∧ u * u = 1 ∧ ∀ g ∈ F, g * u = u * g) := by
  classical
  haveI : Finite (V ≃ₗ[ZMod 2] V) := ClassicalEA.finite_linearEquiv
  have hBs := polarBilin_symm Q
  have horthTop : ∀ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) ⊤, x = 0 := fun x hx =>
    hQ.2 x fun u => hx u Submodule.mem_top
  have hDU : D ≤ TauCeti.QuadraticMap.orthogonalGroup Q ⊓ ptw (LinearMap.BilinForm.orthogonal (polarBilin Q) ⊤) :=
    fun g hg => ⟨hDO hg, fun x hx => by rw [horthTop x hx, map_zero]⟩
  obtain ⟨r', b, W, hbD, hblock, -, horth, hDcl, hDc'⟩ := hasBlocks_of_max hBs hQ Nat.prime_three
    (by norm_num) (isRestrClosed_orthogonalGroup Q) _ ⊤ rfl (nondeg_top hBs hQ) D hDU hD
    (fun F hF hFe => hmax F (hF.trans inf_le_left) hFe)
  have hrr : r' = r := by
    rw [hDc] at hDc'
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hDc').symm
  have hr' : 4 ≤ r' := hrr ▸ hr
  have hDc3 : Nat.card D = 3 ^ r' := hDc'
  have hb3 : ∀ i, b i ^ 3 = 1 := fun i => hD.2 _ (hbD i)
  have hbO : ∀ i, b i ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun i => hDO (hbD i)
  have hcommD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy => hD.comm hx hy
  have hfixW : ∀ i j, i ≠ j → ∀ x ∈ W i, b j x = x := fun i j hij x hx =>
    (hblock j).2.2.2.1 x (horth i j hij hx)
  let FS : Set (Fin r') → Subgroup (V ≃ₗ[ZMod 2] V) := fun S => Subgroup.closure (b '' S)
  have hFSD : ∀ S, FS S ≤ D := fun S => by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, -, rfl⟩
    exact hbD j
  have hFSfix : ∀ S i, i ∉ S → ∀ g ∈ FS S, ∀ x ∈ W i, g x = x := by
    intro S i hi g hg x hx
    have hle : FS S ≤ ptw (W i) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      exact fun y hy => hfixW i j (fun h => hi (h ▸ hj)) y hy
    exact hle hg x hx
  have hFSodd : ∀ S, Odd (Nat.card (FS S)) := fun S => by
    have hdvd : Nat.card (FS S) ∣ 3 ^ r' := hDc3 ▸ Subgroup.card_dvd_of_le (hFSD S)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    rw [hk]
    exact Odd.pow (by decide)
  have hFSO : ∀ S, FS S ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun S => (hFSD S).trans hDO
  have hcard1 : ∀ i, 3 ^ (r' - 1) ≤ Nat.card (FS {j | j ≠ i}) := by
    intro i
    have hle : D ≤ FS {j | j ≠ i} ⊔ Subgroup.zpowers (b i) := by
      rw [hDcl, Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      by_cases hji : j = i
      · subst hji
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨j, hji, rfl⟩)
    have h1 := (Subgroup.card_le_of_le hle).trans (card_sup_le_mul_orthF2 fun x hx y hy =>
      hcommD x (hFSD _ hx) y (Subgroup.zpowers_le.2 (hbD i) hy))
    have h2 := card_zpowers_le_three_orthF2 (hb3 i)
    have h3 : 3 ^ r' ≤ Nat.card (FS {j | j ≠ i}) * 3 :=
      hDc3 ▸ h1.trans (Nat.mul_le_mul_left _ h2)
    have h4 : 3 ^ r' = 3 ^ (r' - 1) * 3 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h4] at h3
    exact Nat.le_of_mul_le_mul_right h3 (by norm_num)
  have hcard2 : ∀ i j, 3 ^ (r' - 2) ≤ Nat.card (FS {k | k ≠ i ∧ k ≠ j}) := by
    intro i j
    have hle : D ≤ FS {k | k ≠ i ∧ k ≠ j} ⊔ (Subgroup.zpowers (b i) ⊔ Subgroup.zpowers (b j)) := by
      rw [hDcl, Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      by_cases hki : k = i
      · subst hki
        exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      · by_cases hkj : k = j
        · subst hkj
          exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨k, ⟨hki, hkj⟩, rfl⟩)
    have hzle : Subgroup.zpowers (b i) ⊔ Subgroup.zpowers (b j) ≤ D :=
      sup_le (Subgroup.zpowers_le.2 (hbD i)) (Subgroup.zpowers_le.2 (hbD j))
    have h1 := (Subgroup.card_le_of_le hle).trans (card_sup_le_mul_orthF2 fun x hx y hy =>
      hcommD x (hFSD _ hx) y (hzle hy))
    have h2 : Nat.card ↥(Subgroup.zpowers (b i) ⊔ Subgroup.zpowers (b j)) ≤ 9 :=
      (card_sup_le_mul_orthF2 fun x hx y hy =>
        hcommD x (Subgroup.zpowers_le.2 (hbD i) hx) y (Subgroup.zpowers_le.2 (hbD j) hy)).trans
        (Nat.mul_le_mul (card_zpowers_le_three_orthF2 (hb3 i)) (card_zpowers_le_three_orthF2 (hb3 j)))
    have h3 : 3 ^ r' ≤ Nat.card (FS {k | k ≠ i ∧ k ≠ j}) * 9 :=
      hDc3 ▸ h1.trans (Nat.mul_le_mul_left _ h2)
    have h4 : 3 ^ r' = 3 ^ (r' - 2) * 9 := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    rw [h4] at h3
    exact Nat.le_of_mul_le_mul_right h3 (by norm_num)
  have h27 : ∀ k, 3 ≤ k → 27 ≤ 3 ^ k := fun k hk =>
    (show 27 = 3 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hk
  have hfin : ∀ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ D → 27 ≤ Nat.card F → Odd (Nat.card F) →
      ∀ e : V, e ≠ 0 → Q e = 0 → (∀ g ∈ F, g e = e) →
      ∃ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ D ∧ 27 ≤ Nat.card F ∧
        ∃ P : HypPair Q, ∀ g ∈ F, g P.e = P.e ∧ g P.f = P.f :=
    fun F hFD hF27 hFodd e he0 heQ heF =>
      ⟨F, hFD, hF27, exists_hypPair_fixed_orthF2 hQ (hFD.trans hDO) hFodd he0 heQ heF⟩
  set i₀ : Fin r' := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin r' := ⟨1, by omega⟩ with hi₁
  have hi01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  by_cases hsing : ∃ i, ∃ a ∈ W i, a ≠ 0 ∧ Q a = 0
  · obtain ⟨i, a, haW, ha0, haQ⟩ := hsing
    exact Or.inl (hfin _ (hFSD _) ((h27 _ (by omega)).trans (hcard1 i)) (hFSodd _) a ha0 haQ
      (fun g hg => hFSfix _ i (by simp) g hg a haW))
  push Not at hsing
  have haniso : ∀ i, ∀ w ∈ W i, w ≠ 0 → Q w ≠ 0 := fun i w hw hw0 => hsing i w hw hw0
  have hne : ∀ i, ∃ a ∈ W i, a ≠ 0 := fun i => Submodule.exists_mem_ne_zero_of_ne_bot (hblock i).2.1
  by_cases hfixc : ∃ c : V, c ≠ 0 ∧ ∀ g ∈ D, g c = c
  · obtain ⟨c, hc0, hcD⟩ := hfixc
    by_cases hcQ : Q c = 0
    · exact Or.inl
        (hfin D le_rfl (hDc3 ▸ h27 _ (by omega)) (by rw [hDc3]; exact Odd.pow (by decide)) c hc0 hcQ hcD)
    refine Or.inl ?_
    obtain ⟨a, haW, ha0⟩ := hne i₀
    obtain ⟨-, -, hbW, -, hfpf, -⟩ := hblock i₀
    have hac : polar Q a c = 0 := by
      have h := orbitSum_eq_zero (hb3 i₀) hbW hfpf haW
      have h1 : polar Q (∑ k ∈ Finset.range 3, (b i₀ ^ k) a) c = polar Q a c := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, polar_add_left,
          polar_add_left]
        have hk : ∀ k : ℕ, polar Q ((b i₀ ^ k) a) c = polar Q a c := fun k => by
          conv_lhs => rw [← ClassicalEA.pow_apply_eq_self (hcD _ (hbD i₀)) k]
          exact polar_map_of_mem (pow_mem (hbO i₀) k) a c
        rw [hk, hk, hk]
        have : ∀ x : ZMod 2, x + x + x = x := by decide
        exact this _
      rw [← h1, h, polar_zero_left]
    refine hfin _ (hFSD _) ((h27 _ (by omega)).trans (hcard1 i₀)) (hFSodd _) (a + c) ?_
      (map_add_eq_zero_orthF2 (haniso i₀ a haW ha0) hcQ hac) ?_
    · intro h
      have hca : c = a := by
        rw [← neg_eq_self_orthF2 a]
        exact eq_neg_of_add_eq_zero_right h
      apply ha0
      refine hfpf a haW ?_
      rw [← hca]
      exact hcD _ (hbD i₀)
    · intro g hg
      rw [map_add, hFSfix _ i₀ (by simp) g hg a haW, hcD g (hFSD _ hg)]
  have hfixc' : ∀ c : V, (∀ g ∈ D, g c = c) → c = 0 := fun c hc => by
    by_contra h
    exact hfixc ⟨c, h, hc⟩
  have hdimle : finrank (ZMod 2) V ≤ 2 * r' := by
    choose a haW ha0 using hne
    have hspan : ∀ i, W i = Submodule.span (ZMod 2) {a i, b i (a i)} := fun i =>
      block_eq_span_pair_orthF2 (hbO i) (hb3 i) (hblock i) (haniso i) (haW i) (ha0 i)
    have htop : (⨆ i, W i) = ⊤ := by
      have horthsup : LinearMap.BilinForm.orthogonal (polarBilin Q) (⨆ i, W i) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Submodule.mem_bot]
        refine hfixc' x ?_
        have hle : D ≤ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) x := by
          rw [hDcl, Subgroup.closure_le]
          rintro _ ⟨i, rfl⟩
          refine (hblock i).2.2.2.1 x fun w hw => hx w ?_
          exact Submodule.mem_iSup_of_mem i hw
        exact fun g hg => hle hg
      rw [← orth_orth hBs hQ (⨆ i, W i), horthsup]
      exact LinearMap.BilinForm.orthogonal_bot
    let v : Fin r' × Bool → V := fun p => if p.2 then b p.1 (a p.1) else a p.1
    have hle : (⊤ : Submodule (ZMod 2) V) ≤ Submodule.span (ZMod 2) (Set.range v) := by
      rw [← htop, iSup_le_iff]
      intro i
      rw [hspan i, Submodule.span_le]
      rintro x (rfl | rfl)
      · exact Submodule.subset_span ⟨(i, false), rfl⟩
      · exact Submodule.subset_span ⟨(i, true), rfl⟩
    have h1 := finrank_range_le_card (R := ZMod 2) v
    have h2 : finrank (ZMod 2) V ≤ (Set.range v).finrank (ZMod 2) := by
      rw [← finrank_top (ZMod 2) V]
      exact Submodule.finrank_mono hle
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h1
    omega
  obtain ⟨a₀, ha₀W, ha₀0⟩ := hne i₀
  obtain ⟨a₁, ha₁W, ha₁0⟩ := hne i₁
  have hpol : polar Q a₀ a₁ = 0 := by
    rw [polar_comm]
    exact horth i₀ i₁ hi01 ha₀W a₁ ha₁W
  by_cases hr5 : 5 ≤ r'
  · refine Or.inl (hfin _ (hFSD _) ((h27 _ (by omega)).trans (hcard2 i₀ i₁)) (hFSodd _) (a₀ + a₁) ?_
      (map_add_eq_zero_orthF2 (haniso i₀ a₀ ha₀W ha₀0) (haniso i₁ a₁ ha₁W ha₁0) hpol) ?_)
    · intro h
      have h10 : a₁ = a₀ := by
        rw [← neg_eq_self_orthF2 a₀]
        exact eq_neg_of_add_eq_zero_right h
      apply ha₁0
      have hmem : a₁ ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (W i₁) := h10 ▸ horth i₀ i₁ hi01 ha₀W
      exact (Submodule.disjoint_def.1 (hblock i₁).1) a₁ ha₁W hmem
    · intro g hg
      rw [map_add, hFSfix _ i₀ (by simp) g hg a₀ ha₀W,
        hFSfix _ i₁ (by simp) g hg a₁ ha₁W]
  refine Or.inr ⟨by omega, ?_⟩
  obtain ⟨-, -, hbW₀, -, hfpf₀, -⟩ := hblock i₀
  obtain ⟨-, -, hbW₁, -, hfpf₁, -⟩ := hblock i₁
  obtain ⟨u, huE, hu1, hu2, hu01, hug⟩ := exists_swap_eichler_orthF2 (hbO i₀) (hbO i₁) (hb3 i₀) (hb3 i₁)
    hbW₀ hbW₁ hfpf₀ hfpf₁ (hfixW i₀ i₁ hi01) (hfixW i₁ i₀ hi01.symm)
    (fun x hx y hy => by rw [polar_comm]; exact horth i₀ i₁ hi01 hx y hy) (haniso i₀) (haniso i₁)
    ha₀W ha₁W ha₀0 ha₁0
  set F : Subgroup (V ≃ₗ[ZMod 2] V) :=
    Subgroup.closure ({b i₀ * b i₁} ∪ b '' {k | k ≠ i₀ ∧ k ≠ i₁}) with hFdef
  have hFD : F ≤ D := by
    rw [hFdef, Subgroup.closure_le]
    rintro _ (h | ⟨k, -, rfl⟩)
    · rw [Set.mem_singleton_iff.1 h]
      exact mul_mem (hbD i₀) (hbD i₁)
    · exact hbD k
  have hFu : ∀ g ∈ F, g * u = u * g := by
    have hle : F ≤ Subgroup.centralizer {u} := by
      rw [hFdef, Subgroup.closure_le]
      rintro _ (h | ⟨k, ⟨hk0, hk1⟩, rfl⟩)
      · rw [Set.mem_singleton_iff.1 h, SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact hu01
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact hug (b k) (hbO k) (hfixW i₀ k (Ne.symm hk0)) (hfixW i₁ k (Ne.symm hk1))
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
  have hleD : D ≤ F ⊔ Subgroup.zpowers (b i₀) := by
    rw [hDcl, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    by_cases hk0 : k = i₀
    · rw [hk0]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    by_cases hk1 : k = i₁
    · rw [hk1]
      have : b i₁ = (b i₀)⁻¹ * (b i₀ * b i₁) := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers _)))
        (Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inl rfl)))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inr ⟨k, ⟨hk0, hk1⟩, rfl⟩))
  have hF27 : 27 ≤ Nat.card F := by
    have h1 := (Subgroup.card_le_of_le hleD).trans (card_sup_le_mul_orthF2 fun x hx y hy =>
      hcommD x (hFD hx) y (Subgroup.zpowers_le.2 (hbD i₀) hy))
    have h2 := card_zpowers_le_three_orthF2 (hb3 i₀)
    have h3 : 3 ^ r' ≤ Nat.card F * 3 := hDc3 ▸ h1.trans (Nat.mul_le_mul_left _ h2)
    have h4 : 81 ≤ 3 ^ r' := (show 81 = 3 ^ 4 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hr'
    omega
  exact ⟨F, hFD, hF27, u, huE, hu1, hu2, hFu⟩

theorem exists_fixed_hypPair_of_maxEA_orthF2 (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 10 ≤ finrank (ZMod 2) V) {D : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hDO : D ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hD : IsElemAbelian 3 D) {r : ℕ}
    (hDc : Nat.card D = 3 ^ r) (hr : 4 ≤ r)
    (hmax : ∀ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      IsElemAbelian 3 F → Nat.card F ≤ Nat.card D) :
    ∃ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ D ∧ 27 ≤ Nat.card F ∧
      ∃ P : HypPair Q, ∀ g ∈ F, g P.e = P.e ∧ g P.f = P.f :=
  (exists_fixed_hypPair_or_swap_of_maxEA_orthF2 hQ hDO hD hDc hr hmax).resolve_right fun h => by
    have := h.1
    omega

end Geom

section Gen

theorem le_centGenI_of_lift_orthF2 {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : commutator ↥K = ⊤) (hZ : Odd (Nat.card (Subgroup.center ↥K)))
    {A : Subgroup X} (hAel : IsElemAbelian 3 A) (hAK : A ≤ Subgroup.normalizer (K : Set X))
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (polarBilin Q).Nondegenerate)
    (φ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(elementaryGroup Q))
    (Yh : ↥A →* ↥(elementaryGroup Q))
    (hYh : ∀ (a : ↥A) (k : ↥K),
      φ (QuotientGroup.mk (K.normalizerMonoidHom ⟨(a : X), hAK a.2⟩ k)) =
        Yh a * φ (QuotientGroup.mk k) * (Yh a)⁻¹)
    (P : HypPair Q)
    (hP : ∀ a : ↥A, ((Yh a : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V) P.e = P.e ∧
      ((Yh a : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V) P.f = P.f) :
    K ≤ GL83.CompFam.centGenI 3 A K := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := ↥K with hY
  set ξ : Y →* ↥(elementaryGroup Q) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y)) with hξ
  have hξsurj : Function.Surjective ξ :=
    φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hξker : ξ.ker = Subgroup.center Y := by
    ext y
    simp [hξ]
  let ρ : A →* (V ≃ₗ[ZMod 2] V) := (elementaryGroup Q).subtype.comp Yh
  have hρO : ∀ a : A, ρ a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun a =>
    elementaryGroup_le_orthogonalGroup Q (Yh a).2
  have hfin : Finite (V ≃ₗ[ZMod 2] V) := by
    have : Finite V := Module.finite_of_finite (ZMod 2)
    exact Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) fun g g' h =>
      LinearEquiv.ext (congrFun h)
  set Ab : Subgroup (V ≃ₗ[ZMod 2] V) := ρ.range with hAb
  have hAbO : Ab ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨a, rfl⟩
    exact hρO a
  have hAbcomm : ∀ x ∈ Ab, ∀ y ∈ Ab, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hAel.1.is_comm.comm a b]
  have hAbexp : ∀ x ∈ Ab, x ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (hAel.2 a a.2)
    rw [this, map_one]
  have hP' : ∀ g ∈ Ab, g P.e = P.e ∧ g P.f = P.f := by
    rintro _ ⟨a, rfl⟩
    exact hP a
  have hpK : ((3 : ℕ) : ZMod 2) ≠ 0 := by decide
  have hgen := CFSG.HardMathSupport.Timmesfeld.Coordinator.elementaryGroup_le_closure_hyperEichlerSet
    (Q := Q) Nat.prime_three hpK hQ hAbO hAbcomm hAbexp P (fun h hh => (hP' h hh).1)
    (fun h hh => (hP' h hh).2)
  set S := CFSG.HardMathSupport.Timmesfeld.Coordinator.hyperEichlerSet Q 3 Ab with hS
  have hSle : ∀ g ∈ S, g ∈ elementaryGroup Q := by
    rintro g ⟨F, -, -, u, w, -, -, rfl⟩
    exact eichler_mem_elementaryGroup Q u w
  have h2 : (2 : ZMod 2) = 0 := by decide
  set 𝒢 : Set Y := {y | ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V) ∈ S} with h𝒢
  have hTtop : Subgroup.closure {ω : ↥(elementaryGroup Q) | (ω : V ≃ₗ[ZMod 2] V) ∈ S} = ⊤ := by
    rw [eq_top_iff]
    rintro ω -
    have hω : (ω : V ≃ₗ[ZMod 2] V) ∈ Subgroup.closure S := hgen ω.2
    have key : ∀ g ∈ Subgroup.closure S, ∃ t ∈ Subgroup.closure
        {ω : ↥(elementaryGroup Q) | (ω : V ≃ₗ[ZMod 2] V) ∈ S}, (t : V ≃ₗ[ZMod 2] V) = g := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        exact ⟨⟨x, hSle x hx⟩, Subgroup.subset_closure hx, rfl⟩
      | one => exact ⟨1, one_mem _, rfl⟩
      | mul x y _ _ hx hy =>
        obtain ⟨t, ht, rfl⟩ := hx
        obtain ⟨t', ht', rfl⟩ := hy
        exact ⟨t * t', mul_mem ht ht', rfl⟩
      | inv x _ hx =>
        obtain ⟨t, ht, rfl⟩ := hx
        exact ⟨t⁻¹, inv_mem ht, rfl⟩
    obtain ⟨t, ht, hte⟩ := key _ hω
    have : t = ω := Subtype.ext hte
    rwa [this] at ht
  have himage : ξ '' 𝒢 = {ω : ↥(elementaryGroup Q) | (ω : V ≃ₗ[ZMod 2] V) ∈ S} := by
    ext ω
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hω
      obtain ⟨y, rfl⟩ := hξsurj ω
      exact ⟨y, hω, rfl⟩
  have hgen' : Subgroup.closure 𝒢 ⊔ Subgroup.center Y = ⊤ := by
    have hmap : (Subgroup.closure 𝒢).map ξ = ⊤ := by
      rw [MonoidHom.map_closure, himage, hTtop]
    have := Subgroup.comap_map_eq ξ (Subgroup.closure 𝒢)
    rw [hmap, Subgroup.comap_top, hξker] at this
    exact this.symm
  have hsq : ∀ y ∈ 𝒢, y ^ 2 ∈ Subgroup.center Y := by
    intro y hy
    rw [← hξker, MonoidHom.mem_ker, map_pow]
    obtain ⟨F, -, -, u, w, -, -, hg⟩ := hy
    apply Subtype.ext
    change ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V) *
      ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V) = 1
    rw [hg]
    exact CFSG.HardMathSupport.Timmesfeld.Coordinator.eichler_mul_self_of_two_eq_zero h2 u w
  set ℰ : Set (Subgroup X) := {E | E ≤ A ∧ Nat.card A ≤ 3 * Nat.card E} with hℰdef
  have hℰ : ∀ E ∈ ℰ, E ≤ Subgroup.normalizer (K : Set X) := fun E hE => hE.1.trans hAK
  have hfix' : ∀ y ∈ 𝒢, ∃ E, ∃ hE : E ∈ ℰ, ∀ (a : X) (ha : a ∈ E),
      ((K.normalizerMonoidHom ⟨a, hℰ E hE ha⟩ : MulAut ↥K) y)⁻¹ * y ∈ Subgroup.center ↥K := by
    intro y hy
    have hg : ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V) ∈ S := hy
    obtain ⟨F, hFAb, hF, hcomm⟩ :=
      CFSG.HardMathSupport.Timmesfeld.Coordinator.exists_commute_of_mem_hyperEichlerSet hAbO hg
    set N : Subgroup A := F.comap ρ with hN
    have hcardN : Nat.card A ≤ 3 * Nat.card N := by
      have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
      set F' : Subgroup Ab := F.subgroupOf Ab with hF'
      have hNeq : N = F'.comap ρ.rangeRestrict := by
        ext a
        simp [hN, hF', Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      have hidx : N.index = F'.index := by
        rw [hNeq]
        exact Subgroup.index_comap_of_surjective F' hsurj
      have hF'card : Nat.card F' = Nat.card F :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFAb).toEquiv
      have h1 : F'.index * Nat.card F' = Nat.card Ab := F'.index_mul_card
      have h2' : N.index * Nat.card N = Nat.card A := N.index_mul_card
      have hFpos : 0 < Nat.card F := Nat.card_pos
      have hle : F'.index ≤ 3 := by
        by_contra hlt
        push Not at hlt
        have h3 : 3 * Nat.card F < F'.index * Nat.card F := Nat.mul_lt_mul_of_pos_right hlt hFpos
        have h4 : F'.index * Nat.card F = Nat.card Ab := by rw [← hF'card]; exact h1
        omega
      calc Nat.card A = N.index * Nat.card N := h2'.symm
        _ ≤ 3 * Nat.card N := Nat.mul_le_mul_right _ (hidx ▸ hle)
    have hE : N.map A.subtype ∈ ℰ := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨a, -, rfl⟩
        exact a.2
      · rw [Subgroup.card_map_of_injective A.subtype_injective]
        exact hcardN
    refine ⟨N.map A.subtype, hE, ?_⟩
    intro a ha
    obtain ⟨a', ha', rfl⟩ := ha
    have hcom := hcomm (ρ a') ha'
    rw [← hξker, MonoidHom.mem_ker, map_mul, map_inv]
    show (ξ (K.normalizerMonoidHom ⟨(a' : X), hAK a'.2⟩ y))⁻¹ * ξ y = 1
    have hξa : ξ (K.normalizerMonoidHom ⟨(a' : X), hAK a'.2⟩ y) =
        Yh a' * ξ y * (Yh a')⁻¹ := hYh a' y
    rw [hξa]
    have hfixed : Yh a' * ξ y * (Yh a')⁻¹ = ξ y := by
      apply Subtype.ext
      change (ρ a') * ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V) * (ρ a')⁻¹ =
        ((ξ y : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V)
      rw [hcom, mul_assoc, mul_inv_cancel, mul_one]
    rw [hfixed, inv_mul_cancel]
  have hmain := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.le_iSup_centralizer_of_lifts
    hK hZ ℰ hℰ 𝒢 hgen' hsq hfix'
  refine hmain.trans (iSup₂_le fun E hE => ?_)
  exact le_iSup (fun E : {E : Subgroup X // E ≤ A ∧ Nat.card A ≤ 3 * Nat.card E} =>
    K ⊓ Subgroup.centralizer (E.1 : Set X)) ⟨E, hE.1, hE.2⟩

theorem le_glbCore_of_orthF2 {X : Type} [Group X] [Finite X]
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (polarBilin Q).Nondegenerate) (hdim : 10 ≤ finrank (ZMod 2) V)
    (hAut : ∀ σ : MulAut ↥(elementaryGroup Q), σ ^ 3 = 1 → ∃ y, σ = MulAut.conj y)
    (hcenter : ∀ z : ↥(elementaryGroup Q), (∀ x : ↥(elementaryGroup Q), z * x = x * z) → z = 1)
    (hodd : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g ^ 3 = 1 → g ∈ elementaryGroup Q)
    {B K : Subgroup X} (hperf : commutator ↥K = ⊤) (hZ : Subgroup.center ↥K = ⊥)
    (φ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(elementaryGroup Q))
    (hB : IsElemAbelian 3 B) (hB4 : 4 ≤ CFSG.Open.pRank 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X))
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥) :
    K ≤ GLBCore 3 2 B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (V ≃ₗ[ZMod 2] V) := ClassicalEA.finite_linearEquiv
  set E := elementaryGroup Q with hEdef
  let α : ↥B →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  let ψα : ↥B →* MulAut ↥E := (MulAut.congr φ).toMonoidHom.comp
    (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.autQuotHom.comp α)
  have hψα3 : ∀ b : ↥B, ψα b ^ 3 = 1 := by
    intro b
    rw [← map_pow]
    have : b ^ 3 = 1 := Subtype.ext (hB.2 b b.2)
    rw [this, map_one]
  choose yfun hyfun using fun b : ↥B => hAut (ψα b) (hψα3 b)
  have hconj_inj : ∀ u v : ↥E, MulAut.conj u = MulAut.conj v → u = v := by
    intro u v h
    have h1 : v⁻¹ * u = 1 := hcenter _ (fun x => by
      have := congrArg (fun f : MulAut ↥E => f x) h
      simp only [MulAut.conj_apply] at this
      calc (v⁻¹ * u) * x = v⁻¹ * (u * x * u⁻¹) * u := by group
        _ = v⁻¹ * (v * x * v⁻¹) * u := by rw [this]
        _ = x * (v⁻¹ * u) := by group)
    exact (inv_mul_eq_one.mp h1).symm
  let Yh : ↥B →* ↥E :=
    { toFun := yfun
      map_one' := by
        apply hconj_inj
        rw [← hyfun, map_one, map_one]
      map_mul' := fun a b => by
        apply hconj_inj
        rw [map_mul, ← hyfun, ← hyfun, ← hyfun, map_mul] }
  have hrel : ∀ (b : ↥B) (k : ↥K), φ (QuotientGroup.mk (α b k)) = Yh b * φ (QuotientGroup.mk k) * (Yh b)⁻¹ := by
    intro b k
    have h1 : ψα b (φ (QuotientGroup.mk k)) = φ (QuotientGroup.mk (α b k)) := by
      simp only [ψα, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
        MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      exact congrArg φ (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.autQuot_mk (α b) k)
    rw [← h1, hyfun b, MulAut.conj_apply]
    rfl
  have hαapp : ∀ (b : ↥B) (k : ↥K), ((α b k : ↥K) : X) = (b : X) * k * (b : X)⁻¹ := fun b k =>
    Subgroup.normalizerMonoidHom_apply_apply_coe K _ k
  have hmk : ∀ k k' : ↥K, (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk k' → k = k' := by
    intro k k' h
    have h' := QuotientGroup.eq.1 h
    rw [hZ, Subgroup.mem_bot] at h'
    exact inv_mul_eq_one.1 h'
  have hYhinj : Function.Injective Yh := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    have hcen : (b : X) ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := hrel b ⟨k, hk⟩
      rw [hb, one_mul, inv_one, mul_one] at h1
      have h3 := congrArg Subtype.val (hmk _ _ (φ.injective h1))
      rw [hαapp] at h3
      calc k * (b : X) = (b : X) * k * (b : X)⁻¹ * b := by rw [h3]
        _ = (b : X) * k := by group
    have hbC : (b : X) ∈ B ⊓ Subgroup.centralizer (K : Set X) := ⟨b.2, hcen⟩
    rw [hC, Subgroup.mem_bot] at hbC
    exact Subgroup.mem_bot.2 (Subtype.ext hbC)
  let ρ : ↥B →* (V ≃ₗ[ZMod 2] V) := E.subtype.comp Yh
  have hρinj : Function.Injective ρ := E.subtype_injective.comp hYhinj
  set D := ρ.range with hD
  have hDO : D ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨b, rfl⟩
    exact elementaryGroup_le_orthogonalGroup Q (Yh b).2
  have hDel : IsElemAbelian 3 D := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun g hg => ?_⟩
    · obtain ⟨_, a, rfl⟩ := x
      obtain ⟨_, b, rfl⟩ := y
      apply Subtype.ext
      show ρ a * ρ b = ρ b * ρ a
      rw [← map_mul, ← map_mul, hB.1.is_comm.comm a b]
    · obtain ⟨b, rfl⟩ := hg
      rw [← map_pow]
      have : b ^ 3 = 1 := Subtype.ext (hB.2 b b.2)
      rw [this, map_one]
  have hBc : Nat.card ↥B = 3 ^ CFSG.Open.pRank 3 B := GL83.PiGen.card_eq_pow_pRank hB
  have hDc : Nat.card D = 3 ^ CFSG.Open.pRank 3 B := by
    rw [hD, ← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv, hBc]
  have hmax : ∀ F : Subgroup (V ≃ₗ[ZMod 2] V), F ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      IsElemAbelian 3 F → Nat.card F ≤ Nat.card D := by
    intro F hFO hF
    have hFE : F ≤ E := fun g hg => hodd g (hFO hg) (hF.2 g hg)
    let ι : ↥E →* X := K.subtype.comp
      ((CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.equivCenterQuot hZ).symm.toMonoidHom.comp
        φ.symm.toMonoidHom)
    have hι : Function.Injective ι := by
      intro x y hxy
      have h1 := Subtype.val_injective hxy
      exact φ.symm.injective
        ((CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.equivCenterQuot hZ).symm.injective h1)
    set F' : Subgroup X := (F.subgroupOf E).map ι with hF'
    have hF'c : Nat.card F' = Nat.card F := by
      rw [hF', Subgroup.card_map_of_injective hι]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv
    have hF'el : IsElemAbelian 3 F' :=
      CFSG.SectionRank.isElemAbelian_map (CFSG.Open.IsElemAbelian.subgroupOf hF E) ι
    obtain ⟨k, hk⟩ := GL83.CompFam.exists_card_eq_pow hF'el
    have hkle : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_top hF'el hk
    rw [← hF'c, hk, hDc, hrk]
    exact Nat.pow_le_pow_right (by norm_num) hkle
  obtain ⟨F, hFD, hF27, P, hP⟩ := exists_fixed_hypPair_of_maxEA_orthF2 hQ hdim hDO hDel hDc hB4 hmax
  have hFr : F ≤ ρ.range := hFD
  set E' : Subgroup X := (F.comap ρ).map B.subtype with hE'
  have hE'B : E' ≤ B := Subgroup.map_subtype_le _
  have hE'c : Nat.card E' = Nat.card F := by
    rw [hE', Subgroup.card_map_of_injective B.subtype_injective, ← Subgroup.card_map_of_injective hρinj,
      Subgroup.map_comap_eq_self hFr]
  have hE'el : IsElemAbelian 3 E' := GL83.CompFam.elem_mono hB hE'B
  have hmemE' : ∀ a : ↥E', ρ (Subgroup.inclusion hE'B a) ∈ F := by
    rintro ⟨_, ⟨b, hb, rfl⟩⟩
    have : Subgroup.inclusion hE'B ⟨B.subtype b, ⟨b, hb, rfl⟩⟩ = b := Subtype.ext rfl
    rw [this]
    exact hb
  have hgen : K ≤ GL83.CompFam.centGenI 3 E' K := by
    refine le_centGenI_of_lift_orthF2 hperf (by rw [hZ, Subgroup.card_bot]; decide) hE'el
      (hE'B.trans hBN) hQ φ (Yh.comp (Subgroup.inclusion hE'B)) (fun a k => ?_) P
      (fun a => hP _ (hmemE' a))
    have h1 := hrel (Subgroup.inclusion hE'B a) k
    exact h1
  exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.le_glbCore_of_centGenI Nat.prime_three
    hE'B hE'el (by rw [hE'c]; exact hF27) hgen

end Gen

section OmegaTwo

open CFSG.LieType.Universal.Spin (quadPlus quadMinus nondegenerate_polarBilin_quadPlus
  nondegenerate_polarBilin_quadMinus_of_finite)
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration (IsPlusSpace IsMinusSpace statedOmegaPlusEquiv
  statedOmegaMinusEquiv)

@[expose] def IsOrthTwoIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ (n : ℕ) (q : TauCeti.PrimePower), 5 ≤ n ∧ q.p = 2 ∧ q.exponent = 1 ∧
    (d.1 = .D n q ∨ d.1 = .twistedD n q)

theorem nonempty_equiv_elementaryGroup_plus_orthF2 {n : ℕ} (hn : 3 ≤ n) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D n q).Valid) (hqp : q.p = 2) (hqe : q.exponent = 1) {S : Type} [Group S]
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.D n q, hv⟩).Group) :
    Nonempty (S ≃* ↥(elementaryGroup (quadPlus n (ZMod 2)))) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even n q hv hqp eS
  rw [hqp, hqe, pow_one] at hF
  obtain ⟨φ⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_ringEquiv_zmod_two hF
  exact ⟨(e.trans (CFSG.LocalAnalysis.GLTheoremA.CatB.statedProjEquivZMod2 φ
    (CFSG.LocalAnalysis.GLTheoremA.CatB.glCongr_statedOmega_plus φ n))).trans (statedOmegaPlusEquiv hn)⟩

theorem nonempty_equiv_elementaryGroup_minus_orthF2 {n : ℕ} (hn : 2 ≤ n) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD n q).Valid) (hqp : q.p = 2) (hqe : q.exponent = 1) {S : Type}
    [Group S] (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedD n q, hv⟩).Group) :
    Nonempty (S ≃* ↥(elementaryGroup (quadMinus n (ZMod 2) 1 1))) := by
  obtain ⟨-, F, _, _, hF, b, c, hbc, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even n q hv hqp eS
  rw [hqp, hqe, pow_one] at hF
  obtain ⟨φ⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_ringEquiv_zmod_two hF
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := zmodTwo_eq_zero_or_one_orthF2
  have hc : φ c = 1 := by
    rcases h01 (φ c) with h | h
    · exfalso
      apply hbc 0
      rw [map_eq_zero_iff φ φ.injective] at h
      rw [h]
      ring
    · exact h
  have hb : φ b = 1 := by
    rcases h01 (φ b) with h | h
    · exfalso
      apply hbc 1
      rw [map_eq_zero_iff φ φ.injective] at h
      apply φ.injective
      rw [h, map_add, map_add, hc]
      simp only [one_pow, map_one, zero_mul, map_zero, add_zero]
      decide
    · exact h
  have hmap := CFSG.ClassicalInvolution.Upgrade.map_statedOmega (ι := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
    (QK := StatedQuadMinus n F b c) (QL := StatedQuadMinus n (ZMod 2) 1 1) φ
    (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp φ hb hc)
  exact ⟨(e.trans (CFSG.LocalAnalysis.GLTheoremA.CatB.statedProjEquivZMod2 φ hmap)).trans
    (statedOmegaMinusEquiv hn)⟩

theorem le_glbCore_of_orthTwoIndex {X : Type} [Group X] [Finite X] (hcore : GLAPPrimeCore 3 X = ⊥)
    {B : Subgroup X} (hB : IsElemAbelian 3 B) (hB4 : 4 ≤ CFSG.Open.pRank 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (hd : IsOrthTwoIndex d)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥) :
    K ≤ GLBCore 3 2 B := by
  have hZ : Subgroup.center ↥K = ⊥ := by
    by_contra hZ
    exact InputsSeitz7.cen_ne_bot_of_center_ne_bot hcore hB hrk hK hZ hBN hC
  have hperf : commutator ↥K = ⊤ := hK.2.2.1
  let eK : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group := (InputsSeitz3.equivCenterQuot hZ).trans e
  obtain ⟨n, q, hn, hqp, hqe, hdq | hdq⟩ := hd
  · obtain ⟨d0, hv⟩ := d
    simp only at hdq
    subst hdq
    obtain ⟨ψ⟩ := nonempty_equiv_elementaryGroup_plus_orthF2 (by omega) hv hqp hqe eK
    have hm : 3 ≤ n := by omega
    have hstd : IsPlusSpace (quadPlus n (ZMod 2)) n := ⟨LinearEquiv.refl _ _, fun v => rfl⟩
    refine le_glbCore_of_orthF2 (nondegenerate_polarBilin_quadPlus n (ZMod 2)) ?_
      (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.inner_of_mulEquiv (statedOmegaPlusEquiv hm)
        (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadPlus_aut_odd_inner n 3
          (by omega) Nat.prime_three (by norm_num) (by omega)))
      (fun z hz => Subtype.ext
        (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.eq_one_of_commute_elementaryGroup_of_isPlusSpace
          hm hstd (elementaryGroup_le_orthogonalGroup _ z.2)
          (fun x hx => congrArg Subtype.val (hz ⟨x, hx⟩))))
      (fun g hg h3 =>
        CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.mem_elementaryGroup_of_odd_pow_of_isPlusSpace
          hm hstd hg (by decide) h3)
      hperf hZ ((InputsSeitz3.equivCenterQuot hZ).symm.trans ψ) hB hB4 hrk hBN hC
    rw [CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.finrank_plus]
    omega
  · obtain ⟨d0, hv⟩ := d
    simp only at hdq
    subst hdq
    obtain ⟨ψ⟩ := nonempty_equiv_elementaryGroup_minus_orthF2 (by omega) hv hqp hqe eK
    have hm : 3 ≤ n := by omega
    have hstd : IsMinusSpace (quadMinus n (ZMod 2) 1 1) n := ⟨LinearEquiv.refl _ _, fun v => rfl⟩
    refine le_glbCore_of_orthF2 (nondegenerate_polarBilin_quadMinus_of_finite n (ZMod 2)
        (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)) ?_
      (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.inner_of_mulEquiv
        (statedOmegaMinusEquiv (by omega))
        (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadMinus_aut_odd_inner n 3
          (by omega) Nat.prime_three (by norm_num)))
      (fun z hz => Subtype.ext
        (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.eq_one_of_commute_elementaryGroup_of_isMinusSpace
          hm hstd (elementaryGroup_le_orthogonalGroup _ z.2)
          (fun x hx => congrArg Subtype.val (hz ⟨x, hx⟩))))
      (fun g hg h3 =>
        CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.mem_elementaryGroup_of_odd_pow_of_isMinusSpace
          (by omega) hstd hg (by decide) h3)
      hperf hZ ((InputsSeitz3.equivCenterQuot hZ).symm.trans ψ) hB hB4 hrk hBN hC
    rw [CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.finrank_minus (by omega)]
    omega

end OmegaTwo

section OmegaEight

open CFSG.LieType.Universal.Spin (quadPlus nondegenerate_polarBilin_quadPlus)
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration (IsPlusSpace)

@[expose] def IsOmegaEightTwoIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .D 4 q

theorem false_of_d4Four
    {X : Type} [Group X] [Finite X] (hcore : GLAPPrimeCore 3 X = ⊥)
    {B : Subgroup X} (hB : IsElemAbelian 3 B) (hB4 : 4 ≤ CFSG.Open.pRank 3 B) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IsD4FourIndex d.1)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hout : ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) : False := by
  have hGK := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112b_glaPComponent_of_isComponentOf hcore hK
  have h27 := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.d44OuterRank_holds ↥K
    (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i116e_isQuasisimple hcore hGK)
    (CFSG.HardMathSupport.Solomon.Coordinator.i271h_primeCore_eq_bot hcore hGK) ⟨d, hd, ⟨e⟩⟩ _
    (InputsSeitz3.isElemAbelian_autIm hB K) hout
  rw [InputsSeitz3.card_autIm hBN hC, GL83.PiGen.card_eq_pow_pRank hB] at h27
  have : 3 ^ 4 ≤ 3 ^ CFSG.Open.pRank 3 B := Nat.pow_le_pow_right (by norm_num) hB4
  omega


theorem le_glbCore_of_omegaEightTwo {X : Type} [Group X] [Finite X] (hcore : GLAPPrimeCore 3 X = ⊥)
    {B : Subgroup X} (hB : IsElemAbelian 3 B) (hB4 : 4 ≤ CFSG.Open.pRank 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (hd : IsOmegaEightTwoIndex d)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥) :
    K ≤ GLBCore 3 2 B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.center ↥K = ⊥ := by
    by_contra hZ
    exact InputsSeitz7.cen_ne_bot_of_center_ne_bot hcore hB hrk hK hZ hBN hC
  have hperf : commutator ↥K = ⊤ := hK.2.2.1
  let eK : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group := (InputsSeitz3.equivCenterQuot hZ).trans e
  obtain ⟨q, hqp, hqe, hdq⟩ := hd
  obtain ⟨d0, hv⟩ := d
  simp only at hdq
  subst hdq
  have hs : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope (.D 4 q) := hqp
  have hAel : IsElemAbelian 3 (InputsSeitz3.autIm B K) := InputsSeitz3.isElemAbelian_autIm hB K
  have hBc : Nat.card ↥B = 3 ^ CFSG.Open.pRank 3 B := GL83.PiGen.card_eq_pow_pRank hB
  have h81 : 81 ≤ Nat.card ↥B := by
    rw [hBc]
    exact (show 81 = 3 ^ 4 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hB4
  have hinn : InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range := by
    by_contra hout
    have hmod := CFSG.Models.lieModel_D 4 q hv eK
    rw [hqp, hqe] at hmod
    obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hmod
    · have h27 := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.D44OuterAux.card_le_of_outer hcl hZ
        (by norm_num) _ hAel hout
      rw [InputsSeitz3.card_autIm hBN hC] at h27
      omega
    · exact absurd h0 (by norm_num)
  obtain ⟨ψ⟩ := nonempty_equiv_elementaryGroup_plus_orthF2 (by norm_num : 3 ≤ 4) hv hqp hqe eK
  set Q := quadPlus 4 (ZMod 2) with hQdef
  have hQ : (polarBilin Q).Nondegenerate := nondegenerate_polarBilin_quadPlus 4 (ZMod 2)
  have hstd : IsPlusSpace Q 4 := ⟨LinearEquiv.refl _ _, fun v => rfl⟩
  set E := elementaryGroup Q with hEdef
  haveI : Finite (Fin 4 ⊕ Fin 4 → ZMod 2) := inferInstance
  haveI : Finite ((Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)) :=
    ClassicalEA.finite_linearEquiv
  have hconj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro x
    have h := congrArg (fun α : MulAut ↥K => α x) ((MonoidHom.mem_ker).mp hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc x * g = g * x * g⁻¹ * g := by rw [h]
      _ = g * x := by group
  let α : ↥B →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hαA : ∀ b : ↥B, α b ∈ (MulAut.conj : ↥K →* MulAut ↥K).range := fun b =>
    hinn ⟨Subgroup.inclusion hBN b, Subgroup.mem_subgroupOf.2 b.2, rfl⟩
  let α' : ↥B →* (MulAut.conj : ↥K →* MulAut ↥K).range := α.codRestrict _ hαA
  let ι : ↥B →* ↥K := (MonoidHom.ofInjective hconj).symm.toMonoidHom.comp α'
  have hι : ∀ b : ↥B, MulAut.conj (ι b) = α b := fun b => by
    have h := congrArg Subtype.val ((MonoidHom.ofInjective hconj).apply_symm_apply (α' b))
    rw [MonoidHom.ofInjective_apply] at h
    exact h
  have hαapp : ∀ (b : ↥B) (k : ↥K), ((α b k : ↥K) : X) = (b : X) * k * (b : X)⁻¹ := fun b k =>
    Subgroup.normalizerMonoidHom_apply_apply_coe K _ k
  have hιapp : ∀ (b : ↥B) (k : ↥K), α b k = ι b * k * (ι b)⁻¹ := fun b k => by
    rw [← hι b, MulAut.conj_apply]
  let Yh : ↥B →* ↥E := ψ.toMonoidHom.comp ι
  have hrel : ∀ (b : ↥B) (k : ↥K), ψ (α b k) = Yh b * ψ k * (Yh b)⁻¹ := fun b k => by
    rw [hιapp, map_mul, map_mul, map_inv]
    rfl
  have hYhinj : Function.Injective Yh := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    have hιb : ι b = 1 := ψ.injective (by rw [map_one]; exact hb)
    have hcen : (b : X) ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := hιapp b ⟨k, hk⟩
      rw [hιb, one_mul, inv_one, mul_one] at h1
      have h3 := congrArg Subtype.val h1
      rw [hαapp] at h3
      calc k * (b : X) = (b : X) * k * (b : X)⁻¹ * b := by rw [h3]
        _ = (b : X) * k := by group
    have hbC : (b : X) ∈ B ⊓ Subgroup.centralizer (K : Set X) := ⟨b.2, hcen⟩
    rw [hC, Subgroup.mem_bot] at hbC
    exact Subgroup.mem_bot.2 (Subtype.ext hbC)
  let ρ : ↥B →* ((Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)) := E.subtype.comp Yh
  have hρinj : Function.Injective ρ := E.subtype_injective.comp hYhinj
  set D := ρ.range with hD
  have hDO : D ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨b, rfl⟩
    exact elementaryGroup_le_orthogonalGroup Q (Yh b).2
  have hDel : IsElemAbelian 3 D := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun g hg => ?_⟩
    · obtain ⟨_, a, rfl⟩ := x
      obtain ⟨_, b, rfl⟩ := y
      apply Subtype.ext
      show ρ a * ρ b = ρ b * ρ a
      rw [← map_mul, ← map_mul, hB.1.is_comm.comm a b]
    · obtain ⟨b, rfl⟩ := hg
      rw [← map_pow]
      have : b ^ 3 = 1 := Subtype.ext (hB.2 b b.2)
      rw [this, map_one]
  have hDc : Nat.card D = 3 ^ CFSG.Open.pRank 3 B := by
    rw [hD, ← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv, hBc]
  have hmax : ∀ F : Subgroup ((Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)),
      F ≤ TauCeti.QuadraticMap.orthogonalGroup Q → IsElemAbelian 3 F → Nat.card F ≤ Nat.card D := by
    intro F hFO hF
    have hFE : F ≤ E := fun g hg =>
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.mem_elementaryGroup_of_odd_pow_of_isPlusSpace
        (by norm_num) hstd (hFO hg) (by decide) (hF.2 g hg)
    let ι' : ↥E →* X := K.subtype.comp ψ.symm.toMonoidHom
    have hι' : Function.Injective ι' := fun x y hxy => ψ.symm.injective (Subtype.val_injective hxy)
    set F' : Subgroup X := (F.subgroupOf E).map ι' with hF'
    have hF'c : Nat.card F' = Nat.card F := by
      rw [hF', Subgroup.card_map_of_injective hι']
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv
    have hF'el : IsElemAbelian 3 F' :=
      CFSG.SectionRank.isElemAbelian_map (CFSG.Open.IsElemAbelian.subgroupOf hF E) ι'
    obtain ⟨k, hk⟩ := GL83.CompFam.exists_card_eq_pow hF'el
    have hkle : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_top hF'el hk
    rw [← hF'c, hk, hDc, hrk]
    exact Nat.pow_le_pow_right (by norm_num) hkle
  have hpre : ∀ F : Subgroup ((Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)), F ≤ D →
      (F.comap ρ).map B.subtype ≤ B ∧ Nat.card ((F.comap ρ).map B.subtype) = Nat.card F ∧
        ∀ a : ↥((F.comap ρ).map B.subtype),
          ρ (Subgroup.inclusion (Subgroup.map_subtype_le (F.comap ρ)) a) ∈ F := by
    intro F hFD
    refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective B.subtype_injective, ← Subgroup.card_map_of_injective hρinj,
        Subgroup.map_comap_eq_self hFD]
    · rintro ⟨_, ⟨b, hb, rfl⟩⟩
      have : Subgroup.inclusion (Subgroup.map_subtype_le (F.comap ρ)) ⟨B.subtype b, ⟨b, hb, rfl⟩⟩ = b :=
        Subtype.ext rfl
      rw [this]
      exact hb
  rcases exists_fixed_hypPair_or_swap_of_maxEA_orthF2 hQ hDO hDel hDc hB4 hmax with
    ⟨F, hFD, hF27, P, hP⟩ | ⟨-, F, hFD, hF27, u, huE, hu1, hu2, hFu⟩
  ·
    obtain ⟨hE'B, hE'c, hmemE'⟩ := hpre F hFD
    set E' := (F.comap ρ).map B.subtype
    have hE'el : IsElemAbelian 3 E' := GL83.CompFam.elem_mono hB hE'B
    let eZ : ↥K ≃* (↥K ⧸ Subgroup.center ↥K) :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    let φ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥E := eZ.symm.trans ψ
    have heZ : ∀ k : ↥K, eZ k = QuotientGroup.mk k := fun k => rfl
    have hφ : ∀ k : ↥K, φ (QuotientGroup.mk k) = ψ k := fun k => by
      show ψ (eZ.symm (QuotientGroup.mk k)) = ψ k
      congr 1
    have hgen : K ≤ GL83.CompFam.centGenI 3 E' K := by
      refine le_centGenI_of_lift_orthF2 hperf (by rw [hZ, Subgroup.card_bot]; decide) hE'el
        (hE'B.trans hBN) hQ φ (Yh.comp (Subgroup.inclusion hE'B)) (fun a k => ?_) P
        (fun a => hP _ (hmemE' a))
      rw [hφ, hφ]
      exact hrel (Subgroup.inclusion hE'B a) k
    exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.le_glbCore_of_centGenI Nat.prime_three
      hE'B hE'el (by rw [hE'c]; exact hF27) hgen
  ·
    have hFp : IsPGroup 3 ↥F := (hDel.mono hFD).isPGroup
    obtain ⟨m, hm⟩ := hFp.exists_card_eq
    have hm3 : 3 ≤ m := by
      by_contra hlt
      have : 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 3) (G := ↥F)
      (by rw [hm]; exact Nat.pow_dvd_pow 3 hm3)
    set F' := F₀.map F.subtype with hF'def
    have hF'F : F' ≤ F := Subgroup.map_subtype_le _
    have hF'c : Nat.card F' = 3 ^ 3 := by
      rw [hF'def, Subgroup.card_map_of_injective F.subtype_injective, hF₀]
    obtain ⟨hE'B, hE'c, hmemE'⟩ := hpre F' (hF'F.trans hFD)
    set E' := (F'.comap ρ).map B.subtype with hE'def
    have hE'C : E' ⊓ Subgroup.centralizer (K : Set X) = ⊥ :=
      le_bot_iff.1 ((inf_le_inf_right _ hE'B).trans hC.le)
    have hE'N : E' ≤ Subgroup.normalizer (K : Set X) := hE'B.trans hBN
    set t : ↥K := ψ.symm ⟨u, huE⟩ with htdef
    have hψt : ψ t = ⟨u, huE⟩ := by rw [htdef, MulEquiv.apply_symm_apply]
    have ht1 : t ≠ 1 := by
      intro h
      apply hu1
      have := congrArg Subtype.val hψt
      rw [h, map_one] at this
      exact this.symm
    have ht2 : t * t = 1 := by
      apply ψ.injective
      rw [map_mul, hψt, map_one]
      exact Subtype.ext hu2
    refine InputsSeitz7.le_glbCore_of_e27_inv hB hs eK hE'B hE'C le_rfl ?_ ht1 ht2 ?_
    · rw [InputsSeitz3.card_autIm hE'N hE'C, hE'c, hF'c]
    · rintro _ ⟨n, hn, rfl⟩
      have hnE' : (n : X) ∈ E' := Subgroup.mem_subgroupOf.1 hn
      set a : ↥E' := ⟨n, hnE'⟩
      set b : ↥B := Subgroup.inclusion hE'B a with hbdef
      have hnb : n = Subgroup.inclusion hBN b := Subtype.ext rfl
      have hρb : ρ b ∈ F := hF'F (hmemE' a)
      have hcomm : ρ b * u = u * ρ b := hFu _ hρb
      have h1 : K.normalizerMonoidHom n t = α b t := by rw [hnb]; rfl
      rw [h1]
      apply ψ.injective
      rw [hrel, hψt]
      apply Subtype.ext
      change ρ b * u * (ρ b)⁻¹ = u
      rw [hcomm, mul_inv_cancel_right]

end OmegaEight

section ExcRank

theorem card_le_27_of_rank_out_orthF2 {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    (hrk : CFSG.LieType.SeitzGeneration.RankLE2 3 S)
    (hout : ∀ D : Subgroup (MulAut S), IsElemAbelian 3 D →
      Nat.card D ≤ 3 * Nat.card ↥(D ⊓ (MulAut.conj : S →* MulAut S).range))
    (D : Subgroup (MulAut S)) (hD : IsElemAbelian 3 D) : Nat.card D ≤ 27 := by
  have hconj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro x
    have h := congrArg (fun α : MulAut S => α x) ((MonoidHom.mem_ker).mp hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc x * g = g * x * g⁻¹ * g := by rw [h]
      _ = g * x := by group
  have h1 := hout D hD
  set D₀ := D ⊓ (MulAut.conj : S →* MulAut S).range with hD₀
  have hmap : (D₀.comap (MulAut.conj : S →* MulAut S)).map MulAut.conj = D₀ :=
    Subgroup.map_comap_eq_self inf_le_right
  have hc : Nat.card (D₀.comap (MulAut.conj : S →* MulAut S)) = Nat.card D₀ := by
    rw [← Subgroup.card_map_of_injective hconj, hmap]
  have hD₀el : IsElemAbelian 3 D₀ := GL83.CompFam.elem_mono hD inf_le_left
  have h2 := hrk (D₀.comap (MulAut.conj : S →* MulAut S))
    (InputsSeitz7.isElemAbelian_comap_of_injective hconj hD₀el)
  rw [hc] at h2
  norm_num at h2
  omega

theorem card_le_three_mul_inner_of_hom_orthF2 {C : Type} [Group C] [Finite C] {L : Type} [Field L]
    (hL : Nat.card (L ≃+* L) = 3) (Θ : MulAut C →* (L ≃+* L))
    (hΘ : Θ.ker = (MulAut.conj : C →* MulAut C).range) (D : Subgroup (MulAut C))
    (hD : IsElemAbelian 3 D) :
    Nat.card D ≤ 3 * Nat.card ↥(D ⊓ (MulAut.conj : C →* MulAut C).range) := by
  haveI : Finite (MulAut C) := MulEquiv.finite_left
  rw [← hΘ]
  have hidx : Θ.ker.index ∣ 3 := by
    rw [Subgroup.index_ker, ← hL]
    exact Subgroup.card_subgroup_dvd_card Θ.range
  refine InputsSeitz7.card_le_three_mul_inf (fun h9 => ?_) (fun h0 => ?_)
    (CFSG.Open.IsElemAbelian.isPGroup hD)
  · have := Nat.le_of_dvd (by norm_num) (h9.trans hidx)
    omega
  · rw [h0] at hidx
    norm_num at hidx

theorem false_of_card_le_27_orthF2 {X : Type} [Group X] [Finite X] {B K : Subgroup X}
    (hB : IsElemAbelian 3 B) (hB4 : 4 ≤ CFSG.Open.pRank 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (h27 : ∀ D : Subgroup (MulAut ↥K), IsElemAbelian 3 D → Nat.card D ≤ 27) : False := by
  have h1 := h27 _ (InputsSeitz3.isElemAbelian_autIm hB K)
  rw [InputsSeitz3.card_autIm hBN hC, GL83.PiGen.card_eq_pow_pRank hB] at h1
  have : 3 ^ 4 ≤ 3 ^ CFSG.Open.pRank 3 B := Nat.pow_le_pow_right (by norm_num) hB4
  omega

@[expose] def IsTriD4TwoIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .trialityD4 q

@[expose] def IsG2EightIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .G2 q


theorem card_le_27_triD4Two_orthF2 {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (hqp : q.p = 2) (hqe : q.exponent = 1) {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) (D : Subgroup (MulAut S))
    (hD : IsElemAbelian 3 D) : Nat.card D ≤ 27 := by
  obtain ⟨L, _, _, σ, hL, -, ⟨Θ, hΘ⟩, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  rw [hqp, hqe] at hL
  have hL3 : Nat.card (L ≃+* L) = 3 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two L
      (by rw [hL]; norm_num)).1
  let ψ := eS.trans eC
  haveI := Finite.of_equiv S ψ.toEquiv
  obtain ⟨eT, hT⟩ := CFSG.HardMathSupport.Seitz.TrialityEven.exists_equiv_trialityGroup8 hqp hqe hv
  refine card_le_27_of_rank_out_orthF2 hZ (fun F hF => ?_)
    (InputsSeitz7.card_le_three_mul_inner_of_mulEquiv ψ
      (card_le_three_mul_inner_of_hom_orthF2 hL3 Θ hΘ)) D hD
  have hF' := CFSG.SectionRank.isElemAbelian_map hF (eS.trans eT).toMonoidHom
  have h9 := CFSG.GF2Type.Smith1980Orth.card_le_nine_of_elementary_trialityGroup8 hT
    (F.map (eS.trans eT).toMonoidHom) (fun x hx y hy => hF'.comm hx hy) (fun x hx => hF'.2 x hx)
  rw [Subgroup.card_map_of_injective (eS.trans eT).injective] at h9
  exact h9

theorem card_le_27_g2Eight_orthF2 {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    (hqp : q.p = 2) (hqe : q.exponent = 3) {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) (D : Subgroup (MulAut S))
    (hD : IsElemAbelian 3 D) : Nat.card D ≤ 27 := by
  obtain ⟨L, _, _, hL, -, ⟨eA⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  have hL' : Nat.card L = 2 ^ 3 := by rw [hL, TauCeti.PrimePower.card_def, hqp, hqe]
  obtain ⟨-, Θ, -, -, hΘ, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
      (by norm_num) L hL'
  have hL3 : Nat.card (L ≃+* L) = 3 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two L hL').1
  let ψ := eS.trans eA
  haveI := Finite.of_equiv S ψ.toEquiv
  exact card_le_27_of_rank_out_orthF2 hZ
    (CFSG.LieType.SeitzGeneration.RankLE2.of_mulEquiv eS.symm
      (CFSG.HardMathSupport.Curtis.Coordinator.rankLE2_cat_G2 q hv hqp Nat.prime_three (by norm_num)))
    (InputsSeitz7.card_le_three_mul_inner_of_mulEquiv ψ (card_le_three_mul_inner_of_hom_orthF2 hL3 Θ hΘ))
    D hD

theorem false_of_triD4Two_or_g2Eight {X : Type} [Group X] [Finite X] (hcore : GLAPPrimeCore 3 X = ⊥)
    {B : Subgroup X} (hB : IsElemAbelian 3 B) (hB4 : 4 ≤ CFSG.Open.pRank 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : IsTriD4TwoIndex d ∨ IsG2EightIndex d)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥) :
    False := by
  have hZ : Subgroup.center ↥K = ⊥ := by
    by_contra hZ
    exact InputsSeitz7.cen_ne_bot_of_center_ne_bot hcore hB hrk hK hZ hBN hC
  let eK : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group := (InputsSeitz3.equivCenterQuot hZ).trans e
  refine false_of_card_le_27_orthF2 hB hB4 hBN hC ?_
  rcases hd with ⟨q, hqp, hqe, hdq⟩ | ⟨q, hqp, hqe, hdq⟩
  · obtain ⟨d0, hv⟩ := d
    simp only at hdq
    subst hdq
    exact card_le_27_triD4Two_orthF2 hv hqp hqe hZ eK
  · obtain ⟨d0, hv⟩ := d
    simp only at hdq
    subst hdq
    exact card_le_27_g2Eight_orthF2 hv hqp hqe hZ eK

end ExcRank

section CoverIdx

theorem not_coverIndex_orthF2 {d : TauCeti.ValidLieTypeIndex}
    (hd : IsOrthTwoIndex d ∨ IsTriD4TwoIndex d ∨ IsG2EightIndex d) :
    ¬ CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 d.1 := by
  rcases hd with ⟨n, q, -, -, -, hdq | hdq⟩ | ⟨q, -, -, hdq⟩ | ⟨q, -, -, hdq⟩ <;> rw [hdq] <;> exact id

end CoverIdx

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz8

end
