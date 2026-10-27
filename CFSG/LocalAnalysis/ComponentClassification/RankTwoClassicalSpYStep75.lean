module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalStep75
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSpYTrick
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSpYDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidGen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidDefs

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem ClassicalModel.not_isLinearFiveFour_of_symplectic {A : Subgroup G}
    {D : ClassicalModel A} (hfam : D.family = .symplectic) : ¬ D.IsLinearFiveFour := by
  cases D with
  | linear => simp [ClassicalModel.family] at hfam
  | unitary => simp [ClassicalModel.family] at hfam
  | symplectic => exact id
  | orthPlus => simp [ClassicalModel.family] at hfam
  | orthMinus => simp [ClassicalModel.family] at hfam

theorem LeviChoice.commutator_W {A : Subgroup G} {D : ClassicalModel A} {p : G}
    {W Y : Subgroup G} (hW : LeviChoice D p W Y) (hq : 4 ≤ D.q) : ⁅W, W⁆ = W := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hW.W_type
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF]; exact hq)
    exact ⟨s, hs⟩
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.LinearGroups.special_linear_isPerfect (K := F) (n := 2) le_rfl (Or.inr h4)
  have : Group.IsPerfect ↥W := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  exact Subgroup.isPerfect_iff.mp this

theorem AParts.mem_J {A R T J : Subgroup G} {p : G} (hJ : AParts A R T p J) : p ∈ J := by
  obtain ⟨t, ht, hρ⟩ := hJ.aPart_mem
  exact hJ.aPart_le t ht p hJ.mem hρ

theorem LeviChoice.le_perfectCore {A R T : Subgroup G} {D : ClassicalModel A} {p : G}
    {W Y : Subgroup G} (hW : LeviChoice D p W Y) (hq : 4 ≤ D.q)
    (hJ : AParts A R T p (D.alpha p)) :
    W ≤ CFSG.Quasithin.perfectCore (A ⊓ centralizer ({p} : Set G)) := by
  refine CFSG.Quasithin.le_perfectCore_of_perfect (fun w hw => ?_) (hW.commutator_W hq)
  obtain ⟨hwA, hwα⟩ := mem_inf.mp (hW.Y_le (hW.W_le hw))
  exact mem_inf.mpr ⟨hwA, mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp hwα p hJ.mem_J).symm⟩

variable [Finite G]

namespace Sec3

variable {A R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
include hc

variable (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
include h32 h4 h34

theorem mem_rightConjugate_of_mem_W {D : ClassicalModel A}
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) (hq : 4 ≤ D.q) {p : G}
    (hJ : AParts A R T p (D.alpha p)) {W Y : Subgroup G} (hW : LeviChoice D p W Y) {y : G}
    (hy : y ∈ W) : y ∈ rightConjugate A g := by
  have h1 := hW.le_perfectCore hq hJ hy
  rw [← hc.inf_centralizer_eq h32 h4 h34 hJ, hc.perfectCore_eq h32 h4 h34 hOut] at h1
  exact (mem_inf.mp (CFSG.Quasithin.perfectCore_le _ h1)).1

theorem not_le_normalizer_zpowers (hO2 : SymplecticOddCentralizerO2) {D : ClassicalModel A}
    (hfam : D.family = .symplectic) (hA : CFSG.Open.IsQuasisimple ↥A) (hch : Choice74 D R T g)
    {y : G} (hyA : y ∈ A) (hyg : y ∈ rightConjugate A g) (hyo : Odd (orderOf y))
    (hTy : T ≤ centralizer ((zpowers y : Subgroup G) : Set G)) :
    ¬ centralizer ((zpowers y : Subgroup G) : Set G) ⊓ centralizer (T : Set G) ≤
      normalizer (R : Set G) := by
  have hgy : g * y * g⁻¹ ∈ A := (mem_rightConjugate_iff A g y).mp hyg
  have hord : orderOf (g * y * g⁻¹) = orderOf y := by
    rw [show g * y * g⁻¹ = MulAut.conj g y from rfl, MulEquiv.orderOf_eq]
  have hNN := noNormalTwo_rightConjugate
    (hO2 G A D hfam hA hch.oddCenter hch.four_le _ hgy (hord ▸ hyo)) g
  rw [rightConjugate_inf, rightConjugate_centralizer_singleton,
    show g⁻¹ * (g * y * g⁻¹) * g = y by group, ← centralizer_closure, ← zpowers_eq_closure] at hNN
  exact hc.not_le_normalizer_of_noNormalTwo h32 h4 h34 (zpowers_le.mpr hyA) hTy hNN

theorem levi75_core
    {D : ClassicalModel A}
    (hch : Choice74 D R T g) {p : G} (hJ : AParts A R T p (D.alpha p)) {Y : Subgroup G}
    (hYA : Y ≤ A) (hYα : Y ≤ centralizer (D.alpha p : Set G))
    (hαL : D.alpha p ≤ layerCentralizer A Y)
    (hLq : CFSG.Open.IsQuasisimple ↥(layerCentralizer A Y))
    (hnoInv : NoInvolutoryCentralizing A (Y ⊔ layerCentralizer A Y))
    (hnn : T ≤ centralizer (Y : Set G) →
      ¬ centralizer (Y : Set G) ⊓ centralizer (T : Set G) ≤ normalizer (R : Set G)) :
    T ≤ centralizer (Y : Set G) ∧
      standardComponentIsStandard ((layerCentralizer A Y).subgroupOf (centralizer (Y : Set G))) ∧
      ¬ ((layerCentralizer A Y).subgroupOf (centralizer (Y : Set G))).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLA := layerCentralizer_le A Y
  have hTY : T ≤ centralizer (Y : Set G) := by
    intro t ht
    rw [mem_centralizer_iff]
    intro z hz
    obtain ⟨p', hp'A, hρ'⟩ := hc.exists_aPart h32 h4 h34 ht
    have hp' := hJ.aPart_le t ht p' hp'A hρ'
    have h1 : Commute p' z := mem_centralizer_iff.mp (hYα hz) p' hp'
    have h2 : Commute (t⁻¹ * p')⁻¹ z := ((hc.commute_of_mem (hYA hz) hρ').symm).inv_left
    have h3 := h1.mul_left h2
    rw [show p' * (t⁻¹ * p')⁻¹ = t by group] at h3
    exact h3.eq.symm
  have hTRL : T ≤ R ⊔ layerCentralizer A Y := by
    intro t ht
    obtain ⟨p', hp'A, hρ'⟩ := hc.exists_aPart h32 h4 h34 ht
    have hp' := hJ.aPart_le t ht p' hp'A hρ'
    rw [show t = p' * (t⁻¹ * p')⁻¹ by group]
    exact mul_mem (mem_sup_right (hαL hp')) (mem_sup_left (inv_mem hρ'))
  have hTL : T ⊓ layerCentralizer A Y = ⊥ := by
    rw [eq_bot_iff, ← hch.inf_eq_bot]
    exact inf_le_inf_left T (hLA.trans inf_le_left)
  have hRY : R ≤ centralizer (Y : Set G) := hc.sylowR.le.trans (centralizer_le hYA)
  have hRL' : R ≤ centralizer (layerCentralizer A Y : Set G) :=
    hc.sylowR.le.trans (centralizer_le (hLA.trans inf_le_left))
  have hRL : IsSylowOf 2 R (centralizer (Y : Set G) ⊓
      centralizer (layerCentralizer A Y : Set G) ⊓ normalizer (R : Set G)) := by
    refine isSylowOf_of_noInvolutory hc.hyp hc.sylowR hnoInv
      (le_inf (le_inf hRY hRL') (Subgroup.le_normalizer)) ?_ inf_le_right
    intro x hx
    obtain ⟨⟨hxY, hxL⟩, -⟩ := mem_inf.mp hx
    exact mem_centralizer_sup hxY hxL
  have hL2 : ∀ n : ℕ, 2 ^ n = Nat.card R →
      Nonempty (↥(layerCentralizer A Y) ≃* SL(2, GaloisField 2 n)) →
        ∀ c : G, ¬ Lemma34.conj R c ≤ layerCentralizer A Y := by
    intro _ _ _ c hle
    rw [conj_eq_rightConjugate] at hle
    exact hch.not_le c⁻¹ (hle.trans (hLA.trans inf_le_left))
  obtain ⟨hstd, hnn'⟩ := lemma38_of_le h4 h32 h34 hc.hyp hc.sylowR hYA hLq hLA
    (normalizer_inf_le_normalizer_layerCentralizer A Y) hRL hTRL hTL hc.card_eq
    (hnn hTY) hL2
  exact ⟨hTY, hstd, hnn'⟩

theorem standard_zpowers
    (hO2 : SymplecticOddCentralizerO2)
    {D : ClassicalModel A} (hfam : D.family = .symplectic) (hA : CFSG.Open.IsQuasisimple ↥A)
    (hch : Choice74 D R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    {p : G} (hJ : AParts A R T p (D.alpha p)) {W : Subgroup G} (hW : LeviChoice D p W W) {z : G}
    (hz : LeviOddElt A W (layerCentralizer A W) z) :
    T ≤ centralizer ((zpowers z : Subgroup G) : Set G) ∧
      standardComponentIsStandard ((layerCentralizer A W).subgroupOf
        (centralizer ((zpowers z : Subgroup G) : Set G))) ∧
      ¬ ((layerCentralizer A W).subgroupOf
        (centralizer ((zpowers z : Subgroup G) : Set G))).Normal := by
  have hzA : z ∈ A := (mem_inf.mp (hW.Y_le hz.mem)).1
  have hzα : z ∈ centralizer (D.alpha p : Set G) := (mem_inf.mp (hW.Y_le hz.mem)).2
  have h := hc.levi75_core h32 h4 h34 hch hJ (zpowers_le.mpr hzA) (zpowers_le.mpr hzα)
    (hz.layer ▸ hW.alpha_le) (hz.layer ▸ hW.quasisimple) (hz.layer ▸ hz.noInv) fun hTz =>
      hc.not_le_normalizer_zpowers h32 h4 h34 hO2 hfam hA hch hzA
        (hc.mem_rightConjugate_of_mem_W h32 h4 h34 hOut hch.four_le hJ hW hz.mem) hz.odd hTz
  rwa [hz.layer] at h

theorem levi75Y_sp_of
    (hO2 : SymplecticOddCentralizerO2)
    {D : ClassicalModel A} (hfam : D.family = .symplectic) (hA : CFSG.Open.IsQuasisimple ↥A)
    (hch : Choice74 D R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    {p : G} (hJ : AParts A R T p (D.alpha p)) {W : Subgroup G} (hW : LeviChoice D p W W) {y : G}
    (hy : LeviOddElt A W (layerCentralizer A W) y)
    (hfour : D.IsLTwoFour → orderOf y = 5 ∧
      (∀ σ : MulAut ↥A, σ * σ = 1 → (∀ x : ↥A, (x : G) ∈ zpowers y → σ x = x) →
        ∃ l ∈ layerCentralizer A W, ∀ z : ↥A, (z : G) ∈ layerCentralizer A W →
          ((σ z : ↥A) : G) = l * z * l⁻¹) ∧
      NoThreeCentralizing A (zpowers y ⊔ layerCentralizer A W) ∧
      ∃ y₃ : G, LeviOddElt A W (layerCentralizer A W) y₃ ∧ orderOf y₃ = 3) :
    Levi75Y D T (zpowers y) W (layerCentralizer A W) := by
  have hWA : W ≤ A := fun w hw => (mem_inf.mp (hW.Y_le hw)).1
  have hLW : layerCentralizer A W ≤ centralizer (W : Set G) :=
    (layerCentralizer_le A W).trans inf_le_right
  obtain ⟨hTy, hstd, hnn⟩ := hc.standard_zpowers h32 h4 h34 hO2 hfam hA hch hOut hJ hW hy
  refine
    { Y_ne_bot := fun h => hy.ne_one (zpowers_eq_bot.mp h)
      Y_le := zpowers_le.mpr (hWA hy.mem)
      T_le := hTy
      L_le := hy.layer ▸ layerCentralizer_le A (zpowers y)
      levi := hW.levi
      quasisimple := hW.quasisimple
      oddCenter := hW.oddCenter
      standard := hstd
      not_normal := hnn
      L_eq := hy.layer.symm
      diag := fun h => absurd h (ClassicalModel.not_isLinearFiveFour_of_symplectic hfam)
      noInv := hy.noInv
      outerFree := fun hD => (hfour hD).2.1
      sym := fun _ h => absurd hfam h
      spFour := fun hD _ => ?_ }
  obtain ⟨hy5, -, hthree, y₃, hy₃, hy₃3⟩ := hfour hD
  obtain ⟨-, s, -, -, hs, hWs, hLs, -⟩ := hW.sym hD
  obtain ⟨-, hstd₃, hnn₃⟩ := hc.standard_zpowers h32 h4 h34 hO2 hfam hA hch hOut hJ hW hy₃
  exact ⟨y, s, y₃, rfl, hy.mem, hy5, hs, hWs, hLs, le_centralizer_iff.mp hLW, hy₃.mem, hy₃3,
    hy₃.noInv, hstd₃, hnn₃, hthree⟩

end Sec3

theorem step75Y_of
    (h32 : Lemma32)
    (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) (h2 : Asc76Theorem2) (hOut : ClassicalOutCommOdd)
    (hF : ClassicalCentralizerCharTwo) (h222 : Classical222Large) (hRC : ClassicalRigidChoice)
    (hSY : SymplecticYChoice) (hO2 : SymplecticOddCentralizerO2) : Step75Y := by
  intro G _ _ A D R T g hA hTy hch
  have hc := hch.sec3 hA
  have hOut' := hOut ↥A hA.standard.1.1 hTy
  obtain ⟨t, ht, ht1⟩ := T.bot_or_exists_ne_one.resolve_left hc.T_ne_bot
  obtain ⟨p, hp, hρ⟩ := hc.exists_aPart h32 h4 h34 ht
  have hJ := hc.aParts_alpha h32 h4 h34 h2 hOut' hF hTy h222 hch ht ht1 hp hρ
  have hpp := hch.primary t ht ht1 p hp hρ
  by_cases hfam : D.family = .symplectic
  · obtain ⟨W, y, hW, hy, hfour⟩ :=
      hSY G A D hfam hA.standard.1 hch.oddCenter hch.four_le p hpp
    exact ⟨zpowers y, W, _,
      hc.levi75Y_sp_of h32 h4 h34 hO2 hfam hA.standard.1 hch hOut' hJ hW hy hfour⟩
  · obtain ⟨p₂, hJ₂⟩ := hc.exists_aParts_swap h32 h4 h34 h2 hOut' hF hTy h222 hch
    obtain ⟨W, Y, hW, hrig⟩ :=
      hRC.exists D hA.standard.1 hch.oddCenter hch.four_le hfam hpp
    exact ⟨Y, W, _, (hc.levi75_of h32 h4 h34 hch hOut' hJ hJ₂ hW hrig).toLevi75Y hfam⟩

end CFSG.ComponentClassification.RankTwoClassical
