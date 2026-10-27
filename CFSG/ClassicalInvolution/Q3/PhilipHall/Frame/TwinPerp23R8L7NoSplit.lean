module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19Sec6Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusLie

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr


section Fix

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem secAut_fix_of_comm_mem_oddCoreOf (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h2Ω : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (g : ↥(Subgroup.centralizer ({c} : Set G))) {J Q : Subgroup G} (hJ : J ∈ tqMembers3 Ω c)
    (hQ : IsSylow2In Q J) (hQc : Q ≤ Subgroup.centralizer ({c} : Set G))
    (h2 : IsPGroup 2 ↥(secImg Ω c J))
    (hgQ : ∀ x ∈ Q, (g : G) * x * (g : G)⁻¹ * x⁻¹ ∈ oddCoreOf (rLayer Ω c)) :
    ∀ y ∈ secImg Ω c J, TwinExitPf6.secAut Ω c hΩ hc2 g y = y := by
  intro y hy
  obtain ⟨a, haQ, rfl⟩ := Fus.exists_of_mem_secImg_syl hc2 hJ hQ hQc h2 hy
  have hHn := TwinExitPf6.normal_coreHull hΩ hc2
  set a' : ↥(coreHull Ω c) :=
    ⟨g * (a : ↥(Subgroup.centralizer ({c} : Set G))) * g⁻¹, hHn.conj_mem _ a.2 g⟩
  rw [TwinExitPf6.secAut_mk hΩ hc2 g a a' rfl]
  have hdY : (((a' * a⁻¹ : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set G))) : G) =
      (g : G) * ((a : ↥(Subgroup.centralizer ({c} : Set G))) : G) * (g : G)⁻¹ *
        ((a : ↥(Subgroup.centralizer ({c} : Set G))) : G)⁻¹ := rfl
  have hd : a' * a⁻¹ ∈ classicalInvolutionOddCore ↥(coreHull Ω c) := by
    apply R56.mem_oddCore_coreHull_of_mem_oddCoreOf_coreLayer
    rw [show coreLayer Ω c = rLayer Ω c from TwinPerpV3.coreHull_map_eq_rLayer hΩ hc2 h2Ω, hdY]
    exact hgQ _ haQ
  have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) (a' * a⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hd
  rwa [map_mul, map_inv, mul_inv_eq_one] at h1

end Fix

section NoSplit


theorem no_split_e {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K' W : Subgroup Y} {u e g : Y} (hc : P23Cfg n Y R S t K' W u e g) (hA6 : SecAE R e 6)
    {P₀ P₀' : Subgroup Y} (hP₀ : IsSylow2In P₀ (tightCore R)) (hP₀' : IsSylow2In P₀' K')
    (hP₀e : P₀ ≤ Subgroup.centralizer ({e} : Set Y))
    (hP₀'e : P₀' ≤ Subgroup.centralizer ({e} : Set Y))
    {w : Y} (hwe : w ∈ Subgroup.centralizer ({e} : Set Y)) (hwodd : Odd (orderOf w))
    (hwP : ∀ x ∈ P₀, w * x * w⁻¹ ∈ P₀) (hwnt : ∃ x ∈ P₀, w * x ≠ x * w)
    (hwP' : ∀ x ∈ P₀', w * x * w⁻¹ * x⁻¹ ∈ oddCoreOf (rLayer (Om R) e)) : False := by
  classical
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc.data.he2
  have h2Ω : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hS := p23_q8Section hc.std.perp hc.data.he2
  obtain ⟨I⟩ := hA6
  have hgen : pSpan (TwinDisc.secFam (Om R) e) = ⊤ := TwinDisc.AE5.hgen_of hS
  have h8 := TwinDisc.AE5.members_card8 (by norm_num : 5 ≤ 6) hS I
  have h2 := TwinDisc.AE5.members_twoN (by norm_num : 5 ≤ 6) hS I
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hKtq : tightCore R ∈ tqMembers3 (Om R) e :=
    ⟨hK, TwinADescent3.mem_tq_of_sylCent hΩ h2Ω hK ⟨P₀, hP₀, hP₀e⟩⟩
  have hK'tq : K' ∈ tqMembers3 (Om R) e :=
    ⟨hc.std.hK'.1, TwinADescent3.mem_tq_of_sylCent hΩ h2Ω hc.std.hK'.1 ⟨P₀', hP₀', hP₀'e⟩⟩
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  obtain ⟨_, _, hzA⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hKtq hz
  obtain ⟨_, _, hzA'⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hK'tq hz'
  have hA := TwinDisc.secImg_mem_secFam hKtq
  have hA' := TwinDisc.secImg_mem_secFam hK'tq
  obtain ⟨β, hβ, b₀, hlab⟩ := I.label _ hA
  obtain ⟨γ, hγ, c₀, hlab'⟩ := I.label _ hA'
  have hγβ : γ = β := AE.eq_of_zBar_eq (by norm_num : (6 : ℕ) ≠ 8)
    ((I.map_eq_zBar (by norm_num) hA' (h8 _ hA') hlab' hzA').symm.trans
      (I.map_eq_zBar (by norm_num) hA (h8 _ hA) hlab hzA))
  have hlabβ : ((secImg (Om R) e K').subgroupOf (pSpan (TwinDisc.secFam (Om R) e))).map I.φ =
      memBar β hβ c₀ := by
    rw [hlab']
    subst hγβ
    rfl
  set D := ZTwo.AEData.ofIdent I hgen
  have hDφ : ∀ (y : SecQ R e) (hy : y ∈ pSpan (TwinDisc.secFam (Om R) e)),
      D.φ y = I.φ ⟨y, hy⟩ := fun _ _ => rfl
  set σ := TwinExitPf6.secAut (Om R) e hΩ hc2 ⟨w, hwe⟩
  obtain ⟨v, hv⟩ := D.exists_wr σ (fun L hL => TwinExitPf10.secAut_map_secFam hΩ hc2 ⟨w, hwe⟩ hL)
  have hfix : ∀ y ∈ secImg (Om R) e K', σ y = y :=
    secAut_fix_of_comm_mem_oddCoreOf hΩ hc2 h2Ω ⟨w, hwe⟩ hK'tq hP₀' hP₀'e (h2 _ hA') hwP'
  have hcent : ∀ z ∈ memBar β hβ c₀, mkQ 6 v * z * (mkQ 6 v)⁻¹ = z := by
    intro z hz
    rw [← hlabβ] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have h1 := hv (y : SecQ R e)
    rw [hfix _ (Subgroup.mem_subgroupOf.mp hy), hDφ _ y.2] at h1
    exact h1.symm
  have h4 := TwinThinPf19.pow_four_cent_memBar (by norm_num : 5 ≤ 6) β hβ c₀ v hcent b₀
  have hσj : ∀ (j : ℕ) (y : SecQ R e),
      D.φ (σ^[j] y) = (mkQ 6 v) ^ j * D.φ y * ((mkQ 6 v) ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro y; simp
    | succ j ih =>
      intro y
      rw [Function.iterate_succ_apply', hv (σ^[j] y), ih y, pow_succ']
      group
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e))
  have hTs : IsSylow2In P₀ (TwinADescent.coreAt e (tightCore R)) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hKtq.2).mpr ⟨hP₀, hP₀e⟩
  have hιH : ∀ x : ↥P₀, (⟨x, hP₀e x.2⟩ : ↥(Subgroup.centralizer ({e} : Set Y))) ∈
      coreHull (Om R) e := fun x =>
    TwinDisc.le_coreHull hKtq (Subgroup.mem_subgroupOf.mpr (hTs.1 x.2))
  let ι : ↥P₀ → ↥(coreHull (Om R) e) := fun x => ⟨⟨x, hP₀e x.2⟩, hιH x⟩
  let κ : ↥P₀ → ↥P₀ := fun x => ⟨w * x * w⁻¹, hwP x x.2⟩
  have hmem : ∀ x : ↥P₀, π (ι x) ∈ secImg (Om R) e (tightCore R) := fun x =>
    ⟨ι x, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr (hTs.1 x.2)), rfl⟩
  have hσκ : ∀ (j : ℕ) (x : ↥P₀), σ^[j] (π (ι x)) = π (ι (κ^[j] x)) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply' (⇑σ) j, ih x, Function.iterate_succ_apply' κ j]
      exact TwinExitPf6.secAut_mk hΩ hc2 ⟨w, hwe⟩ _ _ rfl
  set A : Subgroup ↥(coreHull (Om R) e) :=
    (P₀.subgroupOf (Subgroup.centralizer ({e} : Set Y))).subgroupOf (coreHull (Om R) e)
  have hA2 : IsPGroup 2 ↥A :=
    (hP₀.2.1.comap_of_injective _ (Subgroup.subtype_injective _)).comap_of_injective _
      (Subgroup.subtype_injective _)
  have hNodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥(coreHull (Om R) e))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hAN : A ⊓ classicalInvolutionOddCore ↥(coreHull (Om R) e) = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd _ hA2 le_rfl
      (hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  have hιA : ∀ x : ↥P₀, ι x ∈ A := fun x =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr x.2)
  have hπinj : ∀ x x' : ↥P₀, π (ι x) = π (ι x') → x = x' := by
    intro x x' hxx'
    have h1 : (ι x)⁻¹ * ι x' ∈ A ⊓ classicalInvolutionOddCore ↥(coreHull (Om R) e) :=
      ⟨A.mul_mem (A.inv_mem (hιA x)) (hιA x'), QuotientGroup.eq.mp hxx'⟩
    rw [hAN, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact Subtype.ext (congrArg (fun z : ↥(coreHull (Om R) e) =>
      ((z : ↥(Subgroup.centralizer ({e} : Set Y))) : Y)) h1)
  have hP4 : ∀ x : ↥P₀, κ^[4] x = x := by
    intro x
    have hφ : D.φ (π (ι x)) ∈ memBar β hβ b₀ := by
      rw [← hlab, hDφ _ (le_pSpan hA (hmem x))]
      exact I.mem_map hA (hmem x)
    have he : D.φ (π (ι (κ^[4] x))) = D.φ (π (ι x)) := by
      rw [← hσκ 4 x, hσj 4, h4 _ hφ]
    rw [hDφ _ (le_pSpan hA (hmem _)), hDφ _ (le_pSpan hA (hmem x))] at he
    exact hπinj _ _ (I.injOn (by norm_num) hA (h8 _ hA) hlab (hmem _) (hmem x) he)
  have hκ : ∀ (j : ℕ) (x : ↥P₀), ((κ^[j] x : ↥P₀) : Y) = w ^ j * x * (w ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply' κ j]
      show w * ((κ^[j] x : ↥P₀) : Y) * w⁻¹ = _
      rw [ih x, pow_succ']
      group
  obtain ⟨x, hx, hne⟩ := hwnt
  apply hne
  have hp1 : Function.IsPeriodicPt κ (orderOf w) ⟨x, hx⟩ := by
    apply Subtype.ext
    rw [hκ, pow_orderOf_eq_one]
    simp
  have hp := hp1.gcd (hP4 ⟨x, hx⟩)
  have hg1 : Nat.gcd (orderOf w) 4 = 1 := by
    have : Nat.Coprime (orderOf w) (2 ^ 2) :=
      Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hwodd)
    simpa using this
  rw [hg1] at hp
  have h1 := hκ 1 ⟨x, hx⟩
  rw [hp, pow_one] at h1
  calc w * x = w * x * w⁻¹ * w := by group
    _ = x * w := by rw [← h1]

end NoSplit

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7
