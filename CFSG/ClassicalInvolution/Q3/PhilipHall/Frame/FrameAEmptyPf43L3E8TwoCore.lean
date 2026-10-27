module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Core
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43EndGame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8CaseA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf46OneOne
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent3Fam

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge.Fam
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace L3E8Cfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H Q E S : Subgroup T}

theorem prod_mem_sigmaNorm (cfg : L3E8Cfg K z J zJ H Q E S) {h : T}
    (hc : z * (h⁻¹ * z * h) = h⁻¹ * z * h * z) : h ∈ sigmaNorm K :=
  cfg.zconj_cent (Subgroup.mem_centralizer_singleton_iff.mpr hc.symm)

theorem prod_mem_factor (cfg : L3E8Cfg K z J zJ H Q E S) (h : T) :
    h⁻¹ * z * h ∈ conjSub h⁻¹ (firstFactor K) := by
  simpa using conj_mem_conjSub (n := h⁻¹) (cfg.Q_le_ht (cfg.E_le_Q cfg.z_mem_E))

theorem prod_factor_ne (cfg : L3E8Cfg K z J zJ H Q E S) {h : T}
    (hnot : h⁻¹ * z * h ∉ firstFactor K) : conjSub h⁻¹ (firstFactor K) ≠ firstFactor K :=
  fun e => hnot (e ▸ cfg.prod_mem_factor h)

theorem prod_isUniqueInvolution (cfg : L3E8Cfg K z J zJ H Q E S) (h : T) :
    IsUniqueInvolution (conjSub h⁻¹ K) (h⁻¹ * z * h) := by
  have := cfg.datum.unique.conj h⁻¹
  rwa [inv_inv] at this

theorem prod_sq (cfg : L3E8Cfg K z J zJ H Q E S) {h : T}
    (hc : z * (h⁻¹ * z * h) = h⁻¹ * z * h * z) :
    z * (h⁻¹ * z * h) * (z * (h⁻¹ * z * h)) = 1 := by
  have hz := cfg.datum.unique
  have hw2 : h⁻¹ * z * h * (h⁻¹ * z * h) = 1 := by
    calc h⁻¹ * z * h * (h⁻¹ * z * h) = h⁻¹ * (z * z) * h := by group
      _ = 1 := by rw [hz.sq]; group
  calc z * (h⁻¹ * z * h) * (z * (h⁻¹ * z * h)) =
        z * (h⁻¹ * z * h * z) * (h⁻¹ * z * h) := by group
    _ = z * (z * (h⁻¹ * z * h)) * (h⁻¹ * z * h) := by rw [hc]
    _ = z * z * (h⁻¹ * z * h * (h⁻¹ * z * h)) := by group
    _ = 1 := by rw [hz.sq, hw2, one_mul]

theorem prod_ne_one (cfg : L3E8Cfg K z J zJ H Q E S) {h : T} (hne : h⁻¹ * z * h ≠ z) :
    z * (h⁻¹ * z * h) ≠ 1 := fun h1 =>
  hne ((eq_inv_of_mul_eq_one_right h1).trans (inv_eq_of_mul_eq_one_right cfg.datum.unique.sq))

theorem prod_isPGroup (cfg : L3E8Cfg K z J zJ H Q E S) {h : T} (hne : h⁻¹ * z * h ≠ z)
    (hc : z * (h⁻¹ * z * h) = h⁻¹ * z * h * z) :
    IsPGroup 2 (Subgroup.zpowers (z * (h⁻¹ * z * h))) :=
  IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact cfg.prod_sq hc)
      (cfg.prod_ne_one hne), pow_one])

theorem z_mem_centralizer_prod {h : T} (hc : z * (h⁻¹ * z * h) = h⁻¹ * z * h * z) :
    z ∈ Subgroup.centralizer ({z * (h⁻¹ * z * h)} : Set T) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc z * (z * (h⁻¹ * z * h)) = z * (h⁻¹ * z * h * z) := by rw [hc]
    _ = z * (h⁻¹ * z * h) * z := by group

end L3E8Cfg

section Fam

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem omegaACore_centralizer_eq_coreFamily (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) {c : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    omegaACore Ω (Subgroup.centralizer ({c} : Set G)) = TwinADescent.coreFamily Ω c := by
  rw [← TwinADescent3.sylCoreFamily_eq hΩ h2 hc2]
  ext L
  constructor
  · rintro ⟨M, hM, hT, rfl⟩
    exact ⟨M, ⟨hM, hT⟩, rfl⟩
  · rintro ⟨M, ⟨hM, hT⟩, rfl⟩
    exact ⟨M, hM, hT, rfl⟩

theorem omegaAFam_centralizer_eq_cFam (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) {c : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    omegaAFam Ω (Subgroup.centralizer ({c} : Set G)) = TwinDisc.cFam Ω c := by
  unfold omegaAFam TwinDisc.cFam
  rw [omegaACore_centralizer_eq_coreFamily hΩ h2 hc2]

theorem secFam_aEmpty_of_cFam (hΩ : HypOmegaGen Ω) {c : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hA : ∀ L ∈ TwinDisc.cFam Ω c, AEmpty (TwinDisc.cFam Ω c) L) :
    ∀ M ∈ TwinDisc.secFam Ω c, AEmpty (TwinDisc.secFam Ω c) M := by
  have hΛ := TwinADescent.hypOmegaGen_coreFamily hΩ hc2
  have hΛX := hypOmegaGen_restrict hΛ (TwinDisc.coreHull Ω c)
  have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥(TwinDisc.coreHull Ω c))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(TwinDisc.coreHull Ω c)
  refine TwinADescent2.aEmpty_quotFamily_gen hΛX (TwinEdge.hypOmegaGen_quotFamily_odd hΛX hodd)
    hodd ?_
  rintro _ ⟨L₀, hL₀, hL₀X, rfl⟩
  exact Thm4Twin.aEmpty_restrict hΛ (subset_refl _) hL₀X (hA L₀ hL₀)

end Fam

section Cent

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {S : Subgroup T}

theorem FrameStd.cent_le_sigmaStarNorm_of_core [CaseIAmbient T] (hs : FrameStd K z J zJ)
    {a : T} (ha1 : a ≠ 1) {L : Subgroup T} (hL : L ∈ CoreAssembly.conjClass K) {P : Subgroup T}
    (hP : IsSylow2In P L) (hPX : P ≤ Subgroup.centralizer ({a} : Set T))
    (hnA : ¬ AEmpty (omegaAFam (CoreAssembly.conjClass K) (Subgroup.centralizer ({a} : Set T)))
      ((tightCore (L ⊓ Subgroup.centralizer ({a} : Set T))).subgroupOf
        (Subgroup.centralizer ({a} : Set T)))) :
    Subgroup.centralizer ({a} : Set T) ≤ sigmaStarNorm (CoreAssembly.conjClass K) L :=
  le_sigmaStarNorm_of_core hs.hyp (typeRHyp_omegaAFam hs.typeRHyp _)
    (Thm3A.thm3RGroupQuotG_of_belowG hs.below (hs.card_centralizer_lt ha1)) hL hP hPX hnA

theorem FrameCfg.le_sigmaNorm_of_le_sigmaStarNorm (cfg : FrameCfg K z J zJ S)
    (hU : UniqueCosetZ K z) {X : Subgroup T} (hzX : z ∈ X) {L : Subgroup T}
    (hL : L ∈ CoreAssembly.conjClass K)
    (h : X ≤ sigmaStarNorm (CoreAssembly.conjClass K) L) : X ≤ sigmaNorm K := by
  have hΩc : ConjInvariant (CoreAssembly.conjClass K) := cfg.datum.hyp.conjInvariant
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  obtain ⟨g, rfl⟩ := hL
  have h1 : conjSub z (conjSub g K) ∈ dstarComp (CoreAssembly.conjClass K) (conjSub g K) :=
    (mem_sigmaStarNorm_iff.mp (h hzX) (conjSub g K)).mp Relation.ReflTransGen.refl
  have h2 := dstarComp_conj hΩc h1 g⁻¹
  have e1 : conjSub g⁻¹ (conjSub z (conjSub g K)) = conjSub (g⁻¹ * z * g) K := by
    simp only [← conjSub_mul, mul_assoc]
  rw [e1, conjSub_inv_conjSub] at h2
  have h3 : g⁻¹ * z * g ∈ sigmaNorm K :=
    sigmaStarNorm_le_sigmaNorm K (T7A.mem_sigmaStarNorm_of_conj hΩc hK h2)
  have hgK : conjSub g K ∈ dstarComp (CoreAssembly.conjClass K) K :=
    (mem_sigmaStarNorm_iff.mp (cfg.sigmaNorm_le_sigmaStarNorm (hU g h3)) K).mp
      Relation.ReflTransGen.refl
  rw [sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hK hgK)] at h
  exact h.trans (sigmaStarNorm_le_sigmaNorm K)

end Cent

namespace L3E8Cfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H Q E S : Subgroup T}

theorem aEmpty_cFam_or_cent_le [CaseIAmbient T] (cfg : L3E8Cfg K z J zJ H Q E S)
    (hU : UniqueCosetZ K z) {a : T} (ha2 : IsPGroup 2 (Subgroup.zpowers a)) (ha1 : a ≠ 1)
    (hza : z ∈ Subgroup.centralizer ({a} : Set T)) :
    (∀ L ∈ TwinDisc.cFam (CoreAssembly.conjClass K) a,
        AEmpty (TwinDisc.cFam (CoreAssembly.conjClass K) a) L) ∨
      Subgroup.centralizer ({a} : Set T) ≤ sigmaNorm K := by
  by_cases hA : ∀ L ∈ TwinDisc.cFam (CoreAssembly.conjClass K) a,
      AEmpty (TwinDisc.cFam (CoreAssembly.conjClass K) a) L
  · exact Or.inl hA
  right
  push Not at hA
  obtain ⟨_, ⟨_, ⟨M, hM, rfl⟩, -, rfl⟩, hnA⟩ := hA
  obtain ⟨P, hP, hPc⟩ := TwinADescent.exists_sylow_centralizer_of_tq ha2 hM.2
  have h2 := TwinADescent3.isPGroup_two_quotient_conjClass cfg.datum.twoGroup
  rw [← omegaAFam_centralizer_eq_cFam cfg.datum.hyp h2 ha2] at hnA
  exact cfg.toFrameCfg.le_sigmaNorm_of_le_sigmaStarNorm hU hza hM.1
    (cfg.toFrameStd.cent_le_sigmaStarNorm_of_core ha1 hM.1 hP hPc hnA)

end L3E8Cfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
