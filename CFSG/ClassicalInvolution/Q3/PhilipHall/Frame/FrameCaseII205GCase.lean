module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205GMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf2
public import CFSG.ClassicalInvolution.Q3.Q3T6DExact
public import CFSG.ClassicalInvolution.SmallCases.NDBG1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FrameCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205A
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII207Cent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII2010Final
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3S204
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3S208
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf36Outer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf19Thm3A

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Q3

open scoped commutatorElement

section Defs

@[expose] def FrameCaseIITGS : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [FrameSimple T], Thm3A.Thm3RBelowG (Nat.card T) →
    (∃ a b : T, a * b ≠ b * a) → CIT3Below (Nat.card T) →
    TL4.TightBelowRPlus 3 (Nat.card T) → ¬ TwoSubgroupsFourGenerated T →
    ∀ (R : Subgroup T) (t : T), FrameTightDatum R t →
      ∀ (J : Subgroup T) (zK zJ a g : T),
        AViol (CoreAssembly.conjClass R) R J zK zJ →
        a ∈ pairNormalizers R J zK zJ → a * zJ * a⁻¹ = zK → conjSub a J ≠ R →
        conjSub g R = conjSub a J → g * zK * g⁻¹ = zK →
        aStar (CoreAssembly.conjClass R) R = CoreAssembly.conjClass R → False

end Defs

section Steps

theorem frameC205_of_hyp51 (hCent : Frame20ACentX') (hCov : FrameXCover) {G : Type} [Group G]
    [Finite G] [FrameCore G] {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G}
    {z t : G} (d : Std20Frame K K' J S R R' W V z t)
    (hB : ∀ a : G, Frame205Data d a → Hyp51 (Subgroup.closure ({z, t, a} : Set G)))
    (c4 : Concl20_4 S K K' J z) : Concl20_5 S K K' z := by
  show centralizerModOdd (S : Subgroup G)
      (K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K')) = Subgroup.zpowers z
  refine le_antisymm ?_ (Subgroup.zpowers_le.mpr d.z_mem_cmo_L)
  by_contra hnot
  obtain ⟨u, hu, hu'⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have huM : u ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K') := d.cmo_L_le_cmo_M hu
  have hu1 : u ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J ⊔
      Subgroup.zpowers z := c4.1 ▸ huM
  set A' := centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J with hA'def
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (A' : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff.mpr fun x => ?_)
    have hx : ∀ y ∈ A', z * y * z⁻¹ = y := fun y hy => by
      have hyz := Subgroup.mem_centralizer_singleton_iff.mp (d.hSz hy.1.1)
      calc z * y * z⁻¹ = y * z * z⁻¹ := by rw [← hyz]
        _ = y := by group
    constructor
    · intro hxA
      rw [hx x hxA]
      exact hxA
    · intro hy
      have hyz := Subgroup.mem_centralizer_singleton_iff.mp (d.hSz hy.1.1)
      have hyc : z⁻¹ * (z * x * z⁻¹) * z = z * x * z⁻¹ := by
        calc z⁻¹ * (z * x * z⁻¹) * z = z⁻¹ * ((z * x * z⁻¹) * z) := by group
          _ = z⁻¹ * (z * (z * x * z⁻¹)) := by rw [← hyz]
          _ = z * x * z⁻¹ := by group
      have : x = z⁻¹ * (z * x * z⁻¹) * z := by group
      rw [this, hyc]
      exact hy
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hzN] at hu1
  obtain ⟨a', ha', n, hn, rfl⟩ := hu1
  have haS : a' ∈ (S : Subgroup G) := ha'.1.1
  have hncmo : n ∈ centralizerModOdd (S : Subgroup G)
      (K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K')) :=
    (Subgroup.zpowers_le.mpr d.z_mem_cmo_L) hn
  have ha'cL : a' ∈ centralizerModOdd (S : Subgroup G)
      (K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K')) := by
    have := Subgroup.mul_mem _ hu (Subgroup.inv_mem _ hncmo)
    simpa using this
  have ha1 : a' ≠ 1 := by
    intro h
    have hmem : a' * n ∈ Subgroup.zpowers z := by
      rw [h, one_mul]
      exact hn
    exact hu' hmem
  have hp2 : IsPGroup 2 ↥(Subgroup.zpowers a') :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr haS)
  obtain ⟨m, hm2, hm1⟩ := late_exists_pow_invol hp2 ha1
  set a := a' ^ m with ha_def
  have ha₀A : a ∈ A' := Subgroup.pow_mem _ ha' m
  have ha₀cL : a ∈ centralizerModOdd (S : Subgroup G)
      (K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K')) := Subgroup.pow_mem _ ha'cL m
  have conf : AConf3 S K K' J z a := ⟨ha₀A, hm1, hm2, c4⟩
  have hcentX := hCent G K K' J S R R' W V z t d a conf ha₀cL
  have data : Frame205Data d a := ⟨conf, ha₀cL, hcentX⟩
  have hyp51 := hB a data
  have hcfg : AlphaCfgF S K K' J z t a := ⟨ha₀A, hm1, hm2, c4, hyp51⟩
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hXdef
  set α := alphaOf (Subgroup.closure ({t, z} : Set G)) with hαdef
  have hXN : X ≤ Subgroup.normalizer (α : Set G) := hcfg.sec20X_le_normalizer_alpha d
    (fun x hx => d.oddCoreOf_sec20X_le (hcentX x hx))
  obtain ⟨ρ, haρ, hρz, hρt, -⟩ := d.s_exists_rho_a conf
  have hρα : ρ ∈ Subgroup.normalizer (α : Set G) :=
    Asc77.T3CII.alpha_normalizer (mem_normalizer_Z_of_rho hρz hρt)
  have hXg : conjSub ρ⁻¹ X ≤ Subgroup.normalizer (α : Set G) := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    have hy' : y = ρ⁻¹ * (ρ⁻¹⁻¹ * y * ρ⁻¹) * ρ := by group
    rw [hy']
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ((Subgroup.normalizer _).inv_mem hρα)
      (hXN hy)) hρα
  have hYN : X ⊔ conjSub ρ⁻¹ X ⊔ Subgroup.zpowers ρ ≤ Subgroup.normalizer (α : Set G) :=
    sup_le (sup_le hXN hXg) (Subgroup.zpowers_le.mpr hρα)
  have htop : (⊤ : Subgroup G) ≤ X ⊔ conjSub ρ⁻¹ X ⊔ Subgroup.zpowers ρ := by
    rw [← d.gen]
    exact iSup₂_le fun L hL => hCov G K K' J S R R' W V z t d ρ hρz hρt L
      (by rw [d.star]; exact hL)
  have hnormal : α.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr (htop.trans hYN))
  have hα1 : α = ⊥ := FrameCore.oddNormal d.nonabelian _ hnormal (hcfg.alpha_facts d).1
  have hza : alphaOf (Subgroup.closure ({z, a} : Set G)) = ⊥ := by
    rw [(hcfg.alpha_facts d).2 _ (hcfg.za_le_B d) (hcfg.isElemAbelian2_za d)]
    exact hα1
  have hOz : ∀ o ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)), a * o = o * a := by
    intro o ho
    have haE : a ∈ Subgroup.closure ({z, a} : Set G) := Subgroup.subset_closure (by simp)
    have hzE : z ∈ Subgroup.closure ({z, a} : Set G) := Subgroup.subset_closure (by simp)
    have h1 : ⁅o, a⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({z} : Set G)),
        Subgroup.closure ({z, a} : Set G)⁆ := Subgroup.commutator_mem_commutator ho haE
    have h2 := commutator_le_alphaOf (Subgroup.closure ({z, a} : Set G)) hzE
      d.viol.hzK.ne_one h1
    rw [hza, Subgroup.mem_bot] at h2
    exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
  have hXc : ∀ x ∈ X, a * x = x * a := by
    intro x hx
    have hcO : ⁅a, x⁆ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
      rw [commutatorElement_def]
      exact d.oddCoreOf_sec20X_le (hcentX x hx)
    have hsq := comm_sq_one hm2 (hOz _ hcO)
    have h1 : ⁅a, x⁆ = 1 := by
      by_contra hne
      exact hne (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hcO
        (isPGroup_zpowers_of_mul_self_eq_one hsq hne))
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hYc : X ⊔ conjSub ρ⁻¹ X ⊔ Subgroup.zpowers ρ ≤ Subgroup.centralizer ({a} : Set G) := by
    refine sup_le (sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (hXc x hx).symm) (fun y hy => ?_)) (Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr haρ.symm))
    rw [mem_conjSub_iff] at hy
    have hc := hXc _ hy
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hρi : a * ρ⁻¹ = ρ⁻¹ * a := by
      calc a * ρ⁻¹ = ρ⁻¹ * (ρ * a) * ρ⁻¹ := by group
        _ = ρ⁻¹ * (a * ρ) * ρ⁻¹ := by rw [haρ]
        _ = ρ⁻¹ * a := by group
    have e : y = ρ⁻¹ * (ρ⁻¹⁻¹ * y * ρ⁻¹) * ρ := by group
    rw [e]
    calc ρ⁻¹ * (ρ⁻¹⁻¹ * y * ρ⁻¹) * ρ * a
        = ρ⁻¹ * (ρ⁻¹⁻¹ * y * ρ⁻¹) * (a * ρ) := by rw [haρ]; group
      _ = ρ⁻¹ * ((ρ⁻¹⁻¹ * y * ρ⁻¹) * a) * ρ := by group
      _ = ρ⁻¹ * (a * (ρ⁻¹⁻¹ * y * ρ⁻¹)) * ρ := by rw [← hc]
      _ = (a * ρ⁻¹) * (ρ⁻¹⁻¹ * y * ρ⁻¹) * ρ := by rw [hρi]; group
      _ = a * (ρ⁻¹ * (ρ⁻¹⁻¹ * y * ρ⁻¹) * ρ) := by group
  have hcent : a ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYc (htop (Subgroup.mem_top g)))
  rw [FrameCore.center d.nonabelian, Subgroup.mem_bot] at hcent
  exact hm1 hcent

theorem frameC205CTG_of_steps (hCent : Frame20ACentX') (hB : FrameHyp51BG) (hCov : FrameXCover) :
    ∀ (G : Type) [Group G] [Finite G] [FrameCore G] (K K' J : Subgroup G) (S : Sylow 2 G)
      (R R' W V : Subgroup G) (z t : G), Std20Frame K K' J S R R' W V z t →
        Thm3A.Thm3RBelowG (Nat.card G) → CIT3Below (Nat.card G) →
        TL4.TightBelowRPlus 3 (Nat.card G) → Concl20_4 S K K' J z → Concl20_5 S K K' z := by
  intro G _ _ _ K K' J S R R' W V z t d hT hcit hP c4
  exact frameC205_of_hyp51 hCent hCov d
    (fun a data => hB G K K' J S R R' W V z t d a hT hcit hP data) c4

theorem frameCaseIITG_of_S (h : FrameCaseIITGS) : FrameCaseIITG := by
  intro T _ _ _ hT hnab hcit hP hl R t hdat J zK zJ a g hv ha hac hne hg hgK hs
  exact h T hT hnab hcit hP hl R t hdat J zK zJ a g hv ha hac hne hg hgK hs

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
