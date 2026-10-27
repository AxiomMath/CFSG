module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF10
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2Dich

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2 (imgX imgOf imgOf_conj false_of_imgOf_eq)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin (TwinT4Hyp)
open scoped commutatorElement

section TwinFree


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ b : Y}

theorem coreAt_ne_twin (F : FSet r n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b) :
    coreAt b (tightCore R) ≠ coreAt b K' := by
  intro e3
  obtain ⟨Q, hQ, hqQ⟩ := F.base.syl
  have hQK : Q ≤ tightCore R := hQ.1.trans (TwinADescent.coreAt_le_left b _)
  have hQK' : Q ≤ K' := by
    have := hQ.1.trans e3.le
    exact this.trans (TwinADescent.coreAt_le_left b K')
  have hs := F.hyp.std.setting
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hs.stand.hyp
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := hs.stand.mem
  have hK'Ω : K' ∈ CoreAssembly.conjClass (tightCore R) := hs.hK'.1
  have hne : K' ≠ tightCore R := hs.hne
  have h1 := (hΩ.omega4 (tightCore R) hK K' hK'Ω hne.symm).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : Nat.card ↥Q ∣ Nat.card ↥(tightCore R ⊓ K') :=
    Subgroup.card_dvd_of_le (le_inf hQK hQK')
  obtain ⟨k, hk⟩ := hQ.2.1.exists_card_eq
  have h8 := hqQ.eight_le
  rw [hk] at hdvd h8
  have h2 := (padicValNat_dvd_iff_le Nat.card_pos.ne').mp hdvd
  have h3 : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem center_of_noTwin (F : FSet r n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b)
    {H : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))}
    (hKH : (coreAt b (tightCore R)).subgroupOf (Subgroup.centralizer ({b} : Set Y)) ≤ H)
    (htH : (⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))) ∈ H)
    (hno : ¬ ∃ K'' ∈ twinSet (CoreAssembly.conjClass (imgX b H (tightCore R))) (imgX b H (tightCore R)),
      K'' ≠ imgX b H (tightCore R)) :
    IsUniqueInvolution (imgX b H (tightCore R)) (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
      (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ : ↥H)) ∧
    ∀ g : ↥H ⧸ classicalInvolutionOddCore ↥H, g * QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
      (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ : ↥H) * g⁻¹ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
        (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ : ↥H) := by
  classical
  set K : Subgroup Y := tightCore R with hKdef
  set tC : ↥(Subgroup.centralizer ({b} : Set Y)) := ⟨t, F.htC⟩ with htCdef
  set tH : ↥H := ⟨tC, htH⟩ with htHdef
  have hbase := F.base
  have hΛ := hbase.hypOmegaGen_fFam
  have hT4 := F.hT4 H
  have hKbar : imgX b H K ∈ famF b K H := by
    have hX : (coreAt b (conjSub 1 K)).subgroupOf (Subgroup.centralizer ({b} : Set Y)) ≤ H := by
      rw [conjSub_eq_self_of_mem (Subgroup.one_mem K)]
      exact hKH
    have := imgX_mem_famF (K := K) (c := 1) (b := b) (X := H) (Subgroup.one_mem _) hX
    rwa [conjSub_eq_self_of_mem (Subgroup.one_mem K)] at this
  have hu : IsUniqueInvolution (imgX b H K) (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) tH) :=
    isUniqueInvolution_imgF_X hT4 hKbar hbase.inv_core F.htC htH
  haveI : Fintype (↥H ⧸ classicalInvolutionOddCore ↥H) := Fintype.ofFinite _
  have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hOq : TightOddFree (↥H ⧸ classicalInvolutionOddCore ↥H) :=
    CFSG.ABGLocalTools.oddCore_quotient_oddCore_eq_bot
  have htHsq : tH * tH = 1 := Subtype.ext (Subtype.ext hbase.inv.sq)
  have hiso : ∀ g : ↥H ⧸ classicalInvolutionOddCore ↥H,
      (g * QuotientGroup.mk' (classicalInvolutionOddCore ↥H) tH * g⁻¹) *
          QuotientGroup.mk' (classicalInvolutionOddCore ↥H) tH =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥H) tH *
          (g * QuotientGroup.mk' (classicalInvolutionOddCore ↥H) tH * g⁻¹) →
      g * QuotientGroup.mk' (classicalInvolutionOddCore ↥H) tH * g⁻¹ =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥H) tH := by
    intro g hg
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ g
    by_contra hne
    set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥H) with hπ
    have hzsq : (h * tH * h⁻¹) * (h * tH * h⁻¹) = 1 := by
      calc (h * tH * h⁻¹) * (h * tH * h⁻¹) = h * (tH * tH) * h⁻¹ := by group
        _ = 1 := by rw [htHsq]; group
    have hc : π tH * π (h * tH * h⁻¹) = π (h * tH * h⁻¹) * π tH := by
      have := hg.symm
      simp only [map_mul, map_inv] at this ⊢
      exact this
    obtain ⟨m, hm, hcomm⟩ := OddQuot.exists_conj_commuting (N := classicalInvolutionOddCore ↥H)
      hodd hzsq ⟨1, by rw [pow_one, pow_two]; exact htHsq⟩ hc
    set s : ↥H := m * (h * tH * h⁻¹) * m⁻¹ with hs
    have hs2 : s * s = 1 := by
      calc s * s = m * ((h * tH * h⁻¹) * (h * tH * h⁻¹)) * m⁻¹ := by rw [hs]; group
        _ = 1 := by rw [hzsq]; group
    have hπm : π m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    have hπs : π s = π h * π tH * (π h)⁻¹ := by
      rw [hs]
      simp only [map_mul, map_inv, hπm, one_mul, inv_one, mul_one]
    have hst : s ≠ tH := by
      intro h1
      apply hne
      rw [← hπs, h1]
    have hsC : s * tH = tH * s := hcomm
    set sY : Y := (((s : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y))) : Y) with hsY
    have hsYC : sY ∈ Subgroup.centralizer ({b} : Set Y) := ((s : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y))).2
    have hsYt : sY * t = t * sY := congrArg (fun x : ↥H => (((x : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y))) : Y)) hsC
    have hsY2 : sY * sY = 1 := congrArg (fun x : ↥H => (((x : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y))) : Y)) hs2
    have hsYne : sY ≠ t := by
      intro h1
      apply hst
      exact Subtype.ext (Subtype.ext h1)
    have hsYconj : ∃ y : Y, y * t * y⁻¹ = sY := by
      refine ⟨(((m * h : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y))) : Y), ?_⟩
      have : (m * h) * tH * (m * h)⁻¹ = s := by rw [hs]; group
      have := congrArg (fun x : ↥H => (((x : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y))) : Y)) this
      simpa using this
    have hsw := swap_of_conj F.hr F.hP F.hyp F.h11 F.hbS F.hb2 F.hF₁ hsYt
      (Subgroup.mem_centralizer_singleton_iff.mp hsYC) hsY2 hsYne hsYconj
    set K₁ : Subgroup ↥(Subgroup.centralizer ({b} : Set Y)) := (coreAt b K).subgroupOf (Subgroup.centralizer ({b} : Set Y)) with hK₁
    set K₂ : Subgroup ↥(Subgroup.centralizer ({b} : Set Y)) := conjSub ((s : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y))) K₁ with hK₂
    have hK₂eq : K₂ = (coreAt b K').subgroupOf (Subgroup.centralizer ({b} : Set Y)) := by
      rw [hK₂, hK₁, Generic.conjSub_subgroupOf, TwinADescent.conjSub_coreAt hsYC]
      rw [hsw]
    have hK₁Λ : K₁ ∈ fFam b K := coreAt_subgroupOf_mem_fFam b K
    have hK₂Λ : K₂ ∈ fFam b K := by
      rw [hK₂, hK₁, Generic.conjSub_subgroupOf, TwinADescent.conjSub_coreAt hsYC]
      exact subgroupOf_mem_restrictFamily ⟨sY, hsYC, rfl⟩ (TwinADescent.coreAt_le_centralizer b _)
    have hK₂H : K₂ ≤ H := by
      have h1 := conjSub_mono (n := ((s : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y)))) hKH
      rwa [conjSub_eq_self_of_mem s.2] at h1
    have hne12 : K₁ ≠ K₂ := by
      rw [hK₂eq]
      exact subgroupOf_ne_of_ne (TwinADescent.coreAt_le_centralizer b _)
        (TwinADescent.coreAt_le_centralizer b _) (coreAt_ne_twin F)
    have hu₁ : IsUniqueInvolution K₁ tC :=
      isUniqueInvolution_subgroupOf hbase.inv_core (TwinADescent.coreAt_le_centralizer b _)
    have hsCt : ((s : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y))) * tC * ((s : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y)))⁻¹ = tC := by
      have h1 : ((s : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y))) * tC = tC * ((s : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y))) := congrArg Subtype.val hsC
      calc ((s : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y))) * tC * ((s : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y)))⁻¹ = (tC * ((s : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y)))) * ((s : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y)))⁻¹ := by
            rw [h1]
        _ = tC := by group
    have hu₂ : IsUniqueInvolution K₂ tC := by
      have := hu₁.conj ((s : ↥H) : ↥(Subgroup.centralizer ({b} : Set Y)))
      rwa [hsCt] at this
    have hπimg : conjSub (π s) (imgOf H K₁) = imgOf H K₂ := by
      rw [imgOf_conj H (L := K₁) s]
    have hmemK : conjSub (π s) (imgOf H K₁) ∈ twinSet
        (CoreAssembly.conjClass (imgX b H K)) (imgX b H K) := by
      refine ⟨⟨π s, rfl⟩, π tH, hu, ?_⟩
      have h1 := hu.conj (π s)
      have h2 : π s * π tH * (π s)⁻¹ = π tH := by
        rw [← map_inv, ← map_mul, ← map_mul, show s * tH * s⁻¹ = tH by
          calc s * tH * s⁻¹ = (tH * s) * s⁻¹ := by rw [hsC]
            _ = tH := by group]
      rw [h2] at h1
      exact h1
    have hEq : conjSub (π s) (imgOf H K₁) = imgX b H K := by
      by_contra hneq
      exact hno ⟨_, hmemK, hneq⟩
    rw [hπimg] at hEq
    exact false_of_imgOf_eq hΛ hK₁Λ hK₂Λ hne12 hu₁ hu₂ hKH hK₂H hEq.symm
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar (↥H ⧸ classicalInvolutionOddCore ↥H)
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) tH) hu.ne_one hu.sq hiso
  have hNle : N ≤ classicalInvolutionOddCore (↥H ⧸ classicalInvolutionOddCore ↥H) :=
    le_sSup ⟨hNn, hNodd⟩
  refine ⟨hu, fun g => ?_⟩
  have h1 := hNle (hN g)
  rw [hOq, Subgroup.mem_bot] at h1
  exact mul_inv_eq_one.mp h1

theorem tightInO2_of_noTwin (F : FSet r n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b)
    {H : Subgroup ↥(Subgroup.centralizer ({b} : Set Y))}
    (hKH : (coreAt b (tightCore R)).subgroupOf (Subgroup.centralizer ({b} : Set Y)) ≤ H)
    (htH : (⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))) ∈ H)
    (hno : ¬ ∃ K'' ∈ twinSet (CoreAssembly.conjClass (imgX b H (tightCore R))) (imgX b H (tightCore R)),
      K'' ≠ imgX b H (tightCore R)) :
    TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
      (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ : ↥H)) := by
  obtain ⟨hu, hcent⟩ := center_of_noTwin F hKH htH hno
  refine ⟨Subgroup.zpowers (QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
      (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ : ↥H)),
    ⟨fun x hx g => ?_⟩, isPGroup_zpowers_of_mul_self_eq_one hu.sq hu.ne_one,
    Subgroup.mem_zpowers _⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow, hcent g]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k

end TwinFree

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
