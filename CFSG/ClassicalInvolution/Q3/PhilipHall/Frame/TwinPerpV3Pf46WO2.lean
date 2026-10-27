module

public import CFSG.ClassicalInvolution.Q3.TL3T38
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf27Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf29ExitCases

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

section WO2

variable {n : ℕ}

theorem inO2C_iff {G : Type} [Group G] {z u : G} :
    InO2C z u ↔ ∃ P : Subgroup G, TC.IsNormalTwoIn P u ∧ z ∈ P := by
  constructor
  · rintro ⟨P, hPC, hPn, hP2, hzP⟩
    refine ⟨P, ⟨hPC, hP2, fun c hc p hp => ?_⟩, hzP⟩
    have := hPn.conj_mem ⟨p, hPC hp⟩ (Subgroup.mem_subgroupOf.mpr hp) ⟨c, hc⟩
    exact Subgroup.mem_subgroupOf.mp this
  · rintro ⟨P, ⟨hPC, hP2, hPn⟩, hzP⟩
    refine ⟨P, hPC, ?_, hP2, hzP⟩
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPC]
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro p
    exact ⟨fun hp => hPn c hc p hp, fun hp => by
      have := hPn c⁻¹ ((Subgroup.centralizer ({u} : Set G)).inv_mem hc) _ hp
      simpa [mul_assoc] using this⟩

theorem inO2C_conj {G : Type} [Group G] {z u : G} (h : InO2C z u) (j : G) :
    InO2C (j * z * j⁻¹) (j * u * j⁻¹) := by
  obtain ⟨P, hP, hzP⟩ := inO2C_iff.mp h
  exact inO2C_iff.mpr ⟨conjSub j P, hP.conj j, conj_mem_conjSub hzP⟩

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem v3_P_normalTwo {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J) :
    TC.IsNormalTwoIn (⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M) t := by
  have hd := hStd.datum
  have hΩ := hd.hyp
  have hz := hd.hz
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set V := twinSet Ω K with hV
  refine ⟨iSup₂_le fun M hM x hx => ?_, ?_, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((isUniqueInvolution_of_mem_twinSet hz hM).commute_of_mem hx).symm
  · have h := TC.Thin.isPGroup_pSpan_of_comm (p := 2) (S := V) (fun L hL => h2g L hL.1) ?_
    · exact h
    · intro L hL L' hL' hne x hx y hy
      have hzL := isUniqueInvolution_of_mem_twinSet hz hL
      have hzL' := isUniqueInvolution_of_mem_twinSet hz hL'
      have hn : L ≤ Subgroup.normalizer (L' : Set Y) :=
        Sec6Gen.le_normalizer_of_twin hΩ hL.1 hL'.1 hne hzL hzL'
      exact Sec6Gen.commutes_of_twin_of_isPGroup hΩ hL.1 hL'.1 hne hzL hzL' le_rfl le_rfl
        ((h2g L hL.1).to_sup_of_normal_right' (h2g L' hL'.1) hn) x hx y hy
  · intro c hc p hp
    have hct : c * t * c⁻¹ = t := by
      rw [mul_inv_eq_iff_eq_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp hc
    have hmem : ∀ J ∈ V, conjSub c J ∈ V := fun J hJ =>
      ⟨hΩ.conjInvariant c J hJ.1, t, hz, by
        have := (isUniqueInvolution_of_mem_twinSet hz hJ).conj c
        rwa [hct] at this⟩
    have h1 : conjSub c (⨆ M ∈ V, M) ≤ ⨆ M ∈ V, M := by
      rw [conjSub_iSup₂]
      exact iSup₂_le fun J hJ => le_iSup₂_of_le (conjSub c J) (hmem J hJ) le_rfl
    exact h1 (conj_mem_conjSub hp)

theorem v3_mem_P {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃) :
    u₁ * u₂ ∈ (⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M) ∧
      t ∈ (⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M) := by
  have hd := hStd.datum
  have hK : K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K := mem_twinSet_self hd.mem hd.hz
  have h1 : K ≤ ⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M := le_iSup₂_of_le K hK le_rfl
  have h2 : K' ≤ ⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M :=
    le_iSup₂_of_le K' hd.hK' le_rfl
  exact ⟨Subgroup.mul_mem _ (h1 hd.hu₁.1) (h2 hd.hu₂.1), h1 hd.hz.mem⟩

theorem inO2C_c_t {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J) : InO2C (u₁ * u₂) t :=
  inO2C_iff.mpr ⟨_, v3_P_normalTwo hStd h2g, (v3_mem_P hStd).1⟩

theorem inO2C_tc_t {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J) :
    InO2C (t * (u₁ * u₂)) t :=
  inO2C_iff.mpr ⟨_, v3_P_normalTwo hStd h2g,
    Subgroup.mul_mem _ (v3_mem_P hStd).2 (v3_mem_P hStd).1⟩

theorem exists_inverting {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J) :
    ∃ j : Y, j * t * j⁻¹ = t ∧ j * (u₁ * u₂) * j⁻¹ = t * (u₁ * u₂) := by
  have hd := hStd.datum
  have hΩ := hd.hyp
  have hz := hd.hz
  have hzK' := hd.hzK'
  obtain ⟨e⟩ := members_q8_of_isPGroup hStd.perp h2g K hd.mem
  have hu₁ := hd.hu₁
  have hsq : u₁ * u₁ = t := T7A.sq_eq_of_orderOf_four hz hu₁.1 hu₁.2
  have hq : ∀ a : QuaternionGroup 2, a ^ 2 ≠ 1 → ∃ b : QuaternionGroup 2, b * a * b⁻¹ = a⁻¹ := by
    decide +kernel
  have ha2 : (e ⟨u₁, hu₁.1⟩) ^ 2 ≠ 1 := by
    intro h
    have h' : (⟨u₁, hu₁.1⟩ : ↥K) ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, h, map_one]
    have h'' : u₁ ^ 2 = 1 := congrArg Subtype.val h'
    have := orderOf_dvd_of_pow_eq_one h''
    rw [hu₁.2] at this
    omega
  obtain ⟨b, hb⟩ := hq _ ha2
  set j' : ↥K := e.symm b with hj'
  have hj'inv : (j' : Y) * u₁ * (j' : Y)⁻¹ = u₁⁻¹ := by
    have h1 : j' * ⟨u₁, hu₁.1⟩ * j'⁻¹ = ⟨u₁, hu₁.1⟩⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, map_inv, hj', MulEquiv.apply_symm_apply, hb]
    exact congrArg Subtype.val h1
  refine ⟨(j' : Y), ?_, ?_⟩
  · have := hz.commute_of_mem j'.2
    have h1 : t * (j' : Y) = (j' : Y) * t := this
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.symm
  ·
    have hn : K ≤ Subgroup.normalizer (K' : Set Y) :=
      Sec6Gen.le_normalizer_of_twin hΩ hd.mem hd.hK'.1 hd.hne.symm hz hzK'
    have hcomm : Commutes K K' :=
      Sec6Gen.commutes_of_twin_of_isPGroup hΩ hd.mem hd.hK'.1 hd.hne.symm hz hzK' le_rfl le_rfl
        ((h2g K hd.mem).to_sup_of_normal_right' (h2g K' hd.hK'.1) hn)
    have hc2 : (j' : Y) * u₂ = u₂ * (j' : Y) := hcomm _ j'.2 _ hd.hu₂.1
    have hj2 : (j' : Y) * u₂ * (j' : Y)⁻¹ = u₂ := by rw [hc2]; group
    have e1 : (j' : Y) * (u₁ * u₂) * (j' : Y)⁻¹ =
        ((j' : Y) * u₁ * (j' : Y)⁻¹) * ((j' : Y) * u₂ * (j' : Y)⁻¹) := by group
    have hu1inv : u₁⁻¹ = t * u₁ := by
      have h4 : u₁ ^ 4 = 1 := by
        have := pow_orderOf_eq_one u₁
        rwa [hu₁.2] at this
      apply inv_eq_of_mul_eq_one_right
      calc u₁ * (t * u₁) = u₁ ^ 4 := by rw [← hsq]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := h4
    rw [e1, hj'inv, hj2, hu1inv]
    group

variable (n) in
@[expose] def V3ExitWO2Core : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
    V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
      (∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
        WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) = {V}) →
        InO2C t (u₁ * u₂)

theorem v3ExitWO2_of_core (h : V3ExitWO2Core n) : V3ExitWO2 n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ hin hW
  have h1 := h Y R S t K K' K₃ u₁ u₂ u₃ K₄ hin hW
  obtain ⟨hStd, hF, hα, h2g, hno⟩ := hin
  obtain ⟨j, hjt, hjc⟩ := exists_inverting hStd h2g
  have h4 := inO2C_conj h1 j
  rw [hjt, hjc] at h4
  exact ⟨h1, inO2C_c_t hStd h2g, h4, inO2C_tc_t hStd h2g⟩

end WO2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
