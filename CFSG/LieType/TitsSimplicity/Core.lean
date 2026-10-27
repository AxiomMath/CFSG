module

public import CFSG.LieType.TitsSimplicity.Descent
import Mathlib.Tactic.Group

public section

namespace CFSG.LieType.TitsSimplicity

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType
set_option hygiene false in
local notation "Φ" => RootSystem.ofCartan D.isFiniteType D.divisible

theorem exists_forall_isRightDescent : ∃ w₀ : W, ∀ i, (cs).IsRightDescent w₀ i := by
  have := finite_group D.isFiniteType
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max fun w : W => (cs).length w
  refine ⟨w₀, fun i => by_contra fun hi => ?_⟩
  have h := (cs).not_isRightDescent_iff.mp hi
  have := hw₀ (w₀ * (cs).simple i)
  omega

theorem ht_weylAction_neg {w₀ : W} (hw₀ : ∀ i, (cs).IsRightDescent w₀ i) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (h : 0 < ht γ) : ht (ρ w₀ γ) < 0 := by
  have hnn : 0 ≤ γ := by
    rcases nonneg_or_nonpos D.isFiniteType D.divisible hγ with h' | h'
    · exact h'
    · exfalso
      have : ht γ ≤ 0 := Finset.sum_nonpos fun j _ => h' j
      omega
  refine ht_neg_of_nonpos (weylAction_mem_roots _ w₀ hγ) ?_
  have hsum : ρ w₀ γ = ∑ j, γ j • ρ w₀ (Pi.single j 1) := by
    conv_lhs => rw [← sum_smul_single γ]
    simp only [map_sum, map_zsmul]
  intro k
  rw [hsum, Finset.sum_apply]
  refine Finset.sum_nonpos fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (hnn j) ((isRightDescent_iff _ w₀ j).1 (hw₀ j) k)

variable (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)

theorem nrep_conj_mem_negUnipotent_of_forall_isRightDescent {w₀ : W}
    (hw₀ : ∀ i, (cs).IsRightDescent w₀ i) {u : K} (hu : u ∈ posUnipotent D) :
    nrep hct w₀ * u * (nrep hct w₀)⁻¹ ∈ negUnipotent D :=
  conj_mem_of_forall_mem (fun _ hγ _ hy => rootGroup_le_negUnipotent
    (weylAction_mem_roots _ w₀ hγ.1) (ht_weylAction_neg hw₀ hγ.1 hγ.2)
    ((actsAs_nrep hct w₀).conj_mem hγ.1 hy)) hu

include hct in
theorem normalCore_borel_le_iSup (hBU : BruhatExtras D H) :
    (borel D H).normalCore ≤ ⨆ i, H i := by
  intro z hz
  obtain ⟨w₀, hw₀⟩ := exists_forall_isRightDescent (D := D)
  have h1 : (nrep hct w₀)⁻¹ * z * nrep hct w₀ ∈ borel D H := by
    have := (show ∀ b : K, b * z * b⁻¹ ∈ borel D H from hz) (nrep hct w₀)⁻¹
    rwa [inv_inv] at this
  rw [← SetLike.mem_coe, coe_borel hct, Set.mem_mul] at h1
  obtain ⟨t, ht, u, hu, htu⟩ := h1
  have ht' : nrep hct w₀ * t * (nrep hct w₀)⁻¹ ∈ ⨆ i, H i :=
    conj_mem_iSup_of_mem_weylN hct (nrep_mem_weylN hct w₀) ht
  have hu' := nrep_conj_mem_negUnipotent_of_forall_isRightDescent hct hw₀ hu
  have hz' : z = nrep hct w₀ * t * (nrep hct w₀)⁻¹ * (nrep hct w₀ * u * (nrep hct w₀)⁻¹) := by
    rw [show nrep hct w₀ * t * (nrep hct w₀)⁻¹ * (nrep hct w₀ * u * (nrep hct w₀)⁻¹) =
      nrep hct w₀ * (t * u) * (nrep hct w₀)⁻¹ by group, htu]
    group
  have hv : nrep hct w₀ * u * (nrep hct w₀)⁻¹ ∈ borel D H ⊓ negUnipotent D := by
    refine Subgroup.mem_inf.2 ⟨?_, hu'⟩
    have e : nrep hct w₀ * u * (nrep hct w₀)⁻¹ =
        (nrep hct w₀ * t * (nrep hct w₀)⁻¹)⁻¹ * z := by
      rw [hz']
      group
    rw [e]
    exact mul_mem (inv_mem (iSup_le_borel ht')) (Subgroup.normalCore_le _ hz)
  rw [hBU.borel_inf_negUnipotent, Subgroup.mem_bot] at hv
  rw [hz', hv, mul_one]
  exact ht'

include hct in
theorem normalCore_borel_le_center (hBU : BruhatExtras D H) :
    (borel D H).normalCore ≤ Subgroup.center K := by
  have hZT := normalCore_borel_le_iSup hct hBU
  have hneg : ∀ i, ∀ z ∈ (borel D H).normalCore, ∀ x ∈ D.rootGroup (-Pi.single i 1),
      z * x = x * z := by
    intro i z hz x hx
    have hα' : -Pi.single i 1 ∈ D.roots := (Φ).neg_mem _ ((Φ).single_mem i)
    have h1 : z * x * z⁻¹ ∈ D.rootGroup (-Pi.single i 1) :=
      (Subgroup.mem_normalizer_iff.1 (iSup_le_normalizer_rootGroup hct hα' (hZT hz)) x).1 hx
    have h2 : z * x * z⁻¹ * x⁻¹ ∈ borel D H ⊓ negUnipotent D := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.normalCore_le _ ?_, rootGroup_le_negUnipotent hα' ?_
        (mul_mem h1 (inv_mem hx))⟩
      · have : x * z⁻¹ * x⁻¹ ∈ (borel D H).normalCore :=
          (Subgroup.normalCore_normal _).conj_mem _ (inv_mem hz) x
        rw [show z * x * z⁻¹ * x⁻¹ = z * (x * z⁻¹ * x⁻¹) by group]
        exact mul_mem hz this
      · rw [ht_neg, ht_single]
        exact neg_one_lt_zero
    rw [hBU.borel_inf_negUnipotent, Subgroup.mem_bot] at h2
    calc z * x = z * x * z⁻¹ * x⁻¹ * (x * z) := by group
      _ = x * z := by rw [h2, one_mul]
  have hpos : ∀ i, ∀ z ∈ (borel D H).normalCore, ∀ x ∈ D.rootGroup (Pi.single i 1),
      z * x = x * z := by
    intro i z hz x hx
    have hy : (n i)⁻¹ * x * n i ∈ D.rootGroup (-Pi.single i 1) := by
      have := (actsAs_n hct i).inv_conj_mem ((Φ).single_mem i) hx
      rwa [CoxeterSystem.inv_simple, weylAction_simple_single] at this
    have hz' : (n i)⁻¹ * z * n i ∈ (borel D H).normalCore := by
      have := (Subgroup.normalCore_normal _).conj_mem _ hz (n i)⁻¹
      rwa [inv_inv] at this
    have h := hneg i _ hz' _ hy
    have h' : (n i)⁻¹ * (z * x) * n i = (n i)⁻¹ * (x * z) * n i :=
      calc (n i)⁻¹ * (z * x) * n i = (n i)⁻¹ * z * n i * ((n i)⁻¹ * x * n i) := by group
        _ = (n i)⁻¹ * x * n i * ((n i)⁻¹ * z * n i) := h
        _ = (n i)⁻¹ * (x * z) * n i := by group
    simpa using h'
  have hL : ∀ i, rankOne D.rootGroup i ≤
      Subgroup.centralizer ((borel D H).normalCore : Set K) := fun i =>
    sup_le (fun x hx z hz => hpos i z hz x hx) (fun x hx z hz => hneg i z hz x hx)
  have htop : (⊤ : Subgroup K) ≤ Subgroup.centralizer ((borel D H).normalCore : Set K) := by
    rw [← iSup_leviAmalgam_eq_top (isCTRootSystem D.isFiniteType D.divisible) hct]
    exact iSup_le fun J => iSup₂_le fun j _ => hL j
  rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, Subgroup.le_centralizer_iff]
  exact htop

variable (hext : SteinbergExtras D n H)

include hct hext in
theorem center_le_borel : Subgroup.center K ≤ borel D H := by
  rw [← normalizer_borel hct hext]
  exact Subgroup.center_le_normalizer _

include hct hext in
theorem center_eq_normalCore_borel (hBU : BruhatExtras D H) :
    Subgroup.center K = (borel D H).normalCore :=
  le_antisymm (Subgroup.normal_le_normalCore.2 (center_le_borel hct hext))
    (normalCore_borel_le_center hct hBU)

include hct hext in
theorem center_eq_iInf_map_conj_borel (hBU : BruhatExtras D H) :
    Subgroup.center K = ⨅ g : K, (borel D H).map (MulAut.conj g) := by
  rw [center_eq_normalCore_borel hct hext hBU, Subgroup.normalCore_eq_iInf_map_conj]

end CFSG.LieType.TitsSimplicity
