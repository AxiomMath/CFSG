module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5K1Lin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5K1Fix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem t5_layerCent_le_inf (L : Subgroup G) (s : G) :
    layerCent L s ≤ L ⊓ centralizer ({s} : Set G) := by
  unfold layerCent CFSG.inSubgroup
  exact Subgroup.map_subtype_le _

theorem t5_k1_comm {φ : ↥L →* omegaGroup hQ} {s : G} {τ : OGroup Q}
    (hact : CoverAct L φ s (orthToSim Q τ)) {g : G} (hgL : g ∈ L) (hgs : s * g = g * s) :
    τ * ((φ ⟨g, hgL⟩ : omegaGroup hQ) : OGroup Q) =
      ((φ ⟨g, hgL⟩ : omegaGroup hQ) : OGroup Q) * τ := by
  have h := t5_cent_map_mem hact (l := ⟨g, hgL⟩) hgs
  rw [simAct_orthToSim] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem t5_k1_layer_fix {φ : ↥L →* omegaGroup hQ} (hφ : IsCoverMap L φ) {s : G} {τ : OGroup Q}
    (hty : invType τ = (4, -1)) (hact : CoverAct L φ s (orthToSim Q τ)) {g : G}
    (hg : g ∈ layerCent L s) (hgL : g ∈ L) :
    fixSp τ ≤ fixSp ((φ ⟨g, hgL⟩ : omegaGroup hQ) : OGroup Q) := by
  let H : Subgroup G := L ⊓ centralizer ({s} : Set G)
  let φH : ↥H →* omegaGroup hQ := φ.comp (Subgroup.inclusion inf_le_left)
  let ρ : ↥H →* (V ≃ₗ[ZMod 3] V) :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype.comp
      ((omegaGroup hQ).subtype.comp φH)
  have hW : Module.finrank (ZMod 3) (fixSp τ) = 2 :=
    t5_k1_finrank_fixSp hφ.finrank_eq hty
  have hinv : ∀ a : ↥H, ∀ w ∈ fixSp τ, ρ a w ∈ fixSp τ := by
    intro a w hw
    have haL : (a : G) ∈ L := (Subgroup.mem_inf.mp a.2).1
    have has : s * (a : G) = (a : G) * s := by
      have hmem : (a : G) ∈ Subgroup.centralizer ({s} : Set G) := (Subgroup.mem_inf.mp a.2).2
      exact (Subgroup.mem_centralizer_singleton_iff.mp hmem).symm
    have ha' : (Subgroup.inclusion inf_le_left a : ↥L) = ⟨(a : G), haL⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_inclusion]
    have hcommv : τ * ((φH a : omegaGroup hQ) : OGroup Q) =
        ((φH a : omegaGroup hQ) : OGroup Q) * τ := by
      rw [show φH a = φ ⟨(a : G), haL⟩ from congrArg φ ha']
      exact t5_k1_comm hact haL has
    have hcommv' : (τ : V ≃ₗ[ZMod 3] V) * (ρ a : V ≃ₗ[ZMod 3] V) =
        (ρ a : V ≃ₗ[ZMod 3] V) * (τ : V ≃ₗ[ZMod 3] V) := by
      have h := congrArg (fun e : OGroup Q => (e : V ≃ₗ[ZMod 3] V)) hcommv
      simp only [Subgroup.coe_mul, ρ, MonoidHom.comp_apply, Subgroup.subtype_apply] at h
      exact h
    rw [mem_fixSp_iff]
    calc (τ : V ≃ₗ[ZMod 3] V) (ρ a w)
        = ((τ : V ≃ₗ[ZMod 3] V) * (ρ a : V ≃ₗ[ZMod 3] V)) w :=
          (LinearEquiv.mul_apply _ _ _).symm
      _ = ((ρ a : V ≃ₗ[ZMod 3] V) * (τ : V ≃ₗ[ZMod 3] V)) w := by rw [hcommv']
      _ = (ρ a : V ≃ₗ[ZMod 3] V) ((τ : V ≃ₗ[ZMod 3] V) w) :=
          LinearEquiv.mul_apply _ _ _
      _ = (ρ a : V ≃ₗ[ZMod 3] V) w := by rw [mem_fixSp_iff.mp hw]
  have hfixP : ∀ p ∈ CFSG.layer ↥H, ∀ w ∈ fixSp τ, ρ p w = w :=
    t5_perfect_fix_of_finrank_two ρ (fixSp τ) hW hinv
      (CFSG.LocalCores.layer_isPerfect (G := ↥H))
  intro w hw
  rw [mem_fixSp_iff]
  have hmap : g ∈ (CFSG.layer ↥H).map H.subtype := by
    simpa only [layerCent, CFSG.inSubgroup, H] using hg
  obtain ⟨p, hp, hpval⟩ := Subgroup.mem_map.mp hmap
  have hp' : (Subgroup.inclusion inf_le_left p : ↥L) = ⟨g, hgL⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_inclusion]
    exact hpval
  have hp_eq : ((φH p : omegaGroup hQ) : OGroup Q) =
      ((φ ⟨g, hgL⟩ : omegaGroup hQ) : OGroup Q) := by
    rw [show φH p = φ ⟨g, hgL⟩ from congrArg φ hp']
  have hρ : (((φH p : omegaGroup hQ) : OGroup Q) : V ≃ₗ[ZMod 3] V) w = w :=
    hfixP p hp w hw
  rw [← hp_eq]
  exact hρ

theorem t5_k1_not_mem (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (hφ : IsCoverMap L φ) {s : G}
    {τ : OGroup Q} (hty : invType τ = (4, -1)) (hact : CoverAct L φ s (orthToSim Q τ)) {t : G}
    (ht : t ∈ centerIn L) (ht2 : orderOf t = 2) : t ∉ layerCent L s := by
  intro hmem
  have htL : t ∈ L := (t5_layerCent_le_inf L s hmem).1
  have hfix := t5_k1_layer_fix hφ hty hact hmem htL
  have hπ := hφ.map_central hL ht ht2 htL
  have hW2 := t5_k1_finrank_fixSp hφ.finrank_eq hty
  have hbot : fixSp τ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    have h1 : (piOrth Q : V ≃ₗ[ZMod 3] V) w = w := by
      have h2 := mem_fixSp_iff.mp (hfix hw)
      rw [hπ] at h2
      exact h2
    rw [coe_piOrth_apply] at h1
    have h2 : (2 : ZMod 3) • w = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp h1.symm
    exact (isUnit_of_invertible (2 : ZMod 3)).smul_eq_zero.mp h2
  rw [hbot, finrank_bot] at hW2
  exact absurd hW2 (by decide)

theorem t5_k1_layer_type (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (hφ : IsCoverMap L φ)
    {s : G} {τ : OGroup Q} (hτ : τ * τ = 1) (hty : invType τ = (4, -1))
    (hact : CoverAct L φ s (orthToSim Q τ)) {u : G} (hu : u ∈ layerCent L s)
    (hu2 : orderOf u = 2) (huL : u ∈ L) :
    ((φ ⟨u, huL⟩ : omegaGroup hQ) : OGroup Q) * ((φ ⟨u, huL⟩ : omegaGroup hQ) : OGroup Q) = 1 ∧
      φ ⟨u, huL⟩ ≠ 1 ∧ invType ((φ ⟨u, huL⟩ : omegaGroup hQ) : OGroup Q) = (2, -1) := by
  let a : ↥L := ⟨u, huL⟩
  let v : OGroup Q := ((φ a : omegaGroup hQ) : OGroup Q)
  have hu_sq : u * u = 1 := by
    rw [← pow_two, ← hu2]
    exact pow_orderOf_eq_one u
  have ha_sq : a * a = 1 := Subtype.ext hu_sq
  have hv_sq : v * v = 1 := by
    have h2 : φ a * φ a = 1 := by rw [← map_mul, ha_sq, map_one]
    simpa [v] using congrArg (fun x : omegaGroup hQ => (x : OGroup Q)) h2
  have hφa_ne : φ a ≠ 1 := by
    intro h1
    have ha1 : a = 1 :=
      (hφ.oddCentralCover hL).eq_one_of_mul_self_eq_one (MonoidHom.mem_ker.mpr h1) ha_sq
    have hu1 : u = 1 := by
      have h := congrArg (fun x : ↥L => (x : G)) ha1
      simpa [a] using h
    rw [hu1, orderOf_one] at hu2
    exact absurd hu2 (by decide)
  have hv_ne : v ≠ 1 := by
    intro h1
    exact hφa_ne (Subtype.ext h1)
  have hus : s * u = u * s := by
    have hmem : u ∈ Subgroup.centralizer ({s} : Set G) := (t5_layerCent_le_inf L s hu).2
    exact (Subgroup.mem_centralizer_singleton_iff.mp hmem).symm
  have hcomm : τ * v = v * τ := t5_k1_comm hact huL hus
  have hfix : fixSp τ ≤ fixSp v := t5_k1_layer_fix hφ hty hact hu huL
  have ht5 : invType v = (2, -1) :=
    t5_k1_invType_layer hQ hφ.finrank_eq hτ hty hv_sq hv_ne (φ a).2 hcomm hfix
  exact ⟨hv_sq, hφa_ne, ht5⟩

end CFSG.OddStandard.SmallF3.Omega
