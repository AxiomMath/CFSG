module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CompCplx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CompPar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CompAbs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverPocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5PocketOmega
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5PocketType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem t5_comp_cplx_false (hS : Asc82SchurU43) (hL : IsOm6Z2 L) {s : G}
    (hk : Kind5 L s 4 ∨ Kind5 L s 5) {J : Subgroup G}
    (hJ : IsComponentIn J (L ⊓ centralizer ({s} : Set G))) (h29 : IsL29 J)
    (hnp : ∀ u ∈ J, orderOf u = 2 → ¬ IsI4PlusIn L u) : False := by
  obtain ⟨V, i1, i2, i3, Q, hQ, φ, c, hφ, hc, hcomm⟩ := t5_comp_cplx_data hS hL hk
  letI := i1
  letI := i2
  letI := i3
  have h8 : 8 ∣ Nat.card ↥J := (t5_isL29_card_two_adic h29).1
  have h2dvd : 2 ∣ Nat.card ↥J := dvd_trans (by norm_num : 2 ∣ 8) h8
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu2⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  let g : G := (u : G)
  have hgJ : g ∈ J := u.2
  have hg2 : orderOf g = 2 := by
    simpa only [g] using (Subgroup.orderOf_coe u).trans hu2
  let H : Subgroup G := L ⊓ centralizer ({s} : Set G)
  have hgH : g ∈ H := hJ.1 hgJ
  have hgL : g ∈ L := (Subgroup.mem_inf.mp hgH).1
  let a : ↥H := ⟨g, hgH⟩
  let b : ↥L := ⟨g, hgL⟩
  have hu_sq : u * u = 1 := by
    rw [← pow_two, ← hu2]
    exact pow_orderOf_eq_one u
  have hg_sq : g * g = 1 := by
    have h := congrArg (fun x : ↥J => (x : G)) hu_sq
    simpa [g] using h
  have ha_sq : a * a = 1 := Subtype.ext hg_sq
  have hb_sq : b * b = 1 := Subtype.ext hg_sq
  let φH : ↥H →* omegaGroup hQ := φ.comp (Subgroup.inclusion inf_le_left)
  let ρ : ↥H →* (V ≃ₗ[ZMod 3] V) :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype.comp
      ((omegaGroup hQ).subtype.comp φH)
  have hφa : φH a = φ b := congrArg φ (by
    apply Subtype.ext
    rw [Subgroup.coe_inclusion])
  have hcomm' : ∀ x : ↥H, ∀ v, ρ x (c v) = c (ρ x v) := by
    intro x v
    have hxL : (x : G) ∈ L := (Subgroup.mem_inf.mp x.2).1
    have hxs : s * (x : G) = (x : G) * s := by
      have hmem : (x : G) ∈ Subgroup.centralizer ({s} : Set G) := (Subgroup.mem_inf.mp x.2).2
      exact (Subgroup.mem_centralizer_singleton_iff.mp hmem).symm
    have hx' : (Subgroup.inclusion inf_le_left x : ↥L) = ⟨(x : G), hxL⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_inclusion]
    have hφx : φH x = φ ⟨(x : G), hxL⟩ := congrArg φ hx'
    have h := hcomm ⟨(x : G), hxL⟩ hxs v
    rw [← hφx] at h
    simpa only [ρ, MonoidHom.comp_apply, Subgroup.subtype_apply] using h
  let v₀ : OGroup Q := ((φH a : omegaGroup hQ) : OGroup Q)
  have hv_sq : v₀ * v₀ = 1 := by
    have h2 : φH a * φH a = 1 := by rw [← map_mul, ha_sq, map_one]
    simpa [v₀] using congrArg (fun x : omegaGroup hQ => (x : OGroup Q)) h2
  have hv1 : v₀ ≠ 1 := by
    intro h1
    have hφ1 : φH a = 1 := Subtype.ext h1
    have hφb1 : φ b = 1 := by rw [← hφa]; exact hφ1
    have hb1 : b = 1 :=
      (hφ.oddCentralCover hL).eq_one_of_mul_self_eq_one (MonoidHom.mem_ker.mpr hφb1) hb_sq
    have hg1 : g = 1 := by
      have h := congrArg (fun x : ↥L => (x : G)) hb1
      simpa [b] using h
    rw [hg1, orderOf_one] at hg2
    exact absurd hg2 (by decide)
  have ha2 : ∀ v, ρ a (ρ a v) = v := by
    intro v
    have h1 : ρ a * ρ a = 1 := by rw [← map_mul, ha_sq, map_one]
    have h2 := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) h1
    simpa using h2
  let W : Submodule (ZMod 3) V := commSp v₀
  have hρa : ρ a = (v₀ : V ≃ₗ[ZMod 3] V) := rfl
  have hW : ∀ v, v ∈ W ↔ ρ a v = -v := by
    intro v
    have h1 : v ∈ W ↔ (v₀ : V ≃ₗ[ZMod 3] V) v = -v := by
      change v ∈ commSp v₀ ↔ (v₀ : V ≃ₗ[ZMod 3] V) v = -v
      exact mem_commSp_iff hv_sq
    constructor
    · intro h
      rw [h1] at h
      rwa [hρa]
    · intro h
      rw [h1]
      rw [hρa] at h
      exact h
  have hJperf : Group.IsPerfect ↥(J.subgroupOf H) := hJ.2.1.1
  have ha : a ∈ J.subgroupOf H := Subgroup.mem_subgroupOf.mpr hgJ
  have hparity : Module.finrank (ZMod 3) W % 4 = 0 :=
    t5_cplx_perfect_parity ρ c hc hcomm' hJperf ha ha2 W hW
  have h4dvd : invDim v₀ % 4 = 0 := by
    simpa only [invDim, W] using hparity
  have htype := t5_omega_involution_type (Q := Q) hφ.finrank_eq hv_sq (φH a).2
  have htype4 : invType v₀ = (4, 1) := by
    rcases htype with h0 | h2 | h4 | h6
    · exfalso
      have hd0 : invDim v₀ = 0 := by simpa only [invType] using congrArg Prod.fst h0
      exact hv1 ((invDim_eq_zero_iff hv_sq).mp hd0)
    · exfalso
      have hd2 : invDim v₀ = 2 := by simpa only [invType] using congrArg Prod.fst h2
      rw [hd2] at h4dvd
      exact absurd h4dvd (by decide)
    · exact h4
    · exfalso
      have hd6 : invDim v₀ = 6 := by simpa only [invType] using congrArg Prod.fst h6
      rw [hd6] at h4dvd
      exact absurd h4dvd (by decide)
  have hPocketA : IsI4PlusIn (⊤ : Subgroup ↥(omegaGroup hQ)) (φH a) := by
    refine (t5_isI4PlusIn_omega_iff hφ.finrank_eq hφ.quadSign_eq hv_sq ?_).mpr htype4
    intro h1
    exact hv1 (congrArg (fun x : omegaGroup hQ => (x : OGroup Q)) h1)
  have hPocketH : IsI4PlusIn (⊤ : Subgroup ↥(omegaGroup hQ)) (φ b) := by
    rw [hφa] at hPocketA
    exact hPocketA
  exact hnp g hgJ hg2 ((t5_isI4PlusIn_iff hL hφ hgL hg2).mpr hPocketH)

end CFSG.OddStandard.SmallF3.Omega
