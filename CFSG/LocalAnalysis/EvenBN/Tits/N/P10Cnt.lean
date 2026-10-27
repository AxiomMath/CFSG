module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P09Reg
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P05Core
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P05Syl
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Hyper

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Open
open scoped Pointwise commutatorElement

section Cnt

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem node10_eps_range_V (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀) :
    hd.s56EpsHom.range = d.E := by
  have hsurj := hd.s56_V_eps_surj h49 hz
  refine le_antisymm ?_ ?_
  · rintro k ⟨v, rfl⟩
    exact hd.s56_V_eps_mem_E v.2
  · intro s hs
    obtain ⟨v, hv, hvs⟩ := hsurj s hs
    exact ⟨⟨v, hv⟩, hvs⟩

theorem node10_relIndex_E_inf_F (hd : d.Hyp) : (d.E ⊓ d.F).relIndex d.E = 2 := by
  have h := Subgroup.relIndex_mul_card (H := d.E ⊓ d.F) (K := d.E)
  rw [inf_eq_left.2 (inf_le_left : d.E ⊓ d.F ≤ d.E), hd.s56_card_E_inf_F, hd.A_facts.1] at h
  omega

theorem node10_card_V_inf_N (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz : d.S56Z0 z₀) : Nat.card (d.s56V ⊓ d.N : Subgroup G) = 2 ^ 9 := by
  have hrange := node10_eps_range_V h49 hd hz
  have hcomap : (d.E ⊓ d.F).comap hd.s56EpsHom = (d.s56V ⊓ d.N).subgroupOf d.s56V := by
    ext v
    rw [Subgroup.mem_comap, mem_subgroupOf, mem_inf, mem_inf, hd.s56EpsHom_apply]
    constructor
    · rintro ⟨-, hF⟩
      exact ⟨v.2, (hd.s56_mem_N_iff_eps h49 (hd.s56_Q_le_Q0 v.2.1)).2 hF⟩
    · rintro ⟨-, hN⟩
      exact ⟨hd.s56_V_eps_mem_E v.2, hd.s56_eps_mem_F_of_N h49 hN⟩
  have hidx : ((d.E ⊓ d.F).comap hd.s56EpsHom).index = 2 := by
    rw [Subgroup.index_comap, hrange]
    exact node10_relIndex_E_inf_F hd
  have h1 := Subgroup.card_mul_index ((d.E ⊓ d.F).comap hd.s56EpsHom)
  rw [hidx, hcomap, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : d.s56V ⊓ d.N ≤
    d.s56V)).toEquiv, hd.s56_card_V h49 hz] at h1
  omega

theorem node10_Q2_decomp (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    {q : G} (hq : q ∈ d.s56Q2) : ∃ v ∈ d.s56V, q * v⁻¹ ∈ centralizer (d.A : Set G) := by
  have hqM : q ∈ d.M := (Data.s56_mem_Q2_iff).1 hq |>.1
  obtain ⟨v, hv, hvε⟩ := hd.s56_V_eps_surj h49 hz (d.s56Eps q) (hd.s56_eps_mem_E hqM)
  refine ⟨v, hv, mem_CA_of_Q2_eps hd (mul_mem hq (inv_mem (Data.s56_V_le_Q2 d hv))) ?_⟩
  rw [hd.s56_eps_mul_Q2' hq (inv_mem (Data.s56_V_le_Q2 d hv)),
    hd.s56_eps_inv_Q2 (Data.s56_V_le_Q2 d hv), hvε]
  exact hd.s56_E_sq (hd.s56_eps_mem_E hqM)

theorem node10_Q2_eq_D (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (hR : d.ρ.range = titsD.subgroupOf titsA) : d.s56Q2 = d.s56V ⊔ zpowers d.t := by
  refine le_antisymm (fun q hq => ?_) (sup_le (Data.s56_V_le_Q2 d) (zpowers_le.2 (t_mem_Q2 hd)))
  obtain ⟨v, hv, hc⟩ := node10_Q2_decomp h49 hd hz hq
  rw [CA_eq_A_of_range hd hR] at hc
  have hA : d.A ≤ d.s56V ⊔ zpowers d.t :=
    sup_le (le_sup_of_le_left (hd.s56_E_le_V h49)) le_sup_right
  have e : q = (q * v⁻¹) * v := by group
  rw [e]
  exact mul_mem (hA hc) (mem_sup_left hv)

theorem node10_Q2_eq_Â (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    {y : G} (hy : IsV5 d y) : d.s56Q2 = d.s56V ⊔ zpowers d.t ⊔ zpowers y := by
  have hCy := CA_eq_A_sup_of_IsV5 hd hy
  refine le_antisymm (fun q hq => ?_) (sup_le (sup_le (Data.s56_V_le_Q2 d)
    (zpowers_le.2 (t_mem_Q2 hd))) (zpowers_le.2 (CA_le_Q2 (by
      rw [hCy]; exact mem_sup_right (mem_zpowers y)))))
  obtain ⟨v, hv, hc⟩ := node10_Q2_decomp h49 hd hz hq
  rw [hCy] at hc
  have hA : d.A ⊔ zpowers y ≤ d.s56V ⊔ zpowers d.t ⊔ zpowers y :=
    sup_le (le_sup_of_le_left (sup_le (le_sup_of_le_left (hd.s56_E_le_V h49))
      le_sup_right)) le_sup_right
  have e : q = (q * v⁻¹) * v := by group
  rw [e]
  exact mul_mem (hA hc) (mem_sup_left (mem_sup_left hv))

theorem node10_card_P (hd : d.Hyp) (hQ : IsElemAbQuot d.s56P d.B 5) :
    Nat.card d.s56P = 2 ^ 11 := by
  have h := Subgroup.relIndex_mul_card (H := d.B) (K := d.s56P)
  rw [inf_eq_left.2 hd.s56_B_le_P, hQ.2.2.2.2, hd.B_facts.2.2.2.1] at h
  omega

theorem node10_eps_surj_P (hd : d.Hyp)
    (h7 : ∀ s ∈ (fun f => d.t * f) '' (d.F : Set G), ∃ p ∈ d.s56P, p * d.t * p⁻¹ = s) {f : G}
    (hf : f ∈ d.F) : ∃ p ∈ d.s56P, d.s56Eps p = f := by
  obtain ⟨p, hp, hpf⟩ := h7 (d.t * f) ⟨f, hf, rfl⟩
  refine ⟨p, hp, ?_⟩
  have := hd.s56_conj_t p
  rw [hpf] at this
  exact (mul_left_cancel this).symm

theorem node10_card_P_inf_M (h49 : d.Thm49Statement) (hd : d.Hyp) (hP : Nat.card d.s56P = 2 ^ 11)
    (hsurj : ∀ f ∈ d.F, ∃ p ∈ d.s56P, d.s56Eps p = f) :
    Nat.card (d.s56P ⊓ d.M : Subgroup G) = 2 ^ 10 := by
  have hrange : (node09Eps h49 hd).range = d.F := by
    refine le_antisymm ?_ (fun f hf => ?_)
    · rintro _ ⟨p, rfl⟩
      exact hd.s56_eps_mem_F_of_N h49 (Data.s56_P_le_N d p.2)
    · obtain ⟨p, hp, hpf⟩ := hsurj f hf
      exact ⟨⟨p, hp⟩, hpf⟩
  have hcomap : (d.E ⊓ d.F).comap (node09Eps h49 hd) = (d.s56P ⊓ d.M).subgroupOf d.s56P := by
    ext p
    rw [Subgroup.mem_comap, mem_subgroupOf, mem_inf, mem_inf, node09Eps_apply]
    constructor
    · rintro ⟨hE, -⟩
      exact ⟨p.2, (mem_inf.1 ((hd.s56_P0_inf_M_iff h49).2 ⟨Data.s56_P_le_P0 d p.2,
        d.s56Eps p.1, hE, hd.s56_conj_t p.1⟩)).2⟩
    · rintro ⟨-, hM⟩
      obtain ⟨-, e, he, hpe⟩ := (hd.s56_P0_inf_M_iff h49).1
        (mem_inf.2 ⟨Data.s56_P_le_P0 d p.2, hM⟩)
      have h := hd.s56_conj_t p.1
      rw [hpe] at h
      have hε : d.s56Eps p.1 = e := (mul_left_cancel h).symm
      exact ⟨hε ▸ he, hd.s56_eps_mem_F_of_N h49 (Data.s56_P_le_N d p.2)⟩
  have hidx : ((d.E ⊓ d.F).comap (node09Eps h49 hd)).index = 2 := by
    rw [Subgroup.index_comap, hrange]
    have h := Subgroup.relIndex_mul_card (H := d.E ⊓ d.F) (K := d.F)
    rw [inf_eq_left.2 (inf_le_right : d.E ⊓ d.F ≤ d.F), hd.s56_card_E_inf_F, hd.B_facts.1] at h
    omega
  have h1 := Subgroup.card_mul_index ((d.E ⊓ d.F).comap (node09Eps h49 hd))
  rw [hidx, hcomap, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : d.s56P ⊓ d.M ≤
    d.s56P)).toEquiv, hP] at h1
  omega

theorem node10_PM_le_Q0 (h49 : d.Thm49Statement) (hd : d.Hyp) {p : G}
    (hp : p ∈ d.s56P ⊓ d.M) : p ∈ d.s56Q0 := by
  obtain ⟨hpP, hpM⟩ := mem_inf.1 hp
  refine hd.s56_mem_Q0_of_cent_hyperplane h49 hpM (H := d.E ⊓ d.F) inf_le_left
    (node10_relIndex_E_inf_F hd).le fun h hh => ?_
  have := Data.s56_P_conj_F d hpP (mem_inf.1 hh).2
  calc p * h = (p * h * p⁻¹) * p := by group
    _ = h * p := by rw [this]

theorem node10_mem_Q2_iff (hd : d.Hyp) {p : G} (hp : p ∈ d.s56P ⊓ d.M) :
    p ∈ d.s56Q2 ↔ p * d.pv 8 = d.pv 8 * p := by
  obtain ⟨hpP, hpM⟩ := mem_inf.1 hp
  have hv8 := Data.s56_pv8_mem_E d
  constructor
  · intro h
    exact ((Data.s56_mem_Q2_iff).1 h).2 _ hv8 |>.symm
  · intro h
    refine (Data.s56_mem_Q2_iff).2 ⟨hpM, fun e he => ?_⟩
    have hFc : ∀ f ∈ d.F, f * p = p * f := fun f hf => by
      have := Data.s56_P_conj_F d hpP hf
      calc f * p = (p * f * p⁻¹) * p := by rw [this]
        _ = p * f := by group
    rcases hd.s56_E_cases he with hf | hf
    · exact hFc e hf
    · have hee : e = d.pv 8 * (d.pv 8 * e) := by
        calc e = (d.pv 8 * d.pv 8) * e := by rw [hd.s56_E_sq hv8, one_mul]
          _ = d.pv 8 * (d.pv 8 * e) := by group
      have h2 := hFc _ hf
      calc e * p = (d.pv 8 * (d.pv 8 * e)) * p := by rw [← hee]
        _ = d.pv 8 * ((d.pv 8 * e) * p) := by group
        _ = d.pv 8 * (p * (d.pv 8 * e)) := by rw [h2]
        _ = (d.pv 8 * p) * (d.pv 8 * e) := by group
        _ = (p * d.pv 8) * (d.pv 8 * e) := by rw [h]
        _ = p * (d.pv 8 * (d.pv 8 * e)) := by group
        _ = p * e := by rw [← hee]

theorem node10_card_PM_eq (h49 : d.Thm49Statement) (hd : d.Hyp) :
    Nat.card (d.s56P ⊓ d.M : Subgroup G) = 2 * Nat.card (d.s56P ⊓ d.s56Q2 : Subgroup G) := by
  have hQ2M : d.s56Q2 ≤ d.M := Q2_le_M d
  have hle : d.s56P ⊓ d.s56Q2 ≤ d.s56P ⊓ d.M := inf_le_inf_left _ hQ2M
  have hv7F := hd.s56_pv7_mem_F
  have hv8 := Data.s56_pv8_mem_E d
  have hv7PM : d.pv 7 ∈ d.s56P ⊓ d.M :=
    mem_inf.2 ⟨hd.s56_B_le_P (Data.s56_F_le_B d hv7F), hd.s56_F_le_M hv7F⟩
  have hidx : ((d.s56P ⊓ d.s56Q2).subgroupOf (d.s56P ⊓ d.M)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨d.pv 7, hv7PM⟩, fun b => ?_⟩
    have hbQ0 := node10_PM_le_Q0 h49 hd b.2
    have hcomm := ((hd.s56_mem_Q0_iff h49).1 hbQ0).2 _ hv8
    have hbM : (b : G) ∈ d.M := (mem_inf.1 b.2).2
    have hprod : (b : G) * d.pv 7 * d.pv 8 * ((b : G) * d.pv 7)⁻¹ * (d.pv 8)⁻¹ =
        ((b : G) * d.pv 8 * (b : G)⁻¹ * (d.pv 8)⁻¹) * d.z := by
      have h1 := Data.s56_pv7_conj_pv8 d
      have h2 : (b : G) * d.z * (b : G)⁻¹ = d.z := by
        rw [hd.s56_M_comm_zpowers hbM (mem_zpowers d.z)]
        group
      have h3 : d.pv 8 * d.z * (d.pv 8)⁻¹ = d.z := by
        rw [← hd.s56_E_comm hd.s56_z_mem_E hv8]
        group
      calc (b : G) * d.pv 7 * d.pv 8 * ((b : G) * d.pv 7)⁻¹ * (d.pv 8)⁻¹
          = (b : G) * (d.pv 7 * d.pv 8 * (d.pv 7)⁻¹) * (b : G)⁻¹ * (d.pv 8)⁻¹ := by group
        _ = (b : G) * (d.pv 8 * d.z) * (b : G)⁻¹ * (d.pv 8)⁻¹ := by rw [h1]
        _ = ((b : G) * d.pv 8 * (b : G)⁻¹) * ((b : G) * d.z * (b : G)⁻¹) * (d.pv 8)⁻¹ := by
            group
        _ = ((b : G) * d.pv 8 * (b : G)⁻¹) * d.z * (d.pv 8)⁻¹ := by rw [h2]
        _ = ((b : G) * d.pv 8 * (b : G)⁻¹ * (d.pv 8)⁻¹) * (d.pv 8 * d.z * (d.pv 8)⁻¹) := by group
        _ = ((b : G) * d.pv 8 * (b : G)⁻¹ * (d.pv 8)⁻¹) * d.z := by rw [h3]
    have hmemK : ∀ g : ↥(d.s56P ⊓ d.M), g ∈ (d.s56P ⊓ d.s56Q2).subgroupOf (d.s56P ⊓ d.M) ↔
        (g : G) * d.pv 8 = d.pv 8 * (g : G) := fun g => by
      rw [mem_subgroupOf, mem_inf]
      constructor
      · rintro ⟨-, hq⟩
        exact ((Data.s56_mem_Q2_iff).1 hq).2 _ hv8 |>.symm
      · intro h
        exact ⟨(mem_inf.1 g.2).1, (node10_mem_Q2_iff hd g.2).2 h⟩
    have hmul : ((b * ⟨d.pv 7, hv7PM⟩ : ↥(d.s56P ⊓ d.M)) : G) = (b : G) * d.pv 7 := rfl
    rw [hmemK, hmemK, hmul]
    rcases hd.s56_mem_zpowers_z hcomm with h1 | h1
    ·
      have hb : (b : G) * d.pv 8 = d.pv 8 * (b : G) := by
        calc (b : G) * d.pv 8
            = ((b : G) * d.pv 8 * (b : G)⁻¹ * (d.pv 8)⁻¹) * (d.pv 8 * (b : G)) := by group
          _ = d.pv 8 * (b : G) := by rw [h1, one_mul]
      have hb' : ¬ ((b : G) * d.pv 7 * d.pv 8 = d.pv 8 * ((b : G) * d.pv 7)) := by
        intro h
        have h0 : (b : G) * d.pv 7 * d.pv 8 * ((b : G) * d.pv 7)⁻¹ * (d.pv 8)⁻¹ = 1 := by
          calc (b : G) * d.pv 7 * d.pv 8 * ((b : G) * d.pv 7)⁻¹ * (d.pv 8)⁻¹
              = (d.pv 8 * ((b : G) * d.pv 7)) * ((b : G) * d.pv 7)⁻¹ * (d.pv 8)⁻¹ := by rw [h]
            _ = 1 := by group
        rw [hprod, h1, one_mul] at h0
        exact hd.s56_z_ne_one h0
      exact Or.inr ⟨hb, hb'⟩
    ·
      have hb : ¬ ((b : G) * d.pv 8 = d.pv 8 * (b : G)) := by
        intro h
        have h0 : (b : G) * d.pv 8 * (b : G)⁻¹ * (d.pv 8)⁻¹ = 1 := by
          calc (b : G) * d.pv 8 * (b : G)⁻¹ * (d.pv 8)⁻¹
              = (d.pv 8 * (b : G)) * (b : G)⁻¹ * (d.pv 8)⁻¹ := by rw [h]
            _ = 1 := by group
        rw [h0] at h1
        exact hd.s56_z_ne_one h1.symm
      have hb' : (b : G) * d.pv 7 * d.pv 8 = d.pv 8 * ((b : G) * d.pv 7) := by
        have h0 : (b : G) * d.pv 7 * d.pv 8 * ((b : G) * d.pv 7)⁻¹ * (d.pv 8)⁻¹ = 1 := by
          rw [hprod, h1, hd.s56_z_sq]
        calc (b : G) * d.pv 7 * d.pv 8
            = ((b : G) * d.pv 7 * d.pv 8 * ((b : G) * d.pv 7)⁻¹ * (d.pv 8)⁻¹) *
                (d.pv 8 * ((b : G) * d.pv 7)) := by group
          _ = d.pv 8 * ((b : G) * d.pv 7) := by rw [h0, one_mul]
      exact Or.inl ⟨hb', hb⟩
  have h1 := Subgroup.card_mul_index ((d.s56P ⊓ d.s56Q2).subgroupOf (d.s56P ⊓ d.M))
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
  omega

theorem node10_card_Q2_inf_P (h49 : d.Thm49Statement) (hd : d.Hyp)
    (hQ : IsElemAbQuot d.s56P d.B 5)
    (h7 : ∀ s ∈ (fun f => d.t * f) '' (d.F : Set G), ∃ p ∈ d.s56P, p * d.t * p⁻¹ = s) :
    Nat.card (d.s56Q2 ⊓ d.s56P : Subgroup G) = 2 ^ 9 ∧ d.s56Q2.relIndex d.s56P = 4 := by
  have hP := node10_card_P hd hQ
  have hPM := node10_card_P_inf_M h49 hd hP (fun f hf => node10_eps_surj_P hd h7 hf)
  have hPQ := node10_card_PM_eq h49 hd
  have hcard : Nat.card (d.s56Q2 ⊓ d.s56P : Subgroup G) = 2 ^ 9 := by
    rw [inf_comm]
    omega
  refine ⟨hcard, ?_⟩
  have h := Subgroup.relIndex_mul_card (H := d.s56Q2) (K := d.s56P)
  rw [hcard, hP] at h
  omega

theorem node10_sylT_le_normalizer_P (h49 : d.Thm49Statement) (hd : d.Hyp) :
    sylT d ≤ normalizer (d.s56P : Set G) := by
  have hTN := p05_sylT_le_N hd
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => hd.s56_N_conj_P h49 (hTN hg) hx
  · intro hx
    have h := hd.s56_N_conj_P h49 (inv_mem (hTN hg)) hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at h

theorem node10_isPGroup_sup (h49 : d.Thm49Statement) (hd : d.Hyp) :
    IsPGroup 2 (sylT d ⊔ d.s56P : Subgroup G) := by
  have hPpg : IsPGroup 2 d.s56P := (Data.s56_P0_isPGroup d).to_le (Data.s56_P_le_P0 d)
  rw [sup_comm]
  exact hPpg.to_sup_of_normal_left' (p09_sylow hd).2.1 (node10_sylT_le_normalizer_P h49 hd)

theorem node10_sylow (h49 : d.Thm49Statement) (hd : d.Hyp)
    (h3 : (d.s56P : Set G) * ((d.N ⊓ centralizer ({d.t} : Set G) : Subgroup G) : Set G) =
      (d.N : Set G)) : fusionIsSylowIn 2 (sylT d ⊔ d.s56P) d.N := by
  have hTN := p05_sylT_le_N hd
  have hsyl := p09_sylow hd
  have hle : sylT d ⊔ d.s56P ≤ d.N := sup_le hTN (Data.s56_P_le_N d)
  refine ⟨hle, node10_isPGroup_sup h49 hd, fun R hRN hR hPT => ?_⟩
  refine le_antisymm (fun r hr => ?_) hPT
  have hrN : r ∈ d.N := hRN hr
  have hmem : r ∈ (d.s56P : Set G) *
      ((d.N ⊓ centralizer ({d.t} : Set G) : Subgroup G) : Set G) := by
    rw [h3]
    exact hrN
  obtain ⟨p, hp, c, hc, hpc⟩ := Set.mem_mul.1 hmem
  have hpR : p ∈ R := hPT (mem_sup_right hp)
  have hcR : c ∈ R := by
    have h := mul_mem (inv_mem hpR) hr
    rw [← hpc] at h
    have e : p⁻¹ * (p * c) = c := by group
    rwa [e] at h
  have hCR : R ⊓ centralizer ({d.t} : Set G) = sylT d :=
    hsyl.2.2 _ inf_le_right (hR.to_inf_left) (le_inf (le_sup_left.trans hPT) hsyl.1)
  have hcT : c ∈ sylT d := by
    rw [← hCR]
    exact mem_inf.2 ⟨hcR, (mem_inf.1 hc).2⟩
  rw [← hpc]
  exact mul_mem (mem_sup_right hp) (mem_sup_left hcT)

theorem node10_part_B (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz : d.S56Z0 z₀)
    (h09 : Node09 d z₀) :
    fusionIsSylowIn 2 (sylT d ⊔ d.s56P) d.N ∧
    (d.ρ.range = titsD.subgroupOf titsA → d.s56Q2 = d.s56V ⊔ zpowers d.t) ∧
    (∀ y, IsV5 d y → d.s56Q2 = d.s56V ⊔ zpowers d.t ⊔ zpowers y) ∧
    Nat.card (d.s56Q2 ⊓ d.s56P : Subgroup G) = 2 ^ 9 ∧
    Nat.card (d.s56V ⊓ d.N : Subgroup G) = 2 ^ 9 ∧ d.s56Q2.relIndex d.s56P = 4 := by
  obtain ⟨-, -, h3, -, hQ, -, h7, -⟩ := h09
  obtain ⟨hcard, hrel⟩ := node10_card_Q2_inf_P h49 hd hQ h7
  exact ⟨node10_sylow h49 hd h3, fun hR => node10_Q2_eq_D h49 hd hz hR,
    fun y hy => node10_Q2_eq_Â h49 hd hz hy, hcard, node10_card_V_inf_N h49 hd hz, hrel⟩

end Cnt

end CFSG.LocalAnalysis.EvenBN.Tits.N
