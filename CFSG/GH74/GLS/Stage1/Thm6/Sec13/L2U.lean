module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L2S0

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem card_subgroupOf_inf [Finite G] (E P : Subgroup G) :
    Nat.card (P.subgroupOf E) = Nat.card ↥(P ⊓ E) := by
  rw [← Subgroup.inf_subgroupOf_right]
  exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv

namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {S : Subgroup G} (c : Ctx2S G x T V H f S)
include c

theorem normIn_Hs : NormIn (Hzero H f) (H ⊔ T) :=
  ⟨c.c2.c3.H0_le.trans le_sup_left, c.hPT⟩

theorem cent_P_eq_V [Finite G] {a : G} (haH : a ∈ H) (haP : a ∉ Hzero H f) :
    Hzero H f ⊓ centralizer ({a} : Set G) = V := by
  obtain ⟨q, hq, h | h⟩ := (c.c2.c3.mem_H_iff).1 haH
  · exact absurd (h ▸ hq) haP
  · have hxq : ∀ g ∈ Hzero H f, a * g * a⁻¹ = x * g * x⁻¹ := by
      intro g hg
      rw [h]
      have h1 : q * x * g * (q * x)⁻¹ = q * (x * g * x⁻¹) * q⁻¹ := by group
      rw [h1]
      have hxg := c.c2.c3.H0_norm_H x c.c2.c3.x_mem_H g hg
      have := c.c2.P_comm q hq _ hxg
      calc q * (x * g * x⁻¹) * q⁻¹ = (x * g * x⁻¹) * q * q⁻¹ := by rw [this]
        _ = x * g * x⁻¹ := by group
    rw [← c.c2.c3.C_H0_x]
    ext g
    constructor
    · rintro ⟨hgP, hga⟩
      refine ⟨hgP, ?_⟩
      show g ∈ centralizer ({x} : Set G)
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      have h1 := mem_centralizer_iff.1 hga a rfl
      have h2 : a * g * a⁻¹ = g := by
        calc a * g * a⁻¹ = (g * a) * a⁻¹ := by rw [← h1]
          _ = g := by group
      rw [hxq g hgP] at h2
      calc x * g = (x * g * x⁻¹) * x := by group
        _ = g * x := by rw [h2]
    · rintro ⟨hgP, hgx⟩
      refine ⟨hgP, ?_⟩
      show g ∈ centralizer ({a} : Set G)
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      have h1 := mem_centralizer_iff.1 hgx x rfl
      have h2 : x * g * x⁻¹ = g := by
        calc x * g * x⁻¹ = (g * x) * x⁻¹ := by rw [← h1]
          _ = g := by group
      have h3 : a * g * a⁻¹ = g := by rw [hxq g hgP, h2]
      calc a * g = (a * g * a⁻¹) * a := by group
        _ = g * a := by rw [h3]

end Ctx2S

namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {S : Subgroup G} (c : Ctx2S G x T V H f S)
include c

theorem cent_P_le_four [Finite G] {a : G} (haS : a ∈ H ⊔ T) (haH : a ∉ H) :
    Nat.card ↥(Hzero H f ⊓ centralizer ({a} : Set G)) ≤ 4 := by
  obtain ⟨p, hp, t, ht, rfl⟩ := c.Hstar_decomp a haS
  have htH : t ∉ H := by
    intro h
    apply haH
    exact H.mul_mem (c.c2.c3.H0_le hp) h
  have hP := c.c2.c3
  have htx : t * x = x * t := hP.T_comm_x ht
  have htN : ∀ g ∈ Hzero H f, t * g * t⁻¹ ∈ Hzero H f :=
    fun g hg => c.hPT t (Subgroup.mem_sup_right ht) g hg
  have hCeq : Hzero H f ⊓ centralizer ({p * t} : Set G) = Hzero H f ⊓ centralizer ({t} : Set G) := by
    ext g
    constructor
    · rintro ⟨hg, hga⟩
      refine ⟨hg, ?_⟩
      show g ∈ centralizer ({t} : Set G)
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      have h1 := mem_centralizer_iff.1 hga (p * t) rfl
      have hpg := c.c2.P_comm p hp g hg
      calc t * g = p⁻¹ * (p * t * g) := by group
        _ = p⁻¹ * (g * (p * t)) := by rw [h1]
        _ = p⁻¹ * (g * p) * t := by group
        _ = p⁻¹ * (p * g) * t := by rw [hpg]
        _ = g * t := by group
    · rintro ⟨hg, hgt⟩
      refine ⟨hg, ?_⟩
      show g ∈ centralizer ({p * t} : Set G)
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      have h1 := mem_centralizer_iff.1 hgt t rfl
      have hpg := c.c2.P_comm p hp g hg
      calc p * t * g = p * (t * g) := by group
        _ = p * (g * t) := by rw [h1]
        _ = (p * g) * t := by group
        _ = (g * p) * t := by rw [hpg]
        _ = g * (p * t) := by group
  rw [hCeq]
  set K := Hzero H f ⊓ centralizer ({t} : Set G) with hK
  have hKsq : ∀ k ∈ K, k * k = 1 := fun k hk => c.c2.P_sq k hk.1
  have hKc : ∀ k ∈ K, ∀ l ∈ K, k * l = l * k := fun k hk l hl => c.c2.P_comm k hk.1 l hl.1
  have hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    intro k hk
    refine ⟨hP.H0_norm_H x hP.x_mem_H k hk.1, ?_⟩
    show x * k * x⁻¹ ∈ centralizer ({t} : Set G)
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have h1 := mem_centralizer_iff.1 hk.2 t rfl
    calc t * (x * k * x⁻¹) = (t * x) * k * x⁻¹ := by group
      _ = x * (t * k) * x⁻¹ := by rw [htx]; group
      _ = x * (k * t) * x⁻¹ := by rw [h1]
      _ = (x * k * x⁻¹) * t := by
        calc x * (k * t) * x⁻¹ = x * k * (t * x⁻¹) := by group
          _ = x * k * (x⁻¹ * t) := by
            have : t * x⁻¹ = x⁻¹ * t := by
              calc t * x⁻¹ = x⁻¹ * (x * t) * x⁻¹ := by group
                _ = x⁻¹ * (t * x) * x⁻¹ := by rw [htx]
                _ = x⁻¹ * t := by group
            rw [this]
          _ = (x * k * x⁻¹) * t := by group
  have hcard := card_le_cent_sq hKsq hKc hP.x_sq hxK
  have hKV : K ⊓ centralizer ({x} : Set G) ≤ V ⊓ centralizer ({t} : Set G) := by
    rintro g ⟨⟨hgP, hgt⟩, hgx⟩
    refine ⟨?_, hgt⟩
    rw [← hP.C_H0_x]
    exact ⟨hgP, hgx⟩
  have hVlt : V ⊓ centralizer ({t} : Set G) < V := by
    refine lt_of_le_of_ne inf_le_left (fun h => htH ?_)
    have htV : t ∈ centralizer (V : Set G) := by
      rw [mem_centralizer_iff]
      intro v hv
      have : v ∈ V ⊓ centralizer ({t} : Set G) := by rw [h]; exact hv
      exact (mem_centralizer_iff.1 this.2 t rfl).symm
    have : t ∈ (H ⊔ T) ⊓ centralizer (V : Set G) := ⟨Subgroup.mem_sup_right ht, htV⟩
    rw [hP.Hstar_inf_C] at this
    exact this
  have hV2 : Nat.card ↥(V ⊓ centralizer ({t} : Set G)) ≤ 2 := by
    have h1 := Subgroup.card_lt_of_lt hVlt
    rw [hP.out.V_four.2] at h1
    have hd : Nat.card ↥(V ⊓ centralizer ({t} : Set G)) ∣ 4 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : V ⊓ centralizer ({t} : Set G) ≤ V)
      rwa [hP.out.V_four.2] at this
    have hne3 : Nat.card ↥(V ⊓ centralizer ({t} : Set G)) ≠ 3 := by
      intro h; rw [h] at hd; norm_num at hd
    omega
  have h2 : Nat.card ↥(K ⊓ centralizer ({x} : Set G)) ≤ 2 :=
    le_trans (Subgroup.card_le_of_le hKV) hV2
  calc Nat.card K ≤ Nat.card ↥(K ⊓ centralizer ({x} : Set G)) ^ 2 := hcard
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_left h2 2
    _ = 4 := by norm_num

end Ctx2S


namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {S : Subgroup G} (c : Ctx2S G x T V H f S)
include c

theorem uniq_E [Finite G] {E : Subgroup G} (hE : E ≤ H ⊔ T) (hEel : IsElemAb2 E)
    (hEc : Nat.card E = 16) : E = Hzero H f := by
  by_contra hne
  have hEP : ¬ E ≤ Hzero H f := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge h (by rw [hEc, c.c2.P_card]))
  obtain ⟨a₁, ha₁E, ha₁P⟩ := IsConcreteLE.not_le_iff_exists.1 hEP
  have hEc' : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => (hEel a ha).2 b hb
  have hP := c.c2.c3
  have hB4 : Nat.card ↥(E ⊓ Hzero H f) ≤ 4 := by
    have hle : E ⊓ Hzero H f ≤ Hzero H f ⊓ centralizer ({a₁} : Set G) := by
      rintro g ⟨hgE, hgP⟩
      refine ⟨hgP, ?_⟩
      show g ∈ centralizer ({a₁} : Set G)
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact hEc' a₁ ha₁E g hgE
    have hcase : Nat.card ↥(Hzero H f ⊓ centralizer ({a₁} : Set G)) ≤ 4 := by
      by_cases ha₁H : a₁ ∈ H
      · rw [c.cent_P_eq_V ha₁H ha₁P]; exact le_of_eq hP.out.V_four.2
      · exact c.cent_P_le_four (hE ha₁E) ha₁H
    exact le_trans (Subgroup.card_le_of_le hle) hcase
  have hn := c.normIn_Hs
  have := hn.normal
  have hRcard : Nat.card (↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T)) * 16 = Nat.card ↥(H ⊔ T) := by
    have := card_QR (M := H ⊔ T) (N := Hzero H f) hn.le
    rw [c.c2.P_card] at this
    exact this
  have hR4 : Nat.card (↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T)) ≤ 4 := by
    have h1 := c.card_Hs_le
    rcases c.T_card_cases with h | h <;> omega
  have hker : (phiE (N := Hzero H f) E hE).ker = (Hzero H f).subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact qm_eq_one
  have hφ := Subgroup.card_ker_mul_card_range (phiE (N := Hzero H f) E hE)
  rw [hker, card_subgroupOf_inf, inf_comm, hEc] at hφ
  have hrange_le : Nat.card (phiE (N := Hzero H f) E hE).range ≤
      Nat.card (↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T)) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have hB4' : Nat.card ↥(E ⊓ Hzero H f) = 4 ∧ Nat.card (phiE (N := Hzero H f) E hE).range = 4 ∧
      Nat.card (↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T)) = 4 := by
    have hpos1 : 0 < Nat.card ↥(E ⊓ Hzero H f) := Nat.card_pos
    have hpos2 : 0 < Nat.card (phiE (N := Hzero H f) E hE).range := Nat.card_pos
    have h1 : Nat.card ↥(E ⊓ Hzero H f) * Nat.card (phiE (N := Hzero H f) E hE).range ≤ 4 * 4 := by
      exact Nat.mul_le_mul hB4 (hrange_le.trans hR4)
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  obtain ⟨hB4e, hrng4, hR4e⟩ := hB4'
  have hrtop : (phiE (N := Hzero H f) E hE).range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hrng4, hR4e]
  have hxs : x ∈ H ⊔ T := Subgroup.mem_sup_left hP.x_mem_H
  have hmem : qm (H ⊔ T) (Hzero H f) ⟨x, hxs⟩ ∈ (phiE (N := Hzero H f) E hE).range := by
    rw [hrtop]; exact Subgroup.mem_top _
  obtain ⟨e, heE, heM, he⟩ := (mem_range_phiE hE).1 hmem
  have h1 : e⁻¹ * x ∈ Hzero H f := qm_eq_iff.1 he
  have heH : e ∈ H := by
    have : e = x * (e⁻¹ * x)⁻¹ := by group
    rw [this]
    exact H.mul_mem hP.x_mem_H (H.inv_mem (hP.H0_le h1))
  have heP : e ∉ Hzero H f := by
    intro h
    apply hP.x_notin_H0
    have : x = e * (e⁻¹ * x) := by group
    rw [this]
    exact (Hzero H f).mul_mem h h1
  have hEV : E ⊓ Hzero H f ≤ V := by
    rintro g ⟨hgE, hgP⟩
    rw [← c.cent_P_eq_V heH heP]
    refine ⟨hgP, ?_⟩
    show g ∈ centralizer ({e} : Set G)
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact hEc' e heE g hgE
  have hEVeq : E ⊓ Hzero H f = V :=
    Subgroup.eq_of_le_of_card_ge hEV (by rw [hB4e, hP.out.V_four.2])
  have hVE : V ≤ E := by rw [← hEVeq]; exact inf_le_left
  have hEH : ∃ a₂ ∈ E, a₂ ∉ H := by
    by_contra hcon
    push Not at hcon
    have hsub : ((phiE (N := Hzero H f) E hE).range : Set (↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T))) ⊆
        {1, qm (H ⊔ T) (Hzero H f) ⟨x, hxs⟩} := by
      intro r hr
      obtain ⟨e', he'E, he'M, rfl⟩ := (mem_range_phiE hE).1 hr
      obtain ⟨q, hq, h | h⟩ := (hP.mem_H_iff).1 (hcon e' he'E)
      · left
        show qm (H ⊔ T) (Hzero H f) ⟨e', he'M⟩ = 1
        apply qm_eq_one.2
        show e' ∈ Hzero H f
        rw [h]; exact hq
      · right
        show qm (H ⊔ T) (Hzero H f) ⟨e', he'M⟩ = qm (H ⊔ T) (Hzero H f) ⟨x, hxs⟩
        apply qm_eq_iff.2
        have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hP.x_sq
        have : e'⁻¹ * x = x * q⁻¹ * x⁻¹ := by
          rw [h]
          calc (q * x)⁻¹ * x = x⁻¹ * q⁻¹ * x := by group
            _ = x * q⁻¹ * x⁻¹ := by rw [hxi]
        show e'⁻¹ * x ∈ Hzero H f
        rw [this]
        exact hP.H0_norm_H x hP.x_mem_H q⁻¹ ((Hzero H f).inv_mem hq)
    have h2 : Nat.card (phiE (N := Hzero H f) E hE).range ≤ 2 := by
      have a1 : Nat.card (phiE (N := Hzero H f) E hE).range =
          ((phiE (N := Hzero H f) E hE).range : Set (↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T))).ncard :=
        (Nat.card_coe_set_eq _).symm
      have a2 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have a3 : ({1, qm (H ⊔ T) (Hzero H f) ⟨x, hxs⟩} :
          Set (↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T))).ncard ≤ 2 := by
        refine le_trans (Set.ncard_insert_le _ _) ?_
        rw [Set.ncard_singleton]
      omega
    omega
  obtain ⟨a₂, ha₂E, ha₂H⟩ := hEH
  apply ha₂H
  have hC : a₂ ∈ centralizer (V : Set G) := by
    rw [mem_centralizer_iff]
    intro v hv
    exact (hEc' a₂ ha₂E v (hVE hv)).symm
  have : a₂ ∈ (H ⊔ T) ⊓ centralizer (V : Set G) := ⟨hE ha₂E, hC⟩
  rw [hP.Hstar_inf_C] at this
  exact this

end Ctx2S

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
