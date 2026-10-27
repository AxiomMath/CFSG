module

public import CFSG.GH74.GLS.SP.Local.SPLCt0

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section CtU

variable {G : Type} [Group G] [Finite G] (D : SPLNot1 G)

theorem commutator_mem_zpowers_of_dg_comm (hs : SPLSetup D.toSPLNot0) (a c : ↥D.K₁)
    (h : D.dg hs a * D.dg hs c = D.dg hs c * D.dg hs a) :
    (a : G) * c * (a : G)⁻¹ * (c : G)⁻¹ ∈ zpowers D.z := by
  have h1 : D.dg hs (a * c * a⁻¹ * c⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have := (dg_ker_iff D hs _).mp h1
  simpa using this

theorem exists_u (hs : SPLSetup D.toSPLNot0) : ∃ u : G, SPLCtU D u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc := hs.isCyclic_A0
  have htt := t_mul_t' D hs
  obtain ⟨T₁, hT₁le, hT₁p, -, hT₁card, hT₁eq⟩ := T₁_exists D hs
  have hn3 : 3 ≤ D.n := three_le_n D.toSPLNot0 hs.odd_q hs.q_ge
  have hntriv : Nontrivial ↥T₁ := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hT₁card]
    exact Nat.one_lt_two_pow (by omega)
  have hZ : Nontrivial ↥(center ↥T₁) := hT₁p.center_nontrivial
  have hZp : IsPGroup 2 ↥(center ↥T₁) := hT₁p.to_subgroup _
  have hZ2 : 2 ∣ Nat.card ↥(center ↥T₁) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hZp
    have hm0 : m ≠ 0 := by
      rintro rfl
      have : Nat.card ↥(center ↥T₁) = 1 := by rw [hm]; rfl
      exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' this
    rw [hm]; exact dvd_pow_self 2 hm0
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' 2 hZ2
  set u₁ : ↥T₁ := (x₀ : ↥T₁) with hu₁
  have hu₁c : ∀ y : ↥T₁, y * u₁ = u₁ * y := fun y => (mem_center_iff.mp x₀.2 y)
  have hu₁ord : orderOf u₁ = 2 := by rw [hu₁, Subgroup.orderOf_coe]; exact hx₀
  set u : G := (u₁ : G) with hu
  have huT₁ : u ∈ T₁ := u₁.2
  have hord : orderOf u = 2 := by rw [hu, Subgroup.orderOf_coe]; exact hu₁ord
  have huI : u ∈ D.Ict := (hT₁le huT₁).1
  have huS₁ : u ∈ D.S₁ := (hT₁le huT₁).2
  refine ⟨u, huI, hord, huS₁, ?_⟩
  have huT₁' := huT₁
  rw [hT₁eq] at huT₁'
  obtain ⟨c, hcQ, hcu⟩ := huT₁'
  have hcQ' : (c : G) ∈ (D.S : Subgroup G) ⊓ D.K₁ := hcQ
  have key : ∀ a : ↥D.K₁, (a : G) ∈ (D.S : Subgroup G) ⊓ D.K₁ →
      (a : G) * c * (a : G)⁻¹ * (c : G)⁻¹ ∈ zpowers D.z := by
    intro a ha
    refine commutator_mem_zpowers_of_dg_comm D hs a c ?_
    have hda : D.dg hs a ∈ T₁ := by
      rw [hT₁eq]; exact ⟨a, ha, rfl⟩
    have := hu₁c ⟨D.dg hs a, hda⟩
    have h2 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h2
    rw [hcu]
    exact h2
  have hcu' : u = (c : G) * (D.t * (c : G) * D.t⁻¹) := by rw [← hcu]; rfl
  intro x hx
  have hS₁ : D.S₁ = ((D.S : Subgroup G) ⊓ D.K₁) ⊔ ((D.S : Subgroup G) ⊓ D.K₂) :=
    Q_eq_sup hs.comps hs.gen_syl
  rw [hS₁] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute
    (H := (D.S : Subgroup G) ⊓ D.K₁) (K := (D.S : Subgroup G) ⊓ D.K₂)
    (fun a ha b hb => hs.comps.comm a ha.2 b hb.2) hx
  have haK₁ : a ∈ D.K₁ := ha.2
  have hbK₂ : b ∈ D.K₂ := hb.2
  have hb' : D.t * b * D.t⁻¹ ∈ D.K₁ := t_conj_K₂' D hs b hbK₂
  have hb'S : D.t * b * D.t⁻¹ ∈ (D.S : Subgroup G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hs.syl.t_mem hb.1) (Subgroup.inv_mem _ hs.syl.t_mem)
  have hz1 := key ⟨a, haK₁⟩ ha
  have hz2 := key ⟨D.t * b * D.t⁻¹, hb'⟩ ⟨hb'S, hb'⟩
  simp only at hz1 hz2
  obtain ⟨j₁, hj₁⟩ := mem_zpowers_iff.mp hz1
  obtain ⟨j₂, hj₂⟩ := mem_zpowers_iff.mp hz2
  have hc₁K₁ : (c : G) ∈ D.K₁ := c.2
  have hc₁K : (c : G) ∈ D.K := Subgroup.mem_sup_left hc₁K₁
  have hc₂K₂ : D.t * (c : G) * D.t⁻¹ ∈ D.K₂ := t_conj_K₁' D hs _ hc₁K₁
  have hbc₂ : b * (D.t * (c : G) * D.t⁻¹) * b⁻¹ ∈ D.K₂ :=
    D.K₂.mul_mem (D.K₂.mul_mem hbK₂ hc₂K₂) (D.K₂.inv_mem hbK₂)
  have hab : a * (b * (D.t * (c : G) * D.t⁻¹) * b⁻¹) = (b * (D.t * (c : G) * D.t⁻¹) * b⁻¹) * a :=
    hs.comps.comm a haK₁ _ hbc₂
  have hbc : b * (c : G) = (c : G) * b := (hs.comps.comm (c : G) hc₁K₁ b hbK₂).symm
  have hzK : ∀ (j : ℤ) (y : G), y ∈ D.K → D.z ^ j * y = y * D.z ^ j := fun j y hy =>
    z_central_in_K D hs (zpow_mem (mem_zpowers D.z) j) y hy
  have htz : ∀ j : ℤ, D.t * D.z ^ j * D.t⁻¹ = D.z ^ j := by
    intro j
    have h1 : D.t * D.z = D.z * D.t := (z_comm_t' D hs).symm
    have : D.t * D.z ^ j = D.z ^ j * D.t := (Commute.zpow_right (show Commute D.t D.z from h1) j).eq
    rw [this]; group
  have hA : a * (c : G) * a⁻¹ = D.z ^ j₁ * (c : G) := by
    rw [hj₁]; group
  have hbe : b = D.t * (D.t * b * D.t⁻¹) * D.t⁻¹ := by
    calc b = (D.t * D.t) * b * (D.t * D.t)⁻¹ := by rw [htt]; group
      _ = D.t * (D.t * b * D.t⁻¹) * D.t⁻¹ := by group
  have hB' : (D.t * b * D.t⁻¹) * (c : G) * (D.t * b * D.t⁻¹)⁻¹ = D.z ^ j₂ * (c : G) := by
    rw [hj₂]; group
  have hB : b * (D.t * (c : G) * D.t⁻¹) * b⁻¹ = D.z ^ j₂ * (D.t * (c : G) * D.t⁻¹) := by
    calc b * (D.t * (c : G) * D.t⁻¹) * b⁻¹
        = D.t * ((D.t * b * D.t⁻¹) * (c : G) * (D.t * b * D.t⁻¹)⁻¹) * D.t⁻¹ := by
          conv_lhs => rw [hbe]
          group
      _ = D.t * (D.z ^ j₂ * (c : G)) * D.t⁻¹ := by rw [hB']
      _ = (D.t * D.z ^ j₂ * D.t⁻¹) * (D.t * (c : G) * D.t⁻¹) := by group
      _ = D.z ^ j₂ * (D.t * (c : G) * D.t⁻¹) := by rw [htz]
  have hmain : a * b * u * (a * b)⁻¹ = D.z ^ (j₁ + j₂) * u := by
    rw [hcu']
    calc a * b * ((c : G) * (D.t * (c : G) * D.t⁻¹)) * (a * b)⁻¹
        = a * (b * (c : G)) * (D.t * (c : G) * D.t⁻¹) * b⁻¹ * a⁻¹ := by group
      _ = a * ((c : G) * b) * (D.t * (c : G) * D.t⁻¹) * b⁻¹ * a⁻¹ := by rw [hbc]
      _ = (a * (c : G) * a⁻¹) * (a * (b * (D.t * (c : G) * D.t⁻¹) * b⁻¹) * a⁻¹) := by group
      _ = (a * (c : G) * a⁻¹) * (b * (D.t * (c : G) * D.t⁻¹) * b⁻¹) := by rw [hab]; group
      _ = (D.z ^ j₁ * (c : G)) * (D.z ^ j₂ * (D.t * (c : G) * D.t⁻¹)) := by rw [hA, hB]
      _ = D.z ^ j₁ * (D.z ^ j₂ * (c : G)) * (D.t * (c : G) * D.t⁻¹) := by
          rw [hzK j₂ (c : G) hc₁K]; group
      _ = D.z ^ (j₁ + j₂) * ((c : G) * (D.t * (c : G) * D.t⁻¹)) := by
          rw [zpow_add]; group
  rw [hmain]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (zpow_mem (mem_zpowers D.z) _))
    (Subgroup.mem_sup_left (mem_zpowers u))

end CtU

end CFSG.GH74.GLS.SP.Local
