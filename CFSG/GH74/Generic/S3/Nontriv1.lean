module

public import CFSG.GH74.Generic.S1.SymTransport
public import CFSG.GH74.Generic.JMaxShapes
public import CFSG.GH74.Generic.S3.Defs
public import CFSG.GH74.Generic.S3.LeavesR
public import CFSG.GH74.Generic.S45.PumpC1
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.Generic.S1 (barConj barConj_xbar centralizer_map_mulEquiv)
open scoped commutatorElement

section ZStar

variable {G : Type} [Group G]

theorem exists_commuting_conj_ne [Finite G] (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    {x : G} (hx : orderOf x = 2) :
    ∃ g : G, g * x * g⁻¹ ≠ x ∧ (g * x * g⁻¹) * x = x * (g * x * g⁻¹) := by
  by_contra! hiso
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G x hx1 hxx fun g hg => by
    by_contra hne
    exact hiso g hne hg
  rcases hNn.eq_bot_or_eq_top with hbot | htop
  · have hcen : x ∈ center G := by
      rw [mem_center_iff]
      intro g
      have h := hN g
      rw [hbot, mem_bot, mul_inv_eq_one] at h
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [h]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hc | hc
    · rw [hc, mem_bot] at hcen
      exact hx1 hcen
    · obtain ⟨a, b, hab⟩ := hn
      exact hab ((mem_center_iff.mp (hc ▸ mem_top a : a ∈ center G)) b).symm
  · rw [htop, Subgroup.card_top] at hNodd
    have h2 : 2 ∣ Nat.card G := hx ▸ orderOf_dvd_natCard x
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2)

theorem exists_involution_mem_centralizer [Finite G] {M : Subgroup G} {u : G} (hu2 : u * u = 1)
    (hnorm : ∀ m ∈ M, u * m * u⁻¹ ∈ M) (heven : 2 ∣ Nat.card M) :
    ∃ t ∈ M, t * t = 1 ∧ t ≠ 1 ∧ t * u = u * t := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hconj : ∀ m : G, u * (u * m * u⁻¹) * u⁻¹ = m := fun m => by
    rw [hu]
    calc u * (u * m * u) * u = (u * u) * m * (u * u) := by group
      _ = m := by rw [hu2]; group
  let σ : Equiv.Perm M :=
    { toFun := fun m => ⟨u * m * u⁻¹, hnorm m m.2⟩
      invFun := fun m => ⟨u * m * u⁻¹, hnorm m m.2⟩
      left_inv := fun m => Subtype.ext (hconj m)
      right_inv := fun m => Subtype.ext (hconj m) }
  have hσ : σ ^ 2 = 1 := by
    ext m
    exact hconj m
  have h2 : 2 ∣ (σ.support).card := Equiv.Perm.two_dvd_card_support hσ
  have hcard : Fintype.card M = (σ.support).card + (σ.supportᶜ).card :=
    (Finset.card_add_card_compl σ.support).symm
  have hMcard : Fintype.card M = Nat.card M := Nat.card_eq_fintype_card.symm
  let C : Subgroup G := M ⊓ centralizer ({u} : Set G)
  have hC : Nat.card C = (σ.supportᶜ).card := by
    have e : C ≃ ↥(σ.supportᶜ : Finset M) :=
      { toFun := fun c => ⟨⟨c, c.2.1⟩, by
          simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
          apply Subtype.ext
          have h1 : (c : G) * u = u * c := Subgroup.mem_centralizer_singleton_iff.1 c.2.2
          show u * (c : G) * u⁻¹ = c
          rw [← h1]; group⟩
        invFun := fun m => ⟨(m : M), (m : M).2, by
          have hm := m.2
          simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hm
          have h1 : u * ((m : M) : G) * u⁻¹ = ((m : M) : G) := congrArg Subtype.val hm
          show ((m : M) : G) ∈ centralizer ({u} : Set G)
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc ((m : M) : G) * u = (u * ((m : M) : G) * u⁻¹) * u := by rw [h1]
            _ = u * ((m : M) : G) := by group⟩
        left_inv := fun c => rfl
        right_inv := fun m => rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  have hdvdC : 2 ∣ Nat.card C := by
    rw [hC]
    have h3 : 2 ∣ (σ.support).card + (σ.supportᶜ).card := by
      rw [← hcard, hMcard]; exact heven
    exact (Nat.dvd_add_right h2).1 h3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hdvdC
  have hcG : orderOf (c : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hc
  refine ⟨c, c.2.1, ?_, ?_, ?_⟩
  · have := pow_orderOf_eq_one (c : G)
    rwa [hcG, pow_two] at this
  · intro h1
    rw [h1, orderOf_one] at hcG
    omega
  · exact Subgroup.mem_centralizer_singleton_iff.1 c.2.2

end ZStar

section Conj

variable {G : Type} [Group G]

theorem OnlyInvX.conj {x : G} {K : Subgroup (CentralizerBar x)} (h : OnlyInvX x K) (g : G) :
    OnlyInvX (g * x * g⁻¹) (K.map (barConj x g).toMonoidHom) := by
  intro u hu hu2
  have hu' : u ∈ (centralizer (K : Set (CentralizerBar x))).map (barConj x g).toMonoidHom := by
    rw [← centralizer_map_mulEquiv]; exact hu
  obtain ⟨u₀, hu₀, rfl⟩ := hu'
  have hord : orderOf u₀ = 2 := (MulEquiv.orderOf_eq (barConj x g) u₀).symm.trans hu2
  have := h u₀ hu₀ hord
  rw [this]
  exact barConj_xbar x g

theorem center_map_barConj_eq_bot {x : G} {K : Subgroup (CentralizerBar x)} (h : center ↥K = ⊥)
    (g : G) : center ↥(K.map (barConj x g).toMonoidHom) = ⊥ := by
  have e := K.equivMapOfInjective (barConj x g).toMonoidHom (barConj x g).injective
  have h1 : (center ↥K).map e.toMonoidHom = center ↥(K.map (barConj x g).toMonoidHom) :=
    Subgroup.map_center_eq e
  rw [← h1, h, Subgroup.map_bot]

end Conj

section LemmaU

variable {G : Type} [Group G] [Finite G]

theorem false_of_conj_component {x w g b : G} {K : Subgroup (CentralizerBar x)}
    (hset : S3Setup G x K) (honly : OnlyInvX x K) (hg : g * x * g⁻¹ = w)
    (Λ : Subgroup (CentralizerBar w)) (hΛ : IsComponent Λ) (hbC : b ∈ centralizer ({w} : Set G))
    (hb2 : b * b = 1) (hb1 : b ≠ 1) (hbw : b ≠ w) (hmem : proj w ⟨b, hbC⟩ ∈ Λ)
    (hcent : ∀ l ∈ Λ, l * proj w ⟨b, hbC⟩ = proj w ⟨b, hbC⟩ * l) : False := by
  subst hg
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hset.inv, pow_two] at this
  have hww : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hxx]; group
  have hwo : orderOf (g * x * g⁻¹) = 2 := by
    rw [← hset.inv]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  set K' : Subgroup (CentralizerBar (g * x * g⁻¹)) := K.map (barConj x g).toMonoidHom with hK'
  have hK'c : IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv (barConj x g) hset.comp
  have honly' : OnlyInvX (g * x * g⁻¹) K' := honly.conj g
  obtain ⟨⟨p, f, -, -, -, hmodel⟩, -⟩ := hset.shape
  have hKcen : center ↥K = ⊥ := center_eq_bot_of_quasisimple_lieModel_L3 hset.comp.1 hmodel
  have hK'cen : center ↥K' = ⊥ := center_map_barConj_eq_bot hKcen g
  have hbar1 : proj (g * x * g⁻¹) ⟨b, hbC⟩ ≠ 1 := fun h1 =>
    hb1 (S45.eq_one_of_proj_eq_one_of_sq hbC h1 hb2)
  have hbar2 : proj (g * x * g⁻¹) ⟨b, hbC⟩ * proj (g * x * g⁻¹) ⟨b, hbC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨b, hbC⟩ : ↥(centralizer ({g * x * g⁻¹} : Set G))) * ⟨b, hbC⟩ = 1 := Subtype.ext hb2
    rw [this, map_one]
  have hord : orderOf (proj (g * x * g⁻¹) ⟨b, hbC⟩) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hbar2) hbar1
  rcases CFSG.LocalCores.distinct_components_commute hΛ hK'c with hEq | hcomm
  ·
    rw [hEq] at hmem hcent
    have hz : (⟨proj (g * x * g⁻¹) ⟨b, hbC⟩, hmem⟩ : ↥K') ∈ center ↥K' :=
      Subgroup.mem_center_iff.2 fun l => Subtype.ext (hcent l l.2)
    rw [hK'cen, Subgroup.mem_bot] at hz
    exact hbar1 (congrArg Subtype.val hz)
  ·
    have hcK' : proj (g * x * g⁻¹) ⟨b, hbC⟩ ∈ centralizer (K' : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 : ⁅proj (g * x * g⁻¹) ⟨b, hbC⟩, k⁆ = 1 := by
        have : ⁅proj (g * x * g⁻¹) ⟨b, hbC⟩, k⁆ ∈ ⁅Λ, K'⁆ :=
          Subgroup.commutator_mem_commutator hmem hk
        rw [hcomm] at this
        exact Subgroup.mem_bot.1 this
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
    have hxb : proj (g * x * g⁻¹) ⟨b, hbC⟩ = xbar (g * x * g⁻¹) := honly' _ hcK' hord
    have hwC : g * x * g⁻¹ ∈ centralizer ({g * x * g⁻¹} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 rfl
    have hbw' : b * (g * x * g⁻¹) ∈ centralizer ({g * x * g⁻¹} : Set G) :=
      (centralizer ({g * x * g⁻¹} : Set G)).mul_mem hbC hwC
    have hprod : proj (g * x * g⁻¹) ⟨b * (g * x * g⁻¹), hbw'⟩ = 1 := by
      have : (⟨b * (g * x * g⁻¹), hbw'⟩ : ↥(centralizer ({g * x * g⁻¹} : Set G))) =
          ⟨b, hbC⟩ * ⟨g * x * g⁻¹, hwC⟩ := rfl
      rw [this, map_mul, hxb]
      exact xbar_mul_self hwo
    have hcomm' : b * (g * x * g⁻¹) = (g * x * g⁻¹) * b := Subgroup.mem_centralizer_singleton_iff.1 hbC
    have hsq : b * (g * x * g⁻¹) * (b * (g * x * g⁻¹)) = 1 := by
      calc b * (g * x * g⁻¹) * (b * (g * x * g⁻¹)) = b * ((g * x * g⁻¹) * b) * (g * x * g⁻¹) := by group
        _ = b * (b * (g * x * g⁻¹)) * (g * x * g⁻¹) := by rw [← hcomm']
        _ = (b * b) * ((g * x * g⁻¹) * (g * x * g⁻¹)) := by group
        _ = 1 := by rw [hb2, hww, mul_one]
    have h1 : b * (g * x * g⁻¹) = 1 := S45.eq_one_of_proj_eq_one_of_sq hbw' hprod hsq
    apply hbw
    calc b = b * ((g * x * g⁻¹) * (g * x * g⁻¹)) := by rw [hww, mul_one]
      _ = (b * (g * x * g⁻¹)) * (g * x * g⁻¹) := (mul_assoc _ _ _).symm
      _ = g * x * g⁻¹ := by rw [h1, one_mul]

end LemmaU

end CFSG.GH74.Generic.S3
