module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB2Cover
public import CFSG.Sporadic.Schreier.RuAutInner

public section

namespace CFSG.EvenSporadicStandard.RuStd

open Subgroup CFSG.Sporadic.RuSchreier

namespace B2

theorem card_centralizer_inf_eq {G : Type*} [Group G] (K : Subgroup G) (a b : K) :
    Nat.card ↥(centralizer ({a} : Set K) ⊓ centralizer ({b} : Set K)) =
      Nat.card ↥(K ⊓ centralizer {(a : G)} ⊓ centralizer {(b : G)}) := by
  have h : (centralizer ({a} : Set K) ⊓ centralizer ({b} : Set K)).map K.subtype =
      K ⊓ centralizer {(a : G)} ⊓ centralizer {(b : G)} := by
    ext y
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, coe_subtype]
    constructor
    · rintro ⟨x, ⟨hxa, hxb⟩, rfl⟩
      exact ⟨⟨x.2, congrArg Subtype.val hxa⟩, congrArg Subtype.val hxb⟩
    · rintro ⟨⟨hyK, hya⟩, hyb⟩
      exact ⟨⟨y, hyK⟩, ⟨Subtype.ext hya, Subtype.ext hyb⟩, rfl⟩
  rw [← h, Subgroup.card_map_of_injective K.subtype_injective]

theorem card_centralizer_eq {G : Type*} [Group G] (K : Subgroup G) (a : K) :
    Nat.card ↥(centralizer ({a} : Set K)) = Nat.card ↥(K ⊓ centralizer {(a : G)}) := by
  have h : (centralizer ({a} : Set K)).map K.subtype = K ⊓ centralizer {(a : G)} := by
    ext y
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, coe_subtype]
    constructor
    · rintro ⟨x, hxa, rfl⟩
      exact ⟨x.2, congrArg Subtype.val hxa⟩
    · rintro ⟨hyK, hya⟩
      exact ⟨⟨y, hyK⟩, Subtype.ext hya, rfl⟩
  rw [← h, Subgroup.card_map_of_injective K.subtype_injective]

theorem card_inf_centralizer_conj {G : Type*} [Group G] (K : Subgroup G) {g : G} (hg : g ∈ K)
    (a b : G) : Nat.card ↥(K ⊓ centralizer {a} ⊓ centralizer {b}) =
      Nat.card ↥(K ⊓ centralizer {g⁻¹ * a * g} ⊓ centralizer {g⁻¹ * b * g}) := by
  refine Nat.card_congr ((MulAut.conj g⁻¹).toEquiv.subtypeEquiv fun x => ?_)
  have key : ∀ u v : G, u * v = v * u ↔ (g⁻¹ * u * g) * (g⁻¹ * v * g) =
      (g⁻¹ * v * g) * (g⁻¹ * u * g) := by
    intro u v
    rw [show (g⁻¹ * u * g) * (g⁻¹ * v * g) = g⁻¹ * (u * v) * g by group,
      show (g⁻¹ * v * g) * (g⁻¹ * u * g) = g⁻¹ * (v * u) * g by group, mul_left_inj,
      mul_right_inj]
  have hK : x ∈ K ↔ g⁻¹ * x * g ∈ K := by
    refine ⟨fun hx => K.mul_mem (K.mul_mem (K.inv_mem hg) hx) hg, fun hx => ?_⟩
    have := K.mul_mem (K.mul_mem hg hx) (K.inv_mem hg)
    simpa [mul_assoc] using this
  simp only [mem_inf, mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
    MulAut.conj_apply, inv_inv]
  rw [hK, ← key x a, ← key x b]

theorem mem_ruZP_of_card
    {p : ruP} (hp : orderOf p = 2)
    (hc : Nat.card (centralizer ({p} : Set ruP)) = 245760) :
    (p : Equiv.Perm (Fin 4060)) ∈ ruZP := by
  have hp' : (p : Equiv.Perm (Fin 4060)) ∈ {t | t ∈ ruP ∧ orderOf t = 2} :=
    ⟨p.2, by rw [Subgroup.orderOf_coe]; exact hp⟩
  rw [ruInvolutions_eq] at hp'
  rcases hp' with h | h
  · exact h
  · exfalso
    have e1 := ncard_conjSet_mul_card ruP (p : Equiv.Perm (Fin 4060))
    have e2 := ncard_conjSet_mul_card ruP ruA0
    rw [ruCentralizer_a, card_ruL, card_ruP] at e2
    rw [conjSet_eq_of_mem h, card_ruP, ← card_centralizer_eq ruP p, hc] at e1
    have hN : 0 < (conjSet ruP ruA0).ncard := by
      rcases Nat.eq_zero_or_pos (conjSet ruP ruA0).ncard with h0 | h0
      · rw [h0] at e2
        omega
      · exact h0
    rw [← e2] at e1
    have := Nat.eq_of_mul_eq_mul_left hN e1
    omega

end B2

theorem ruP_no_256 :
    ∀ p q : ruP, orderOf p = 2 → orderOf q = 2 → p ≠ q → p * q = q * p →
      Nat.card (centralizer ({p} : Set ruP)) = 245760 →
      Nat.card (centralizer ({q} : Set ruP)) = 245760 →
      Nat.card ↥(centralizer ({p} : Set ruP) ⊓ centralizer ({q} : Set ruP)) ≠ 256 := by
  intro p q hp hq hpq hcomm hcp hcq
  obtain ⟨g, hg, hgp⟩ := B2.mem_ruZP_of_card hp hcp
  obtain ⟨h, hh, hhq⟩ := B2.mem_ruZP_of_card hq hcq
  have hcomm' : (p : Equiv.Perm (Fin 4060)) * q = q * p := congrArg Subtype.val hcomm
  have hp' : g⁻¹ * (p : Equiv.Perm (Fin 4060)) * g = ruZ := by rw [← hgp]; group
  set q' : Equiv.Perm (Fin 4060) := g⁻¹ * (q : Equiv.Perm (Fin 4060)) * g with hq'
  have hcard : Nat.card ↥(centralizer ({p} : Set ruP) ⊓ centralizer ({q} : Set ruP)) =
      Nat.card ↥(ruC ⊓ Subgroup.centralizer {q'}) := by
    rw [B2.card_centralizer_inf_eq ruP p q, B2.card_inf_centralizer_conj ruP hg, hp',
      ← ruC_eq_centralizer]
  rw [hcard]
  have hx : q' ∈ ruC := by
    rw [ruC_eq_centralizer]
    refine Subgroup.mem_inf.2 ⟨ruP.mul_mem (ruP.mul_mem (ruP.inv_mem hg) q.2) hg,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hp', hq']
    calc g⁻¹ * (q : Equiv.Perm (Fin 4060)) * g * (g⁻¹ * (p : Equiv.Perm (Fin 4060)) * g)
        = g⁻¹ * ((q : Equiv.Perm (Fin 4060)) * p) * g := by group
      _ = g⁻¹ * ((p : Equiv.Perm (Fin 4060)) * q) * g := by rw [hcomm']
      _ = g⁻¹ * (p : Equiv.Perm (Fin 4060)) * g * (g⁻¹ * (q : Equiv.Perm (Fin 4060)) * g) := by
        group
  have h2 : orderOf q' = 2 := by
    have : q' = (MulAut.conj g⁻¹) (q : Equiv.Perm (Fin 4060)) := by simp [hq']
    rw [this, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hq]
  have hfix : (fixSet q').ncard = 92 := by
    have : q' = (g⁻¹ * h) * ruZ * (g⁻¹ * h)⁻¹ := by
      rw [hq', ← hhq]
      group
    rw [this]
    exact conj_ruZ_ncard
  have hz : q' ≠ ruZ := by
    intro hqz
    refine hpq (Subtype.ext ?_)
    rw [← hp', hq'] at hqz
    exact (mul_left_cancel (mul_right_cancel hqz)).symm
  rcases B2.card_ruC_inf_centralizer_of_fixed hx h2 hfix hz with h | h | h | h <;> omega

end CFSG.EvenSporadicStandard.RuStd
