module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.B68Defs

public section

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp.B68

open Subgroup

variable {G : Type} [Group G] [Finite G] {N sz : Fin 4 → ℕ}

omit [Finite G] in
theorem Arith.class_of_commute (hA : Arith N sz) {x t : G} (hx : orderOf x = 17)
    (hxt : x * t = t * x) {k : Fin 4} (ht : Inv N k t) : k = 0 ∨ k = 3 := by
  have hmem : x ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hxt
  have hdvd := Subgroup.orderOf_dvd_natCard (centralizer ({t} : Set G)) hmem
  rw [hx, ht.2] at hdvd
  exact hA.dvd17 k hdvd

theorem del_commute (hA : Arith N sz) (hT4 : TableIV (G := G) N sz) {x : G} (hx : orderOf x = 17)
    {u v : G} (hu : u ∈ Del N x) (hv : v ∈ Del N x) (huv : u ≠ v) :
    u * v = v * u ∧ Inv N 3 (u * v) := by
  obtain ⟨hcov, hconj, hcard⟩ := hT4 u hu.1
  obtain ⟨k, hk⟩ := hcov v hv.1 huv.symm
  have hxuv : u * v * x = x * (u * v) := commute_mul_of_commute hu.2 hv.2
  fin_cases k
  · exfalso
    have hk' : Inv N 1 (u * v) := hk
    rcases hA.class_of_commute hx hxuv.symm hk' with h | h <;> exact absurd h (by decide)
  · have hk' : Inv N 3 (u * v) := hk
    exact ⟨comm_of_mul_self_eq_one hu.1.mul_self hv.1.mul_self hk'.mul_self, hk'⟩
  · exfalso
    have hO : ∀ h ∈ centralizer ({u} : Set G), h * v * h⁻¹ ∈ {s | Inv N 0 s ∧ Orb N 2 u s} := by
      intro h hh
      have hh' : h * u = u * h := mem_centralizer_singleton_iff.1 hh
      exact ⟨Inv.of_isConj hv.1 (isConj_iff.2 ⟨h, rfl⟩), Orb.conj hh' hk⟩
    have htr : ∀ s' ∈ {s | Inv N 0 s ∧ Orb N 2 u s},
        ∃ h ∈ centralizer ({u} : Set G), h * v * h⁻¹ = s' := fun s' hs' =>
      hconj 2 v s' hv.1 hs'.1 hk hs'.2
    have hmul := card_inf_centralizer_mul_ncard_of_orbit (centralizer ({u} : Set G)) v _ hO htr
    rw [hcard 2, hu.1.2] at hmul
    have hxmem : x ∈ (centralizer ({u} : Set G) ⊓ centralizer ({v} : Set G) : Subgroup G) :=
      ⟨mem_centralizer_singleton_iff.2 hu.2.symm, mem_centralizer_singleton_iff.2 hv.2.symm⟩
    have hdvd := Subgroup.orderOf_dvd_natCard _ hxmem
    rw [hx] at hdvd
    obtain ⟨c', hc'⟩ := hdvd
    rw [hc'] at hmul
    obtain ⟨m, hm⟩ := hA.dvd_sz2
    apply hA.nsq
    exact ⟨c' * m, by rw [← hmul, hm]; ring⟩
  · exfalso
    have hk' : orderOf (u * v) = 4 ∧ Inv N 1 ((u * v) ^ 2) := hk
    have hx2 : x * (u * v) ^ 2 = (u * v) ^ 2 * x := by
      generalize u * v = w at hxuv ⊢
      rw [pow_two, ← mul_assoc, ← hxuv, mul_assoc, ← hxuv, ← mul_assoc]
    rcases hA.class_of_commute hx hx2 hk'.2 with h | h <;> exact absurd h (by decide)

theorem del_three (hA : Arith N sz) (hT4 : TableIV (G := G) N sz) (hCap : Cap (G := G) N) {x : G}
    (hx : orderOf x = 17) {u v w : G} (hu : u ∈ Del N x) (hv : v ∈ Del N x) (hw : w ∈ Del N x) :
    u = v ∨ u = w ∨ v = w := by
  by_contra hcon
  push Not at hcon
  obtain ⟨huv, huw, hvw⟩ := hcon
  obtain ⟨hcuv, hC3⟩ := del_commute hA hT4 hx hu hv huv
  obtain ⟨hcuw, -⟩ := del_commute hA hT4 hx hu hw huw
  classical
  have hne1 : ∀ {k : Fin 4} {t : G}, Inv N k t → (1 : G) ≠ t := fun h => (Inv.ne_one h).symm
  have hu1 : (1 : G) ≠ u := hne1 hu.1
  have hv1 : (1 : G) ≠ v := hne1 hv.1
  have hw1 : (1 : G) ≠ w := hne1 hw.1
  have huv1 : (1 : G) ≠ u * v := hne1 hC3
  have hu_uv : u ≠ u * v := by
    intro h
    exact hv1 (mul_left_cancel (by rw [mul_one]; exact h : u * 1 = u * v))
  have hv_uv : v ≠ u * v := by
    intro h
    exact hu1 (mul_right_cancel (by rw [one_mul]; exact h : 1 * v = u * v))
  have hw_uv : w ≠ u * v := by
    intro h
    have hC3w : Inv N 3 w := by rw [h]; exact hC3
    exact absurd (Inv.unique hA.inj hw.1 hC3w) (by decide)
  have hA1 : (1 : G) ∉ ({u, v, w, u * v} : Finset G) := by simp [hu1, hv1, hw1, huv1]
  have hA2 : u ∉ ({v, w, u * v} : Finset G) := by simp [huv, huw, hu_uv]
  have hA3 : v ∉ ({w, u * v} : Finset G) := by simp [hvw, hv_uv]
  have hA4 : w ∉ ({u * v} : Finset G) := by simp [hw_uv]
  have h5 : ({1, u, v, w, u * v} : Finset G).card = 5 := by
    rw [Finset.card_insert_of_notMem hA1, Finset.card_insert_of_notMem hA2,
      Finset.card_insert_of_notMem hA3, Finset.card_insert_of_notMem hA4, Finset.card_singleton]
  let T : Subgroup G := centralizer ({u} : Set G) ⊓ centralizer ({x} : Set G)
  have hxT : x ∈ T :=
    ⟨mem_centralizer_singleton_iff.2 hu.2.symm, mem_centralizer_singleton_iff.2 rfl⟩
  have hmemT : ∀ g : G, g * u = u * g → g * x = x * g → g ∈ T := fun g h1 h2 =>
    ⟨mem_centralizer_singleton_iff.2 h1, mem_centralizer_singleton_iff.2 h2⟩
  have hS : (↑({1, u, v, w, u * v} : Finset G) : Set G) ⊆ T := by
    intro g hg
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact hmemT _ (by rw [one_mul, mul_one]) (by rw [one_mul, mul_one])
    · exact hmemT _ rfl hu.2
    · exact hmemT _ hcuv.symm hv.2
    · exact hmemT _ hcuw.symm hw.2
    · exact hmemT _ (by rw [mul_assoc, ← hcuv]) (commute_mul_of_commute hu.2 hv.2)
  have h4 := ncard_le_four_of_pow_four hxT (fun t ht => mem_centralizer_singleton_iff.1 ht.2) hx
    (hCap hu.1 hx hu.2) hS (fun g hg => by
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl
      · exact one_pow 4
      · exact hu.1.pow_four
      · exact hv.1.pow_four
      · exact hw.1.pow_four
      · exact hC3.pow_four)
  rw [Set.ncard_coe_finset, h5] at h4
  omega

theorem exists_partner (hA : Arith N sz) (hT4 : TableIV (G := G) N sz) {x : G} (hx : orderOf x = 17)
    {u : G} (hu : u ∈ Del N x) : ∃ v ∈ Del N x, v ≠ u := by
  obtain ⟨hcov, hconj, hcard⟩ := hT4 u hu.1
  have hne : {s : G | Inv N 0 s ∧ Orb N 1 u s}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hcard 1]
    exact hA.ne_sz1
  obtain ⟨e₀, he₀, he₀o⟩ := hne
  have he₀' : Inv N 3 (u * e₀) := he₀o
  have hcomm : u * e₀ = e₀ * u :=
    comm_of_mul_self_eq_one hu.1.mul_self he₀.mul_self he₀'.mul_self
  have hO : ∀ h ∈ centralizer ({u} : Set G), h * e₀ * h⁻¹ ∈ {s | Inv N 0 s ∧ Orb N 1 u s} := by
    intro h hh
    have hh' : h * u = u * h := mem_centralizer_singleton_iff.1 hh
    exact ⟨Inv.of_isConj he₀ (isConj_iff.2 ⟨h, rfl⟩), Orb.conj hh' he₀o⟩
  have htr : ∀ s' ∈ {s | Inv N 0 s ∧ Orb N 1 u s},
      ∃ h ∈ centralizer ({u} : Set G), h * e₀ * h⁻¹ = s' := fun s' hs' =>
    hconj 1 e₀ s' he₀ hs'.1 he₀o hs'.2
  have hmul := card_inf_centralizer_mul_ncard_of_orbit (centralizer ({u} : Set G)) e₀ _ hO htr
  rw [hcard 1, hu.1.2] at hmul
  have h17 : 17 ∣
      Nat.card (centralizer ({u} : Set G) ⊓ centralizer ({e₀} : Set G) : Subgroup G) := by
    have h := hA.dvd0
    rw [← hmul] at h
    exact Nat.Coprime.dvd_of_dvd_mul_right hA.cop_sz1 h
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(centralizer ({u} : Set G) ⊓ centralizer ({e₀} : Set G) : Subgroup G)) 17 h17
  let H : Subgroup G := centralizer ({u} : Set G)
  have hxH : x ∈ H := mem_centralizer_singleton_iff.2 hu.2.symm
  have he₀H : e₀ ∈ H := mem_centralizer_singleton_iff.2 hcomm.symm
  let x₁ : H := ⟨x, hxH⟩
  let y₁ : H := ⟨(y : G), y.2.1⟩
  let z₁ : H := ⟨e₀, he₀H⟩
  have hx₁ : orderOf x₁ = 17 := by rw [← hx]; exact Subgroup.orderOf_mk _ _
  have hy₁ : orderOf y₁ = 17 := by
    rw [← hy, ← Subgroup.orderOf_coe y]
    exact Subgroup.orderOf_mk _ _
  have hp2 : ¬ 17 ^ 2 ∣ Nat.card H := by
    show ¬ 17 ^ 2 ∣ Nat.card (centralizer ({u} : Set G))
    rw [hu.1.2]
    exact hA.nsq
  have hz : Commute y₁ z₁ := Subtype.ext (mem_centralizer_singleton_iff.1 y.2.2)
  obtain ⟨g, hg⟩ := exists_conj_commute_of_prime hp2 hx₁ hy₁ hz
  have hg' : x * ((g : G)⁻¹ * e₀ * (g : G)) = (g : G)⁻¹ * e₀ * (g : G) * x := by
    have := congrArg Subtype.val hg.eq
    simpa [x₁, z₁] using this
  have hgu : (g : G) * u = u * (g : G) := mem_centralizer_singleton_iff.1 g.2
  have hgu' : (g : G)⁻¹ * u = u * (g : G)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgu, mul_inv_cancel_right]
  have he : Inv N 0 ((g : G)⁻¹ * e₀ * (g : G)) :=
    Inv.of_isConj he₀ (isConj_iff.2 ⟨(g : G)⁻¹, by rw [inv_inv]⟩)
  have heo : Orb N 1 u ((g : G)⁻¹ * e₀ * (g : G)) := by
    have := Orb.conj hgu' he₀o
    rwa [inv_inv] at this
  refine ⟨(g : G)⁻¹ * e₀ * (g : G), ⟨he, hg'.symm⟩, ?_⟩
  intro hue
  have hne : u * ((g : G)⁻¹ * e₀ * (g : G)) ≠ 1 := Inv.ne_one (show Inv N 3 _ from heo)
  apply hne
  rw [hue]
  exact hu.1.mul_self

theorem exists_pair (hA : Arith N sz) (hT3 : TableIII (G := G) N) (hT4 : TableIV (G := G) N sz)
    (h2A : ∃ c : G, Inv N 0 c) {x d : G} (hx : orderOf x = 17) (hxd : x * d = d * x)
    (hd : Inv N 3 d) : ∃ c ∈ Del N x, ∃ e ∈ Del N x, c * e = d := by
  obtain ⟨c₀, hc₀⟩ := h2A
  obtain ⟨-, -, hcard₀⟩ := hT4 c₀ hc₀
  have hne : {s : G | Inv N 0 s ∧ Orb N 1 c₀ s}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hcard₀ 1]
    exact hA.ne_sz1
  obtain ⟨e₀, he₀, he₀o⟩ := hne
  have hd₀ : Inv N 3 (c₀ * e₀) := he₀o
  obtain ⟨g, hg⟩ := isConj_iff.1 (hT3.2 3 (c₀ * e₀) d hd₀ hd)
  have hc : Inv N 0 (g * c₀ * g⁻¹) := Inv.of_isConj hc₀ (isConj_iff.2 ⟨g, rfl⟩)
  have he : Inv N 0 (g * e₀ * g⁻¹) := Inv.of_isConj he₀ (isConj_iff.2 ⟨g, rfl⟩)
  have hce : g * c₀ * g⁻¹ * (g * e₀ * g⁻¹) = d := by rw [← hg]; group
  have heo : Orb N 1 (g * c₀ * g⁻¹) (g * e₀ * g⁻¹) := by
    show Inv N 3 _
    rw [hce]
    exact hd
  generalize g * c₀ * g⁻¹ = c at hc hce heo
  generalize g * e₀ * g⁻¹ = e at he hce heo
  obtain ⟨hcov, hconj, hcard⟩ := hT4 c hc
  have hO : ∀ h ∈ centralizer ({c} : Set G), h * e * h⁻¹ ∈ {s | Inv N 0 s ∧ Orb N 1 c s} := by
    intro h hh
    have hh' : h * c = c * h := mem_centralizer_singleton_iff.1 hh
    exact ⟨Inv.of_isConj he (isConj_iff.2 ⟨h, rfl⟩), Orb.conj hh' heo⟩
  have htr : ∀ s' ∈ {s | Inv N 0 s ∧ Orb N 1 c s},
      ∃ h ∈ centralizer ({c} : Set G), h * e * h⁻¹ = s' := fun s' hs' =>
    hconj 1 e s' he hs'.1 heo hs'.2
  have hmul := card_inf_centralizer_mul_ncard_of_orbit (centralizer ({c} : Set G)) e _ hO htr
  rw [hcard 1, hc.2] at hmul
  have hcomm : c * e = e * c := comm_of_mul_self_eq_one hc.mul_self he.mul_self (by
    have : Inv N 3 (c * e) := heo
    exact this.mul_self)
  have hRle : (centralizer ({c} : Set G) ⊓ centralizer ({e} : Set G) : Subgroup G) ≤
      centralizer ({d} : Set G) := by
    intro r hr
    have h1 : r * c = c * r := mem_centralizer_singleton_iff.1 hr.1
    have h2 : r * e = e * r := mem_centralizer_singleton_iff.1 hr.2
    rw [mem_centralizer_singleton_iff, ← hce]
    exact (commute_mul_of_commute h1.symm h2.symm).symm
  have hcardR : Nat.card (centralizer ({d} : Set G)) =
      2 * Nat.card (centralizer ({c} : Set G) ⊓ centralizer ({e} : Set G) : Subgroup G) := by
    rw [hd.2]
    have : N 3 * sz 1 = (2 * Nat.card
        (centralizer ({c} : Set G) ⊓ centralizer ({e} : Set G) : Subgroup G)) * sz 1 := by
      rw [hA.idx, mul_assoc, ← hmul]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hA.ne_sz1) this
  have hxd' : x ∈ centralizer ({d} : Set G) := mem_centralizer_singleton_iff.2 hxd
  have hxR := mem_of_odd_orderOf_of_card hRle hcardR hxd' (by rw [hx]; decide)
  exact ⟨c, ⟨hc, (mem_centralizer_singleton_iff.1 hxR.1).symm⟩, e,
    ⟨he, (mem_centralizer_singleton_iff.1 hxR.2).symm⟩, hce⟩

end CFSG.EvenSporadicStandard.HypOne.BabyHyp.B68
