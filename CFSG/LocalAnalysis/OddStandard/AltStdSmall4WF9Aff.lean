module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.AltStdSmall4.WF9

open Subgroup

variable {G : Type} [Group G]

theorem two_mul_card_le_of_mem [Finite G] {H K : Subgroup G} (hHK : H ≤ K) {x : G} (hxK : x ∈ K)
    (hxH : x ∉ H) : 2 * Nat.card H ≤ Nat.card K := by
  have h1 := relIndex_mul_card (H := H) (K := K)
  rw [inf_of_le_left hHK] at h1
  have h2 : H.relIndex K ≠ 1 := fun h => hxH (relIndex_eq_one.1 h hxK)
  have h3 : H.relIndex K ≠ 0 := Subgroup.index_ne_zero_of_finite
  calc 2 * Nat.card H ≤ H.relIndex K * Nat.card H := Nat.mul_le_mul_right _ (by omega)
    _ = Nat.card K := h1

theorem mem_sup_iff_of_le_normalizer {N H : Subgroup G} (hle : H ≤ normalizer (N : Set G))
    {x : G} : x ∈ N ⊔ H ↔ ∃ n ∈ N, ∃ h ∈ H, n * h = x := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left N H hle, Set.mem_mul]
  simp only [SetLike.mem_coe]

theorem eq_of_mul_eq_of_inf_eq_bot {N H : Subgroup G} (hNH : N ⊓ H = ⊥) {n n' h h' : G}
    (hn : n ∈ N) (hn' : n' ∈ N) (hh : h ∈ H) (hh' : h' ∈ H) (heq : n * h = n' * h') :
    n = n' ∧ h = h' := by
  have hmem : n'⁻¹ * n ∈ N ⊓ H := by
    refine mem_inf.2 ⟨N.mul_mem (N.inv_mem hn') hn, ?_⟩
    have : n'⁻¹ * n = h' * h⁻¹ := by
      calc n'⁻¹ * n = n'⁻¹ * (n * h) * h⁻¹ := by group
        _ = h' * h⁻¹ := by rw [heq]; group
    rw [this]
    exact H.mul_mem hh' (H.inv_mem hh)
  rw [hNH, mem_bot, inv_mul_eq_one] at hmem
  subst hmem
  exact ⟨rfl, mul_left_cancel heq⟩

theorem eq_one_or_eq_of_mem_zpowers_of_mul_self {d x : G} (hdd : d * d = 1)
    (hx : x ∈ zpowers d) : x = 1 ∨ x = d := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  have h2 : d ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hdd
  rw [zpow_eq_zpow_emod k h2]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk <;> rw [hk]
  · exact Or.inl (zpow_zero d)
  · exact Or.inr (zpow_one d)

private theorem mul_eq_mul_swap {x u v y : G} (huv : u * v = v * u) (hv : v * v = 1)
    (hu : u * u = 1) (h : x * v = y * u) : x * u = y * v :=
  calc x * u = x * u * (v * v) := by rw [hv, mul_one]
    _ = x * (u * v) * v := by group
    _ = x * (v * u) * v := by rw [huv]
    _ = x * v * (u * v) := by group
    _ = y * u * (u * v) := by rw [h]
    _ = y * (u * u) * v := by group
    _ = y * v := by rw [hu, mul_one]

structure AffData (E D : Subgroup G) : Prop where
  sq : ∀ e ∈ E, e * e = 1
  cardE : Nat.card E = 8
  cardD : Nat.card D = 8
  norm : D ≤ normalizer (E : Set G)
  inf : E ⊓ D = ⊥
  faith : ∀ d ∈ D, (∀ e ∈ E, d * e = e * d) → d = 1

namespace AffData

variable {E D : Subgroup G} (hA : AffData E D)
include hA

theorem inv_eq {e : G} (he : e ∈ E) : e⁻¹ = e :=
  inv_eq_of_mul_eq_one_right (hA.sq e he)

theorem comm {e f : G} (he : e ∈ E) (hf : f ∈ E) : e * f = f * e := by
  have h1 := inv_eq_of_mul_eq_one_right (hA.sq _ (mul_mem he hf))
  rw [mul_inv_rev, hA.inv_eq he, hA.inv_eq hf] at h1
  exact h1.symm

theorem conj_mem {d e : G} (hd : d ∈ D) (he : e ∈ E) : d * e * d⁻¹ ∈ E :=
  (mem_normalizer_iff.1 (hA.norm hd) e).1 he

theorem not_mem_of_ne_one {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) : d ∉ E := fun hdE => by
  have h : d ∈ E ⊓ D := ⟨hdE, hd⟩
  rw [hA.inf, mem_bot] at h
  exact hd1 h

theorem mem_sup_iff {x : G} : x ∈ E ⊔ D ↔ ∃ e ∈ E, ∃ d ∈ D, e * d = x :=
  mem_sup_iff_of_le_normalizer hA.norm

theorem eq_of_mul_eq {e e' d d' : G} (he : e ∈ E) (he' : e' ∈ E) (hd : d ∈ D) (hd' : d' ∈ D)
    (heq : e * d = e' * d') : e = e' ∧ d = d' :=
  eq_of_mul_eq_of_inf_eq_bot hA.inf he he' hd hd' heq

theorem card_sup_ge [Finite G] : 64 ≤ Nat.card (E ⊔ D : Subgroup G) := by
  let f : E × D → (E ⊔ D : Subgroup G) := fun p =>
    ⟨(p.1 : G) * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨e, d⟩ ⟨e', d'⟩ h
    obtain ⟨h1, h2⟩ := hA.eq_of_mul_eq e.2 e'.2 d.2 d'.2 (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, hA.cardE, hA.cardD] at h

theorem sq_of_mul {e d : G} (he : e ∈ E) (hd : d ∈ D) (h2 : e * d * (e * d) = 1) :
    d * d = 1 ∧ d * e = e * d := by
  have hu := hA.conj_mem hd he
  have heq : e * (d * e * d⁻¹) * (d * d) = 1 * 1 := by
    rw [one_mul, ← h2]
    group
  obtain ⟨h1, h3⟩ := hA.eq_of_mul_eq (mul_mem he hu) (one_mem _) (mul_mem hd hd) (one_mem _) heq
  refine ⟨h3, ?_⟩
  have h4 : d * e * d⁻¹ = e := (eq_inv_of_mul_eq_one_right h1).trans (hA.inv_eq he)
  calc d * e = d * e * d⁻¹ * d := by group
    _ = e * d := by rw [h4]

theorem exists_comm [Finite G] {e : G} (he : e ∈ E) : ∃ c ∈ D, c ≠ 1 ∧ c * e = e * c := by
  by_cases he1 : e = 1
  · rcases D.bot_or_exists_ne_one with hD | ⟨c, hc, hc1⟩
    · have h := hA.cardD
      rw [hD, card_bot] at h
      omega
    · exact ⟨c, hc, hc1, by rw [he1, mul_one, one_mul]⟩
  · by_contra hne
    push Not at hne
    let φ : D → E := fun c => ⟨(c : G) * e * (c : G)⁻¹, hA.conj_mem c.2 he⟩
    have hφ : Function.Injective φ := by
      intro c c' hcc
      have h1 : (c : G) * e * (c : G)⁻¹ = c' * e * (c' : G)⁻¹ := congrArg Subtype.val hcc
      by_contra hne'
      have hne'' : (c' : G)⁻¹ * c ≠ 1 := fun h0 =>
        hne' (Subtype.ext (inv_mul_eq_one.1 h0).symm)
      apply hne _ (mul_mem (inv_mem c'.2) c.2) hne''
      calc (c' : G)⁻¹ * c * e = (c' : G)⁻¹ * (c * e * (c : G)⁻¹) * c := by group
        _ = (c' : G)⁻¹ * (c' * e * (c' : G)⁻¹) * c := by rw [h1]
        _ = e * ((c' : G)⁻¹ * c) := by group
    have hbij := hφ.bijective_of_nat_card_le (hA.cardE.trans hA.cardD.symm).le
    obtain ⟨c, hc⟩ := hbij.2 ⟨1, one_mem _⟩
    have h1 : (c : G) * e * (c : G)⁻¹ = 1 := congrArg Subtype.val hc
    apply he1
    calc e = (c : G)⁻¹ * (c * e * (c : G)⁻¹) * c := by group
      _ = 1 := by rw [h1]; group

theorem card_ge_of_mem [Finite G] {e : G} (he : e ∈ E) :
    16 ≤ Nat.card ((E ⊔ D) ⊓ centralizer ({e} : Set G) : Subgroup G) := by
  obtain ⟨c, hcD, hc1, hce⟩ := hA.exists_comm he
  have hle : E ⊔ zpowers c ≤ (E ⊔ D) ⊓ centralizer ({e} : Set G) := by
    refine sup_le (le_inf le_sup_left fun f hf => mem_centralizer_singleton_iff.2 (hA.comm hf he))
      ?_
    rw [zpowers_le]
    exact ⟨mem_sup_right hcD, mem_centralizer_singleton_iff.2 hce⟩
  have h2 := two_mul_card_le_of_mem (le_sup_left : E ≤ E ⊔ zpowers c)
    (mem_sup_right (mem_zpowers c)) (hA.not_mem_of_ne_one hcD hc1)
  rw [hA.cardE] at h2
  exact h2.trans (card_le_of_le hle)

private def psi {d : G} (hd : d ∈ D) : E →* G where
  toFun f := (f : G) * (d * f * d⁻¹)
  map_one' := by simp
  map_mul' f g := by
    have h1 : (g : G) * (d * f * d⁻¹) = d * f * d⁻¹ * g := hA.comm g.2 (hA.conj_mem hd f.2)
    simp only [Subgroup.coe_mul]
    calc (f : G) * g * (d * (f * g) * d⁻¹) = f * (g * (d * f * d⁻¹)) * (d * g * d⁻¹) := by
          group
      _ = f * (d * f * d⁻¹) * (g * (d * g * d⁻¹)) := by rw [h1]; group

private theorem psi_apply {d : G} (hd : d ∈ D) (f : E) :
    hA.psi hd f = f * (d * f * d⁻¹) := rfl

private theorem psi_eq_one_iff {d : G} (hd : d ∈ D) (f : E) :
    hA.psi hd f = 1 ↔ (f : G) * d = d * f := by
  rw [psi_apply]
  constructor
  · intro h1
    have h2 : d * f * d⁻¹ = f := (eq_inv_of_mul_eq_one_right h1).trans (hA.inv_eq f.2)
    calc (f : G) * d = d * f * d⁻¹ * d := by rw [h2]
      _ = d * f := by group
  · intro h1
    have h2 : d * f * d⁻¹ = f := by rw [← h1]; group
    rw [h2]
    exact hA.sq _ f.2

private theorem psi_mem {d : G} (hd : d ∈ D) (hdd : d * d = 1) (f : E) :
    hA.psi hd f ∈ E ⊓ centralizer ({d} : Set G) := by
  have hu := hA.conj_mem hd f.2
  have hc : (f : G) * (d * f * d⁻¹) = d * f * d⁻¹ * f := hA.comm f.2 hu
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  refine ⟨mul_mem f.2 hu, mem_centralizer_singleton_iff.2 ?_⟩
  rw [psi_apply]
  calc (f : G) * (d * f * d⁻¹) * d = d * f * d⁻¹ * f * d := by rw [hc]
    _ = d * (f * (d * f * d⁻¹)) := by rw [hdi]; group

theorem exists_comm_not_mem_zpowers [Finite G] {d : G} (hd : d ∈ D) (hdd : d * d = 1) :
    ∃ c ∈ D, c * d = d * c ∧ c ∉ zpowers d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDp : IsPGroup 2 D := IsPGroup.of_card (n := 3) (by rw [hA.cardD]; norm_num)
  have : Nontrivial D := Finite.one_lt_card_iff_nontrivial.1 (by rw [hA.cardD]; norm_num)
  have := hDp.center_nontrivial
  obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ := exists_ne (1 : center D)
  have hz₀c : ∀ x ∈ D, (z₀ : G) * x = x * z₀ := fun x hx =>
    (congrArg Subtype.val ((mem_center_iff.1 hz₀) ⟨x, hx⟩)).symm
  have hz₀1' : (z₀ : G) ≠ 1 := fun h => hz₀1 (Subtype.ext (Subtype.ext h))
  by_cases hz₀d : (z₀ : G) ∈ zpowers d
  · have hz₀eq : (z₀ : G) = d :=
      (eq_one_or_eq_of_mem_zpowers_of_mul_self hdd hz₀d).resolve_left hz₀1'
    have hnle : ¬ D ≤ zpowers d := by
      intro hle
      have h1 := card_le_of_le hle
      rw [hA.cardD, Nat.card_zpowers] at h1
      have h2 : orderOf d ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hdd)
      have h3 := Nat.le_of_dvd (by norm_num) h2
      omega
    obtain ⟨c, hcD, hcz⟩ := Set.not_subset.1 hnle
    exact ⟨c, hcD, by rw [← hz₀eq]; exact (hz₀c c hcD).symm, hcz⟩
  · exact ⟨z₀, z₀.2, hz₀c d hd, hz₀d⟩

private theorem card_cent_eq_four [Finite G] {d : G} (hd : d ∈ D) (hd1 : d ≠ 1)
    (hdd : d * d = 1) :
    Nat.card (E ⊓ centralizer ({d} : Set G) : Subgroup G) = 4 ∧
      (hA.psi hd).range.relIndex (E ⊓ centralizer ({d} : Set G)) = 2 := by
  have hIC : (hA.psi hd).range ≤ E ⊓ centralizer ({d} : Set G) := by
    rintro _ ⟨f, rfl⟩
    exact hA.psi_mem hd hdd f
  have hker : Nat.card (hA.psi hd).ker =
      Nat.card (E ⊓ centralizer ({d} : Set G) : Subgroup G) := Nat.card_congr
    { toFun := fun f => ⟨f.1.1, f.1.2,
        mem_centralizer_singleton_iff.2 ((hA.psi_eq_one_iff hd f.1).1 f.2)⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩,
        (hA.psi_eq_one_iff hd ⟨x.1, x.2.1⟩).2 (mem_centralizer_singleton_iff.1 x.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hprod : Nat.card (E ⊓ centralizer ({d} : Set G) : Subgroup G) *
      Nat.card (hA.psi hd).range = 8 := by
    rw [← hker, ← hA.cardE]
    exact card_ker_mul_card_range _
  have hCE : 2 * Nat.card (E ⊓ centralizer ({d} : Set G) : Subgroup G) ≤ 8 := by
    obtain ⟨f, hf, hfd⟩ : ∃ f ∈ E, ¬ d * f = f * d := by
      by_contra hne
      push Not at hne
      exact hd1 (hA.faith d hd hne)
    rw [← hA.cardE]
    exact two_mul_card_le_of_mem inf_le_left hf fun hfC =>
      hfd (mem_centralizer_singleton_iff.1 hfC.2).symm
  have hIle := card_le_of_le hIC
  have hC4 : Nat.card (E ⊓ centralizer ({d} : Set G) : Subgroup G) = 4 := by
    have : Nat.card (E ⊓ centralizer ({d} : Set G) : Subgroup G) ≤ 4 := by omega
    interval_cases h : Nat.card (E ⊓ centralizer ({d} : Set G) : Subgroup G) <;> omega
  have hI2 : Nat.card (hA.psi hd).range = 2 := by
    rw [hC4] at hprod
    omega
  refine ⟨hC4, ?_⟩
  have h := relIndex_mul_card (H := (hA.psi hd).range) (K := E ⊓ centralizer ({d} : Set G))
  rw [inf_of_le_left hIC, hC4, hI2] at h
  omega

private theorem conj_mem_psi_range {d c : G} (hd : d ∈ D) (hc : c ∈ D) (hcd : c * d = d * c)
    {x : G} (hx : x ∈ (hA.psi hd).range) : c * x * c⁻¹ ∈ (hA.psi hd).range := by
  obtain ⟨f, rfl⟩ := hx
  refine ⟨⟨c * f * c⁻¹, hA.conj_mem hc f.2⟩, ?_⟩
  rw [psi_apply, psi_apply]
  have h1 : c⁻¹ * d * c = d := by rw [mul_assoc, ← hcd, inv_mul_cancel_left]
  have h2 : c⁻¹ * d⁻¹ = d⁻¹ * c⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hcd]
  calc c * f * c⁻¹ * (d * (c * f * c⁻¹) * d⁻¹)
      = c * f * (c⁻¹ * d * c) * f * (c⁻¹ * d⁻¹) := by group
    _ = c * f * d * f * (d⁻¹ * c⁻¹) := by rw [h1, h2]
    _ = c * (f * (d * f * d⁻¹)) * c⁻¹ := by group

private theorem mul_conj_mem_psi_range [Finite G] {d c e : G} (hd : d ∈ D) (hd1 : d ≠ 1)
    (hdd : d * d = 1) (hc : c ∈ D) (hcd : c * d = d * c) (he : e ∈ E) (hde : d * e = e * d) :
    e * (c * e * c⁻¹) ∈ (hA.psi hd).range := by
  have hidx := (hA.card_cent_eq_four hd hd1 hdd).2
  have hcd' : c⁻¹ * d = d * c⁻¹ := by
    calc c⁻¹ * d = c⁻¹ * (d * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * d) * c⁻¹ := by rw [hcd]
      _ = d * c⁻¹ := by group
  have heC : e ∈ E ⊓ centralizer ({d} : Set G) := ⟨he, mem_centralizer_singleton_iff.2 hde.symm⟩
  have hceC : c * e * c⁻¹ ∈ E ⊓ centralizer ({d} : Set G) := by
    refine ⟨hA.conj_mem hc he, mem_centralizer_singleton_iff.2 ?_⟩
    calc c * e * c⁻¹ * d = c * e * (c⁻¹ * d) := by group
      _ = c * (e * d) * c⁻¹ := by rw [hcd']; group
      _ = c * (d * e) * c⁻¹ := by rw [hde]
      _ = c * d * e * c⁻¹ := by group
      _ = d * (c * e * c⁻¹) := by rw [hcd]; group
  have hiff := mul_mem_iff_of_index_two hidx (a := ⟨e, heC⟩) (b := ⟨c * e * c⁻¹, hceC⟩)
  rw [mem_subgroupOf, mem_subgroupOf, mem_subgroupOf] at hiff
  refine hiff.2 ⟨fun h => hA.conj_mem_psi_range hd hc hcd h, fun h => ?_⟩
  have h2 := hA.conj_mem_psi_range hd (inv_mem hc) hcd' h
  rwa [show c⁻¹ * (c * e * c⁻¹) * c⁻¹⁻¹ = e by group] at h2

theorem card_ge_of_ne [Finite G] {e d : G} (he : e ∈ E) (hd : d ∈ D) (hd1 : d ≠ 1)
    (hdd : d * d = 1) (hde : d * e = e * d) :
    16 ≤ Nat.card ((E ⊔ D) ⊓ centralizer ({e * d} : Set G) : Subgroup G) := by
  have hC4 := (hA.card_cent_eq_four hd hd1 hdd).1
  obtain ⟨c, hcD, hcd, hcz⟩ := hA.exists_comm_not_mem_zpowers hd hdd
  obtain ⟨f, hf⟩ := hA.mul_conj_mem_psi_range hd hd1 hdd hcD hcd he hde
  rw [psi_apply] at hf
  have hkey : (f : G) * (c * e * c⁻¹) = e * (d * f * d⁻¹) :=
    mul_eq_mul_swap (hA.comm (hA.conj_mem hcD he) (hA.conj_mem hd f.2))
      (hA.sq _ (hA.conj_mem hd f.2)) (hA.sq _ (hA.conj_mem hcD he)) hf
  have hfc : (f : G) * c ∈ centralizer ({e * d} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc (f : G) * c * (e * d) = f * (c * e * c⁻¹) * (c * d) := by group
      _ = e * (d * f * d⁻¹) * (d * c) := by rw [hkey, hcd]
      _ = e * d * (f * c) := by group
  have hdC : d ∉ E ⊓ centralizer ({d} : Set G) := fun h => hA.not_mem_of_ne_one hd hd1 h.1
  have h8 := two_mul_card_le_of_mem
    (le_sup_left : E ⊓ centralizer ({d} : Set G) ≤ E ⊓ centralizer ({d} : Set G) ⊔ zpowers d)
    (mem_sup_right (mem_zpowers d)) hdC
  have hW₀le : E ⊓ centralizer ({d} : Set G) ⊔ zpowers d ≤ E ⊔ zpowers d :=
    sup_le (inf_le_left.trans le_sup_left) le_sup_right
  have hfcW : (f : G) * c ∉ E ⊓ centralizer ({d} : Set G) ⊔ zpowers d := by
    intro hmem
    obtain ⟨g, hg, w, hw, hgw⟩ :=
      (mem_sup_iff_of_le_normalizer (zpowers_le.2 (hA.norm hd))).1 (hW₀le hmem)
    have hwc := (hA.eq_of_mul_eq hg f.2 ((zpowers_le.2 hd) hw) hcD hgw).2
    exact hcz (hwc ▸ hw)
  have h16 := two_mul_card_le_of_mem
    (le_sup_left : E ⊓ centralizer ({d} : Set G) ⊔ zpowers d ≤
      E ⊓ centralizer ({d} : Set G) ⊔ zpowers d ⊔ zpowers ((f : G) * c))
    (mem_sup_right (mem_zpowers _)) hfcW
  have hW₁le : E ⊓ centralizer ({d} : Set G) ⊔ zpowers d ⊔ zpowers ((f : G) * c) ≤
      (E ⊔ D) ⊓ centralizer ({e * d} : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      refine ⟨mem_sup_left hx.1, mem_centralizer_singleton_iff.2 ?_⟩
      have hxe : x * e = e * x := hA.comm hx.1 he
      have hxd : x * d = d * x := mem_centralizer_singleton_iff.1 hx.2
      calc x * (e * d) = x * e * d := by group
        _ = e * (x * d) := by rw [hxe]; group
        _ = e * d * x := by rw [hxd]; group
    · rw [zpowers_le]
      refine ⟨mem_sup_right hd, mem_centralizer_singleton_iff.2 ?_⟩
      calc d * (e * d) = d * e * d := by group
        _ = e * d * d := by rw [hde]
    · rw [zpowers_le]
      exact ⟨mul_mem (mem_sup_left f.2) (mem_sup_right hcD), hfc⟩
  rw [hC4] at h8
  calc 16 ≤ Nat.card (E ⊓ centralizer ({d} : Set G) ⊔ zpowers d ⊔ zpowers ((f : G) * c) :
      Subgroup G) := by omega
    _ ≤ _ := card_le_of_le hW₁le

theorem card_centralizer_ge [Finite G] {a : G} (ha : a ∈ E ⊔ D) (ha2 : a * a = 1) :
    16 ≤ Nat.card ((E ⊔ D) ⊓ centralizer ({a} : Set G) : Subgroup G) := by
  obtain ⟨e, he, d, hd, rfl⟩ := hA.mem_sup_iff.1 ha
  obtain ⟨hdd, hde⟩ := hA.sq_of_mul he hd ha2
  by_cases hd1 : d = 1
  · subst hd1
    simp only [mul_one]
    exact hA.card_ge_of_mem he
  · exact hA.card_ge_of_ne he hd hd1 hdd hde

end AffData

end CFSG.OddStandard.AltStdSmall4.WF9
