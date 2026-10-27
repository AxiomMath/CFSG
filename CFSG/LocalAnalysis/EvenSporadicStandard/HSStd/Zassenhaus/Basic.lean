module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_normalizer_zpowers_of_commute {a t : G} (h : a * t = t * a) :
    a ∈ normalizer ((zpowers t : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  simp [MulAut.conj_apply, h]

theorem forall_conj_mul_of_conj_mul {L E : Subgroup G} {t z m : G}
    (htL : ∀ l ∈ L, l * t = t * l) (hEL : E ≤ L)
    (htrans : ∀ e ∈ E, e ≠ 1 → ∃ a ∈ normalizer (E : Set G) ⊓ L, a * z * a⁻¹ = e)
    (hm : m ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G)) (hmt : m * t * m⁻¹ = z * t) :
    ∀ e ∈ E, ∃ m' ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G),
      m' * t * m'⁻¹ = t * e := by
  intro e he
  by_cases he1 : e = 1
  · exact ⟨1, one_mem _, by simp [he1]⟩
  obtain ⟨a, ⟨haN, haL⟩, hae⟩ := htrans e he he1
  have hat : a * t = t * a := htL a haL
  refine ⟨a * m, mul_mem (inf_normalizer_le_normalizer_sup _ _
    ⟨mem_normalizer_zpowers_of_commute hat, haN⟩) hm, ?_⟩
  have h1 : a * m * t * (a * m)⁻¹ = a * (m * t * m⁻¹) * a⁻¹ := by group
  have h2 : a * t * a⁻¹ = t := by rw [hat, mul_inv_cancel_right]
  rw [h1, hmt]
  calc a * (z * t) * a⁻¹ = (a * z * a⁻¹) * (a * t * a⁻¹) := by group
    _ = e * t := by rw [hae, h2]
    _ = t * e := htL e (hEL he)

theorem commutator_sup_zpowers_le {L : Subgroup G} {t : G}
    (htL : t ∈ centralizer (L : Set G)) : ⁅L ⊔ zpowers t, L ⊔ zpowers t⁆ ≤ L := by
  have hle : zpowers t ≤ centralizer (L : Set G) := zpowers_le.2 htL
  rw [commutator_le]
  intro a ha b hb
  obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hle ha
  obtain ⟨l', hl', d, hd, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hb
  have hcL : ∀ x ∈ L, c * x = x * c := fun x hx => (mem_centralizer_iff.1 (hle hc) x hx).symm
  have hdL : ∀ x ∈ L, d * x = x * d := fun x hx => (mem_centralizer_iff.1 (hle hd) x hx).symm
  have hcd : c * d = d * c := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hc
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hd
    rw [← zpow_add, ← zpow_add, add_comm]
  have key : ⁅l * c, l' * d⁆ = ⁅l, l'⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    have h1 : l * c * (l' * d) * (l * c)⁻¹ * (l' * d)⁻¹ =
        l * (c * l') * d * c⁻¹ * l⁻¹ * d⁻¹ * l'⁻¹ := by group
    rw [h1, hcL l' hl']
    have h2 : l * (l' * c) * d * c⁻¹ * l⁻¹ * d⁻¹ * l'⁻¹ =
        l * l' * (c * d * c⁻¹) * l⁻¹ * d⁻¹ * l'⁻¹ := by group
    rw [h2, hcd, mul_inv_cancel_right]
    have h3 : l * l' * d * l⁻¹ * d⁻¹ * l'⁻¹ = l * l' * (d * l⁻¹) * d⁻¹ * l'⁻¹ := by group
    rw [h3, hdL l⁻¹ (inv_mem hl)]
    group
  rw [key, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hl hl') (inv_mem hl)) (inv_mem hl')

theorem eq_of_mem_zpowers_of_ne_one {z x : G} (hz2 : orderOf z = 2) (hx : x ∈ zpowers z)
    (hx1 : x ≠ 1) : x = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, hz2] at hx1 ⊢
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · simp [h0] at hx1
  · simp [h0]

theorem conj_eq_self_of_normalizer [Finite G] {L S : Subgroup G} {t z n : G}
    (htL : t ∈ centralizer (L : Set G)) (hSle : S ≤ L ⊔ zpowers t) (htS : t ∈ S)
    (hS2 : IsPGroup 2 S) (hz2 : orderOf z = 2)
    (hzc : centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L = zpowers z)
    (hnS : n ∈ normalizer (S : Set G)) (hR : 2 < Nat.card (S ⊓ L : Subgroup G)) :
    n * z * n⁻¹ = z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup G := S ⊓ L with hRdef
  have hRp : IsPGroup 2 R := hS2.to_le inf_le_left
  have : Group.IsNilpotent R := hRp.isNilpotent
  have hzR : z ∈ centralizer (R : Set G) ⊓ L := hzc ▸ mem_zpowers z
  have hne : commutator R ≠ ⊥ := by
    intro hbot
    have hcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
      intro a ha b hb
      have hab : ⁅(⟨a, ha⟩ : R), ⟨b, hb⟩⁆ ∈ commutator R :=
        commutator_mem_commutator (mem_top _) (mem_top _)
      rw [hbot, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hab
      exact congrArg Subtype.val hab
    have hle : R ≤ zpowers z := by
      intro r hr
      rw [← hzc]
      exact ⟨mem_centralizer_iff.2 fun b hb => (hcomm r hr b hb).symm, hr.2⟩
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hz2] at this
    omega
  obtain ⟨x, hx, hx1⟩ := ((commutator R ⊓ center R).bot_or_exists_ne_one).resolve_left
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hxC : (x : G) ∈ centralizer (R : Set G) ⊓ L := by
    refine ⟨mem_centralizer_iff.2 fun b hb => ?_, x.2.2⟩
    exact congrArg Subtype.val (mem_center_iff.1 hx.2 ⟨b, hb⟩)
  have hxz : (x : G) = z := by
    refine eq_of_mem_zpowers_of_ne_one hz2 (hzc ▸ hxC) ?_
    intro h
    exact hx1 (Subtype.ext h)
  have hzRR : z ∈ ⁅R, R⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨x, hx.1, hxz⟩
  have hSS : (⁅S, S⁆ : Subgroup G).map (MulAut.conj n : G →* G) = ⁅S, S⁆ := by
    rw [map_commutator, mem_normalizer_iff_map_conj_eq.1 hnS]
  have hnzS : n * z * n⁻¹ ∈ ⁅S, S⁆ := by
    rw [← hSS]
    exact ⟨z, commutator_mono inf_le_left inf_le_left hzRR, by simp [MulAut.conj_apply]⟩
  have hnzL : n * z * n⁻¹ ∈ L :=
    commutator_sup_zpowers_le htL (commutator_mono hSle hSle hnzS)
  have hzCS : z ∈ centralizer (S : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (zpowers_le.2 htL) (hSle hs)
    have hcS : c ∈ S := (zpowers_le.2 htS) hc
    have hlS : l ∈ S := by simpa using mul_mem hs (inv_mem hcS)
    have h1 : l * z = z * l := mem_centralizer_iff.1 hzR.1 l ⟨hlS, hl⟩
    have h2 : c * z = z * c := (mem_centralizer_iff.1 ((zpowers_le.2 htL) hc) z hzR.2).symm
    calc l * c * z = l * (c * z) := mul_assoc _ _ _
      _ = l * (z * c) := by rw [h2]
      _ = (l * z) * c := (mul_assoc _ _ _).symm
      _ = (z * l) * c := by rw [h1]
      _ = z * (l * c) := mul_assoc _ _ _
  have hnzCS : n * z * n⁻¹ ∈ centralizer (S : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    have hs' : n⁻¹ * s * n ∈ S := (mem_normalizer_iff''.1 hnS s).1 hs
    have := mem_centralizer_iff.1 hzCS _ hs'
    calc s * (n * z * n⁻¹) = n * ((n⁻¹ * s * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * s * n)) * n⁻¹ := by rw [this]
      _ = n * z * n⁻¹ * s := by group
  have hmem : n * z * n⁻¹ ∈ zpowers z := by
    rw [← hzc]
    exact ⟨centralizer_le inf_le_left hnzCS, hnzL⟩
  refine eq_of_mem_zpowers_of_ne_one hz2 hmem ?_
  intro h
  have : z = 1 := by
    have h' := congrArg (fun x => n⁻¹ * x * n) h
    simpa [mul_assoc] using h'
  rw [this, orderOf_one] at hz2
  omega

theorem conj_mem_of_mem_centralizer {L : Subgroup G} {t c l : G}
    (hinner : centralizer ({t} : Set G) = L ⊔ zpowers t) (htL : t ∈ centralizer (L : Set G))
    (hc : c ∈ centralizer ({t} : Set G)) (hl : l ∈ L) : c * l * c⁻¹ ∈ L := by
  rw [hinner] at hc
  obtain ⟨l0, hl0, d, hd, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer (zpowers_le.2 htL) hc
  have hdl : d * l = l * d := (mem_centralizer_iff.1 ((zpowers_le.2 htL) hd) l hl).symm
  have : l0 * d * l * (l0 * d)⁻¹ = l0 * l * l0⁻¹ := by
    calc l0 * d * l * (l0 * d)⁻¹ = l0 * (d * l) * d⁻¹ * l0⁻¹ := by group
      _ = l0 * (l * d) * d⁻¹ * l0⁻¹ := by rw [hdl]
      _ = l0 * l * l0⁻¹ := by group
  rw [this]
  exact mul_mem (mul_mem hl0 hl) (inv_mem hl0)

theorem conj_ne_of_inner {L : Subgroup G} {t z n : G}
    (hinner : centralizer ({t} : Set G) = L ⊔ zpowers t) (htL : t ∈ centralizer (L : Set G))
    (hLC : L ⊓ centralizer (L : Set G) = ⊥) (ht1 : t ≠ 1) (hzL : z ∈ L)
    (hnz : n * z * n⁻¹ = z) (hnt : n * t * n⁻¹ = z * t) (g : G) : g * t * g⁻¹ ≠ z := by
  intro hg
  set n' := g⁻¹ * n * g
  set t' := g⁻¹ * t * g
  have hzt : g⁻¹ * z * g = t := by rw [← hg]; group
  have hzc : ∀ x : G, x * z = z * x → g⁻¹ * x * g ∈ centralizer ({t} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff, ← hzt]
    calc g⁻¹ * x * g * (g⁻¹ * z * g) = g⁻¹ * (x * z) * g := by group
      _ = g⁻¹ * (z * x) * g := by rw [hx]
      _ = g⁻¹ * z * g * (g⁻¹ * x * g) := by group
  have htz : t * z = z * t := (mem_centralizer_iff.1 htL z hzL).symm
  have hnzc : n * z = z * n := by
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [hnz]
  have ht'C : t' ∈ centralizer ({t} : Set G) := hzc t htz
  have hn'C : n' ∈ centralizer ({t} : Set G) := hzc n hnzc
  have hn't' : n' * t' * n'⁻¹ = t * t' := by
    calc n' * t' * n'⁻¹ = g⁻¹ * (n * t * n⁻¹) * g := by simp only [n', t']; group
      _ = g⁻¹ * (z * t) * g := by rw [hnt]
      _ = (g⁻¹ * z * g) * (g⁻¹ * t * g) := by group
      _ = t * t' := by rw [hzt]
  have ht'' := ht'C
  rw [hinner] at ht''
  obtain ⟨l, hl, d, hd, hld⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (zpowers_le.2 htL) ht''
  have hn'd : n' * d * n'⁻¹ = d := by
    have := mem_centralizer_singleton_iff.1 hn'C
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hd
    rw [← conj_zpow, show n' * t * n'⁻¹ = t by rw [mul_inv_eq_iff_eq_mul, this]]
  have key : n' * l * n'⁻¹ * d = t * (l * d) := by
    rw [← hld, ← hn't', hld]
    calc n' * l * n'⁻¹ * d = n' * l * n'⁻¹ * (n' * d * n'⁻¹) := by rw [hn'd]
      _ = n' * (l * d) * n'⁻¹ := by group
  have htmem : t ∈ L := by
    have h1 : t = n' * l * n'⁻¹ * l⁻¹ := by
      have : n' * l * n'⁻¹ * d * d⁻¹ * l⁻¹ = t * (l * d) * d⁻¹ * l⁻¹ := by rw [key]
      simpa [mul_assoc] using this.symm
    rw [h1]
    exact mul_mem (conj_mem_of_mem_centralizer hinner htL hn'C hl) (inv_mem hl)
  have : t ∈ L ⊓ centralizer (L : Set G) := ⟨htmem, htL⟩
  rw [hLC, mem_bot] at this
  exact ht1 this

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
