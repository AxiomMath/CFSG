module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinJ2A
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinOutC
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55AltHH

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinJ2

open Subgroup CFSG CFSG.GH74.GLS FinGlue
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer inner_normal)

theorem isPGroup_two {G : Type*} [Group G] {E : Subgroup G} (h : ∀ e ∈ E, e * e = 1) :
    IsPGroup 2 ↥E :=
  fun g => ⟨1, by rw [pow_one, pow_two]; exact Subtype.ext (h g g.2)⟩

theorem closure_union {G : Type} [Group G] {U Q : Subgroup G} (hU : IVK.IsFourSubgroup U)
    (hQ : IVK.IsFourSubgroup Q) (hUQ : ∀ u ∈ U, ∀ q ∈ Q, u * q = q * u) :
    (∀ e ∈ closure ((U : Set G) ∪ Q), ∀ f ∈ closure ((U : Set G) ∪ Q), e * f = f * e) ∧
      ∀ e ∈ closure ((U : Set G) ∪ Q), e * e = 1 := by
  have := hU.1
  have := hQ.1
  have hsq : ∀ x ∈ (U : Set G) ∪ Q, x * x = 1 := by
    rintro x (hx | hx) <;> rw [← pow_two]
    · exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) x hx
    · exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Q) x hx
  have hcomm : ∀ x ∈ (U : Set G) ∪ Q, ∀ y ∈ (U : Set G) ∪ Q, x * y = y * x := by
    rintro x (hx | hx) y (hy | hy)
    · exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥U)).comm ⟨x, hx⟩ ⟨y, hy⟩)
    · exact hUQ x hx y hy
    · exact (hUQ y hy x hx).symm
    · exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥Q)).comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hpair : ((U : Set G) ∪ Q).Pairwise Commute := fun a ha b hb _ => hcomm a ha b hb
  have hall : ∀ e ∈ closure ((U : Set G) ∪ Q), ∀ f ∈ closure ((U : Set G) ∪ Q),
      e * f = f * e := fun e he f hf =>
    congrArg Subtype.val ((Subgroup.isMulCommutative_closure hpair).is_comm.comm ⟨e, he⟩ ⟨f, hf⟩)
  refine ⟨hall, fun e he => ?_⟩
  induction he using Subgroup.closure_induction with
  | mem x hx => exact hsq x hx
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    calc x * y * (x * y) = (x * x) * (y * y) := by
          rw [mul_assoc, ← mul_assoc y x y, ← hall x hx y hy]; group
      _ = 1 := by rw [ihx, ihy, mul_one]
  | inv x hx ihx => rw [← mul_inv_rev, ihx, inv_one]

theorem sixteen_le_card {G : Type*} [Group G] [Finite G] {U Q : Subgroup G}
    (hU4 : Nat.card U = 4) (hQ4 : Nat.card Q = 4) (hUQ : U ⊓ Q = ⊥) {E : Subgroup G}
    (hUE : U ≤ E) (hQE : Q ≤ E) : 16 ≤ Nat.card E := by
  let f : ↥U × ↥Q → ↥E := fun x => ⟨x.1 * x.2, E.mul_mem (hUE x.1.2) (hQE x.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : G) * b = a' * b' := congrArg Subtype.val h
    have hm : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h']
        _ = b' * (b : G)⁻¹ := by group
    have hmem : (a' : G)⁻¹ * a ∈ U ⊓ Q := Subgroup.mem_inf.mpr
      ⟨U.mul_mem (U.inv_mem a'.2) a.2, hm ▸ Q.mul_mem b'.2 (Q.inv_mem b.2)⟩
    rw [hUQ, mem_bot] at hmem
    have ha : (a : G) = a' := by
      calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
        _ = a' := by rw [hmem, mul_one]
    have hb : (b : G) = b' := by
      rw [ha] at h'
      exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, hU4, hQ4] at h

theorem finCellB_of_facts {Y : Type} [Group Y] [Finite Y] (hc : center Y = ⊥)
    (hcard : Nat.card (MulAut Y) = 1209600) (hidx : Nat.card (MulAut Y) ≤ 2 * Nat.card Y)
    (h3 : ∀ y : Y, orderOf y = 3 → ∃ a b : Y, KleinWit y a b)
    (h5 : ∀ x : MulAut Y, orderOf x = 5 → ¬ 8 ∣ Nat.card ↥(centralizer ({x} : Set (MulAut Y))))
    (h7 : ∀ s y : Y, orderOf s = 2 → orderOf y = 7 → s * y ≠ y * s) : FinCellB Y := by
  intro p hp hp2 X U I Q hX hU hQ hQI hUQ _ hIU hUX hIX b hb hbp
  have hfin : Finite (MulAut Y) :=
    Finite.of_injective (fun α : MulAut Y => (α : Y → Y)) DFunLike.coe_injective
  have hO := FinOut.card_outer_le hc hidx
  have hInj := conj_injective_of_center' hc
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinner : ∀ x : MulAut Y, orderOf x = p → ∃ y : Y, MulAut.conj y = x ∧ orderOf y = p := by
    intro x hx
    obtain ⟨y, hy⟩ := FinOut.exists_conj_of_orderOf hO hp hp2 hx
    refine ⟨y, hy, ?_⟩
    rw [← orderOf_injective _ hInj y, hy, hx]
  have hpd : p ∣ 2 ^ 8 * (3 ^ 3 * (5 ^ 2 * 7)) := by
    have h : p ∣ Nat.card (MulAut Y) := by
      rw [← hbp]
      exact orderOf_dvd_natCard b
    rw [hcard] at h
    simpa using h
  have hp357 : p = 3 ∨ p = 5 ∨ p = 7 := by
    rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)) hp2
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
        (hp.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))
  rcases hp357 with rfl | hp57
  ·
    obtain ⟨y, rfl, hy⟩ := hinner b hbp
    obtain ⟨a, a', hw⟩ := h3 y hy
    obtain ⟨E, -, hEc, hEe, hEn, e, heE, hen⟩ := AltHH.klein_abstract ⊤ (mem_top a)
      (mem_top a') hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2.1 hw.2.2.2.2.2
    exact ⟨2, Nat.prime_two, by norm_num, E, isPGroup_two hEe, fun _ => hEc,
      fun z hz => by rw [MulAut.conj_apply]; exact hEn z hz, e, heE,
      by rw [MulAut.conj_apply]; exact hen⟩
  exfalso
  have hXc : Nat.card X = p ∨ Nat.card X = p ^ 2 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hX
    have hdvd : p ^ k ∣ 1209600 := hcard ▸ hk ▸ Subgroup.card_subgroup_dvd_card X
    have hk2 : k ≤ 2 := by
      by_contra h
      have h3' : p ^ 3 ∣ 1209600 := (Nat.pow_dvd_pow p (by omega)).trans hdvd
      rcases hp57 with rfl | rfl <;> norm_num at h3'
    have hk1 : 1 ≤ k := by
      by_contra h
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero] at hk
      have hb1 : b = 1 := by
        have hXb := (Subgroup.card_eq_one).mp hk
        rw [hXb, mem_bot] at hb
        exact hb
      rw [hb1, orderOf_one] at hbp
      exact hp.one_lt.ne hbp
    interval_cases k
    · left
      rw [hk, pow_one]
    · right
      exact hk
  have hUQc : ∀ u ∈ U, ∀ q ∈ Q, u * q = q * u := fun u hu q hq =>
    mem_centralizer_iff.mp (hIU (hQI hq)) u hu
  obtain ⟨hEc, hEe⟩ := closure_union hU hQ hUQc
  have hE16 : 16 ≤ Nat.card (closure ((U : Set (MulAut Y)) ∪ Q)) :=
    sixteen_le_card hU.2 hQ.2 hUQ (fun u hu => subset_closure (Or.inl hu))
      (fun q hq => subset_closure (Or.inr hq))
  have hEX : closure ((U : Set (MulAut Y)) ∪ Q) ≤ normalizer (X : Set (MulAut Y)) := by
    rw [closure_le]
    rintro g (hg | hg)
    · exact hUX hg
    · exact hIX (hQI hg)
  obtain ⟨x, -, hxo, hxE⟩ := exists_large_centralizer hp hp2 hXc hEe hEc hEX
  have hF8 : 8 ∣ Nat.card ↥(closure ((U : Set (MulAut Y)) ∪ Q) ⊓
      centralizer ({x} : Set (MulAut Y))) := by
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).1
      (isPGroup_two (E := closure ((U : Set (MulAut Y)) ∪ Q) ⊓
        centralizer ({x} : Set (MulAut Y))) fun e he => hEe e (mem_inf.mp he).1)
    have h8 : 8 ≤ 2 ^ j := by
      rw [← hj]
      omega
    have hj3 : 3 ≤ j := by
      by_contra h
      have hj' : j < 3 := by omega
      interval_cases j <;> simp at h8
    rw [hj]
    simpa using Nat.pow_dvd_pow 2 hj3
  rcases hp57 with rfl | rfl
  · exact h5 x hxo (hF8.trans (Subgroup.card_dvd_of_le inf_le_right))
  obtain ⟨y, rfl, hy⟩ := hinner x hxo
  set F := closure ((U : Set (MulAut Y)) ∪ Q) ⊓
    centralizer ({MulAut.conj y} : Set (MulAut Y)) with hF
  have : (inner Y).Normal := inner_normal Y
  let π : MulAut Y →* Outer Y := QuotientGroup.mk' (inner Y)
  have hker : ∀ φ : MulAut Y, π φ = 1 ↔ φ ∈ inner Y := fun φ => QuotientGroup.eq_one_iff φ
  let πF : ↥F →* Outer Y := π.comp F.subtype
  have hr2 : Nat.card ↥πF.range ≤ 2 := (Subgroup.card_le_card_group _).trans hO
  have hmul : Nat.card ↥πF.ker * Nat.card ↥πF.range = Nat.card F := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hk2 : 2 ≤ Nat.card ↥πF.ker := by
    have h8 : 8 ≤ Nat.card F := Nat.le_of_dvd Nat.card_pos hF8
    by_contra hk
    push Not at hk
    have := Nat.mul_le_mul (Nat.lt_succ_iff.mp hk) hr2
    omega
  obtain ⟨⟨t, htk⟩, ht1⟩ := (Subgroup.one_lt_card_iff_ne_bot _).mp hk2 |>
    fun h => (Subgroup.ne_bot_iff_exists_ne_one).mp h
  have ht1' : (t : MulAut Y) ≠ 1 := fun h => ht1 (Subtype.ext (Subtype.ext h))
  obtain ⟨s, hs'⟩ := MonoidHom.mem_range.mp ((hker _).mp htk)
  have hs : MulAut.conj s = (t : MulAut Y) := hs'
  have htE := (mem_inf.mp t.2).1
  have htC := (mem_inf.mp t.2).2
  have hs2 : orderOf s = 2 := by
    have hss : s ^ 2 = 1 := hInj (by rw [map_pow, hs, pow_two, hEe _ htE, map_one])
    exact orderOf_eq_prime hss (fun h => ht1' (by rw [← hs, h, map_one]))
  apply h7 s y hs2 hy
  apply hInj
  rw [map_mul, map_mul, hs]
  exact mem_centralizer_singleton_iff.mp htC

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinJ2
