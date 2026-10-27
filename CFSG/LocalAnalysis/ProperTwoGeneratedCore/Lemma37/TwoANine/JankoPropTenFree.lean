module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTenA
public import CFSG.Adapters.QiuzhenLegacy.Compat.G3.DicksonCounting

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTen

open Subgroup

variable {G : Type} [Group G]

@[expose] def powSubgroup (A : Subgroup G) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (n : ℕ) :
    Subgroup G where
  carrier := {a | a ∈ A ∧ a ^ n = 1}
  mul_mem' {a b} ha hb := ⟨A.mul_mem ha.1 hb.1, by
    rw [(Commute.mul_pow (hA a ha.1 b hb.1)) n, ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨A.one_mem, one_pow n⟩
  inv_mem' {a} ha := ⟨A.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

variable [Finite G] {z : G} {fr : JankoFrame G z}

namespace Hyp

theorem exists_T (fr : JankoFrame G z) : ∃ T : Subgroup G, T ≤ fr.F₁ ∧ Nat.card T = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := fr.F₁) 2 (n := 3)
    (by rw [fr.card_F₁]; norm_num)
  refine ⟨K.map fr.F₁.subtype, map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective fr.F₁.subtype_injective, hK]
  norm_num

omit [Finite G] in
theorem F₁_le_F (fr : JankoFrame G z) : fr.F₁ ≤ fr.F := fr.F₁_eq ▸ inf_le_left

omit [Finite G] in
theorem F₁_le_t (fr : JankoFrame G z) : fr.F₁ ≤ centralizer ({fr.t} : Set G) :=
  fr.F₁_eq ▸ inf_le_right

omit [Finite G] in
theorem F₁_le_normalizer_At (fr : JankoFrame G z) : fr.F₁ ≤ normalizer (fr.At : Set G) :=
  fun _ hu => inf_mem_normalizer (C₁_le_normalizer_M fr (fr.F_le_centralizer (F₁_le_F fr hu)))
    (Subgroup.le_normalizer (F₁_le_t fr hu))

theorem exists_pow_eq_z (fr : JankoFrame G z) {T : Subgroup G} (hTF : T ≤ fr.F)
    (hT : Nat.card T = 8) {u : G} (hu : u ∈ T) (hu1 : u ≠ 1) : ∃ k : ℕ, u ^ k = z := by
  have hdvd : orderOf u ∣ 2 ^ 3 := by
    have := Subgroup.orderOf_dvd_natCard T hu
    rwa [hT] at this
  obtain ⟨m, hm, hmu⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hu1 (orderOf_eq_one_iff.mp (by rw [hmu, pow_zero]))
  have heven : 2 ∣ orderOf u := by
    rw [hmu]; exact dvd_pow_self 2 hm0
  set n := orderOf u / 2 with hn
  have hn0 : n ≠ 0 := by
    have : 0 < orderOf u := orderOf_pos u
    omega
  have hndvd : n ∣ orderOf u := Nat.div_dvd_of_dvd heven
  have hord : orderOf (u ^ n) = 2 := by
    rw [orderOf_pow_of_dvd hn0 hndvd, hn, Nat.div_div_self heven (orderOf_pos u).ne']
  exact ⟨n, fr.eq_z_of_mem_F _ (pow_mem (hTF hu) n) hord⟩

theorem eq_one_of_commute (h : Hyp fr) {T : Subgroup G} (hTF : T ≤ fr.F₁)
    (hT : Nat.card T = 8) {u a : G} (hu : u ∈ T) (hu1 : u ≠ 1) (ha : a ∈ fr.At)
    (hua : u * a = a * u) : a = 1 := by
  obtain ⟨k, hk⟩ := exists_pow_eq_z fr (hTF.trans (F₁_le_F fr)) hT hu hu1
  have hza : a * z = z * a := by
    rw [← hk]; exact ((Commute.pow_left hua k).eq).symm
  have : a ∈ fr.At ⊓ centralizer ({z} : Set G) := ⟨ha, mem_centralizer_singleton_iff.mpr hza⟩
  rwa [At_inf_H h, mem_bot] at this

theorem eight_dvd_card_sub_one
    (h : Hyp fr) {T : Subgroup G} (hTF : T ≤ fr.F₁)
    (hT : Nat.card T = 8) {B : Subgroup G} (hBA : B ≤ fr.At)
    (hTB : T ≤ normalizer (B : Set G)) : 8 ∣ Nat.card B - 1 := by
  let := Walter.J1.conjAct T B hTB
  have key := CFSG.Glauberman.Dickson.h826_card_actor_dvd_group_card_sub_one (A := T) (E := B)
    (fun a ha e hae => by
      have hae' : (a : G) * e * (a : G)⁻¹ = e := congrArg Subtype.val hae
      have hcomm : (a : G) * e = e * a := by
        calc (a : G) * e = (a : G) * e * (a : G)⁻¹ * a := by group
          _ = e * a := by rw [hae']
      have ha1 : (a : G) ≠ 1 := fun h1 => ha (Subtype.ext h1)
      exact Subtype.ext (eq_one_of_commute h hTF hT a.2 ha1 (hBA e.2) hcomm))
  rwa [hT] at key

theorem card_centralizer_t (h : Hyp fr) :
    Nat.card (centralizer ({fr.t} : Set G)) = 362880 :=
  (h.set.twoANine_centralizer fr.t fr.orderOf_t).card_eq

theorem card_dvd_of_le_At (h : Hyp fr) {B : Subgroup G} (hB : B ≤ fr.At) :
    Nat.card B ∣ 362880 :=
  card_centralizer_t h ▸ Subgroup.card_dvd_of_le (hB.trans (At_le_t fr))

theorem T_le_normalizer_powSubgroup (h : Hyp fr) {T : Subgroup G} (hTF : T ≤ fr.F₁) (n : ℕ) :
    T ≤ normalizer (powSubgroup fr.At (fun _ ha _ hb => At_comm h ha hb) n : Set G) :=
  fun u hu => Walter.J1.mem_normalizer_of_conj_mem fun x hx =>
    ⟨conj_mem_of_le_normalizer (F₁_le_normalizer_At fr) (hTF hu) hx.1, by
      rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩

theorem not_dvd_card_At
    (h : Hyp fr) {p : ℕ} (hp : p.Prime) (hp8 : ¬ 8 ∣ p - 1)
    (hp2 : ¬ p ^ 2 ∣ 362880) : ¬ p ∣ Nat.card fr.At := by
  intro hpA
  obtain ⟨T, hTF, hT⟩ := exists_T fr
  have : Fact p.Prime := ⟨hp⟩
  set B := powSubgroup fr.At (fun _ ha _ hb => At_comm h ha hb) p
  have hBA : B ≤ fr.At := fun x hx => hx.1
  have hB : IsPGroup p B := fun x => ⟨1, Subtype.ext (by simpa using x.2.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hB
  have hdvd := card_dvd_of_le_At h hBA
  rw [hn] at hdvd
  have hn1 : n ≤ 1 := by
    by_contra hcon
    exact hp2 ((pow_dvd_pow p (by omega : 2 ≤ n)).trans hdvd)
  have h8 := eight_dvd_card_sub_one h hTF hT hBA (T_le_normalizer_powSubgroup h hTF p)
  rw [hn] at h8
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := fr.At) p hpA
  have hxB : (x : G) ∈ B := by
    refine ⟨x.2, ?_⟩
    rw [← Subgroup.orderOf_coe] at hx
    rw [← hx]
    exact pow_orderOf_eq_one _
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hB1 : B = ⊥ := Subgroup.eq_bot_of_card_eq B (by rw [hn, pow_zero])
    rw [hB1, mem_bot] at hxB
    rw [show x = 1 from Subtype.ext hxB, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have : n = 1 := by omega
  rw [this, pow_one] at h8
  exact hp8 h8

theorem card_At (h : Hyp fr) : Nat.card fr.At = 9 := by
  obtain ⟨T, hTF, hT⟩ := exists_T fr
  have h5 := not_dvd_card_At h Nat.prime_five (by decide) (by decide)
  have h7 := not_dvd_card_At h (by norm_num : Nat.Prime 7) (by decide) (by decide)
  have h2 : ¬ 2 ∣ Nat.card fr.At := fun h2 => by
    have := Odd.of_dvd_nat (odd_card_M fr) (Subgroup.card_dvd_of_le (At_le_M fr))
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h2)
  have hdvd := card_dvd_of_le_At h (le_refl fr.At)
  have hcop : Nat.Coprime (Nat.card fr.At) (2 ^ 7 * 5 * 7) := by
    refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_
    · exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
    · exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h5).symm
    · exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).mpr h7).symm
  have h81 : Nat.card fr.At ∣ 3 ^ 4 :=
    hcop.dvd_of_dvd_mul_right (by
      rw [show 3 ^ 4 * (2 ^ 7 * 5 * 7) = 362880 by norm_num]; exact hdvd)
  obtain ⟨m, hm, hmA⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h81
  have h8 := eight_dvd_card_sub_one h hTF hT le_rfl (fun u hu => F₁_le_normalizer_At fr (hTF hu))
  rw [hmA] at h8
  have hne1 : Nat.card fr.At ≠ 1 := fun h1 => At_ne_bot h (Subgroup.eq_bot_of_card_eq _ h1)
  interval_cases m
  · exact absurd hmA (by simpa using hne1)
  · norm_num at h8
  · simpa using hmA
  · norm_num at h8
  · exfalso
    obtain ⟨frt⟩ := h.frames fr.t fr.orderOf_t
    obtain ⟨a, ha, b, hb, hab⟩ := frt.exists_ne_comm fr.At (At_le_t fr) (by rw [hmA]; norm_num)
    exact hab (At_comm h ha hb)

theorem pow_three_of_mem_At
    (h : Hyp fr) {x : G} (hx : x ∈ fr.At) : x ^ 3 = 1 := by
  obtain ⟨T, hTF, hT⟩ := exists_T fr
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := powSubgroup fr.At (fun _ ha _ hb => At_comm h ha hb) 3
  have hBA : B ≤ fr.At := fun x hx => hx.1
  have h8 := eight_dvd_card_sub_one h hTF hT hBA (T_le_normalizer_powSubgroup h hTF 3)
  have hdvd : Nat.card B ∣ 9 := card_At h ▸ Subgroup.card_dvd_of_le hBA
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := fr.At) 3 (by rw [card_At h]; norm_num)
  have hyB : (y : G) ∈ B := by
    refine ⟨y.2, ?_⟩
    rw [← Subgroup.orderOf_coe] at hy
    rw [← hy]
    exact pow_orderOf_eq_one _
  have hB1 : Nat.card B ≠ 1 := by
    intro h1
    have hB : B = ⊥ := Subgroup.eq_bot_of_card_eq B h1
    rw [hB, mem_bot] at hyB
    rw [show y = 1 from Subtype.ext hyB, orderOf_one] at hy
    omega
  have hB9 : Nat.card B = 9 := by
    have hle : Nat.card B ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hc : Nat.card B <;> simp_all
  have hBeq : B = fr.At := Subgroup.eq_of_le_of_card_ge hBA (by rw [hB9, card_At h])
  exact (hBeq ▸ hx : x ∈ B).2

theorem card_Atz (h : Hyp fr) : Nat.card fr.Atz = 9 :=
  (card_Atz_eq fr).trans (card_At h)

theorem card_M (h : Hyp fr) : Nat.card fr.M = 3 ^ 5 := by
  rw [card_M_eq h, card_At h]
  norm_num

theorem pow_three_of_mem_Atz
    (h : Hyp fr) {x : G} (hx : x ∈ fr.Atz) : x ^ 3 = 1 := by
  rw [← map_y_At fr] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [conj_pow, pow_three_of_mem_At h ha, mul_one, mul_inv_cancel]

theorem exists_conj_At
    (h : Hyp fr) {x y : G} (hx : x ∈ fr.At) (hy : y ∈ fr.At) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) : ∃ g ∈ centralizer ({fr.t} : Set G), g * x * g⁻¹ = y := by
  obtain ⟨T, hTF, hT⟩ := exists_T fr
  have hα : Nat.card {a : fr.At // a ≠ 1} = 8 := by
    classical
    let : Fintype fr.At := Fintype.ofFinite _
    have : Fintype.card {a : fr.At // a ≠ 1} = Fintype.card fr.At - 1 := by simp
    rw [Nat.card_eq_fintype_card, this, ← Nat.card_eq_fintype_card, card_At h]
  let f : T → {a : fr.At // a ≠ 1} := fun u =>
    ⟨⟨u * x * (u : G)⁻¹, conj_mem_of_le_normalizer (F₁_le_normalizer_At fr) (hTF u.2) hx⟩,
      fun h1 => hx1 (by
        have h1' : (u : G) * x * (u : G)⁻¹ = 1 := congrArg Subtype.val h1
        rw [mul_inv_eq_one, mul_eq_left] at h1'
        exact h1')⟩
  have hf : Function.Injective f := by
    intro u v huv
    have huv' : (u : G) * x * (u : G)⁻¹ = v * x * (v : G)⁻¹ :=
      congrArg (fun a : {a : fr.At // a ≠ 1} => ((a : fr.At) : G)) huv
    have hcomm : ((v : G)⁻¹ * u) * x = x * ((v : G)⁻¹ * u) := by
      calc ((v : G)⁻¹ * u) * x = (v : G)⁻¹ * ((u : G) * x * (u : G)⁻¹) * u := by group
        _ = (v : G)⁻¹ * (v * x * (v : G)⁻¹) * u := by rw [huv']
        _ = x * ((v : G)⁻¹ * u) := by group
    by_contra hne
    have hvu : (v : G)⁻¹ * u ≠ 1 := fun h1 => hne (Subtype.ext (inv_mul_eq_one.mp h1).symm)
    exact hx1 (eq_one_of_commute h hTF hT (T.mul_mem (T.inv_mem v.2) u.2) hvu hx hcomm)
  obtain ⟨u, hu⟩ := (hf.bijective_of_nat_card_le (by rw [hα, hT])).2
    ⟨⟨y, hy⟩, fun h1 => hy1 (congrArg Subtype.val h1)⟩
  exact ⟨u, F₁_le_t fr (hTF u.2), congrArg (fun a : {a : fr.At // a ≠ 1} => ((a : fr.At) : G)) hu⟩

theorem isConj_of_mem_At
    (h : Hyp fr) {x : G} (hx : x ∈ fr.At) (hx1 : x ≠ 1) :
    IsConj x fr.s₃ := by
  obtain ⟨frt⟩ := h.frames fr.t fr.orderOf_t
  have h162 := frt.type_s₃_of_conj fr.At (At_le_t fr) (card_At h)
    (fun a ha b hb ha1 hb1 => exists_conj_At h ha hb ha1 hb1) x hx hx1
  exact (h.p7.isConj_s₃_iff fr.t fr.orderOf_t x (At_le_t fr hx)
    (pow_three_of_mem_At h hx)).mpr h162

theorem isConj_of_mem_Atz
    (h : Hyp fr) {x : G} (hx : x ∈ fr.Atz) (hx1 : x ≠ 1) :
    IsConj x fr.s₃ := by
  rw [← map_y_At fr] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  have ha1 : a ≠ 1 := by rintro rfl; exact hx1 (map_one _)
  exact (isConj_iff.mpr ⟨fr.ℓ ^ 2, rfl⟩).symm.trans (isConj_of_mem_At h ha ha1)

theorem not_At_le (h : Hyp fr) : ¬ fr.At ≤ centralizer (fr.P₂ : Set G) := by
  intro hle
  set K₀ := fr.F₁ ⊓ centralizer (fr.At : Set G)
  have hP₂K : fr.P₂ ≤ K₀ := le_inf fr.P₂_le_F₁ fun p hp =>
    mem_centralizer_iff.mpr fun a ha => (mem_centralizer_iff.mp (hle ha) p hp).symm
  have hodd : ¬ 2 ∣ Nat.card K₀ := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K₀) 2 h2
    have hx' : orderOf (x : G) = 2 := by rwa [Subgroup.orderOf_coe]
    have hxz : (x : G) = z := fr.eq_z_of_mem_F x (F₁_le_F fr x.2.1) hx'
    have hAz : fr.At ≤ fr.At ⊓ centralizer ({z} : Set G) := fun a ha => ⟨ha, by
      refine mem_centralizer_singleton_iff.mpr ?_
      rw [← hxz]
      exact mem_centralizer_iff.mp x.2.2 a ha⟩
    rw [At_inf_H h] at hAz
    exact At_ne_bot h (le_bot_iff.mp hAz)
  have hdvd24 : Nat.card K₀ ∣ 24 := fr.card_F₁ ▸ Subgroup.card_dvd_of_le inf_le_left
  have hcard3 : Nat.card fr.P₂ = 3 := by rw [fr.P₂_eq, Nat.card_zpowers, fr.orderOf_s₂]
  have h3 : 3 ∣ Nat.card K₀ := hcard3 ▸ Subgroup.card_dvd_of_le hP₂K
  have hK3 : Nat.card K₀ = 3 := by
    have hle : Nat.card K₀ ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd24
    interval_cases hc : Nat.card K₀ <;> omega
  have hK : K₀ = fr.P₂ := (Subgroup.eq_of_le_of_card_ge hP₂K (by rw [hK3, hcard3])).symm
  apply fr.not_le_normalizer_P₂
  intro u hu
  rw [← hK]
  exact inf_mem_normalizer (Subgroup.le_normalizer hu)
    (mem_normalizer_centralizer (F₁_le_normalizer_At fr hu))

end Hyp

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTen
