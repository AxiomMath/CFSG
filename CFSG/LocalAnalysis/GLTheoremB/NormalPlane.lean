module

public import CFSG.LocalAnalysis.GLTheoremB.TheoremBFromTwo

public section

universe u

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Power

variable {R : Type*} [Group R]

theorem mul_pow_eq_of_central {x y d : R} (hd : ∀ g : R, g * d = d * g) (h : y * x = x * y * d)
    (n : ℕ) : (x * y) ^ n = x ^ n * y ^ n * d ^ n.choose 2 := by
  have hc : ∀ g : R, Commute d g := fun g => (hd g).symm
  have hyx : ∀ n : ℕ, y ^ n * x = x * y ^ n * d ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc y ^ (n + 1) * x = y * (y ^ n * x) := by rw [pow_succ', mul_assoc]
        _ = y * (x * y ^ n * d ^ n) := by rw [ih]
        _ = (y * x) * y ^ n * d ^ n := by simp only [mul_assoc]
        _ = x * y * d * y ^ n * d ^ n := by rw [h]
        _ = x * y * (d * y ^ n) * d ^ n := by simp only [mul_assoc]
        _ = x * y * (y ^ n * d) * d ^ n := by rw [(hc (y ^ n)).eq]
        _ = x * y ^ (n + 1) * d ^ (n + 1) := by
          rw [pow_succ', pow_succ']; simp only [mul_assoc]
  induction n with
  | zero => simp
  | succ n ih =>
    have hC : (x * y) * d ^ n.choose 2 = d ^ n.choose 2 * (x * y) :=
      ((hc (x * y)).pow_left _).symm.eq
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
      _ = x ^ n * y ^ n * d ^ n.choose 2 * (x * y) := by rw [ih]
      _ = x ^ n * y ^ n * ((d ^ n.choose 2) * (x * y)) := by simp only [mul_assoc]
      _ = x ^ n * y ^ n * ((x * y) * d ^ n.choose 2) := by rw [hC]
      _ = x ^ n * (y ^ n * x) * y * d ^ n.choose 2 := by simp only [mul_assoc]
      _ = x ^ n * (x * y ^ n * d ^ n) * y * d ^ n.choose 2 := by rw [hyx n]
      _ = x ^ (n + 1) * y ^ n * (d ^ n * y) * d ^ n.choose 2 := by
        rw [pow_succ]; simp only [mul_assoc]
      _ = x ^ (n + 1) * y ^ n * (y * d ^ n) * d ^ n.choose 2 := by
        rw [((hc y).pow_left n).eq]
      _ = x ^ (n + 1) * y ^ (n + 1) * d ^ (n + 1).choose 2 := by
        have hch : (n + 1).choose 2 = n + n.choose 2 := by
          have := Nat.choose_succ_succ n 1
          simpa using this
        rw [pow_succ y n, hch, pow_add d n]
        simp only [mul_assoc]

theorem mul_pow_prime_of_central {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {x y d : R}
    (hd : ∀ g : R, g * d = d * g) (hdp : d ^ p = 1) (h : y * x = x * y * d) :
    (x * y) ^ p = x ^ p * y ^ p := by
  rw [mul_pow_eq_of_central hd h p]
  have h2 : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)
  obtain ⟨k, hk⟩ := hp.out.dvd_choose_self (by norm_num) h2
  rw [hk, pow_mul, hdp, one_pow, mul_one]

end Power

section Quotient

variable {R : Type u} [Group R]

theorem normal_of_le_center {N : Subgroup R} (h : N ≤ Subgroup.center R) : N.Normal :=
  ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.1 (h hn) g
    rwa [this, mul_inv_cancel_right]⟩

theorem card_comap_mk [Finite R] (N : Subgroup R) [N.Normal] (H : Subgroup (R ⧸ N)) :
    Nat.card (H.comap (QuotientGroup.mk' N)) = Nat.card H * Nat.card N := by
  have h1 := Subgroup.card_mul_index (H.comap (QuotientGroup.mk' N))
  have h2 := Subgroup.card_mul_index H
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)] at h1
  have hidx : 0 < H.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hidx
  calc Nat.card (H.comap (QuotientGroup.mk' N)) * H.index = Nat.card R := h1
    _ = Nat.card (R ⧸ N) * Nat.card N := h3
    _ = Nat.card H * H.index * Nat.card N := by rw [h2]
    _ = Nat.card H * Nat.card N * H.index := by ring

end Quotient

section CaseA

variable {R : Type u} [Group R]

theorem isElemAbelian_zpowers_of_comm {p : ℕ} (hcomm : ∀ a b : R, a * b = b * a) {y : R}
    (hy : y ^ p = 1) : IsElemAbelian p (Subgroup.zpowers y) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a b)⟩⟩, fun w hw => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]

theorem exists_plane_of_cyclic_quotient {p : ℕ} [hp : Fact p.Prime] [Finite R]
    (hR : IsPGroup p R) (hnc : ¬ IsCyclic R) {z : R} (hz : z ∈ Subgroup.center R)
    (hzp : orderOf z = p) [(Subgroup.zpowers z).Normal]
    (hcyc : IsCyclic (R ⧸ Subgroup.zpowers z)) :
    ∃ U : Subgroup R, U.Normal ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2 := by
  have hp' : p.Prime := hp.out
  have hNc : Subgroup.zpowers z ≤ Subgroup.center R := (Subgroup.zpowers_le).2 hz
  have hcomm : ∀ a b : R, a * b = b * a := by
    have := (QuotientGroup.mk' (Subgroup.zpowers z)).isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [QuotientGroup.ker_mk']; exact hNc)
    exact fun a b => mul_comm' a b
  have hzpow : z ^ p = 1 := hzp ▸ pow_orderOf_eq_one z
  have hzcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzp]
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  have hsup : Subgroup.zpowers x ⊔ Subgroup.zpowers z = ⊤ := by
    rw [eq_top_iff]
    intro r _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg (QuotientGroup.mk r))
    have h1 : (x ^ k)⁻¹ * r ∈ Subgroup.zpowers z := by
      rw [← QuotientGroup.eq, QuotientGroup.mk_zpow]; exact hk
    have h2 : r = x ^ k * ((x ^ k)⁻¹ * r) := by group
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers x k))
      (Subgroup.mem_sup_right h1)
  have hzX : z ∉ Subgroup.zpowers x := by
    intro hzx
    apply hnc
    have : Subgroup.zpowers x = ⊤ := by
      rw [← hsup, sup_eq_left.2 ((Subgroup.zpowers_le).2 hzx)]
    exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨x, this⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hR x
  have hk1 : k ≠ 0 := by
    rintro rfl
    apply hnc
    have hx1 : x = 1 := orderOf_eq_one_iff.1 (by simpa using hk)
    rw [hx1, Subgroup.zpowers_one_eq_bot, bot_sup_eq] at hsup
    exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨z, hsup⟩
  set y : R := x ^ (p ^ (k - 1)) with hy
  have hyord : orderOf y = p := by
    rw [hy, orderOf_pow_of_dvd (pow_ne_zero _ hp'.ne_zero), hk]
    · rw [Nat.pow_div (by omega : k - 1 ≤ k) hp'.pos]
      have : k - (k - 1) = 1 := by omega
      rw [this, pow_one]
    · rw [hk]; exact pow_dvd_pow p (by omega)
  have hypow : y ^ p = 1 := hyord ▸ pow_orderOf_eq_one y
  have hyX : y ∈ Subgroup.zpowers x := Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _
  have hyN : y ∉ Subgroup.zpowers z := by
    intro hyn
    have hle : Subgroup.zpowers y ≤ Subgroup.zpowers z := (Subgroup.zpowers_le).2 hyn
    have hycard : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hyord]
    have heq : Subgroup.zpowers y = Subgroup.zpowers z :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hzcard, hycard])
    exact hzX (((Subgroup.zpowers_le).2 hyX) (heq ▸ Subgroup.mem_zpowers z))
  set U0 : Subgroup R := Subgroup.zpowers y ⊔ Subgroup.zpowers z with hU0
  have hU0el : IsElemAbelian p U0 :=
    isElemAbelian_sup_of_commute (isElemAbelian_zpowers_of_comm hcomm hypow)
      (isElemAbelian_zpowers_of_comm hcomm hzpow)
      (fun a _ => Subgroup.mem_centralizer_iff.2 fun b _ => hcomm b a)
  obtain ⟨j, hj⟩ := exists_card_eq_pow (hR.to_subgroup U0)
  have hgt : p < Nat.card U0 := by
    by_contra hle
    have heq : Subgroup.zpowers z = U0 :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hzcard]; omega)
    exact hyN (heq ▸ (le_sup_left : Subgroup.zpowers y ≤ U0) (Subgroup.mem_zpowers y))
  have hj2 : 2 ≤ j := by
    by_contra h
    have h1 : p ^ j ≤ p := by
      calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp'.pos (by omega)
        _ = p := pow_one p
    omega
  obtain ⟨K, -, hKel, hKcard⟩ := exists_le_isElemAbelian_card hU0el (n := 2)
    (hj ▸ pow_dvd_pow p hj2)
  exact ⟨K, ⟨fun n hn g => by
    rw [show g * n * g⁻¹ = n by rw [hcomm g n, mul_inv_cancel_right]]; exact hn⟩, hKel, hKcard⟩

end CaseA

section CaseB

variable {R : Type u} [Group R]

theorem exists_plane_of_quotient_plane {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) [Finite R]
    (hR : IsPGroup p R) {z : R} (hz : z ∈ Subgroup.center R) (hzp : orderOf z = p)
    [(Subgroup.zpowers z).Normal] (Ubar : Subgroup (R ⧸ Subgroup.zpowers z)) [Ubar.Normal]
    (hU : IsElemAbelian p Ubar) (hcard : Nat.card Ubar = p ^ 2) :
    ∃ U : Subgroup R, U.Normal ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2 := by
  have hp' : p.Prime := hp.out
  have hNc : Subgroup.zpowers z ≤ Subgroup.center R := (Subgroup.zpowers_le).2 hz
  have hzpow : z ^ p = 1 := hzp ▸ pow_orderOf_eq_one z
  have hNcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzp]
  have hker : (QuotientGroup.mk' (Subgroup.zpowers z)).ker = Subgroup.zpowers z :=
    QuotientGroup.ker_mk' _
  have hdcentral : ∀ d ∈ Subgroup.zpowers z, ∀ g : R, g * d = d * g := fun d hd g =>
    Subgroup.mem_center_iff.1 (hNc hd) g
  have hdp : ∀ d ∈ Subgroup.zpowers z, d ^ p = 1 := by
    intro d hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzpow, one_zpow]
  set W : Subgroup R := Ubar.comap (QuotientGroup.mk' (Subgroup.zpowers z)) with hW
  have hWcard : Nat.card W = p ^ 3 := by
    rw [hW, card_comap_mk, hcard, hNcard]; ring
  have hpowN : ∀ x ∈ W, x ^ p ∈ Subgroup.zpowers z := by
    intro x hx
    rw [← hker, MonoidHom.mem_ker, map_pow]
    exact hU.2 _ (Subgroup.mem_comap.1 hx)
  have hcommN : ∀ x ∈ W, ∀ y ∈ W, (x * y)⁻¹ * (y * x) ∈ Subgroup.zpowers z := by
    intro x hx y hy
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul,
      elemAbelian_comm hU (Subgroup.mem_comap.1 hx) (Subgroup.mem_comap.1 hy), inv_mul_cancel]
  have hpm : ∀ x ∈ W, ∀ y ∈ W, (x * y) ^ p = x ^ p * y ^ p := by
    intro x hx y hy
    have hd := hcommN x hx y hy
    refine mul_pow_prime_of_central hp2 (hdcentral _ hd) (hdp _ hd) ?_
    group
  let φ : ↥W →* R := MonoidHom.mk' (fun x : W => (x : R) ^ p) (fun a b => hpm a.1 a.2 b.1 b.2)
  have hrange : φ.range ≤ Subgroup.zpowers z := by
    rintro _ ⟨w, rfl⟩
    exact hpowN w.1 w.2
  have hrcard : Nat.card φ.range ≤ p := hNcard ▸ Subgroup.card_le_of_le hrange
  have hkr := Subgroup.card_ker_mul_card_range φ
  rw [hWcard] at hkr
  have hkerge : p ^ 2 ≤ Nat.card φ.ker := by
    have h1 : p * p ^ 2 ≤ Nat.card φ.ker * p := by
      calc p * p ^ 2 = p ^ 3 := by ring
        _ = Nat.card φ.ker * Nat.card φ.range := hkr.symm
        _ ≤ Nat.card φ.ker * p := Nat.mul_le_mul_left _ hrcard
    rw [mul_comm p] at h1
    exact Nat.le_of_mul_le_mul_right h1 hp'.pos
  set Ω : Subgroup R := φ.ker.map W.subtype with hΩ
  have hΩmem : ∀ x : R, x ∈ Ω ↔ x ∈ W ∧ x ^ p = 1 := by
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, hw⟩
    · rintro ⟨hx, hxp⟩
      exact ⟨⟨x, hx⟩, hxp, rfl⟩
  have hΩcard : Nat.card Ω = Nat.card φ.ker := Subgroup.card_map_of_injective W.subtype_injective
  have hΩW : Ω ≤ W := fun x hx => ((hΩmem x).1 hx).1
  have hΩn : Ω.Normal := ⟨fun n hn g => by
    rw [hΩmem] at hn ⊢
    refine ⟨(inferInstance : W.Normal).conj_mem n hn.1 g, ?_⟩
    rw [conj_pow, hn.2, mul_one, mul_inv_cancel]⟩
  have hΩdvd : Nat.card Ω ∣ p ^ 3 := hWcard ▸ Subgroup.card_dvd_of_le hΩW
  obtain ⟨i, hi, hΩi⟩ := (Nat.dvd_prime_pow hp').1 hΩdvd
  have hge : p ^ 2 ≤ p ^ i := hΩi ▸ hΩcard ▸ hkerge
  have hi2 : 2 ≤ i := (Nat.pow_le_pow_iff_right hp'.one_lt).1 hge
  rcases (by omega : i = 2 ∨ i = 3) with rfl | rfl
  · exact ⟨Ω, hΩn, ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hΩi,
      fun x hx => ((hΩmem x).1 hx).2⟩, hΩi⟩
  · have hΩeq : Ω = W := Subgroup.eq_of_le_of_card_ge hΩW (by rw [hWcard, hΩi])
    have hWp : ∀ x ∈ W, x ^ p = 1 := fun x hx => ((hΩmem x).1 (hΩeq ▸ hx)).2
    have hnil : Group.IsNilpotent (R ⧸ Subgroup.zpowers z) := (hR.to_quotient _).isNilpotent
    have hUne : Ubar ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hcard
      have := hp'.one_lt
      nlinarith
    obtain ⟨⟨xb, hxbU, hxbC⟩, hxb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hUne)
    have hxb1' : xb ≠ 1 := fun h => hxb1 (Subtype.ext h)
    have hxbord : orderOf xb = p := orderOf_eq_prime (hU.2 xb hxbU) hxb1'
    have hVU : Subgroup.zpowers xb ≤ Ubar := (Subgroup.zpowers_le).2 hxbU
    have hVc : Subgroup.zpowers xb ≤ Subgroup.center (R ⧸ Subgroup.zpowers z) :=
      (Subgroup.zpowers_le).2 hxbC
    have hVn : (Subgroup.zpowers xb).Normal := normal_of_le_center hVc
    have hVcard : Nat.card (Subgroup.zpowers xb) = p := by rw [Nat.card_zpowers, hxbord]
    have hUcard : Nat.card ((Subgroup.zpowers xb).comap (QuotientGroup.mk' (Subgroup.zpowers z)))
        = p ^ 2 := by
      rw [card_comap_mk, hVcard, hNcard]; ring
    exact ⟨(Subgroup.zpowers xb).comap (QuotientGroup.mk' (Subgroup.zpowers z)),
      Subgroup.normal_comap _, ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hUcard,
        fun x hx => hWp x (Subgroup.comap_mono hVU hx)⟩, hUcard⟩

end CaseB

section Induction

variable {p : ℕ} [hp : Fact p.Prime]

theorem exists_normal_plane (hp2 : p ≠ 2) {R : Type u} [Group R] [Finite R] (hR : IsPGroup p R)
    (hnc : ¬ IsCyclic R) :
    ∃ U : Subgroup R, U.Normal ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2 := by
  have hp' : p.Prime := hp.out
  suffices h : ∀ n : ℕ, ∀ (R : Type u) [Group R] [Finite R], Nat.card R = n → IsPGroup p R →
      ¬ IsCyclic R → ∃ U : Subgroup R, U.Normal ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2 from
    h _ R rfl hR hnc
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro R _ _ hcardR hR hnc
    have hnt : Nontrivial R := by
      by_contra h
      exact hnc (@isCyclic_of_subsingleton R _ (not_nontrivial_iff_subsingleton.1 h))
    have hnil : Group.IsNilpotent R := hR.isNilpotent
    have hCnt : Nontrivial (Subgroup.center R) := hR.center_nontrivial
    have hdvd : p ∣ Nat.card (Subgroup.center R) := by
      rcases (hR.to_subgroup (Subgroup.center R)).card_eq_or_dvd with h | h
      · exact absurd h (Finite.one_lt_card (α := Subgroup.center R)).ne'
      · exact h
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hz : (c : R) ∈ Subgroup.center R := c.2
    have hzp : orderOf (c : R) = p := by rw [← hc]; exact Subgroup.orderOf_coe c
    have : (Subgroup.zpowers (c : R)).Normal := normal_of_le_center ((Subgroup.zpowers_le).2 hz)
    by_cases hcyc : IsCyclic (R ⧸ Subgroup.zpowers (c : R))
    · exact exists_plane_of_cyclic_quotient hR hnc hz hzp hcyc
    · have hNcard : Nat.card (Subgroup.zpowers (c : R)) = p := by rw [Nat.card_zpowers, hzp]
      have hlt : Nat.card (R ⧸ Subgroup.zpowers (c : R)) < n := by
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers (c : R))
        have h2 : 0 < Nat.card (R ⧸ Subgroup.zpowers (c : R)) := Nat.card_pos
        rw [hNcard] at h1
        have := hp'.two_le
        nlinarith
      obtain ⟨Ubar, hUn, hUel, hUcard⟩ := ih _ hlt (R ⧸ Subgroup.zpowers (c : R)) rfl
        (hR.to_quotient _) hcyc
      exact exists_plane_of_quotient_plane hp2 hR hz hzp Ubar hUel hUcard

end Induction

section Subgroups

variable {G : Type*} [Group G]

theorem not_isCyclic_of_two_le_pRank [Finite G] {p : ℕ} [hp : Fact p.Prime] {R : Subgroup G}
    (h : 2 ≤ pRank p R) : ¬ IsCyclic R := by
  intro hcyc
  obtain ⟨E, hER, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (p := p) hp.out.one_lt R
  have hEcyc : IsCyclic E :=
    isCyclic_of_injective (Subgroup.inclusion hER) (Subgroup.inclusion_injective hER)
  exact not_isCyclic_of_isElemAbelian hE (by rw [hEc]; exact Nat.pow_le_pow_right hp.out.pos h)
    hEcyc

theorem normalPlaneLemma : NormalPlaneLemma := by
  intro p hp hp2 G _ _ R hR h2
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨U', hU'n, hU'el, hU'card⟩ :=
    exists_normal_plane hp2 hR (not_isCyclic_of_two_le_pRank h2)
  refine ⟨U'.map R.subtype, Subgroup.map_subtype_le U',
    ⟨CFSG.SectionRank.isElemAbelian_map hU'el _, ?_⟩, ?_⟩
  · rw [Subgroup.card_map_of_injective R.subtype_injective]
    exact hU'card
  · rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le U'),
      show (U'.map R.subtype).subgroupOf R = U' from
        Subgroup.comap_map_eq_self_of_injective R.subtype_injective U']
    exact hU'n

theorem theoremB_of_theoremOne_theoremTwo' (h1 : TheoremOne) (h2 : TheoremTwo) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → ∀ m : ℕ, 4 ≤ m →
        (∀ q ∈ GLABeta (m + 1) G, GLAWeakCoreLocal G q) →
          ∀ p ∈ GLABeta m G, GLAWeakCoreLocal G p ∨ GLADeltaZero G p :=
  theoremB_of_theoremOne_theoremTwo h1 h2 normalPlaneLemma

theorem theoremB_holds' (h1 : TheoremOne) (h2 : TheoremTwo) : TheoremB :=
  theoremB_of_theoremOne_theoremTwo' h1 h2

end Subgroups

end CFSG.LocalAnalysis.GLTheoremB
