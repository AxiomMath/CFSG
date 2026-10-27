module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalCentral

public section

namespace CFSG.OddStandard.AltStdBal

open Subgroup CFSG.OddStandard.Solomon75
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open scoped Pointwise

section FullPair

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem Cyc.of_card (d : Cyc L Q z) {R : Subgroup G} (hRK : R ≤ centralizer (L : Set G))
    (hR : IsPGroup 2 R) (hcard : Nat.card R = Nat.card Q) : ∃ z', Cyc L R z' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (L : Set G) with hK
  have hQ' : IsPGroup 2 (Q.subgroupOf K) := d.pgroup.of_equiv (subgroupOfEquivOfLe d.le).symm
  let S : Sylow 2 K := hQ'.toSylow d.odd_index
  have hS : IsCyclic S := by
    have h : IsCyclic (Q.subgroupOf K) := (subgroupOfEquivOfLe d.le).isCyclic.2 d.cyclic
    exact h
  have hRc : IsCyclic R := (isCyclic_and_card_le_of_le S hS hRK hR).1
  have h2 : 2 ∣ Nat.card R := by
    rw [hcard]
    have := orderOf_dvd_natCard (⟨z, d.mem⟩ : Q)
    rwa [Subgroup.orderOf_mk, d.order] at this
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 h2
  refine ⟨x, hRK, hR, ?_, hRc, ?_, x.2⟩
  · have e1 := relIndex_mul_card (H := R) (K := K)
    have e2 := relIndex_mul_card (H := Q) (K := K)
    rw [inf_of_le_left hRK] at e1
    rw [inf_of_le_left d.le] at e2
    have hpos : 0 < Nat.card Q := Nat.card_pos
    have : R.relIndex K = Q.relIndex K := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [← hcard]
      rw [e1, ← e2, hcard]
    rw [this]
    exact d.odd_index
  · rw [Subgroup.orderOf_coe]
    exact hx

theorem false_of_mem_inf_conj (h : Setting G L n) {g : G} (hg : g ∉ normalizer (L : Set G))
    {y : G} (hy : Even (orderOf y)) (hyK : y ∈ centralizer (L : Set G))
    (hyK' : y ∈ CFSG.conjugate (centralizer (L : Set G)) g) : False := by
  have hy1 : y ∈ (centralizer (L : Set G)).map (MulAut.conj (1 : G)).toMonoidHom := by
    simpa using hyK
  have hgN := mem_normalizer_of_even_orderOf_mem h.isStandard (a := 1) (b := g⁻¹) (x := y)
    hy hy1 hyK'
  have hgN' : g⁻¹ ∈ normalizer (centralizer (L : Set G) : Set G) := by simpa using hgN
  apply hg
  rw [← h.normalizer_eq]
  simpa using Subgroup.inv_mem _ hgN'

theorem inf_eq_bot_of_conj (h : Setting G L n) {g : G} (hg : g ∉ normalizer (L : Set G))
    {P P' : Subgroup G} (hP : P ≤ centralizer (L : Set G)) (hp : IsPGroup 2 P)
    (hP' : P' ≤ CFSG.conjugate (centralizer (L : Set G)) g) : P' ⊓ P = ⊥ := by
  by_contra hne
  have hPp : IsPGroup 2 (P' ⊓ P : Subgroup G) := hp.to_le inf_le_right
  obtain ⟨m, hm⟩ := hPp.exists_card_eq
  have h2 : 2 ∣ Nat.card (P' ⊓ P : Subgroup G) := by
    rcases m with _ | m
    · exfalso
      have h1 : Nat.card (P' ⊓ P : Subgroup G) = 1 := by simpa using hm
      exact hne (Subgroup.card_eq_one.1 h1)
    · rw [hm, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := (P' ⊓ P : Subgroup G)) 2 h2
  have hy2 : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
  exact false_of_mem_inf_conj h hg (by rw [hy2]; exact even_two)
    (hP (Subgroup.mem_inf.1 y.2).2) (hP' (Subgroup.mem_inf.1 y.2).1)

theorem mem_sup_of_mem_sup_centralizer (h : Setting G L n) (d : Cyc L Q z) {c : G}
    (hc : c ∈ centralizer ({z} : Set G)) (hcK : c ∈ L ⊔ centralizer (L : Set G)) :
    c ∈ L ⊔ Q := by
  have hKN : centralizer (L : Set G) ≤ normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left L (centralizer (L : Set G)) hKN
  have hcK' : c ∈ (L : Set G) * (centralizer (L : Set G) : Set G) := by
    rw [← hm]
    exact hcK
  obtain ⟨l, hl, k, hk, rfl⟩ := hcK'
  have hkC : k ∈ centralizer ({z} : Set G) := by
    have : k = l⁻¹ * (l * k) := by group
    rw [this]
    exact mul_mem (inv_mem (le_centralizer_single h d hl)) hc
  have hkQ : k ∈ Q := by
    rw [← cent_inf_eq h d]
    exact ⟨hk, hkC⟩
  exact mul_mem (mem_sup_left hl) (mem_sup_right hkQ)

theorem fullPair_analysis (h : Setting G L n) (d : Cyc L Q z) {g : G}
    (hg : g ∉ normalizer (L : Set G)) {T : Subgroup G}
    (hTK : T ≤ CFSG.conjugate (centralizer (L : Set G)) g) (hTp : IsPGroup 2 T)
    (hTcard : Nat.card T = Nat.card Q) (hQT : Q ≤ centralizer (T : Set G))
    (h4 : 4 ≤ Nat.card Q) :
    Nat.card Q = 4 ∧ ¬ T ≤ L ⊔ centralizer (L : Set G) ∧
      ¬ Q ≤ CFSG.conjugate L g ⊔ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
  have h' := h.conj g
  have d' := d.conj g
  have hTK' : T ≤ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
    rw [centralizer_conjugate]
    exact hTK
  obtain ⟨a, d₂⟩ := Cyc.of_card d' hTK' hTp (by rw [hTcard, card_conjugate])
  have hTz : ∀ t ∈ T, t * z = z * t := fun t ht =>
    mem_centralizer_iff.1 (hQT d.mem) t ht
  have hTC : T ≤ centralizer ({z} : Set G) := fun t ht => mem_centralizer_singleton_iff.2 (hTz t ht)
  have hTQ : T ⊓ Q = ⊥ := inf_eq_bot_of_conj h hg d.le d.pgroup hTK
  obtain ⟨t₀, ht₀T, ht₀⟩ := exists_orderOf_eq_two_pow (k := 2) d₂.cyclic d₂.pgroup
    (by rw [hTcard]; simpa using h4)
  have ht₀sq : orderOf (t₀ ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [ht₀]; norm_num), ht₀]
    norm_num
  have ha_eq : t₀ ^ 2 = a :=
    eq_of_orderOf_eq_two_of_isCyclic d₂.cyclic (pow_mem ht₀T 2) d₂.mem ht₀sq d₂.order
  have haLQ : a ∈ L ⊔ Q := ha_eq ▸ sq_mem_sup h d (hTC ht₀T)
  have hsq : ∀ t ∈ T, ∀ y ∈ L, y * a = a * y → t * y ^ 2 = y ^ 2 * t := by
    intro t ht y _ hya
    exact d₂.comm_sup ht (sq_mem_sup h' d₂ (mem_centralizer_singleton_iff.2 hya))
  have key := no_order_four_of_commute h d d₂.cyclic d₂.mem d₂.order hTQ haLQ hsq
  have hQ4 : Nat.card Q = 4 := by
    obtain ⟨j, hj⟩ := d.pgroup.exists_card_eq
    by_contra hne
    have hj3 : 3 ≤ j := by
      by_contra hlt
      push Not at hlt
      have h2j : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h2j
      omega
    have h8 : 2 ^ 3 ≤ Nat.card T := by
      rw [hTcard, hj]
      exact Nat.pow_le_pow_right (by norm_num) hj3
    obtain ⟨u, huT, hu⟩ := exists_orderOf_eq_two_pow (k := 3) d₂.cyclic d₂.pgroup h8
    have hu2 : orderOf (u ^ 2) = 4 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hu]; norm_num), hu]
      norm_num
    exact key (u ^ 2) (pow_mem huT 2) (sq_mem_sup h d (hTC huT)) hu2
  refine ⟨hQ4, fun hle => key t₀ ht₀T (mem_sup_of_mem_sup_centralizer h d (hTC ht₀T)
    (hle ht₀T)) (by simpa using ht₀), ?_⟩
  intro hle
  obtain ⟨q₀, hq₀Q, hq₀⟩ := exists_orderOf_eq_two_pow (k := 2) d.cyclic d.pgroup
    (by simpa using h4)
  have hq₀sq : orderOf (q₀ ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hq₀]; norm_num), hq₀]
    norm_num
  have hz_eq : q₀ ^ 2 = z :=
    eq_of_orderOf_eq_two_of_isCyclic d.cyclic (pow_mem hq₀Q 2) d.mem hq₀sq d.order
  have hq₀a : q₀ ∈ centralizer ({a} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 (hQT hq₀Q) a d₂.mem).symm
  have hzLT : z ∈ CFSG.conjugate L g ⊔ T := hz_eq ▸ sq_mem_sup h' d₂ hq₀a
  have hsq' : ∀ q ∈ Q, ∀ y ∈ CFSG.conjugate L g, y * z = z * y → q * y ^ 2 = y ^ 2 * q := by
    intro q hq y _ hyz
    exact d.comm_sup hq (sq_mem_sup h d (mem_centralizer_singleton_iff.2 hyz))
  have key' := no_order_four_of_commute h' d₂ d.cyclic d.mem d.order
    (by rw [inf_comm]; exact hTQ) hzLT hsq'
  exact key' q₀ hq₀Q (mem_sup_of_mem_sup_centralizer h' d₂ hq₀a (hle hq₀Q))
    (by simpa using hq₀)

theorem fullPair_false (h : Setting G L n) (d : Cyc L Q z) {g : G}
    (hg : g ∉ normalizer (L : Set G)) {T : Subgroup G}
    (hTK : T ≤ CFSG.conjugate (centralizer (L : Set G)) g) (hTp : IsPGroup 2 T)
    (hTcard : Nat.card T = Nat.card Q) (hQT : Q ≤ centralizer (T : Set G))
    (h4 : 4 ≤ Nat.card Q) : False := by
  obtain ⟨-, hTn, -⟩ := fullPair_analysis h d hg hTK hTp hTcard hQT h4
  obtain ⟨t, htT, htK⟩ := Set.not_subset.1 hTn
  have htC : t ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hQT d.mem) t htT)
  have htQ : t ∉ L ⊔ Q := fun hmem => htK (sup_le_sup_left d.le L hmem)
  have h2 := card_eq_two_of_central h d (fun c hc q hq =>
    central_of_commute_outer h d htC htQ hq (mem_centralizer_iff.1 (hQT hq) t htT) c hc)
  omega

end FullPair

end CFSG.OddStandard.AltStdBal
