module

public import CFSG.Certificates.Kernel.SporSch.SylowCount

public section

namespace CFSG.KS.SylowCount

open Finset
open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_subgroup_of_closed [Finite G] (S : Set G) (hne : S.Nonempty)
    (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) : ∃ H : Subgroup G, ∀ x, x ∈ H ↔ x ∈ S := by
  have hpow : ∀ x ∈ S, ∀ k, x ^ (k + 1) ∈ S := fun x hx k => by
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      rw [pow_succ]
      exact hmul _ ih _ hx
  have hone : (1 : G) ∈ S := by
    obtain ⟨x, hx⟩ := hne
    have h := hpow x hx (orderOf x - 1)
    rwa [Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one] at h
  have hinv : ∀ x ∈ S, x⁻¹ ∈ S := fun x hx => by
    have h := hpow x hx (2 * orderOf x - 2)
    have e : 2 * orderOf x - 2 + 1 = orderOf x + (orderOf x - 1) := by
      have := orderOf_pos x
      omega
    rw [e, pow_add, pow_orderOf_eq_one, one_mul] at h
    have hi : x⁻¹ = x ^ (orderOf x - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    rw [hi]
    exact h
  refine ⟨Subgroup.closure S, fun x => ⟨fun hx => ?_, fun hx => Subgroup.subset_closure hx⟩⟩
  induction hx using Subgroup.closure_induction with
  | mem x h => exact h
  | one => exact hone
  | mul x y _ _ hx hy => exact hmul x hx y hy
  | inv x _ hx => exact hinv x hx

theorem conj_into_of_card [Finite G] {p k : ℕ} [hp : Fact p.Prime] (H : Subgroup G)
    (hH : Nat.card H = p ^ k) (hk : ¬p ^ (k + 1) ∣ Nat.card G) {y : G} {e : ℕ}
    (hy : orderOf y = p ^ e) : ∃ c : G, c * y * c⁻¹ ∈ H := by
  have hpos : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hf : (Nat.card G).factorization p = k := by
    have h1 : p ^ k ∣ Nat.card G := by
      rw [← hH]
      exact Subgroup.card_subgroup_dvd_card H
    have hle := (hp.out.pow_dvd_iff_le_factorization hpos).1 h1
    have hlt : ¬k + 1 ≤ (Nat.card G).factorization p := fun h2 =>
      hk ((hp.out.pow_dvd_iff_le_factorization hpos).2 h2)
    omega
  let P : Sylow p G := Sylow.ofCard H (by rw [hH, hf])
  have hpg : IsPGroup p (Subgroup.zpowers y) := IsPGroup.of_card (by rw [Nat.card_zpowers, hy])
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  have hyQ : y ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers y)
  have h2 : MulAut.conj g • y ∈ MulAut.conj g • (Q : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (Q : Subgroup G) hyQ
  rw [← Sylow.coe_subgroup_smul, hg] at h2
  exact h2

variable [Fintype G]

open scoped Classical

theorem card_order_classes (m : ℕ) (R : List G) (hR : ∀ r ∈ R, orderOf r = m)
    (hRd : R.Pairwise fun i j => ¬IsConj i j)
    (hcov : ∀ y : G, orderOf y = m → ∃ r ∈ R, IsConj r y) :
    #(univ.filter fun y : G => orderOf y = m) =
      (R.map fun r => #(univ.filter (IsConj r))).sum := by
  have he : (univ.filter fun y : G => orderOf y = m) =
      univ.filter fun y : G => ∃ r ∈ R, IsConj r y := by
    refine Finset.filter_congr fun y _ => ⟨hcov y, ?_⟩
    rintro ⟨r, hr, hc⟩
    obtain ⟨c, rfl⟩ := isConj_iff.1 hc
    rw [orderOf_conj']
    exact hR r hr
  rw [he]
  clear he hcov hR
  induction R with
  | nil => simp
  | cons r R ih =>
    rw [List.pairwise_cons] at hRd
    have hu : (univ.filter fun y : G => ∃ s ∈ r :: R, IsConj s y) =
        (univ.filter (IsConj r)) ∪ univ.filter fun y : G => ∃ s ∈ R, IsConj s y := by
      ext y
      simp
    have hd : Disjoint (univ.filter (IsConj r)) (univ.filter fun y : G => ∃ s ∈ R, IsConj s y) := by
      rw [Finset.disjoint_filter]
      rintro y _ h1 ⟨s, hs, h2⟩
      exact hRd.1 s hs (h1.trans (isConj_comm.1 h2))
    rw [hu, card_union_of_disjoint hd, ih hRd.2, List.map_cons, List.sum_cons]

theorem not_isConj_of_comm_card {r s : G}
    (h : #(univ.filter fun c => c * r = r * c) ≠ #(univ.filter fun c => c * s = s * c)) :
    ¬IsConj r s := fun hc => by
  apply h
  have hr := card_conj_mul_card_comm r
  have hs := card_conj_mul_card_comm s
  have e : #(univ.filter (IsConj r)) = #(univ.filter (IsConj s)) := by
    congr 1
    exact Finset.filter_congr fun y _ => ⟨fun h => (isConj_comm.1 hc).trans h, fun h => hc.trans h⟩
  have hpos : 0 < #(univ.filter (IsConj s)) :=
    Finset.card_pos.2 ⟨s, mem_filter.2 ⟨mem_univ s, IsConj.refl s⟩⟩
  rw [e] at hr
  exact Nat.eq_of_mul_eq_mul_left hpos (hr.trans hs.symm)

end CFSG.KS.SylowCount

end
