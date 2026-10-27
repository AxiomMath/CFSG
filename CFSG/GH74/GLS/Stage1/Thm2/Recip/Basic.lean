module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Statements
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Core
public import CFSG.GH74.GLS.TwoThin.Rank

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

section Involutions

variable {G : Type*} [Group G]

theorem mul_self_eq_one_of_orderOf_eq_two {a : G} (h : orderOf a = 2) : a * a = 1 := by
  have := pow_orderOf_eq_one a
  rwa [h, pow_two] at this

theorem ne_one_of_orderOf_eq_two {a : G} (h : orderOf a = 2) : a ≠ 1 := by
  rintro rfl
  simp at h

theorem orderOf_eq_two_of_mul_self_eq_one {a : G} (h : a * a = 1) (h1 : a ≠ 1) : orderOf a = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h) h1

theorem orderOf_conj_eq (g a : G) : orderOf (g * a * g⁻¹) = orderOf a := by
  have := (MulAut.conj g).orderOf_eq a
  simpa [MulAut.conj_apply] using this

theorem inv_eq_self_of_mul_self_eq_one {a : G} (h : a * a = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right h

end Involutions

theorem mem_of_isSylow2In_of_central {G : Type*} [Group G] [Finite G] {S H : Subgroup G}
    (hS : IsSylow2In S H) {x : G} (hxH : x ∈ H) (hxc : ∀ h ∈ H, x * h = h * x)
    (hx : x * x = 1) : x ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSH, hSp, hSi⟩ := hS
  have hSp' : IsPGroup 2 ↥(S.subgroupOf H) := hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  have hidx : ¬ 2 ∣ (S.subgroupOf H).index := hSi
  let P : Sylow 2 ↥H := hSp'.toSylow hidx
  let x' : ↥H := ⟨x, hxH⟩
  have hx'c : ∀ g : ↥H, x' * g = g * x' := fun g => Subtype.ext (hxc g g.2)
  let N : Subgroup ↥H := zpowers x'
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    have : g * x' ^ k * g⁻¹ = x' ^ k := by
      have hc : Commute g x' := (hx'c g).symm
      rw [(hc.zpow_right k).eq]
      group
    rw [this]
    exact zpow_mem_zpowers _ _
  have hNp : IsPGroup 2 ↥N := by
    intro g
    refine ⟨1, ?_⟩
    have hx'sq : x' * x' = 1 := Subtype.ext hx
    apply Subtype.ext
    simp only [pow_one]
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    rcases eq_one_or_eq_of_mem_zpowers hx'sq g.2 with h | h <;> rw [h]
    · simp
    · rw [pow_two, hx'sq]
  have hle : N ≤ (P : Subgroup ↥H) := hNp.le_sylow_of_normal P
  have hx'P : x' ∈ (P : Subgroup ↥H) := hle (mem_zpowers x')
  have : x' ∈ S.subgroupOf H := by simpa [P, IsPGroup.toSylow_coe] using hx'P
  exact this

section TwoRank

variable {G : Type*} [Group G]

theorem isElemAbelian_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : CFSG.Open.IsElemAbelian 2 (Subgroup.closure ({a, b} : Set G)) := by
  have hcomm : IsMulCommutative (Subgroup.closure ({a, b} : Set G)) :=
    Subgroup.isMulCommutative_closure (by
      intro x hx y hy _
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact Commute.refl _
      · rw [Set.mem_singleton_iff.mp hy]; exact hab
      · rw [Set.mem_singleton_iff.mp hx]; exact hab.symm
      · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy])
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · rw [sq]; exact ha
    · rw [Set.mem_singleton_iff.mp hy, sq]; exact hb
  | one => simp
  | mul y z hy' hz' hy hz =>
    have hc : y * z = z * y := by
      have h := hcomm.is_comm.comm (⟨y, hy'⟩ : Subgroup.closure ({a, b} : Set G)) ⟨z, hz'⟩
      exact congrArg Subtype.val h
    rw [sq] at hy hz ⊢
    calc y * z * (y * z) = y * (z * y) * z := by group
      _ = y * (y * z) * z := by rw [← hc]
      _ = (y * y) * (z * z) := by group
      _ = 1 := by rw [hy, hz, one_mul]
  | inv y _ hy => rw [inv_pow, hy, inv_one]

theorem three_le_card_of_distinct [Finite G] {E : Subgroup G} {a b : G} (haE : a ∈ E) (hbE : b ∈ E)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) : 3 ≤ Nat.card E := by
  have hsub : ({1, a, b} : Set G) ⊆ (E : Set G) := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact E.one_mem
    · exact haE
    · exact hbE
  have h3 : ({1, a, b} : Set G).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨1, a, b, ha1.symm, hb1.symm, hne, rfl⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq (E : Set G)
  omega

variable [Finite G]

theorem two_le_pRank_of_pair {H : Subgroup G} {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) (haH : a ∈ H)
    (hbH : b ∈ H) : 2 ≤ CFSG.Open.pRank 2 H := by
  set E := Subgroup.closure ({a, b} : Set G) with hE
  have hEel : CFSG.Open.IsElemAbelian 2 E := isElemAbelian_closure_pair ha hb hab
  have haE : a ∈ E := Subgroup.subset_closure (by simp)
  have hbE : b ∈ E := Subgroup.subset_closure (by simp)
  have hEH : E ≤ H := (Subgroup.closure_le _).2 (by
    intro x hx
    rcases hx with rfl | hx
    · exact haH
    · rw [Set.mem_singleton_iff.mp hx]; exact hbH)
  have hpg : IsPGroup 2 E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hEel.2 x x.2⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hpg
  have h3 : 3 ≤ Nat.card E := three_le_card_of_distinct haE hbE ha1 hb1 hne
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    have : Nat.card E ≤ 2 := by
      rw [hn]
      interval_cases n <;> simp
    omega
  exact hn2.trans (CFSG.SectionRank.le_pRank one_lt_two hEH hEel hn)

end TwoRank

variable {G : Type} [Group G] [Finite G]

theorem eq_of_pRank_one {K : Subgroup G} (hr : pRank 2 ↥K = 1) {a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a * b = b * a) : a = b := by
  by_contra hne
  have h := two_le_pRank_of_pair (mul_self_eq_one_of_orderOf_eq_two ha2)
    (mul_self_eq_one_of_orderOf_eq_two hb2) hab (ne_one_of_orderOf_eq_two ha2)
    (ne_one_of_orderOf_eq_two hb2) hne ha hb
  rw [← TwoThin.pRank_two_subgroup_eq_open K, hr] at h
  omega

namespace IsIntrinsic

variable {t : G} {K : Subgroup G}

omit [Finite G] in
theorem le_centralizer (h : IsIntrinsic t K) : K ≤ centralizer ({t} : Set G) := h.1.1

omit [Finite G] in
theorem comm_of_mem (h : IsIntrinsic t K) {k : G} (hk : k ∈ K) : k * t = t * k := by
  have := mem_centralizer_iff.mp (h.1.1 hk) t (Set.mem_singleton t)
  exact this.symm

theorem eq_of_involution (h : IsIntrinsic t K) (ht : orderOf t = 2) {i : G} (hi : i ∈ K)
    (hi2 : orderOf i = 2) : i = t :=
  eq_of_pRank_one h.2.1 hi h.2.2 hi2 ht (h.comm_of_mem hi)

theorem mem_zpowers_of_isPGroup (h : IsIntrinsic t K) (ht : orderOf t = 2) {s : G} (hs : s ∈ K)
    (hs2 : IsPGroup 2 ↥(zpowers s)) (hs1 : s ≠ 1) : t ∈ zpowers s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hs2) ⟨s, Subgroup.mem_zpowers s⟩
  have hk' : orderOf s = 2 ^ k := by simpa using hk
  have hk1 : k ≠ 0 := by
    rintro rfl
    simp at hk'
    exact hs1 hk'
  have h2 : 2 ∣ orderOf s := by
    rw [hk']
    exact dvd_pow_self 2 hk1
  have hpos : orderOf s ≠ 0 := (orderOf_pos s).ne'
  have hord : orderOf (s ^ (orderOf s / 2)) = 2 := orderOf_pow_orderOf_div hpos h2
  have hmem : s ^ (orderOf s / 2) ∈ K := pow_mem hs _
  have := h.eq_of_involution ht hmem hord
  rw [← this]
  exact pow_mem (Subgroup.mem_zpowers s) _

theorem normalizer_le_centralizer (h : IsIntrinsic t K) (ht : orderOf t = 2) :
    normalizer (K : Set G) ≤ centralizer ({t} : Set G) := by
  intro n hn
  have h1 : n * t * n⁻¹ ∈ K := (mem_normalizer_iff.mp hn t).mp h.2.2
  have h2 : orderOf (n * t * n⁻¹) = 2 := by rw [orderOf_conj_eq]; exact ht
  have h3 := h.eq_of_involution ht h1 h2
  rw [mem_centralizer_singleton_iff]
  calc n * t = n * t * n⁻¹ * n := by group
    _ = t * n := by rw [h3]

theorem mem_sylow (h : IsIntrinsic t K) (ht : orderOf t = 2) {S : Subgroup G}
    (hS : IsSylow2In S K) : t ∈ S :=
  mem_of_isSylow2In_of_central hS h.2.2 (fun _ hk => (h.comm_of_mem hk).symm)
    (mul_self_eq_one_of_orderOf_eq_two ht)

end IsIntrinsic

end CFSG.GH74.GLS.Stage1.Thm2.Recip
