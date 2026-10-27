module

public import CFSG.LocalAnalysis.GH72.Sec4Basic

public section

namespace CFSG.GH72

open Subgroup
open CFSG.GorensteinWalter (twoResidualOf)

section Generic

variable {X : Type*} [Group X]

theorem mem_of_odd_of_index_eq_two_pow {N : Subgroup X} [N.Normal] {n : ℕ}
    (hN : N.index = 2 ^ n) {x : X} (hx : Odd (orderOf x)) : x ∈ N := by
  have h1 : orderOf (QuotientGroup.mk' N x) ∣ orderOf x := orderOf_map_dvd _ x
  have h2 : orderOf (QuotientGroup.mk' N x) ∣ 2 ^ n := by
    rw [← hN]
    exact orderOf_dvd_natCard _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  rcases j with _ | j
  · rw [pow_zero, orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hj
    exact hj
  · exfalso
    rw [hj] at h1
    exact (Nat.not_even_iff_odd.2 hx)
      (even_iff_two_dvd.2 ((dvd_pow_self 2 j.succ_ne_zero).trans h1))

theorem exists_odd_orderOf_pow [Finite X] (x : X) : ∃ k : ℕ, Odd (orderOf (x ^ 2 ^ k)) := by
  obtain ⟨k, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨k, ?_⟩
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hxm⟩, hxm,
    Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
  exact hm

theorem closure_odd_normal : (closure {x : X | Odd (orderOf x)}).Normal := by
  constructor
  intro n hn g
  have hmap : (closure {x : X | Odd (orderOf x)}).map (MulAut.conj g).toMonoidHom =
      closure {x : X | Odd (orderOf x)} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [orderOf_conj_eq]
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by group⟩
      have e : g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ := by rw [inv_inv]
      rwa [e, orderOf_conj_eq]
  have h : g * n * g⁻¹ ∈ (closure {x : X | Odd (orderOf x)}).map (MulAut.conj g).toMonoidHom :=
    ⟨n, hn, rfl⟩
  rwa [hmap] at h

theorem sInf_normal_two_pow_index_eq_closure [Finite X] :
    sInf {N : Subgroup X | N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n} =
      closure {x : X | Odd (orderOf x)} := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := closure_odd_normal (X := X)
  apply le_antisymm
  · refine sInf_le ⟨inferInstance, ?_⟩
    have h2 : IsPGroup 2 (X ⧸ closure {x : X | Odd (orderOf x)}) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk⟩ := exists_odd_orderOf_pow x
      exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact subset_closure hk⟩
    exact IsPGroup.iff_card.1 h2
  · rw [closure_le]
    intro x hx
    rw [SetLike.mem_coe, mem_sInf]
    rintro N ⟨hNn, n, hn⟩
    haveI := hNn
    exact mem_of_odd_of_index_eq_two_pow hn hx

theorem sInf_normal_two_pow_index_normal [Finite X] :
    (sInf {N : Subgroup X | N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n}).Normal := by
  rw [sInf_normal_two_pow_index_eq_closure]
  exact closure_odd_normal

end Generic

section Residual

variable {G : Type*} [Group G] [Finite G]

theorem twoResidualOf_eq_closure (H : Subgroup G) :
    twoResidualOf H = closure {x : G | x ∈ H ∧ Odd (orderOf x)} := by
  rw [twoResidualOf, sInf_normal_two_pow_index_eq_closure, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by rwa [Subgroup.orderOf_coe]⟩
  · rintro ⟨hx, hodd⟩
    exact ⟨⟨x, hx⟩, by rwa [Subgroup.orderOf_mk], rfl⟩

theorem twoResidualOf_top_eq_closure :
    twoResidualOf (⊤ : Subgroup G) = closure {x : G | Odd (orderOf x)} := by
  rw [twoResidualOf_eq_closure]
  simp only [mem_top, true_and]

theorem twoResidualOf_top_normal : (twoResidualOf (⊤ : Subgroup G)).Normal := by
  rw [twoResidualOf_top_eq_closure]
  exact closure_odd_normal

omit [Finite G] in
theorem twoResidualOf_le_self (H : Subgroup G) : twoResidualOf H ≤ H := map_subtype_le _

theorem mem_twoResidualOf_of_odd {H : Subgroup G} {x : G} (hx : x ∈ H)
    (hodd : Odd (orderOf x)) : x ∈ twoResidualOf H := by
  rw [twoResidualOf_eq_closure]
  exact subset_closure ⟨hx, hodd⟩

theorem twoResidualOf_le_of_forall {H L : Subgroup G}
    (h : ∀ x ∈ H, Odd (orderOf x) → x ∈ L) : twoResidualOf H ≤ L := by
  rw [twoResidualOf_eq_closure, closure_le]
  rintro x ⟨hx, hodd⟩
  exact h x hx hodd

theorem twoResidualOf_subgroupOf_normal (H : Subgroup G) :
    ((twoResidualOf H).subgroupOf H).Normal := by
  haveI := sInf_normal_two_pow_index_normal (X := ↥H)
  rw [twoResidualOf, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
  infer_instance

theorem le_normalizer_twoResidualOf (H : Subgroup G) :
    H ≤ normalizer (twoResidualOf H : Set G) := by
  haveI := sInf_normal_two_pow_index_normal (X := ↥H)
  exact CFSG.ABGLocalTools.le_normalizer_map_subtype H _

theorem exists_pow_mem_twoResidualOf {H : Subgroup G} {h : G} (hh : h ∈ H) :
    ∃ k : ℕ, h ^ 2 ^ k ∈ twoResidualOf H := by
  obtain ⟨k, hk⟩ := exists_odd_orderOf_pow h
  exact ⟨k, mem_twoResidualOf_of_odd (pow_mem hh _) hk⟩

theorem exists_relIndex_twoResidualOf (H : Subgroup G) :
    ∃ n : ℕ, (twoResidualOf H).relIndex H = 2 ^ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := twoResidualOf_subgroupOf_normal H
  have h2 : IsPGroup 2 (↥H ⧸ (twoResidualOf H).subgroupOf H) := by
    intro q
    obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_twoResidualOf hh
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]; exact hk⟩
  exact IsPGroup.iff_card.1 h2

theorem twoResidualOf_mono {H J : Subgroup G} (h : H ≤ J) : twoResidualOf H ≤ twoResidualOf J :=
  twoResidualOf_le_of_forall fun _ hx hodd => mem_twoResidualOf_of_odd (h hx) hodd

theorem twoResidualOf_twoResidualOf (H : Subgroup G) :
    twoResidualOf (twoResidualOf H) = twoResidualOf H :=
  le_antisymm (twoResidualOf_le_self _) (twoResidualOf_le_of_forall fun _ hx hodd =>
    mem_twoResidualOf_of_odd (mem_twoResidualOf_of_odd hx hodd) hodd)

theorem index_ne_two_of_twoResidualOf (H : Subgroup G) (N : Subgroup ↥(twoResidualOf H))
    (hN : N.Normal) : N.index ≠ 2 := by
  intro h2
  haveI := hN
  have hle : twoResidualOf (twoResidualOf H) ≤ N.map (twoResidualOf H).subtype := by
    apply twoResidualOf_le_of_forall
    intro x hx hodd
    exact ⟨⟨x, hx⟩, mem_of_odd_of_index_eq_two_pow (n := 1) (by rw [h2, pow_one])
      (by rwa [Subgroup.orderOf_mk]), rfl⟩
  rw [twoResidualOf_twoResidualOf] at hle
  have htop : N = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy⟩ := hle y.2
    have e : y' = y := Subtype.ext hyy
    rwa [← e]
  rw [htop, index_top] at h2
  exact absurd h2 (by norm_num)

theorem twoResidualOf_subgroupOf_eq_closure (H : Subgroup G) :
    (twoResidualOf H).subgroupOf H = closure {y : ↥H | Odd (orderOf y)} := by
  rw [twoResidualOf, sInf_normal_two_pow_index_eq_closure, subgroupOf,
    comap_map_eq_self_of_injective H.subtype_injective]

theorem bar_twoResidualOf (H : Subgroup G) :
    bar H (twoResidualOf H) = twoResidualOf (⊤ : Subgroup (Bar H)) := by
  rw [bar, twoResidualOf_subgroupOf_eq_closure, MonoidHom.map_closure,
    twoResidualOf_top_eq_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Odd.of_dvd_nat hx (orderOf_map_dvd _ x)
  · intro hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore H) y
    refine ⟨x, ?_, rfl⟩
    have h1 : x ^ orderOf (QuotientGroup.mk' (CFSG.oddCore H) x) ∈ CFSG.oddCore H := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, pow_orderOf_eq_one]
    have h2 : orderOf x ∣ orderOf (QuotientGroup.mk' (CFSG.oddCore H) x) *
        Nat.card (CFSG.oddCore H) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul]
      have h3 := pow_card_eq_one' (x := (⟨_, h1⟩ : CFSG.oddCore H))
      exact congrArg Subtype.val h3
    exact Odd.of_dvd_nat (Odd.mul hy CFSG.ABGLocalTools.odd_card_oddCore) h2

end Residual

end CFSG.GH72
