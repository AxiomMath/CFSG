module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Lemma36
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.General
import CFSG.GroupTheory.OddOverlap

public section

namespace CFSG.EvenSporadicStandard.Induction.Closing

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78

theorem eq_of_orderOf_eq_two_of_cyclic {X : Type} [Group X] [Finite X] {U : Subgroup X}
    (hU : IsCyclic U) {a b : X} (ha : a ∈ U) (hb : b ∈ U) (ha2 : orderOf a = 2)
    (hb2 : orderOf b = 2) : a = b := by
  have ha' : orderOf (⟨a, ha⟩ : U) = 2 := by rw [Subgroup.orderOf_mk, ha2]
  have hb' : orderOf (⟨b, hb⟩ : U) = 2 := by rw [Subgroup.orderOf_mk, hb2]
  have heq : Subgroup.zpowers (⟨a, ha⟩ : U) = Subgroup.zpowers ⟨b, hb⟩ :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, ha', hb'])
  have hmem : (⟨a, ha⟩ : U) ∈ Subgroup.zpowers ⟨b, hb⟩ := heq ▸ Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  rcases zpow_eq_one_or_self_of_orderOf_eq_two hb' k with h1 | h1
  · rw [h1] at hk
    rw [← hk, orderOf_one] at ha'
    omega
  · rw [h1] at hk
    exact congrArg Subtype.val hk.symm

section Generic

variable {H : Type} [Group H] [Finite H] {L : Subgroup H}

omit [Finite H] in
theorem conj_mem_centralizer {m x : H} (hm : m ∈ normalizer (L : Set H))
    (hx : x ∈ centralizer (L : Set H)) : m * x * m⁻¹ ∈ centralizer (L : Set H) := by
  refine mem_centralizer_iff.2 fun l hl => ?_
  have h1 : m⁻¹ * l * m ∈ L := by
    have := (mem_normalizer_iff.1 hm (m⁻¹ * l * m)).2 (by
      have e : m * (m⁻¹ * l * m) * m⁻¹ = l := by group
      rw [e]; exact hl)
    exact this
  have h2 := mem_centralizer_iff.1 hx _ h1
  calc l * (m * x * m⁻¹) = m * ((m⁻¹ * l * m) * x) * m⁻¹ := by group
    _ = m * (x * (m⁻¹ * l * m)) * m⁻¹ := by rw [h2]
    _ = m * x * m⁻¹ * l := by group

omit [Finite H] in
theorem centralizer_le_normalizer_of_stdBare (hstd : StdBare L) {x : H}
    (hx : x ∈ centralizer (L : Set H)) (hx2 : orderOf x = 2) :
    centralizer ({x} : Set H) ≤ normalizer (L : Set H) := fun _ hg =>
  StandardSubgroupAPI.mem_of_odd_inf_map_conj_of_commute hstd.2 hx hx2
    (mem_centralizer_singleton_iff.1 hg)

theorem eq_one_or_eq_of_commute
    (hS : ∃ S : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥S) {t x : H}
    (ht : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2)
    (hx : x ∈ centralizer (L : Set H)) (hxx : x * x = 1) (hxt : x * t = t * x) :
    x = 1 ∨ x = t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  right
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rwa [pow_two]) hx1
  set C : Subgroup H := centralizer (L : Set H) with hC
  let a : C := ⟨x, hx⟩
  let b : C := ⟨t, ht⟩
  have ha2 : orderOf a = 2 := by rw [Subgroup.orderOf_mk]; exact hx2
  have hb2 : orderOf b = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  have hab : a * b = b * a := Subtype.ext hxt
  have haa : a * a = 1 := Subtype.ext hxx
  have hbb : b * b = 1 := Subtype.ext (mul_self_eq_one_of_orderOf_eq_two ht2)
  have hle : zpowers b ≤ centralizer ((zpowers a : Subgroup C) : Set C) := by
    rw [zpowers_le]
    refine mem_centralizer_iff.2 fun g hg => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    exact (Commute.zpow_left (show Commute a b from hab) k).eq
  have hE : IsPGroup 2 (zpowers a ⊔ zpowers b : Subgroup C) := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨y, hy⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hy₁
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy₂
    have h1 : (a ^ i * b ^ j) * (a ^ i * b ^ j) = 1 := by
      have hc : Commute (b ^ j) (a ^ i) :=
        (Commute.zpow_zpow (show Commute b a from hab.symm) j i)
      calc (a ^ i * b ^ j) * (a ^ i * b ^ j) = a ^ i * (b ^ j * a ^ i) * b ^ j := by group
        _ = a ^ i * (a ^ i * b ^ j) * b ^ j := by rw [hc.eq]
        _ = (a ^ i * a ^ i) * (b ^ j * b ^ j) := by group
        _ = 1 := by
          have e1 : a ^ i * a ^ i = 1 := by
            rcases zpow_eq_one_or_self_of_orderOf_eq_two ha2 i with h | h <;> rw [h]
            · exact mul_one 1
            · exact haa
          have e2 : b ^ j * b ^ j = 1 := by
            rcases zpow_eq_one_or_self_of_orderOf_eq_two hb2 j with h | h <;> rw [h]
            · exact mul_one 1
            · exact hbb
          rw [e1, e2, mul_one]
    have h2 : orderOf (⟨a ^ i * b ^ j, hy⟩ : ↥(zpowers a ⊔ zpowers b)) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_two]
      exact Subtype.ext h1
    have h3 : orderOf (⟨a ^ i * b ^ j, hy⟩ : ↥(zpowers a ⊔ zpowers b)) ∣ 2 ^ 1 := by
      simpa using h2
    obtain ⟨k, -, hk2⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h3
    exact ⟨k, hk2⟩
  obtain ⟨S', hS'⟩ := hE.exists_le_sylow
  obtain ⟨S₀, hS₀⟩ := hS
  have hcyc : IsCyclic ↥S' := by
    let f : S₀ ≃* S' := Sylow.equiv S₀ S'
    exact isCyclic_of_surjective f.toMonoidHom f.surjective
  have haS : a ∈ (S' : Subgroup C) := hS' (Subgroup.mem_sup_left (mem_zpowers a))
  have hbS : b ∈ (S' : Subgroup C) := hS' (Subgroup.mem_sup_right (mem_zpowers b))
  have := eq_of_orderOf_eq_two_of_cyclic hcyc haS hbS ha2 hb2
  exact congrArg Subtype.val this

theorem not_mem_of_odd_center (hodd : Odd (Nat.card ↥(center ↥L))) {x : H}
    (hxC : x ∈ centralizer (L : Set H)) (hx2 : orderOf x = 2) : x ∉ L := fun hxL =>
  not_odd_card_center_of_mem hxL hx2 (fun y hy => (mem_centralizer_iff.1 hxC y hy)) hodd

end Generic

structure ClosingSetup (H : Type) [Group H] [Finite H] (N L : Subgroup H) (t u : H) : Prop where
  fstar : FStarSimple N
  quasisimple : CFSG.IsQuasisimple ↥L
  centre_odd : Odd (Nat.card ↥(center ↥L))
  stdBare : StdBare L
  cyclicSylow : ∃ S : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥S
  t_order : orderOf t = 2
  t_mem : t ∈ centralizer (L : Set H)
  u_order : orderOf u = 2
  u_mem : u ∈ L
  u_comm_t : u * t = t * u
  hyp38 : centralizer ({u} : Set H) ≤ normalizer (L : Set H)

namespace ClosingSetup

variable {H : Type} [Group H] [Finite H] {N L K : Subgroup H} {t u : H}

theorem of_hypQ (h : SolomonHypQ H N L K t u) (huL : u ∈ L) : ClosingSetup H N L t u where
  fstar := h.fstar
  quasisimple := h.quasisimpleL
  centre_odd := h.centre_odd
  stdBare := h.standardL.stdBare
  cyclicSylow := h.cyclicSylow
  t_order := h.t_order
  t_mem := h.t_mem
  u_order := h.u_order
  u_mem := huL
  u_comm_t := h.u_comm_t
  hyp38 := h.hyp38_2

variable (S : ClosingSetup H N L t u)
include S

theorem t_mul_self : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two S.t_order

theorem u_mul_self : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two S.u_order

theorem perfect : commutator ↥L = ⊤ := Group.isPerfect_def.1 S.quasisimple.1

theorem t_not_mem : t ∉ L := not_mem_of_odd_center S.centre_odd S.t_mem S.t_order

theorem centralizer_t_le : centralizer ({t} : Set H) ≤ normalizer (L : Set H) :=
  centralizer_le_normalizer_of_stdBare S.stdBare S.t_mem S.t_order

theorem eq_one_or_eq_t {x : H} (hx : x ∈ centralizer (L : Set H)) (hxx : x * x = 1)
    (hxt : x * t = t * x) : x = 1 ∨ x = t :=
  eq_one_or_eq_of_commute S.cyclicSylow S.t_mem S.t_order hx hxx hxt

theorem t_comm {l : H} (hl : l ∈ L) : l * t = t * l := mem_centralizer_iff.1 S.t_mem l hl

theorem u_not_central : (⟨u, S.u_mem⟩ : ↥L) ∉ center ↥L := fun hz =>
  not_odd_card_center_of_mem (M := L) S.u_mem S.u_order
    (fun x hx => congrArg Subtype.val (mem_center_iff.1 hz ⟨x, hx⟩)) S.centre_odd

end ClosingSetup

end CFSG.EvenSporadicStandard.Induction.Closing
