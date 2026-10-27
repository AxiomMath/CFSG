module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1Slim
public import CFSG.Monster.Existence.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterTransfer

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open CFSG.Monster.Existence CFSG.Blueprint

structure MonsterFacts (Y : Type) [Group Y] : Prop where
  simple : IsSimpleGroup Y
  nonabelian : ∃ a b : Y, a * b ≠ b * a
  card : Nat.card Y = monsterOrder
  twoA : ∀ u : Y, orderOf u = 2 → 2 * monsterBabyOrder ≤ Nat.card ↥(centralizer ({u} : Set Y)) →
    IsTwoACentralizer u ∧ Nat.card ↥(centralizer ({u} : Set Y)) = 2 * monsterBabyOrder ∧
      IsCoatom (centralizer ({u} : Set Y))
  allInner : AllInner Y
  baby_simple : IsSimpleGroup NativeSporadic.B
  baby_allInner : AllInner NativeSporadic.B

theorem outTwo_of_allInner {Y : Type} [Group Y] (h : AllInner Y) : OutTwo Y :=
  fun α _ => Or.inl (h α)

theorem exists_inner_of_mulEquiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (h : ∀ α : MulAut X', ∃ c : X', ∀ x : X', α x = c * x * c⁻¹) (α : MulAut X) :
    ∃ c : X, ∀ x : X, α x = c * x * c⁻¹ := by
  obtain ⟨c, hc⟩ := h (e.symm.trans (α.trans e))
  refine ⟨e.symm c, fun x => ?_⟩
  have := hc (e x)
  apply e.injective
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at this
  simpa using this

theorem allInner_of_quotient {C B : Type} [Group C] [Group B] (hperf : Group.IsPerfect C)
    (e : C ⧸ center C ≃* B) (hB : AllInner B) (α : MulAut C) :
    ∃ c : C, ∀ k, α k = c * k * c⁻¹ := by
  refine exists_inner_of_perfect_of_quotient_inner (fun β => ?_) α
  obtain ⟨x, hx⟩ := exists_inner_of_mulEquiv e (fun γ => by
    obtain ⟨g, hg⟩ := hB γ
    exact ⟨g, fun x => by rw [hg]; rfl⟩) β
  exact ⟨x, hx⟩

theorem factorization_two_monsterOrder : monsterOrder.factorization 2 = 46 := by
  have h : monsterOrder = 2 ^ 46 * (3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 *
      31 * 41 * 47 * 59 * 71) := by
    unfold monsterOrder
    ring
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_two_double_baby : (2 * monsterBabyOrder).factorization 2 = 42 := by
  have h : 2 * monsterBabyOrder = 2 ^ 42 * (3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 *
      47) := by
    unfold monsterBabyOrder
    ring
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

variable {G : Type} [Group G] [Finite G]

theorem m_pair_data {L K : Subgroup G} {u : G} (hM : MonsterFacts ↥L) (hu : u ∈ L)
    (hu2 : orderOf u = 2) (hKL : K ≤ L) (hKu : ∀ k ∈ K, k * u = u * k)
    (hcard : 2 * monsterBabyOrder ≤ Nat.card K) :
    K = L ⊓ centralizer ({u} : Set G) ∧
      K.subgroupOf L = centralizer ({(⟨u, hu⟩ : ↥L)} : Set ↥L) ∧
      IsTwoACentralizer (⟨u, hu⟩ : ↥L) ∧ IsCoatom (centralizer ({(⟨u, hu⟩ : ↥L)} : Set ↥L)) ∧
      Nat.card ↥(centralizer ({(⟨u, hu⟩ : ↥L)} : Set ↥L)) = 2 * monsterBabyOrder := by
  let u' : ↥L := ⟨u, hu⟩
  have hu'2 : orderOf u' = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have hKz : K.subgroupOf L ≤ centralizer ({u'} : Set ↥L) := fun k hk =>
    mem_centralizer_singleton_iff.2 (Subtype.ext (hKu k (mem_subgroupOf.1 hk)))
  have hKcard : Nat.card ↥(K.subgroupOf L) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv
  have hge : 2 * monsterBabyOrder ≤ Nat.card ↥(centralizer ({u'} : Set ↥L)) := by
    rw [← hKcard] at hcard
    exact hcard.trans (Subgroup.card_le_of_le hKz)
  obtain ⟨hA, hC, hcoat⟩ := hM.twoA u' hu'2 hge
  have hKeq' : K.subgroupOf L = centralizer ({u'} : Set ↥L) :=
    Subgroup.eq_of_le_of_card_ge hKz (by rw [hC, hKcard]; exact hcard)
  refine ⟨?_, hKeq', hA, hcoat, hC⟩
  ext x
  constructor
  · intro hx
    exact ⟨hKL hx, mem_centralizer_singleton_iff.2 (hKu x hx)⟩
  · rintro ⟨hxL, hxc⟩
    have : (⟨x, hxL⟩ : ↥L) ∈ centralizer ({u'} : Set ↥L) :=
      mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 hxc))
    rw [← hKeq'] at this
    exact mem_subgroupOf.1 this

end CFSG.EvenSporadicStandard.Solomon78
