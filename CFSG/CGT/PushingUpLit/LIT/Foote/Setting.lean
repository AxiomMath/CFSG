module

public import CFSG.CGT.PushingUpLit.LIT.FooteSimple
public import CFSG.CGT.PushingUpLit.LIT.Foote.TightAux

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

structure CE (G : Type) [Group G] [Finite G] (M J : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  charTwo : IsCharTwoType G
  maxLocal : IsMaximalTwoLocal M
  le : J ≤ M
  subnormal : (J.subgroupOf M).IsSubnormal
  block : QBlock J
  unique : maximalTwoLocalsContaining (J : Set G) = {M}
  notNormal : ¬ (J.subgroupOf M).Normal

section Top

variable {G : Type} [Group G] [Finite G]

theorem QBlock.top_not_prime {K : Subgroup G} (hK : QBlock K) :
    ¬ (Nat.card (↥K ⧸ pCore 2 ↥K)).Prime := by
  intro hp
  have : Fact (Nat.card (↥K ⧸ pCore 2 ↥K)).Prime := ⟨hp⟩
  have : IsCyclic (↥K ⧸ pCore 2 ↥K) := isCyclic_of_prime_card rfl
  obtain ⟨-, -, a, b, hab⟩ := hK.quasisimple
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥K ⧸ pCore 2 ↥K)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg y)
  exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    (Commute.zpow_zpow_self g i j).eq])

end Top

namespace CE

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} (c : CE G M J)
include c

theorem ne_top : M ≠ ⊤ := by
  have := c.simple
  exact ne_top_of_isMaximalTwoLocal_of_isShortGroup (X := J) c.maxLocal c.block.short

theorem isPLocal : IsPLocal 2 M := c.maxLocal.1

theorem oTwoIn_ne_bot : oTwoIn M ≠ ⊥ := by
  intro h
  apply pCore_ne_bot_of_isPLocal c.isPLocal
  have := Subgroup.map_eq_bot_iff_of_injective (pCore 2 ↥M) M.subtype_injective
  exact this.1 h

theorem isCharacteristicP : IsCharacteristicP 2 ↥M :=
  isCharacteristicP_of_isPLocal c.charTwo c.isPLocal

theorem normalizer_eq : Subgroup.normalizer (M : Set G) = M := by
  have hlocal : IsPLocal 2 (Subgroup.normalizer (oTwoIn M : Set G)) :=
    isPLocal_normalizer_of_isPGroup (isPGroup_oTwoIn M) c.oTwoIn_ne_bot
  have hMH : M ≤ Subgroup.normalizer (oTwoIn M : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoIn M)
  have hHM : Subgroup.normalizer (oTwoIn M : Set G) ≤ M := by
    by_contra hnot
    exact c.maxLocal.2 _ (lt_of_le_of_ne hMH fun h => hnot (h ▸ le_rfl)) hlocal
  exact le_antisymm ((normalizer_le_normalizer_oTwoIn M).trans hHM) Subgroup.le_normalizer

theorem maxLocal_eq {M' : Subgroup G} (hM' : IsMaximalTwoLocal M') {m : G} (hm : m ∈ M)
    (hJ : rightConjugate J m ≤ M') : M' = M := by
  have hconj : IsMaximalTwoLocal (rightConjugate M' m⁻¹) := by
    have := isMaximalTwoLocal_map_conj hM' m
    simpa [rightConjugate] using this
  have hJle : (J : Set G) ⊆ (rightConjugate M' m⁻¹ : Subgroup G) := by
    intro x hx
    rw [SetLike.mem_coe, mem_rightConjugate_iff]
    apply hJ
    rw [mem_rightConjugate_iff]
    have e : m * (m⁻¹ * x * m⁻¹⁻¹) * m⁻¹ = x := by group
    rw [e]
    exact hx
  have hmem : rightConjugate M' m⁻¹ ∈ maximalTwoLocalsContaining (J : Set G) := ⟨hconj, hJle⟩
  rw [c.unique, Set.mem_singleton_iff] at hmem
  have hM : rightConjugate M m = M :=
    (rightConjugate_eq_self_iff M m).2 (Subgroup.le_normalizer hm)
  calc M' = rightConjugate (rightConjugate M' m⁻¹) m := by
        rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
    _ = M := by rw [hmem, hM]

theorem mem_of_conj_le {x : G} (hx : rightConjugate J x ≤ M) : x ∈ M := by
  have hconj : IsMaximalTwoLocal (rightConjugate M x⁻¹) := by
    have := isMaximalTwoLocal_map_conj c.maxLocal x
    simpa [rightConjugate] using this
  have hJle : (J : Set G) ⊆ (rightConjugate M x⁻¹ : Subgroup G) := by
    intro y hy
    rw [SetLike.mem_coe, mem_rightConjugate_iff]
    apply hx
    rw [mem_rightConjugate_iff]
    have e : x * (x⁻¹ * y * x⁻¹⁻¹) * x⁻¹ = y := by group
    rw [e]
    exact hy
  have hmem : rightConjugate M x⁻¹ ∈ maximalTwoLocalsContaining (J : Set G) := ⟨hconj, hJle⟩
  rw [c.unique, Set.mem_singleton_iff] at hmem
  have hN : x⁻¹ ∈ Subgroup.normalizer (M : Set G) := (rightConjugate_eq_self_iff M x⁻¹).1 hmem
  rw [c.normalizer_eq] at hN
  simpa using M.inv_mem hN

theorem twoLocal_le {H : Subgroup G} (hH : IsPLocal 2 H) {m : G} (hm : m ∈ M)
    (hJ : rightConjugate J m ≤ H) : H ≤ M := by
  obtain ⟨M', hHM', hM'⟩ := exists_isMaximalTwoLocal_ge hH
  exact (c.maxLocal_eq hM' hm (hJ.trans hHM')) ▸ hHM'

theorem normalizer_le {A : Subgroup G} (hA : IsPGroup 2 A) (hA1 : A ≠ ⊥) {m : G} (hm : m ∈ M)
    (hJ : rightConjugate J m ≤ Subgroup.normalizer (A : Set G)) :
    Subgroup.normalizer (A : Set G) ≤ M :=
  c.twoLocal_le (isPLocal_normalizer_of_isPGroup hA hA1) hm hJ

theorem conj_le {m : G} (hm : m ∈ M) : rightConjugate J m ≤ M := by
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  have := M.mul_mem (M.mul_mem (M.inv_mem hm) (c.le hx)) hm
  simpa [mul_assoc] using this

theorem subnormal_conj {m : G} (hm : m ∈ M) : ((rightConjugate J m).subgroupOf M).IsSubnormal := by
  have h : ((J.subgroupOf M).map (MulAut.conj (⟨m, hm⟩ : ↥M)⁻¹).toMonoidHom).IsSubnormal :=
    c.subnormal.map (MulAut.conj _).surjective
  have heq : (J.subgroupOf M).map (MulAut.conj (⟨m, hm⟩ : ↥M)⁻¹).toMonoidHom =
      (rightConjugate J m).subgroupOf M := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      mem_rightConjugate_iff]
    simp
  rwa [heq] at h

theorem exists_conj_ne : ∃ m ∈ M, rightConjugate J m ≠ J := by
  by_contra hall
  push Not at hall
  apply c.notNormal
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer c.le]
  intro m hm
  exact (rightConjugate_eq_self_iff J m).1 (hall m hm)

theorem commutator_conj_eq_bot {m : G} (hm : m ∈ M) (hne : rightConjugate J m ≠ J) :
    ⁅J, rightConjugate J m⁆ = ⊥ :=
  distinct_blocks_commute_rel c.isCharacteristicP c.le (c.conj_le hm) c.subnormal
    (c.subnormal_conj hm) c.block.short (c.block.conj m).short hne.symm fun hp _ =>
      (c.block.top_not_prime hp).elim

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
