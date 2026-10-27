module

public import CFSG.CGT.PushingUpLit.LIT.FooteSimple
public import CFSG.CGT.PushingUpLit.BlocksCommute
public import CFSG.CGT.PushingUpLit.SolK.ThreeBlock
public import CFSG.CGT.PushingUp.TwoLocals

public section

namespace CFSG.CGT.PushingUpLit.A4

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open scoped commutatorElement

section ConjSub

variable {G : Type} [Group G]

theorem conjSub_conjSub (g h : G) (H : Subgroup G) :
    conjSub g (conjSub h H) = conjSub (g * h) H := by
  ext z
  simp only [mem_conjSub_iff]
  have e : (g * h)⁻¹ * z * (g * h) = h⁻¹ * (g⁻¹ * z * g) * h := by group
  rw [e]

theorem conjSub_inv_self (g : G) (H : Subgroup G) : conjSub g (conjSub g⁻¹ H) = H := by
  rw [conjSub_conjSub, mul_inv_cancel, conjSub_one]

theorem conjSub_eq_self_of_mem {m : G} {M : Subgroup G} (hm : m ∈ M) : conjSub m M = M := by
  ext z
  rw [mem_conjSub_iff]
  constructor
  · intro h
    have := M.mul_mem (M.mul_mem hm h) (M.inv_mem hm)
    simpa [mul_assoc] using this
  · intro h
    exact M.mul_mem (M.mul_mem (M.inv_mem hm) h) hm

end ConjSub

structure A4Cfg (G : Type) [Group G] [Finite G] (M X : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  charTwo : IsCharTwoType G
  maxLocal : IsMaximalTwoLocal M
  le : X ≤ M
  subnormal : (X.subgroupOf M).IsSubnormal
  short : IsShortGroup ↥X
  nat : IsNaturalAltModule ↥X 1
  unique : maximalTwoLocalsContaining (X : Set G) = {M}

namespace A4Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (c : A4Cfg G M X)
include c

theorem ne_top : M ≠ ⊤ := by
  have := c.simple
  exact ne_top_of_isMaximalTwoLocal_of_isShortGroup (X := X) c.maxLocal c.short

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
    (hX : conjSub m X ≤ M') : M' = M := by
  have hconj : IsMaximalTwoLocal (conjSub m⁻¹ M') := isMaximalTwoLocal_map_conj hM' m⁻¹
  have hXle : (X : Set G) ⊆ (conjSub m⁻¹ M' : Subgroup G) := by
    intro x hx
    rw [SetLike.mem_coe, mem_conjSub_iff]
    have h1 := hX (conj_mem_conjSub (g := m) hx)
    simpa using h1
  have hmem : conjSub m⁻¹ M' ∈ maximalTwoLocalsContaining (X : Set G) := ⟨hconj, hXle⟩
  rw [c.unique, Set.mem_singleton_iff] at hmem
  calc M' = conjSub m (conjSub m⁻¹ M') := (conjSub_inv_self m M').symm
    _ = conjSub m M := by rw [hmem]
    _ = M := conjSub_eq_self_of_mem hm

theorem mem_of_conj_le {g : G} (hg : conjSub g X ≤ M) : g ∈ M := by
  have hconj : IsMaximalTwoLocal (conjSub g⁻¹ M) := isMaximalTwoLocal_map_conj c.maxLocal g⁻¹
  have hXle : (X : Set G) ⊆ (conjSub g⁻¹ M : Subgroup G) := by
    intro x hx
    rw [SetLike.mem_coe, mem_conjSub_iff]
    have h1 := hg (conj_mem_conjSub (g := g) hx)
    simpa using h1
  have hmem : conjSub g⁻¹ M ∈ maximalTwoLocalsContaining (X : Set G) := ⟨hconj, hXle⟩
  rw [c.unique, Set.mem_singleton_iff] at hmem
  have h2 : conjSub g⁻¹ M = conjSub 1 M := hmem.trans (conjSub_one M).symm
  have hN := mem_normalizer_of_conjSub_eq h2
  rw [c.normalizer_eq] at hN
  simpa using M.inv_mem hN

theorem twoLocal_le {H : Subgroup G} (hH : IsPLocal 2 H) {m : G} (hm : m ∈ M)
    (hX : conjSub m X ≤ H) : H ≤ M := by
  obtain ⟨M', hHM', hM'⟩ := exists_isMaximalTwoLocal_ge hH
  exact (c.maxLocal_eq hM' hm (hX.trans hHM')) ▸ hHM'

theorem normalizer_le {A : Subgroup G} (hA : IsPGroup 2 A) (hA1 : A ≠ ⊥) {m : G} (hm : m ∈ M)
    (hX : conjSub m X ≤ Subgroup.normalizer (A : Set G)) :
    Subgroup.normalizer (A : Set G) ≤ M :=
  c.twoLocal_le (isPLocal_normalizer_of_isPGroup hA hA1) hm hX

theorem conj_le {m : G} (hm : m ∈ M) : conjSub m X ≤ M := by
  intro z hz
  rw [mem_conjSub_iff] at hz
  have := M.mul_mem (M.mul_mem hm (c.le hz)) (M.inv_mem hm)
  simpa [mul_assoc] using this

theorem subnormal_conj {m : G} (hm : m ∈ M) : ((conjSub m X).subgroupOf M).IsSubnormal := by
  have h : ((X.subgroupOf M).map (MulAut.conj (⟨m, hm⟩ : ↥M)).toMonoidHom).IsSubnormal :=
    c.subnormal.map (MulAut.conj _).surjective
  have heq : (X.subgroupOf M).map (MulAut.conj (⟨m, hm⟩ : ↥M)).toMonoidHom =
      (conjSub m X).subgroupOf M := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      mem_conjSub_iff, MulAut.conj_symm_apply]
    simp
  rwa [heq] at h

theorem short_conj (g : G) : IsShortGroup ↥(conjSub g X) :=
  isShortGroup_of_mulEquiv ((MulAut.conj g).subgroupMap X) c.short

theorem card_top : Nat.card (↥X ⧸ pCore 2 ↥X) = 3 := by
  obtain ⟨φ, -⟩ := c.nat
  have h3 : Nat.card (alternatingGroup (Fin (2 * 1 + 1))) = 3 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [Nat.card_congr φ.toEquiv, h3]

theorem commutator_conj_eq_bot {m : G} (hm : m ∈ M) (hne : conjSub m X ≠ X) :
    ⁅X, conjSub m X⁆ = ⊥ :=
  distinct_blocks_commute_rel c.isCharacteristicP c.le (c.conj_le hm) c.subnormal
    (c.subnormal_conj hm) c.short (c.short_conj m) hne.symm fun _ _ =>
      (card_top_conjSub X m).symm

theorem exists_order_three :
    ∃ a ∈ X, a ^ 3 = 1 ∧
      (∀ x ∈ X, ∃ y ∈ pCoreOf 2 X, ∃ j : ℕ, x = y * a ^ j) ∧
      (∀ y ∈ pCoreOf 2 X, ∀ y' ∈ pCoreOf 2 X, y * y' = y' * y) ∧
      (∀ y ∈ pCoreOf 2 X, y * y = 1) ∧
      Nat.card ↥(pCoreOf 2 X) = 4 ∧
      (∀ y ∈ pCoreOf 2 X, a * y * a⁻¹ = y → y = 1) :=
  SolK.three_block_ambient c.short c.nat

end A4Cfg

end CFSG.CGT.PushingUpLit.A4
