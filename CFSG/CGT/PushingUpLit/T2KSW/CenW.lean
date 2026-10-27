module

public import CFSG.CGT.PushingUpLit.Defs

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.CGT.PushingUpLit
open scoped commutatorElement

variable {G : Type} [Group G] {L M : Subgroup G}

@[expose] def cenW (L M : Subgroup G) : Subgroup G := M ⊓ centralizerModCore L

theorem mem_cenW {x : G} : x ∈ cenW L M ↔
    x ∈ M ∧ x ∈ Subgroup.normalizer (L : Set G) ∧ ∀ l ∈ L, ⁅x, l⁆ ∈ oTwoIn L := Iff.rfl

theorem cenW_le : cenW L M ≤ M := inf_le_left

theorem cenW_le_normalizer : cenW L M ≤ Subgroup.normalizer (L : Set G) :=
  fun _ hx => (mem_cenW.1 hx).2.1

theorem mem_cenW_of_le (hMN : M ≤ Subgroup.normalizer (L : Set G)) {x : G} :
    x ∈ cenW L M ↔ x ∈ M ∧ ∀ l ∈ L, ⁅x, l⁆ ∈ oTwoIn L :=
  ⟨fun hx => ⟨(mem_cenW.1 hx).1, (mem_cenW.1 hx).2.2⟩,
    fun hx => mem_cenW.2 ⟨hx.1, hMN hx.1, hx.2⟩⟩

theorem conj_mem_cenW (hMN : M ≤ Subgroup.normalizer (L : Set G)) {m x : G} (hm : m ∈ M)
    (hx : x ∈ cenW L M) : m * x * m⁻¹ ∈ cenW L M := by
  obtain ⟨hxM, hxN, hxc⟩ := mem_cenW.1 hx
  refine mem_cenW.2 ⟨M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hMN hm) hxN) (Subgroup.inv_mem _ (hMN hm)),
    fun l hl => ?_⟩
  have hl' : m⁻¹ * l * m ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hMN hm)) l).1 hl
    simpa using this
  have e : ⁅m * x * m⁻¹, l⁆ = m * ⁅x, m⁻¹ * l * m⁆ * m⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact conj_mem_oTwoIn (hMN hm) (hxc _ hl')

theorem le_normalizer_cenW (hMN : M ≤ Subgroup.normalizer (L : Set G)) :
    M ≤ Subgroup.normalizer (cenW L M : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_cenW hMN hm hy, fun hy => ?_⟩
  have := conj_mem_cenW hMN (M.inv_mem hm) hy
  simpa [mul_assoc] using this

end CFSG.CGT.PushingUpLit.T2KSW
