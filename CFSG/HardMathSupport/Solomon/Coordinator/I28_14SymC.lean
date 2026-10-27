module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SymModel
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SymPerm
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal CFSG.Open

theorem i28_14_isElemAbelian_map {G G' : Type*} [Group G] [Group G'] (f : G →* G') {p : ℕ}
    {B : Subgroup G} (hB : IsElemAbelian p B) : IsElemAbelian p (B.map f) :=
  CFSG.Open.IsElemAbelian.map hB _

theorem i28_14_isElemAbelian_comap {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) {p : ℕ} {A : Subgroup G'} (hA : IsElemAbelian p A) :
    IsElemAbelian p (A.comap f) := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    refine Subtype.ext (hf ?_)
    have := congrArg Subtype.val (hA.1.is_comm.comm (⟨f x, hx⟩ : A) ⟨f y, hy⟩)
    simpa [map_mul] using this
  · intro x hx
    apply hf
    rw [map_pow, map_one]
    exact hA.2 _ hx

theorem i28_14_exists_perm_two {α : Type*} [DecidableEq α] {i j u v : α} (hij : i ≠ j)
    (huv : u ≠ v) : ∃ y : Equiv.Perm α, y i = u ∧ y j = v := by
  have hj : Equiv.swap i u j ≠ u := fun h => by
    apply hij
    have := Equiv.swap_apply_left i u
    exact (Equiv.swap i u).injective (h.trans this.symm) |>.symm
  refine ⟨Equiv.swap (Equiv.swap i u j) v * Equiv.swap i u, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hj.symm huv]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

variable {m : ℕ} {H : Type} [AddCommGroup H] [Module (ZMod 2) H] (M : SymModel m H)

theorem i28_14_symModel_C (hm : 5 ≤ m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) H)}
    (hA : IsMaxElemAbelianIn (U := H) p M.ψ.range A)
    {t : LinearMap.GeneralLinearGroup (ZMod 2) H} (htG : t ∈ M.ψ.range)
    (ht : IsF2Transvection t) : HasCentralizedConj (U := H) p M.ψ.range A t := by
  obtain ⟨hAle, hAab, hAmax⟩ := hA
  by_cases hsmall : Nat.card A ≤ p
  · refine ⟨1, one_mem _, ⊥, bot_le, ?_, fun e he => ?_⟩
    · rw [Subgroup.card_bot, mul_one]
      exact hsmall
    · rw [Subgroup.mem_bot.mp he]
      simp
  push Not at hsmall
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p A := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hAab.2 g g.2)⟩
  have : Finite M.ψ.range := Finite.of_surjective M.ψ.rangeRestrict M.ψ.rangeRestrict_surjective
  have : Finite A := Finite.of_injective (Subgroup.inclusion hAle)
    (Subgroup.inclusion_injective hAle)
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  have hA2 : p ^ 2 ≤ Nat.card A := by
    rw [hk] at hsmall ⊢
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k ≤ 1 := by omega
      have := Nat.pow_le_pow_right hp.pos this
      rw [pow_one] at this
      omega
    exact Nat.pow_le_pow_right hp.pos hk2
  set A' : Subgroup (Equiv.Perm (Fin m)) := A.comap M.ψ with hA'
  have hmap : A'.map M.ψ = A := Subgroup.map_comap_eq_self hAle
  have hcardA' : Nat.card A' = Nat.card A := by
    have := Subgroup.card_map_of_injective (K := A') M.inj
    rw [hmap] at this
    exact this.symm
  have hA'ab : IsElemAbelian p A' := i28_14_isElemAbelian_comap M.inj hAab
  have hmax' : ∀ B : Subgroup (Equiv.Perm (Fin m)), IsElemAbelian p B →
      Nat.card B ≤ Nat.card A' := by
    intro B hB
    rw [hcardA', ← Subgroup.card_map_of_injective M.inj (K := B)]
    exact hAmax _ (Subgroup.map_le_range M.ψ B) (i28_14_isElemAbelian_map M.ψ hB)
  obtain ⟨i, j, hij, E', hE'le, hE'card, hE'fix⟩ :=
    i28_14_symPerm_fixTwo hp hp2 hA'ab hmax' (by rw [hcardA']; exact hA2)
  obtain ⟨σ₀, rfl⟩ := htG
  obtain ⟨u, v, huv, rfl⟩ := i28_14_symModel_swap_of_transv M hm ht
  obtain ⟨y', hy'i, hy'j⟩ := i28_14_exists_perm_two (α := Fin m) hij huv
  have hconj : y'⁻¹ * Equiv.swap u v * y' = Equiv.swap i j := by
    rw [← hy'i, ← hy'j, Equiv.swap_apply_apply]
    group
  refine ⟨M.ψ y', ⟨y', rfl⟩, E'.map M.ψ, ?_, ?_, ?_⟩
  · exact Subgroup.map_le_iff_le_comap.mpr hE'le
  · rw [Subgroup.card_map_of_injective M.inj, ← hcardA']
    exact hE'card
  · rintro _ ⟨e', he', rfl⟩
    have hy : (M.ψ y')⁻¹ * M.ψ (Equiv.swap u v) * M.ψ y' = M.ψ (Equiv.swap i j) := by
      rw [← hconj, map_mul, map_mul, map_inv]
    rw [hy, ← map_mul, ← map_mul]
    congr 1
    obtain ⟨hi, hj⟩ := hE'fix e' he'
    have := Equiv.swap_apply_apply e' i j
    rw [hi, hj] at this
    calc e' * Equiv.swap i j = (e' * Equiv.swap i j * e'⁻¹) * e' := by group
      _ = Equiv.swap i j * e' := by rw [← this]

end CFSG.HardMathSupport.Solomon.Coordinator
