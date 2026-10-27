module

public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
import CFSG.GroupTheory.ChiefFactors.OddElement

public section

namespace CFSG.GroupTheory

open CFSG.RankThree.GroupTheory.SteinbergBY
open scoped commutatorElement

theorem le_inSubgroup_pCore_sup_centralizer {G : Type*} [Group G] [Finite G] {X T L : Subgroup G}
    [X.Normal] (hTR : T ≤ inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set G)))
    (hirr : ∀ Y : Subgroup G, T ≤ Y →
      Y ≤ inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set G)) →
      X ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (Y : Set G) →
      Y = T ∨ Y = inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set G)))
    (hS2 : ∀ l ∈ Subgroup.centralizer (T : Set G),
      (∀ b ∈ inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set G)), ⁅l, b⁆ ∈ T) →
      l ∈ inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set G)) ⊔
        Subgroup.centralizer (X : Set G))
    (hL : IsPGroup 2 L) (hLT : L ≤ Subgroup.centralizer (T : Set G))
    (hNL : X ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    L ≤ inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set G)) ⊔
      Subgroup.centralizer (X : Set G) := by
  set N₀ : Subgroup G := X ⊓ Subgroup.normalizer (T : Set G) with hN₀
  set R : Subgroup G := inSubgroup (pCore 2) N₀ with hR
  have hCN : Subgroup.centralizer (T : Set G) ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.centralizer_le_normalizer (T : Set G)
  have hLR : L ≤ Subgroup.normalizer (R : Set G) := fun l hl =>
    normalizer_le_normalizer_inSubgroup_pCore 2 N₀
      (mem_normalizer_inf
        ((Subgroup.le_normalizer_of_normal : L ≤ Subgroup.normalizer (X : Set G)) hl)
        (Subgroup.le_normalizer (hCN (hLT hl))))
  intro l hl
  refine hS2 l (hLT hl) fun b hb => ?_
  rcases eq_or_ne R T with hRT | hRT
  · have hbT : b ∈ T := by
      have hbR : b ∈ R := hb
      rw [hRT] at hbR
      exact hbR
    rw [commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_centralizer_iff.1 (hLT hl) b hbT).symm]
    exact T.one_mem
  · have h1 := commutator_mem_of_chief (N := N₀ ⊔ L) hL le_sup_right
      (sup_le hNL Subgroup.le_normalizer)
      (isPGroup_inSubgroup_pCore 2 N₀)
      (lt_of_le_of_ne hTR (Ne.symm hRT))
      (sup_le (le_normalizer_inSubgroup_pCore 2 N₀) hLR)
      (sup_le inf_le_right (hLT.trans hCN))
      ((inSubgroup_pCore_le 2 N₀).trans inf_le_right)
      (fun Y h1 h2 h3 => hirr Y h1 h2 (le_sup_left.trans h3)) l hl b hb
    rwa [commutatorElement_def]

end CFSG.GroupTheory
