module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5

open Subgroup CFSG
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem component_le_of_mem_normal_of_not_commute {A K L : Subgroup G} (hKA : K ≤ A)
    (hK : (K.subgroupOf A).Normal) (hLA : L ≤ A) (hL : IsComponent L) {t : G} (htK : t ∈ K)
    (hnc : ∃ l ∈ L, t * l ≠ l * t) : L ≤ K := by
  have hconj : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ ∈ K := by
    intro a ha k hk
    have := hK.conj_mem ⟨k, hKA hk⟩ (Subgroup.mem_subgroupOf.2 hk) ⟨a, ha⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hcomm : ∀ l ∈ L, ∀ k ∈ K, ⁅l, k⁆ ∈ K := by
    intro l hl k hk
    rw [commutatorElement_def]
    exact K.mul_mem (hconj l (hLA hl) k hk) (K.inv_mem hk)
  by_cases hN : t ∈ Subgroup.normalizer (L : Set G)
  ·
    set N : Subgroup G := ⁅L, Subgroup.zpowers t⁆ with hNdef
    have hNK : N ≤ K := by
      rw [hNdef, Subgroup.commutator_le]
      intro l hl s hs
      exact hcomm l hl s (Subgroup.zpowers_le.2 htK hs)
    have hzn : Subgroup.zpowers t ≤ Subgroup.normalizer (L : Set G) := Subgroup.zpowers_le.2 hN
    have hNL : N ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hzn
    have hLN : L ≤ Subgroup.normalizer (N : Set G) := by
      rw [hNdef, Subgroup.commutator_comm]
      exact Subgroup.normalizer_commutator_ge_right _ _
    have hNn : (N.subgroupOf L).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLN
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hL.1 hNn with htop | hcen
    · exact (Subgroup.subgroupOf_eq_top.1 htop).trans hNK
    · exfalso
      have h1 : ⁅N, L⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro n hn
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have := Subgroup.mem_center_iff.1
          (hcen (Subgroup.mem_subgroupOf.2 hn : (⟨n, hNL hn⟩ : ↥L) ∈ N.subgroupOf L)) ⟨l, hl⟩
        exact congrArg Subtype.val this
      have h2 := CFSG.LocalCores.perfect_double_commutator hL.1.1 h1
      obtain ⟨l, hl, hne⟩ := hnc
      apply hne
      have hmem : ⁅l, t⁆ ∈ (⁅L, Subgroup.zpowers t⁆ : Subgroup G) :=
        Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers t)
      rw [h2, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem.symm
  ·
    have hM : IsComponent (L.map (MulAut.conj t).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hL
    have hML : L.map (MulAut.conj t).toMonoidHom ≠ L := fun h =>
      hN (Subgroup.mem_normalizer_iff_map_conj_eq.2 h)
    have hcomL : ⁅L.map (MulAut.conj t).toMonoidHom, L⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hM hL).resolve_left hML
    have hLL : ⁅L, L⁆ ≤ K := by
      rw [Subgroup.commutator_le]
      intro l hl m hm
      set m' : G := t * m * t⁻¹ with hm'
      have hm'M : m' ∈ L.map (MulAut.conj t).toMonoidHom := ⟨m, hm, by simp [MulAut.conj_apply, hm']⟩
      have hlm' : l * m' = m' * l :=
        Subgroup.mem_centralizer_iff.1
          (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomL hm'M) l hl
      have hk₀ : m'⁻¹ * m ∈ K := by
        have h1 : m⁻¹ * t⁻¹ * m⁻¹⁻¹ ∈ K := hconj m⁻¹ (hLA (L.inv_mem hm)) t⁻¹ (K.inv_mem htK)
        have h2 : t * (m⁻¹ * t⁻¹ * m⁻¹⁻¹) ∈ K := K.mul_mem htK h1
        have e : m'⁻¹ * m = t * (m⁻¹ * t⁻¹ * m⁻¹⁻¹) := by rw [hm']; group
        rw [e]
        exact h2
      have hm'A : m' ∈ A := A.mul_mem (A.mul_mem (hKA htK) (hLA hm)) (A.inv_mem (hKA htK))
      have hlk := hcomm l hl _ hk₀
      have hmm : m = m' * (m'⁻¹ * m) := by group
      have e : ⁅l, m⁆ = m' * ⁅l, m'⁻¹ * m⁆ * m'⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]
        calc l * m * l⁻¹ * m⁻¹ = l * (m' * (m'⁻¹ * m)) * l⁻¹ * (m' * (m'⁻¹ * m))⁻¹ := by rw [← hmm]
          _ = (l * m') * (m'⁻¹ * m) * l⁻¹ * (m'⁻¹ * m)⁻¹ * m'⁻¹ := by group
          _ = (m' * l) * (m'⁻¹ * m) * l⁻¹ * (m'⁻¹ * m)⁻¹ * m'⁻¹ := by rw [hlm']
          _ = m' * (l * (m'⁻¹ * m) * l⁻¹ * (m'⁻¹ * m)⁻¹) * m'⁻¹ := by group
      rw [e]
      exact hconj m' hm'A _ hlk
    intro l hl
    have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.1.1
    exact hLL (by rw [hperf]; exact hl)

theorem component_acts_trivially_of_not_commute {k V : Type*} [CommSemiring k] [AddCommMonoid V]
    [Module k V] (ρ : Representation k G V) {W : Submodule k V} {L : Subgroup G} (hL : IsComponent L)
    {t : G} (hW : ∀ x : G, (x ∈ L ∨ x = t) → ∀ w ∈ W, ρ x w ∈ W ∧ ρ x⁻¹ w ∈ W)
    (htW : ∀ w ∈ W, ρ t w = w) (hnc : ∃ l ∈ L, t * l ≠ l * t) : ∀ l ∈ L, ∀ w ∈ W, ρ l w = w := by
  have hmul : ∀ (a b : G) (w : V), ρ (a * b) w = ρ a (ρ b w) := fun a b w => by rw [map_mul]; rfl
  have hone : ∀ w : V, ρ 1 w = w := fun w => by rw [map_one]; rfl
  have hinv : ∀ (a : G) (w : V), ρ a (ρ a⁻¹ w) = w := fun a w => by
    rw [← hmul, mul_inv_cancel, hone]
  have hinv' : ∀ (a : G) (w : V), ρ a⁻¹ (ρ a w) = w := fun a w => by
    rw [← hmul, inv_mul_cancel, hone]
  let A : Subgroup G :=
    { carrier := {g | ∀ w ∈ W, ρ g w ∈ W ∧ ρ g⁻¹ w ∈ W}
      one_mem' := fun w hw => ⟨by rw [hone]; exact hw, by rw [inv_one, hone]; exact hw⟩
      mul_mem' := fun {a b} ha hb w hw => by
        refine ⟨?_, ?_⟩
        · rw [hmul]
          exact (ha _ (hb w hw).1).1
        · rw [mul_inv_rev, hmul]
          exact (hb _ (ha w hw).2).2
      inv_mem' := fun {a} ha w hw => ⟨(ha w hw).2, by rw [inv_inv]; exact (ha w hw).1⟩ }
  let K : Subgroup G :=
    { carrier := {g | g ∈ A ∧ ∀ w ∈ W, ρ g w = w}
      one_mem' := ⟨A.one_mem, fun w _ => hone w⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨A.mul_mem ha.1 hb.1, fun w hw => by rw [hmul, hb.2 w hw, ha.2 w hw]⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, fun w hw => by
        have := hinv' a w
        rw [ha.2 w hw] at this
        exact this⟩ }
  have hKA : K ≤ A := fun g hg => hg.1
  have hK : (K.subgroupOf A).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨(g * n * g⁻¹ : A).2, fun w hw => ?_⟩
    show ρ ((g : G) * (n : G) * (g : G)⁻¹) w = w
    rw [hmul, hmul, hn.2 _ (g.2 w hw).2]
    exact hinv g w⟩
  have hLA : L ≤ A := fun l hl w hw => hW l (Or.inl hl) w hw
  have htK : t ∈ K := ⟨fun w hw => hW t (Or.inr rfl) w hw, htW⟩
  have hLK : L ≤ K := component_le_of_mem_normal_of_not_commute hKA hK hLA hL htK hnc
  exact fun l hl w hw => (hLK hl).2 w hw

end CFSG.LocalAnalysis.RankThreeUC.Section5
