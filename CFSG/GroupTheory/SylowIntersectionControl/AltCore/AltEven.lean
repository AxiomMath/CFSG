module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.StarOrbit
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.Commute
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.TransitiveCase
import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup MulAction

section Abstract

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normal_closure_sq_mem_of_le {H N : Subgroup G}
    (hN : N ≤ normalizer (H : Set G)) :
    ((closure {a | a ∈ N ∧ a ^ 2 ∈ H}).subgroupOf N).Normal := by
  have hsN : ∀ n ∈ N, ∀ a ∈ {a | a ∈ N ∧ a ^ 2 ∈ H}, n * a * n⁻¹ ∈ {a | a ∈ N ∧ a ^ 2 ∈ H} :=
    fun n hn a ha => ⟨mul_mem (mul_mem hn ha.1) (inv_mem hn), by
      rw [conj_pow]
      exact (mem_normalizer_iff.mp (hN hn) _).mp ha.2⟩
  have hmap : ∀ n ∈ N, (closure {a | a ∈ N ∧ a ^ 2 ∈ H}).map (MulAut.conj n).toMonoidHom ≤
      closure {a | a ∈ N ∧ a ^ 2 ∈ H} := fun n hn => by
    rw [MonoidHom.map_closure]
    refine closure_mono ?_
    rintro _ ⟨a, ha, rfl⟩
    exact hsN n hn a ha
  refine (normal_subgroupOf_iff_le_normalizer ((closure_le N).mpr fun _ ha => ha.1)).mpr
    fun n hn => ?_
  refine mem_normalizer_iff.mpr fun y => ⟨fun hy => hmap n hn ⟨y, hy, rfl⟩, fun hy => ?_⟩
  have := hmap n⁻¹ (inv_mem hn) ⟨_, hy, rfl⟩
  rwa [show (MulAut.conj n⁻¹).toMonoidHom (n * y * n⁻¹) = y by simp [mul_assoc]] at this

theorem _root_.CFSG.GroupTheory.IsPIsolatedOver.exists_le_of_sq_mem_of_le
    {H N M : Subgroup G}
    (h : IsPIsolatedOver 2 N H) (hH : IsPGroup 2 H) (hHN : H ≤ N)
    (hN : N ≤ normalizer (H : Set G)) (hM : ∀ a ∈ N, a ^ 2 ∈ H → a ∈ M) :
    ∃ K : Subgroup G, H ≤ K ∧ K ≤ N ∧ (K.subgroupOf N).IsSubnormal ∧ 2 ∣ H.relIndex K ∧
      K ≤ M := by
  obtain ⟨x, hxN, hxH, hx2⟩ := IsPIsolatedOver.exists_sq_mem_of_le h hH hHN hN
  have hHK : H ≤ closure {a | a ∈ N ∧ a ^ 2 ∈ H} := fun y hy =>
    subset_closure ⟨hHN hy, pow_mem hy 2⟩
  have hKN : closure {a | a ∈ N ∧ a ^ 2 ∈ H} ≤ N := (closure_le N).mpr fun _ ha => ha.1
  exact ⟨_, hHK, hKN, (normal_closure_sq_mem_of_le hN).isSubnormal,
    two_dvd_relIndex_of_sq_mem hHK (hKN.trans hN) (subset_closure ⟨hxN, hx2⟩) hxH hx2,
    (closure_le M).mpr fun a ha => hM a ha.1 ha.2⟩

end Abstract

variable {α : Type} [Fintype α] [DecidableEq α] {H : Subgroup (Perm α)}

@[expose] def IsEvenSetAlt (H : Subgroup (Perm α)) (O : Set α) : Prop :=
  ∃ x ∈ normalizer (H : Set (Perm α)) ⊓ alternatingGroup α, x ∈ fixOutside O ∧ x ∉ H ∧ x ^ 2 ∈ H

theorem IsEvenSetAlt.mono {O O' : Set α} (h : IsEvenSetAlt H O) (hOO' : O ⊆ O') :
    IsEvenSetAlt H O' := by
  obtain ⟨x, hx, hxO, hxH, hx2⟩ := h
  exact ⟨x, hx, fun y hy => hxO y fun h => hy (hOO' h), hxH, hx2⟩

theorem isEvenSetAlt_univ (hH : IsPGroup 2 H) (hHL : H ≤ alternatingGroup α)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm α)) ⊓ alternatingGroup α) H) :
    IsEvenSetAlt H Set.univ := by
  obtain ⟨x, hx, hxH, hx2⟩ :=
    IsPIsolatedOver.exists_sq_mem_of_le hiso hH (le_inf le_normalizer hHL) inf_le_left
  exact ⟨x, hx, fun y hy => absurd (Set.mem_univ y) hy, hxH, hx2⟩

private theorem two_dvd_relIndex_secOf_inf (hH : IsPGroup 2 H) (hrad : IsRadical H)
    (hHL : H ≤ alternatingGroup α) {O : Set α} [DecidablePred (· ∈ O)]
    (hO : normalizer (H : Set (Perm α)) ≤ setStab O) (he : IsEvenSetAlt H O) :
    2 ∣ H.relIndex (secOf O hO ⊓ alternatingGroup α) := by
  obtain ⟨x, hx, hxO, hxH, hx2⟩ := he
  have h1 : restrHom Oᶜ ⟨x, (setStab_compl O ▸ hO) (mem_inf.mp hx).1⟩ = 1 := by
    ext z
    by_cases hz : z ∈ Oᶜ
    · rw [restrHom_apply_of_mem _ hz]
      exact hxO z hz
    · rw [restrHom_apply_of_not_mem _ hz]
      rfl
  refine two_dvd_relIndex_of_sq_mem (le_inf (le_secOf hH hrad hO) hHL)
    (inf_le_left.trans (secOf_le hO)) (mem_inf.mpr ⟨⟨(mem_inf.mp hx).1, ?_⟩, (mem_inf.mp hx).2⟩)
    hxH hx2
  rw [h1]
  exact one_mem _

theorem not_isEvenSetAlt_of_disjoint (hH : IsPGroup 2 H) (hrad : IsRadical H)
    (hHL : H ≤ alternatingGroup α)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm α)) ⊓ alternatingGroup α) H)
    {O O' : Set α} (hO : normalizer (H : Set (Perm α)) ≤ setStab O)
    (hO' : normalizer (H : Set (Perm α)) ≤ setStab O') (hOO' : O ⊆ O'ᶜ)
    (he : IsEvenSetAlt H O) (he' : IsEvenSetAlt H O') : False := by
  classical
  have hn : ∀ {C : Set α} [DecidablePred (· ∈ C)]
      (hC : normalizer (H : Set (Perm α)) ≤ setStab C),
      normalizer (H : Set (Perm α)) ⊓ alternatingGroup α ≤
        normalizer ((secOf C hC ⊓ alternatingGroup α : Subgroup (Perm α)) : Set (Perm α)) :=
    fun hC => (le_inf (inf_le_left.trans (le_normalizer_secOf hH hrad hC))
      le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  exact not_isPIsolatedOver_of_commute hH (le_inf le_normalizer hHL) inf_le_left
    (le_inf (le_secOf hH hrad hO) hHL) (le_inf (le_secOf hH hrad hO') hHL)
    (inf_le_inf_right _ (secOf_le hO)) (inf_le_inf_right _ (secOf_le hO')) (hn hO) (hn hO')
    (fun g hg k hk => commutator_mem_of_mem_secOf hH hrad hO hO' hOO' (mem_inf.mp hg).1
      (mem_inf.mp hk).1)
    (two_dvd_relIndex_secOf_inf hH hrad hHL hO he)
    (two_dvd_relIndex_secOf_inf hH hrad hHL hO' he') hiso

theorem eq_restrSub_of_not_isEvenSetAlt (hH : IsPGroup 2 H) (hrad : IsRadical H)
    {O : Set α} [DecidablePred (· ∈ O)] (hO : normalizer (H : Set (Perm α)) ≤ setStab O)
    (hne : ¬ IsEvenSetAlt H O) {Q : Subgroup (Perm α)} (hQ : IsPGroup 2 Q)
    (hQO : Q ≤ fixOutside O ⊓ alternatingGroup α) (hPQ : restrSub O H ≤ Q) :
    Q = restrSub O H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (le_of_inf_normalizer_le_of_isPGroup hQ hPQ fun y hy => ?_) hPQ
  obtain ⟨hyQ, hyN⟩ := mem_inf.mp hy
  have hyO := (mem_inf.mp (hQO hyQ)).1
  have hyH : y ∈ normalizer (H : Set (Perm α)) :=
    mem_normalizer_of_mem_fixOutside hH hrad hO hyO hyN
  by_cases hyH' : y ∈ H
  · rw [← restrHom_eq_self hyO (fixOutside_le_setStab _ hyO)]
    exact restrHom_mem_restrSub hyH'
  · exfalso
    obtain ⟨m, hm⟩ := hQ ⟨y, hyQ⟩
    obtain ⟨k, hk, hk2⟩ := exists_pow_not_mem_sq_mem (m := m)
      (by simpa using congrArg Subtype.val hm) hyH'
    exact hne ⟨_, mem_inf.mpr ⟨pow_mem hyH _, pow_mem (mem_inf.mp (hQO hyQ)).2 _⟩,
      pow_mem hyO _, hk, hk2⟩

private theorem isEvenSetAlt_fixSet_of_four {x y u v : α} (hx : x ∈ fixSet H) (hy : y ∈ fixSet H)
    (hu : u ∈ fixSet H) (hv : v ∈ fixSet H) (hxy : x ≠ y) (hxu : x ≠ u) (hxv : x ≠ v)
    (hyu : y ≠ u) (hyv : y ≠ v) (huv : u ≠ v) : IsEvenSetAlt H (fixSet H) := by
  have hsq : (swap x y * swap u v) ^ 2 = 1 :=
    CFSG.LocalAnalysis.ComponentInitial.swap_mul_swap_sq_of_ne hxu hxv hyu.symm hyv
  refine ⟨swap x y * swap u v, mem_inf.mpr ⟨mul_mem (swap_mem_normalizer_of_mem_fixSet hx hy)
    (swap_mem_normalizer_of_mem_fixSet hu hv), mul_mem_alternatingGroup_of_isSwap
    (swap_isSwap_iff.mpr hxy) (swap_isSwap_iff.mpr huv)⟩, fun z hz => ?_, fun hH' => ?_, ?_⟩
  · have hzx : z ≠ x := fun h => hz (h ▸ hx)
    have hzy : z ≠ y := fun h => hz (h ▸ hy)
    have hzu : z ≠ u := fun h => hz (h ▸ hu)
    have hzv : z ≠ v := fun h => hz (h ▸ hv)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hzu hzv, swap_apply_of_ne_of_ne hzx hzy]
  · have := hx _ hH'
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxu hxv, swap_apply_left] at this
    exact hxy this.symm
  · rw [hsq]
    exact one_mem _

theorem ncard_fixSet_le_three (hne : ¬ IsEvenSetAlt H (fixSet H)) : (fixSet H).ncard ≤ 3 := by
  classical
  by_contra h
  have h4 : 4 ≤ (fixSet H).toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card']
    omega
  obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq h4
  obtain ⟨x, y, u, v, hxy, hxu, hxv, hyu, hyv, huv, rfl⟩ := Finset.card_eq_four.mp hcard
  have hm : ∀ z ∈ ({x, y, u, v} : Finset α), z ∈ fixSet H := fun z hz =>
    Set.mem_toFinset.mp (ht hz)
  exact hne (isEvenSetAlt_fixSet_of_four (hm x (by simp)) (hm y (by simp)) (hm u (by simp))
    (hm v (by simp)) hxy hxu hxv hyu hyv huv)

end CFSG.GroupTheory.AltCore
