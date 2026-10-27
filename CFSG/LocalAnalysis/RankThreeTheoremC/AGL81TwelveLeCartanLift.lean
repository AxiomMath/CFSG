module

public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.SmallDegreeSix
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.RichardWeiss.Coordinator Subgroup
open scoped commutatorElement

theorem exists_isComponentOf_fixSubgroup_of_map {Y : Type} [Group Y] [Finite Y] (α : MulAut Y)
    {Kb : Subgroup (Y ⧸ center Y)}
    (hK : IsComponentOf Kb (fixSubgroup (centerQuotientAut Y α))) :
    ∃ K : Subgroup Y, IsComponentOf K (fixSubgroup α) ∧
      K.map (QuotientGroup.mk' (center Y)) = Kb := by
  classical
  set π : Y →* Y ⧸ center Y := QuotientGroup.mk' (center Y) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  obtain ⟨hKC, hKsub, hKq⟩ := hK
  set K₁ : Subgroup Y := Kb.comap π with hK₁
  set K : Subgroup Y := ⁅K₁, K₁⁆ with hKdef
  have hmov : ∀ x ∈ K₁, ∃ z ∈ center Y, α x = x * z := by
    intro x hx
    have h1 : (centerQuotientAut Y α) (π x) = π x := hKC hx
    have h2 : π (α x) = π x := h1
    have h3 := QuotientGroup.eq.mp h2
    refine ⟨x⁻¹ * α x, ?_, by group⟩
    simpa using inv_mem h3
  have hcomm : ∀ (a b z w : Y), z ∈ center Y → w ∈ center Y → ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
    intro a b z w hz hw
    have h1 : ∀ g : Y, ⁅z, g⁆ = 1 := fun g =>
      commutatorElement_eq_one_iff_mul_comm.2 (mem_center_iff.1 hz g).symm
    have h2 : ∀ g : Y, ⁅g, w⁆ = 1 := fun g =>
      commutatorElement_eq_one_iff_mul_comm.2 (mem_center_iff.1 hw g)
    simp [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj, h1,
      h2]
  have hfix : K ≤ fixSubgroup α := by
    refine commutator_le.2 fun a ha b hb => ?_
    obtain ⟨z, hz, hza⟩ := hmov a ha
    obtain ⟨w, hw, hwb⟩ := hmov b hb
    show α ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement, hza, hwb, hcomm a b z w hz hw]
  have hK₁map : K₁.map π = Kb := map_comap_eq_self_of_surjective hπs Kb
  have hKbperf : ⁅Kb, Kb⁆ = Kb := by
    rw [← map_subtype_commutator, hKq.1, Subgroup.map_top, range_subtype]
  have hKmap : K.map π = Kb := by
    rw [hKdef, map_commutator, hK₁map, hKbperf]
  have hdec : ∀ x ∈ K₁, ∃ k ∈ K, ∃ z ∈ center Y, x = k * z := by
    intro x hx
    have hxK : π x ∈ K.map π := by
      rw [hKmap]
      exact hx
    obtain ⟨k, hk, hkx⟩ := hxK
    refine ⟨k, hk, k⁻¹ * x, ?_, by group⟩
    exact QuotientGroup.eq.mp hkx
  have hKperf : ⁅K, K⁆ = K := by
    refine le_antisymm (commutator_le_self K) ?_
    show ⁅K₁, K₁⁆ ≤ ⁅K, K⁆
    refine commutator_le.2 fun a ha b hb => ?_
    obtain ⟨k, hk, z, hz, rfl⟩ := hdec a ha
    obtain ⟨k', hk', w, hw, rfl⟩ := hdec b hb
    rw [hcomm k k' z w hz hw]
    exact commutator_mem_commutator hk hk'
  have hKbq : CFSG.IsQuasisimple ↥Kb :=
    ⟨⟨hKq.1⟩, hKq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
      Kb hKq⟩
  have hKq' : CFSG.IsQuasisimple ↥K := by
    have hperfK : Group.IsPerfect ↥K := isPerfect_iff.mpr hKperf
    have hkerK : (π.subgroupMap K).ker ≤ center ↥K := by
      intro x hx
      have hπx : π (x : Y) = 1 := congrArg Subtype.val hx
      have hxz : (x : Y) ∈ center Y := (QuotientGroup.eq_one_iff _).1 hπx
      exact mem_center_iff.2 fun g => Subtype.ext (mem_center_iff.1 hxz g)
    refine (CFSG.LocalCores.isQuasisimple_iff_of_surjective hperfK (π.subgroupMap K)
      (π.subgroupMap_surjective K) hkerK).2 ?_
    rw [hKmap]
    exact hKbq
  have hsub : IsSubnormal K (fixSubgroup α) := by
    have h1 : IsSubnormal K₁ ((fixSubgroup (centerQuotientAut Y α)).comap π) := hKsub.comap π
    have hC : fixSubgroup α ≤ (fixSubgroup (centerQuotientAut Y α)).comap π := by
      intro y hy
      have hy' : α y = y := hy
      show π (α y) = π y
      rw [hy']
    have h2 : IsSubnormal (K₁ ⊓ fixSubgroup α) (fixSubgroup α) := h1.inf_of_le hC
    have hKK₁ : K ≤ K₁ := commutator_le_self K₁
    have hKK : K ≤ K₁ ⊓ fixSubgroup α := le_inf hKK₁ hfix
    have hnormK₁ : (K.subgroupOf K₁).Normal := by
      have h : K.subgroupOf K₁ = commutator ↥K₁ := by
        rw [hKdef, ← map_subtype_commutator]
        exact comap_map_eq_self_of_injective K₁.subtype_injective _
      rw [h]
      infer_instance
    have hconj : ∀ h g : Y, h ∈ K → g ∈ K₁ → g * h * g⁻¹ ∈ K :=
      (normal_subgroupOf_iff hKK₁).1 hnormK₁
    have hnorm : (K.subgroupOf (K₁ ⊓ fixSubgroup α)).Normal :=
      (normal_subgroupOf_iff hKK).2 fun h g hh hg => hconj h g hh hg.1
    exact IsSubnormal.step hKK hnorm h2
  exact ⟨K, ⟨hfix, hsub, LieSemisimple.open_isQuasisimple hKq'⟩, hKmap⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe
