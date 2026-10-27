module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporBasic
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup

theorem eq_top_of_isComponent_of_isQuasisimple {X : Type*} [Group X] (hX : IsQuasisimple X)
    {B : Subgroup X} (hB : IsComponent B) : B = ⊤ := by
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hX hB.2 with h | h
  · exact h
  · exfalso
    have : Nontrivial B := LocalCores.isQuasisimple_nontrivial hB.1
    have hcomm : ∀ a b : B, a * b = b * a := fun a b => Subtype.ext
      (mem_center_iff.1 (h a.2) b).symm
    have : Group.IsPerfect B := hB.1.1
    exact Group.IsPerfect.not_isSolvable B (Group.isSolvable_of_comm hcomm)

theorem compsSatisfy_of_isQuasisimple {X : Type} [Group X] (hX : IsQuasisimple X)
    {Q : (Y : Type) → [Group Y] → Prop} (hQ : IsoInvariant Q) (h : Q X) : CompsSatisfy X Q := by
  intro B hB
  have hB' := eq_top_of_isComponent_of_isQuasisimple hX hB
  exact hQ B X ((MulEquiv.subgroupCongr hB').trans Subgroup.topEquiv) h

theorem eq_of_isComponent_of_simple_normal {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    [K.Normal] (hK : IsSimpleGroup K) (hC : Group.IsSolvable (centralizer (K : Set X)))
    {B : Subgroup X} (hB : IsComponent B) : B = K := by
  have : Nontrivial B := LocalCores.isQuasisimple_nontrivial hB.1
  have : Group.IsPerfect B := hB.1.1
  rcases LocalCores.component_normal_subgroup hB (inferInstance : K.Normal) with hle | hcomm
  · have hsub : (B.subgroupOf K).IsSubnormal := hB.2.subgroupOf
    rcases hsub.eq_bot_or_top_of_isSimpleGroup hK with h | h
    · exfalso
      rw [subgroupOf_eq_bot] at h
      obtain ⟨x, hx⟩ := exists_ne (1 : B)
      exact hx (Subtype.ext (by simpa using Subgroup.disjoint_def.1 h x.2 (hle x.2)))
    · exact le_antisymm hle (by simpa [subgroupOf_eq_top] using h)
  · exfalso
    have hBC : B ≤ centralizer (K : Set X) := commutator_eq_bot_iff_le_centralizer.mp hcomm
    have : Group.IsSolvable B :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hBC)
    exact Group.IsPerfect.not_isSolvable B inferInstance

theorem compsSatisfy_of_isSimpleGroup {X : Type} [Group X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) :
    CompsSatisfy X fun Y _ => Nat.card (Y ⧸ center Y) ∈ ({Nat.card X} : Set ℕ) := by
  obtain ⟨hq, hZ⟩ := LocalCores.isQuasisimple_of_isSimpleGroup hX
  refine compsSatisfy_of_isQuasisimple hq (isoInvariant_card_quotient_center _) ?_
  show Nat.card (X ⧸ center X) = Nat.card X
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center X)
  rw [hZ, Subgroup.card_bot, mul_one] at h
  rw [hZ]
  exact h.symm

theorem alternating_ten_not_comm : ∃ a b : alternatingGroup (Fin 10), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, ?_⟩, ⟨Equiv.swap 0 1 * Equiv.swap 1 3, ?_⟩, ?_⟩
  · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
  · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
  · intro h
    have h2 := congrArg (fun p : alternatingGroup (Fin 10) => (p : Equiv.Perm (Fin 10)) 2) h
    revert h2
    decide

theorem compsSatisfy_perm_ten :
    CompsSatisfy (Equiv.Perm (Fin 10))
      fun Y _ => Nat.card (Y ⧸ center Y) ∈ ({1814400} : Set ℕ) := by
  intro B hB
  have hs : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hC : Group.IsSolvable
      (centralizer (alternatingGroup (Fin 10) : Set (Equiv.Perm (Fin 10)))) := by
    rw [ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot (by simp)]
    infer_instance
  obtain rfl := eq_of_isComponent_of_simple_normal hs hC hB
  obtain ⟨-, hZ⟩ := LocalCores.isQuasisimple_of_isSimpleGroup alternating_ten_not_comm
  show Nat.card (↥(alternatingGroup (Fin 10)) ⧸ center ↥(alternatingGroup (Fin 10))) = 1814400
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center ↥(alternatingGroup (Fin 10)))
  rw [hZ, Subgroup.card_bot, mul_one, Nat.card_eq_fintype_card, card_alternatingGroup,
    Fintype.card_fin] at h
  rw [hZ, ← h]
  norm_num [Nat.factorial]

theorem compsSatisfy_centralizer_of_isConj {G : Type} [Group G] {r x : G} (h : IsConj r x)
    {Q : (Y : Type) → [Group Y] → Prop} (hQ : IsoInvariant Q)
    (hr : CompsSatisfy (centralizer ({r} : Set G)) Q) :
    CompsSatisfy (centralizer ({x} : Set G)) Q := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have e : ↥(centralizer ({r} : Set G)) ≃* ↥(centralizer ({x} : Set G)) :=
    (centralizerEquiv (MulAut.conj c) r).trans (MulEquiv.subgroupCongr (by
      rw [MulAut.conj_apply, hc]))
  exact CompsSatisfy.of_mulEquiv hQ e.symm hr

end CFSG.ComponentClassification.RestrictedStd.Spor
