module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I1420

@[expose] def IsSubnormalQuotient (G : Type*) [Group G] (L : Type*) [Group L] : Prop :=
  ∃ H : Subgroup G, H.IsSubnormal ∧ ∃ f : H →* L, Function.Surjective f

namespace IsSubnormalQuotient

variable {G G' L : Type*} [Group G] [Group G'] [Group L]

theorem of_mulEquiv (e : G ≃* G') (h : IsSubnormalQuotient G L) : IsSubnormalQuotient G' L := by
  obtain ⟨H, hH, f, hf⟩ := h
  refine ⟨H.map e.toMonoidHom, hH.map e.surjective,
    f.comp (H.equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom, ?_⟩
  exact hf.comp (MulEquiv.surjective _)

theorem false_of_isSolvable [Group.IsSolvable G] (hL : ¬ Group.IsSolvable L)
    (h : IsSubnormalQuotient G L) : False := by
  obtain ⟨H, -, f, hf⟩ := h
  exact hL (Group.isSolvable_of_surjective hf)

theorem split [IsSimpleGroup L] (ψ : G →* G') (hψ : Function.Surjective ψ)
    (h : IsSubnormalQuotient G L) :
    IsSubnormalQuotient ψ.ker L ∨ IsSubnormalQuotient G' L := by
  obtain ⟨H, hH, f, hf⟩ := h
  have : (ψ.ker.subgroupOf H).Normal := inferInstance
  have : ((ψ.ker.subgroupOf H).map f).Normal := Subgroup.Normal.map inferInstance f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((ψ.ker.subgroupOf H).map f) with h0 | h1
  · right
    refine ⟨H.map ψ, hH.map hψ, ?_⟩
    have hker : (ψ.subgroupMap H).ker ≤ f.ker := by
      intro x hx
      have hx' : x ∈ ψ.ker.subgroupOf H := by
        rw [← Subgroup.ker_subgroupMap]
        exact hx
      have : f x ∈ (ψ.ker.subgroupOf H).map f := ⟨x, hx', rfl⟩
      rw [h0] at this
      simpa using this
    refine ⟨MonoidHom.liftOfSurjective (ψ.subgroupMap H) (ψ.subgroupMap_surjective H) ⟨f, hker⟩,
      fun l => ?_⟩
    obtain ⟨x, rfl⟩ := hf l
    exact ⟨ψ.subgroupMap H x, MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨f, hker⟩ x⟩
  · left
    refine ⟨H.subgroupOf ψ.ker, hH.subgroupOf, ?_⟩
    let ι : ↥(H.subgroupOf ψ.ker) →* ↥H :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine ⟨f.comp ι, fun l => ?_⟩
    have hl : l ∈ (ψ.ker.subgroupOf H).map f := by rw [h1]; trivial
    obtain ⟨m, hm, rfl⟩ := hl
    exact ⟨⟨⟨m.1, hm⟩, m.2⟩, rfl⟩

theorem subsingleton_of_surj {H : Type*} [Group H] (f : H →* L) (hf : Function.Surjective f)
    (h : ∀ x, f x = 1) : Subsingleton L := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := hf a
  obtain ⟨y, rfl⟩ := hf b
  rw [h x, h y]

theorem alt_of_perm {β : Type*} [Fintype β] [DecidableEq β] [IsSimpleGroup L]
    (hL : ¬ Group.IsSolvable L) (h : IsSubnormalQuotient (Equiv.Perm β) L) :
    5 ≤ Nat.card β ∧ Nonempty (L ≃* alternatingGroup β) := by
  by_cases h5 : 5 ≤ Nat.card β
  swap
  · have : Group.IsSolvable (Equiv.Perm β) := Equiv.Perm.isSolvable (by omega)
    exact (h.false_of_isSolvable hL).elim
  refine ⟨h5, ?_⟩
  have : Nontrivial β := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  rcases split (Equiv.Perm.sign : Equiv.Perm β →* ℤˣ) (Equiv.Perm.sign_surjective β) h with
    h' | h'
  · have h'' : IsSubnormalQuotient (alternatingGroup β) L := h'
    have : IsSimpleGroup (alternatingGroup β) := alternatingGroup.isSimpleGroup h5
    obtain ⟨H, hH, f, hf⟩ := h''
    rcases hH.eq_bot_or_top_of_isSimpleGroup this with rfl | rfl
    · exfalso
      refine not_subsingleton L (subsingleton_of_surj f hf fun x => ?_)
      have hx : (x : alternatingGroup β) ∈ (⊥ : Subgroup (alternatingGroup β)) := x.2
      rw [Subgroup.mem_bot] at hx
      have : x = 1 := Subtype.ext hx
      rw [this, map_one]
    · let f' : alternatingGroup β →* L := f.comp Subgroup.topEquiv.symm.toMonoidHom
      have hf' : Function.Surjective f' := hf.comp (MulEquiv.surjective _)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f'.ker with hk | hk
      · exact ⟨MulEquiv.symm (MulEquiv.ofBijective f'
          ⟨(MonoidHom.ker_eq_bot_iff f').1 hk, hf'⟩)⟩
      · exfalso
        exact not_subsingleton L (subsingleton_of_surj f' hf' fun x =>
          (MonoidHom.mem_ker).1 (hk ▸ Subgroup.mem_top x))
  · exact (h'.false_of_isSolvable hL).elim

end IsSubnormalQuotient

end CFSG.HardMathSupport.Solomon.Coordinator.I1420
