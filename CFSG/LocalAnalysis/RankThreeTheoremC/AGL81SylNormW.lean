module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransfer
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding Subgroup Equiv

theorem map_isSubnormal_and_shape {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    {T : Subgroup Q} (hsub : IsSubnormal T ⊤)
    (hshape : IsComponentOf T ⊤ ∨ IsSymThreeOrSUThreeTwo ↥T) :
    IsSubnormal (T.map e.toMonoidHom) ⊤ ∧
      (IsComponentOf (T.map e.toMonoidHom) ⊤ ∨ IsSymThreeOrSUThreeTwo ↥(T.map e.toMonoidHom)) := by
  have htop : (⊤ : Subgroup Q).map e.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ e.surjective
  refine ⟨?_, ?_⟩
  · have h := hsub.map e.toMonoidHom
    rwa [htop] at h
  · rcases hshape with h | h
    · exact Or.inl ((CFSG.ComponentClassification.LocalComponents.equiv_iff e T).2 h)
    · exact Or.inr (IsSymThreeOrSUThreeTwo.of_mulEquiv
        (Subgroup.equivMapOfInjective T e.toMonoidHom e.injective) h)

theorem map_wSup_le {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') :
    (wSup Q).map e.toMonoidHom ≤ wSup Q' := by
  unfold wSup
  rw [Subgroup.map_iSup]
  refine iSup_le fun T => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hT => ?_
  exact le_iSup₂ (f := fun (T' : Subgroup Q')
      (_ : T' ∈ {T : Subgroup Q' | IsSubnormal T ⊤ ∧
        (IsComponentOf T ⊤ ∨ IsSymThreeOrSUThreeTwo ↥T)}) => T')
    (T.map e.toMonoidHom) (map_isSubnormal_and_shape e hT.1 hT.2)

theorem map_wSup_eq {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') :
    (wSup Q).map e.toMonoidHom = wSup Q' := by
  refine le_antisymm (map_wSup_le e) ?_
  have h := Subgroup.map_mono (f := e.toMonoidHom) (map_wSup_le e.symm)
  rwa [Subgroup.map_map,
    show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Q' from by ext x; simp,
    Subgroup.map_id] at h

theorem le_wSup_of_normal_of_isQuasisimple {Q : Type} [Group Q] {N : Subgroup Q} (hN : N.Normal)
    (hq : IsQuasisimple N) : N ≤ wSup Q := by
  haveI : N.Normal := hN
  have hsub : IsSubnormal N ⊤ :=
    IsSubnormal.step le_top Subgroup.normal_subgroupOf (IsSubnormal.refl ⊤)
  have hq' : CFSG.Open.IsQuasisimple ↥N := ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
  refine le_iSup₂ (f := fun (T : Subgroup Q)
      (_ : T ∈ {T : Subgroup Q | IsSubnormal T ⊤ ∧
        (IsComponentOf T ⊤ ∨ IsSymThreeOrSUThreeTwo ↥T)}) => T)
    N ⟨hsub, Or.inl ⟨le_top, hsub, hq'⟩⟩

theorem le_wSup_of_normal_of_mulEquiv {Q : Type} [Group Q] {N : Subgroup Q} (hN : N.Normal)
    (e : N ≃* Perm (Fin 3)) : N ≤ wSup Q := by
  haveI : N.Normal := hN
  have hsub : IsSubnormal N ⊤ :=
    IsSubnormal.step le_top Subgroup.normal_subgroupOf (IsSubnormal.refl ⊤)
  refine le_iSup₂ (f := fun (T : Subgroup Q)
      (_ : T ∈ {T : Subgroup Q | IsSubnormal T ⊤ ∧
        (IsComponentOf T ⊤ ∨ IsSymThreeOrSUThreeTwo ↥T)}) => T)
    N ⟨hsub, Or.inr (Or.inl ⟨e⟩)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
