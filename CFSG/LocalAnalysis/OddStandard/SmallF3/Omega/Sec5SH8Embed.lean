module

public import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma92b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.GorensteinWalter (PSL2 PGL2 IsOddPrimePower HasDihedralSylowTwo)

theorem sec5sh8_embed
    {X : Type} [Group X] [Finite X] (hO : CFSG.oddCore X = ⊥) (hDih : HasDihedralSylowTwo X)
    (hNC : ¬ CFSG.HasNormalPComplement 2 X) (P : Sylow 2 X)
    (hgen : Subgroup.normalClosure ((P : Subgroup X) : Set X) = ⊤) :
    Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F), IsOddPrimePower (Nat.card F) ∧
        (Nonempty (X ≃* PSL2 F) ∨ Nonempty (X ≃* PGL2 F)) := by
  rcases CFSG.ABGDGroups.aSeven_or_embedding_of_hasDihedralSylowTwo hDih hNC hO with
    h7 | ⟨F, hField, hFinite, hF, ι, M, hι, hM, hMle, hodd⟩
  · exact Or.inl h7
  right
  have hMn : M.Normal := by
    rcases hM with rfl | rfl
    · exact CFSG.ABGDGroups.pGammaL2PSLRange_normal hF
    · infer_instance
  let N : Subgroup X := M.comap ι
  haveI : N.Normal := hMn.comap ι
  have hNidx : N.index = M.relIndex ι.range := Subgroup.index_comap M ι
  have hNodd : Odd N.index := hNidx ▸ hodd
  have hPN : (P : Subgroup X) ≤ N :=
    CFSG.GH74.GLS.IVK.Proofs2.sylow_le_of_odd_index N hNodd P
  have htop : N = ⊤ := by
    have hle : Subgroup.normalClosure ((P : Subgroup X) : Set X) ≤ N :=
      Subgroup.normalClosure_le_normal (N := N) (fun x hx => hPN hx)
    rw [hgen] at hle
    exact top_le_iff.mp hle
  have hrange_le : ι.range ≤ M := by
    rintro x ⟨y, rfl⟩
    have hy : y ∈ N := by rw [htop]; exact Subgroup.mem_top y
    exact hy
  have hEq : ι.range = M := le_antisymm hrange_le hMle
  have e : X ≃* M :=
    (MulEquiv.ofBijective ι.rangeRestrict
      ⟨fun a b hab => hι (congrArg Subtype.val hab), ι.rangeRestrict_surjective⟩).trans
      (MulEquiv.subgroupCongr hEq)
  refine ⟨F, hField, hFinite, hF, ?_⟩
  rcases hM with hM | hM
  · left
    exact ⟨e.trans ((MulEquiv.subgroupCongr hM).trans
      (CFSG.GorensteinWalter.pGammaL2PSLRangeEquiv F).symm)⟩
  · right
    exact ⟨e.trans ((MulEquiv.subgroupCongr hM).trans
      (CFSG.GorensteinWalter.pGammaL2PGLRangeEquiv F).symm)⟩

end CFSG.OddStandard.SmallF3.Omega
