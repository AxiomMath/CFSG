module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Surv
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U42Idx

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.Assembly.LowTwoRank

theorem genericKill_of_sp4_hom {P : Type} [Group P] (α : MulAut P) {F : Type} [Field F] [Finite F]
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (ϖ : ↥(StatedSp 2 F) →* P) (hfix : ∀ x, α (ϖ x) = ϖ x)
    (hker : ∀ x, ϖ x = 1 →
      (x : GL (Fin 2 ⊕ Fin 2) F) ∈ StatedScalars (Fin 2 ⊕ Fin 2) F) : GenericKill P α := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hq3 : 3 ≤ Nat.card F := by
    rw [hF]
    exact hp3.trans (Nat.le_self_pow (by omega) p)
  have hq2 : p ^ f ≠ 2 := by
    have : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by omega) p)
    omega
  have hperf : Group.IsPerfect (StatedSp 2 F) := by
    refine CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 2 F ?_
    rcases (show 4 ≤ Nat.card F ∨ Nat.card F = 3 by omega) with h4 | h3
    · left
      have := Fintype.ofFinite F
      have h4' : 4 ≤ (Finset.univ : Finset F).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact h4
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4'
      exact ⟨s, hs⟩
    · exact Or.inr (Or.inl ⟨h3, le_rfl⟩)
  have hTs : IsSimpleGroup (StatedProj (StatedSp 2 F)) := by
    refine CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num) ?_
    rcases (show 4 ≤ Nat.card F ∨ Nat.card F = 3 by omega) with h4 | h3
    · exact Or.inl (Or.inr h4)
    · exact Or.inr (Or.inl ⟨h3, le_rfl⟩)
  have : Group.IsPerfect (StatedProj (StatedSp 2 F)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have : Nontrivial (StatedProj (StatedSp 2 F)) := IsSimpleGroup.toNontrivial
  have hle : ϖ.ker ≤ ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)).comap
      (MonoidHom.id (StatedSp 2 F)) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hker x hx)
  let c : ↥ϖ.range →* StatedProj (StatedSp 2 F) :=
    (QuotientGroup.map ϖ.ker _ (MonoidHom.id (StatedSp 2 F)) hle).comp
      (QuotientGroup.quotientKerEquivRange ϖ).symm.toMonoidHom
  have hc : Function.Surjective c :=
    (QuotientGroup.map_surjective_of_surjective ϖ.ker
      ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)) (MonoidHom.id (StatedSp 2 F))
      (fun t => QuotientGroup.mk_surjective t) hle).comp
      (QuotientGroup.quotientKerEquivRange ϖ).symm.surjective
  have hlie : LieModel (StatedProj (StatedSp 2 F)) .PSp 2 p f :=
    Or.inl ⟨by decide, ⟨hp, hf, le_refl 2, fun h' => hq2 (Prod.mk.inj h').2⟩, F, inferInstance,
      inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  have hFSp : FSp4 (StatedProj (StatedSp 2 F)) := ⟨p, f, hp, hf, hp2, hlie⟩
  refine Or.inl ⟨ϖ.range, Group.IsPerfect.range ϖ, ?_, StatedProj (StatedSp 2 F), inferInstance, hTs,
    c, hc, Group.IsPerfect.not_isSolvable _, fun k hk =>
      not_kindFactorAll_of_FSp4 minIndexU42 hFSp k (KindFactor.all hk)⟩
  rintro _ ⟨x, rfl⟩
  exact hfix x

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
