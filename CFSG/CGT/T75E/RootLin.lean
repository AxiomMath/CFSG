module

public import CFSG.CGT.T75E.RootLinCore
public import CFSG.CGT.Timmesfeld75.ListWCLin

public noncomputable section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki CFSG.Assembly.LowTwoRank Matrix
open scoped MatrixGroups

section Map

variable {K : Type} [Group K] {n : ℕ} {F : Type} [Field F]

@[expose] def slToK (e : K ≃* StatedProj (StatedSL n F)) : SL(n, F) →* K :=
  e.symm.toMonoidHom.comp
    ((QuotientGroup.mk' _).comp (specialLinearGroupEquivStatedSL n F).toMonoidHom)

theorem slToK_surjective (e : K ≃* StatedProj (StatedSL n F)) :
    Function.Surjective (slToK e) :=
  e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp
    (specialLinearGroupEquivStatedSL n F).surjective)

theorem map_slToK_tvCenterSL (e : K ≃* StatedProj (StatedSL n F)) (c : Fin n → F) :
    (tvCenterSL c).map (slToK e) =
      (transvImage n F (transvCenter n F c)).map e.symm.toMonoidHom := by
  rw [slToK, ← Subgroup.map_map, ← Subgroup.map_map, map_tvCenterSL]
  rfl

theorem map_slToK_tvAxisSL (e : K ≃* StatedProj (StatedSL n F)) (a : Fin n → F) :
    (tvAxisSL a).map (slToK e) =
      (transvImage n F (transvAxis n F a)).map e.symm.toMonoidHom := by
  rw [slToK, ← Subgroup.map_map, ← Subgroup.map_map, map_tvAxisSL]
  rfl

end Map

section Centre

variable {K : Type} [Group K] {Tb : Subgroup K} {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_centre_data (hn : 3 ≤ n) (e : K ≃* StatedProj (StatedSL n F)) (hT : IsWC Tb)
    (hT1 : Tb ≠ ⊥) : ∃ π : SL(n, F) →* K, Function.Surjective π ∧
      ∃ c : Fin n → F, c ≠ 0 ∧ Tb = (tvCenterSL c).map π := by
  obtain ⟨-, hcase, -⟩ := lin_wc hn e hT hT1
  have hback : (Tb.map e.toMonoidHom).map e.symm.toMonoidHom = Tb :=
    map_symm_map_mulEquiv e.symm Tb
  rcases hcase with ⟨c, hc, hTc⟩ | ⟨a, ha, hTa⟩
  · exact ⟨slToK e, slToK_surjective e, c, hc, by
      rw [map_slToK_tvCenterSL, ← hTc, hback]⟩
  · exact ⟨(slToK e).comp invT, (slToK_surjective e).comp invT_surjective, a, ha, by
      rw [← Subgroup.map_map, map_invT_tvCenterSL, map_slToK_tvAxisSL, ← hTa, hback]⟩

end Centre

section Main

variable {K : Type} [Group K] [Finite K] {Tb : Subgroup K} {c₁ c₂ : K} {f n : ℕ}
  {F : Type} [Field F] [Finite F] [CharP F 2]

theorem rootGroup_lin (hn : 3 ≤ n) (e : K ≃* StatedProj (StatedSL n F)) (hT : IsWC Tb)
    (hT1 : Tb ≠ ⊥) (hf : 2 ≤ f) (ρ : ↥(Y3 Tb c₁ c₂) →* PSU3Model f)
    (hρ : Function.Surjective ρ) : False := by
  obtain ⟨π, hπ, c, hc, hTb⟩ := exists_centre_data hn e hT hT1
  exact rootGroup_lin_core π hπ hc hTb hT hf ρ hρ

end Main
end CFSG.CGT.T75E

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki CFSG.Assembly.LowTwoRank

variable {K : Type} [Group K] [Finite K] {Tb : Subgroup K} {c₁ c₂ : K} {f n : ℕ}

theorem rootGroup_lin_of_model {m : ℕ} (hn : 3 ≤ n)
    (hG : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSL n 2 m) (hT : IsWC Tb)
    (hT1 : Tb ≠ ⊥) (hf : 2 ≤ f) (ρ : ↥(Y3 Tb c₁ c₂) →* PSU3Model f)
    (hρ : Function.Surjective ρ) : False := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hG
  have : CharP F 2 := charP_two_of_card hF
  exact rootGroup_lin hn e hT hT1 hf ρ hρ

end CFSG.CGT.T75E
