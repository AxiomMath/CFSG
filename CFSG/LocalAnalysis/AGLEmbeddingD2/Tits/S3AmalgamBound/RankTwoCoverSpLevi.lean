module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverSpAdj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverFamilies

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

variable {m : ℕ} {F : Type} [Field F]

noncomputable def leviSL (m : ℕ) (F : Type) [Field F] :
    Matrix.SpecialLinearGroup (Fin (m + 1)) F →* StatedSp (m + 1) F :=
  ((equivStatedSp (m + 1) F).toMonoidHom.comp TauCeti.GLSymplecticFin.leviHom).comp
    Matrix.SpecialLinearGroup.toGL

theorem leviSL_transvection {i j : Fin (m + 1)} (hij : i ≠ j) (c : F) :
    leviSL m F (Matrix.SpecialLinearGroup.transvection hij c) = elt (.difference i j hij) c := by
  simp only [leviSL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    TauCeti.toGL_transvection_eq_transvectionUnit]
  exact (elt_difference_eq_leviHom hij c).symm

theorem leviSL_injective : Function.Injective (leviSL m F) := by
  intro A B h
  have h1 := congrArg (mat (m + 1) F) h
  simp only [leviSL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, mat_equiv_leviHom] at h1
  have h2 := (Matrix.fromBlocks_inj.1 h1).1
  exact Subtype.ext h2

theorem leviSL_rankOne_le (i : Fin m) :
    (rankOne (SpecialLinear.rootDatum m F).rootGroup i).map (leviSL m F) ≤
      rankOne (rootDatum (m + 1) F).rootGroup i.castSucc := by
  have hne : i.castSucc ≠ i.succ := Fin.castSucc_lt_succ.ne
  have hk : (i.castSucc).val + 1 < m + 1 := by simp
  rw [Subgroup.map_le_iff_le_comap]
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · have hx' : x ∈ SpecialLinear.rootSubgroup m F hne := by
      rw [← SpecialLinear.rootGroup_eq m F hne (SpecialLinear.toStd_single m i)]
      exact hx
    obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup hne x).1 hx'
    rw [Subgroup.mem_comap, leviSL_transvection]
    refine Subgroup.mem_sup_left ?_
    have := elt_short_mem_pos hk c
    rw [elt_difference_congr (a' := i.castSucc) (b' := i.succ) rfl (Fin.ext (by simp)) _ hne c]
      at this
    exact this
  · have hneg : SpecialLinear.toStd m (-Pi.single i 1 : Fin m → ℤ) =
        Pi.single i.succ 1 - Pi.single i.castSucc 1 := by
      rw [SpecialLinear.toStd_neg, SpecialLinear.toStd_single, neg_sub]
    have hx' : x ∈ SpecialLinear.rootSubgroup m F hne.symm := by
      rw [← SpecialLinear.rootGroup_eq m F hne.symm hneg]
      exact hx
    obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup hne.symm x).1 hx'
    rw [Subgroup.mem_comap, leviSL_transvection]
    refine Subgroup.mem_sup_right ?_
    have := elt_short_mem_neg hk c
    rw [elt_difference_congr (a' := i.succ) (b' := i.castSucc) (Fin.ext (by simp)) rfl _
      hne.symm c] at this
    exact this

theorem not_isPSolvable_sp_of_sl [Finite F] (i j : Fin m)
    (hsl : ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(rankOne (SpecialLinear.rootDatum m F).rootGroup i ⊔
        rankOne (SpecialLinear.rootDatum m F).rootGroup j)) :
    ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(rankOne (rootDatum (m + 1) F).rootGroup i.castSucc ⊔
        rankOne (rootDatum (m + 1) F).rootGroup j.castSucc) := by
  intro h
  have hmap := not_isPSolvable_map_of_injective (leviSL_injective (m := m) (F := F)) hsl
  have hle : (rankOne (SpecialLinear.rootDatum m F).rootGroup i ⊔
      rankOne (SpecialLinear.rootDatum m F).rootGroup j).map (leviSL m F) ≤
      rankOne (rootDatum (m + 1) F).rootGroup i.castSucc ⊔
        rankOne (rootDatum (m + 1) F).rootGroup j.castSucc := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (leviSL_rankOne_le i) (leviSL_rankOne_le j)
  exact hmap (OrdinaryProofs.PSolvableClosure.isPSolvable_of_le (p := 3) h hle)

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
