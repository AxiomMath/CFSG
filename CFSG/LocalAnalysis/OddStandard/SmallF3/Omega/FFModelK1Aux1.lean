module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Block
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}
theorem ff_commSp_blockHom_inl {t : OGroup Q} (htt : t * t = 1)
    (a : OGroup (Q.restrict (fixSp t))) :
    commSp (blockHom htt (a, 1)) = (commSp a).map (fixSp t).subtype := by
  ext v
  rw [Submodule.mem_map]
  constructor
  · intro hv
    obtain ⟨x, hx⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hv
    obtain ⟨w, u, rfl⟩ := exists_fixSp_add_commSp htt x
    refine ⟨(a : fixSp t ≃ₗ[ZMod 3] fixSp t) w - w, ?_, ?_⟩
    · exact CFSG.RankThree.OrthogonalInvolutions.sub_mem_commSpace _ _
    · rw [← hx]
      change (fixSp t).subtype ((a : fixSp t ≃ₗ[ZMod 3] fixSp t) w - w) = _
      rw [LinearMap.map_sub]
      have h1 : ((blockHom htt (a, 1) : OGroup Q) : V ≃ₗ[ZMod 3] V) ((w : V) + (u : V)) =
          (((a : fixSp t ≃ₗ[ZMod 3] fixSp t) w : fixSp t) : V) + (u : V) := by
        rw [blockHom_apply htt]
        rfl
      rw [h1]
      change (((a : fixSp t ≃ₗ[ZMod 3] fixSp t) w : fixSp t) : V) - (w : V) = _
      abel
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨u, hu⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hy
    refine CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mpr ⟨(u : V), ?_⟩
    have happ := blockHom_apply htt (a, 1) u 0
    have h1 : ((blockHom htt (a, 1) : OGroup Q) : V ≃ₗ[ZMod 3] V) (u : V) =
        (((a : fixSp t ≃ₗ[ZMod 3] fixSp t) u : fixSp t) : V) := by
      have h0 : ((u : V) + ((0 : commSp t) : V)) = (u : V) := by simp
      rw [← h0, happ]
      simp
    rw [h1, ← hu]
    rfl

theorem ff_invType_blockHom_inl (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    {a : OGroup (Q.restrict (fixSp t))} (haa : a * a = 1) :
    invType (blockHom htt (a, 1)) = invType a := by
  have hbb : blockHom htt (a, 1) * blockHom htt (a, 1) = 1 := by
    have hmul : (a, 1) * (a, 1) = (1 : OGroup (Q.restrict (fixSp t)) ×
        OGroup (Q.restrict (commSp t))) := by
      rw [Prod.mk_mul_mk, haa]
      rfl
    rw [← map_mul, hmul, map_one]
  have hQU := nondegenerate_restrict_fixSp hQ htt
  have hmap := ff_commSp_blockHom_inl htt a
  simp only [invType]
  apply Prod.ext
  · simp only [invDim]
    rw [hmap]
    exact Submodule.finrank_map_subtype_eq (fixSp t) (commSp a)
  · simp only [invSign]
    let e : commSp a ≃ₗ[ZMod 3] commSp (blockHom htt (a, 1)) :=
      (Submodule.equivMapOfInjective (fixSp t).subtype (Submodule.injective_subtype _)
        (commSp a)).trans (LinearEquiv.ofEq _ _ hmap.symm)
    have hequiv : ((Q.restrict (fixSp t)).restrict (commSp a)).Equivalent
        (Q.restrict (commSp (blockHom htt (a, 1)))) := by
      refine ⟨⟨e, ?_⟩⟩
      intro y
      rfl
    exact (quadSign_congr (nondegenerate_restrict_commSp hQU haa) hequiv).symm

theorem ff_blockHom_inl_commute {t : OGroup Q} (htt : t * t = 1)
    (a : OGroup (Q.restrict (fixSp t))) :
    blockHom htt (a, 1) * t = t * blockHom htt (a, 1) := by
  calc blockHom htt (a, 1) * t
      = blockHom htt (a, 1) * blockHom htt (1, piOrth (Q.restrict (commSp t))) := by
          rw [blockHom_one_piOrth htt]
    _ = blockHom htt ((a, 1) * (1, piOrth (Q.restrict (commSp t)))) := by rw [map_mul]
    _ = blockHom htt ((1, piOrth (Q.restrict (commSp t))) * (a, 1)) := by
          congr 1
    _ = blockHom htt (1, piOrth (Q.restrict (commSp t))) * blockHom htt (a, 1) := by
          rw [map_mul]
    _ = t * blockHom htt (a, 1) := by rw [blockHom_one_piOrth htt]


end CFSG.OddStandard.SmallF3.Omega
