module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2BlockInr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem commSp_blockInr {s : OGroup Q} (hs : s * s = 1) (b : OGroup (Q.restrict (commSp s))) :
    commSp (blockInr hs b) = (commSp b).map (commSp s).subtype := by
  ext v
  rw [Submodule.mem_map]
  constructor
  · intro hv
    obtain ⟨x, hx⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hv
    obtain ⟨w, u, rfl⟩ := exists_fixSp_add_commSp hs x
    have happ := blockHom_apply hs (1, b) w u
    refine ⟨(b : commSp s ≃ₗ[ZMod 3] commSp s) u - u, ?_, ?_⟩
    · exact CFSG.RankThree.OrthogonalInvolutions.sub_mem_commSpace _ _
    · rw [← hx]
      change (commSp s).subtype ((b : commSp s ≃ₗ[ZMod 3] commSp s) u - u) = _
      rw [LinearMap.map_sub]
      have h1 : ((blockInr hs b : OGroup Q) : V ≃ₗ[ZMod 3] V) ((w : V) + (u : V)) =
          (w : V) + (((b : commSp s ≃ₗ[ZMod 3] commSp s) u : commSp s) : V) := by
        rw [blockInr_apply, happ]
        rfl
      rw [h1]
      change (((b : commSp s ≃ₗ[ZMod 3] commSp s) u : commSp s) : V) - (u : V) = _
      abel
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨u, hu⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hy
    refine CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mpr ⟨(u : V), ?_⟩
    have happ := blockHom_apply hs (1, b) 0 u
    have h1 : ((blockInr hs b : OGroup Q) : V ≃ₗ[ZMod 3] V) ((u : V)) =
        (((b : commSp s ≃ₗ[ZMod 3] commSp s) u : commSp s) : V) := by
      have h0 : (((0 : fixSp s) : V) + (u : V)) = (u : V) := by simp
      rw [blockInr_apply, ← h0, happ]
      simp
    rw [h1, ← hu]
    rfl

theorem invType_blockInr (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    {b : OGroup (Q.restrict (commSp s))} (hb : b * b = 1) :
    invType (blockInr hs b) = invType b := by
  have hbb : blockInr hs b * blockInr hs b = 1 := by rw [← map_mul, hb, map_one]
  have hQU := nondegenerate_restrict_commSp hQ hs
  have hmap := commSp_blockInr hs b
  simp only [invType]
  apply Prod.ext
  · simp only [invDim]
    rw [hmap]
    exact Submodule.finrank_map_subtype_eq (commSp s) (commSp b)
  · simp only [invSign]
    let e : commSp b ≃ₗ[ZMod 3] commSp (blockInr hs b) :=
      (Submodule.equivMapOfInjective (commSp s).subtype (Submodule.injective_subtype _)
        (commSp b)).trans (LinearEquiv.ofEq _ _ hmap.symm)
    have hequiv : ((Q.restrict (commSp s)).restrict (commSp b)).Equivalent
        (Q.restrict (commSp (blockInr hs b))) := by
      refine ⟨⟨e, ?_⟩⟩
      intro y
      rfl
    exact (quadSign_congr (nondegenerate_restrict_commSp hQU hb) hequiv).symm

end CFSG.OddStandard.SmallF3.Omega
