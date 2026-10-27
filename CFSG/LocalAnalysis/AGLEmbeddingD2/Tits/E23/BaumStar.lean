module

public import CFSG.CGT.PushingUpLit.BHS5.JPart

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS5

section Baum

variable {G : Type} [Group G] [Finite G] {T V : Subgroup G} (hV : IsElemAbelian 2 V)

include hV in
theorem mem_omegaOneCenterOf_thompsonJ (hVT : V ≤ T) {v : G} (hv : v ∈ V)
    (hc : ∀ a ∈ thompsonJ T, a * v = v * a) : v ∈ omegaOneCenterOf (thompsonJ T) := by
  rw [← (omegaOne_centralizer_thompsonJ T).1]
  exact Subgroup.subset_closure ⟨⟨hVT hv, Subgroup.mem_centralizer_iff.2 hc⟩, hV.2 v hv⟩

theorem autI_baum_le_cenIn (hVT : V ≤ T) (hTN : T ≤ Subgroup.normalizer (V : Set G)) :
    autI hV (baum T) ≤ cenIn (autI hV T) (fixV (autI hV (thompsonJ T))) := by
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  intro φ hφ
  obtain ⟨g, hgB, rfl⟩ := (mem_autI hV).1 hφ
  refine ⟨(mem_autI hV).2 ⟨g, hgB.1, rfl⟩, fun u hu => ?_⟩
  have hc := (mem_fixV_autI hV (hJT.trans hTN) u).1 hu
  have huΩ := mem_omegaOneCenterOf_thompsonJ hV hVT (IntMod.val_mem u)
    (Subgroup.mem_centralizer_iff.1 hc)
  refine IntMod.val_injective ?_
  rw [convI_apply_val]
  have h2 := Subgroup.mem_centralizer_iff.1 hgB.2 _ huΩ
  rw [← h2, mul_inv_cancel_right]

theorem autI_baum_eq (hVT : V ≤ T) (hTN : T ≤ Subgroup.normalizer (V : Set G))
    (hcen : cenIn (autI hV T) (fixV (autI hV (thompsonJ T))) ≤ autI hV (thompsonJ T)) :
    autI hV (baum T) = autI hV (thompsonJ T) :=
  le_antisymm ((autI_baum_le_cenIn hV hVT hTN).trans hcen)
    (autI_mono hV (B6.thompsonJ_le_baum T))

end Baum

theorem not_strong_of_hyp51 {W : Type} [CommGroup W] [Finite W]
    {P T M : Subgroup (MulAut W)} (h : Hyp51 P T M) (hW : ∀ w : W, w ^ 2 = 1)
    {X : Subgroup (MulAut W)} (hXP : X ≤ P) : ∀ B, ¬ IsStrongFFStarOffender X B := by
  rintro B ⟨hB, hr⟩
  have hlt := (rAV_lt_one_iff hW hB.isA2).1 hr
  have hle := wt_le_offMax (hB.1.trans hXP) (offender_iff.1 hB).2
  rw [offMax_eq_card h hW] at hle
  have hwt : wt B = Nat.card B * Nat.card (fixV B) := rfl
  omega

end CFSG.AGLEmbeddingD2.Tits.E23
