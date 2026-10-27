module

public import CFSG.CGT.PushingUpLit.BHS6.Conj

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6

variable {Γ : Type} [Group Γ] [Finite Γ] {G T T' : Subgroup Γ}

theorem thompsonJ_le_thompsonJ_of_le_sylow (hT : IsSylowTwoOf T G) (hT' : IsSylowTwoOf T' G)
    (h : thompsonJ T ≤ T') : thompsonJ T ≤ thompsonJ T' := by
  obtain ⟨x, hx, hxT⟩ := B6.isSylowTwoOf_exists_conj hT hT'
  refine iSup₂_le fun A hA => ?_
  refine B6.le_thompsonJ ⟨(B6.le_thompsonJ hA).trans h, hA.2.1, fun B hBT' hB => ?_⟩
  have hB' : B6.conjSub x⁻¹ B ≤ T := by
    have := (B6.conjSub x⁻¹).le_iff_le.mpr hBT'
    rwa [hxT, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one] at this
  have h1 := hA.2.2 _ hB' (B6.isElemAbelian_conjSub hB x⁻¹)
  rwa [B6.card_conjSub] at h1

theorem baum_eq_of_le_sylow (hT : IsSylowTwoOf T G) (hT' : IsSylowTwoOf T' G)
    (h : baum T ≤ T') : baum T' = baum T := by
  obtain ⟨x, hx, hxT⟩ := B6.isSylowTwoOf_exists_conj hT hT'
  have hJT : thompsonJ T ≤ T' := (B6.thompsonJ_le_baum T).trans h
  have hJ : thompsonJ T ≤ thompsonJ T' := thompsonJ_le_thompsonJ_of_le_sylow hT hT' hJT
  have hJ' : thompsonJ T = thompsonJ T' := by
    refine Subgroup.eq_of_le_of_card_ge hJ ?_
    rw [hxT, B6.thompsonJ_conjSub]
    exact (B6.card_conjSub _ _).le
  have hB : baum T ≤ baum T' := by
    refine le_inf h ?_
    rw [← hJ']
    exact (inf_le_right : baum T ≤ _)
  refine (Subgroup.eq_of_le_of_card_ge hB ?_).symm
  rw [hxT, b6_conjSub_eq, baum_conjSub]
  exact (B6.card_conjSub _ _).le

theorem mem_normalizer_baum_of_pGroup (hT : IsSylowTwoOf T G) {P : Subgroup Γ}
    (hP : IsPGroup 2 P) (hPG : P ≤ G) (hBP : baum T ≤ P) {g : Γ} (hg : g ∈ G)
    (hgP : g ∈ Subgroup.normalizer (P : Set Γ)) : g ∈ Subgroup.normalizer (baum T : Set Γ) := by
  obtain ⟨T₁, hT₁, hPT₁⟩ := B6.exists_isSylowTwoOf_ge hP hPG
  have hT₂ : IsSylowTwoOf (A1b.conjSub g T₁) G := isSylowTwoOf_conjSub_of_mem hT₁ hg
  have hPT₂ : P ≤ A1b.conjSub g T₁ := by
    have := A1b.conjSub_mono g hPT₁
    have e : A1b.conjSub g P = P := B6.conjSub_eq_self hgP
    rwa [e] at this
  have h1 : baum T₁ = baum T := baum_eq_of_le_sylow hT hT₁ (hBP.trans hPT₁)
  have h2 : baum (A1b.conjSub g T₁) = baum T := baum_eq_of_le_sylow hT hT₂ (hBP.trans hPT₂)
  rw [baum_conjSub, h1] at h2
  exact BHS.mem_normalizer_of_conjSub_eq h2

end CFSG.CGT.PushingUpLit.BHS7
