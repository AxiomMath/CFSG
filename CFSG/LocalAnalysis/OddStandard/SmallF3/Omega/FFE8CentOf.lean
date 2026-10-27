module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8CentModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8CentOfAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L771In

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem asc82E8Cent_of (hP : Asc82Tab6P) : Asc82E8Cent := by
  intro G _ _ K hK E z ν hE hEK hzE hzI hνK hν3 hνN hfix
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff_exists_model_six_plus hK
  have hz0 : Subgroup.center ↥K = ⊥ := by
    have h1 := hP.center_triv G K hK
    rw [centerIn] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp h1
  haveI := ffOutFFE8Tr_finite_projSim Q
  have hρ : Function.Injective (ffOutFFE8TrRho hQ e) := ffOutFFE8TrRho_injective hQ hz0 e
  have hrange := ffOutFFE8TrRho_range hQ e
  have hzT := ffOutFFE8TrCent_simHasType hK hQ hdim hsgn e (hEK hzE) hzI
  have h := ffOutFFE8Tr_sdata hQ hdim hsgn hz0 e hE hEK hzE hνK hν3 hνN hfix hzT
  obtain ⟨⟨hab, hcard⟩, P', hP'syl, hP'E16⟩ := ffE8_model_cent hQ hdim hsgn h
  rw [ffOutFFE8TrThetaImg_eq hQ hdim hsgn e hEK] at hab hcard hP'E16
  have hP'le : P' ≤ (ffOutFFE8TrRho hQ e).range := by
    rw [hrange]
    exact hP'syl.1
  have hE16 := ffOutFFE8TrPull_normalE16 hρ hP'le hP'E16
  rw [← hrange, ffOutFFE8TrCent_pull_inf hρ hEK] at hE16
  have hcomm : ∀ x ∈ normalizer (K : Set G), (∀ g ∈ E, x * g = g * x) →
      ∀ b ∈ K ⊓ centralizer (E : Set G), x * b = b * x := by
    intro x hxN hx b hb
    obtain ⟨hbK, hbC⟩ := Subgroup.mem_inf.mp hb
    have h1 := ffOutFFE8TrCent_theta_mem_centralizer hQ hdim hsgn hz0 e hxN hx
    have h2 : ffOutFFE8TrRho hQ e ⟨b, hbK⟩ ∈
        centralizer (ffImg (ffOutFFE8TrRho hQ e) E : Set (ProjSim Q)) :=
      (ffOutFFE8TrCent_mem_centralizer_iff hρ hEK ⟨b, hbK⟩).mpr hbC
    have h3 := congrArg Subtype.val (hab.1.is_comm.comm
      ⟨ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩, h1⟩ ⟨ffOutFFE8TrRho hQ e ⟨b, hbK⟩, h2⟩)
    exact (ff6p_commute_iff hQ hdim hsgn hz0 e hxN ⟨b, hbK⟩).mpr h3
  refine ⟨⟨ffOutFFE8TrPull (ffOutFFE8TrRho hQ e) P', ?_, hE16,
    le_inf hEK (Subgroup.le_centralizer_iff_isMulCommutative.mpr hE.1.1)⟩, hcomm, ?_⟩
  · exact ffOutFFE8TrPull_sylow hρ (by rw [hrange]; exact hP'syl)
  · let θH : ↥(normalizer (K : Set G) ⊓ centralizer (E : Set G)) →* ProjSim Q :=
      (ffTheta6P hQ hdim hsgn e).comp (Subgroup.inclusion inf_le_left)
    have hker : θH.ker = (centralizer (K : Set G)).subgroupOf
        (normalizer (K : Set G) ⊓ centralizer (E : Set G)) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact ff6p_theta_eq_one_iff hK hQ hdim hsgn e (Subgroup.mem_inf.mp x.2).1
    have hrng : θH.range ≤ centralizer (ffImg (ffOutFFE8TrRho hQ e) E : Set (ProjSim Q)) := by
      rintro _ ⟨x, rfl⟩
      exact ffOutFFE8TrCent_theta_mem_centralizer hQ hdim hsgn hz0 e (Subgroup.mem_inf.mp x.2).1
        (fun g hg => ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp x.2).2) g hg).symm)
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
    exact (Subgroup.card_le_of_le hrng).trans hcard

end CFSG.OddStandard.SmallF3.Omega
