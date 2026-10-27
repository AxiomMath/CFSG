module

public import CFSG.ClassicalInvolution.Q3.Q3EXD4FLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.RouteD.Gaps (locMk)


section CA

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem ca_of_cliques_comm3 (hnab : ∃ x y : G, x * y ≠ y * x) (S : D4Ctx3 G K z 4)
    {N J : Subgroup G} (hN : N ∈ conjClass3 K) (hJ : J ∈ conjClass3 K)
    (hJc : ∀ L ∈ outerSet (conjClass3 K) N, Commutes J L) {zN zJ : G}
    (hzN : IsClassicalMember3 N zN) (hzJ : IsClassicalMember3 J zJ)
    (hzcomm : zN * zJ = zJ * zN) :
    cnbhd (conjClass3 K) J = cnbhd (conjClass3 K) N := by
  classical
  by_contra hne
  set Ω := conjClass3 K with hΩdef
  have hΩ : InClass3 Ω := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  obtain ⟨M, hM⟩ := outerSet_nonempty_of_shape3 S hN
  have hMΩ : M ∈ Ω := hM.1.1
  have hNM : N ∈ outerSet Ω M := mem_outerSet_symm hN hM
  have hJN : J ≠ N := fun h => hne (by rw [h])
  have hnotcomm : ¬ Commutes J N := by
    intro hc
    have hJin : J ∈ outerSet Ω N := ⟨⟨hJ, Or.inr hc⟩, hne⟩
    obtain ⟨L, hL, -, hnc⟩ := exists_noncommuting_outer3 S hN hJin
    exact hnc (hJc L hL)
  have hJM : J ∈ outerSet Ω M := by
    refine ⟨⟨hJ, Or.inr (hJc M hM)⟩, fun h => ?_⟩
    obtain ⟨L, hL, hLM, hnc⟩ := exists_noncommuting_outer3 S hN hM
    have hLJ : L ∈ cnbhd Ω J := ⟨hL.1.1, Or.inr (hJc L hL).symm⟩
    rw [h] at hLJ
    exact hnc (hLJ.2.resolve_left hLM).symm
  obtain ⟨w, hw, hP1, hO3, ι, hι, D, i₁, hcard, hk, hrest⟩ := exists_D4At3 S hMΩ
  have hout := outerSet_eq_compMembers3 hΩ hex hw hMΩ hP1 hO3 (single_class_of_mem3 hMΩ) D hk
    hrest
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hpc := powCop3_of_kind hk (trivial : IsFundTag (.POmegaPlus : StatedLieTag)) hadm
    (by decide) (by decide)
  have hgen3 := gen3_of_kind hk
  have hk3 := ker_k3_of_powCop3 hpc (D.hom i₁) (D.ker_le_center i₁)
  have hsc := singleClass_of_kind hk (trivial : IsFundTag (.POmegaPlus : StatedLieTag)) hadm
    (by decide) (by decide)
  have hNc : N ∈ compMembers3 Ω w D i₁ := hout ▸ hNM
  have hJc' : J ∈ compMembers3 Ω w D i₁ := hout ▸ hJM
  obtain ⟨RN, hRN⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hNc
  obtain ⟨RJ, hRJ⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hJc'
  have hne' : RJ ≠ RN := fun h => hJN (corr_unique_right3 hΩ hex hP1 hO3 hRJ (h ▸ hRN))
  have hnc' : ¬ Commutes RN RJ := fun h =>
    hnotcomm ((corr_commutes3 hΩ hex hP1 hO3 hpc hRN hRJ).mpr h).symm
  have hzNY : zN ∈ locLayer Ω w := le_centralizingLayer hRN.1 hzN.mem
  have hzJY : zJ ∈ locLayer Ω w := le_centralizingLayer hRJ.1 hzJ.mem
  obtain ⟨cN, hcNR, hcNz, hcNimg, hcN1⟩ := exists_central_preimage3 hgen3 hk3 hRN hzN hzNY
  obtain ⟨cJ, hcJR, hcJz, hcJimg, hcJ1⟩ := exists_central_preimage3 hgen3 hk3 hRJ hzJ hzJY
  have hcomm : cN * cJ * cN⁻¹ * cJ⁻¹ ∈ Subgroup.center (D.kind i₁).G := by
    refine D.ker_le_center i₁ ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcNimg, hcJimg]
    have hab : locMk Ω w ⟨zN, hzNY⟩ * locMk Ω w ⟨zJ, hzJY⟩ =
        locMk Ω w ⟨zJ, hzJY⟩ * locMk Ω w ⟨zN, hzNY⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hzcomm
    rw [hab, mul_inv_cancel_right, mul_inv_cancel]
  have hgen := generate_of_comm_of_kind hk hRN.2.1 hRJ.2.1 hne' hnc' hcNR hcNz hcN1 hcJR hcJz hcJ1
    hcomm
  set 𝒮 := {S' : Subgroup (D.kind i₁).G | S' ∈ (D.kind i₁).fund ∧
    (S' = RN ∨ Commutes S' RN ∨ S' = RJ ∨ Commutes S' RJ)} with h𝒮
  have hgen' : (⨆ s : ↥𝒮, s.1) = ⊤ := by
    rw [← hgen]
    exact (iSup_subtype' (p := fun S' => S' ∈ 𝒮) (f := fun S' _ => S')).symm
  choose T hT using fun s : ↥𝒮 => exists_corr_right3 hΩ D hsc s.2.1
  have hTout : ∀ s : ↥𝒮, T s ∈ outerSet Ω M := fun s => by
    rw [hout]
    exact ⟨(hT s).1, (hT s).2.2 ▸ Subgroup.map_le_range _ _⟩
  have hTB : ∀ s : ↥𝒮, ∀ L ∈ outerSet Ω N, Commutes (T s) L := by
    intro s L hL
    have hLne : ∀ Y, cnbhd Ω Y = cnbhd Ω N → L ≠ Y := fun Y hY h => hL.2 (by rw [h, hY])
    rcases s.2.2 with h | h | h | h
    · have hTN : T s = N := corr_unique_right3 hΩ hex hP1 hO3 (hT s) (h ▸ hRN)
      rw [hTN]
      exact (hL.1.2.resolve_left (hLne N rfl)).symm
    · have hc : Commutes (T s) N := (corr_commutes3 hΩ hex hP1 hO3 hpc (hT s) hRN).mpr h
      have htw := commutes_outer_eq_twin3 S hN hM (hTout s) hc
      have hLmem : L ∈ cnbhd Ω (T s) := by
        rw [htw]
        exact hL.1
      exact (hLmem.2.resolve_left (hLne (T s) htw)).symm
    · have hTJ : T s = J := corr_unique_right3 hΩ hex hP1 hO3 (hT s) (h ▸ hRJ)
      rw [hTJ]
      exact hJc L hL
    · have hc : Commutes (T s) J := (corr_commutes3 hΩ hex hP1 hO3 hpc (hT s) hRJ).mpr h
      have hMJ : M ∈ outerSet Ω J := mem_outerSet_symm hMΩ hJM
      have htw := commutes_outer_eq_twin3 S hJ hMJ (hTout s) hc
      have hLmem : L ∈ cnbhd Ω (T s) := by
        rw [htw]
        exact ⟨hL.1.1, Or.inr (hJc L hL).symm⟩
      refine (hLmem.2.resolve_left fun hLT => ?_).symm
      have hNmem : N ∈ cnbhd Ω (T s) := by
        rw [← hLT]
        exact mem_cnbhd_symm hN hL.1
      rw [htw] at hNmem
      rcases hNmem.2 with hNJ | hNJ
      · exact hJN hNJ.symm
      · exact hnotcomm hNJ.symm
  set Θ := outerGen Ω N with hΘ
  have hTle : ∀ s : ↥𝒮, T s ≤ Subgroup.centralizer (Θ : Set G) := by
    intro s g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hΘg : Θ ≤ Subgroup.centralizer ({g} : Set G) := iSup₂_le fun L hL y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hTB s L hL g hg y hy).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hΘg hh)
  have hΞ : outerGen Ω M ≤ Subgroup.centralizer (Θ : Set G) := by
    refine iSup₂_le fun L hL => ?_
    have hLc : L ∈ compMembers3 Ω w D i₁ := hout ▸ hL
    have := le_iSup_of_model_generates3 hΩ hex hP1 hO3 T (fun s => s.1) hT hgen' hLc
    exact this.trans (iSup_le hTle)
  have htop : Subgroup.normalizer (Θ : Set G) = ⊤ :=
    eq_top_of_outerGen_le3 S hN hM Subgroup.le_normalizer
      (hΞ.trans (Subgroup.centralizer_le_normalizer _))
  have hnormal : Θ.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Θ with hbot | htop'
  · obtain ⟨zM, hzM⟩ := hΩ.classical M hMΩ
    have hmem : zM ∈ Θ := le_outerGen hM hzM.mem
    rw [hbot, Subgroup.mem_bot] at hmem
    have h2 := hzM.orderOf_eq_two
    rw [hmem, orderOf_one] at h2
    omega
  · obtain ⟨zN', hzN'⟩ := hΩ.classical N hN
    have hzc : zN' ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro h
      have hΘg : Θ ≤ Subgroup.centralizer ({zN'} : Set G) := iSup₂_le fun L hL y hy =>
        Subgroup.mem_centralizer_singleton_iff.mpr
          ((hL.1.2.resolve_left (fun h' => hL.2 (by rw [h']))) y hy zN' hzN'.mem)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hΘg (htop' ▸ Subgroup.mem_top h))
    rw [center_eq_bot_of_simple hnab, Subgroup.mem_bot] at hzc
    have h2 := hzN'.orderOf_eq_two
    rw [hzc, orderOf_one] at h2
    omega

end CA

end CFSG.ClassicalInvolution.Q3.Q3W.EX
