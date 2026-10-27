module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL3Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL3Aut
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KACover
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3GraphOrth

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.KGroups.L3Eps
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ComponentClassification.Burgoyne.PSL
  CFSG.ComponentClassification
open scoped MatrixGroups

section GraphFive

variable {F : Type} [Field F] [Finite F]

theorem kaL3_graph_five (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (B : GL (Fin 3) F)
    (hB : (B : Matrix (Fin 3) (Fin 3) F)ᵀ = B) : KAAll (conjAut 3 F B * dualAut 3 F) := by
  set α : MulAut (projectiveSL 3 F) := conjAut 3 F B * dualAut 3 F with hα
  set R : GL (Fin 3) F := B⁻¹ with hR
  have hRs : (R : Matrix (Fin 3) (Fin 3) F)ᵀ = R := transpose_inv_of_symm B hB
  have hΩ := fl3GraphOrth_of_omega3 hodd h5 R hRs
  have h4 : 4 ≤ Nat.card F := by omega
  obtain ⟨ι, hι⟩ := exists_sl2_hom hodd h5 R hRs
  have hq : CFSG.IsQuasisimple SL(2, F) := isQuasisimple_sl2c h4
  have hfixΩ : ∀ g ∈ omega3 R, α (proj 3 F g) = proj 3 F g := by
    intro g hg
    rw [hα, conjAut_mul_dualAut_proj]
    congr 1
    exact (graphLift_eq_iff B g).2 (hΩ.isometry hg)
  have hnormΩ : ∀ g ∈ isometrySL 3 R,
      g ∈ normalizer ((omega3 R : Subgroup SL(3, F)) : Set SL(3, F)) := by
    intro g hg
    have hgI : SpecialLinearGroup.toGL g ∈ CatalogueBGraphForm.isometryGroup 3 F R := hg
    have hN := ka_normalizer_commutator (Subgroup.le_normalizer hgI)
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro s
    show SpecialLinearGroup.toGL s ∈ ⁅CatalogueBGraphForm.isometryGroup 3 F R,
        CatalogueBGraphForm.isometryGroup 3 F R⁆ ↔
      SpecialLinearGroup.toGL (g * s * g⁻¹) ∈ ⁅CatalogueBGraphForm.isometryGroup 3 F R,
        CatalogueBGraphForm.isometryGroup 3 F R⁆
    rw [map_mul, map_mul, map_inv]
    exact hN _
  refine ka_all_of_normal_comm
    (ka_conj_injective_of_center_bot center_projectiveSL_three_eq_bot)
    ((omega3 R).map (proj 3 F)) ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact hfixΩ g hg
  · exact ka_cover_map_perfect (proj 3 F) (Subgroup.isPerfect_iff.mp hΩ.perfect)
  · intro x hx
    obtain ⟨g, rfl⟩ := proj_surjective 3 F x
    rw [mem_fixSub, hα, conjAut_mul_dualAut_proj] at hx
    obtain ⟨g', hg', hgg'⟩ := exists_isometrySL_rep hB hx
    rw [← hgg']
    exact ka_map_mem_normalizer (proj 3 F) (hnormΩ g' hg')
  · intro p hp hp2 M hML hMp hMn
    have hr : ((proj 3 F).comp ι).range = (omega3 R).map (proj 3 F) := by
      rw [MonoidHom.range_comp, hι]
    have := ka_central_of_quasisimple_image ((proj 3 F).comp ι) hq hp M (hr ▸ hML) hMp
      (fun l hl => hMn l (hr ▸ hl))
    intro m hm l hl
    exact this m hm l (hr ▸ hl)
  · intro p hp hp2 e hord _ hfix
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hord) ⟨e, Subgroup.mem_zpowers e⟩
    rw [Subgroup.orderOf_mk] at hm
    have hβ : e ^ (p ^ m) = 1 := by rw [← hm]; exact pow_orderOf_eq_one e
    exact kaL3_aut_fixing_trivial (fun A σ h => semiSL_fix_of_perfect A σ hΩ.perfect h) hΩ.comm
      (fun σ _ h => hΩ.traces σ h) ((hp.odd_of_ne_two hp2).pow) hβ
      (fun g hg => hfix _ ⟨g, hg, rfl⟩)

end GraphFive

section GraphThree

variable {F : Type} [Field F] [Finite F]

theorem kaL3_graph_three (hF3 : Nat.card F = 3) (B : GL (Fin 3) F)
    (hB : (B : Matrix (Fin 3) (Fin 3) F)ᵀ = B) : KAAll (conjAut 3 F B * dualAut 3 F) := by
  have hodd : Odd (Nat.card F) := by rw [hF3]; decide
  set α : MulAut (projectiveSL 3 F) := conjAut 3 F B * dualAut 3 F with hα
  set R : GL (Fin 3) F := B⁻¹ with hR
  have hRs : (R : Matrix (Fin 3) (Fin 3) F)ᵀ = R := transpose_inv_of_symm B hB
  obtain ⟨ι, hiso, hirr, hcomm, hker⟩ := exists_ad_hom3 hodd R hRs
  have hZ : scalars 3 F = ⊥ := fl3g_scalars_eq_bot_of_card_three hF3
  have hΩiso : ι.range ≤ isometrySL 3 R := by
    rintro _ ⟨S, rfl⟩
    exact hiso S
  have hfixΩ : ∀ g ∈ ι.range, α (proj 3 F g) = proj 3 F g := by
    intro g hg
    rw [hα, conjAut_mul_dualAut_proj]
    congr 1
    exact (graphLift_eq_iff B g).2 (hΩiso hg)
  have hprojinj : Function.Injective (proj 3 F) := by
    intro a b hab
    have := proj_eq_proj_iff.1 hab
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at this
    exact this
  have hirr' : ∀ W : Submodule F (Fin 3 → F),
      (∀ g ∈ ι.range, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => hirr W fun S v hv => hW (ι S) (MonoidHom.mem_range.2 ⟨S, rfl⟩) v hv
  have h12 : 12 ∣ Nat.card ((ι.range).map (proj 3 F)) := by
    have h1 : Nat.card ((ι.range).map (proj 3 F)) = Nat.card ι.range :=
      (Nat.card_congr (ι.range.equivMapOfInjective (proj 3 F) hprojinj).toEquiv).symm
    rw [h1]
    exact fl3g_twelve_dvd_card_range hF3 ι hker
  refine ka_all_of_X0_bot (ka_conj_injective_of_center_bot center_projectiveSL_three_eq_bot)
    ((ι.range).map (proj 3 F)) ?_ ?_ ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact hfixΩ g hg
  · refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      exact fun x hx => hx.1
    · rintro _ ⟨_, ⟨S, rfl⟩, rfl⟩
      have hS : S ∈ Subgroup.closure {y : SL(2, F) | orderOf y = 3} := by
        rw [CFSG.LieType.HighestRoot.closure_orderOf_three_eq_top hF3]
        exact Subgroup.mem_top S
      induction hS using Subgroup.closure_induction with
      | mem y hy =>
        have hmem : proj 3 F (ι y) ∈ (ι.range).map (proj 3 F) :=
          Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.2 ⟨y, rfl⟩)
        refine Subgroup.subset_closure ⟨hmem, ?_⟩
        have hd : orderOf ((proj 3 F).comp ι y) ∣ orderOf y :=
          orderOf_map_dvd ((proj 3 F).comp ι) y
        rw [hy] at hd
        exact Odd.of_dvd_nat (by decide) hd
      | one =>
        rw [map_one, map_one]
        exact one_mem _
      | mul a b _ _ ha hb =>
        rw [map_mul, map_mul]
        exact mul_mem ha hb
      | inv a _ ha =>
        rw [map_inv, map_inv]
        exact inv_mem ha
  · intro p hp hp2 X _ hXp hXn
    have : Fact p.Prime := ⟨hp⟩
    let e : ↥(⊤ : Subgroup (projectiveSL 3 F)) ≃* projectiveSL 3 F := Subgroup.topEquiv
    have hnorm : ∀ k ∈ subgroupOfEquiv e ((ι.range).map (proj 3 F)),
        (k : projectiveSL 3 F) ∈ normalizer ((X ⊓ ⊤ : Subgroup (projectiveSL 3 F)) :
          Set (projectiveSL 3 F)) := by
      intro k hk
      rw [mem_subgroupOfEquiv] at hk
      rw [inf_top_eq]
      exact hXn _ hk
    have hX0 : X ⊓ ⊤ = ⊥ := by
      by_cases hpF : p ∣ Nat.card F
      · have : CharP F p := fl3g_charP_of_dvd_card hpF
        exact fl3g_X0_bot_of_char e hirr' hXp hnorm
      · by_contra hne
        have hne' : X ≠ ⊥ := by
          intro h
          apply hne
          rw [h, bot_inf_eq]
        have hTcard : Nat.card (subgroupOfEquiv e ((ι.range).map (proj 3 F))) =
            Nat.card ((ι.range).map (proj 3 F)) := fl3g_card_subgroupOfEquiv e _
        refine fl3_three_sylow_false hF3 e hp2 hpF hXp hne' le_top
          (subgroupOfEquiv e ((ι.range).map (proj 3 F))) ?_ (hTcard ▸ h12)
        intro k hk
        have := hnorm k hk
        rw [inf_top_eq, Subgroup.mem_normalizer_iff] at this
        rw [Subgroup.mem_normalizer_iff]
        intro y
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact this (y : projectiveSL 3 F)
    rw [inf_top_eq] at hX0
    exact hX0
  · intro p hp hp2 e hord hfix
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hord) ⟨e, Subgroup.mem_zpowers e⟩
    rw [Subgroup.orderOf_mk] at hm
    have hβ : e ^ (p ^ m) = 1 := by rw [← hm]; exact pow_orderOf_eq_one e
    exact kaL3_aut_fixing_trivial (fun A σ h => semiSL_fix_of_center_bot A σ hZ h)
      (fun T hT => hcomm T fun S => hT (ι S) (MonoidHom.mem_range.2 ⟨S, rfl⟩))
      (fun σ _ _ => fl3g_ringEquiv_eq_one_of_card_three hF3 σ) ((hp.odd_of_ne_two hp2).pow) hβ
      (fun g hg => hfix _ ⟨g, hg, rfl⟩)

end GraphThree

section Graph

variable {F : Type} [Field F] [Finite F]

theorem kaL3_graph (hodd : Odd (Nat.card F)) (h3 : 3 ≤ Nat.card F) (B : GL (Fin 3) F)
    (hB : (B : Matrix (Fin 3) (Fin 3) F)ᵀ = B) : KAAll (conjAut 3 F B * dualAut 3 F) := by
  by_cases h5 : 5 ≤ Nat.card F
  · exact kaL3_graph_five hodd h5 B hB
  · exact kaL3_graph_three (by obtain ⟨k, hk⟩ := hodd; omega) B hB

end Graph

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
