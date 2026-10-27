module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426LieFourUnitary

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.RankThree.PartTwo.Sec4

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Lie


theorem exists_fourGroup_map_congr {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (A : Subgroup (MulAut G))
    (h : ∃ T : Subgroup H, IsElemAbelian 2 T ∧ Nat.card ↥T = 4 ∧
      (∀ α ∈ A.map (MulAut.congr e).toMonoidHom, Subgroup.map α.toMonoidHom T = T) ∧
      ∃ α ∈ A.map (MulAut.congr e).toMonoidHom, ∀ t ∈ T, ∃ s ∈ T, t = α s * s⁻¹) :
    ∃ T : Subgroup G, IsElemAbelian 2 T ∧ Nat.card ↥T = 4 ∧
      (∀ α ∈ A, Subgroup.map α.toMonoidHom T = T) ∧
      ∃ α ∈ A, ∀ t ∈ T, ∃ s ∈ T, t = α s * s⁻¹ := by
  obtain ⟨T, hT2, hTcard, hTinv, α', hα', hsurj⟩ := h
  refine ⟨T.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · exact IsElemAbelian.map hT2 e.symm.toMonoidHom
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hTcard
  · intro α hα
    have hα'A : MulAut.congr e α ∈ A.map (MulAut.congr e).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hα
    have hcomp : α.toMonoidHom.comp e.symm.toMonoidHom =
        e.symm.toMonoidHom.comp (MulAut.congr e α).toMonoidHom := by
      ext x
      simp [MulAut.congr_apply]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hTinv _ hα'A]
  · obtain ⟨α, hα, hαeq⟩ := Subgroup.mem_map.1 hα'
    refine ⟨α, hα, ?_⟩
    intro t ht
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
    obtain ⟨s', hs', hse⟩ := hsurj t' ht'
    refine ⟨e.symm s', Subgroup.mem_map_of_mem _ hs', ?_⟩
    rw [← hαeq] at hse
    have hse' : t' = MulAut.congr e α s' * s'⁻¹ := hse
    calc e.symm t' = e.symm (MulAut.congr e α s' * s'⁻¹) := by rw [hse']
      _ = α (e.symm s') * (e.symm s')⁻¹ := by simp [MulAut.congr_apply]

theorem l3AutFourFacts_holds : L3AutFourFacts := by
  intro S _ _ hmodel A hA hlay
  refine ⟨card_le_nine_mulAut_of_l3Model hmodel hA hlay, ?_⟩
  intro hcard
  rcases hmodel with ⟨K, hK, hKf, hmod, ⟨e⟩⟩ | ⟨K, hK, hKf, p, f, hp, hf, hmod, hcardK, ⟨e⟩⟩
  · let e' : S ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
      e.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 K).symm
    exact exists_fourGroup_map_congr e' A
      (exists_fourGroup_projectiveSL hmod
        (IsElemAbelian.map hA (MulAut.congr e').toMonoidHom)
        (layerTrivialOn_map_congr e' hlay)
        (by rw [Subgroup.card_map_of_injective (MulAut.congr e').injective, hcard]))
  · have hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
      ⟨hp, hf, by rw [hcardK, ← pow_mul, Nat.mul_comm]⟩
    let e' : S ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hF 3 :=
      e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hF (n := 3) (by norm_num)).symm
    exact exists_fourGroup_map_congr e' A
      (exists_fourGroup_unitaryPSU hF hmod
        (IsElemAbelian.map hA (MulAut.congr e').toMonoidHom)
        (layerTrivialOn_map_congr e' hlay)
        (by rw [Subgroup.card_map_of_injective (MulAut.congr e').injective, hcard]))

end CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

end
