module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.FusionW3Rep
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.CoverMonster

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS CFSG.Monster.Existence


@[expose] def MonsterLocalFourW3Rep : Prop :=
  ∃ w : ↥(cent tGriess), orderOf w = 2 ∧ w ∉ center ↥(cent tGriess) ∧
    (Nat.card ↥(centralizer ({w} : Set ↥(cent tGriess))) = babyCentOrder 2 ∨
      Nat.card ↥(centralizer ({w} : Set ↥(cent tGriess))) = 2 * babyCentOrder 2) ∧
    (center ↥(centralizer ({w} : Set ↥(cent tGriess)))).map
        (centralizer ({w} : Set ↥(cent tGriess))).subtype =
      zpowers w ⊔ zpowers (⟨tGriess, self_mem_cent tGriess⟩ : ↥(cent tGriess))

theorem twoBLocalFourW3Rep_of_monster (h : MonsterLocalFourW3Rep) : TwoBLocalFourW3Rep := by
  intro L _ _ hcov t ht ht2
  obtain ⟨ψ⟩ := hcov.nonempty_mulEquiv isTwoBCover_cent_tGriess
  have hψt : ψ t = ⟨tGriess, self_mem_cent tGriess⟩ := by
    apply eq_of_mem_center_cent_tGriess
    · rw [mem_center_iff]
      intro g
      have := mem_center_iff.1 ht (ψ.symm g)
      have h2 := congrArg ψ this
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
    · rw [MulEquiv.orderOf_eq]; exact ht2
  obtain ⟨w0, hw2, hwc, hcard, hZ⟩ := h
  refine ⟨ψ.symm w0, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact hw2
  · intro hmem
    apply hwc
    have h1 : ψ (ψ.symm w0) ∈ (center L).map ψ.toMonoidHom := Subgroup.mem_map_of_mem _ hmem
    rwa [RankThree.PartOne.Torsion37.center_map_mulEquiv ψ, MulEquiv.apply_symm_apply] at h1
  · rw [← Nat.card_congr (centralizerEquiv ψ.symm w0).toEquiv]
    exact hcard
  · rw [← map_center_centralizer ψ.symm w0, hZ, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers]
    have h3 : ψ.symm ⟨tGriess, self_mem_cent tGriess⟩ = t := by
      rw [← hψt, ψ.symm_apply_apply]
    exact congrArg (fun a => zpowers (ψ.symm w0) ⊔ zpowers a) h3

end CFSG.EvenSporadicStandard.TwoB
