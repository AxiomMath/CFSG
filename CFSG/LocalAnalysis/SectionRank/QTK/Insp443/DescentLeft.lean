module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.DescentConfig
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.DescentConcl
public import CFSG.Quasithin.Background.KnownMultTypes

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem isCyclic_sylow_of_isPSL_two_two {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsPSL 2 2 n X) {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (S : Sylow r X) :
    IsCyclic (S : Subgroup X) := by
  obtain ⟨⟨-, hn1, -, h22, -⟩, F, _, _, hF, ⟨e₀⟩⟩ := h
  have hn : 2 ≤ n := by
    by_contra hlt
    obtain rfl : n = 1 := by omega
    exact h22 rfl
  let e : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    e₀.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  let Sbar : Sylow r (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S
  have hbar : IsCyclic (Sbar : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :=
    psl_two_sylow_isCyclic_even hn hF hr2 Sbar
  have hmap : (Sbar : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) =
      (S : Subgroup X).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
  rw [hmap] at hbar
  exact (e.subgroupMap (S : Subgroup X)).isCyclic.mpr hbar

variable {K : Type} [Group K] [Finite K] {L V MK : Subgroup K}

theorem KConf.conclK_of_bar_psl2 (hK : KConf K L V MK)
    (hX : ∀ L' V' MK' : Subgroup (K ⧸ Subgroup.center K),
      KConfig (K ⧸ Subgroup.center K) L' V' MK' →
        ConclKLeft (K ⧸ Subgroup.center K) L' V' MK' ∧ ∃ n : ℕ, IsPSL 2 2 n (ModO2 L')) :
    ConclK K L V MK := by
  obtain ⟨hc, n, hpsl⟩ := hX _ _ _ hK.kConfig_bar
  have hLZ : L ⊓ Subgroup.center K = ⊥ := by
    refine hK.inf_center_eq_bot fun r hr hrZ S => ?_
    have : Fact r.Prime := ⟨hr⟩
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact hK.odd_card_center.not_two_dvd_nat hrZ
    exact isCyclic_sylow_of_isPSL_two_two hpsl hr2 S
  have hker := QuotientGroup.ker_mk' (Subgroup.center K)
  refine (conclKLeft_of_map (QuotientGroup.mk' (Subgroup.center K))
    (QuotientGroup.mk'_surjective _) hker.le ?_ hK.elemAbelian hK.le_normalizer ?_ hc).conclK
  · rw [hker]
    exact hK.odd_card_center
  · rw [hker]
    exact hLZ

end CFSG.SectionRank.QTK.Insp443
