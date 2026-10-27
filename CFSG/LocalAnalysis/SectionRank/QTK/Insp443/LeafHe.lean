module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Descent
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.HeConcl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.HeIdent
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.HeOrb
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OfForK
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ProvedRows

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He
  CFSG.Sporadic.HeldB

variable {A : Type} [Group A] [Finite A] {L V MK : Subgroup A}
  {ι : A →* Equiv.Perm (Fin 8330)}

theorem KConfig.conclK_he
    (h : KConfig A L V MK) (hι : CFSG.Quasithin.KGC31.He.Emb ⊤ ι) : ConclK A L V MK := by
  obtain ⟨ι', hι', y, hy, p, k, hp, hp5, hyk, hy1, hW | hW⟩ := h.he_ref hι
  · obtain ⟨hL, hV⟩ := h.he_eq_w5 hι' hW hy hp hp5 hyk hy1
    have hLsP : lGrp ≤ heP := Ls_le.trans inf_le_left
    have hperf : ⁅lGrp, lGrp⁆ = lGrp := by
      rw [← hι'.map_comap hLsP, ← hL, ← Subgroup.map_commutator, h.perfect]
    rcases He.irr_comap hι' hperf hV (hL ▸ h.le_normalizer) with h0 | hE
    · exact absurd h0 h.ne_bot
    · rw [hL, hE]
      exact conclK_he_ref hι' hperf MK
  · exact (h.he_not_w7 hι' hW hy hp hp5 hyk hy1).elim

theorem He.emb_of_mulEquiv {A : Type} [Group A] (φ : A ≃* heP) :
    CFSG.Quasithin.KGC31.He.Emb (⊤ : Subgroup A) (heP.subtype.comp φ.toMonoidHom) := by
  refine ⟨heP.subtype_injective.comp φ.injective, ?_, ?_⟩
  · rw [← Subgroup.map_map, Subgroup.map_top_of_surjective _ φ.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · rintro _ ⟨x, rfl⟩
    exact heP_le_heAutGroup (φ x).2

theorem conclK_He
    {L V MK : Subgroup (NativeSporadic.Carrier .He)}
    (h : KConfig (NativeSporadic.Carrier .He) L V MK) :
    ConclK (NativeSporadic.Carrier .He) L V MK := by
  let φ : NativeSporadic.Carrier .He ≃* heP := heEquivP
  haveI : Finite (NativeSporadic.Carrier .He) := Finite.of_injective (⇑φ) φ.injective
  exact KConfig.conclK_he h (He.emb_of_mulEquiv φ)

theorem forK_He :
    ForK (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .He)) := by
  let φ : NativeSporadic.Carrier .He ≃* heP := heEquivP
  haveI : Finite (NativeSporadic.Carrier .He) := Finite.of_injective (⇑φ) φ.injective
  refine forK_of_kConfig (X := NativeSporadic.Carrier .He) ?_ (fun L V MK h => conclK_He h)
  rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_He]
  decide

theorem for_He
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .He)) :=
  For.of_forK h37 h38 h39 forK_He

end CFSG.SectionRank.QTK.Insp443

end
