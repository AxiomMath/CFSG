module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineNineConseq
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenCF
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenG1

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

namespace NineSettingGen

theorem exists_isSylowOf_normalizer_le (h : NineSettingGen G M p Q H E k)
    (hp : p ∉ sigmaM G M) (hU : NineNineOne M p) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P H ∧ P ≤ M ∧ normalizer (P : Set G) ≤ M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (H ⊓ M)
  obtain ⟨hPH, hN⟩ :=
    _root_.CFSG.LocalAnalysis.RankThreeUC.AGL81C.isSylowOf_of_NineNineOne
      h.setting.maxLocal h.mem_Q h.Q_le_H hp hU hP
  exact ⟨P, hPH, hP.le.trans inf_le_right, hN⟩

theorem pCore_quotKer_eq_bot (h : NineSettingGen G M p Q H E k) (hp : p ∉ sigmaM G M)
    (hU : NineNineOne M p) : CFSG.pCore p (QuotKer M H) = ⊥ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨P, hPH, hPM, -⟩ := h.exists_isSylowOf_normalizer_le hp hU
  exact _root_.CFSG.LocalAnalysis.RankThreeUC.AGL81C.pCore_quotKer_eq_bot hPH hPM

theorem center_quotKer_eq_bot (h : NineSettingGen G M p Q H E k) (hp : p ∉ sigmaM G M)
    (hU : NineNineOne M p) : Subgroup.center (QuotKer M H) = ⊥ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨P, hPH, -, hN⟩ := h.exists_isSylowOf_normalizer_le hp hU
  exact _root_.CFSG.LocalAnalysis.RankThreeUC.AGL81C.center_quotKer_eq_bot hPH hN

theorem dvd_card_quotKer (h : NineSettingGen G M p Q H E k) (hp : p ∉ sigmaM G M)
    (hU : NineNineOne M p) : p ∣ Nat.card (QuotKer M H) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨P, hPH, -, hN⟩ := h.exists_isSylowOf_normalizer_le hp hU
  exact _root_.CFSG.LocalAnalysis.RankThreeUC.AGL81C.dvd_card_quotKer hPH hN h.not_le

theorem isPSLType_oPPrimeHull_quotKer_of_hom_GL23 (h : NineSettingGen G M 3 Q H E k)
    (hp : 3 ∉ sigmaM G M) (hU : NineNineOne M 3) {X : Type} [Group X]
    (ρ : X →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (π : X →* QuotKer M H)
    (hπ : Function.Surjective π) (hρ : IsPGroup 3 (ρ.ker.map π)) :
    IsPSLType 2 (ZMod 3) ↥(oPPrimeHull 3 (⊤ : Subgroup (QuotKer M H))) :=
  isPSLType_oPPrimeHull_of_hom_GL23 ρ π hπ hρ (h.dvd_card_quotKer hp hU)
    (h.pCore_quotKer_eq_bot hp hU) (h.center_quotKer_eq_bot hp hU)

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
