module

public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem i1122At_of_iso {p : ℕ} (h1131 : I1131At G p) (h1122 : I1122IsoAt G p) :
    I1122At G p := by
  intro B y K b hB hy hK hb hbN J hJ
  have hExc := h1131 B y K hB hy hK fun h => hbN (h hb)
  have hp : p.Prime := hExc.1 ▸ Nat.prime_three
  obtain ⟨e⟩ := h1122 B y K b hB hy hK hb hbN J hJ
  have hZK := center_pSimple_eq_bot hp hK
  have hZJ : Subgroup.center (PQuot p J) = ⊥ := by
    have h := Subgroup.map_center_eq e
    rw [hZK, Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h
    exact h
  have f : PSimple p J ≃* PSimple p K :=
    ((QuotientGroup.quotientMulEquivOfEq hZJ).trans QuotientGroup.quotientBot).trans e
  refine ⟨hExc.1, ?_, (catalogIs_congr f).2 ?_⟩
  · rw [hZJ, Subgroup.card_bot]
  · obtain ⟨i, hi, hf⟩ := hExc.2.2
    exact ⟨i, Or.inl hi, hf⟩

end CFSG.LocalAnalysis.GLTheoremA
