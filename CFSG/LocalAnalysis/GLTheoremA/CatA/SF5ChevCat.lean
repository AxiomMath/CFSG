module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H196Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator

theorem sf5_lieIndexChar_eq_characteristic (d : TauCeti.LieTypeIndex) :
    lieIndexChar d = d.characteristic := by
  cases d <;> simp [lieIndexChar]

theorem sf5_isChevIndexOfChar {p : ℕ} (d : TauCeti.LieTypeIndex) (h : d.characteristic = p) :
    IsChevIndexOfChar p d := by
  have hl : lieIndexChar d = p := (sf5_lieIndexChar_eq_characteristic d).trans h
  cases d with
  | A n r =>
    rcases n with _ | _ | n
    · exact hl
    · exact Or.inl hl
    · exact hl
  | twistedA n r =>
    rcases n with _ | _ | _ | n
    · exact hl
    · exact hl
    · exact Or.inl hl
    · exact hl
  | B n r => exact hl
  | C n r => exact hl
  | D n r => exact hl
  | twistedD n r => exact hl
  | E6 r => exact hl
  | E7 r => exact hl
  | E8 r => exact hl
  | F4 r => exact hl
  | G2 r => exact hl
  | twistedE6 r => exact hl
  | trialityD4 r => exact hl
  | reeG2 m => exact hl
  | suzuki m => exact hl
  | reeF4 m => exact hl
  | tits => exact hl

theorem I196ChevCat_holds : ∀ p : ℕ, I196ChevCat p := by
  intro p _hp _hp2 S _ _ _hSimple hChev
  unfold IsChevSimple at hChev
  rcases hChev with ⟨i, hi, e⟩ | hamb
  · cases i with
    | cyclic q hq => exact False.elim hi
    | alternating n hn => exact False.elim hi
    | sporadic s => exact False.elim hi
    | lie j =>
      obtain ⟨d, hv⟩ := j
      have hd : d.characteristic = p := hi
      refine Or.inl ?_
      unfold IsChevOfChar
      exact ⟨⟨d, hv⟩, sf5_isChevIndexOfChar d hd, e⟩
  · exact Or.inr hamb

end CFSG.LocalAnalysis.GLTheoremA

end
