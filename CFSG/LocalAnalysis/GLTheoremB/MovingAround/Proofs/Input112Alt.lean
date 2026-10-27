module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Bridges1
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input112Alt

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem conj_injective_of_isAltType {Y : Type} [Group Y] {n : ℕ} (hn : 5 ≤ n)
    (hY : MovingAround.IsAltType n Y) : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  obtain ⟨e⟩ := hY
  rw [injective_iff_map_eq_one]
  intro x hx
  have hcen : e x ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h : x * e.symm g * x⁻¹ = e.symm g := by
      simpa [MulAut.conj_apply] using congrArg (fun f : MulAut Y => f (e.symm g)) hx
    have h' : e.symm g * x = x * e.symm g := by
      calc e.symm g * x = x * e.symm g * x⁻¹ * x := by rw [h]
        _ = x * e.symm g := by group
    simpa [map_mul] using congrArg e h'
  rw [alternatingGroup.center_eq_bot (by simp; omega), Subgroup.mem_bot] at hcen
  exact e.injective (by rw [hcen, map_one])

theorem three_le_pRank_mulAut {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 9 ≤ n)
    (hY : MovingAround.IsAltType n Y) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut Y)) := by
  have hinj := conj_injective_of_isAltType (by omega) hY
  obtain ⟨e⟩ := hY
  have hK : MovingAround.IsAltType n ↥(MulAut.conj : Y →* MulAut Y).range :=
    ⟨(MonoidHom.ofInjective hinj).symm.trans e⟩
  obtain ⟨-, E, -, hE, hcard⟩ := Lemma118R.Input10_6AltRank_holds n 3 (MulAut Y)
    (MulAut.conj : Y →* MulAut Y).range (by omega) Nat.prime_three (by norm_num) hK
  have h := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_top hE hcard
  have h3 : 3 ≤ n / 3 := by omega
  omega

section Holds112

set_option linter.unusedSectionVars false


theorem input11_2Alt_holds
    : Lemma118R.Input11_2Alt := by
  intro G _ _ m p hS X B L _ hB hBX hr hL n hn hAlt
  by_contra hnot
  obtain ⟨rfl, -, hrank, -, -⟩ :=
    Bridges1.input11_2Full_holds G m p hS X B L hB hBX hr hL hnot
  have h := three_le_pRank_mulAut (by omega : 9 ≤ n) hAlt
  omega

end Holds112

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input112Alt
