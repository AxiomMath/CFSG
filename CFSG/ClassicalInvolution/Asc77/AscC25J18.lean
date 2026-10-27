module

public import CFSG.ClassicalInvolution.Asc77.AscC25J17
public import CFSG.ClassicalInvolution.Asc77.AscC25J16

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Classify

variable {E : Type} [Group E] [Finite E] {Φ : Set (Subgroup E)} {ι : Type}


theorem classify3 {n : ℕ} (h4 : Thm4BelowU 3 1 n) (hlt : Nat.card E < n)
    (hΦ : HypOmegaModU (.sl2 3 1) Φ) (hO : classicalInvolutionOddCore E = ⊥)
    (hA : ∀ L ∈ Φ, AEmpty Φ L) (D : LieSystemDataU 3 1 ι E Φ) {i₀ : ι} (hi : ∀ j, j = i₀)
    {A A' : Subgroup E} {z a₀ b₀ : E} (T : TwinSect0 Φ A A' z a₀ b₀) :
    (∀ L ∈ Φ, L = A ∨ L = A') ∨
      ∃ (t : StatedLieTag) (k : ℕ), CompIs 3 1 (D.kind i₀) t k ∧
        ((t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4) ∨ (t = .PSU ∧ k = 4) ∨
          (t = .POmegaOdd ∧ k = 3) ∨ (t = .POmegaPlus ∧ k = 4) ∨ (t = .POmegaMinus ∧ k = 4)) := by
  have hΩg : HypOmegaGen Φ := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΦ
  have hne : Φ.Nonempty := ⟨A, T.hA⟩
  have hsurj : Function.Surjective (D.hom i₀) := by
    apply MonoidHom.range_eq_top.mp
    have h1 : (⨆ j, (D.hom j).range) = (D.hom i₀).range :=
      le_antisymm (iSup_le fun j => by rw [hi j]) (le_iSup (fun j => (D.hom j).range) i₀)
    rw [← h1, D.generate]
  have hfund' : ∀ L ∈ Φ, ∃ R ∈ (D.kind i₀).fund, L = R.map (D.hom i₀) := by
    intro L hL
    obtain ⟨j, R, hR, hLR⟩ := D.fundamental L hL
    obtain rfl := hi j
    exact ⟨R, hR, hLR⟩
  have hAA' : A' ∈ twinSet Φ A := ⟨T.hA', z, T.hzA, T.hzA'⟩
  rcases D.valid i₀ with ⟨t, k, e, hfund, hadm, he, hc⟩ | ⟨-, hc | hc⟩
  · obtain ⟨M⟩ := ih8Model_of_comp hΦ.conjInvariant hfund hadm he hc (D.hom i₀)
      (D.ker_le_center i₀) hsurj hfund'
    obtain ⟨RA, hRA, hAR⟩ := (M.mem_iff A).mp T.hA
    obtain ⟨RB, hRB, hBR⟩ := (M.mem_iff A').mp T.hA'
    have hRR : RA ≠ RB := fun h => T.ne (by rw [hAR, hBR, h])
    have hzRA : IsUniqueInvolution (RA.map M.ψ) z := hAR ▸ T.hzA
    have hzRB : IsUniqueInvolution (RB.map M.ψ) z := hBR ▸ T.hzA'
    by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
    · rcases dConnected_or_transitive3 h4 hlt hΦ hO hA with hconn | htrans
      · exact Or.inl (all_twin_of_dConnected hΩg hconn T)
      · exact absurd (noTwins_of_g2d4_datum M htrans hG2d4 A T.hA A' hAA') T.ne.symm
    have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
    have hD4 : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
    have hshape := twin_tag_cases3 M hΦ hne hG2 hD4 hRA hRB hRR hzRA hzRB
    have hef : e = 1 := he.resolve_right fun h => hD4 h.1
    have hCI : CompIs 3 1 (D.kind i₀) t k := ⟨e, he, hfund, hadm, hc⟩
    rcases tag_casesU (p := 3) (e := e) (by norm_num) hfund hadm hG2 hD4 with hconn | hsmall
    · exact Or.inl (all_twin_of_dConnected hΩg
        (dConnected_of_connectedU M hΦ hne hG2 hD4 hconn) T)
    · right
      refine ⟨t, k, hCI, ?_⟩
      rcases hsmall with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases hshape with h | h | h | h | h | h
        · exact absurd h.1 (by decide)
        · exact Or.inr (Or.inl h)
        · exact absurd h.1 (by decide)
        · exact absurd h.1 (by decide)
        · exact absurd h.1 (by decide)
        · exact absurd h.1 (by decide)
      · rcases hshape with h | h | h | h | h | h
        · exact absurd h.1 (by decide)
        · exact absurd h.1 (by decide)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact absurd h.1 (by decide)
        · exact absurd h.1 (by decide)
        · exact absurd h.1 (by decide)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  ·
    exfalso
    obtain ⟨R, hR, hAR⟩ := hfund' A T.hA
    obtain ⟨R', hR', hBR⟩ := hfund' A' T.hA'
    obtain ⟨S, hS, hRS⟩ := exists_map_castHom hc (D.hom i₀) hR
    obtain ⟨S', hS', hRS'⟩ := exists_map_castHom hc (D.hom i₀) hR'
    have hStop : S = ⊤ := Set.mem_singleton_iff.mp hS
    have hS'top : S' = ⊤ := Set.mem_singleton_iff.mp hS'
    have hAtop : A = ⊤ := by
      rw [hAR, ← hRS, hStop, Subgroup.map_top, range_castHom]
      exact MonoidHom.range_eq_top.mpr hsurj
    have hBtop : A' = ⊤ := by
      rw [hBR, ← hRS', hS'top, Subgroup.map_top, range_castHom]
      exact MonoidHom.range_eq_top.mpr hsurj
    exact T.ne (hAtop.trans hBtop.symm)
  ·
    exfalso
    have hsurj' : Function.Surjective (castHom hc (D.hom i₀)) := by
      have h := hsurj
      rw [← MonoidHom.range_eq_top] at h ⊢
      rw [range_castHom]
      exact h
    have hinj : Function.Injective (castHom hc (D.hom i₀)) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact (castHom_ker_le_center hc (D.hom i₀) (D.ker_le_center i₀)).trans
        (Q3.center_m11_eq_bot Q3.m11Facts).le
    let e : ↥CFSG.Blueprint.NativeSporadic.M11 ≃* E :=
      MulEquiv.ofBijective (castHom hc (D.hom i₀)) ⟨hinj, hsurj'⟩
    exact T.ne (noTwins_of_mulEquiv_m11 e hΦ A T.hA A' hAA').symm

end Classify

end CFSG.ClassicalInvolution.Asc77.C25J
