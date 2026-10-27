module

public import CFSG.ClassicalInvolution.Asc77.AscIHD4
public import CFSG.ClassicalInvolution.Asc77.AscIHExact
public import CFSG.ClassicalInvolution.Asc77.AscIHTwin

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

theorem thm4Below_of_citBelow {n : ℕ} (hn : CITBelowU p f n) : Thm4Below p f n := by
  intro hp2 hq G _ _ hG Ω hΩ hO hA K hK J hJ hnc
  obtain ⟨D⟩ := exists_omegaLie hn hΩ ⟨K, hK⟩ hO hG
  have hΩ := hΩ.toExact (D.exactMembers hp2 hq hΩ)
  obtain ⟨i, R, hR, hKR⟩ := D.fundamental K hK
  obtain ⟨j, S, hS, hJS⟩ := D.fundamental J hJ
  by_cases hij : i = j
  swap
  · intro a ha b hb
    rw [hKR] at ha
    rw [hJS] at hb
    obtain ⟨x, -, rfl⟩ := ha
    obtain ⟨y, -, rfl⟩ := hb
    exact D.commute i j hij x y
  subst hij
  exfalso
  have key : ∀ g, S = R.map (MulAut.conj g).toMonoidHom → ∃ g' : G, conjSub g' K = J := by
    intro g hg
    refine ⟨D.hom i g, ?_⟩
    rw [hKR, hJS, hg, map_conj_eq_conjSub_map]
  by_cases hconj : ∃ g, S = R.map (MulAut.conj g).toMonoidHom
  · obtain ⟨g, hg⟩ := hconj
    exact hnc (key g hg)
  by_cases hG2' : D.tag i = .G2
  · refine false_of_g2_pair hp2 hq hΩ hA D i hG2' hR hS (by rw [← hKR]; exact hK)
      (by rw [← hJS]; exact hJ) (by rw [← hKR, ← hJS]; exact hnc)
  by_cases hD4' : D.tag i = .trialityD4
  · have hne : ¬ (D.tag i = .PSL ∧ D.rank i = 2) := fun h => by
      rw [hD4'] at h
      exact absurd h.1 (by decide)
    have hcardR : Nat.card R = Nat.card SL(2, GaloisField p f) := by
      rw [← natCard_map_of_injOn (D.hom i) (D.injOn_fund i hne hR), ← hKR]
      exact natCard_member hΩ hK
    have hcardS : Nat.card S = Nat.card SL(2, GaloisField p f) := by
      rw [← natCard_map_of_injOn (D.hom i) (D.injOn_fund i hne hS), ← hJS]
      exact natCard_member hΩ hJ
    exact d4OrdersDiffer p (D.tag i) (D.rank i) (D.exp i) hD4' (D.admissible i) R hR S hS hconj
      (hcardR.trans hcardS.symm)
  exact hconj (ModelFacts.fundamentalSingleClass (D.tag i) (D.rank i) p (D.exp i) Fact.out
    (isFundTag_modelFacts (D.isFundTag i)) (D.admissible i) hG2' hD4' R hR S hS)

theorem ihInterface : IHInterface p f :=
  fun _ hn => ⟨thm4Below_of_citBelow hn, thm2Below_of_citBelow hn⟩

end CFSG.ClassicalInvolution.Asc77
