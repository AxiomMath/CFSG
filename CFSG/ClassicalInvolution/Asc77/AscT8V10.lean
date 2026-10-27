module

public import CFSG.ClassicalInvolution.Asc77.AscT7S2RK
public import CFSG.ClassicalInvolution.Asc77.AscIHSectKD
public import CFSG.ClassicalInvolution.Asc77.AscT8V9
public import CFSG.ClassicalInvolution.Asc77.AscT8Clique

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups

namespace T8V

variable {p f : ℕ} [Fact p.Prime]


theorem e4_tag (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : CITBelowU p f n)
    {X : Type} [Group X] [Finite X] (hlt : Nat.card X < n) {Φ : Set (Subgroup X)}
    (hΦ : HypOmegaMod p f Φ) (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (hnt : ∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K) (hdisc : ¬ T3.DStarConnected Φ)
    {A B : Subgroup X} (hA : A ∈ Φ) (hB : B ∈ omegaNbr Φ A) :
    (∃ e, Nonempty (Ih8Model p f Φ .PSp 2 e)) ∨
      (p ^ f % 4 = 3 ∧ ∃ e, Nonempty (Ih8Model p f Φ .PSL 4 e)) ∨
      (p ^ f % 4 = 1 ∧ ∃ e, Nonempty (Ih8Model p f Φ .PSU 4 e)) := by
  classical
  have hne : Φ.Nonempty := ⟨A, hA⟩
  have hmod : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
    have hodd : Odd (p ^ f) := (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
    rcases hodd with ⟨k, hk⟩
    omega
  rcases dConnected_or_transitive_noTwins hp2 hq (thm4NTBelow_of_citBelow hn) hlt hΦ hO hnt with
    hc | htrans
  · exact absurd (fun K hK L hL => T7A.mem_dstarComp_of_mem_dComp hp2 hΦ (hc K hK L hL)) hdisc
  obtain ⟨D⟩ := exists_omegaLie hn hΦ hne hO hlt
  obtain ⟨t, k, e, M, -⟩ := exists_datum_of_omegaLie D hΦ hgen htrans hne
  by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
  · exact absurd (Or.inl hB) (dEdgeless_of_g2d4_datum hp2 hq hΦ htrans M hG2d4 _ hA _ hB.1)
  have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
  have hD4' : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
  have hBA : B ≠ A := hB.2.1
  have htop := top_notMem_of_transitive htrans hA hB.1 hBA
  have hnpsl := M.not_psl_two_sect hp2 hne htop
  have hq' : 5 ≤ p ^ e := by rw [M.exp_eq_f hD4']; exact hq
  obtain ⟨RA, hRA, rfl⟩ := (M.mem_iff A).mp hA
  obtain ⟨RB, hRB, hRBB⟩ := (M.mem_iff B).mp hB.1
  have hcomm : Commutes RA RB :=
    M.commutes_of_omegaNbr_sect hΦ hp2 hq hG2 hD4' hRA hRB (by rw [← hRBB]; exact hB)
  have hRne : RA ≠ RB := fun h => hBA (by rw [hRBB, h])
  rcases ih8_tag_cases hp2 hq' M.isFundTag M.admissible hG2 hD4' with hconn | hsmall
  · exact absurd (fun K hK L hL => T7A.mem_dstarComp_of_mem_dComp hp2 hΦ
      (M.dConnected_of_connected hp2 hq hne hG2 hD4' hconn K hK L hL)) hdisc
  rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    have hk2 : 2 ≤ k := M.admissible.2.2.1
    have : k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl
    · exact absurd ⟨rfl, rfl⟩ hnpsl
    · exfalso
      have := four_le_of_commutes_psl hp2 (le_refl 3) (M.cls_sub hRA) (M.cls_sub hRB) hRne hcomm
      omega
    · right
      left
      refine ⟨?_, e, ⟨M⟩⟩
      rcases hmod with h | h
      · exact absurd (dstarConnected_psl4 M hΦ hp2 hq hne h) hdisc
      · exact h
  ·
    have hk3 : 3 ≤ k := M.admissible.2.2.1
    have : k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl
    · exfalso
      have := four_le_of_commutes_psu hp2 M.admissible (M.cls_sub hRA) (M.cls_sub hRB) hRne hcomm
      omega
    · right
      right
      refine ⟨?_, e, ⟨M⟩⟩
      rcases hmod with h | h
      · exact h
      · exact absurd (dstarConnected_psu4 M hΦ hp2 hq hne h) hdisc
  · exact Or.inl ⟨e, ⟨M⟩⟩
  · exact absurd (T7S2R.ih8S4Star p f hp2 hq X Φ e hΦ (Or.inl ⟨M⟩)) hdisc
  · exact absurd (ih8D4Star hp2 hq X Φ e hΦ ⟨M⟩) hdisc
  · exact absurd (T7S2R.ih8S4Star p f hp2 hq X Φ e hΦ (Or.inr ⟨M⟩)) hdisc

end T8V

end CFSG.ClassicalInvolution.Asc77
