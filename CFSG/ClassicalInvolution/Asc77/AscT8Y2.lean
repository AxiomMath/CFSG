module

public import CFSG.ClassicalInvolution.Asc77.AscT8Clique

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

section Triangle

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem dstarConnected_of_triangle {n : ℕ} (hn : CITBelowU p f n) (hlt : Nat.card X < n)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hD4 : Ih8D4Star p f) (hΦ : HypOmegaMod p f Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (hnt : ∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K) (B : Fin 3 → Subgroup X)
    (hB : ∀ i, B i ∈ Φ) (hinj : Function.Injective B)
    (hadj : ∀ i j, i ≠ j → B j ∈ omegaNbr Φ (B i)) : T3.DStarConnected Φ := by
  classical
  have hne : Φ.Nonempty := ⟨B 0, hB 0⟩
  rcases dConnected_or_transitive_noTwins hp2 hq (thm4NTBelow_of_citBelow hn) hlt hΦ hO hnt with
    hc | htrans
  · intro K hK L hL
    exact T7A.mem_dstarComp_of_mem_dComp hp2 hΦ (hc K hK L hL)
  obtain ⟨D⟩ := exists_omegaLie hn hΦ hne hO hlt
  obtain ⟨t, k, e, M, -⟩ := exists_datum_of_omegaLie D hΦ hgen htrans hne
  by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
  · exact absurd (Or.inl (hadj 0 1 (by decide))) (dEdgeless_of_g2d4_datum hp2 hq hΦ htrans M hG2d4
      _ (hB 0) _ (hB 1))
  have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
  have hD4' : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
  have h10 : B 1 ≠ B 0 := fun h => absurd (hinj h) (by decide)
  have htop := top_notMem_of_transitive htrans (hB 0) (hB 1) h10
  have hnpsl := M.not_psl_two_sect hp2 hne htop
  have hq' : 5 ≤ p ^ e := by rw [M.exp_eq_f hD4']; exact hq
  have hpre : ∀ i, ∃ R ∈ M.cls, B i = R.map M.ψ := fun i => (M.mem_iff _).mp (hB i)
  choose R hRcls hRB using hpre
  have hcomm : ∀ i j, i ≠ j → Commutes (R i) (R j) := fun i j hij =>
    M.commutes_of_omegaNbr_sect hΦ hp2 hq hG2 hD4' (hRcls i) (hRcls j)
      (by rw [← hRB i, ← hRB j]; exact hadj i j hij)
  have hRne : ∀ i j, i ≠ j → R i ≠ R j := fun i j hij h =>
    hij (hinj (by rw [hRB i, hRB j, h]))
  have hRf := fun i => M.cls_sub (hRcls i)
  rcases ih8_tag_cases hp2 hq' M.isFundTag M.admissible hG2 hD4' with hconn | hsmall
  · intro K hK L hL
    exact T7A.mem_dstarComp_of_mem_dComp hp2 hΦ
      (M.dConnected_of_connected hp2 hq hne hG2 hD4' hconn K hK L hL)
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hNT := smallNoThree (p := p)
  rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    exfalso
    have hk2 : 2 ≤ k := M.admissible.2.2.1
    have : k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl
    · exact hnpsl ⟨rfl, rfl⟩
    · have := four_le_of_commutes_psl hp2 (le_refl 3) (hRf 0) (hRf 1) (hRne 0 1 h01)
        (hcomm 0 1 h01)
      omega
    · exact hNT _ _ _ M.admissible hp2 hq' (Or.inr (Or.inl ⟨rfl, rfl⟩)) _ (hRf 0) _ (hRf 1) _
        (hRf 2) (hRne 0 1 h01) (hRne 0 2 h02) (hRne 1 2 h12) (hcomm 0 1 h01) (hcomm 0 2 h02)
        (hcomm 1 2 h12)
  ·
    exfalso
    have hk3 : 3 ≤ k := M.admissible.2.2.1
    have : k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl
    · have := four_le_of_commutes_psu hp2 M.admissible (hRf 0) (hRf 1) (hRne 0 1 h01)
        (hcomm 0 1 h01)
      omega
    · exact hNT _ _ _ M.admissible hp2 hq' (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) _ (hRf 0) _
        (hRf 1) _ (hRf 2) (hRne 0 1 h01) (hRne 0 2 h02) (hRne 1 2 h12) (hcomm 0 1 h01)
        (hcomm 0 2 h02) (hcomm 1 2 h12)
  · exfalso
    exact hNT _ _ _ M.admissible hp2 hq' (Or.inl ⟨rfl, rfl⟩) _ (hRf 0) _ (hRf 1) _ (hRf 2)
      (hRne 0 1 h01) (hRne 0 2 h02) (hRne 1 2 h12) (hcomm 0 1 h01) (hcomm 0 2 h02)
      (hcomm 1 2 h12)
  · exfalso
    exact hNT _ _ _ M.admissible hp2 hq' (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) _
      (hRf 0) _ (hRf 1) _ (hRf 2) (hRne 0 1 h01) (hRne 0 2 h02) (hRne 1 2 h12)
      (hcomm 0 1 h01) (hcomm 0 2 h02) (hcomm 1 2 h12)
  ·
    exact hD4 hp2 hq X Φ e hΦ ⟨M⟩
  · exfalso
    exact hNT _ _ _ M.admissible hp2 hq' (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))) _
      (hRf 0) _ (hRf 1) _ (hRf 2) (hRne 0 1 h01) (hRne 0 2 h02) (hRne 1 2 h12)
      (hcomm 0 1 h01) (hcomm 0 2 h02) (hcomm 1 2 h12)

end Triangle

end CFSG.ClassicalInvolution.Asc77
