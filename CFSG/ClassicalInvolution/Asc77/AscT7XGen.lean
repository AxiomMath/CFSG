module

public import CFSG.ClassicalInvolution.Asc77.AscT7HC1
import CFSG.ClassicalInvolution.Asc77.AscIHSectF
import CFSG.ClassicalInvolution.ModelFacts.Orth15SExact

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.ExactLayer

namespace T7X

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)} {c : G}

theorem genSection_exactPair (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : ∀ M ∈ Ω, AEmpty Ω M) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G) :
    GenSection p f (oddQuotientFamily (exactPair Ω c)) ∧
      Nat.card (↥(exactLayer Ω c) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω c)) <
        Nat.card G := by
  set Y := exactLayer Ω c with hY
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : HypOmegaMod p f (exactPair Ω c) := hypOmegaMod_exactPair hp hq hΩ hc2
  have hΦ : HypOmegaMod p f (oddQuotientFamily (exactPair Ω c)) :=
    oddQuotHyp p f hp hq ↥Y (exactPair Ω c) hΛ N₀ hN₀odd
  have hAΛ : ∀ L ∈ exactPair Ω c, AEmpty (exactPair Ω c) L := by
    have h0 := aEmpty_exactPair hp hq hΩ hA hc2
    have e0 : centralizingMembers (exactFamily Ω c) {c} = exactFamily Ω c :=
      centMembers_exactFamily Ω c
    rw [e0] at h0
    exact h0
  refine ⟨⟨hΦ, CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y, ?_,
    aEmpty_quotFamily hp hq hΛ hΦ hN₀odd hAΛ⟩, ?_⟩
  · exact omegaGen_quotFamily_eq_top (exactPair Ω c) N₀
      (omegaGen_restrictFamily_eq_top (exactFamily Ω c) Y (exactLayer_eq_iSup Ω c).symm)
  · show Nat.card (↥Y ⧸ N₀) < Nat.card G
    have h1 : Nat.card (↥Y ⧸ N₀) ≤ Nat.card ↥Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    have h2 : Nat.card ↥Y < Nat.card G := card_exactLayer_lt hnc
    omega


theorem exactImg_isolated (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K K' : Subgroup G} (hK : K ∈ tqMembers Ω c)
    (hperp : KPerp Ω K = {K, K'}) (hK' : K' ∉ tqMembers Ω c) {J : Subgroup G}
    (hJ : J ∈ tqMembers Ω c) :
    T7H.exactImg Ω c J ∉
      omegaNbr (oddQuotientFamily (exactPair Ω c)) (T7H.exactImg Ω c K) := by
  intro h
  obtain ⟨n, -, hnb⟩ := T7H.exactImg_nbr_lift hp hq hΩ hc2 hK hJ h
  have hncent : (n : G) ∈ Subgroup.centralizer ({c} : Set G) :=
    exactLayer_le_centralizer Ω c n.2
  have h1 := omegaNbr_conj hΩ.conjInvariant hnb (n : G)⁻¹
  rw [conjSub_inv_conjSub] at h1
  have h2 : conjSub (n : G)⁻¹ J ∈ KPerp Ω K := Set.mem_insert_of_mem _ h1
  rw [hperp] at h2
  have h3 : conjSub (n : G)⁻¹ J = K' := by
    rcases h2 with h2 | h2
    · exact absurd h2 h1.2.1
    · exact h2
  have h4 : conjSub (n : G)⁻¹ J ∈ tqMembers Ω c :=
    conjSub_mem_tqMembers hΩ.conjInvariant (Subgroup.inv_mem _ hncent) hJ
  rw [h3] at h4
  exact hK' h4

end T7X

end CFSG.ClassicalInvolution.Asc77
