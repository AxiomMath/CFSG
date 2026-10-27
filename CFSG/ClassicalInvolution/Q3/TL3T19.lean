module

public import CFSG.ClassicalInvolution.Q3.TL3T18
public import CFSG.ClassicalInvolution.Q3.TL3T15

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

@[expose] def TightThmD3Below (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaGen Ω →
    (∀ J ∈ Ω, IsPGroup 2 J) → (∀ J ∈ Ω, Nat.card J = 8) →
    (∀ J ∈ Ω, ∀ u : G, IsUniqueInvolution J u →
      Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G)) →
    (∀ J ∈ Ω, AEmpty Ω J) →
    (∀ J ∈ Ω, ∀ J' ∈ Ω, ∀ u : G, IsUniqueInvolution J u → IsUniqueInvolution J' u → J = J') →
    ∀ P : Set (Subgroup G), P ⊆ Ω → Nat.card ↥(pSpan P) < n →
    (∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L') →
    (∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) →
    classicalInvolutionOddCore ↥(pSpan P) = ⊥ →
    (∀ L ∈ P, ∀ u : G, IsUniqueInvolution L u → ∃ Q : Subgroup G, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q) →
    (∀ L ∈ P, ∀ u : G, IsUniqueInvolution L u → ∀ Q : Subgroup G, Q ≤ pSpan P →
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) → IsPGroup 2 Q → ∀ x ∈ L, x ∈ Q →
        x = 1 ∨ x = u) →
    (∀ L ∈ P, ∀ L' ∈ P, L ≠ L' → ¬ nbrAdj Ω L L') ∨
      (∃ n : ℕ, 5 ≤ n ∧ Nonempty (AEIdent P n)) ∨
      Nonempty (AEIdentOn P 7 AE.e64Sets AE.e64Sub) ∨
      Nonempty (AEIdentOn P 8 AE.e29Sets AE.e29Sub)

@[expose] def ThmDGenBelow (r n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaGen Ω →
    (∀ J ∈ Ω, IsPGroup 2 J) → (∀ J ∈ Ω, Nat.card J = 2 ^ r) →
    (∀ J ∈ Ω, AEmpty Ω J) →
    ∀ P : Set (Subgroup G), P ⊆ Ω → Nat.card ↥(pSpan P) < n →
    (∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L') →
    (∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) →
    classicalInvolutionOddCore ↥(pSpan P) = ⊥ →
    (∀ L ∈ P, ∀ u : G, IsUniqueInvolution L u → ∃ Q : Subgroup G, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q) →
    (∀ L ∈ P, ∀ L' ∈ P, L = L') ∨
      (∃ W : Subgroup G, WIn P (pSpan P) = {W}) ∨ (∃ E : Subgroup G, E8Struct (pSpan P) E) ∨
      Nonempty (AEIdentOn P 7 AE.e64Sets AE.e64Sub) ∨
      (∃ n : ℕ, 5 ≤ n ∧ Nonempty (AEIdent P n)) ∨
      Nonempty (AEIdentOn P 8 AE.e29Sets AE.e29Sub)

theorem tightThmD3_of_below (h : ∀ n, TightThmD3Below n) : TightThmD3 := by
  intro G _ _ Ω hΩ h2 h8 htight hA hnt P hPΩ
  exact h (Nat.card ↥(pSpan P) + 1) G Ω hΩ h2 h8 htight hA hnt P hPΩ (Nat.lt_succ_self _)

theorem thmDGen_of_below {r : ℕ} (h : ∀ n, ThmDGenBelow r n) : ThmDGen r := by
  intro G _ _ Ω hΩ h2 h8 hA P hPΩ
  exact h (Nat.card ↥(pSpan P) + 1) G Ω hΩ h2 h8 hA P hPΩ (Nat.lt_succ_self _)

theorem tightThmD3Below_of_genBelow {n : ℕ} (hD : ThmDGenBelow 3 n) : TightThmD3Below n := by
  intro G _ _ Ω hΩ h2 h8 _ hA hnt P hPΩ hcard htrans hinv hodd hE2 hthin
  by_cases hPne : P.Nonempty
  swap
  · exact Or.inl fun L hL => absurd ⟨L, hL⟩ hPne
  rcases hD G Ω hΩ h2 (fun J hJ => by rw [h8 J hJ]; norm_num) hA P hPΩ hcard htrans hinv hodd
      hE2 with hsing | ⟨W, hW⟩ | ⟨E, hE⟩ | h64 | hAE | h29
  · exact Or.inl fun L hL L' hL' hne => absurd (hsing L hL L' hL') hne
  · exact (false_of_WIn_eq hΩ h2 h8 hPΩ hPne hinv hthin hW).elim
  · exact Or.inl (indep_of_e8Struct hΩ h2 h8 hnt hPΩ hE2 hE)
  · exact Or.inr (Or.inr (Or.inl h64))
  · exact Or.inr (Or.inl hAE)
  · exact Or.inr (Or.inr (Or.inr h29))

end CFSG.ClassicalInvolution.Q3.TC.Thin

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Cit3


variable {n : ℕ}

theorem tightIndepLeaf_of_thmD3Below (hD : TC.Thin.TightThmD3Below n) : TightIndepLeaf n := by
  intro Y _ _ R S t hL hO hconn hsep hall M hM
  obtain ⟨g, rfl⟩ := hM
  have hS := hL.thinStd hO hconn hsep
  refine hS.indep_conj ?_ g
  have huniq := hL.datum.isUniqueInvolution_core
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set K₀ := tightCore R with hK₀
  have hOC : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : Y) ∈ oddCoreImg (Subgroup.centralizer ({t} : Set Y)) := ⟨x, hx, rfl⟩
    unfold TightOddCent at hO
    rw [hO, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hthM : TC.Thin.ThinAtM Ω K₀ := fun N h => hall K₀ N h
  set P : Set (Subgroup Y) := {L : Subgroup Y | MaxAdj (TC.nbrAdj Ω) K₀ L} with hPdef
  have hPΩ : P ⊆ Ω := fun L hL => (show MaxAdj (TC.nbrAdj Ω) K₀ L from hL).1.2.1
  have hcard : Nat.card ↥(TC.Thin.pSpan P) < n := by
    have hle : TC.Thin.pSpan P ≤ Subgroup.centralizer ({t} : Set Y) :=
      hS.pSpan_le_centralizer huniq
    have hne : Subgroup.centralizer ({t} : Set Y) ≠ ⊤ := by
      intro htop
      apply huniq.ne_one
      have ht : t ∈ Subgroup.center Y := by
        rw [Subgroup.mem_center_iff]
        intro y
        have hy : y ∈ Subgroup.centralizer ({t} : Set Y) := htop ▸ Subgroup.mem_top y
        exact (Subgroup.mem_centralizer_singleton_iff.mp hy)
      rw [hL.center, Subgroup.mem_bot] at ht
      exact ht
    have h1 := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne)
    rw [Subgroup.card_top, hL.card] at h1
    exact lt_of_le_of_lt (Subgroup.card_le_of_le hle) h1
  have htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ TC.Thin.pSpan P, conjSub x L = L' :=
    fun L hL L' hL' => hS.exists_conj_maxOrb hL hL'
  have hinv : ∀ L ∈ P, ∀ x ∈ TC.Thin.pSpan P, conjSub x L ∈ P := fun L hL x hx =>
    hS.maxAdj_conj_of_mem hL huniq (hS.pSpan_le_centralizer huniq hx)
  have hodd := hS.oddCore_pSpan_eq_bot huniq hOC
  have hE2 : ∀ L ∈ P, ∀ u : Y, IsUniqueInvolution L u → ∃ Q : Subgroup Y,
      Q ≤ TC.Thin.pSpan P ∧ (∀ x ∈ TC.Thin.pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧
        IsPGroup 2 Q ∧ u ∈ Q := by
    intro L hL u hu
    refine ⟨TC.Thin.Qz t ⊓ TC.Thin.pSpan P, inf_le_right, ?_, ?_, ?_⟩
    · intro x hx q hq
      refine ⟨(TC.Thin.isNormalTwoIn_Qz t).2.2 x (hS.pSpan_le_centralizer huniq hx) q hq.1, ?_⟩
      exact (TC.Thin.pSpan P).mul_mem ((TC.Thin.pSpan P).mul_mem hx hq.2)
        ((TC.Thin.pSpan P).inv_mem hx)
    · exact (TC.Thin.isNormalTwoIn_Qz t).2.1.to_le inf_le_left
    · exact ⟨TC.Thin.mem_Qz_of_maxAdj hthM hL huniq hu,
        TC.Thin.le_pSpan hL hu.mem⟩
  have hthin : ∀ L ∈ P, ∀ u : Y, IsUniqueInvolution L u → ∀ Q : Subgroup Y,
      Q ≤ TC.Thin.pSpan P → (∀ x ∈ TC.Thin.pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) →
        IsPGroup 2 Q → ∀ x ∈ L, x ∈ Q → x = 1 ∨ x = u := by
    intro L hL u hu Q hQX hQn hQ2 x hxL hxQ
    exact hS.eq_of_mem_Qz (show MaxAdj (TC.nbrAdj Ω) K₀ L from hL).1 (hthM L hL) huniq hu hxL
      (hS.le_Qz_of_normal huniq hQX hQn hQ2 hxQ)
  rcases hD Y Ω hS.hyp hS.two hS.card hS.tight hS.aEmpty
      (fun J hJ J' hJ' u hu hu' => hS.eq_of_uniqueInvolution hJ hJ' hu hu') P hPΩ hcard htrans
      hinv hodd hE2 hthin with hind | ⟨m, hm, ⟨I⟩⟩ | hI | hI
  · exact fun N N' hN hN' hne => hind N hN N' hN' hne
  · intro N N' hN _ _ _
    exact hS.false_of_aeIdent hL.center hall hN hm I hodd fun L hL => hS.trans L hL
  · exact absurd hI (tightCaseE64Leaf_holds n Y R S t hL hO hconn hsep hall)
  · exact absurd hI (tightCase29Leaf_holds n Y R S t hL hO hconn hsep hall)

end Cit3

end CFSG.ClassicalInvolution.Q3
