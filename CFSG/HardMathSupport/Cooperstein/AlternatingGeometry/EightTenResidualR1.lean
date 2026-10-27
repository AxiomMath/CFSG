module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenOutcomeFiveFinal
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenGivenNatural
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFour
public import CFSG.HardMathSupport.Cooperstein.Proving.SolvableSylowNormalizerAll
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenNaturalCases

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19 CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

variable {G : Type} [Group G] [Finite G]

open scoped Classical in
@[expose] def EightTenResidual' (S L : Subgroup G) (m : ℕ) : Prop :=
  ∃ θ : ↥(L ⊔ S) →* Perm (Fin m), NaturalSectionTheta S L m θ ∧
    (∀ m' : ↥(L ⊔ S), θ m' = 1 → (m' : G) ∈ S) ∧
    ((∃ r : ℕ, 1 ≤ r ∧ 2 * r + 4 = m ∧ (r = 1 ∨ r = 3 ∨ 5 ≤ r) ∧
      ∃ e : Fin m ≃ OmegaE r 4,
        ((thompsonJ S).subgroupOf (L ⊔ S)).map (e.permCongrHom.toMonoidHom.comp θ) = Wr r 4) ∨
    (∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ∃ x : Fin m,
      Nat.card (orbit ((A.subgroupOf (L ⊔ S)).map θ) x) = 4) ∨
    (∃ (A : Subgroup G) (σ : Perm (Fin m)) (c : Fin m → Bool), IsMaxElemAbelian S A ∧
      BlockData ((A.subgroupOf (L ⊔ S)).map θ) σ c ∧ ∃ x, (cls c x).card = 4) ∨
    ∃ σ : Perm (Fin m), ∃ (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x),
      (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m))) ≤
        pairPres σ hσ1 hσ2 ∧
      (∀ x y, y ≠ x → y ≠ σ x →
        swap x (σ x) ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m))) →
        swap y (σ y) ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m))) →
        swap x (σ x) * swap y (σ y) ∈
          (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))) ∧
      (Finset.univ.filter fun x : Fin m => swap x (σ x) ∉
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))).card ≠ 2 * 1 ∧
      ((Finset.univ.filter fun x : Fin m => swap x (σ x) ∉
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))).card = 2 * 4 ∨
      (Finset.univ.filter fun x : Fin m => swap x (σ x) ∈
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))).card = 2 * 4))

theorem eightTen_outcomes_or_residual'
    (hnat : GF2NaturalLSL) {X S L : Subgroup G}
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) {m : ℕ}
    (hm : 8 < m)
    (e : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m))
    (hN : NaturalSectionLSL S L m) :
    EightTenOutcomes X S L ∨ EightTenResidual' S L m := by
  classical
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  obtain ⟨θ, hNS, hθS, h⟩ := eightTen_cases_of_natural hX hA hL hm e hN
  rcases h with (⟨r, s, hr1, hs1, hrs, hD, hDX, hY3, hYS, hT, he4⟩ | ⟨n, hn5, hn, hPAD⟩) | hb | hc |
    ⟨σ, hσ1, hσ2, hle, hD, hN1, hN2, hC2, hPAD⟩
  · by_cases hgood : (r = 1 ∨ r = 3 ∨ 5 ≤ r) ∧ (s = 1 ∨ s = 3 ∨ 5 ≤ s)
    · have hY := hYS hgood.1 hgood.2
      rcases Nat.even_or_odd m with hmev | hmodd
      · have hs6 : 6 ≤ s := by
          obtain ⟨k, hk⟩ := hmev
          rcases hgood.2 with h1 | h1 | h1 <;> omega
        exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr
          (outcomeFive_of_caseA' hX hA hL hm hmev e hN hr1 hrs hgood.1 hs6 hDX hY)))))
      · exact Or.inl (Or.inl (outcomeOne_of_caseA_odd' hX hA hL hm hmodd e hN hY))
    · have hDXX : EightBlockData X S L r s := hDX X hA hL hSL symAutInner
      by_cases hr : r = 2 ∨ r = 4
      · exfalso
        rcases hr with rfl | rfl
        · exact eightTwo_false hA hL.toIsTwoPrimeComponent hSL
            (Proving.solvableSylowNormalizerAll G X S hX hA) hDXX
        · exact Coordinator.eightBlockData_four_false (N := m) (s := s) hnat hX hA hL hSL hs1
            (by omega) hDXX
      · have hrgood : r = 1 ∨ r = 3 ∨ 5 ≤ r := by omega
        have hsbad : s = 2 ∨ s = 4 := by
          by_contra hs
          exact hgood ⟨hrgood, by omega⟩
        rcases hsbad with rfl | rfl
        · exfalso
          obtain ⟨θ', hker', hAlt', hW'⟩ := hT
          exact false_of_theta_s_two (Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL)
            (le_sup_right : S ≤ L ⊔ S) θ' hker' hAlt' hW' hr1 hrgood
        · obtain ⟨e4, he4'⟩ := he4
          exact Or.inr ⟨θ, hNS, hθS, Or.inl ⟨r, hr1, hrs, hrgood, e4, he4'⟩⟩
  · refine Or.inl (Or.inr (Or.inr (Or.inl ⟨n, hn5, hPAD, ?_⟩)))
    have := hN.naturalSectionL
    rwa [← hn] at this
  · exact Or.inr ⟨θ, hNS, hθS, Or.inr (Or.inl hb)⟩
  · exact Or.inr ⟨θ, hNS, hθS, Or.inr (Or.inr (Or.inl hc))⟩
  · by_cases h8 : (Finset.univ.filter fun x : Fin m => swap x (σ x) ∉
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))).card = 2 * 4 ∨
      (Finset.univ.filter fun x : Fin m => swap x (σ x) ∈
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))).card = 2 * 4
    · exact Or.inr ⟨θ, hNS, hθS, Or.inr (Or.inr (Or.inr ⟨σ, hσ1, hσ2, hle, hD, hN1, h8⟩))⟩
    · push Not at h8
      obtain ⟨ι, i1, i2, eι, hcard, -⟩ := exists_blockEquiv σ hσ1 hσ2
      have hmn : 2 * Fintype.card ι = m := by simpa using hcard.symm
      refine Or.inl (Or.inr (Or.inr (Or.inl ⟨Fintype.card ι, by omega,
        hPAD _ (by omega) hmn h8.1 h8.2, ?_⟩)))
      have := hN.naturalSectionL
      rwa [← hmn] at this

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
