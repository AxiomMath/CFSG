module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArms
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenArm
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpL4Order
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.ResidualA8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.HarrisLit.T1.SporRow (not_oddLieOrder_L34)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer (alt_degree_unique)


variable {S : Type} [Group S] [Finite S]

theorem card_quotient_of_alt8 {X : Type} [Group X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 8))) : Nat.card X = 20160 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem rows_alt8 (s : TauCeti.SporadicName) (hd : 20160 ∣ AGLEmbedding.sporOrd s) :
    (SporadicInnerRow s 20160 → s = .McL ∨ s = .Suz ∨ s = .ONan ∨ s = .He) ∧
      (SporadicOuterRow s 20160 → s = .HS) := by
  cases s <;> first
    | exact absurd hd (by simp only [AGLEmbedding.sporOrd]; decide)
    | (simp only [SporadicInnerRow, SporadicOuterRow]; decide)

theorem lieModel_psl44_of_even_alt8 (hO : LieOrderFormulasInput)
    (hEI : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
      ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B)
    (hT : EvenOuterTypedInput) [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (heven : EvenLieType S) {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)}
    (hD : IsComponent D) (hA8 : Nonempty (↥D ⧸ center ↥D ≃* alternatingGroup (Fin 8))) :
    LieModel S .PSL 4 2 2 := by
  obtain ⟨τ, n, f, hadm, hmod⟩ := heven
  obtain ⟨-, h⟩ := even_arm_typed hEI hT hna hadm hmod hσ hD
  rcases h with ⟨τ', n', f', hadm', hmod', himp⟩ | hA | hU
  · obtain ⟨h1, h2, h3⟩ := eq_psl_four_one_of_lieModel_two_of_alt8 hO hadm' hmod' hA8
    obtain ⟨rfl, rfl, rfl⟩ := himp h1 h2
    subst h3
    exact hmod
  · exact absurd (alt_degree_unique (by norm_num) (by norm_num) hA hA8) (by norm_num)
  · have hadm3 : StatedLieAdmissible .PSU 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
    obtain ⟨-, h1, h2⟩ := hO _ .PSU 3 3 1 hadm3 hU
    rw [card_quotient_of_alt8 hA8] at h1 h2
    exact absurd ⟨.PSU, 3, 3, 1, Nat.prime_three, by norm_num, hadm3, h1, h2⟩ not_oddLieOrder_L34

theorem clause1_of_inputs (I : ArmInputs) (hT : EvenOuterTypedInput) (hHSO : HeSuzONNoAltEight)
    (hMcL : ∀ {S : Type} [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      (S ≃* Carrier .McL) → ∀ {σ : MulAut S}, orderOf σ = 2 →
      σ ∈ (MulAut.conj : S →* MulAut S).range → ∀ {D : Subgroup ↥(fixedSubgroup σ)},
      IsComponent D → Nat.card (center ↥D) = 2)
    [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D)
    (hA8 : Nonempty (↥D ⧸ center ↥D ≃* alternatingGroup (Fin 8))) :
    (∃ m : ℕ, 5 ≤ m ∧ Nonempty (S ≃* alternatingGroup (Fin (2 * m)))) ∨ IsSporadic S .HS ∨
      LieModel S .PSL 4 2 2 ∨ (IsSporadic S .McL ∧ Nat.card (center ↥D) = 2) := by
  have hc : Nat.card (↥D ⧸ center ↥D) = 20160 := card_quotient_of_alt8 hA8
  rcases catalog_fixed_component I.gls I.evenInner I.evenOuter hna hcat hσ hD with
    ⟨n, k, -, hk5, hkn, hpar, ⟨θ⟩, hDk⟩ | ⟨-, hodd⟩ | ⟨heven, -⟩ | ⟨s', ⟨es⟩⟩
  · have hk : k = 8 := alt_degree_unique (by omega) (by norm_num) hDk hA8
    subst hk
    obtain ⟨r, hr⟩ := hpar
    have hn : n = 2 * (4 + r) := by omega
    subst hn
    exact Or.inl ⟨4 + r, by omega, ⟨θ⟩⟩
  · exfalso
    rcases hodd with ⟨τ', n', p, f', hp, hp2, hadm', hY⟩ | hL8
    · obtain ⟨-, h1, h2⟩ := I.order _ τ' n' p f' hadm' hY
      rw [hc] at h1 h2
      exact not_oddLieOrder_L34 ⟨τ', n', p, f', hp, hp2, hadm', h1, h2⟩
    · have hadmL : StatedLieAdmissible .PSL 2 2 3 :=
        ⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩
      obtain ⟨-, h1, -⟩ := I.order _ .PSL 2 2 3 hadmL hL8
      have h504 : Nat.card ↥D = 504 := by
        simp only [lieOrderDivisor, lieOrderNumerator] at h1
        norm_num [Finset.Icc_self] at h1
        omega
      have hle : Nat.card (↥D ⧸ center ↥D) ≤ Nat.card ↥D :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      omega
  · exact Or.inr (Or.inr (Or.inl
      (lieModel_psl44_of_even_alt8 I.order I.evenInner hT hna heven hσ hD hA8)))
  · obtain ⟨hdvd, hin, hout⟩ := I.table ‹IsSimpleGroup S› hna es hσ hD
    rw [hc] at hdvd hin hout
    obtain ⟨hr1, hr2⟩ := rows_alt8 s' hdvd
    by_cases hinn : σ ∈ (MulAut.conj : S →* MulAut S).range
    · rcases hr1 (hin hinn) with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr ⟨⟨es⟩, hMcL ‹IsSimpleGroup S› hna es hσ hinn hD⟩))
      · exact absurd hA8 (hHSO S ‹IsSimpleGroup S› hna (Or.inr (Or.inl ⟨es⟩)) σ hσ D hD)
      · exact absurd hA8 (hHSO S ‹IsSimpleGroup S› hna (Or.inr (Or.inr ⟨es⟩)) σ hσ D hD)
      · exact absurd hA8 (hHSO S ‹IsSimpleGroup S› hna (Or.inl ⟨es⟩) σ hσ D hD)
    · have h := hr2 (hout hinn)
      subst h
      exact Or.inr (Or.inl ⟨es⟩)

end CFSG.ComponentClassification.CatFC
