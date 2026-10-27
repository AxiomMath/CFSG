module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArms
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer (alt_degree_unique card_eq_of_alt_equiv)
open CFSG.OddStandard.AltStdSec (not_oddLieType_alt not_evenLieType_alt)

theorem oddLieType_transport {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : OddLieType X) : OddLieType Y := by
  obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := h
  exact ⟨t, n, p, f, hp, hp2, hadm, CFSG.Blueprint.LieModel.of_mulEquiv e hm⟩

theorem evenLieType_transport {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : EvenLieType X) : EvenLieType Y := by
  obtain ⟨t, n, f, hadm, hm⟩ := h
  exact ⟨t, n, f, hadm, CFSG.Blueprint.LieModel.of_mulEquiv e hm⟩

theorem sporOrd_pos_lt (s : TauCeti.SporadicName) :
    0 < AGLEmbedding.sporOrd s ∧ AGLEmbedding.sporOrd s < 10 ^ 54 := by
  cases s <;> norm_num [AGLEmbedding.sporOrd]

theorem rows_alt_even (s : TauCeti.SporadicName) {j : ℕ} (hj : 5 ≤ j)
    (hd : (2 * j).factorial / 2 ∣ AGLEmbedding.sporOrd s) :
    (SporadicInnerRow s ((2 * j).factorial / 2) → False) ∧
      (SporadicOuterRow s ((2 * j).factorial / 2) → s = .HN ∧ j = 5) := by
  obtain ⟨hpos, hlt⟩ := sporOrd_pos_lt s
  have hle : (2 * j).factorial / 2 ≤ AGLEmbedding.sporOrd s := Nat.le_of_dvd hpos hd
  have hj22 : j < 22 := by
    by_contra h
    have h44 : (44 : ℕ).factorial ≤ (2 * j).factorial := Nat.factorial_le (by omega)
    have h3 : (44 : ℕ).factorial / 2 ≤ (2 * j).factorial / 2 := Nat.div_le_div_right h44
    have h4 : 10 ^ 54 ≤ (44 : ℕ).factorial / 2 := by norm_num [Nat.factorial]
    exact absurd (h4.trans (h3.trans hle)) (not_le.mpr hlt)
  interval_cases j <;> cases s <;> simp only [SporadicInnerRow, SporadicOuterRow] <;>
    revert hd <;> decide

variable {S : Type} [Group S] [Finite S]

theorem clause2_of_inputs (I : ArmInputs) [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (hcat : Catalog S) {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)}
    (hD : IsComponent D) {j : ℕ} (hj : 5 ≤ j)
    (hA : Nonempty (↥D ⧸ center ↥D ≃* alternatingGroup (Fin (2 * j)))) :
    (∃ m : ℕ, j < m ∧ Nonempty (S ≃* alternatingGroup (Fin (2 * m)))) ∨
      (j = 5 ∧ IsSporadic S .HN) := by
  have hc : Nat.card (↥D ⧸ center ↥D) = (2 * j).factorial / 2 :=
    card_eq_of_alt_equiv (n := 2 * j) (by omega) hA
  have h10 : 3628800 ≤ (2 * j).factorial := by
    have h := Nat.factorial_le (show 10 ≤ 2 * j by omega)
    norm_num [Nat.factorial] at h
    exact h
  rcases catalog_fixed_component I.gls I.evenInner I.evenOuter hna hcat hσ hD with
    ⟨n, k, -, hk5, hkn, hpar, hSn, hDk⟩ | ⟨hodd, hD'⟩ | ⟨heven, -, hE⟩ | ⟨s, ⟨es⟩⟩
  ·
    have hk : k = 2 * j := alt_degree_unique (by omega) (by omega) hDk hA
    obtain ⟨r, hr⟩ := hpar
    have hn : n = 2 * (j + r) := by omega
    subst hn
    exact Or.inl ⟨j + r, by omega, hSn⟩
  ·
    exfalso
    rcases hD' with hO | hL
    · obtain ⟨eA⟩ := hA
      exact not_oddLieType_alt I.order (m := 2 * j) (by omega)
        (oddLieType_transport eA hO)
    · have hadmL : StatedLieAdmissible .PSL 2 2 3 :=
        ⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩
      obtain ⟨-, h1, -⟩ := I.order _ .PSL 2 2 3 hadmL hL
      have h504 : Nat.card ↥D = 504 := by
        simp only [lieOrderDivisor, lieOrderNumerator] at h1
        norm_num [Finset.Icc_self] at h1
        omega
      have hle : Nat.card (↥D ⧸ center ↥D) ≤ Nat.card ↥D :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      rw [hc, h504] at hle
      omega
  ·
    exfalso
    rcases hE with hE' | hA6 | hU
    · obtain ⟨eA⟩ := hA
      exact not_evenLieType_alt I.order (m := 2 * j) (by omega)
        (evenLieType_transport eA hE')
    · have h6 : 2 * j = 6 := alt_degree_unique (by omega) (by norm_num) hA hA6
      omega
    · have hadm3 : StatedLieAdmissible .PSU 3 3 1 :=
        ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
      obtain ⟨-, h1, -⟩ := I.order _ .PSU 3 3 1 hadm3 hU
      have h6048 : Nat.card (↥D ⧸ center ↥D) = 6048 := by
        have hnum : lieOrderNumerator .PSU 3 (3 ^ 1) = 6048 := by decide
        have hdiv : lieOrderDivisor .PSU 3 (3 ^ 1) = 1 := by decide
        rw [hnum, hdiv, mul_one] at h1
        exact h1
      omega
  ·
    obtain ⟨hdvd, hin, hout⟩ := I.table ‹IsSimpleGroup S› hna es hσ hD
    rw [hc] at hdvd hin hout
    have hrows := rows_alt_even s hj hdvd
    by_cases hinn : σ ∈ (MulAut.conj : S →* MulAut S).range
    · exact (hrows.1 (hin hinn)).elim
    · obtain ⟨rfl, rfl⟩ := hrows.2 (hout hinn)
      exact Or.inr ⟨rfl, Nonempty.intro es⟩

end CFSG.ComponentClassification.CatFC
