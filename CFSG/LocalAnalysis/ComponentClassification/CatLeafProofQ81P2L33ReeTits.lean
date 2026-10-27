module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33ReeTools
public import CFSG.Sporadic.Schreier.TitsInter
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.Ree

open CFSG Subgroup CFSG.Sporadic.Schreier.Tits

theorem card_centralizer_of_isConj {G : Type*} [Group G] {x y : G} (h : IsConj x y) :
    Nat.card (centralizer ({x} : Set G)) = Nat.card (centralizer ({y} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc, ← map_conj_centralizer, card_map_of_injective (MulAut.conj c).injective]

theorem ne_two_pow_of_odd_dvd {n m : ℕ} (hm : 3 ≤ m) (hmo : Odd m) (hmn : m ∣ n) (k : ℕ) :
    n ≠ 2 ^ k := by
  rintro rfl
  have h1 : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hmo)
  have h2 : m ∣ 1 := by
    have := Nat.Coprime.gcd_eq_one h1
    rw [← this]
    exact Nat.dvd_gcd dvd_rfl hmn
  have := Nat.le_of_dvd one_pos h2
  omega

theorem tits_not_isPGroup
    (α : MulAut titsD) (hα : orderOf α = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints α) ⧸ pPrimeCore 2 ↥(fixedPoints α)) := by
  obtain ⟨x, hx2, rfl⟩ := mem_inner_of_orderOf_two hα
  rw [fixedPoints_conj]
  obtain ⟨-, -, -, hcls, -, -, -, hH, hHc, -, -, -, -, hN, hNc, -, -, -, -, hodd⟩ :=
    CTUC_Tits_two_involution_classes_and_centralizer_two_kernels
  apply not_isPGroup_of_card
  · exact hodd x hx2 _ inferInstance (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  · intro k
    rcases hcls x hx2 with hz | ht
    · rw [← card_centralizer_of_isConj hz]
      have h1 : Nat.card (centralizer ({titsZD} : Set titsD)) = 10240 := by
        rw [← card_map_of_injective titsD.subtype_injective,
          CFSG.Sporadic.Schreier.Tits.map_subtype_centralizer]
        change Nat.card ↥(titsD ⊓ centralizer {titsZ}) = 10240
        rw [hH, hHc]
      rw [h1]
      exact ne_two_pow_of_odd_dvd (m := 5) (by norm_num) (by decide) (by norm_num) k
    · rw [← card_centralizer_of_isConj ht]
      have h1 : Nat.card (centralizer ({titsTD} : Set titsD)) = 1536 := by
        rw [← card_map_of_injective titsD.subtype_injective,
          CFSG.Sporadic.Schreier.Tits.map_subtype_centralizer]
        change Nat.card ↥(titsD ⊓ centralizer {titsTInv}) = 1536
        rw [← hN, hNc]
      rw [h1]
      exact ne_two_pow_of_odd_dvd (m := 3) (by norm_num) (by decide) (by norm_num) k

theorem tits_not_isPGroup_of_model
    (Y : Type) [Group Y] [Finite Y] {p f : ℕ} (hY : Blueprint.ReeTitsModel Y .Tits p f)
    (a : MulAut Y) (ha : orderOf a = 2) :
    ¬ IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) := by
  obtain ⟨e⟩ := titsModelEquiv Y p f hY
  exact not_isPGroup_of_mulEquiv e tits_not_isPGroup a ha

end CFSG.ComponentClassification.HarrisLit.L33.Ree
