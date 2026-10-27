module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81B
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81Monster
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSROrd
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0ClsK

public section

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder sporFactors)

set_option linter.unusedSectionVars false

theorem co2_dvd_sporOrder (s : TauCeti.SporadicName) (h : 42305421312000 ∣ sporOrder s) :
    s = .Co1 ∨ s = .Co2 ∨ s = .B ∨ s = .M := by
  cases s <;> first
    | (left; rfl) | (right; left; rfl) | (right; right; left; rfl) | (right; right; right; rfl)
    | (exfalso; revert h; simp only [sporOrder, sporFactors]; decide)

theorem sporOrder_co2 : sporOrder .Co2 = 42305421312000 := by
  simp only [sporOrder, sporFactors]
  decide


theorem ds81_sporadic {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) {s : TauCeti.SporadicName} (e : X ≃* Carrier s) (τ : X)
    (hτ : orderOf τ = 2) (_hchar : IsCharacteristicP 2 ↥(centralizer ({τ} : Set X)))
    (hab : IsMulCommutative (pCore 2 ↥(centralizer ({τ} : Set X)))) :
    ¬ Nonempty (↥(centralizer ({τ} : Set X)) ⧸ pCore 2 ↥(centralizer ({τ} : Set X)) ≃*
      Carrier .Co2) := by
  rintro ⟨f⟩
  have hG : Nat.card (Carrier .Co2) = 42305421312000 := CFSG.Sporadic.Co2.card_Co2
  have hshape : IsCo2Shape (Nat.card ↥(centralizer ({τ} : Set X))) :=
    isCo2Shape_of_quotient f hG
  have hCX : Nat.card ↥(centralizer ({τ} : Set X)) ∣ Nat.card X :=
    Subgroup.card_subgroup_dvd_card _
  by_cases hM : s = .M
  · subst hM
    exact hshape.not_dvd_thirteen (monster_centralizer_thirteen e hτ)
  · have hX : Nat.card X = sporOrder s :=
      (Nat.card_congr e.toEquiv).trans
        (CFSG.ComponentClassification.GSThmB.QPUSpor.card_carrier_eq_sporOrder s hM)
    have hdvd : 42305421312000 ∣ sporOrder s := by
      rw [← hX]
      exact hshape.dvd.trans hCX
    rcases co2_dvd_sporOrder s hdvd with rfl | rfl | rfl | rfl
    ·
      have h3 := CFSG.EvenSporadicStandard.TwoCo1.card_centralizer_involution_of_isSporadic_co1
        (Y := X) ⟨e⟩ hτ
      have hd := hshape.dvd
      rcases h3 with h | h | h <;> rw [h] at hd <;> revert hd <;> norm_num
    ·
      have hpos : 0 < Nat.card ↥(centralizer ({τ} : Set X)) := Nat.card_pos
      have hle : 42305421312000 ≤ Nat.card ↥(centralizer ({τ} : Set X)) :=
        Nat.le_of_dvd hpos hshape.dvd
      have hXc : Nat.card X = 42305421312000 := hX.trans sporOrder_co2
      have heq : Nat.card ↥(centralizer ({τ} : Set X)) = Nat.card X :=
        le_antisymm (Nat.le_of_dvd Nat.card_pos hCX) (hXc ▸ hle)
      have htop : centralizer ({τ} : Set X) = ⊤ :=
        (Subgroup.card_eq_iff_eq_top _).1 heq
      have hcent : τ ∈ center X := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : g ∈ centralizer ({τ} : Set X) := by rw [htop]; trivial
        exact Subgroup.mem_centralizer_singleton_iff.1 hg
      have hbot : center X = ⊥ := by
        rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
        · exact h
        · exfalso
          obtain ⟨a, b, hab'⟩ := hna
          apply hab'
          have ha : a ∈ center X := by rw [h]; trivial
          exact ((Subgroup.mem_center_iff.1 ha) b).symm
      rw [hbot, Subgroup.mem_bot] at hcent
      rw [hcent, orderOf_one] at hτ
      exact absurd hτ (by norm_num)
    ·
      exact baby_not_isCo2Shape e τ hτ hab hshape
    · exact absurd rfl hM

end CFSG.ComponentClassification.CatFC.DS81
