module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4FinkTwoA
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup CFSG.ComponentClassification.M12Cover

theorem noNormalFour_centralizer_of_abelian_two {J : Type*} [Group J] [Finite J] (y : J)
    (hF : ∀ {M P : Subgroup J}, M ≤ centralizer ({y} : Set J) →
      (∀ c ∈ centralizer ({y} : Set J), ∀ m ∈ M, c * m * c⁻¹ ∈ M) →
      (∀ Q : Subgroup J, Q ≤ M → IsPGroup 2 Q → ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) →
      P ≤ M → IsPGroup 2 P → 4 ≤ Nat.card P → False) :
    NoNormalFour (centralizer ({y} : Set J)) := by
  have key : ∀ N : Subgroup (centralizer ({y} : Set J)), N.Normal →
      (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) → IsPGroup 2 N → 4 ≤ Nat.card N → False := by
    intro N hN hab h2 h4
    let M : Subgroup J := N.map (centralizer ({y} : Set J)).subtype
    have hMz : M ≤ centralizer ({y} : Set J) := by
      rintro _ ⟨n, -, rfl⟩
      exact n.2
    have hMn : ∀ c ∈ centralizer ({y} : Set J), ∀ m ∈ M, c * m * c⁻¹ ∈ M := by
      rintro c hc _ ⟨n, hn, rfl⟩
      exact ⟨⟨c, hc⟩ * n * ⟨c, hc⟩⁻¹, hN.conj_mem n hn ⟨c, hc⟩, rfl⟩
    have hMab : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hab a ha b hb)
    have hMcard : Nat.card M = Nat.card N :=
      Subgroup.card_map_of_injective (centralizer ({y} : Set J)).subtype_injective
    have hMp : IsPGroup 2 M := by
      obtain ⟨k, hk⟩ := h2.exists_card_eq
      exact IsPGroup.of_card (n := k) (by rw [hMcard, hk])
    exact hF hMz hMn (fun Q hQ _ x hx y hy => hMab x (hQ hx) y (hQ hy)) le_rfl hMp
      (by rw [hMcard]; exact h4)
  intro N hN
  refine ⟨⟨fun e => ?_⟩, ⟨fun e => ?_⟩⟩
  · refine key N hN ?_ ?_ ?_
    · intro x hx y hy
      have h : (⟨x, hx⟩ : N) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
        e.injective (by rw [map_mul, map_mul, mul_comm])
      exact congrArg Subtype.val h
    · exact IsPGroup.of_card (n := 2) (by rw [Nat.card_congr e.toEquiv]; simp)
    · rw [Nat.card_congr e.toEquiv]; simp
  · refine key N hN ?_ ?_ ?_
    · intro x hx y hy
      have h : (⟨x, hx⟩ : N) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
        e.injective (by rw [map_mul, map_mul, mul_comm])
      exact congrArg Subtype.val h
    · exact IsPGroup.of_card (n := 3) (by rw [Nat.card_congr e.toEquiv]; simp)
    · rw [Nat.card_congr e.toEquiv]; simp

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.ComponentClassification.RankTwoSporadic.J4Fink in
theorem noNormalFour_centralizer_eta_1131 :
    NoNormalFour (centralizer ({eta uJ 11 1131} : Set J)) :=
  noNormalFour_centralizer_of_abelian_two _ fun hMz hMn hab hPM hP hP4 =>
    false_of_twoA hMz hMn hab hPM hP hP4

end CFSG.EvenSporadicStandard.J4Std
