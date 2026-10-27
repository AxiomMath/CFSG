module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Stab8

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

theorem seg27_case0 {S₀ S₁ X₀ X₁ : Subgroup (Equiv.Perm (Fin 8))} {p₀ q₀ p₁ q₁ : Fin 8}
    (h02 : p₀ ≠ p₁) (h03 : p₀ ≠ q₁) (h12 : q₀ ≠ p₁) (h13 : q₀ ≠ q₁)
    (h₀ : Seg27Six X₀ p₀ q₀) (h₁ : Seg27Six X₁ p₁ q₁)
    (hS₀ : S₀ ≤ alternatingGroup (Fin 8)) (hS₁ : S₁ ≤ alternatingGroup (Fin 8))
    (hcS₀ : Nat.card S₀ = 120) (hcS₁ : Nat.card S₁ = 120) (hX₀ : X₀ ≤ S₀) (hX₁ : X₁ ≤ S₁) :
    ∃ g ∈ S₀ ⊓ S₁, orderOf g = 2 := by
  have hSt₀ : Nat.card (S₀ ⊓ seg27PairStab p₁ q₁ : Subgroup (Equiv.Perm (Fin 8))) = 8 :=
    seg27_card_inf_pairStab h02 h03 h12 h13 h₁.ne h₀ hcS₀ hX₀
  have hSt₁ : Nat.card (S₁ ⊓ seg27PairStab p₀ q₀ : Subgroup (Equiv.Perm (Fin 8))) = 8 :=
    seg27_card_inf_pairStab h02.symm h12.symm h03.symm h13.symm h₀.ne h₁ hcS₁ hX₁
  have hbox : Nat.card (alternatingGroup (Fin 8) ⊓ seg27PairStab p₀ q₀ ⊓ seg27PairStab p₁ q₁ :
      Subgroup (Equiv.Perm (Fin 8))) ≤ 48 :=
    seg27_card_box_le h₀.ne h02 h03 h12 h13 h₁.ne
  have hle₀ : (S₀ ⊓ seg27PairStab p₁ q₁ : Subgroup (Equiv.Perm (Fin 8))) ≤
      (alternatingGroup (Fin 8) ⊓ seg27PairStab p₀ q₀ ⊓ seg27PairStab p₁ q₁ :
        Subgroup (Equiv.Perm (Fin 8))) := by
    refine le_inf (le_inf ?_ ?_) ?_
    · exact le_trans inf_le_left hS₀
    · exact le_trans inf_le_left (seg27_le_pairStab h₀ hX₀ hcS₀)
    · exact inf_le_right
  have hle₁ : (S₁ ⊓ seg27PairStab p₀ q₀ : Subgroup (Equiv.Perm (Fin 8))) ≤
      (alternatingGroup (Fin 8) ⊓ seg27PairStab p₀ q₀ ⊓ seg27PairStab p₁ q₁ :
        Subgroup (Equiv.Perm (Fin 8))) := by
    refine le_inf (le_inf ?_ ?_) ?_
    · exact le_trans inf_le_left hS₁
    · exact inf_le_right
    · exact le_trans inf_le_left (seg27_le_pairStab h₁ hX₁ hcS₁)
  have hmul := seg27_card_mul_card_le hle₀ hle₁
  rw [hSt₀, hSt₁] at hmul
  have hk : 2 ≤ Nat.card ((S₀ ⊓ seg27PairStab p₁ q₁) ⊓ (S₁ ⊓ seg27PairStab p₀ q₀) :
      Subgroup (Equiv.Perm (Fin 8))) := by
    by_contra h
    push Not at h
    have h1 : Nat.card ((S₀ ⊓ seg27PairStab p₁ q₁) ⊓ (S₁ ⊓ seg27PairStab p₀ q₀) :
        Subgroup (Equiv.Perm (Fin 8))) ≤ 1 := by omega
    have hle := Nat.mul_le_mul hbox h1
    omega
  have hdvd : Nat.card ((S₀ ⊓ seg27PairStab p₁ q₁) ⊓ (S₁ ⊓ seg27PairStab p₀ q₀) :
      Subgroup (Equiv.Perm (Fin 8))) ∣ 2 ^ 3 := by
    have h : Nat.card ((S₀ ⊓ seg27PairStab p₁ q₁) ⊓ (S₁ ⊓ seg27PairStab p₀ q₀) :
        Subgroup (Equiv.Perm (Fin 8))) ∣
        Nat.card (S₀ ⊓ seg27PairStab p₁ q₁ : Subgroup (Equiv.Perm (Fin 8))) :=
      Subgroup.card_dvd_of_le
        (inf_le_left : ((S₀ ⊓ seg27PairStab p₁ q₁) ⊓ (S₁ ⊓ seg27PairStab p₀ q₀) :
            Subgroup (Equiv.Perm (Fin 8))) ≤ S₀ ⊓ seg27PairStab p₁ q₁)
    rw [hSt₀] at h
    simpa using h
  have h2dvd : 2 ∣ Nat.card ((S₀ ⊓ seg27PairStab p₁ q₁) ⊓ (S₁ ⊓ seg27PairStab p₀ q₀) :
      Subgroup (Equiv.Perm (Fin 8))) := by
    obtain ⟨k, _hk3, hkeq⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hdvd
    have hk1 : 1 ≤ k := by
      by_contra h
      push Not at h
      have hk0 : k = 0 := by omega
      rw [hk0] at hkeq
      have hone : Nat.card ((S₀ ⊓ seg27PairStab p₁ q₁) ⊓ (S₁ ⊓ seg27PairStab p₀ q₀) :
          Subgroup (Equiv.Perm (Fin 8))) = 1 := by
        simpa [hkeq]
      omega
    rw [hkeq]
    exact pow_dvd_pow 2 hk1
  obtain ⟨g, hg, hg2⟩ := seg27_exists_orderOf_two
    ((S₀ ⊓ seg27PairStab p₁ q₁) ⊓ (S₁ ⊓ seg27PairStab p₀ q₀)) h2dvd
  exact ⟨g, ⟨hg.1.1, hg.2.1⟩, hg2⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
