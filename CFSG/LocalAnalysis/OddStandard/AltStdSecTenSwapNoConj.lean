module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapTwist
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapReps

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G}

theorem mul_liftS8_mul_self {x : G}
    {π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)} (hOS : OneSided z ι x π)
    {ρ : Perm (Fin 8)} (hρ2 : ρ * ρ = 1) :
    (x * ι (liftS8 ρ)) * (x * ι (liftS8 ρ)) = 1 := by
  have hL2 : liftS8 ρ * liftS8 ρ = 1 := by rw [← map_mul, hρ2, map_one]
  have hτ2 : τ₀ * τ₀ = 1 := τ₀_mul_self
  rw [hOS.eq, ← map_mul, ← map_mul]
  rw [show (τ₀ * liftS8 ρ) * (τ₀ * liftS8 ρ) = 1 from by
    calc (τ₀ * liftS8 ρ) * (τ₀ * liftS8 ρ) = τ₀ * (liftS8 ρ * τ₀) * liftS8 ρ := by group
      _ = τ₀ * (τ₀ * liftS8 ρ) * liftS8 ρ := by rw [liftS8_mul_τ₀]
      _ = (τ₀ * τ₀) * (liftS8 ρ * liftS8 ρ) := by group
      _ = 1 := by rw [hτ2, hL2, mul_one]]
  rw [map_one]

theorem isConj_of_card_cycleType_and_kappa {x : G}
    {π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)} (hOS : OneSided z ι x π)
    {κ : ↥(centralizer ({x} : Set G)) →* ℤˣ} (hκ : Retraction z x κ)
    {c c' : ↥(centralizer ({x} : Set G))} (hc2 : c * c = 1) (hc'2 : c' * c' = 1)
    (hcard : Multiset.card (π c).cycleType = Multiset.card (π c').cycleType)
    (hκc : κ c = κ c') : IsConj (c : G) (c' : G) := by
  have hπc2 : π c * π c = 1 := by rw [← map_mul, hc2, map_one]
  have hπc'2 : π c' * π c' = 1 := by rw [← map_mul, hc'2, map_one]
  exact isConj_of_retraction hOS.sec hκ.self
    (isConj_of_card_cycleType_eq hπc2 hπc'2 hcard) hκc

theorem isConj_x_mul_liftS8_of_involutions (hC : CentData z ι) (hN : NoSwapConj z ι) {x : G}
    {π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)} (hOS : OneSided z ι x π)
    {κ : ↥(centralizer ({x} : Set G)) →* ℤˣ} (hκ : Retraction z x κ)
    {ρ ρ' : Perm (Fin 8)} (hρ2 : ρ * ρ = 1) (hρ'2 : ρ' * ρ' = 1)
    (hsignρ : sign ρ = 1) (hsignρ' : sign ρ' = -1)
    (hcard : Multiset.card ρ.cycleType + (if Odd (Multiset.card ρ.cycleType) then 1 else 0) =
      Multiset.card ρ'.cycleType + (if Odd (Multiset.card ρ'.cycleType) then 1 else 0)) :
    IsConj (x * ι (liftS8 ρ)) (ι (liftS8 ρ')) := by
  have hρx : ι (liftS8 ρ) ∈ centralizer ({x} : Set G) := by
    rw [hOS.eq]; exact ι_liftS8_mem_centralizer ι ρ
  have hzρ : z * ι (liftS8 ρ) ∈ centralizer ({x} : Set G) :=
    z_mul_liftS8_mem_centralizer hC hOS ρ
  have hρ'x : ι (liftS8 ρ') ∈ centralizer ({x} : Set G) := by
    rw [hOS.eq]; exact ι_liftS8_mem_centralizer ι ρ'
  have hzρ' : z * ι (liftS8 ρ') ∈ centralizer ({x} : Set G) :=
    z_mul_liftS8_mem_centralizer hC hOS ρ'
  obtain ⟨hκρ, hcardρ⟩ := twist_facts hC hN hOS hκ ρ hρx hzρ
  obtain ⟨hκρ', hcardρ'⟩ := twist_facts hC hN hOS hκ ρ' hρ'x hzρ'
  obtain ⟨hcardρ1, _⟩ := hcardρ hρ2
  obtain ⟨hcardρ'1, _⟩ := hcardρ' hρ'2
  let c : ↥(centralizer ({x} : Set G)) := selfC x * liftS8Centralizer (ι := ι) hOS.eq ρ
  let c' : ↥(centralizer ({x} : Set G)) := liftS8Centralizer (ι := ι) hOS.eq ρ'
  have hc2 : c * c = 1 := by
    apply Subtype.ext
    change (x * ι (liftS8 ρ)) * (x * ι (liftS8 ρ)) = 1
    exact mul_liftS8_mul_self hOS hρ2
  have hL'2 : liftS8 ρ' * liftS8 ρ' = 1 := by rw [← map_mul, hρ'2, map_one]
  have hc'2 : c' * c' = 1 := by
    apply Subtype.ext
    change (ι (liftS8 ρ') : G) * (ι (liftS8 ρ')) = 1
    rw [← map_mul, hL'2, map_one]
  have hcardπ : Multiset.card (π c).cycleType = Multiset.card (π c').cycleType := by
    change Multiset.card (π (selfC x * liftS8Centralizer (ι := ι) hOS.eq ρ)).cycleType =
      Multiset.card (π (liftS8Centralizer (ι := ι) hOS.eq ρ')).cycleType
    rw [map_mul, (hOS.sec.ker (selfC x)).2 (Or.inr rfl), one_mul,
      show π (liftS8Centralizer (ι := ι) hOS.eq ρ) = π ⟨ι (liftS8 ρ), hρx⟩ from
        congrArg π (Subtype.ext rfl),
      show π (liftS8Centralizer (ι := ι) hOS.eq ρ') = π ⟨ι (liftS8 ρ'), hρ'x⟩ from
        congrArg π (Subtype.ext rfl),
      hcardρ1, hcardρ'1]
    exact hcard
  have hκc : κ c = κ c' := by
    have h1 : κ (liftS8Centralizer (ι := ι) hOS.eq ρ) = sign ρ := by
      rw [show liftS8Centralizer (ι := ι) hOS.eq ρ = ⟨ι (liftS8 ρ), hρx⟩ from Subtype.ext rfl]
      exact hκρ
    have h2 : κ (liftS8Centralizer (ι := ι) hOS.eq ρ') = sign ρ' := by
      rw [show liftS8Centralizer (ι := ι) hOS.eq ρ' = ⟨ι (liftS8 ρ'), hρ'x⟩ from Subtype.ext rfl]
      exact hκρ'
    change κ (selfC x * liftS8Centralizer (ι := ι) hOS.eq ρ) =
      κ (liftS8Centralizer (ι := ι) hOS.eq ρ')
    rw [map_mul, hκ.self, h1, hsignρ, h2, hsignρ']
    decide
  have hconj := isConj_of_card_cycleType_and_kappa hOS hκ hc2 hc'2 hcardπ hκc
  have hcval : (c : G) = x * ι (liftS8 ρ) := rfl
  have hc'val : (c' : G) = ι (liftS8 ρ') := rfl
  rw [← hcval, ← hc'val]
  exact hconj

theorem not_isConj_z_ι_of_card_cycleType_eq_three (hC : CentData z ι) (hN : NoSwapConj z ι)
    {x : G} {π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)} (hOS : OneSided z ι x π)
    {κ : ↥(centralizer ({x} : Set G)) →* ℤˣ} (hκ : Retraction z x κ) {σ : Perm (Fin 10)}
    (hσ2 : σ * σ = 1) (hcard : Multiset.card σ.cycleType = 3) : ¬ IsConj z (ι σ) := by
  intro hconj
  have hσr₂ : IsConj σ (τ₀ * r₂) := (isConj_rep_of_card_cycleType hσ2).2.2.1 hcard
  have hισ : IsConj (ι σ) (ι (τ₀ * r₂)) := MonoidHom.map_isConj ι hσr₂
  have hτr : ι (τ₀ * r₂) = x * ι (liftS8 r₂') := by
    rw [τ₀_mul_r₂_eq, map_mul, ← hOS.eq]
  have hxconj : IsConj (x * ι (liftS8 r₂')) (ι (liftS8 r₁')) :=
    isConj_x_mul_liftS8_of_involutions hC hN hOS hκ r₂'_mul_self r₁'_mul_self
      sign_r₂' sign_r₁' (by rw [card_cycleType_r₂', card_cycleType_r₁']; decide)
  have hz : IsConj z (x * ι (liftS8 r₂')) := by
    have h := hconj.trans hισ
    rwa [hτr] at h
  have hz1 : IsConj z (ι r₁) := by
    have h := hz.trans hxconj
    rwa [liftS8_r₁'] at h
  exact (hN r₁ ⟨0, 1, by decide, rfl⟩).1 hz1

theorem not_isConj_z_ι_of_card_cycleType_eq_five (hC : CentData z ι) (hN : NoSwapConj z ι)
    {x : G} {π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)} (hOS : OneSided z ι x π)
    {κ : ↥(centralizer ({x} : Set G)) →* ℤˣ} (hκ : Retraction z x κ) {σ : Perm (Fin 10)}
    (hσ2 : σ * σ = 1) (hcard : Multiset.card σ.cycleType = 5) : ¬ IsConj z (ι σ) := by
  intro hconj
  have hσρ : IsConj σ (τ₀ * ρ₄) := (isConj_rep_of_card_cycleType hσ2).2.2.2.2 hcard
  have hισ : IsConj (ι σ) (ι (τ₀ * ρ₄)) := MonoidHom.map_isConj ι hσρ
  have hτρ : ι (τ₀ * ρ₄) = x * ι (liftS8 ρ₄') := by
    rw [τ₀_mul_ρ₄_eq, map_mul, ← hOS.eq]
  have hxconj : IsConj (x * ι (liftS8 ρ₄')) (ι (liftS8 r₃')) :=
    isConj_x_mul_liftS8_of_involutions hC hN hOS hκ ρ₄'_mul_self r₃'_mul_self
      sign_ρ₄' sign_r₃' (by rw [card_cycleType_ρ₄', card_cycleType_r₃']; decide)
  have hz : IsConj z (x * ι (liftS8 ρ₄')) := by
    have h := hconj.trans hισ
    rwa [hτρ] at h
  have hz3 : IsConj z (ι r₃) := by
    have h := hz.trans hxconj
    rwa [liftS8_r₃'] at h
  have hr₃2 : r₃ * r₃ = 1 := by rw [← liftS8_r₃', ← map_mul, r₃'_mul_self, map_one]
  have hcard₃ : Multiset.card r₃.cycleType = 3 := by
    rw [← liftS8_r₃', cycleType_liftS8, card_cycleType_r₃']
  exact not_isConj_z_ι_of_card_cycleType_eq_three hC hN hOS hκ hr₃2 hcard₃ hz3

theorem not_isConj_z_ι (hC : CentData z ι) (hN : NoSwapConj z ι) {x : G}
    {π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)} (hOS : OneSided z ι x π)
    {κ : ↥(centralizer ({x} : Set G)) →* ℤˣ} (hκ : Retraction z x κ) (σ : Perm (Fin 10)) :
    ¬ IsConj z (ι σ) := by
  intro hconj
  have hσ2 : σ * σ = 1 := by
    obtain ⟨g, hg⟩ := isConj_iff.1 hconj
    apply hC.inj
    rw [map_mul, map_one, ← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hC.mul_self]; group
  have hle : Multiset.card σ.cycleType ≤ 5 := card_cycleType_le_five hσ2
  have hne0 : Multiset.card σ.cycleType ≠ 0 := by
    intro h0
    have hσ1 : σ = 1 := Equiv.Perm.card_cycleType_eq_zero.1 h0
    have hz1 : z = 1 := by
      have h : IsConj z (1 : G) := by simpa [hσ1] using hconj
      exact isConj_one_left.1 h
    have horder : orderOf z = 1 := by rw [hz1]; exact orderOf_one
    rw [hC.order] at horder
    exact absurd horder (by decide)
  have hcases : Multiset.card σ.cycleType = 1 ∨ Multiset.card σ.cycleType = 2 ∨
      Multiset.card σ.cycleType = 3 ∨ Multiset.card σ.cycleType = 4 ∨
      Multiset.card σ.cycleType = 5 := by omega
  rcases hcases with h1 | h2 | h3 | h4 | h5
  · exact (hN σ (isSwap_of_card_cycleType_eq_one hσ2 h1)).1 hconj
  · have hσr₂ : IsConj σ r₂ := (isConj_rep_of_card_cycleType hσ2).2.1 h2
    have hι : IsConj (ι σ) (ι r₂) := MonoidHom.map_isConj ι hσr₂
    have hzr₂ : IsConj z (ι r₂) := hconj.trans hι
    obtain ⟨γ, hγ⟩ := exists_sq_r₂
    have hsq : ∃ y : G, y * y = ι r₂ := ⟨ι γ, by rw [← map_mul, hγ]⟩
    obtain ⟨y, hy⟩ := exists_sq_of_isConj (IsConj.symm hzr₂) hsq
    exact hC.not_sq y hy
  · exact not_isConj_z_ι_of_card_cycleType_eq_three hC hN hOS hκ hσ2 h3 hconj
  · have hσρ : IsConj σ ρ₄ := (isConj_rep_of_card_cycleType hσ2).2.2.2.1 h4
    have hι : IsConj (ι σ) (ι ρ₄) := MonoidHom.map_isConj ι hσρ
    have hzρ : IsConj z (ι ρ₄) := hconj.trans hι
    obtain ⟨γ, hγ⟩ := exists_sq_ρ₄
    have hsq : ∃ y : G, y * y = ι ρ₄ := ⟨ι γ, by rw [← map_mul, hγ]⟩
    obtain ⟨y, hy⟩ := exists_sq_of_isConj (IsConj.symm hzρ) hsq
    exact hC.not_sq y hy
  · exact not_isConj_z_ι_of_card_cycleType_eq_five hC hN hOS hκ hσ2 h5 hconj

end CFSG.OddStandard.AltStdSec.SwapPattern
