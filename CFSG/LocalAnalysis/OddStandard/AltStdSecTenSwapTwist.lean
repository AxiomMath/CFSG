module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapRetract
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapCycle
public import CFSG.LocalAnalysis.OddStandard.AltStdSmallSylow

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G}

theorem ι_liftS8_mem_centralizer (ι : Perm (Fin 10) →* G) (ρ : Perm (Fin 8)) :
    ι (liftS8 ρ) ∈ centralizer ({ι τ₀} : Set G) := by
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, liftS8_mul_τ₀]

section Centralizer

variable {x : G}

@[expose] noncomputable def liftS8Centralizer (hx : x = ι τ₀) :
    Perm (Fin 8) →* ↥(centralizer ({x} : Set G)) :=
  (ι.comp liftS8).codRestrict _ fun ρ => by
    rw [hx]; exact ι_liftS8_mem_centralizer ι ρ

@[simp] theorem liftS8Centralizer_apply (hx : x = ι τ₀) (ρ : Perm (Fin 8)) :
    ((liftS8Centralizer (ι := ι) hx ρ : ↥(centralizer ({x} : Set G))) : G) =
      ι (liftS8 ρ) := rfl

variable {π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)}

@[expose] noncomputable def beta (hx : x = ι τ₀) : Perm (Fin 8) →* Perm (Fin 10) :=
  π.comp (liftS8Centralizer (ι := ι) hx)

theorem beta_apply (hx : x = ι τ₀) (ρ : Perm (Fin 8))
    (hρ : ι (liftS8 ρ) ∈ centralizer ({x} : Set G)) :
    beta (ι := ι) (π := π) hx ρ = π ⟨ι (liftS8 ρ), hρ⟩ := by
  rw [beta, MonoidHom.comp_apply]
  exact congrArg π (Subtype.ext rfl)

theorem z_mem_centralizer_of_oneSided (hC : CentData z ι) (hOS : OneSided z ι x π) :
    z ∈ centralizer ({x} : Set G) := by
  rw [hOS.eq, mem_centralizer_singleton_iff]
  exact hC.comm τ₀

theorem z_mul_liftS8_mem_centralizer (hC : CentData z ι) (hOS : OneSided z ι x π)
    (ρ : Perm (Fin 8)) : z * ι (liftS8 ρ) ∈ centralizer ({x} : Set G) := by
  rw [hOS.eq, mem_centralizer_singleton_iff]
  have h1 : ι (liftS8 ρ) * ι τ₀ = ι τ₀ * ι (liftS8 ρ) :=
    mem_centralizer_singleton_iff.1 (ι_liftS8_mem_centralizer ι ρ)
  calc (z * ι (liftS8 ρ)) * ι τ₀ = z * (ι (liftS8 ρ) * ι τ₀) := by group
    _ = z * (ι τ₀ * ι (liftS8 ρ)) := by rw [h1]
    _ = (z * ι τ₀) * ι (liftS8 ρ) := by group
    _ = (ι τ₀ * z) * ι (liftS8 ρ) := by rw [hC.comm τ₀]
    _ = ι τ₀ * (z * ι (liftS8 ρ)) := by group

theorem beta_eq_one_iff (hC : CentData z ι) (hOS : OneSided z ι x π) (ρ : Perm (Fin 8)) :
    beta (ι := ι) (π := π) hOS.eq ρ = 1 ↔ ρ = 1 := by
  constructor
  · intro h
    have hk := (hOS.sec.ker (liftS8Centralizer (ι := ι) hOS.eq ρ)).1 h
    rw [liftS8Centralizer_apply] at hk
    rcases hk with h1 | h1
    · have h2 : liftS8 ρ = 1 := hC.inj (h1.trans (map_one ι).symm)
      exact liftS8_injective (by simpa using h2)
    · have h2 : liftS8 ρ = τ₀ := hC.inj (h1.trans hOS.eq)
      have h3 := congrArg (fun f : Perm (Fin 10) => f 8) h2
      rw [liftS8_apply_eight] at h3
      simp [τ₀] at h3
  · intro h
    rw [h, map_one]

theorem beta_injective (hC : CentData z ι) (hOS : OneSided z ι x π) :
    Function.Injective (beta (ι := ι) (π := π) hOS.eq) := by
  intro ρ σ h
  have h1 : beta (ι := ι) (π := π) hOS.eq (ρ * σ⁻¹) = 1 := by
    rw [map_mul, h, map_inv, mul_inv_cancel]
  have h2 := (beta_eq_one_iff hC hOS (ρ * σ⁻¹)).1 h1
  rw [mul_inv_eq_one] at h2
  exact h2

theorem beta_comm_τ₀ (hC : CentData z ι) (hOS : OneSided z ι x π) (ρ : Perm (Fin 8)) :
    beta (ι := ι) (π := π) hOS.eq ρ * τ₀ =
      τ₀ * beta (ι := ι) (π := π) hOS.eq ρ := by
  have hzx := z_mem_centralizer_of_oneSided hC hOS
  have huw : (⟨z, hzx⟩ : ↥(centralizer ({x} : Set G))) *
        liftS8Centralizer (ι := ι) hOS.eq ρ =
      liftS8Centralizer (ι := ι) hOS.eq ρ * ⟨z, hzx⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, liftS8Centralizer_apply]
    exact hC.comm (liftS8 ρ)
  change π (liftS8Centralizer (ι := ι) hOS.eq ρ) * τ₀ =
    τ₀ * π (liftS8Centralizer (ι := ι) hOS.eq ρ)
  rw [← hOS.swap hzx, ← map_mul, ← map_mul, huw]

theorem beta_ne_τ₀ (hC : CentData z ι) (hOS : OneSided z ι x π) (ρ : Perm (Fin 8)) :
    beta (ι := ι) (π := π) hOS.eq ρ ≠ τ₀ := by
  intro h
  have hzx := z_mem_centralizer_of_oneSided hC hOS
  have h1 : π (liftS8Centralizer (ι := ι) hOS.eq ρ) =
      π (⟨z, hzx⟩ : ↥(centralizer ({x} : Set G))) := by
    rw [hOS.swap hzx]
    exact h
  have h2 : π (((⟨z, hzx⟩ : ↥(centralizer ({x} : Set G)))⁻¹) *
      liftS8Centralizer (ι := ι) hOS.eq ρ) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  have h3 := (hOS.sec.ker _).1 h2
  rw [Subgroup.coe_mul, Subgroup.coe_inv, liftS8Centralizer_apply] at h3
  rcases h3 with h3 | h3
  · have h4 : z = ι (liftS8 ρ) := inv_mul_eq_one.1 h3
    exact hC.ne_z (liftS8 ρ) h4.symm
  · have h4 : ι (liftS8 ρ) = z * x := inv_mul_eq_iff_eq_mul.1 h3
    rw [hOS.eq] at h4
    have h5 : ι (liftS8 ρ * τ₀⁻¹) = z := by
      rw [map_mul, map_inv, h4]
      group
    exact hC.ne_z (liftS8 ρ * τ₀⁻¹) h5

theorem exists_sq_of_isConj {a b : G} (h : IsConj a b) (ha : ∃ y : G, y * y = a) :
    ∃ y : G, y * y = b := by
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  obtain ⟨y, rfl⟩ := ha
  exact ⟨g * y * g⁻¹, by rw [← hg]; group⟩

theorem isConj_z_of_kappa_one_isSwap (hOS : OneSided z ι x π)
    {κ : ↥(centralizer ({x} : Set G)) →* ℤˣ} (hκ : Retraction z x κ)
    (hzx : z ∈ centralizer ({x} : Set G))
    {c : ↥(centralizer ({x} : Set G))} (hκc : κ c = 1) (hswap : (π c).IsSwap) :
    IsConj (c : G) z := by
  have hπ : IsConj (π c) (π ⟨z, hzx⟩) := by
    rw [hOS.swap hzx]
    rcases hswap with ⟨a, b, hab, heq⟩
    rw [heq]
    simpa [τ₀] using Equiv.Perm.isConj_swap hab (by decide)
  have hκc' : κ c = κ ⟨z, hzx⟩ := by rw [hκ.z_one hzx]; exact hκc
  have h := isConj_of_retraction hOS.sec hκ.self hπ hκc'
  simpa using h

theorem twist_indicator_r₁'_ne_one (hC : CentData z ι) (hN : NoSwapConj z ι)
    {x : G} {π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)} (hOS : OneSided z ι x π)
    {κ : ↥(centralizer ({x} : Set G)) →* ℤˣ} (hκ : Retraction z x κ)
    {β : Perm (Fin 8) →* Perm (Fin 10)} (hβ : β = beta (ι := ι) (π := π) hOS.eq)
    {ε : Perm (Fin 8) →* ℤˣ}
    (hε : ∀ ρ, ε ρ = if β ρ 8 = 9 then -1 else 1) :
    ε r₁' ≠ 1 := by
  intro hε1
  let u : ↥(centralizer ({x} : Set G)) := liftS8Centralizer (ι := ι) hOS.eq r₁'
  have hzx : z ∈ centralizer ({x} : Set G) := z_mem_centralizer_of_oneSided hC hOS
  have hinj : Function.Injective β := by rw [hβ]; exact beta_injective hC hOS
  have hcomm : ∀ ρ, β ρ * τ₀ = τ₀ * β ρ := by rw [hβ]; exact beta_comm_τ₀ hC hOS
  have hne : ∀ ρ, β ρ ≠ τ₀ := by rw [hβ]; exact beta_ne_τ₀ hC hOS
  have hr1'sq : r₁' * r₁' = 1 := by rw [r₁', swap_mul_self]
  have hr1swap : r₁.IsSwap := ⟨0, 1, by decide, rfl⟩
  have hk1 : Multiset.card r₁'.cycleType = 1 := by
    rw [← cycleType_liftS8 r₁', liftS8_r₁']
    exact card_cycleType_of_isSwap hr1swap
  have hβsq : β r₁' * β r₁' = 1 := by rw [← map_mul, hr1'sq, map_one]
  have hcard := card_cycleType_of_commute_swap β hinj hcomm hne hr1'sq
  have hπu : π u = β r₁' := by rw [hβ]; rfl
  have huval : (u : G) = ι r₁ := by
    show ((liftS8Centralizer (ι := ι) hOS.eq r₁' : ↥(centralizer ({x} : Set G))) : G) = ι r₁
    rw [liftS8Centralizer_apply, liftS8_r₁']
  have hπx : π (selfC x) = 1 := (hOS.sec.ker (selfC x)).2 (Or.inr rfl)
  have hβ8 : β r₁' 8 ≠ 9 := by
    intro h8
    have hneg : ε r₁' = -1 := by rw [hε r₁', if_pos h8]
    rw [hε1] at hneg
    exact absurd hneg (by decide)
  have hβswap : (β r₁').IsSwap := by
    refine isSwap_of_card_cycleType_eq_one hβsq ?_
    rw [hcard.1, hk1, if_neg hβ8, add_zero]
  have hswap_u : (π u).IsSwap := by rw [hπu]; exact hβswap
  rcases Int.units_eq_one_or (κ u) with hκu | hκu
  · have hconj := isConj_z_of_kappa_one_isSwap hOS hκ hzx hκu hswap_u
    have : IsConj z (ι r₁) := IsConj.symm (by simpa [huval] using hconj)
    exact (hN r₁ hr1swap).1 this
  · let d : ↥(centralizer ({x} : Set G)) := u * selfC x
    have hπd : π d = β r₁' := by
      show π (u * selfC x) = β r₁'
      rw [map_mul, hπx, mul_one, hπu]
    have hκd : κ d = 1 := by
      show κ (u * selfC x) = 1
      rw [map_mul, hκ.self, hκu]
      decide
    have hswap_d : (π d).IsSwap := by rw [hπd]; exact hβswap
    have hconj := isConj_z_of_kappa_one_isSwap hOS hκ hzx hκd hswap_d
    obtain ⟨γ, hγ⟩ := exists_sq_r₁_mul_τ₀
    have hdval : (d : G) = ι r₁ * x := by
      show ((u * selfC x : ↥(centralizer ({x} : Set G))) : G) = ι r₁ * x
      rw [Subgroup.coe_mul, huval]
      rfl
    have hdsq : ∃ y : G, y * y = (d : G) := by
      refine ⟨ι γ, ?_⟩
      rw [← map_mul, hγ, map_mul, hdval, hOS.eq]
    obtain ⟨y, hy⟩ := exists_sq_of_isConj hconj hdsq
    exact hC.not_sq y hy

theorem twist_indicator_r₁'_kappa_ne_one (hC : CentData z ι) (hN : NoSwapConj z ι)
    {x : G} {π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)} (hOS : OneSided z ι x π)
    {κ : ↥(centralizer ({x} : Set G)) →* ℤˣ} (hκ : Retraction z x κ)
    {β : Perm (Fin 8) →* Perm (Fin 10)} (hβ : β = beta (ι := ι) (π := π) hOS.eq)
    {ε : Perm (Fin 8) →* ℤˣ}
    (hε : ∀ ρ, ε ρ = if β ρ 8 = 9 then -1 else 1) (hεneg : ε r₁' = -1) :
    κ (liftS8Centralizer (ι := ι) hOS.eq r₁') ≠ 1 := by
  intro hκu1
  let u : ↥(centralizer ({x} : Set G)) := liftS8Centralizer (ι := ι) hOS.eq r₁'
  have hκu : κ u = 1 := hκu1
  have hzx : z ∈ centralizer ({x} : Set G) := z_mem_centralizer_of_oneSided hC hOS
  have hcomm : ∀ ρ, β ρ * τ₀ = τ₀ * β ρ := by rw [hβ]; exact beta_comm_τ₀ hC hOS
  have hr1'sq : r₁' * r₁' = 1 := by rw [r₁', swap_mul_self]
  have hr1swap : r₁.IsSwap := ⟨0, 1, by decide, rfl⟩
  have hk1 : Multiset.card r₁'.cycleType = 1 := by
    rw [← cycleType_liftS8 r₁', liftS8_r₁']
    exact card_cycleType_of_isSwap hr1swap
  have hβsq : β r₁' * β r₁' = 1 := by rw [← map_mul, hr1'sq, map_one]
  have hτ0sq : τ₀ * τ₀ = 1 := by rw [τ₀, swap_mul_self]
  have hβne : ∀ ρ, β ρ ≠ τ₀ := by rw [hβ]; exact beta_ne_τ₀ hC hOS
  have hcard := card_cycleType_of_commute_swap β (by rw [hβ]; exact beta_injective hC hOS)
    hcomm hβne hr1'sq
  have hπu : π u = β r₁' := by rw [hβ]; rfl
  have huval : (u : G) = ι r₁ := by
    show ((liftS8Centralizer (ι := ι) hOS.eq r₁' : ↥(centralizer ({x} : Set G))) : G) = ι r₁
    rw [liftS8Centralizer_apply, liftS8_r₁']
  have hβ9 : β r₁' 8 = 9 := by
    by_contra h8
    rw [hε r₁', if_neg h8] at hεneg
    exact absurd hεneg (by decide)
  have hβτinv : (τ₀ * β r₁') * (τ₀ * β r₁') = 1 := by
    have hc : Commute τ₀ (β r₁') := (hcomm r₁').symm
    rw [← pow_two, hc.mul_pow 2, pow_two, pow_two, hτ0sq, hβsq, one_mul]
  have hcard2' : Multiset.card (τ₀ * β r₁').cycleType = 1 := by
    rw [hcard.2, hk1, if_pos hβ9, add_zero]
  have hβτswap : (τ₀ * β r₁').IsSwap := isSwap_of_card_cycleType_eq_one hβτinv hcard2'
  let c₁ : ↥(centralizer ({x} : Set G)) := ⟨z, hzx⟩ * u
  have hπc₁ : π c₁ = τ₀ * β r₁' := by
    show π (⟨z, hzx⟩ * u) = τ₀ * β r₁'
    rw [map_mul, hOS.swap hzx, hπu]
  have hκc₁ : κ c₁ = 1 := by
    show κ (⟨z, hzx⟩ * u) = 1
    rw [map_mul, hκ.z_one hzx, hκu, one_mul]
  have hswap_c₁ : (π c₁).IsSwap := by rw [hπc₁]; exact hβτswap
  have hconj := isConj_z_of_kappa_one_isSwap hOS hκ hzx hκc₁ hswap_c₁
  have hc₁val : (c₁ : G) = z * ι r₁ := by
    show (((⟨z, hzx⟩ : ↥(centralizer ({x} : Set G))) * u :
      ↥(centralizer ({x} : Set G))) : G) = z * ι r₁
    rw [Subgroup.coe_mul, huval]
  have : IsConj z (z * ι r₁) := IsConj.symm (by simpa [hc₁val] using hconj)
  exact (hN r₁ hr1swap).2 this

theorem twist_indicator_r₁' (hC : CentData z ι) (hN : NoSwapConj z ι)
    {x : G} {π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)} (hOS : OneSided z ι x π)
    {κ : ↥(centralizer ({x} : Set G)) →* ℤˣ} (hκ : Retraction z x κ)
    {β : Perm (Fin 8) →* Perm (Fin 10)} (hβ : β = beta (ι := ι) (π := π) hOS.eq)
    {ε : Perm (Fin 8) →* ℤˣ}
    (hε : ∀ ρ, ε ρ = if β ρ 8 = 9 then -1 else 1) :
    ε r₁' = -1 ∧ κ (liftS8Centralizer (ι := ι) hOS.eq r₁') = -1 := by
  have hεne : ε r₁' ≠ 1 := twist_indicator_r₁'_ne_one hC hN hOS hκ hβ hε
  have hεneg : ε r₁' = -1 := (Int.units_eq_one_or (ε r₁')).resolve_left hεne
  have hκne : κ (liftS8Centralizer (ι := ι) hOS.eq r₁') ≠ 1 :=
    twist_indicator_r₁'_kappa_ne_one hC hN hOS hκ hβ hε hεneg
  exact ⟨hεneg,
    (Int.units_eq_one_or (κ (liftS8Centralizer (ι := ι) hOS.eq r₁'))).resolve_left hκne⟩

end Centralizer

theorem twist_facts (hC : CentData z ι) (hN : NoSwapConj z ι) {x : G}
    {π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)} (hOS : OneSided z ι x π)
    {κ : ↥(centralizer ({x} : Set G)) →* ℤˣ} (hκ : Retraction z x κ) (ρ : Perm (Fin 8))
    (hρx : ι (liftS8 ρ) ∈ centralizer ({x} : Set G))
    (hzρ : z * ι (liftS8 ρ) ∈ centralizer ({x} : Set G)) :
    κ ⟨ι (liftS8 ρ), hρx⟩ = sign ρ ∧
      (ρ * ρ = 1 →
        Multiset.card (π ⟨ι (liftS8 ρ), hρx⟩).cycleType =
            Multiset.card ρ.cycleType + (if Odd (Multiset.card ρ.cycleType) then 1 else 0) ∧
          Multiset.card (π ⟨z * ι (liftS8 ρ), hzρ⟩).cycleType =
            Multiset.card ρ.cycleType + (if Odd (Multiset.card ρ.cycleType) then 0 else 1)) := by
  let β : Perm (Fin 8) →* Perm (Fin 10) := beta (ι := ι) (π := π) hOS.eq
  have hβ : β = beta (ι := ι) (π := π) hOS.eq := rfl
  have hcomm : ∀ ρ, β ρ * τ₀ = τ₀ * β ρ := beta_comm_τ₀ hC hOS
  obtain ⟨ε, hε⟩ := exists_swapIndicator β hcomm
  obtain ⟨hεneg, hκneg⟩ := twist_indicator_r₁' hC hN hOS hκ hβ hε
  have hεsign : ε = sign := by
    rcases eq_one_or_eq_sign ε with h | h
    · exfalso
      have h1 : ε r₁' = 1 := by rw [h]; rfl
      rw [hεneg] at h1
      exact absurd h1 (by decide)
    · exact h
  have hχsign : κ.comp (liftS8Centralizer (ι := ι) hOS.eq) = sign := by
    rcases eq_one_or_eq_sign (κ.comp (liftS8Centralizer (ι := ι) hOS.eq)) with h | h
    · exfalso
      have h1 : (κ.comp (liftS8Centralizer (ι := ι) hOS.eq)) r₁' = 1 := by rw [h]; rfl
      have h2 : (κ.comp (liftS8Centralizer (ι := ι) hOS.eq)) r₁' = -1 := hκneg
      rw [h2] at h1
      exact absurd h1 (by decide)
    · exact h
  refine ⟨?_, ?_⟩
  · have hval : (κ.comp (liftS8Centralizer (ι := ι) hOS.eq)) ρ =
        κ ⟨ι (liftS8 ρ), hρx⟩ := by
      show κ (liftS8Centralizer (ι := ι) hOS.eq ρ) = κ ⟨ι (liftS8 ρ), hρx⟩
      exact congrArg κ (Subtype.ext rfl)
    rw [← hval, hχsign]
  · intro hρ2
    have hβinj : Function.Injective β := by rw [hβ]; exact beta_injective hC hOS
    have hβne : ∀ ρ, β ρ ≠ τ₀ := by rw [hβ]; exact beta_ne_τ₀ hC hOS
    have hcard := card_cycleType_of_commute_swap β hβinj hcomm hβne hρ2
    have hsignk : sign ρ = (-1 : ℤˣ) ^ Multiset.card ρ.cycleType :=
      CFSG.OddStandard.AltStdSmall.sign_eq_neg_one_pow_of_mul_self hρ2
    have hodd : Odd (Multiset.card ρ.cycleType) ↔ β ρ 8 = 9 := by
      constructor
      · intro ho
        have h1 : ε ρ = -1 := by
          rw [hεsign, hsignk]
          exact ho.neg_one_pow
        by_contra h8
        rw [hε ρ, if_neg h8] at h1
        exact absurd h1 (by decide)
      · intro h8
        have h1 : ε ρ = -1 := by rw [hε ρ, if_pos h8]
        have h2 : (-1 : ℤˣ) ^ Multiset.card ρ.cycleType = -1 := by
          rw [← hsignk, ← hεsign]
          exact h1
        exact (neg_one_pow_eq_neg_one_iff_odd (by decide : (-1 : ℤˣ) ≠ 1)).1 h2
    have hπρ : π ⟨ι (liftS8 ρ), hρx⟩ = β ρ := by
      rw [hβ]
      exact (beta_apply (ι := ι) (π := π) hOS.eq ρ hρx).symm
    have hπzρ : π ⟨z * ι (liftS8 ρ), hzρ⟩ = τ₀ * β ρ := by
      have hzx : z ∈ centralizer ({x} : Set G) := z_mem_centralizer_of_oneSided hC hOS
      have hdecomp : (⟨z * ι (liftS8 ρ), hzρ⟩ : ↥(centralizer ({x} : Set G))) =
          (⟨z, hzx⟩ : ↥(centralizer ({x} : Set G))) *
            liftS8Centralizer (ι := ι) hOS.eq ρ :=
        Subtype.ext rfl
      rw [hdecomp, map_mul, hOS.swap hzx, hβ]
      rfl
    have hif1 : (if β ρ 8 = 9 then (1 : ℕ) else 0) =
        (if Odd (Multiset.card ρ.cycleType) then 1 else 0) := by
      by_cases h8 : β ρ 8 = 9
      · rw [if_pos h8, if_pos (hodd.mpr h8)]
      · rw [if_neg h8, if_neg (fun ho => h8 (hodd.mp ho))]
    have hif2 : (if β ρ 8 = 9 then (0 : ℕ) else 1) =
        (if Odd (Multiset.card ρ.cycleType) then 0 else 1) := by
      by_cases h8 : β ρ 8 = 9
      · rw [if_pos h8, if_pos (hodd.mpr h8)]
      · rw [if_neg h8, if_neg (fun ho => h8 (hodd.mp ho))]
    exact ⟨by rw [hπρ, hcard.1, hif1], by rw [hπzρ, hcard.2, hif2]⟩

end CFSG.OddStandard.AltStdSec.SwapPattern
