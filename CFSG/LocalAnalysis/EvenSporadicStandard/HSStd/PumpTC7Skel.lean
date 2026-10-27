module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Syl

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open Subgroup
open scoped commutatorElement

@[expose] def ExcludedProp {M : Type*} [Group M] (P : Subgroup M) (r : M) : Prop :=
  ∃ Q : Subgroup M, Q ≤ P ⊓ centralizer ({r} : Set M) ∧ ¬ Nat.card Q ∣ 2880

@[expose] def ExcludedCard {M : Type*} [Group M] (R : Subgroup M) (r : M) : Prop :=
  ¬ 2880 ∣ Nat.card ↥(R ⊓ centralizer ({r} : Set M))

@[expose] def ExcludedDer {M : Type*} [Group M] (P : Subgroup M) (r : M) : Prop :=
  2880 ≤ Nat.card ↥(P ⊓ centralizer ({r} : Set M)) ∧
    360 < Nat.card ↥⁅P ⊓ centralizer ({r} : Set M), P ⊓ centralizer ({r} : Set M)⁆

@[expose] def SurvivorProp {M : Type*} [Group M] (R : Subgroup M) (r : M) : Prop :=
  ∀ z ∈ R, orderOf z = 3 → z ∈ centralizer ({r} : Set M) →
    ¬ 8 ∣ Nat.card ↥(R ⊓ centralizer ({z} : Set M))

theorem card_inf_centralizer_conj {M : Type*} [Group M] {R : Subgroup M} {c : M} (hc : c ∈ R)
    (x : M) : Nat.card ↥(R ⊓ centralizer ({c * x * c⁻¹} : Set M)) =
      Nat.card ↥(R ⊓ centralizer ({x} : Set M)) := by
  have h : (R ⊓ centralizer ({x} : Set M)).map (MulAut.conj c).toMonoidHom =
      R ⊓ centralizer ({c * x * c⁻¹} : Set M) := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective, centralizer_conj_eq]
    congr 1
    ext z
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact R.mul_mem (R.mul_mem hc hw) (R.inv_mem hc)
    · intro hz
      exact ⟨c⁻¹ * z * c, R.mul_mem (R.mul_mem (R.inv_mem hc) hz) hc, by group⟩
  rw [← h]
  exact Subgroup.card_map_of_injective (MulAut.conj c).injective

theorem harris_skeleton {M Γ : Type*} [Group M] [Finite M] [Group Γ] [Finite Γ]
    (P R : Subgroup M) (hPn : R ≤ normalizer (P : Set M)) (ρ : Γ →* M)
    (hρ : Function.Injective ρ) (hρR : ρ.range ≤ R) (hPρ : P ≤ ρ.range) (r : ℕ → M) (J : ℕ)
    (hcover : ∀ τ ∈ R, orderOf τ = 2 → ∃ j < J, ∃ c ∈ R, τ = c * r j * c⁻¹)
    (hcases : ∀ j < J, ExcludedProp P (r j) ∨ ExcludedCard R (r j) ∨ ExcludedDer P (r j) ∨
      SurvivorProp R (r j))
    {t : Γ} (ht : orderOf t = 2) (hC : Nat.card ↥(centralizer ({t} : Set Γ)) = 2880)
    (hD : Nat.card ↥⁅centralizer ({t} : Set Γ), centralizer ({t} : Set Γ)⁆ ≤ 360)
    {y : Γ} (hy3 : orderOf y = 3) :
    y ∈ centralizer ({t} : Set Γ) → ¬ 8 ∣ Nat.card ↥(centralizer ({y} : Set Γ)) := by
  intro hy
  have hτ : orderOf (ρ t) = 2 := by rw [orderOf_injective ρ hρ]; exact ht
  have hρtR : ρ t ∈ R := hρR ⟨t, rfl⟩
  obtain ⟨j, hj, c, hcR, hc⟩ := hcover (ρ t) hρtR hτ
  have key : ∀ Q : Subgroup M, Q ≤ P ⊓ centralizer ({r j} : Set M) →
      Q.map (MulAut.conj c).toMonoidHom ≤ (centralizer ({t} : Set Γ)).map ρ := by
    intro Q hQ
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨hqP, hqC⟩ := Subgroup.mem_inf.1 (hQ hq)
    have hP' : c * q * c⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (hPn hcR) q).1 hqP
    obtain ⟨γ, hγ⟩ := hPρ hP'
    refine ⟨γ, ?_, hγ⟩
    show γ ∈ centralizer ({t} : Set Γ)
    rw [mem_centralizer_singleton_iff]
    apply hρ
    have hqr : q * r j = r j * q := mem_centralizer_singleton_iff.1 hqC
    rw [map_mul, map_mul, hγ, hc]
    calc c * q * c⁻¹ * (c * r j * c⁻¹) = c * (q * r j) * c⁻¹ := by group
      _ = c * (r j * q) * c⁻¹ := by rw [hqr]
      _ = c * r j * c⁻¹ * (c * q * c⁻¹) := by group
  have hcardC : Nat.card ↥((centralizer ({t} : Set Γ)).map ρ) = 2880 := by
    rw [Subgroup.card_map_of_injective hρ, hC]
  rcases hcases j hj with ⟨Q, hQ, hQ2⟩ | hCard | ⟨hbig, hder⟩ | hS
  · exfalso
    apply hQ2
    have h1 := Subgroup.card_dvd_of_le (key Q hQ)
    rw [hcardC, Subgroup.card_map_of_injective (MulAut.conj c).injective] at h1
    exact h1
  · exfalso
    apply hCard
    have hle : (centralizer ({t} : Set Γ)).map ρ ≤ R ⊓ centralizer ({ρ t} : Set M) := by
      rintro _ ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.2 ⟨hρR ⟨g, rfl⟩, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hg' : g * t = t * g := mem_centralizer_singleton_iff.1 hg
      rw [← map_mul, ← map_mul, hg']
    have h1 := Subgroup.card_dvd_of_le hle
    rw [hcardC, hc, card_inf_centralizer_conj hcR] at h1
    exact h1
  · exfalso
    set Q := P ⊓ centralizer ({r j} : Set M) with hQdef
    have hQ'le := key Q le_rfl
    have hQ'card : Nat.card ↥(Q.map (MulAut.conj c).toMonoidHom) = Nat.card Q :=
      Subgroup.card_map_of_injective (MulAut.conj c).injective
    have heq : Q.map (MulAut.conj c).toMonoidHom = (centralizer ({t} : Set Γ)).map ρ :=
      Subgroup.eq_of_le_of_card_ge hQ'le (by rw [hQ'card, hcardC]; exact hbig)
    have h1 : Nat.card ↥⁅Q.map (MulAut.conj c).toMonoidHom, Q.map (MulAut.conj c).toMonoidHom⁆ =
        Nat.card ↥⁅Q, Q⁆ := by
      rw [← Subgroup.map_commutator]
      exact Subgroup.card_map_of_injective (MulAut.conj c).injective
    have h2 : Nat.card ↥⁅(centralizer ({t} : Set Γ)).map ρ, (centralizer ({t} : Set Γ)).map ρ⁆ =
        Nat.card ↥⁅centralizer ({t} : Set Γ), centralizer ({t} : Set Γ)⁆ := by
      rw [← Subgroup.map_commutator]
      exact Subgroup.card_map_of_injective hρ
    rw [heq] at h1
    omega
  · have hρyR : ρ y ∈ R := hρR ⟨y, rfl⟩
    have hz3 : orderOf (c⁻¹ * ρ y * c) = 3 := by
      have h := (MulAut.conj c⁻¹).orderOf_eq (ρ y)
      rw [MulAut.conj_apply, inv_inv] at h
      rw [h, orderOf_injective ρ hρ]
      exact hy3
    have hzR : c⁻¹ * ρ y * c ∈ R := R.mul_mem (R.mul_mem (R.inv_mem hcR) hρyR) hcR
    have hzc : c⁻¹ * ρ y * c ∈ centralizer ({r j} : Set M) := by
      rw [mem_centralizer_singleton_iff]
      have hyt : ρ y * ρ t = ρ t * ρ y := by
        rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hy]
      rw [hc] at hyt
      calc c⁻¹ * ρ y * c * r j = c⁻¹ * (ρ y * (c * r j * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * r j * c⁻¹) * ρ y) * c := by rw [hyt]
        _ = r j * (c⁻¹ * ρ y * c) := by group
    have h8 := hS _ hzR hz3 hzc
    have hcinv : c⁻¹ ∈ R := R.inv_mem hcR
    rw [show c⁻¹ * ρ y * c = c⁻¹ * ρ y * c⁻¹⁻¹ by rw [inv_inv],
      card_inf_centralizer_conj hcinv] at h8
    intro h
    refine h8 (h.trans ?_)
    have hle : (centralizer ({y} : Set Γ)).map ρ ≤ R ⊓ centralizer ({ρ y} : Set M) := by
      rintro _ ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.2 ⟨hρR ⟨g, rfl⟩, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hg' : g * y = y * g := mem_centralizer_singleton_iff.1 hg
      rw [← map_mul, ← map_mul, hg']
    rw [← Subgroup.card_map_of_injective hρ]
    exact Subgroup.card_dvd_of_le hle

end CFSG.EvenSporadicStandard.HSStd.PumpTC7
