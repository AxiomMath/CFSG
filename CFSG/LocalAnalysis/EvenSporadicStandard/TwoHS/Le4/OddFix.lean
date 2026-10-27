module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.OddFixModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.OddFixTransport
public import CFSG.Sporadic.SmallOddCore.HSAut

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Blueprint
  CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.HSStd (hsT1_mem_ord hsT2_mem_ord hsOddA_mem hsOddA_pow hsOddB_mem
  hsOddB_pow hs_u2b)

theorem commute_of_fixes {e : hsR ≃* MulAut hsP}
    (he : ∀ (x : hsR) (p : hsP), ((e x p : hsP) : Equiv.Perm (Fin 3850)) =
      (x : Equiv.Perm (Fin 3850)) * p * (x : Equiv.Perm (Fin 3850))⁻¹)
    {τ : ↥hsP} {x : hsR}
    (hφ : ∀ c ∈ centralizer ({τ} : Set ↥hsP), Odd (orderOf c) → e x c = c)
    {a : Equiv.Perm (Fin 3850)}
    (ha : a ∈ hsP ⊓ centralizer ({(τ : Equiv.Perm (Fin 3850))} : Set (Equiv.Perm (Fin 3850))))
    {n : ℕ} (han : a ^ n = 1) (hn : Odd n) : (x : Equiv.Perm (Fin 3850)) * a = a * x := by
  have haτ : (⟨a, (mem_inf.1 ha).1⟩ : ↥hsP) ∈ centralizer ({τ} : Set ↥hsP) := by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (by simpa using mem_centralizer_singleton_iff.1 (mem_inf.1 ha).2)
  have hord : Odd (orderOf (⟨a, (mem_inf.1 ha).1⟩ : ↥hsP)) := by
    rw [← Subgroup.orderOf_coe]
    exact hn.of_dvd_nat (orderOf_dvd_of_pow_eq_one han)
  have h2 := congrArg Subtype.val (hφ _ haτ hord)
  rw [he] at h2
  exact mul_inv_eq_iff_eq_mul.1 h2

theorem oddFixAt_t1
    (τ : ↥hsP)
    (hτ : (τ : Equiv.Perm (Fin 3850)) = hsT1) : OddFixAt ↥hsP τ := by
  obtain ⟨e, he, -⟩ := hs_full_automorphism_model
  intro φ hφ
  obtain ⟨x, rfl⟩ := e.surjective φ
  have key : ∀ (a : Equiv.Perm (Fin 3850)) (n : ℕ), a ∈ hsC1 → a ^ n = 1 → Odd n →
      (x : Equiv.Perm (Fin 3850)) * a = a * x := fun a n ha han hn =>
    commute_of_fixes he hφ (by rwa [hτ]) han hn
  have hx4 := hs_odd1 (x : Equiv.Perm (Fin 3850)) x.2
    (key _ 5 hsOdd1A_mem hsOdd1A_pow (by decide)) (key _ 5 hsOdd1B_mem hsOdd1B_pow (by decide))
  rw [← map_pow, show x ^ 4 = 1 from Subtype.ext (by simpa using hx4), map_one]

theorem oddFixAt_t2
    (τ : ↥hsP) (hτ : (τ : Equiv.Perm (Fin 3850)) = hsT2) :
    OddFixAt ↥hsP τ := by
  obtain ⟨e, he, -⟩ := hs_full_automorphism_model
  intro φ hφ
  obtain ⟨x, rfl⟩ := e.surjective φ
  have key : ∀ (a : Equiv.Perm (Fin 3850)) (n : ℕ), a ∈ hsC2 → a ^ n = 1 → Odd n →
      (x : Equiv.Perm (Fin 3850)) * a = a * x := fun a n ha han hn =>
    commute_of_fixes he hφ (by rwa [hτ]) han hn
  have hx2 := hs_u2b (x : Equiv.Perm (Fin 3850)) x.2
    (key _ 5 hsOddA_mem hsOddA_pow (by decide)) (key _ 3 hsOddB_mem hsOddB_pow (by decide))
  have hx4 : (x : Equiv.Perm (Fin 3850)) ^ 4 = 1 := by
    rw [show (x : Equiv.Perm (Fin 3850)) ^ 4 = (x * x) * (x * x) by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc], hx2, mul_one]
  rw [← map_pow, show x ^ 4 = 1 from Subtype.ext (by simpa using hx4), map_one]

theorem oddFixFourth_hsP :
    OddFixFourth ↥hsP := by
  intro τ hτ
  have hτ' : orderOf (τ : Equiv.Perm (Fin 3850)) = 2 := by rwa [Subgroup.orderOf_coe]
  obtain ⟨-, -, -, -, hcover⟩ := CFSG.Sporadic.SmallOddCore.hs_reps
  obtain ⟨r, hr, g, hg, hrg⟩ := hcover τ τ.2 hτ'
  have hτg : ∀ τ₀ : ↥hsP, (τ₀ : Equiv.Perm (Fin 3850)) = r →
      τ = (⟨g, hg⟩ : ↥hsP) * τ₀ * (⟨g, hg⟩ : ↥hsP)⁻¹ := fun τ₀ h0 =>
    Subtype.ext (by simp [h0, hrg])
  rcases hr with rfl | rfl
  · rw [hτg ⟨hsT1, hsT1_mem_ord.1⟩ rfl]
    exact (oddFixAt_t1 ⟨hsT1, hsT1_mem_ord.1⟩ rfl).conj _
  · rw [hτg ⟨hsT2, hsT2_mem_ord.1⟩ rfl]
    exact (oddFixAt_t2 ⟨hsT2, hsT2_mem_ord.1⟩ rfl).conj _

theorem oddFixFourth_of_isSporadic_hs
    {Y : Type} [Group Y] (h : IsSporadic Y .HS) :
    OddFixFourth Y := by
  obtain ⟨e₀⟩ := h
  have e : Y ≃* NativeSporadic.HS := e₀
  exact OddFixFourth.of_mulEquiv (e.trans hsPermEquiv) oddFixFourth_hsP

end CFSG.EvenSporadicStandard.TwoHS
