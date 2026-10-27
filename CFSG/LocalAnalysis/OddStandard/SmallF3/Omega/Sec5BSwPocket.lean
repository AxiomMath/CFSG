module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

structure SwPocket {Λ : Type*} [Group Λ] (A : Subgroup Λ) (z : Λ) : Prop where
  mem : z ∈ A
  le_cent : A ≤ centralizer ({z} : Set Λ)
  gen : A ≤ closure {a : Λ | a ∈ A ∧ Odd (orderOf a)}
  noncomm : ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a
  two_center : ∀ w ∈ A, (∀ a ∈ A, a * w = w * a) → (∃ k : ℕ, orderOf w = 2 ^ k) →
    ∀ w' ∈ A, (∀ a ∈ A, a * w' = w' * a) → (∃ k : ℕ, orderOf w' = 2 ^ k) →
      w = 1 ∨ w' = 1 ∨ w = w'
  sylow : ∃ S : Subgroup Λ, S ≤ A ∧ IsPGroup 2 S ∧ Nat.card S = 8

private abbrev SL23 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

private theorem sl23_central_eq :
    ∀ g h : SL23, (∀ x : SL23, x * g = g * x) → (∀ x : SL23, x * h = h * x) →
      g = 1 ∨ h = 1 ∨ g = h := by
  decide +kernel

private theorem swp_odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem swPocket_of_isSL23Mod {Λ : Type} [Group Λ] [Finite Λ] {A : Subgroup Λ} {z : Λ}
    (hz : z ∈ A) (hc : A ≤ centralizer ({z} : Set Λ)) (hA : IsSL23Mod ↥A) : SwPocket A z := by
  refine ⟨hz, hc, l34g_le_closure_odd hA, ?_, ?_, ?_⟩
  ·
    obtain ⟨a, b, hab⟩ := hA.exists_noncomm
    exact ⟨(a : Λ), a.2, (b : Λ), b.2, fun h => hab (Subtype.ext h)⟩
  ·
    intro w hwA hwcent hw2 w' hw'A hw'cent hw'2
    obtain ⟨e⟩ := hA
    let π : ↥A →* SL23 := e.toMonoidHom.comp (QuotientGroup.mk' (oddCore ↥A))
    let W : ↥A := ⟨w, hwA⟩
    let W' : ↥A := ⟨w', hw'A⟩
    have hπsurj : Function.Surjective π := by
      intro g
      obtain ⟨q, hq⟩ := e.surjective g
      obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (oddCore ↥A) q
      exact ⟨b, by simp [π, MonoidHom.comp_apply, hb, hq]⟩
    have hker : ∀ a : ↥A, π a = 1 ↔ a ∈ oddCore ↥A := by
      intro a
      constructor
      · intro ha
        have h1 : a ∈ MonoidHom.ker (QuotientGroup.mk' (oddCore ↥A)) := by
          rw [MonoidHom.mem_ker]
          apply e.injective
          simpa [π, MonoidHom.comp_apply] using ha
        rwa [QuotientGroup.ker_mk'] at h1
      · intro ha
        have h1 : a ∈ MonoidHom.ker (QuotientGroup.mk' (oddCore ↥A)) := by
          rwa [QuotientGroup.ker_mk']
        rw [MonoidHom.mem_ker] at h1
        simp [π, MonoidHom.comp_apply, h1]
    have hoddCore : Odd (Nat.card (oddCore ↥A)) := swp_odd_card_oddCore ↥A
    have hWcent : ∀ a : ↥A, a * W = W * a := by
      intro a
      apply Subtype.ext
      simpa [W] using hwcent (a : Λ) a.2
    have hW'cent : ∀ a : ↥A, a * W' = W' * a := by
      intro a
      apply Subtype.ext
      simpa [W'] using hw'cent (a : Λ) a.2
    have hordW : orderOf W = orderOf w := Subgroup.orderOf_mk w hwA
    have hordW' : orderOf W' = orderOf w' := Subgroup.orderOf_mk w' hw'A
    have hone : π W = 1 → w = 1 := by
      intro hW1
      have hmem : W ∈ oddCore ↥A := (hker W).mp hW1
      obtain ⟨k, hk⟩ := hw2
      have hkW : orderOf W = 2 ^ k := by rw [hordW]; exact hk
      have hcop : Nat.Coprime (2 ^ k) (Nat.card (oddCore ↥A)) :=
        (Nat.coprime_two_left.mpr hoddCore).pow_left k
      have h1 : orderOf W = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop (by rw [hkW])
          (Subgroup.orderOf_dvd_natCard _ hmem)
      exact Subtype.ext_iff.mp (orderOf_eq_one_iff.mp h1)
    have hone' : π W' = 1 → w' = 1 := by
      intro hW'1
      have hmem : W' ∈ oddCore ↥A := (hker W').mp hW'1
      obtain ⟨k, hk⟩ := hw'2
      have hkW : orderOf W' = 2 ^ k := by rw [hordW']; exact hk
      have hcop : Nat.Coprime (2 ^ k) (Nat.card (oddCore ↥A)) :=
        (Nat.coprime_two_left.mpr hoddCore).pow_left k
      have h1 : orderOf W' = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop (by rw [hkW])
          (Subgroup.orderOf_dvd_natCard _ hmem)
      exact Subtype.ext_iff.mp (orderOf_eq_one_iff.mp h1)
    by_cases hW1 : π W = 1
    · exact Or.inl (hone hW1)
    · by_cases hW'1 : π W' = 1
      · exact Or.inr (Or.inl (hone' hW'1))
      · refine Or.inr (Or.inr ?_)
        have hcW : ∀ x : SL23, x * π W = π W * x := by
          intro x
          obtain ⟨a, rfl⟩ := hπsurj x
          rw [← map_mul, ← map_mul, hWcent a]
        have hcW' : ∀ x : SL23, x * π W' = π W' * x := by
          intro x
          obtain ⟨a, rfl⟩ := hπsurj x
          rw [← map_mul, ← map_mul, hW'cent a]
        have heq : π W = π W' := by
          rcases sl23_central_eq (π W) (π W') hcW hcW' with h | h | h
          · exact absurd h hW1
          · exact absurd h hW'1
          · exact h
        have hmem : W⁻¹ * W' ∈ oddCore ↥A := (hker (W⁻¹ * W')).mp (by
          rw [map_mul, map_inv, heq, inv_mul_cancel])
        have hodd : Odd (orderOf (W⁻¹ * W')) :=
          Odd.of_dvd_nat hoddCore (Subgroup.orderOf_dvd_natCard _ hmem)
        obtain ⟨k, hk⟩ := hw2
        obtain ⟨k', hk'⟩ := hw'2
        have hkW : orderOf W = 2 ^ k := by rw [hordW]; exact hk
        have hkW' : orderOf W' = 2 ^ k' := by rw [hordW']; exact hk'
        have hcomm : Commute W W' := (hWcent W').symm
        have hWbig : W ^ (2 ^ max k k') = 1 :=
          orderOf_dvd_iff_pow_eq_one.mp (by rw [hkW]; exact pow_dvd_pow 2 (le_max_left k k'))
        have hW'big : W' ^ (2 ^ max k k') = 1 :=
          orderOf_dvd_iff_pow_eq_one.mp (by rw [hkW']; exact pow_dvd_pow 2 (le_max_right k k'))
        have hprod : (W⁻¹ * W') ^ (2 ^ max k k') = 1 := by
          rw [(hcomm.inv_left).mul_pow, inv_pow, hWbig, inv_one, one_mul, hW'big]
        have hcop : Nat.Coprime (2 ^ max k k') (Nat.card (oddCore ↥A)) :=
          (Nat.coprime_two_left.mpr hoddCore).pow_left _
        have h1 : orderOf (W⁻¹ * W') = 1 :=
          Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_iff_pow_eq_one.mpr hprod)
            (Subgroup.orderOf_dvd_natCard _ hmem)
        have hWeq : W⁻¹ * W' = 1 := orderOf_eq_one_iff.mp h1
        have hWW' : W = W' := by
          have h := congrArg (fun x : ↥A => W * x) hWeq
          simp only [mul_one] at h
          rw [← mul_assoc, mul_inv_cancel, one_mul] at h
          exact h.symm
        exact Subtype.ext_iff.mp hWW'
  ·
    obtain ⟨e⟩ := hA
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hquot : Nat.card (↥A ⧸ oddCore ↥A) = 24 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      decide
    have hcardA : Nat.card ↥A = Nat.card (oddCore ↥A) * 24 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (oddCore ↥A), hquot, Nat.mul_comm]
    have hNodd : Odd (Nat.card (oddCore ↥A)) := swp_odd_card_oddCore ↥A
    have hNfact : Nat.factorization (Nat.card (oddCore ↥A)) 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun h => hNodd.not_two_dvd_nat h
    have h24fact : Nat.factorization 24 2 = 3 := by
      have h : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
      rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.factorization_pow_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3), add_zero]
    have hfact : Nat.factorization (Nat.card ↥A) 2 = 3 := by
      rw [hcardA, Nat.factorization_mul
          (Nat.card_pos (α := ↥(oddCore ↥A))).ne' (by norm_num),
        Finsupp.add_apply, hNfact, h24fact, zero_add]
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥A))
    refine ⟨(P : Subgroup ↥A).map A.subtype, Subgroup.map_subtype_le (P : Subgroup ↥A), ?_, ?_⟩
    · exact P.isPGroup'.map A.subtype
    · rw [Subgroup.card_map_of_injective A.subtype_injective, Sylow.card_eq_multiplicity P,
        hfact]
      norm_num

end CFSG.OddStandard.SmallF3.Omega

end
