module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L10

open Subgroup

@[expose] def Recog1 : Prop :=
  ∀ {Λ : Type} [Group Λ] [Finite Λ], Nat.card Λ = 48 → ∀ (Q : Subgroup Λ) [Q.Normal],
    QuaternionGroup 2 ≃* ↥Q → ∀ x y : Λ, x ^ 3 = 1 → y ^ 2 = 1 → y * x * y⁻¹ = x⁻¹ →
      (∃ q ∈ Q, x * q * x⁻¹ ≠ q) → y ≠ 1 → Nonempty (Λ ≃* GL (Fin 2) (ZMod 3))

@[expose] def Recog2 : Prop := CFSG.pPrimeCore 2 (GL (Fin 2) (ZMod 3)) = ⊥

theorem pPrimeCore_eq_of_recognition (hR1 : Recog1) (hR2 : Recog2) {M : Type} [Group M] [Finite M]
    (hM : Nat.card M = 432) (Os : Subgroup M) [hOsN : Os.Normal] (hOs : Nat.card Os = 9)
    (Q : Subgroup M) [hQN : Q.Normal] (e : QuaternionGroup 2 ≃* ↥Q) (hQ4 : ∀ q ∈ Q, q ^ 4 = 1)
    (x y : M) (hx3 : x ^ 3 = 1) (hy2 : y ^ 2 = 1) (hyx : y * x * y⁻¹ = x⁻¹)
    (hxQ : ∃ q ∈ Q, (x * q * x⁻¹)⁻¹ * q ∉ Os) (hy1 : y ∉ Os) :
    CFSG.pPrimeCore 2 M = Os ∧ Nonempty (M ⧸ CFSG.pPrimeCore 2 M ≃* GL (Fin 2) (ZMod 3)) := by
  classical
  let mk : M →* M ⧸ Os := QuotientGroup.mk' Os
  have hmk : Function.Surjective mk := QuotientGroup.mk'_surjective _
  have hΛ : Nat.card (M ⧸ Os) = 48 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Os
    rw [hM, hOs] at h
    omega
  have hQOs : Q ⊓ Os = ⊥ := by
    rw [eq_bot_iff]
    rintro q ⟨hqQ, hqO⟩
    have h4 : orderOf q ∣ 4 := orderOf_dvd_of_pow_eq_one (hQ4 q hqQ)
    have h9 : orderOf q ∣ 9 := by
      rw [← hOs]
      exact Subgroup.orderOf_dvd_natCard Os hqO
    have h1 : orderOf q ∣ 1 := by
      have := Nat.dvd_gcd h4 h9
      simpa using this
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))
  have hinj : Function.Injective (mk.comp Q.subtype) := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have hqO : (q : M) ∈ Os := (QuotientGroup.eq_one_iff _).mp hq
    have : (q : M) ∈ Q ⊓ Os := ⟨q.2, hqO⟩
    rw [hQOs] at this
    exact Subtype.ext (Subgroup.mem_bot.mp this)
  have hrange : (mk.comp Q.subtype).range = Q.map mk := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eQ : QuaternionGroup 2 ≃* ↥(Q.map mk) :=
    e.trans ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))
  have : (Q.map mk).Normal := Subgroup.Normal.map hQN mk hmk
  have hxQ' : ∃ q ∈ Q.map mk, mk x * q * (mk x)⁻¹ ≠ q := by
    obtain ⟨q₀, hq₀, hq₀O⟩ := hxQ
    refine ⟨mk q₀, Subgroup.mem_map_of_mem mk hq₀, fun h => hq₀O ?_⟩
    have h2 : mk (x * q₀ * x⁻¹) = mk q₀ := by rw [map_mul, map_mul, map_inv]; exact h
    exact (QuotientGroup.eq.mp h2)
  have hy1' : mk y ≠ 1 := fun h => hy1 ((QuotientGroup.eq_one_iff y).mp h)
  obtain ⟨φ⟩ := hR1 hΛ (Q.map mk) eQ (mk x) (mk y) (by rw [← map_pow, hx3, map_one])
    (by rw [← map_pow, hy2, map_one]) (by simpa only [map_mul, map_inv] using congrArg mk hyx) hxQ' hy1'
  have hpc : CFSG.pPrimeCore 2 (M ⧸ Os) = ⊥ := by
    have h := CFSG.pPrimeCore_map_iso 2 φ
    rw [hR2] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h
  have hOsle : Os ≤ CFSG.pPrimeCore 2 M := by
    have hcop : Nat.Coprime 2 (Nat.card Os) := by rw [hOs]; norm_num
    exact le_sSup ⟨hOsN, hcop⟩
  have hle : CFSG.pPrimeCore 2 M ≤ Os := by
    intro n hn
    have hNn : (CFSG.pPrimeCore 2 M).Normal := CFSG.pPrimeCore_normal
    have hNc : Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 M)) := CFSG.pPrimeCore_coprime_card
    have hmapn : (CFSG.pPrimeCore 2 M).map mk ≤ CFSG.pPrimeCore 2 (M ⧸ Os) := by
      have hn' : (CFSG.pPrimeCore 2 M).map mk |>.Normal := hNn.map mk hmk
      have hc' : Nat.Coprime 2 (Nat.card ((CFSG.pPrimeCore 2 M).map mk)) :=
        Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) hNc
      exact le_sSup ⟨hn', hc'⟩
    rw [hpc] at hmapn
    have : mk n ∈ (CFSG.pPrimeCore 2 M).map mk := Subgroup.mem_map_of_mem mk hn
    have h1 : mk n = 1 := Subgroup.mem_bot.mp (hmapn this)
    exact (QuotientGroup.eq_one_iff n).mp h1
  have hEq : CFSG.pPrimeCore 2 M = Os := le_antisymm hle hOsle
  refine ⟨hEq, ⟨(QuotientGroup.quotientMulEquivOfEq hEq).trans φ⟩⟩

end CFSG.GH74.Uniqueness.SU.SU13.TA.L10
