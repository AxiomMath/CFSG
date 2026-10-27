module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnStmt
public import CFSG.GH74.GLS.Stage2.Local.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpLift

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

namespace L29E

section PCoreLemmas

theorem map_pCore_le_of_surjective {X Y : Type*} [Group X] [Group Y] (p : ℕ) (ψ : X →* Y)
    (hψ : Function.Surjective ψ) : (pCore p X).map ψ ≤ pCore p Y := by
  have hn : ((pCore p X).map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
  exact le_sSup ⟨hn, pCore_isPGroup.map ψ⟩

theorem le_pCore_of_normal {X : Type*} [Group X] (p : ℕ) (S : Subgroup X) [S.Normal]
    (hS : IsPGroup p ↥S) : S ≤ pCore p X :=
  le_sSup ⟨inferInstance, hS⟩

theorem pCore_two_eq_bot_of_card_three {P : Type*} [Group P] (h : Nat.card P = 3) :
    pCore 2 P = ⊥ := by
  have : Finite P := Nat.finite_of_card_ne_zero (by omega)
  have hP : IsPGroup 2 ↥(pCore 2 P) := pCore_isPGroup
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  have hd : 2 ^ k ∣ 3 := h ▸ hk ▸ Subgroup.card_subgroup_dvd_card (pCore 2 P)
  have h1 : 2 ^ k = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k (by norm_num)) hd
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, h1])

theorem pCore_two_perm3 : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
  have hP : IsPGroup 2 ↥(pCore 2 (Equiv.Perm (Fin 3))) := pCore_isPGroup
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card]; decide
  rw [eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_bot]
  by_contra hk1
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨k, hk⟩
  rw [Subgroup.orderOf_mk] at hj
  have hd : orderOf k ∣ 6 := hcard ▸ orderOf_dvd_natCard k
  have hd2 : orderOf k ∣ 2 := by
    have : orderOf k ∣ 2 * 3 := hd
    have hc : Nat.Coprime (orderOf k) 3 := by
      rw [hj]; exact Nat.Coprime.pow_left j (by norm_num)
    exact hc.dvd_of_dvd_mul_right this
  have h2 : orderOf k = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hk1
    · exact h
  have hkk : k * k = 1 := by rw [← sq, ← h2, pow_orderOf_eq_one]
  have htop := Stage1.Thm6.Prod.perm3_normal_top (pCore 2 (Equiv.Perm (Fin 3)))
    ⟨k, hk, hk1, hkk⟩
  have c3 : ∃ c : Equiv.Perm (Fin 3), c ^ 3 = 1 ∧ c ≠ 1 := by decide
  obtain ⟨c, hc3, hc1⟩ := c3
  have hcm : c ∈ pCore 2 (Equiv.Perm (Fin 3)) := by rw [htop]; trivial
  obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨c, hcm⟩
  rw [Subgroup.orderOf_mk] at hi
  have hc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  rw [hc] at hi
  have h3 : (3 : ℕ) ∣ 2 ^ i := ⟨1, by omega⟩
  have : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

end PCoreLemmas

section PPrimePCore

variable {C : Type*} [Group C]

theorem pPrimeCore_le_pPrimePCore (p : ℕ) : pPrimeCore p C ≤ pPrimePCore p C := by
  intro x hx
  rw [pPrimePCore, Subgroup.mem_comap]
  have h1 : (QuotientGroup.mk' (pPrimeCore p C)) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
  rw [h1]
  exact one_mem _

theorem le_pPrimePCore_of_normal (p : ℕ) (S : Subgroup C) [S.Normal] (hS : IsPGroup p ↥S) :
    S ≤ pPrimePCore p C := by
  intro x hx
  rw [pPrimePCore, Subgroup.mem_comap]
  have hn : (S.map (QuotientGroup.mk' (pPrimeCore p C))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  exact le_pCore_of_normal p _ (hS.map _) ⟨x, hx, rfl⟩

theorem pPrimePCore_le_ker (p : ℕ) {P : Type*} [Group P] (φ : C →* P)
    (hφ : Function.Surjective φ) (hker : pPrimeCore p C ≤ φ.ker) (hP : pCore p P = ⊥) :
    pPrimePCore p C ≤ φ.ker := by
  let ψ : C ⧸ pPrimeCore p C →* P := QuotientGroup.lift (pPrimeCore p C) φ hker
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨c, rfl⟩ := hφ y
    exact ⟨(c : C ⧸ pPrimeCore p C), rfl⟩
  intro x hx
  have hx' : (QuotientGroup.mk' (pPrimeCore p C)) x ∈ pCore p (C ⧸ pPrimeCore p C) := hx
  have h1 := map_pCore_le_of_surjective p ψ hψ ⟨_, hx', rfl⟩
  rw [hP, Subgroup.mem_bot] at h1
  exact h1

end PPrimePCore

open CFSG.GH74.GLS.IVK.Proofs2.Ivk5An in
theorem O2core_O2res_subgroupOf {E : Type} [Group E] (Y : Subgroup E) :
    (O2core (O2res Y)).subgroupOf Y =
      (pCore 2 ↥(oResidual 2 ↥Y)).map (oResidual 2 ↥Y).subtype := by
  let R : Subgroup ↥Y := oResidual 2 ↥Y
  let e : ↥R ≃* ↥(R.map Y.subtype) := Subgroup.equivMapOfInjective R Y.subtype Y.subtype_injective
  have h1 := pCore_map_iso 2 e
  have hcomp : (R.map Y.subtype).subtype.comp e.toMonoidHom = Y.subtype.comp R.subtype := by
    ext x; rfl
  have h2 : O2core (O2res Y) = ((pCore 2 ↥R).map R.subtype).map Y.subtype := by
    unfold O2core O2res
    rw [← h1, Subgroup.map_map, hcomp, ← Subgroup.map_map]
  rw [h2, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]

end L29E

open CFSG.GH74.GLS.IVK.Proofs2.Ivk5An in
theorem O2core_O2res_normal {E : Type} [Group E] [Finite E] (Y : Subgroup E) :
    ((O2core (O2res Y)).subgroupOf Y).Normal := by
  have hR : (oResidual 2 ↥Y).Normal := Stage1.Thm6.Prod.oResidual_normal 2 ↥Y
  rw [L29E.O2core_O2res_subgroupOf]
  infer_instance

open CFSG.GH74.GLS.IVK.Proofs2.Ivk5An in
theorem O22Of_eq_of_concl53 {E : Type} [Group E] [Finite E] (CK : Subgroup E) (n : ℕ)
    (he : Nat.card ↥(pPrimeCoreOf 2 CK) = if n = 11 then 3 else 1)
    (hf : (n ≤ 9 → IVK.Proofs2.Ivk5An.QuotIso CK (O2core (O2res CK)) (alternatingGroup (Fin 3))) ∧
      (10 ≤ n → IVK.Proofs2.Ivk5An.QuotIso CK (pPrimeCoreOf 2 CK ⊔ O2core (O2res CK))
        (Equiv.Perm (Fin 3)))) :
    O22Of CK = pPrimeCoreOf 2 CK ⊔ O2core (O2res CK) := by
  have key : ∃ (P : Type) (_ : Group P) (φ : ↥CK →* P), Function.Surjective φ ∧
      φ.ker = (pPrimeCoreOf 2 CK ⊔ O2core (O2res CK)).subgroupOf CK ∧ pCore 2 P = ⊥ := by
    rcases Nat.lt_or_ge n 10 with hn | hn
    · obtain ⟨φ, hφs, hφk⟩ := hf.1 (by omega)
      have hbot : pPrimeCoreOf 2 CK = ⊥ := by
        apply Subgroup.eq_bot_of_card_eq
        have hne : n ≠ 11 := by omega
        rw [he]
        simp [hne]
      refine ⟨↥(alternatingGroup (Fin 3)), inferInstance, φ, hφs, ?_, ?_⟩
      · rw [hφk, hbot, bot_sup_eq]
      · apply L29E.pCore_two_eq_bot_of_card_three
        rw [Nat.card_eq_fintype_card]; decide
    · obtain ⟨φ, hφs, hφk⟩ := hf.2 hn
      exact ⟨Equiv.Perm (Fin 3), inferInstance, φ, hφs, hφk, L29E.pCore_two_perm3⟩
  obtain ⟨P, _, φ, hφs, hφk, hP⟩ := key
  have hOker : pPrimeCore 2 ↥CK ≤ φ.ker := by
    rw [hφk]
    intro x hx
    show (x : E) ∈ pPrimeCoreOf 2 CK ⊔ O2core (O2res CK)
    exact Subgroup.mem_sup_left ⟨x, hx, rfl⟩
  have hB : pPrimePCore 2 ↥CK ≤ φ.ker := L29E.pPrimePCore_le_ker 2 φ hφs hOker hP
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have h1 := hB hx
    rw [hφk] at h1
    exact h1
  · refine sup_le ?_ ?_
    · exact Subgroup.map_mono (L29E.pPrimeCore_le_pPrimePCore 2)
    · have hQle : O2core (O2res CK) ≤ CK :=
        (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
      have hQn : ((O2core (O2res CK)).subgroupOf CK).Normal := O2core_O2res_normal CK
      have hQ2 : IsPGroup 2 ↥((O2core (O2res CK)).subgroupOf CK) := by
        rw [L29E.O2core_O2res_subgroupOf]
        exact pCore_isPGroup.map _
      have h1 := L29E.le_pPrimePCore_of_normal 2 ((O2core (O2res CK)).subgroupOf CK) hQ2
      calc O2core (O2res CK) = ((O2core (O2res CK)).subgroupOf CK).map CK.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hQle).symm
        _ ≤ O22Of CK := Subgroup.map_mono h1

theorem isSylowOf_sup_of_commute_odd {E : Type} [Group E] [Finite E] (A B : Subgroup E)
    (hA : IsPGroup 2 ↥A) (hB : Odd (Nat.card ↥B)) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    CFSG.ABGLocalTools.IsSylowOf 2 A (A ⊔ B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    (hc a a.2 b b.2 : (a : E) * b = b * a)
  let f : ↥A × ↥B →* E := MonoidHom.noncommCoprod A.subtype B.subtype hcomm
  have hrange : f.range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hinf : A ⊓ B = ⊥ := isPGroup_two_inf_eq_bot_of_odd A B hA hB
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    rw [MonoidHom.mem_ker] at hab
    have hab' : (a : E) * b = 1 := hab
    have hmem : (a : E) ∈ A ⊓ B := by
      refine Subgroup.mem_inf.mpr ⟨a.2, ?_⟩
      have : (a : E) = (b : E)⁻¹ := eq_inv_of_mul_eq_one_left hab'
      rw [this]
      exact B.inv_mem b.2
    rw [hinf, Subgroup.mem_bot] at hmem
    have ha1 : a = 1 := Subtype.ext hmem
    have hb1 : (b : E) = 1 := by simpa [hmem] using hab'
    rw [Subgroup.mem_bot]
    exact Prod.ext ha1 (Subtype.ext hb1)
  have hcard : Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
    rw [← hrange, ← Nat.card_prod]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hA
  refine CFSG.ABGLocalTools.isSylowOf_of_card le_sup_left ?_
  rw [hcard, hk]
  have hb0 : Nat.card ↥B ≠ 0 := Nat.card_pos.ne'
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hb0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hB.not_two_dvd_nat]
  simp

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
