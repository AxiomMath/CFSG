module

public import CFSG.GH74.GLS.IVK.L2.Transport
public import CFSG.LinearAlgebra.LinearGroups.SmallFieldModels
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

open Subgroup

namespace CFSG.GH74.GLS.LU.Local.Five

section CbarF

theorem psl2_card_arith {q n : ℕ} (hq : Odd q) (hq3 : 3 < q) (hn : n = q * (q ^ 2 - 1) / 2)
    (hdvd : n ∣ 28800) (h4 : 4 ∣ n) (h8 : ¬ 8 ∣ n) : q = 5 := by
  have hn0 : n ≤ 28800 := Nat.le_of_dvd (by norm_num) hdvd
  have hq38 : q ≤ 38 := by
    by_contra hcon
    have h39 : 39 ≤ q := by omega
    have h1 : 1520 ≤ q ^ 2 - 1 := by
      have : 39 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h39 2
      omega
    have h2 : 39 * 1520 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul h39 h1
    omega
  obtain ⟨k, hk⟩ := hq
  interval_cases q <;> simp_all

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem mem_of_orderOf_two {L : Subgroup H} [L.Normal] (h4 : 4 ∣ Nat.card L)
    (h8 : ¬ 8 ∣ Nat.card H) {x : H} (hx : orderOf x = 2) : x ∈ L := by
  have hmul := card_eq_card_quotient_mul_card_subgroup L
  have hodd : ¬ 2 ∣ Nat.card (H ⧸ L) := by
    intro h2
    have h28 : 2 * 4 ∣ Nat.card (H ⧸ L) * Nat.card L := mul_dvd_mul h2 h4
    rw [← hmul] at h28
    exact h8 h28
  have hcop : Nat.Coprime 2 (Nat.card (H ⧸ L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
  have h1 : orderOf (QuotientGroup.mk' L x) ∣ 2 := hx ▸ orderOf_map_dvd _ x
  have h2 : orderOf (QuotientGroup.mk' L x) ∣ Nat.card (H ⧸ L) := orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk' L x) = 1 :=
    Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff x).mp h3

theorem conjNormal_injective_of_pPrimeCore {L : Subgroup H} [L.Normal]
    (hO : CFSG.pPrimeCore 2 H = ⊥) (h4 : 4 ∣ Nat.card L) (h8 : ¬ 8 ∣ Nat.card H)
    (hcen : ∀ x : L, (∀ y : L, y * x = x * y) → x = 1) :
    Function.Injective (MulAut.conjNormal (H := L) : H →* MulAut L) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  set K := (MulAut.conjNormal (H := L) : H →* MulAut L).ker with hK
  refine CFSG.pPrimeCore_eq_bot_iff.mp hO K inferInstance ?_
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hy' : orderOf (y : H) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
  have hxL : (y : H) ∈ L := mem_of_orderOf_two h4 h8 hy'
  have hyK : MulAut.conjNormal (y : H) = (1 : MulAut L) := y.2
  have hcomm : ∀ z : L, z * ⟨y, hxL⟩ = ⟨y, hxL⟩ * z := by
    intro z
    apply Subtype.ext
    have h1 : (y : H) * (z : H) * (y : H)⁻¹ = z := by
      have := congrArg (fun φ : MulAut L => ((φ z : L) : H)) hyK
      simpa using this
    show (z : H) * y = y * z
    calc (z : H) * y = ((y : H) * z * (y : H)⁻¹) * y := by rw [h1]
      _ = y * z := by group
  have h1 : (y : H) = 1 := congrArg Subtype.val (hcen ⟨y, hxL⟩ hcomm)
  rw [h1, orderOf_one] at hy'
  exact absurd hy' (by norm_num)

end CbarF

theorem nat_card_mulAut_alternatingGroup_five :
    Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
  rw [← Nat.card_eq_of_bijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl (by norm_num))]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem nat_card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem alternatingGroup_five_central_eq_one (a : alternatingGroup (Fin 5))
    (h : ∀ b : alternatingGroup (Fin 5), b * a = a * b) : a = 1 := by
  have hc : a ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    exact h
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
  exact hc

theorem cbar_alternating_five {H₁ : Type} [Group H₁] [Finite H₁] (hO : pPrimeCore 2 H₁ = ⊥)
    (hH2 : (Nat.card H₁).factorization 2 = 2)
    (S : Subgroup H₁) (hS4 : Nat.card ↥S = 4)
    (L : Subgroup H₁) [L.Normal] (hSL : S ≤ L)
    {F : Type} [Field F] [Finite F] (hF : CFSG.GH74.GLS.IVK.L2Field F)
    (eL : ↥L ≃* CFSG.GH74.GLS.IVK.L2 F) (hdiv : Nat.card ↥L ∣ 28800) :
    Nonempty (H₁ ≃* alternatingGroup (Fin 5)) := by
  have hH0 : Nat.card H₁ ≠ 0 := Nat.card_pos.ne'
  have hH8 : ¬ 8 ∣ Nat.card H₁ := by
    intro h
    have h' := (Nat.prime_two.pow_dvd_iff_le_factorization hH0).mp (by simpa using h : 2 ^ 3 ∣ Nat.card H₁)
    omega
  have hL4 : 4 ∣ Nat.card L := hS4 ▸ Subgroup.card_dvd_of_le hSL
  have hLH : Nat.card L ∣ Nat.card H₁ := Subgroup.card_subgroup_dvd_card L
  have hL8 : ¬ 8 ∣ Nat.card L := fun h => hH8 (h.trans hLH)
  have hq : Nat.card F = 5 :=
    psl2_card_arith hF.1 hF.2 (CFSG.GH74.GLS.IVK.card_eq_of_L2Field eL hF) hdiv hL4 hL8
  obtain ⟨⟨e⟩, -⟩ := CFSG.LinearGroups.five_field_linear_two_alternating_five_model F hq
  let e₅ : ↥L ≃* alternatingGroup (Fin 5) := (CFSG.GH74.GLS.IVK.toPSL eL).trans e
  have hL60 : Nat.card L = 60 := by
    rw [Nat.card_congr e₅.toEquiv, nat_card_alternatingGroup_five]
  have hcen : ∀ x : L, (∀ y : L, y * x = x * y) → x = 1 := by
    intro x hx
    rw [← e₅.map_eq_one_iff]
    refine alternatingGroup_five_central_eq_one _ fun b => ?_
    have := congrArg e₅ (hx (e₅.symm b))
    simpa using this
  have hinj := conjNormal_injective_of_pPrimeCore (L := L) hO hL4 hH8 hcen
  have hdvd : Nat.card H₁ ∣ 120 := by
    rw [← nat_card_mulAut_alternatingGroup_five, ← Nat.card_congr (MulAut.congr e₅).toEquiv]
    exact Subgroup.card_dvd_of_injective _ hinj
  have hle : Nat.card H₁ ≤ 120 := Nat.le_of_dvd (by norm_num) hdvd
  have h60 : 60 ∣ Nat.card H₁ := hL60 ▸ hLH
  have hcard : Nat.card H₁ = 60 := by omega
  have hLtop : L = ⊤ := Subgroup.eq_top_of_card_eq L (by rw [hL60, hcard])
  exact ⟨((MulEquiv.subgroupCongr hLtop).trans Subgroup.topEquiv).symm.trans e₅⟩

end CFSG.GH74.GLS.LU.Local.Five
