module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovArith
public import CFSG.GH74.GLS.Stage2.Local.P34Kind
public import CFSG.LieType.SteinbergBRSemidirectSL2
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape
public import CFSG.GH74.GLS.Stage2.Local.P34Embed

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.GH74.GLS.Stage2.Local.P34
open scoped MatrixGroups

namespace Ivk93Cov

variable {J : Type} [Group J] [Finite J] {x : J} {n : ℕ} {B : Subgroup J}

theorem surj_quasisimple_card (h : Ivk93Cov x n B) {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) (ψ : Q →* ↥B) (hψ : Function.Surjective ψ) :
    ∃ N : Subgroup Q, N ≤ center Q ∧ Nat.card Q = Nat.card ↥N * n.factorial ∧
      Nat.card ↥(center Q) = 2 * Nat.card ↥N := by
  classical
  let ψ' : Q →* (↥B ⧸ pPrimeCore 2 ↥B) := (QuotientGroup.mk' (pPrimeCore 2 ↥B)).comp ψ
  have hψ' : Function.Surjective ψ' := (QuotientGroup.mk'_surjective _).comp hψ
  have hbig := h.card_ge_big
  have hK := h.card_quot
  obtain ⟨-, hZ, -⟩ := h.cover
  have hN : ψ'.ker.Normal := MonoidHom.normal_ker ψ'
  have hker : ψ'.ker ≤ center Q := by
    rcases LocalCores.quasisimple_normal_subgroups hQ hN with h0 | h0
    · exfalso
      have h1 : Nat.card (Q ⧸ ψ'.ker) = Nat.card (↥B ⧸ pPrimeCore 2 ↥B) :=
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ' hψ').toEquiv
      rw [h0, hK] at h1
      have h2 : Nat.card (Q ⧸ (⊤ : Subgroup Q)) = 1 := Subgroup.index_top
      rw [h2] at h1
      have := Nat.factorial_le h.eight
      have h8 : Nat.factorial 8 = 40320 := by decide
      omega
    · exact h0
  refine ⟨ψ'.ker, hker, ?_, ?_⟩
  · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ'.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ' hψ').toEquiv, hK] at h1
    rw [h1]
    ring
  ·
    let g : ↥(center Q) →* ↥(center (↥B ⧸ pPrimeCore 2 ↥B)) :=
      (ψ'.comp (center Q).subtype).codRestrict (center (↥B ⧸ pPrimeCore 2 ↥B)) (by
        intro z
        rw [Subgroup.mem_center_iff]
        intro k
        obtain ⟨q, rfl⟩ := hψ' k
        show ψ' q * ψ' z = ψ' z * ψ' q
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 z.2 q)])
    have hg : Function.Surjective g := by
      intro k
      obtain ⟨q, hq⟩ := hψ' (k : ↥B ⧸ pPrimeCore 2 ↥B)
      have hqc : q ∈ center Q := by
        apply mem_center_of_commutators_central hQ
        intro y
        apply hker
        simp only [MonoidHom.mem_ker, map_mul, map_inv]
        rw [hq]
        have := Subgroup.mem_center_iff.1 k.2 (ψ' y)
        calc (k : ↥B ⧸ pPrimeCore 2 ↥B) * ψ' y * (k : ↥B ⧸ pPrimeCore 2 ↥B)⁻¹ * (ψ' y)⁻¹
            = (k * ψ' y) * (ψ' y * k)⁻¹ := by group
          _ = 1 := by rw [this, mul_inv_cancel]
      exact ⟨⟨q, hqc⟩, Subtype.ext hq⟩
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv, hZ] at h1
    have hkerg : Nat.card ↥g.ker = Nat.card ↥ψ'.ker := by
      have hk : g.ker = ψ'.ker.subgroupOf (center Q) := by
        ext z
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
        constructor
        · intro hz
          have := congrArg Subtype.val hz
          exact this
        · intro hz
          exact Subtype.ext hz
      rw [hk]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv
    rw [hkerg] at h1
    exact h1

theorem false_of_surj_odd_center (h : Ivk93Cov x n B) {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) (ψ : Q →* ↥B) (hψ : Function.Surjective ψ)
    (hZ : Odd (Nat.card ↥(center Q))) : False := by
  obtain ⟨N, -, -, hc⟩ := h.surj_quasisimple_card hQ ψ hψ
  rw [hc] at hZ
  exact (Nat.not_odd_iff_even.2 (even_two_mul _)) hZ

theorem false_of_surj_sl2 (h : Ivk93Cov x n B) {E : Type} [Field E] [Finite E]
    (hodd : Odd (Nat.card E)) (h5 : 5 ≤ Nat.card E) (ψ : SL(2, E) →* ↥B)
    (hψ : Function.Surjective ψ) : False := by
  have h2 : (2 : E) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  have hchar : ringChar E ≠ 2 := CFSG.ABGLocalTools.ringChar_ne_two_of_odd_card hodd
  have hQ : CFSG.IsQuasisimple SL(2, E) := GHInv.isQuasisimple_sl2 (by omega)
  obtain ⟨N, -, h1, h2'⟩ := h.surj_quasisimple_card hQ ψ hψ
  have hZ : Nat.card ↥(center SL(2, E)) = 2 := CFSG.LieType.SteinbergBR.card_center_SL2_eq_two hchar
  rw [hZ] at h2'
  have hN : Nat.card ↥N = 1 := by omega
  rw [hN, one_mul, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two E] at h1
  exact ivk93cov_sl2_ne_factorial h.eight h.le_eleven h1

end Ivk93Cov

end CFSG.GH74.GLS.IVK.Proofs2
