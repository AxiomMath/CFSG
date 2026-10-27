module

public import CFSG.GH74.GLS.IVK.A7.Glue
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.C3.Layer1.Back91Setup
public import CFSG.GH74.GLS.C3.Layer1.BackAuxSA
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back

theorem isD8_of_card_eight_alt7 {X : Subgroup (alternatingGroup (Fin 7))} (hX : Nat.card ↥X = 8) :
    Nonempty (↥X ≃* DihedralGroup 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X' : Subgroup (Equiv.Perm (Fin 7)) := X.map (alternatingGroup (Fin 7)).subtype
  have hX'card : Nat.card ↥X' = 8 := by
    rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective]
    exact hX
  have hX'2 : IsPGroup 2 ↥X' := IsPGroup.of_card (n := 3) (by rw [hX'card]; norm_num)
  obtain ⟨T, hT⟩ := hX'2.exists_le_sylow
  obtain ⟨k, hk, hk2, ⟨d⟩⟩ := IVK.ivk_1_1a T
  have hk4 : k = 4 := by omega
  subst hk4
  have hX'le : X' ≤ (T : Subgroup (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) :=
    le_inf hT (by rintro _ ⟨y, -, rfl⟩; exact y.2)
  have hTAcard : Nat.card ↥((T : Subgroup (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) = 8 := by
    rw [Nat.card_congr d.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  have heq : X' = (T : Subgroup (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) :=
    Subgroup.eq_of_le_of_card_ge hX'le (by rw [hTAcard, hX'card])
  exact ⟨(Subgroup.equivMapOfInjective X (alternatingGroup (Fin 7)).subtype
    (alternatingGroup (Fin 7)).subtype_injective).trans ((MulEquiv.subgroupCongr heq).trans d)⟩

theorem factorization_twentyFiveTwenty : (2520 : ℕ).factorization 2 = 3 := by
  have h : (2520 : ℕ) = 2 ^ 3 * 315 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem factorization_two_card_of_equiv_A7 {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (e : kBar K ≃* alternatingGroup (Fin 7)) : (Nat.card ↥K).factorization 2 = 3 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)
  have h2 : Nat.card (kBar K) = 2520 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
  have hne : Nat.card (pPrimeCore 2 ↥K) ≠ 0 := Nat.card_pos.ne'
  have h3 : Nat.card ↥K = 2520 * Nat.card (pPrimeCore 2 ↥K) := by
    rw [h1]
    show Nat.card (kBar K) * _ = _
    rw [h2]
  rw [h3, Nat.factorization_mul (by norm_num) hne, Finsupp.add_apply,
    factorization_twentyFiveTwenty, Setup91.factorization_two_of_odd hodd]

end CFSG.GH74.GLS.C3.Layer1.Bk
