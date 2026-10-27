module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCoverAlternating

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

theorem a5_no_order_four {H : Type} [Group H] (e : H ≃* alternatingGroup (Fin 5)) (a : H)
    (ha : a ^ 4 = 1) : a ^ 2 = 1 := by
  have key : ∀ g : alternatingGroup (Fin 5), g ^ 4 = 1 → g ^ 2 = 1 := by decide +kernel
  apply e.injective
  rw [map_pow, map_one]
  exact key _ (by rw [← map_pow, ha, map_one])

theorem a5_aut_centralizer_inner
    {H : Type} [Group H] (e : H ≃* alternatingGroup (Fin 5))
    (P : Subgroup H) (hP : Nat.card ↥P = 4) (α : MulAut H) (hα : ∀ p ∈ P, α p = p) :
    ∃ h : H, α = MulAut.conj h := by
  have : Finite H := Finite.of_equiv _ e.symm.toEquiv
  have : IsSimpleGroup H := MulEquiv.isSimpleGroup e
  have hH : Nat.card H = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (Nat.card H).factorization 2 = 2 := by
    rw [hH, show (60 : ℕ) = 2 ^ 2 * 15 by norm_num,
      Nat.factorization_mul_apply_of_coprime (by decide), Nat.factorization_pow, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul, Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide)]
  let S : Sylow 2 H := Sylow.ofCard P (by rw [hP, hfac]; norm_num)
  exact CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover.exists_eq_conj_of_card_sixty hH α S
    fun s hs => hα s hs

theorem card_perm_five_dvd_two_part {A : Type} [Group A] [Finite A] (φ : A →* Equiv.Perm (Fin 5))
    (hA : IsPGroup 2 A) : Nat.card ↥φ.range ∣ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥φ.range := hA.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hdvd : Nat.card ↥φ.range ∣ Nat.card (Equiv.Perm (Fin 5)) :=
    Subgroup.card_subgroup_dvd_card _
  have h120 : Nat.card (Equiv.Perm (Fin 5)) = 8 * 15 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  rw [hn, h120] at hdvd
  rw [hn]
  exact (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 15)).dvd_of_dvd_mul_right hdvd

end CFSG.GH74.GLS.C3.Layer1.Back
