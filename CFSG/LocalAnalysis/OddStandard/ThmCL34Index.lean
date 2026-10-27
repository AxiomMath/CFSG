module

public import CFSG.LocalAnalysis.OddStandard.ThmCL34Aux
public import CFSG.GH74.KGroups.L34Tables

public section

namespace CFSG.OddStandard.ThmC

open CFSG CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 Subgroup


theorem l34IndexThree : L34IndexThree := by
  intro X _ _ hO K hKn hK T hTK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := equiv_of_lieModel hK
  have hcard : Nat.card K = 20160 := by
    rw [Nat.card_congr e.toEquiv, card_group QP QP_ok, QP_valid.2]
  have haut : Nat.card (MulAut K) = 241920 := card_mulAut e
  have hcen : ∀ g : K, (∀ n : K, n * g = g * n) → g = 1 := fun g hg => center_trivial e g hg
  have hodd : ¬ 2 ∣ K.index := fun h =>
    Sylow.not_dvd_index T (h.trans (Subgroup.index_dvd_of_le hTK))
  let c : X →* MulAut K := MulAut.conjNormal
  have hker : c.ker = ⊥ := by
    refine pPrimeCore_eq_bot_iff.1 hO c.ker inferInstance ?_
    by_contra hcop
    have h2 : 2 ∣ Nat.card c.ker :=
      not_not.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).not.1 hcop)
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hgX : orderOf (g : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hg
    have hgK : (g : X) ∈ K := mem_of_orderOf_two_of_odd_index hodd hgX
    have hgc : c (g : X) = 1 := g.2
    generalize (g : X) = g' at hgX hgK hgc
    have hk : (⟨g', hgK⟩ : K) = 1 := by
      apply hcen
      intro n
      apply Subtype.ext
      have h3 : g' * n * g'⁻¹ = n := by
        have h1 : (((c g') n : K) : X) = g' * n * g'⁻¹ := rfl
        have h2 : (((c g') n : K) : X) = n := by rw [hgc]; rfl
        exact h1.symm.trans h2
      show (n : X) * g' = g' * n
      calc (n : X) * g' = (g' * n * g'⁻¹) * g' := by rw [h3]
        _ = g' * n := by group
    have h1 : g' = 1 := congrArg Subtype.val hk
    rw [h1, orderOf_one] at hgX
    omega
  have hinj : Function.Injective c := (MonoidHom.ker_eq_bot_iff c).1 hker
  have hdvd : Nat.card X ∣ Nat.card (MulAut K) := Subgroup.card_dvd_of_injective c hinj
  rw [← Subgroup.index_mul_card K, hcard, haut] at hdvd
  have h12 : K.index ∣ 12 := by
    have : K.index * 20160 ∣ 12 * 20160 := by simpa using hdvd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
  have hcop : Nat.Coprime K.index (2 ^ 2) :=
    Nat.Coprime.pow_right 2 ((Nat.coprime_comm.trans (Nat.Prime.coprime_iff_not_dvd
      Nat.prime_two)).2 hodd)
  exact hcop.dvd_of_dvd_mul_right (by simpa using h12 : K.index ∣ 3 * 2 ^ 2)

end CFSG.OddStandard.ThmC
