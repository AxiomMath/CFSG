module

public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly
public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace ExcRank

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem eq_of_pow_eq_of_coprime {M : Type*} [CommGroup M] {x y : M} {p q : ℕ}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hq : Nat.Coprime p q) (h : x ^ q = y ^ q) : x = y := by
  have h1 : (x * y⁻¹) ^ q = 1 := by rw [mul_pow, inv_pow, h, mul_inv_cancel]
  have h2 : (x * y⁻¹) ^ p = 1 := by rw [mul_pow, inv_pow, hx, hy, inv_one, mul_one]
  have h3 : orderOf (x * y⁻¹) ∣ Nat.gcd p q :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1)
  rw [Nat.Coprime.gcd_eq_one hq] at h3
  have h4 : orderOf (x * y⁻¹) = 1 := Nat.dvd_one.1 h3
  rw [orderOf_eq_one_iff, mul_inv_eq_one] at h4
  exact h4


variable {τ : Tag} {L : Type} [Field L]

theorem canonicalRep_mem_familyGroup_of_closure {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    {y : WeylGroup τ}
    (hy : y ∈ Subgroup.closure ((fun α => rootReflection α) '' familyKernel a)) :
    canonicalRep (coxeterSystem τ) L y ∈ familyGroup (K := L) a := by
  let R : Subgroup (WeylGroup τ) :=
    { carrier := {x | canonicalRep (coxeterSystem τ) L x ∈ familyGroup (K := L) a}
      mul_mem' := fun {x x'} hx hx' => by
        obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (τ := τ) (R := L) x x'
        have hmul : canonicalRep (coxeterSystem τ) L (x * x') =
            k⁻¹ * (canonicalRep (coxeterSystem τ) L x * canonicalRep (coxeterSystem τ) L x') := by
          rw [hkk]
          group
        show canonicalRep (coxeterSystem τ) L (x * x') ∈ familyGroup (K := L) a
        rw [hmul]
        exact mul_mem (inv_mem (Subgroup.mem_sup_left hk)) (mul_mem hx hx')
      one_mem' := by
        show canonicalRep (coxeterSystem τ) L 1 ∈ familyGroup (K := L) a
        rw [canonicalRep_one]
        exact one_mem _
      inv_mem' := fun {x} hx => by
        obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (τ := τ) (R := L) x x⁻¹
        rw [mul_inv_cancel, canonicalRep_one, mul_one] at hkk
        have hinv : canonicalRep (coxeterSystem τ) L x⁻¹ =
            (canonicalRep (coxeterSystem τ) L x)⁻¹ * k := by
          rw [← hkk]
          group
        show canonicalRep (coxeterSystem τ) L x⁻¹ ∈ familyGroup (K := L) a
        rw [hinv]
        exact mul_mem (inv_mem hx) (Subgroup.mem_sup_left hk) }
  have hgen : ∀ r ∈ (fun α => rootReflection α) '' familyKernel a, r ∈ R := by
    rintro r ⟨α, hα, rfl⟩
    show canonicalRep (coxeterSystem τ) L (rootReflection α) ∈ familyGroup (K := L) a
    have hn := canonicalRep_rootReflection_mem (τ := τ) (K := L) hα.1
    have hneg : -α ∈ familyKernel a := ⟨IsRoot.neg hα.1, fun i => by
      have h1 := hα.2 i
      simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib] at h1 ⊢
      rw [h1, inv_one]⟩
    have hsub : rootSubgroup τ L α ⊔ rootSubgroup τ L (-α) ≤ familyGroup (K := L) a :=
      sup_le ((rootSubgroup_le_rootSpan (τ := τ) (K := L) hα).trans le_sup_right)
        ((rootSubgroup_le_rootSpan (τ := τ) (K := L) hneg).trans le_sup_right)
    exact (sup_le le_sup_left hsub) hn
  exact (Subgroup.closure_le R).2 (fun r hr => hgen r hr) hy

variable {ι : Type}

theorem exists_datum_change [IsAlgClosed L] (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ] (e : ℕ)
    (he : 1 ≤ e) (a : ι → Fin τ.rank → Lˣ) (w w0 : WeylGroup τ) (g : ModGL τ L)
    (hfix : entrywiseFrobGL τ L ℓ e g = g * canonicalRep (coxeterSystem τ) L w)
    (hw0 : (fun α => w0 • α) '' familyKernel a = familyKernel a)
    (hy : canonicalRep (coxeterSystem τ) L (w0⁻¹ * w) ∈ familyGroup (K := L) a) :
    ∃ z ∈ familyGroup (K := L) a,
      entrywiseFrobGL τ L ℓ e (g * z) = g * z * canonicalRep (coxeterSystem τ) L w0 := by
  have hQ := canonicalRep_mem_normalizer_of_image (τ := τ) (K := L) hw0
  obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (τ := τ) (R := L) w0 (w0⁻¹ * w)
  rw [mul_inv_cancel_left] at hkk
  have hmM : canonicalRep (coxeterSystem τ) L w *
      (canonicalRep (coxeterSystem τ) L w0)⁻¹ ∈ familyGroup (K := L) a := by
    have h1 : canonicalRep (coxeterSystem τ) L w =
        k⁻¹ * (canonicalRep (coxeterSystem τ) L w0 *
          canonicalRep (coxeterSystem τ) L (w0⁻¹ * w)) := by
      rw [hkk]
      group
    rw [h1]
    have hc := (Subgroup.mem_normalizer_iff.1 hQ _).1 hy
    have h2 : k⁻¹ * (canonicalRep (coxeterSystem τ) L w0 *
          canonicalRep (coxeterSystem τ) L (w0⁻¹ * w)) *
        (canonicalRep (coxeterSystem τ) L w0)⁻¹ =
        k⁻¹ * (canonicalRep (coxeterSystem τ) L w0 *
          canonicalRep (coxeterSystem τ) L (w0⁻¹ * w) *
          (canonicalRep (coxeterSystem τ) L w0)⁻¹) := by
      group
    rw [h2]
    exact mul_mem (inv_mem (Subgroup.mem_sup_left hk)) hc
  have hn : (g⁻¹ * entrywiseFrobGL τ L ℓ e g) =
      (canonicalRep (coxeterSystem τ) L w * (canonicalRep (coxeterSystem τ) L w0)⁻¹) *
        canonicalRep (coxeterSystem τ) L w0 := by
    rw [hfix]
    group
  obtain ⟨z, hz, hzeq⟩ := exists_mem_lang_conj (entrywiseFrobGL τ L ℓ e)
    (M := familyGroup (K := L) a) hmM hn (lang_familyGroup ℓ a e he _ hQ)
  refine ⟨z, hz, ?_⟩
  rw [inv_mul_eq_iff_eq_mul] at hzeq
  exact hzeq

end ExcRank

end CFSG.LocalAnalysis.RankFourTheoremC
