module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSInvolutions

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Blueprint
  CFSG.Blueprint.NativeSporadic

section Model

set_option linter.unusedSectionVars false


theorem mul_self_eq_one_of_fix_odd_t2 (τ : ↥hsP) (hτ : (τ : Equiv.Perm (Fin 3850)) = hsT2)
    (φ : MulAut ↥hsP)
    (hφ : ∀ x ∈ centralizer ({τ} : Set ↥hsP), Odd (orderOf x) → φ x = x) : φ * φ = 1 := by
  obtain ⟨e, he, -⟩ := hs_full_automorphism_model
  obtain ⟨x, rfl⟩ := e.surjective φ
  have key : ∀ (a : Equiv.Perm (Fin 3850)) (n : ℕ), a ∈ hsC2 → a ^ n = 1 → Odd n →
      (x : Equiv.Perm (Fin 3850)) * a = a * x := by
    intro a n ha han hn
    have haτ : (⟨a, (mem_inf.1 ha).1⟩ : ↥hsP) ∈ centralizer ({τ} : Set ↥hsP) := by
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (by simpa [hτ] using mem_centralizer_singleton_iff.1 (mem_inf.1 ha).2)
    have hord : Odd (orderOf (⟨a, (mem_inf.1 ha).1⟩ : ↥hsP)) := by
      rw [← Subgroup.orderOf_coe]
      exact hn.of_dvd_nat (orderOf_dvd_of_pow_eq_one han)
    exact (CFSG.EvenSporadicStandard.HSStd.aut_apply_eq_iff he x _).1 (hφ _ haτ hord)
  have hx2 := hs_u2b (x : Equiv.Perm (Fin 3850)) x.2
    (key _ 5 hsOddA_mem hsOddA_pow (by decide)) (key _ 3 hsOddB_mem hsOddB_pow (by decide))
  rw [← map_mul, show x * x = 1 from Subtype.ext hx2, map_one]

theorem mul_self_eq_one_of_fix_odd_hsP (m : ↥hsP) (hm : orderOf m = 2)
    (h2B : Nat.card (centralizer ({m} : Set ↥hsP)) = 2880) (φ : MulAut ↥hsP)
    (hφ : ∀ x ∈ centralizer ({m} : Set ↥hsP), Odd (orderOf x) → φ x = x) : φ * φ = 1 := by
  obtain ⟨-, -, -, h2, -⟩ := CFSG.Sporadic.SmallOddCore.hs_reps
  obtain ⟨hm2, ho2⟩ := hsT2_mem_ord
  set τ : ↥hsP := ⟨hsT2, hm2⟩ with hτ
  have hτ2 : orderOf τ = 2 := by rw [← Subgroup.orderOf_coe]; exact ho2
  have hcτ : Nat.card (centralizer ({τ} : Set ↥hsP)) = 2880 := by
    rw [hτ, card_centralizer_hsP]
    exact h2
  obtain ⟨c, hc⟩ := isConj_iff.1
    (hsInvolutionData_hsP.isConj_of_card_eq hm hτ2 (h2B.trans hcτ.symm))
  set A : MulAut ↥hsP := MulAut.conj c with hA
  have hψ : (A * φ * A⁻¹) * (A * φ * A⁻¹) = 1 :=
    mul_self_eq_one_of_fix_odd_t2 τ rfl (A * φ * A⁻¹) fun x hx hxo => by
      have h2 : A⁻¹ x = c⁻¹ * x * c := by simp [hA]
      have hm' : m = c⁻¹ * τ * c := by rw [← hc]; group
      have hy : A⁻¹ x ∈ centralizer ({m} : Set ↥hsP) := by
        rw [mem_centralizer_singleton_iff]
        have h1 : x * τ = τ * x := mem_centralizer_singleton_iff.1 hx
        rw [h2, hm']
        calc c⁻¹ * x * c * (c⁻¹ * τ * c) = c⁻¹ * (x * τ) * c := by group
          _ = c⁻¹ * (τ * x) * c := by rw [h1]
          _ = c⁻¹ * τ * c * (c⁻¹ * x * c) := by group
      have hyo : Odd (orderOf (A⁻¹ x)) := by rwa [MulEquiv.orderOf_eq]
      have hfix := hφ _ hy hyo
      show A (φ (A⁻¹ x)) = x
      rw [hfix, h2]
      simp only [hA, MulAut.conj_apply]
      group
  calc φ * φ = A⁻¹ * ((A * φ * A⁻¹) * (A * φ * A⁻¹)) * A := by group
    _ = 1 := by rw [hψ]; group

theorem mul_self_eq_one_of_fix_odd_hs {Y : Type} [Group Y] (hY : IsSporadic Y .HS)
    (m : Y) (hm : orderOf m = 2) (h2B : Nat.card (centralizer ({m} : Set Y)) = 2880)
    (φ : MulAut Y)
    (hφ : ∀ x ∈ centralizer ({m} : Set Y), Odd (orderOf x) → φ x = x) : φ * φ = 1 := by
  obtain ⟨e₀⟩ := hY
  have e : Y ≃* NativeSporadic.HS := e₀
  obtain ⟨f⟩ : Nonempty (Y ≃* ↥hsP) := ⟨e.trans hsPermEquiv⟩
  let ψ : MulAut ↥hsP := f.symm.trans (φ.trans f)
  have hψ : ψ * ψ = 1 := by
    refine mul_self_eq_one_of_fix_odd_hsP (f m) ((f.orderOf_eq m).trans hm)
      ((card_centralizer_equiv f m).trans h2B) ψ fun x hx hxo => ?_
    have hy : f.symm x ∈ centralizer ({m} : Set Y) := by
      rw [mem_centralizer_singleton_iff]
      have h1 : x * f m = f m * x := mem_centralizer_singleton_iff.1 hx
      apply f.injective
      simpa using h1
    have hyo : Odd (orderOf (f.symm x)) := by rwa [MulEquiv.orderOf_eq]
    show f (φ (f.symm x)) = x
    rw [hφ _ hy hyo]
    simp
  ext y
  have h := congrArg (fun χ : MulAut ↥hsP => χ (f y)) hψ
  simp only [MulAut.mul_apply, MulAut.one_apply] at h ⊢
  apply f.injective
  simpa [ψ] using h

theorem sq_mem_centralizer_of_normalizes {G : Type} [Group G] (M : Subgroup G)
    (hM : IsSporadic ↥M .HS) (m : G) (hmM : m ∈ M) (hm : orderOf m = 2)
    (h2B : Nat.card (M ⊓ centralizer ({m} : Set G) : Subgroup G) = 2880)
    (ζ : G) (hζ : ζ ∈ normalizer (M : Set G))
    (hfix : ∀ x ∈ M, x * m = m * x → Odd (orderOf x) → ζ * x = x * ζ) :
    ∀ x ∈ M, ζ ^ 2 * x = x * ζ ^ 2 := by
  set m' : ↥M := ⟨m, hmM⟩ with hm'
  have hm2 : orderOf m' = 2 := by rw [← Subgroup.orderOf_coe]; exact hm
  have hcard : Nat.card (centralizer ({m'} : Set ↥M)) = 2880 := by
    rw [← h2B]
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, mem_centralizer_singleton_iff.2 (by
          have := mem_centralizer_singleton_iff.1 x.2
          exact congrArg Subtype.val this)⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, mem_centralizer_singleton_iff.2 (Subtype.ext (by
          exact mem_centralizer_singleton_iff.1 x.2.2))⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  set φ : MulAut ↥M := M.normalizerMonoidHom ⟨ζ, hζ⟩ with hφdef
  have hφapp : ∀ x : ↥M, ((φ x : ↥M) : G) = ζ * x * ζ⁻¹ := fun x => rfl
  have hsq := mul_self_eq_one_of_fix_odd_hs hM m' hm2 hcard φ fun x hx hxo => by
    have hc : (x : G) * m = m * x := by
      have := mem_centralizer_singleton_iff.1 hx
      exact congrArg Subtype.val this
    have hxo' : Odd (orderOf (x : G)) := by rwa [Subgroup.orderOf_coe]
    have h := hfix x x.2 hc hxo'
    apply Subtype.ext
    rw [hφapp, h]
    group
  intro x hx
  rw [pow_two]
  have h := congrArg (fun χ : MulAut ↥M => ((χ ⟨x, hx⟩ : ↥M) : G)) hsq
  simp only [MulAut.mul_apply, MulAut.one_apply, hφapp] at h
  calc ζ * ζ * x = (ζ * (ζ * x * ζ⁻¹) * ζ⁻¹) * (ζ * ζ) := by group
    _ = x * (ζ * ζ) := by rw [h]

end Model

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
