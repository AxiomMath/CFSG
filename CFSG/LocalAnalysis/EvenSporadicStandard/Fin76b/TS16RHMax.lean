module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RHarada

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem maximal_two_sup_central {G : Type} [Group G] [Finite G] {Y C A V0 : Subgroup G}
    (hYCA : Y = C ⊔ A) (hA2 : IsPGroup 2 A)
    (hAc : ∀ a ∈ A, ∀ y ∈ Y, a * y = y * a)
    (hV0C : V0 ≤ C)
    (hV0max : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ C → V0 ≤ R → R ≤ V0) :
    ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Y → V0 ⊔ A ≤ R → R ≤ V0 ⊔ A := by
  intro R hR2 hRY hV0AR
  have hAcC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a := fun a ha c hc =>
    hAc a ha c (by rw [hYCA]; exact mem_sup_left hc)
  let R' : Subgroup G :=
    { carrier := {c | c ∈ C ∧ ∃ a ∈ A, c * a ∈ R}
      mul_mem' := by
        rintro c₁ c₂ ⟨hc₁, a₁, ha₁, h₁⟩ ⟨hc₂, a₂, ha₂, h₂⟩
        refine ⟨C.mul_mem hc₁ hc₂, a₁ * a₂, A.mul_mem ha₁ ha₂, ?_⟩
        have e : c₁ * c₂ * (a₁ * a₂) = (c₁ * a₁) * (c₂ * a₂) := by
          calc c₁ * c₂ * (a₁ * a₂) = c₁ * (c₂ * a₁) * a₂ := by simp only [mul_assoc]
            _ = c₁ * (a₁ * c₂) * a₂ := by rw [hAcC a₁ ha₁ c₂ hc₂]
            _ = (c₁ * a₁) * (c₂ * a₂) := by simp only [mul_assoc]
        rw [e]
        exact R.mul_mem h₁ h₂
      one_mem' := ⟨C.one_mem, 1, A.one_mem, by rw [mul_one]; exact R.one_mem⟩
      inv_mem' := by
        rintro c ⟨hc, a, ha, h⟩
        refine ⟨C.inv_mem hc, a⁻¹, A.inv_mem ha, ?_⟩
        have hcm : Commute a c := hAcC a ha c hc
        have e : c⁻¹ * a⁻¹ = (c * a)⁻¹ := by
          rw [mul_inv_rev]
          exact hcm.inv_inv.symm.eq
        rw [e]
        exact R.inv_mem h }
  have hR'2 : IsPGroup 2 R' := by
    rintro ⟨c, hcC, a, ha, hca⟩
    have hcm : Commute c a := (hAcC a ha c hcC).symm
    obtain ⟨m, hm⟩ := hR2 ⟨c * a, hca⟩
    obtain ⟨n, hn⟩ := hA2 ⟨a, ha⟩
    have hm' : (c * a) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hn' : a ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h1 : (c * a) ^ 2 ^ (m + n) = 1 := by rw [pow_add, pow_mul, hm', one_pow]
    have h2 : a ^ 2 ^ (m + n) = 1 := by rw [pow_add, pow_mul', hn', one_pow]
    have h3 : c ^ 2 ^ (m + n) = 1 := by
      have e := hcm.mul_pow (2 ^ (m + n))
      rw [h1, h2, mul_one] at e
      exact e.symm
    exact ⟨m + n, Subtype.ext (by simpa using h3)⟩
  have hV0R' : V0 ≤ R' := fun v hv =>
    ⟨hV0C hv, 1, A.one_mem, by rw [mul_one]; exact hV0AR (mem_sup_left hv)⟩
  have hR'C : R' ≤ C := fun c hc => hc.1
  have hR'V0 : R' ≤ V0 := hV0max R' hR'2 hR'C hV0R'
  intro r hr
  have hrY : r ∈ C ⊔ A := by rw [← hYCA]; exact hRY hr
  have hAcent : A ≤ centralizer (C : Set G) := fun a ha =>
    mem_centralizer_iff.2 fun c hc => (hAcC a ha c hc).symm
  obtain ⟨c, hcC, a, ha, rfl⟩ := exists_mul_of_mem_sup_comm' hAcent hrY
  have hcR' : c ∈ R' := ⟨hcC, a, ha, hr⟩
  exact (V0 ⊔ A).mul_mem (mem_sup_left (hR'V0 hcR')) (mem_sup_right ha)

end CFSG.EvenSporadicStandard.Fin76b
