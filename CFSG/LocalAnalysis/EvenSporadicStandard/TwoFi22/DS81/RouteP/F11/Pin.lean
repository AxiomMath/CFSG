module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F11.Sylow

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

theorem exists_equiv_mem_iff_of_odd_index_normalizer {L C : Type*} [Group L] [Group C] [Finite C]
    (ψ₀ : L ≃* C) {E : Subgroup L} {EC : Subgroup C} {n : ℕ}
    (hodd : Odd (Subgroup.normalizer (EC : Set C)).index)
    (hsq : ∀ x ∈ E, x ^ 2 = 1) (hcard : Nat.card E = n)
    (huniq : ∀ B : Subgroup C, B ≤ Subgroup.normalizer (EC : Set C) →
      (∀ b ∈ B, b ^ 2 = 1) → Nat.card B = n → B = EC) :
    ∃ ψ : L ≃* C, ∀ x : L, x ∈ E ↔ ψ x ∈ EC := by
  set F : Subgroup C := E.map ψ₀.toMonoidHom with hFdef
  have hFsq : ∀ y ∈ F, y ^ 2 = 1 := by
    intro y hy
    rw [hFdef, Subgroup.mem_map_equiv] at hy
    have h := congr_arg ψ₀ (hsq (ψ₀.symm y) hy)
    simpa using h
  have hF : IsPGroup 2 F := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (by simpa using hFsq g g.2)
  have huniq' : ∀ B : Subgroup C, B ≤ Subgroup.normalizer (EC : Set C) →
      Nonempty (↥B ≃* ↥F) → B = EC := by
    intro B hB hBiso
    obtain ⟨φ⟩ := hBiso
    refine huniq B hB (fun b hb => ?_) ?_
    · have hφ : (φ ⟨b, hb⟩) ^ 2 = 1 :=
        Subtype.ext (by simpa using hFsq (φ ⟨b, hb⟩) (φ ⟨b, hb⟩).2)
      have hb2 : (⟨b, hb⟩ : ↥B) ^ 2 = 1 := by
        have h := congr_arg (fun z : ↥F => φ.symm z) hφ
        simpa using h
      have h := congr_arg (fun z : ↥B => (z : C)) hb2
      simpa using h
    · have hcardB : Nat.card B = Nat.card F := Nat.card_congr φ.toEquiv
      have hcardF : Nat.card F = n := by
        rw [hFdef, ← hcard]
        exact Subgroup.card_map_of_injective (K := E) (f := ψ₀.toMonoidHom) ψ₀.injective
      exact hcardB.trans hcardF
  obtain ⟨c, hc⟩ :=
    exists_conj_of_odd_index_normalizer (E := EC) (F := F) hodd hF huniq'
  refine ⟨ψ₀.trans (MulAut.conj c⁻¹), fun x => ?_⟩
  have h1 : x ∈ E ↔ ψ₀ x ∈ F := by
    rw [hFdef, Subgroup.mem_map_equiv]
    simp
  have h2 : ψ₀ x ∈ F ↔ c⁻¹ * ψ₀ x * c ∈ EC := hc (ψ₀ x)
  have h3 : (ψ₀.trans (MulAut.conj c⁻¹)) x = c⁻¹ * ψ₀ x * c := by
    rw [MulEquiv.trans_apply, MulAut.conj_apply]
    simp
  rw [h3]
  exact h1.trans h2

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
