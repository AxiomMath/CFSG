module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem even_unitary_all_involution_full_centralizer_odd_core {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K} (hC : IsPrimeFormGram C) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    {H : Subgroup (MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)))}
    (hH : inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) ≤ H) :
    ∀ α ∈ H, orderOf α = 2 → CFSG.oddCore ↥(H ⊓ centralizer {α}) = ⊥ := by
  intro α hαH hα
  rcases (even_unitary_involution_matrix_lifts h hC hn hq α hα).1 with hF | hF
  ·
    have hαD : α ∈ primeFormD h (C : Matrix (Fin n) (Fin n) K) := by
      rw [← ker_primeFormFieldFactor h hC hn hq, MonoidHom.mem_ker]
      exact hF
    exact (even_unitary_inner_involution_full_centralizer_odd_core h hC hn hq hH).1 α hαH hαD hα
  ·
    obtain ⟨-, -, C₀, hC₀, hcase₀, -, -, -, -, ⟨θ, -, hθα⟩, -⟩ :=
      even_unitary_antiunitary_involution_descent h hC hn hq α hα hF
    set φ := primeFormFieldFactor h hC hn hq α with hφ
    set T := MulAut.congr θ with hT
    have hαT : α = T (primeFormFieldHom h hC₀ φ) := MulEquiv.ext fun x => by
      rw [hθα x, hT, MulAut.congr_apply]
      rfl
    have hH' : inner (primeFormP h (C₀ : Matrix (Fin n) (Fin n) K)) ≤ H.comap T.toMonoidHom := by
      rintro _ ⟨y, rfl⟩
      rw [mem_comap]
      apply hH
      refine ⟨θ y, MulEquiv.ext fun x => ?_⟩
      change θ y * x * (θ y)⁻¹ = θ (y * θ.symm x * y⁻¹)
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    have h0 := even_unitary_canonical_field_involution_odd_core h hn hq hC₀ hcase₀ φ hF hH'
    have hmem : ∀ x : MulAut (primeFormP h (C₀ : Matrix (Fin n) (Fin n) K)),
        x ∈ H.comap T.toMonoidHom ⊓ centralizer {primeFormFieldHom h hC₀ φ} ↔
          T x ∈ H ⊓ centralizer {α} := by
      intro x
      rw [mem_inf, mem_inf, mem_comap, mem_centralizer_singleton_iff,
        mem_centralizer_singleton_iff, hαT]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [← map_mul, ← map_mul, h2]⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, T.injective (by rw [map_mul, map_mul, h2])⟩
    let e : ↥(H.comap T.toMonoidHom ⊓ centralizer {primeFormFieldHom h hC₀ φ}) ≃*
        ↥(H ⊓ centralizer {α}) :=
      { toFun := fun x => ⟨T x, (hmem x).mp x.2⟩
        invFun := fun y => ⟨T.symm y, (hmem _).mpr (by rw [MulEquiv.apply_symm_apply]; exact y.2)⟩
        left_inv := fun x => Subtype.ext (T.symm_apply_apply x)
        right_inv := fun y => Subtype.ext (T.apply_symm_apply y)
        map_mul' := fun x y => Subtype.ext
          (map_mul T (x : MulAut (primeFormP h (C₀ : Matrix (Fin n) (Fin n) K))) y) }
    exact EvenCatalog.oddCore_eq_bot_of_mulEquiv e h0

end CFSG.ComponentClassification.UnbalancedCatalog
