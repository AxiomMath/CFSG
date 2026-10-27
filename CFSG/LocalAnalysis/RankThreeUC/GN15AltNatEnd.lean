module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Lift
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltBaumComb

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv
open CFSG.HardMathSupport.Cooperstein.Coordinator

variable {n : ℕ}

theorem altNat_evenWeightPerm_mul (σ τ : Perm (Fin n)) (x : evenWeight n) :
    evenWeightPerm (σ * τ) x = evenWeightPerm σ (evenWeightPerm τ x) :=
  Subtype.ext (funext fun i => by
    simp only [evenWeightPerm, mul_inv_rev, Perm.mul_apply])

theorem altNat_evenWeightPerm_one (x : evenWeight n) : evenWeightPerm 1 x = x :=
  Subtype.ext (funext fun i => by simp [evenWeightPerm])

theorem altNat_evenWeightPerm_add (σ : Perm (Fin n)) (x y : evenWeight n) :
    evenWeightPerm σ (x + y) = evenWeightPerm σ x + evenWeightPerm σ y :=
  Subtype.ext rfl

theorem altNat_endo_eq (hn : Odd n) (h5 : 5 ≤ n) (φ : evenWeight n →+ evenWeight n)
    (hφ : ∀ σ ∈ alternatingGroup (Fin n), ∀ v, φ (evenWeightPerm σ v) = evenWeightPerm σ (φ v)) :
    φ = 0 ∨ φ = AddMonoidHom.id (evenWeight n) := by
  have hy : ∀ x : Fin n, φ (altBaumY hn x) = 0 ∨ φ (altBaumY hn x) = altBaumY hn x := by
    intro x
    refine eq_zero_or_eq_altBaumY_of_fixed hn (by omega) fun σ hσ hσx => ?_
    rw [← hφ σ hσ, evenWeightPerm_altBaumY, hσx]
  have htrans : ∀ x x' : Fin n, ∃ σ ∈ alternatingGroup (Fin n), σ x = x' := fun x x' => by
    obtain ⟨g, hg⟩ := EightFive.exists_alt_apply_eq (by omega : 3 ≤ n) x x'
    exact ⟨g, g.2, hg⟩
  have hspan : ∀ (ψ ψ' : evenWeight n →+ evenWeight n),
      (∀ x, ψ (altBaumY hn x) = ψ' (altBaumY hn x)) → ψ = ψ' := by
    intro ψ ψ' h
    ext v
    rw [← sum_val_smul_altBaumY hn v]
    simp only [map_sum, map_nsmul, h]
  by_cases hx : ∃ x, φ (altBaumY hn x) = altBaumY hn x
  · right
    obtain ⟨x, hx⟩ := hx
    refine hspan φ (AddMonoidHom.id (evenWeight n)) fun x' => ?_
    obtain ⟨σ, hσ, hσx⟩ := htrans x x'
    have := hφ σ hσ (altBaumY hn x)
    rw [hx, evenWeightPerm_altBaumY, hσx] at this
    exact this
  · left
    push Not at hx
    refine hspan φ 0 fun x' => ?_
    exact (hy x').resolve_right (hx x')

theorem altNat_eq_perm_of_twisted (hn : Odd n) (h7 : 7 ≤ n) {θ : evenWeight n →+ evenWeight n}
    (hθ : Function.Injective θ) (c : alternatingGroup (Fin n) ≃* alternatingGroup (Fin n))
    (hc : ∀ (g : alternatingGroup (Fin n)) (v : evenWeight n),
      θ (evenWeightPerm (g : Perm (Fin n)) v) = evenWeightPerm (c g : Perm (Fin n)) (θ v)) :
    ∃ σ : Perm (Fin n), (∀ v, θ v = evenWeightPerm σ v) ∧
      ∀ g : alternatingGroup (Fin n), (c g : Perm (Fin n)) = σ * (g : Perm (Fin n)) * σ⁻¹ := by
  obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    (Or.inr h7) c
  let φ : evenWeight n →+ evenWeight n :=
    { toFun := fun v => evenWeightPerm σ⁻¹ (θ v)
      map_zero' := by
        have : θ 0 = 0 := map_zero θ
        rw [this]; exact Subtype.ext rfl
      map_add' := fun v w => by
        rw [map_add, altNat_evenWeightPerm_add] }
  have hφ : ∀ g ∈ alternatingGroup (Fin n), ∀ v, φ (evenWeightPerm g v) = evenWeightPerm g (φ v) := by
    intro g hg v
    show evenWeightPerm σ⁻¹ (θ (evenWeightPerm g v)) = evenWeightPerm g (evenWeightPerm σ⁻¹ (θ v))
    rw [hc ⟨g, hg⟩ v, ← altNat_evenWeightPerm_mul, ← altNat_evenWeightPerm_mul]
    congr 1
    have := hσ ⟨g, hg⟩
    simp only at this ⊢
    rw [this]
    group
  have hφ1 : φ = AddMonoidHom.id (evenWeight n) := by
    rcases altNat_endo_eq hn (by omega) φ hφ with h | h
    · exfalso
      have h0 : ∀ v, θ v = 0 := fun v => by
        have := congrArg (fun f : evenWeight n →+ evenWeight n => evenWeightPerm σ (f v)) h
        simp only [AddMonoidHom.zero_apply] at this
        have e1 : evenWeightPerm σ (φ v) = θ v := by
          show evenWeightPerm σ (evenWeightPerm σ⁻¹ (θ v)) = θ v
          rw [← altNat_evenWeightPerm_mul, mul_inv_cancel, altNat_evenWeightPerm_one]
        rw [← e1, this]
        exact Subtype.ext rfl
      have hy0 := altBaumY_ne_zero hn (by omega : 2 ≤ n) ⟨0, by omega⟩
      exact hy0 (hθ ((h0 _).trans (map_zero θ).symm))
    · exact h
  refine ⟨σ, fun v => ?_, hσ⟩
  have := DFunLike.congr_fun hφ1 v
  have e1 : evenWeightPerm σ (φ v) = θ v := by
    show evenWeightPerm σ (evenWeightPerm σ⁻¹ (θ v)) = θ v
    rw [← altNat_evenWeightPerm_mul, mul_inv_cancel, altNat_evenWeightPerm_one]
  rw [← e1, this]
  rfl

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
