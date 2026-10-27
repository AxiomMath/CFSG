module

public import CFSG.LieType.Universal.Unitary.BinaryModel.FixedLine
public import CFSG.LieType.SpecialLinear.ExteriorModel.AdjointHeart
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.StatedTransport
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.QuadraticDescent
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.AdjointHeartUnitary
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open Module CFSG.Open CFSG.HardMathSupport.GuralnickMalle CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.SpecialLinear.ExteriorModel Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} {k : Type} [Field k] [CharP k 2]

omit [CharP k 2] in
theorem toGL_suTwist_apply (φ₀ : K →+* k) {m : ℕ} (g : SU (unitaryInvolution K 2 f) m) (r : Fin f) :
    SpecialLinearGroup.toGL (suTwist φ₀ f m g r) =
      GeneralLinearGroup.map (suFrob φ₀ f r) (g : GL (Fin m) K) := by
  refine Units.ext ?_
  rw [SpecialLinearGroup.coe_GL_coe_matrix, coe_suTwist_apply, SUExtras.mat_apply]
  rfl

theorem card_le_of_suRep_adjoint (hK : Nat.card K = (2 ^ f) ^ 2) (φ₀ : K →+* k) {m : ℕ} (hm : 3 ≤ m)
    (ε : Fin f → Finset (Fin m)) {P : Subgroup (SU (unitaryInvolution K 2 f) m)}
    (hPel : IsElemAbelian 2 P) (i₀ : Fin f) (hε' : ∀ i, i ≠ i₀ → ε i = ∅)
    (hε : ε i₀ = {⟨1, by omega⟩, ⟨m - 1, by omega⟩})
    (hquad : ∀ a ∈ P, ∀ b ∈ P, (suRep φ₀ m ε a - 1) * (suRep φ₀ m ε b - 1) = 0) :
    Nat.card P ≤ 2 ^ f := by
  obtain ⟨Φ, hΦ⟩ := exists_bModel_equiv_adjointHeart (k := k) hm ε i₀ hε hε'
  let ψ := suFrob φ₀ f i₀
  let τ' : Representation k (SU (unitaryInvolution K 2 f) m) (AdjointHeart m k) :=
    (adjointHeartRep m k).comp
      ((GeneralLinearGroup.map ψ).comp (SU (unitaryInvolution K 2 f) m).subtype)
  have hβ : ∀ (g : SU (unitaryInvolution K 2 f) m) (v : BModel k ε),
      Φ (suRep φ₀ m ε g v) = τ' g (Φ v) := by
    intro g v
    rw [suRep, MonoidHom.comp_apply, hΦ, toGL_suTwist_apply]
    rfl
  have hquadK : ∀ a ∈ P, ∀ b ∈ P, (adjointHeartRep m K (a : GL (Fin m) K) - 1) *
      (adjointHeartRep m K (b : GL (Fin m) K) - 1) = 0 := fun a ha b hb =>
    adjointHeartRep_sub_one_mul_sub_one_of_map ψ _ _
      (sub_one_mul_sub_one_of_equiv Φ hβ (hquad a ha b hb))
  obtain ⟨A, hAS, hAel, hcard, hA⟩ := exists_stated_transport hK hPel
  rw [← hcard]
  refine card_le_of_adjointHeart_of_le_statedSU hK hAS hAel fun a ha b hb => ?_
  obtain ⟨x, hx, rfl⟩ := hA a ha
  obtain ⟨y, hy, rfl⟩ := hA b hb
  exact sub_one_mul_sub_one_conj _ _ _ _ (hquadK x hx y hy)

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
