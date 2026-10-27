module

public import CFSG.Quasithin.Background.JonesParshallSL2

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbModule

open CFSG.Quasithin.JonesParshall
open scoped Matrix

@[expose] noncomputable def natRep (K : Type) [Field K] [Algebra (ZMod 2) K] :
    Representation (ZMod 2) (SL2 K) (Fin 2 → K) where
  toFun g := AddMonoidHom.toZModLinearMap 2 (mu2 g : (Fin 2 → K) →+ (Fin 2 → K))
  map_one' := LinearMap.ext fun w => by
    change mu2 (1 : SL2 K) w = w
    rw [map_one]
    rfl
  map_mul' g h := LinearMap.ext fun w => by
    change mu2 (g * h) w = mu2 g (mu2 h w)
    rw [map_mul]
    rfl

theorem natRep_apply {K : Type} [Field K] [Algebra (ZMod 2) K] (g : SL2 K) (w : Fin 2 → K) :
    natRep K g w = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w := rfl

namespace DualNat

variable (K : Type) [Field K] [Algebra (ZMod 2) K]

noncomputable def trSymp : LinearMap.BilinForm (ZMod 2) (Fin 2 → K) :=
  LinearMap.mk₂ (ZMod 2) (fun v w => Algebra.trace (ZMod 2) K (v 0 * w 1 + v 1 * w 0))
    (fun v₁ v₂ w => by
      rw [← map_add]
      exact congrArg _ (by simp only [Pi.add_apply]; ring))
    (fun c v w => by
      rw [← map_smul]
      exact congrArg _ (by simp only [Pi.smul_apply, smul_mul_assoc, smul_add]))
    (fun v w₁ w₂ => by
      rw [← map_add]
      exact congrArg _ (by simp only [Pi.add_apply]; ring))
    (fun c v w => by
      rw [← map_smul]
      exact congrArg _ (by simp only [Pi.smul_apply, mul_smul_comm, smul_add]))

variable {K}

theorem trSymp_apply (v w : Fin 2 → K) :
    trSymp K v w = Algebra.trace (ZMod 2) K (v 0 * w 1 + v 1 * w 0) := by
  simp [trSymp]

theorem trSymp_comm (v w : Fin 2 → K) : trSymp K v w = trSymp K w v := by
  rw [trSymp_apply, trSymp_apply]
  exact congrArg _ (by ring)

theorem symp_natRep [CharP K 2] (g : SL2 K) (v w : Fin 2 → K) :
    natRep K g v 0 * natRep K g w 1 + natRep K g v 1 * natRep K g w 0 =
      v 0 * w 1 + v 1 * w 0 := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) K).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [natRep_apply, natRep_apply, mulVec_two_zero, mulVec_two_one, mulVec_two_zero,
    mulVec_two_one]
  generalize (g : Matrix (Fin 2) (Fin 2) K) = M at hdet ⊢
  linear_combination (v 0 * w 1 + v 1 * w 0) * hdet +
    (M 0 0 * M 1 0 * v 0 * w 0 + M 0 1 * M 1 1 * v 1 * w 1 +
      M 0 1 * M 1 0 * (v 0 * w 1 + v 1 * w 0)) * h2

theorem trSymp_natRep [CharP K 2] (g : SL2 K) (v w : Fin 2 → K) :
    trSymp K (natRep K g v) (natRep K g w) = trSymp K v w := by
  rw [trSymp_apply, trSymp_apply, symp_natRep]

theorem trSymp_natRep_left [CharP K 2] (g : SL2 K) (v w : Fin 2 → K) :
    trSymp K (natRep K g v) w = trSymp K v (natRep K g⁻¹ w) := by
  rw [← trSymp_natRep g v (natRep K g⁻¹ w), Representation.self_inv_apply]

theorem eq_zero_of_trace_mul [Finite K] {c : K}
    (h : ∀ x : K, Algebra.trace (ZMod 2) K (c * x) = 0) : c = 0 := by
  by_contra hc
  obtain ⟨y, hy⟩ := Algebra.trace_surjective (ZMod 2) K 1
  have := h (y / c)
  rw [mul_div_cancel₀ _ hc, hy] at this
  exact one_ne_zero this

theorem trSymp_nondegenerate [Finite K] : (trSymp K).Nondegenerate := by
  have hsep : ∀ v : Fin 2 → K, (∀ w, trSymp K v w = 0) → v = 0 := fun v hv => by
    have h0 : v 0 = 0 := eq_zero_of_trace_mul fun x => by
      simpa [trSymp_apply] using hv ![0, x]
    have h1 : v 1 = 0 := eq_zero_of_trace_mul fun x => by
      simpa [trSymp_apply] using hv ![x, 0]
    funext i
    fin_cases i
    · exact h0
    · exact h1
  exact ⟨hsep, fun w hw => hsep w fun v => (trSymp_comm v w).symm.trans (hw v)⟩

end DualNat

theorem natRep_dual_equiv (K : Type) [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K] :
    ∃ Φ : (Fin 2 → K) ≃+ Module.Dual (ZMod 2) (Fin 2 → K),
      ∀ (g : SL2 K) (w : Fin 2 → K), Φ (natRep K g w) = (natRep K).dual g (Φ w) :=
  ⟨((DualNat.trSymp K).toDual DualNat.trSymp_nondegenerate).toAddEquiv, fun g w =>
    LinearMap.ext fun w' => DualNat.trSymp_natRep_left g w w'⟩

end CFSG.CGT.PushingUpLit.CGT6.EmbModule
