module

public import CFSG.Quasithin.H13.L32AC44c
public import CFSG.RankThree.FFModules.Transvections

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open Matrix
open scoped MatrixGroups

namespace InnerSemi

theorem exists_mulEquiv {F : Type} [Field F] [Fintype F] (a : (Fin 3 → F) ≃+ (Fin 3 → F))
    (hn : ∀ g : SL(3, F), ∃ g' : SL(3, F), ∀ v : Fin 3 → F,
      a ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = (g' : Matrix (Fin 3) (Fin 3) F) *ᵥ a v) :
    ∃ α : SL(3, F) ≃* SL(3, F), ∀ (g : SL(3, F)) (v : Fin 3 → F),
      a ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
        ((α g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ a v := by
  choose α hα using hn
  have hmul : ∀ g h : SL(3, F), α (g * h) = α g * α h := by
    intro g h
    refine CFSG.Quasithin.H13.L32A.C.SL3N.ext_of_mulVec fun w => ?_
    obtain ⟨v, rfl⟩ := a.surjective w
    rw [← hα, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec,
      Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, ← hα, ← hα]
  let φ : SL(3, F) →* SL(3, F) := MonoidHom.mk' α hmul
  have hinj : Function.Injective φ := by
    intro g h hgh
    refine CFSG.Quasithin.H13.L32A.C.SL3N.ext_of_mulVec fun v => a.injective ?_
    rw [hα g v, hα h v]
    exact congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F) *ᵥ a v) hgh
  exact ⟨MulEquiv.ofBijective φ (Finite.injective_iff_bijective.mp hinj), hα⟩

theorem exists_ringEquiv {F : Type} [Field F] [Fintype F] (E : (Fin 3 → F) ≃+ (Fin 3 → F))
    (μ : F → F) (hμ : ∀ (c : F) (v : Fin 3 → F), E (c • v) = μ c • E v) :
    ∃ θ : F ≃+* F, ∀ (c : F) (v : Fin 3 → F), E (c • v) = θ c • E v := by
  let e : Fin 3 → F := Pi.single 0 1
  have he : e ≠ 0 := fun h => by simpa [e] using congrFun h 0
  have hne : E e ≠ 0 := fun h => he (E.injective (h.trans (map_zero E).symm))
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  replace hi : E e i ≠ 0 := hi
  have hcoord : ∀ c : F, E (c • e) i = μ c * E e i := fun c => by rw [hμ]; rfl
  have h1 : μ 1 = 1 := by
    have h := hcoord 1
    rw [one_smul] at h
    exact mul_right_cancel₀ hi (by rw [one_mul]; exact h.symm)
  have hadd : ∀ c d, μ (c + d) = μ c + μ d := by
    intro c d
    refine mul_right_cancel₀ hi ?_
    have h := hcoord (c + d)
    rw [add_smul, map_add, Pi.add_apply, hcoord c, hcoord d] at h
    rw [add_mul]
    exact h.symm
  have hmulμ : ∀ c d, μ (c * d) = μ c * μ d := by
    intro c d
    refine mul_right_cancel₀ hi ?_
    have h := hcoord (c * d)
    rw [mul_smul, hμ, Pi.smul_apply, smul_eq_mul, hcoord d] at h
    rw [mul_assoc]
    exact h.symm
  have hzero : μ 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    linear_combination -h
  let θR : F →+* F :=
    { toFun := μ, map_one' := h1, map_mul' := hmulμ, map_zero' := hzero, map_add' := hadd }
  exact ⟨RingEquiv.ofBijective θR (Finite.injective_iff_bijective.mp θR.injective), hμ⟩

theorem not_tauSL {F : Type} [Field F] [Fintype F] [CharP F 2] (b : (Fin 3 → F) ≃+ (Fin 3 → F))
    (h : ∀ (g : SL(3, F)) (v : Fin 3 → F), b ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
      ((CFSG.QuasithinUnique.Setup.X7a.tauSL F g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        b v) : False :=
  CFSG.RankThree.FFModules.not_exists_natural_dual_iso ⟨b, fun g v => h g v⟩

end InnerSemi

theorem semilinear_of_normalizes {F : Type} [Field F] [Fintype F] [CharP F 2] {f : ℕ}
    (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ f) (a : (Fin 3 → F) ≃+ (Fin 3 → F))
    (hn : ∀ g : SL(3, F), ∃ g' : SL(3, F), ∀ v : Fin 3 → F,
      a ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = (g' : Matrix (Fin 3) (Fin 3) F) *ᵥ a v) :
    ∃ μ : F ≃+* F, ∀ (c : F) (v : Fin 3 → F), a (c • v) = μ c • a v := by
  obtain ⟨α, hα⟩ := InnerSemi.exists_mulEquiv a hn
  obtain ⟨ψ, hψ, E, μ₀, hE, hμ₀⟩ :=
    CFSG.Quasithin.H13.L32A.C.SL3N.exists_semilinear_of_aut hf hF α
  have hEa : ∀ (g : SL(3, F)) (v : Fin 3 → F), (a.trans E) ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
      ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ (a.trans E) v := by
    intro g v
    show E (a _) = _ *ᵥ E (a v)
    rw [hα, hE]
  rcases hψ with rfl | rfl
  · obtain ⟨m, hm⟩ := CFSG.Quasithin.H13.L32A.C.SL3N.eq_smul_of_comm (a.trans E).toAddMonoidHom
      fun g v => hEa g v
    obtain ⟨θ, hθ⟩ := InnerSemi.exists_ringEquiv E μ₀ hμ₀
    refine ⟨θ.symm, fun c v => E.injective ?_⟩
    have h1 : E (a (c • v)) = m • c • v := hm (c • v)
    have h2 : E (a v) = m • v := hm v
    rw [h1, hθ, RingEquiv.apply_symm_apply, h2, smul_comm]
  · exact (InnerSemi.not_tauSL (a.trans E) hEa).elim

end CFSG.LocalAnalysis.RankThreeUC.S15
