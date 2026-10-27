module

public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem mem_range_of_baseChangeGL_mem_range
    {τ : Tag} {K L : Type} [Field K]
    [Field L] (f : K →+* L) (σ : L →+* L) (hσf : σ.comp f = f)
    (hfix : ∀ c : L, σ c = c → c ∈ f.range)
    (ψK : Matrix.SpecialLinearGroup (Fin 3) K →* ModGL τ K)
    (ψL : Matrix.SpecialLinearGroup (Fin 3) L →* ModGL τ L)
    (hKL : ∀ A, ψL (Matrix.SpecialLinearGroup.map f A) = baseChangeGL f (ψK A))
    (hLL : ∀ A, ψL (Matrix.SpecialLinearGroup.map σ A) = baseChangeGL σ (ψL A))
    (hinj : Function.Injective ψL) {x : ModGL τ K}
    (hx : baseChangeGL f x ∈ ψL.range) : x ∈ ψK.range := by
  obtain ⟨y, hy⟩ := hx
  have hyσ : Matrix.SpecialLinearGroup.map σ y = y := by
    apply hinj
    rw [hLL, hy, baseChangeGL_baseChangeGL f σ x, hσf]
  have hent : ∀ i j, ∃ c : K, f c = (y : Matrix (Fin 3) (Fin 3) L) i j := by
    intro i j
    have h := congrArg
      (fun z : Matrix.SpecialLinearGroup (Fin 3) L => (z : Matrix (Fin 3) (Fin 3) L) i j) hyσ
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at h
    obtain ⟨c, hc⟩ := hfix _ h
    exact ⟨c, hc⟩
  choose c hc using hent
  have hA0 : (Matrix.of c).map f = (y : Matrix (Fin 3) (Fin 3) L) := by
    ext i j
    exact hc i j
  have hdet : (Matrix.of c).det = 1 := by
    apply f.injective
    rw [RingHom.map_det, map_one]
    change ((Matrix.of c).map f).det = 1
    rw [hA0]
    exact y.2
  let A : Matrix.SpecialLinearGroup (Fin 3) K := ⟨Matrix.of c, hdet⟩
  have hAy : Matrix.SpecialLinearGroup.map f A = y :=
    Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      exact hA0)
  refine ⟨A, baseChangeGL_injective (f := f) ?_⟩
  rw [← hKL, hAy, hy]

end CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
