module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin7

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open

namespace LinEngine

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {p : ℕ}
variable [Finite (SpecialLinearGroup F V)]

theorem exists_elemAbelian_q_Jsub_of_split [Fintype F]
    (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : HypBlocks.Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Fintype.card F - 1)
    (D : HypBlocks.Hyperplane A p)
    (hdim : 4 ≤ Module.finrank F
      ↥(HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht D))) :
    ∃ Q : Subgroup (SpecialLinearGroup F V),
      Q ≤ Jsub A hp hpF hA t ht D ∧ IsElemAbelian q Q ∧ 3 ≤ CFSG.Open.pRank q Q := by
  classical
  haveI : Fintype V := by
    haveI : Module.Free F V := Module.Free.of_divisionRing F V
    exact Fintype.ofEquiv (Fin (Module.finrank F V) → F)
      (Module.finBasis F V).equivFun.symm.toEquiv
  let W : Submodule F V := HypBlocks.fixedByEnd (HypBlocks.blockEnd A hp hpF hA t ht D)
  have hWfree : Module.Free F W := Module.Free.of_divisionRing F W
  have hWfin : Module.Finite F W := Module.Finite.of_injective (Submodule.subtype W)
    Subtype.val_injective
  have hK : 4 ≤ Module.finrank F W := hdim
  have hK1 : Module.finrank F W = (Module.finrank F W - 1) + 1 := by omega
  let b : Module.Basis (Fin ((Module.finrank F W - 1) + 1)) F W :=
    (Module.finBasis F W).reindex (finCongr hK1)
  let e₁ : Matrix.SpecialLinearGroup (Fin ((Module.finrank F W - 1) + 1)) F ≃*
      SpecialLinearGroup F W := Matrix.SpecialLinearGroup.toLin_equiv b
  let e₂ : ↥(Jsub A hp hpF hA t ht D) ≃* SpecialLinearGroup F W :=
    JsubEquiv A hp hpF hA t ht D
  let ψ : Matrix.SpecialLinearGroup (Fin ((Module.finrank F W - 1) + 1)) F →*
      ↥(Jsub A hp hpF hA t ht D) := e₂.symm.toMonoidHom.comp e₁.toMonoidHom
  let Φ : Matrix.SpecialLinearGroup (Fin ((Module.finrank F W - 1) + 1)) F →*
      SpecialLinearGroup F V := (Jsub A hp hpF hA t ht D).subtype.comp ψ
  refine ⟨(diagSLSub (F := F) (Module.finrank F W - 1) q).map Φ, ?_, ?_, ?_⟩
  ·
    rintro x ⟨y, -, rfl⟩
    exact (ψ y).2
  ·
    exact CFSG.SectionRank.isElemAbelian_map (isElemAbelian_diagSLSub (F := F)) Φ
  ·
    have hfinj : Function.Injective Φ := by
      intro x y hxy
      have h1 : ψ x = ψ y := Subtype.ext hxy
      have h2 : e₁ x = e₁ y := e₂.symm.injective h1
      exact e₁.injective h2
    have hpq : 1 < q := hq.one_lt
    have hrank := CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective
      (G := SpecialLinearGroup F V) hpq Φ hfinj
      (diagSLSub (F := F) (Module.finrank F W - 1) q)
    rw [hrank]
    refine three_le_pRank_diagSLSub (F := F) hq ?_ (by omega)
    rwa [Nat.card_eq_fintype_card]

end LinEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
