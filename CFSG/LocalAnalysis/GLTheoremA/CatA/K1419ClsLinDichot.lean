module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsLinBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsLinCentral
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI Matrix

theorem k1419ClsLinDichot {F : Type} [Field F] [Finite F] (h2 : (2 : F) = 0) {n : ℕ} (hn : 1 ≤ n)
    (A : GL (Fin n) F)
    (hA3 : ∃ c : F, ((A ^ 3 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      c • (1 : Matrix (Fin n) (Fin n) F))
    (hAns : ∀ c : F, (A : Matrix (Fin n) (Fin n) F) ≠ c • (1 : Matrix (Fin n) (Fin n) F))
    (M : Subgroup (GL (Fin n) F))
    (hM : IsComponentOf M (Subgroup.centralizer ({A} : Set (GL (Fin n) F)) ⊓ StatedSL n F)) :
    ∃ (a : ℕ) (E : Type) (_ : Field E) (_ : Algebra F E) (_ : Finite E), 2 ≤ a ∧
      Nonempty (M ⧸ Subgroup.center M ≃* StatedProj (StatedSL a E)) ∧
      (3 ∣ Module.finrank F E ∨
        ((3 ∣ a ∧ 3 ∣ Nat.card E - 1) →
          ∃ z : GL (Fin n) F, z ∈ M ∧ z ≠ 1 ∧ z ^ 3 = 1 ∧ (∀ y ∈ M, z * y = y * z) ∧
            z ∉ StatedScalars (Fin n) F)) := by
  obtain ⟨c, hc⟩ := hA3
  have hodd : Odd (orderOf A) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.odd_orderOf_of_pow_scalar h2 hn A
      (by norm_num : Odd 3) hc
  have hord : ((orderOf A : ℕ) : F) ≠ 0 :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.cast_orderOf_ne_zero_of_odd h2 A hodd
  obtain ⟨r, D, d, hFld, hFin, hAlg, Φ, θ, hd, hΦ, hθ, hθA, hθΦ, i, hi, hMeq⟩ :=
    k1419ClsLinBlock_exists A hord M hM
  letI : ∀ i, Field (D i) := hFld
  letI : ∀ i, Finite (D i) := hFin
  letI : ∀ i, Algebra F (D i) := hAlg
  have hms : Function.Injective
      (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) := by
    intro a b hab
    have := congrFun hab i
    simpa [MonoidHom.mulSingle_apply] using this
  have eJ : ↥M ≃* ↥(StatedSL (d i) (D i)) :=
    (MulEquiv.subgroupCongr hMeq).trans
      ((Subgroup.equivMapOfInjective _ θ hθ).symm.trans
        (Subgroup.equivMapOfInjective (StatedSL (d i) (D i))
          (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i) hms).symm)
  refine ⟨d i, D i, hFld i, hAlg i, hFin i, hi,
    CFSG.LieType.SemisimpleCentralizers.Held.nonempty_quotientCenter_equiv_statedProj eJ, ?_⟩
  exact k1419ClsLinCentral Φ θ hd hΦ hθ hθΦ A hθA ⟨c, hc⟩ hAns i hi M hMeq

end CFSG.LocalAnalysis.GLTheoremA.K1419
