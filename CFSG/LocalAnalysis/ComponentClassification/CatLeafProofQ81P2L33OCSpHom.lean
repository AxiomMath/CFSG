module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2Base
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CHom
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareModel
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.OC

open CFSG Subgroup Matrix Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare QuaternionMatrices
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher FourGroupOddUnitary

theorem odd_closure_image {G P : Type*} [Group G] [Group P] (θ : G →* P) {S : Set G}
    (hS : closure S = ⊤) (hSo : ∀ s ∈ S, Odd (orderOf s)) {x : G} (hx4 : x ^ 4 = 1)
    (hx1 : θ x ≠ 1) :
    (∀ t ∈ θ '' S, Odd (orderOf t)) ∧ 2 ∣ Nat.card (closure (θ '' S)) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact Odd.of_dvd_nat (hSo s hs) (orderOf_map_dvd θ s)
  · have hcl : closure (θ '' S) = θ.range := by
      rw [← MonoidHom.map_closure, hS, MonoidHom.range_eq_map]
    rw [hcl]
    have h4 : θ x ^ 4 = 1 := by rw [← map_pow, hx4, map_one]
    have h2 : 2 ∣ orderOf (θ x) := by
      have hpos : orderOf (θ x) ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.1 h)
      rcases (Nat.dvd_prime_pow Nat.prime_two).1
          (show orderOf (θ x) ∣ 2 ^ 2 from orderOf_dvd_of_pow_eq_one h4) with ⟨k, hk, hk'⟩
      interval_cases k
      · exact absurd (by rw [hk']; rfl) hpos
      · rw [hk']; exact ⟨1, rfl⟩
      · rw [hk']; exact ⟨2, rfl⟩
    exact CatLeafProof.Q81P2.two_dvd_card_range θ rfl h2

theorem elementary_closure_odd {K : Type*} [Field K] [Finite K] (hK : ringChar K ≠ 2) (m : ℕ) :
    closure (LinearGroups.elementarySet m K) = ⊤ ∧
      ∀ s ∈ LinearGroups.elementarySet m K, Odd (orderOf s) := by
  have hpr : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  exact ⟨LinearGroups.special_linear_elementary_generation,
    fun s hs => GSThmB.Cent516.odd_orderOf_of_mem_elementarySet hpr hK hs⟩

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]

theorem exists_sl2_sp [FiniteDimensional F W] [Nontrivial W] (B : LinearMap.BilinForm F W)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    ∃ ψ : SpecialLinearGroup (Fin 2) F →* LinearMap.GeneralLinearGroup F W,
      (∀ X, ψ X ∈ sesqUnitaryGroup B) ∧ ψ (-1) = -1 ∧
        ∀ a : F, (ψ (slQuatI F) : Module.End F W) ≠ a • 1 := by
  obtain ⟨m, c, hdim, hc⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis B hB hnd
  have hm : 0 < m := by
    have := Module.finrank_pos (R := F) (M := W)
    omega
  have hG : ∀ k l, B (c k) (c l) = J (Fin m) F k l := fun k l => by
    rw [← hc, LinearMap.BilinForm.toMatrix_apply]
  let q := Units.map (quatHomEnd c)
  have hq : ∀ M : GL (Fin 2) F, ((q M : LinearMap.GeneralLinearGroup F W) : Module.End F W) =
      Matrix.toLin c c (quatBlock (M : Matrix (Fin 2) (Fin 2) F)) := fun _ => rfl
  refine ⟨q.comp SpecialLinearGroup.toGL, fun M x y => ?_, ?_, fun r h => ?_⟩
  · change B ((q (SpecialLinearGroup.toGL M) : Module.End F W) x)
      ((q (SpecialLinearGroup.toGL M) : Module.End F W) y) = B x y
    rw [hq]
    exact toLin_preserves B c (J (Fin m) F) hG (fun _ _ => rfl)
      (by rw [quatBlock_J]; change (M : Matrix (Fin 2) (Fin 2) F).det • _ = _
          rw [M.prop, one_smul]) x y
  · have h1 : SpecialLinearGroup.toGL (-1 : SpecialLinearGroup (Fin 2) F) = -1 :=
      Units.ext (by rw [SpecialLinearGroup.coe_GL_coe_matrix]; simp)
    change q (SpecialLinearGroup.toGL (-1)) = -1
    rw [h1]
    refine Units.ext ?_
    rw [hq, Units.val_neg, Units.val_one, Units.val_neg, Units.val_one,
      show (-1 : Matrix (Fin 2) (Fin 2) F) = (-1 : F) • 1 by rw [neg_one_smul], quatBlock_smul,
      quatBlock_one, map_smul, Matrix.toLin_one, neg_one_smul]
    rfl
  · have h' : Matrix.toLin c c (quatBlock (quatI F)) = r • (1 : Module.End F W) := by
      rw [← h]
      rfl
    have h2 := eq_of_quatBlock_eq_smul hm (toLin_eq_smul_id c (by rw [h']; rfl))
    have := congrFun (congrFun h2 0) 1
    simp [quatI] at this

end CFSG.ComponentClassification.HarrisLit.L33.OC
