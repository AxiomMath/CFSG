module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSingerActionLinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSingerActionSuzuki
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSingerActionUnitary

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ShultStronglyClosedTI.SuzukiModel

theorem singerAction_of_central_odd_cover_psl2 {L : Type*} [Group L] [Finite L]
    (C : Subgroup L) [C.Normal] (hC : C ≤ Subgroup.center L) (hCodd : Odd (Nat.card C))
    (R : Sylow 2 L) {f : ℕ} (hf : f ≠ 0) (E : L ⧸ C ≃* PSL2BinaryMatrixGroup f) :
    let U := Subgroup.closure {x | x ∈ (R : Subgroup L) ∧ orderOf x = 2}
    IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ f ∧ IsCyclic U.normalizerMonoidHom.range ∧
      Nat.card U.normalizerMonoidHom.range = 2 ^ f - 1 ∧
      (∀ x y : U, x ≠ 1 → y ≠ 1 →
        ∃! σ : U.normalizerMonoidHom.range, (σ : MulAut U) x = y) ∧
      ∃ (F : Type) (_ : Field F), Nat.card F = 2 ^ f ∧ ∃ e : Additive U ≃+ F,
        ∀ σ : MulAut U, σ ∈ U.normalizerMonoidHom.range ↔
          ∃ c : Fˣ, ∀ x : U, e (Additive.ofMul (σ x)) = c * e (Additive.ofMul x) :=
  (isSingerAction_of_central_odd_quotient C hC hCodd E
    (isSingerAction_psl2 hf (GaloisField.card 2 f hf)) R).conclusion hf

theorem singerAction_of_central_odd_cover_suzuki
    {L : Type*} [Group L] [Finite L]
    (C : Subgroup L) [C.Normal] (hC : C ≤ Subgroup.center L) (hCodd : Odd (Nat.card C))
    (R : Sylow 2 L) {m : ℕ} (E : L ⧸ C ≃* SuzukiMatrixGroup m) :
    let U := Subgroup.closure {x | x ∈ (R : Subgroup L) ∧ orderOf x = 2}
    IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (2 * m + 1) ∧
      IsCyclic U.normalizerMonoidHom.range ∧
      Nat.card U.normalizerMonoidHom.range = 2 ^ (2 * m + 1) - 1 ∧
      (∀ x y : U, x ≠ 1 → y ≠ 1 →
        ∃! σ : U.normalizerMonoidHom.range, (σ : MulAut U) x = y) ∧
      ∃ (F : Type) (_ : Field F), Nat.card F = 2 ^ (2 * m + 1) ∧ ∃ e : Additive U ≃+ F,
        ∀ σ : MulAut U, σ ∈ U.normalizerMonoidHom.range ↔
          ∃ c : Fˣ, ∀ x : U, e (Additive.ofMul (σ x)) = c * e (Additive.ofMul x) :=
  have hK : Nat.card (BinaryGaloisField (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 (2 * m + 1) (by omega)
  (isSingerAction_of_central_odd_quotient C hC hCodd
    (E.trans (suzukiGroupEquivSuzukiMatrixGroup hK).symm)
    (isSingerAction_suzukiGroup hK) R).conclusion (by omega)

theorem singerAction_of_central_odd_cover_unitary {L : Type*} [Group L] [Finite L]
    (C : Subgroup L) [C.Normal] (hC : C ≤ Subgroup.center L) (hCodd : Odd (Nat.card C))
    (R : Sylow 2 L) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (A : HermitianForm 3 K) (hA : A.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // A.conj x = x} = 2 ^ f)
    (E : L ⧸ C ≃* ProjectiveSpecialUnitaryMatrixGroup A) :
    let U := Subgroup.closure {x | x ∈ (R : Subgroup L) ∧ orderOf x = 2}
    IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ f ∧ IsCyclic U.normalizerMonoidHom.range ∧
      Nat.card U.normalizerMonoidHom.range = 2 ^ f - 1 ∧
      (∀ x y : U, x ≠ 1 → y ≠ 1 →
        ∃! σ : U.normalizerMonoidHom.range, (σ : MulAut U) x = y) ∧
      ∃ (F : Type) (_ : Field F), Nat.card F = 2 ^ f ∧ ∃ e : Additive U ≃+ F,
        ∀ σ : MulAut U, σ ∈ U.normalizerMonoidHom.range ↔
          ∃ c : Fˣ, ∀ x : U, e (Additive.ofMul (σ x)) = c * e (Additive.ofMul x) :=
  (isSingerAction_of_central_odd_quotient C hC hCodd E
    (isSingerAction_unitary A f hf hcard hfixed hA) R).conclusion (by omega)

theorem even_rank_one_central_odd_cover_involution_normalizer_singer_action
    {L : Type*} [Group L] [Finite L] (C : Subgroup L) [C.Normal]
    (hC : C ≤ Subgroup.center L) (hCodd : Odd (Nat.card C)) (R : Sylow 2 L) (q : ℕ)
    (hmodel : (∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧ Nonempty (L ⧸ C ≃* PSL2BinaryMatrixGroup f)) ∨
      (∃ m : ℕ, 1 ≤ m ∧ q = 2 ^ (2 * m + 1) ∧ Nonempty (L ⧸ C ≃* SuzukiMatrixGroup m)) ∨
      (∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
        (A : HermitianForm 3 K), A.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
          Nat.card K = q ^ 2 ∧ Nat.card {x : K // A.conj x = x} = q ∧
          Nonempty (L ⧸ C ≃* ProjectiveSpecialUnitaryMatrixGroup A))) :
    let U := Subgroup.closure {x | x ∈ (R : Subgroup L) ∧ orderOf x = 2}
    IsElementaryAbelian 2 U ∧ Nat.card U = q ∧ IsCyclic U.normalizerMonoidHom.range ∧
      Nat.card U.normalizerMonoidHom.range = q - 1 ∧
      (∀ x y : U, x ≠ 1 → y ≠ 1 →
        ∃! σ : U.normalizerMonoidHom.range, (σ : MulAut U) x = y) ∧
      ∃ (F : Type) (_ : Field F), Nat.card F = q ∧ ∃ e : Additive U ≃+ F,
        ∀ σ : MulAut U, σ ∈ U.normalizerMonoidHom.range ↔
          ∃ c : Fˣ, ∀ x : U, e (Additive.ofMul (σ x)) = c * e (Additive.ofMul x) := by
  rcases hmodel with ⟨f, hf, rfl, ⟨E⟩⟩ | ⟨m, -, rfl, ⟨E⟩⟩ |
      ⟨f, hf, rfl, K, _, _, A, hA, hcard, hfixed, ⟨E⟩⟩
  · exact singerAction_of_central_odd_cover_psl2 C hC hCodd R (by omega) E
  · exact singerAction_of_central_odd_cover_suzuki C hC hCodd R E
  · exact singerAction_of_central_odd_cover_unitary C hC hCodd R hf A hA hcard hfixed E

end CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger
