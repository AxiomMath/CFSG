module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three7
public import CFSG.RankThree.PartOne.KE.E7ThreeFrame

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix


theorem mem_fixedCharTuples_e7T3XTuple {p : ℕ} [NeZero p] {L : Type} [Field L]
    {Fr : L →+* L} {q₀ : ℕ} (hFr : ∀ c, Fr c = c ^ q₀) {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hq : (q₀ : ZMod p) ^ 2 + (ε : ZMod p) * (q₀ : ZMod p) + 1 = 0) :
    (fun i => ζ ^ (e7T3XColumn ε (q₀ : ZMod p) i).val) ∈ fixedCharTuples (ε • e7T3W) Fr := by
  rw [e7T3_mem_fixed_iff_ker hFr,
    CFSG.RankThree.Classical2.zetaPow_mem_ker_monomialHom_iff hζ]
  have hmap : (((Matrix.scalar (Fin Tag.E7.rank) (q₀ : ℤ) - ε • e7T3W)).transpose).map
      (Int.cast : ℤ → ZMod p) =
      Matrix.scalar (Fin Tag.E7.rank) (q₀ : ZMod p) -
        ((ε • e7T3W).map (Int.cast : ℤ → ZMod p)).transpose := by
    ext i j
    simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.transpose_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul,
      Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  have hsmul : (Matrix.scalar (Fin Tag.E7.rank) (q₀ : ZMod p)) *ᵥ
      e7T3XColumn ε (q₀ : ZMod p) = (q₀ : ZMod p) • e7T3XColumn ε (q₀ : ZMod p) := by
    ext i
    rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [hmap, Matrix.sub_mulVec, hsmul, e7T3XColumn_eigen hε hq, sub_self]

theorem rootDiagUnit_mem_twistedTorus_e7T3XTuple {K : Type} [Field K] [Finite K]
    {ℓ f p : ℕ} [Fact ℓ.Prime] [NeZero p] {L : Type} [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L ℓ] {ε : ℤ} (F : E7ThreeFrame K L ℓ f p ε)
    (hK : Nat.card K = ℓ ^ f)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) (hε : ε = 1 ∨ ε = -1)
    (hq : (Nat.card K : ZMod p) ^ 2 + (ε : ZMod p) * (Nat.card K : ZMod p) + 1 = 0) :
    rootDiagUnit .E7 (fun i => ζ ^ (e7T3XColumn ε (Nat.card K : ZMod p) i).val) ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ Nat.card K := by
    intro c
    rw [iterateFrobenius_def, hK]
  rw [F.hT]
  exact Subgroup.mem_map_of_mem (rootDiagUnitHom .E7 L)
    (mem_fixedCharTuples_e7T3XTuple hFr hζ hε hq)

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
