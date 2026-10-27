module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeIndexLang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcRootTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three5

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  (a2ci_rootTorusSL2_mem_rootSpan)
open scoped Matrix MatrixGroups

section Certs


theorem exists_adjointGroup_of_mem_perfectFixed_e8 {K : Type} [Field K] [Finite K]
    {ℓ f : ℕ} [Fact ℓ.Prime] {L : Type} [Field L] [Algebra K L] [CharP L ℓ]
    (n : ModGL Tag.E8 L) (g0 : ModGL Tag.E8 L) (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E8 L), Finite P → P ≤ adjointGroup Tag.E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E8 K L).range)
    {P : Subgroup (ModGL Tag.E8 L)} (hPfin : Finite P) (hPadj : P ≤ adjointGroup Tag.E8 L)
    (hPfix : P ≤ twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (hPperf : ⁅P, P⁆ = P) {t : ModGL Tag.E8 L} (ht : t ∈ P) :
    ∃ x : adjointGroup Tag.E8 K, adjEmb Tag.E8 K L x = g0 * t * g0⁻¹ := by
  classical
  set P' : Subgroup (ModGL Tag.E8 L) := P.map (MulAut.conj g0).toMonoidHom with hP'def
  have hP'fin : Finite P' :=
    Finite.of_equiv ↥P (Subgroup.equivMapOfInjective P (MulAut.conj g0).toMonoidHom
      (MulAut.conj g0).injective).toEquiv
  have hP'adj : P' ≤ adjointGroup Tag.E8 L := by
    rintro _ ⟨y, hy, rfl⟩
    rw [show (MulAut.conj g0).toMonoidHom y = g0 * y * g0⁻¹ by simp [MulAut.conj_apply]]
    exact mul_mem (mul_mem hg0C (hPadj hy)) (inv_mem hg0C)
  have hP'fix : ∀ y ∈ P', Units.map (entrywiseHom (iterateFrobenius L ℓ f)) y = y := by
    rintro _ ⟨y, hy, rfl⟩
    have hyfix : n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) y * n⁻¹ = y :=
      mem_twistedFixedPoints.1 (hPfix hy)
    rw [show (MulAut.conj g0).toMonoidHom y = g0 * y * g0⁻¹ by simp [MulAut.conj_apply]]
    rw [map_mul, map_mul, map_inv, hg0]
    calc g0 * n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) y * (g0 * n)⁻¹
        = g0 * (n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) y * n⁻¹) * g0⁻¹ := by
          group
      _ = g0 * y * g0⁻¹ := by rw [hyfix]
  have hP'perf : ⁅P', P'⁆ = P' := by
    rw [hP'def, ← Subgroup.map_commutator, hPperf]
  have hrange : P' ≤ (adjEmb Tag.E8 K L).range := hperf P' hP'fin hP'adj hP'fix hP'perf
  have ht' : g0 * t * g0⁻¹ ∈ P' := by
    rw [hP'def]
    exact Subgroup.mem_map.mpr ⟨t, ht, by simp [MulAut.conj_apply]⟩
  obtain ⟨x, hx⟩ := hrange ht'
  exact ⟨x, hx⟩

@[expose] def e8T3BetaOne : Fin Tag.E8.rank → ℤ :=
  toVec Tag.E8.rank [0, 0, 0, 0, -1, 0, 0, 0]

@[expose] def e8T3BetaTwo : Fin Tag.E8.rank → ℤ :=
  toVec Tag.E8.rank [-2, -3, -4, -6, -5, -3, -2, -1]

@[expose] def e8T3GammaOne : Fin Tag.E8.rank → ℤ :=
  toVec Tag.E8.rank [1, 1, 2, 2, 2, 2, 2, 1]

@[expose] def e8T3GammaTwo : Fin Tag.E8.rank → ℤ :=
  toVec Tag.E8.rank [0, 0, 0, 0, 0, 0, 1, 1]

@[expose] def e8T3YColumn {p : ℕ} (ε : ℤ) (q : ZMod p) : Fin Tag.E8.rank → ZMod p :=
  fun k => (ExceptionalCover.cartanCoord e8T3GammaOne k : ZMod p) +
    ((ε : ZMod p) * q) * (ExceptionalCover.cartanCoord e8T3GammaTwo k : ZMod p)

theorem isRoot_e8T3BetaOne : IsRoot Tag.E8 e8T3BetaOne := isRoot_toVec (by decide +kernel)

theorem isRoot_e8T3BetaTwo : IsRoot Tag.E8 e8T3BetaTwo := isRoot_toVec (by decide +kernel)

theorem isRoot_e8T3GammaOne : IsRoot Tag.E8 e8T3GammaOne := isRoot_toVec (by decide +kernel)

theorem isRoot_e8T3GammaTwo : IsRoot Tag.E8 e8T3GammaTwo := isRoot_toVec (by decide +kernel)

theorem cartanCoord_e8T3BetaOne :
    ExceptionalCover.cartanCoord e8T3BetaOne = e8T3XAVec := by decide +kernel

theorem cartanCoord_e8T3BetaTwo :
    ExceptionalCover.cartanCoord e8T3BetaTwo = e8T3XDVec := by decide +kernel

theorem cartanCoord_e8T3GammaOne :
    ExceptionalCover.cartanCoord e8T3GammaOne = e8T3ZAVec - e8T3XAVec := by decide +kernel

theorem cartanCoord_e8T3GammaTwo :
    ExceptionalCover.cartanCoord e8T3GammaTwo = e8T3ZDVec - e8T3XDVec := by decide +kernel

private theorem rootDiagUnit_zetaPow_mul_coroot {L : Type} [Field L] {p : ℕ} [NeZero p]
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) {z : Fin Tag.E8.rank → ZMod p}
    {β₁ β₂ : Fin Tag.E8.rank → ℤ} (hβ₁ : IsRoot Tag.E8 β₁) (hβ₂ : IsRoot Tag.E8 β₂) {e : ℤ}
    (hcol : ∀ k, z k = (ExceptionalCover.cartanCoord β₁ k : ZMod p) +
      (e : ZMod p) * (ExceptionalCover.cartanCoord β₂ k : ZMod p)) :
    rootDiagUnit Tag.E8 (fun k => ζ ^ (z k).val) =
      rootTorusSL2 Tag.E8 L β₁ ζ * rootTorusSL2 Tag.E8 L β₂ (ζ ^ e) := by
  have hfun : (fun k => ζ ^ (z k).val) =
      fun k => ζ ^ (ExceptionalCover.cartanCoord β₁ k +
        e * ExceptionalCover.cartanCoord β₂ k) := by
    funext k
    rw [← zpow_natCast ζ (z k).val, zpow_eq_zpow_iff_modEq]
    have hmod : ((z k).val : ℤ) ≡ ExceptionalCover.cartanCoord β₁ k +
        e * ExceptionalCover.cartanCoord β₂ k [ZMOD p] := by
      refine (ZMod.intCast_eq_intCast_iff _ _ p).1 ?_
      push_cast
      rw [ZMod.natCast_zmod_val, hcol k]
    simpa only [hζ.eq_orderOf] using hmod
  rw [hfun]
  have hsplit : rootDiagUnit Tag.E8
      (fun k => ζ ^ (ExceptionalCover.cartanCoord β₁ k +
        e * ExceptionalCover.cartanCoord β₂ k)) =
      rootDiagUnit Tag.E8 (fun k => ζ ^ ExceptionalCover.cartanCoord β₁ k) *
        rootDiagUnit Tag.E8 (fun k => ζ ^ (e * ExceptionalCover.cartanCoord β₂ k)) := by
    rw [← rootDiagUnit_mul]
    congr 1
    funext k
    simp only [Pi.mul_apply, _root_.zpow_add]
  rw [hsplit]
  have h1 : rootDiagUnit Tag.E8 (fun k => ζ ^ ExceptionalCover.cartanCoord β₁ k) =
      rootTorusSL2 Tag.E8 L β₁ ζ :=
    (rootTorusSL2_eq_rootDiagUnit_cartanCoord (τ := Tag.E8) rfl hβ₁ ζ).symm
  have h2 : rootDiagUnit Tag.E8 (fun k => ζ ^ (e * ExceptionalCover.cartanCoord β₂ k)) =
      rootTorusSL2 Tag.E8 L β₂ (ζ ^ e) := by
    rw [rootTorusSL2_eq_rootDiagUnit_cartanCoord (τ := Tag.E8) rfl hβ₂]
    congr 1
    funext k
    rw [_root_.zpow_mul]
  rw [h1, h2]

theorem rootDiagUnit_e8T3XColumn_eq_mul {L : Type} [Field L] {p : ℕ} [NeZero p] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) {ε : ℤ} {q : ZMod p} {e : ℤ}
    (he : (e : ZMod p) = (ε : ZMod p) * q) :
    rootDiagUnit Tag.E8 (fun k => ζ ^ (e8T3XColumn ε q k).val) =
      rootTorusSL2 Tag.E8 L e8T3BetaOne ζ * rootTorusSL2 Tag.E8 L e8T3BetaTwo (ζ ^ e) := by
  refine rootDiagUnit_zetaPow_mul_coroot (p := p) hζ isRoot_e8T3BetaOne isRoot_e8T3BetaTwo
    (e := e) ?_
  intro k
  have hz : e8T3XColumn ε q k =
      (e8T3XAVec k : ZMod p) + (ε : ZMod p) * q * (e8T3XDVec k : ZMod p) := by
    simp only [e8T3XColumn, e8T3XAVec, e8T3XDVec, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
      Pi.single_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  rw [hz, ← he, ← cartanCoord_e8T3BetaOne, ← cartanCoord_e8T3BetaTwo]

theorem rootDiagUnit_e8T3YColumn_eq_mul {L : Type} [Field L] {p : ℕ} [NeZero p] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) {ε : ℤ} {q : ZMod p} {e : ℤ}
    (he : (e : ZMod p) = (ε : ZMod p) * q) :
    rootDiagUnit Tag.E8 (fun k => ζ ^ (e8T3YColumn ε q k).val) =
      rootTorusSL2 Tag.E8 L e8T3GammaOne ζ * rootTorusSL2 Tag.E8 L e8T3GammaTwo (ζ ^ e) := by
  refine rootDiagUnit_zetaPow_mul_coroot (p := p) hζ isRoot_e8T3GammaOne isRoot_e8T3GammaTwo
    (e := e) ?_
  intro k
  have hz : e8T3YColumn ε q k =
      (ExceptionalCover.cartanCoord e8T3GammaOne k : ZMod p) +
        (ε : ZMod p) * q * (ExceptionalCover.cartanCoord e8T3GammaTwo k : ZMod p) := rfl
  rw [hz, ← he]

theorem rootDiagUnit_e8T3XColumn_mem_rootSpan {L : Type} [Field L] {p : ℕ} [NeZero p] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) {ε : ℤ} {q : ZMod p} {e : ℤ}
    (he : (e : ZMod p) = (ε : ZMod p) * q) {S : Set (Fin Tag.E8.rank → ℤ)}
    (h₁ : e8T3BetaOne ∈ S) (h₁' : -e8T3BetaOne ∈ S)
    (h₂ : e8T3BetaTwo ∈ S) (h₂' : -e8T3BetaTwo ∈ S) :
    rootDiagUnit Tag.E8 (fun k => ζ ^ (e8T3XColumn ε q k).val) ∈ rootSpan Tag.E8 L S := by
  rw [rootDiagUnit_e8T3XColumn_eq_mul hζ he]
  exact mul_mem
    (a2ci_rootTorusSL2_mem_rootSpan isRoot_e8T3BetaOne h₁ h₁' ζ)
    (a2ci_rootTorusSL2_mem_rootSpan isRoot_e8T3BetaTwo h₂ h₂' _)

theorem rootDiagUnit_e8T3YColumn_mem_rootSpan {L : Type} [Field L] {p : ℕ} [NeZero p] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) {ε : ℤ} {q : ZMod p} {e : ℤ}
    (he : (e : ZMod p) = (ε : ZMod p) * q) {S : Set (Fin Tag.E8.rank → ℤ)}
    (h₁ : e8T3GammaOne ∈ S) (h₁' : -e8T3GammaOne ∈ S)
    (h₂ : e8T3GammaTwo ∈ S) (h₂' : -e8T3GammaTwo ∈ S) :
    rootDiagUnit Tag.E8 (fun k => ζ ^ (e8T3YColumn ε q k).val) ∈ rootSpan Tag.E8 L S := by
  rw [rootDiagUnit_e8T3YColumn_eq_mul hζ he]
  exact mul_mem
    (a2ci_rootTorusSL2_mem_rootSpan isRoot_e8T3GammaOne h₁ h₁' ζ)
    (a2ci_rootTorusSL2_mem_rootSpan isRoot_e8T3GammaTwo h₂ h₂' _)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
