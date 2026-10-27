module

public import CFSG.RankThree.PartOne.KE.E7ThreeFrame

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

section Descent


theorem exists_adjointGroup_of_mem_perfectFixed {K : Type} [Field K] [Finite K]
    {ℓ f p : ℕ} [Fact ℓ.Prime] {L : Type} [Field L] [Algebra K L] [CharP L ℓ] {ε : ℤ}
    (F : E7ThreeFrame K L ℓ f p ε) {P : Subgroup (ModGL Tag.E7 L)} (hPfin : Finite P)
    (hPadj : P ≤ adjointGroup Tag.E7 L)
    (hPfix : P ≤ twistedFixedPoints F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (hPperf : ⁅P, P⁆ = P) {t : ModGL Tag.E7 L} (ht : t ∈ P) :
    ∃ x : adjointGroup Tag.E7 K, adjEmb Tag.E7 K L x = F.g0 * t * F.g0⁻¹ := by
  classical
  set P' : Subgroup (ModGL Tag.E7 L) := P.map (MulAut.conj F.g0).toMonoidHom with hP'def
  have hP'fin : Finite P' :=
    Finite.of_equiv ↥P (Subgroup.equivMapOfInjective P (MulAut.conj F.g0).toMonoidHom
      (MulAut.conj F.g0).injective).toEquiv
  have hP'adj : P' ≤ adjointGroup Tag.E7 L := by
    rintro _ ⟨y, hy, rfl⟩
    rw [show (MulAut.conj F.g0).toMonoidHom y = F.g0 * y * F.g0⁻¹ by
      simp [MulAut.conj_apply]]
    exact mul_mem (mul_mem F.hg0C (hPadj hy)) (inv_mem F.hg0C)
  have hP'fix : ∀ y ∈ P', Units.map (entrywiseHom (iterateFrobenius L ℓ f)) y = y := by
    rintro _ ⟨y, hy, rfl⟩
    have hyfix : F.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) y * F.n⁻¹ = y :=
      mem_twistedFixedPoints.1 (hPfix hy)
    rw [show (MulAut.conj F.g0).toMonoidHom y = F.g0 * y * F.g0⁻¹ by
      simp [MulAut.conj_apply]]
    rw [map_mul, map_mul, map_inv, F.hg0]
    calc F.g0 * F.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) y * (F.g0 * F.n)⁻¹
        = F.g0 * (F.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) y * F.n⁻¹) *
            F.g0⁻¹ := by group
      _ = F.g0 * y * F.g0⁻¹ := by rw [hyfix]
  have hP'perf : ⁅P', P'⁆ = P' := by
    rw [hP'def, ← Subgroup.map_commutator, hPperf]
  have hrange : P' ≤ (adjEmb Tag.E7 K L).range := F.hperf P' hP'fin hP'adj hP'fix hP'perf
  have ht' : F.g0 * t * F.g0⁻¹ ∈ P' := by
    rw [hP'def]
    exact Subgroup.mem_map.mpr ⟨t, ht, by simp [MulAut.conj_apply]⟩
  obtain ⟨x, hx⟩ := hrange ht'
  exact ⟨x, hx⟩

end Descent

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
