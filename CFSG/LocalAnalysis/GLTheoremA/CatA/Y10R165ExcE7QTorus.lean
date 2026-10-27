module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbedding.RankLemmas
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin2
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.RankThree.PartTwo.Census.Carrier.TitsCert

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Open CFSG.RankThree.Classical2 CFSG.RankThree.PartTwo.Census
open scoped MatrixGroups Pointwise

section Split

variable {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L]

noncomputable def splitModelHom {Φ' : SL(6, L) ≃* SL(6, L)} {H : SL(6, L)}
    (hfix : ∀ X : SL(6, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y : SL(6, K), X = H * Matrix.SpecialLinearGroup.map (algebraMap K L) Y * H⁻¹) :
    SL(6, K) →* ↥(fixSubgroup Φ') where
  toFun Y := ⟨H * Matrix.SpecialLinearGroup.map (algebraMap K L) Y * H⁻¹, (hfix _).2 ⟨Y, rfl⟩⟩
  map_one' := Subtype.ext (by simp)
  map_mul' Y Z := Subtype.ext (by
    simp only [Subtype.coe_mk, Subgroup.coe_mul, map_mul]
    group)

omit [Finite K] in
theorem splitModelHom_injective {Φ' : SL(6, L) ≃* SL(6, L)} {H : SL(6, L)}
    (hfix : ∀ X : SL(6, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y : SL(6, K), X = H * Matrix.SpecialLinearGroup.map (algebraMap K L) Y * H⁻¹) :
    Function.Injective (splitModelHom hfix) := by
  intro Y Z hYZ
  have h := congrArg (fun t : ↥(fixSubgroup Φ') => (t : SL(6, L))) hYZ
  change H * Matrix.SpecialLinearGroup.map (algebraMap K L) Y * H⁻¹ =
    H * Matrix.SpecialLinearGroup.map (algebraMap K L) Z * H⁻¹ at h
  refine CFSG.RankThree.Classical2.specialLinearGroup_map_injective (n := 6)
    (RingHom.injective (algebraMap K L)) ?_
  have h2 := congrArg (fun t : SL(6, L) => H⁻¹ * t * H) h
  simpa [mul_assoc] using h2

omit [Finite K] in
private theorem splitModelHom_surjective {Φ' : SL(6, L) ≃* SL(6, L)} {H : SL(6, L)}
    (hfix : ∀ X : SL(6, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y : SL(6, K), X = H * Matrix.SpecialLinearGroup.map (algebraMap K L) Y * H⁻¹) :
    Function.Surjective (splitModelHom hfix) := by
  intro X
  obtain ⟨Y, hY⟩ := (hfix X).1 X.2
  exact ⟨Y, Subtype.ext hY.symm⟩

private theorem splitModel_finite {Φ' : SL(6, L) ≃* SL(6, L)} {H : SL(6, L)}
    (hfix : ∀ X : SL(6, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y : SL(6, K), X = H * Matrix.SpecialLinearGroup.map (algebraMap K L) Y * H⁻¹) :
    Finite ↥(fixSubgroup Φ') :=
  Finite.of_surjective (splitModelHom hfix) (splitModelHom_surjective hfix)

theorem exists_elemAbelian_pRank_three_of_fixSubgroup_split
    {Φ' : SL(6, L) ≃* SL(6, L)} {H : SL(6, L)}
    (hfix : ∀ X : SL(6, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y : SL(6, K), X = H * Matrix.SpecialLinearGroup.map (algebraMap K L) Y * H⁻¹)
    {J : Type*} [Group J] [Finite J] (ρ : ↥(fixSubgroup Φ') →* J)
    (hρ : Function.Surjective ρ)
    (hc : ∀ z ∈ ρ.ker, ∀ u : ↥(fixSubgroup Φ'), z * u = u * z)
    (hk : Nat.card ρ.ker ∣ 6) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ∣ Nat.card K - 1) :
    ∃ F : Subgroup J, IsElemAbelian q F ∧ 3 ≤ CFSG.Open.pRank q F := by
  classical
  haveI hFfin : Finite ↥(fixSubgroup Φ') := splitModel_finite hfix
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  set E : Subgroup ↥(fixSubgroup Φ') :=
    (LinEngine.diagSLSub (F := K) 5 q).map (splitModelHom hfix) with hEdef
  have hEel : IsElemAbelian q E :=
    (LinEngine.isElemAbelian_diagSLSub (F := K) (n := 5) (q := q)).map (splitModelHom hfix)
  have hErank : 5 ≤ CFSG.Open.pRank q E := by
    rw [hEdef]
    exact (LinEngine.le_pRank_diagSLSub (F := K) (n := 5) hq hdvd).trans
      (CFSG.SectionRank.pRank_le_map hq.one_lt (splitModelHom hfix)
        (splitModelHom_injective hfix) (LinEngine.diagSLSub (F := K) 5 q))
  have hsmall : CFSG.Open.pRank q (E ⊓ ρ.ker) ≤ 1 := by
    refine CFSG.SectionRank.pRank_le hq.one_lt ?_
    intro G hG hGe
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hGe.isPGroup)
    have hle : q ^ j ≤ 6 := by
      rw [← hj]
      exact (Subgroup.card_le_of_le (hG.trans inf_le_right)).trans (Nat.le_of_dvd (by norm_num) hk)
    have hj1 : j ≤ 1 := by
      by_contra h
      push Not at h
      have h2 : q ^ 2 ≤ q ^ j := Nat.pow_le_pow_right hq.one_le (by omega)
      have h6 : q ^ 2 ≤ 6 := h2.trans hle
      have hq3 : 3 ≤ q := by
        have := hq.two_le
        omega
      have h9 : 9 ≤ q ^ 2 := by nlinarith
      omega
    calc Nat.card G = q ^ j := hj
      _ ≤ q ^ 1 := Nat.pow_le_pow_right hq.one_le hj1
  have hineq : CFSG.Open.pRank q E ≤
      CFSG.Open.pRank q (E ⊓ ρ.ker) + CFSG.Open.pRank q (E.map ρ) :=
    CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map hq ρ E
  exact ⟨E.map ρ, hEel.map ρ, by omega⟩

end Split

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
