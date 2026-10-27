module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkDefs
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkBase
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutSpOrthAux.Psp
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartTwo.KFacts
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.KCSpComm
  CFSG.RankThree.CASymplecticSubfield CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.HardMathSupport.Dickson.Sec6 CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

private theorem outerSubThree_fieldAut_psp {r f : ℕ} (hr : 2 ≤ r) {K : Type} [Field K]
    [Finite K] {σ : K ≃+* K} (hσ : orderOf σ = 3) (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) :
    OuterSubThree .PSp r f (fixSubgroup (fieldAut r K σ)) := by
  have : NeZero r := ⟨by omega⟩
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨h3f, hkcard⟩ := card_semilinearFixedSubfield Nat.prime_three hf hK hσ
  set k := descentField σ
  have hkcard' : Nat.card k = 3 ^ (f / 3) := hkcard
  have hf0 : 1 ≤ f / 3 := by
    have : 3 ≤ f := Nat.le_of_dvd (by omega) h3f
    omega
  have h3k : 3 ≤ 3 ^ (f / 3) := Nat.le_self_pow (by omega) 3
  have hinj := subfieldSpProj_injective (K := K) (r := r) (by omega) k
  have hfix : fixSubgroup (fieldAut r K σ) = (subfieldSpProj r k).range := by
    ext x
    have h1 := fixed_iff_mem_range (r := r) (p := 3) (by decide) hσ3 x
    have h2 : (subfieldProj σ).range = (subfieldSpProj r k).range := by
      ext y
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨proj r k g, subfieldSpProj_proj k g⟩
      · rintro ⟨z, rfl⟩
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
        exact ⟨g, (subfieldSpProj_proj k g).symm⟩
    exact h1.trans (Iff.of_eq (congrArg (x ∈ ·) h2))
  let eD : ↥(fixSubgroup (fieldAut r K σ)) ≃* StatedProj (StatedSp r ↥k) :=
    (MulEquiv.subgroupCongr hfix).trans (MonoidHom.ofInjective hinj).symm
  obtain ⟨hsk, hpk⟩ := simple_perfect_statedProj (k := ↥k) hr fun ⟨_, h2⟩ => by
    rw [hkcard'] at h2
    omega
  have hnab : ∃ a b : StatedProj (StatedSp r ↥k), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨hcon⟩⟩
  have hadm : StatedLieAdmissible .PSp r 3 (f / 3) :=
    ⟨Nat.prime_three, hf0, hr, fun hc => by have := (Prod.mk.inj hc).2; omega⟩
  have hmodel : LieModel (StatedProj (StatedSp r ↥k)) .PSp r 3 (f / 3) :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨hadm, ↥k, inferInstance, inferInstance, hkcard', ⟨MulEquiv.refl _⟩⟩
  exact outerSubThree_of_fixed_equiv _ eD hsk hnab
    (outerLayerThree_of_field (by decide) (Nat.mul_div_cancel' h3f) hmodel)

theorem lieOuterThreeAt_psp : LieOuterThreeAt FamPsp := by
  intro P _ _ t n f hadm hF hm ψ hψ3 hψ
  obtain ⟨rfl, -⟩ := hF
  have hC : StatedClassicalModel P .PSp n 3 f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  haveI : Finite (StatedProj (StatedSp n K)) := Finite.of_equiv P e0.toEquiv
  refine outerSubThree_congr e0 ?_
  have hψ3' : MulAut.congr e0 ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hninn : ¬ IsInnerAut (MulAut.congr e0 ψ) := fun h =>
    hψ ((congr_mem_inner_iff_of_equiv e0 ψ).mp h)
  obtain ⟨γ, σ, hσ, hψγ⟩ :=
    OutSpOrth.psp_field_descent hadm.2.2.1 Nat.prime_three hadm.2.1 hK hψ3' hninn
  rw [hψγ]
  exact outerSubThree_conj γ (outerSubThree_fieldAut_psp hadm.2.2.1 hσ hadm.2.1 hK)

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
