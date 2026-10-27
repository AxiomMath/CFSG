module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutSpOrthAux.OrthDescent
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutSpOrthAux.Psp

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.OutSpOrth

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.KCSpComm
  CFSG.RankThree.CASymplecticSubfield CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.CatLeaf CFSG.HardMathSupport.Dickson.Sec6
  CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem noL34Layer_fieldAut_psp_odd (hO : LieOrderFormulasInput) {r : ℕ} (hr : 2 ≤ r) {K : Type}
    [Field K] [Finite K] {σ : K ≃+* K} (hσ : orderOf σ = 3) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) :
    NoL34Layer (fieldAut r K σ) := by
  have : NeZero r := ⟨by omega⟩
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨h3f, hkcard⟩ := card_semilinearFixedSubfield hp hf hK hσ
  set k := descentField σ with hkdef
  have hkcard' : Nat.card k = p ^ (f / 3) := hkcard
  have hf0 : 1 ≤ f / 3 := by
    have : 3 ≤ f := Nat.le_of_dvd (by omega) h3f
    omega
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
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpk : 3 ≤ p ^ (f / 3) := hp3.trans (Nat.le_self_pow (by omega) p)
  have hadm : StatedLieAdmissible .PSp r p (f / 3) :=
    ⟨hp, hf0, hr, fun hc => by
      have h2 := (Prod.mk.inj hc).2
      omega⟩
  have hmodelk : StatedClassicalModel (StatedProj (StatedSp r ↥k)) .PSp r p (f / 3) :=
    ⟨hadm, ↥k, inferInstance, inferInstance, hkcard', ⟨MulEquiv.refl _⟩⟩
  haveI hsk : IsSimpleGroup (StatedProj (StatedSp r ↥k)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ r p (f / 3)
      hmodelk
  have hmodel : LieModel (StatedProj (StatedSp r ↥k)) .PSp r p (f / 3) :=
    (lieModel_classical_iff (by decide)).mpr hmodelk
  obtain ⟨hfin, hM, -⟩ := hO _ .PSp r p (f / 3) hadm hmodel
  have hnab := exists_noncomm_of_simple_of_order hadm hM (by
    show 2 ≤ (f / 3) * (r ^ 2)
    nlinarith)
  exact noL34Layer_of_fixed_equiv _ eD hsk hnab (not_isLThreeFour_of_lieModel_odd hO hp2 hmodel)

theorem noL34Layer_psp_outer_odd (hO : LieOrderFormulasInput) {P : Type} [Group P] [Finite P]
    {n p f : ℕ} (hadm : StatedLieAdmissible .PSp n p f) (hp2 : p ≠ 2)
    (hm : LieModel P .PSp n p f) {ψ : MulAut P} (hψ3 : ψ ^ 3 = 1)
    (hψ : ψ ∉ inner P) : NoL34Layer ψ := by
  have hC : StatedClassicalModel P .PSp n p f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  haveI : Finite (StatedProj (StatedSp n K)) := Finite.of_equiv P e0.toEquiv
  refine noL34Layer_congr e0 ?_
  have hψ3' : MulAut.congr e0 ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hninn : ¬ IsInnerAut (MulAut.congr e0 ψ) := fun h =>
    hψ ((congr_mem_inner_iff_of_equiv e0 ψ).mp h)
  obtain ⟨γ, σ, hσ, hψγ⟩ := psp_field_descent hadm.2.2.1 hadm.1 hadm.2.1 hK hψ3' hninn
  rw [hψγ]
  exact noL34Layer_conj γ (noL34Layer_fieldAut_psp_odd hO hadm.2.2.1 hσ hadm.1 hp2 hadm.2.1 hK)

end CFSG.HardMathSupport.Dickson.Sec6.OutSpOrth

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.CatLeaf CFSG.HardMathSupport.Dickson.Sec6.I923

theorem noL34OuterAt3_psp (hO : LieOrderFormulasInput) : NoL34OuterAtThree FamPsp := by
  intro P _ _ t n f hadm _ hF hm ψ hψ3 hψ
  obtain ⟨rfl, -⟩ := hF
  exact OutSpOrth.noL34Layer_psp_outer_odd hO hadm (by norm_num) hm hψ3 hψ

theorem noL34OuterAt3_orthOdd (hO : LieOrderFormulasInput) : NoL34OuterAtThree FamOrthOdd := by
  intro P _ _ t n f _ _ hF hm ψ hψ3 hψ
  obtain rfl := hF
  have hC : StatedClassicalModel P .POmegaOdd n 3 f :=
    (lieModel_classical_iff (by decide)).mp hm
  exact OutSpOrth.noL34Layer_omega_odd_outer hO hC hψ3 fun a h => hψ ⟨a, h⟩

theorem noL34OuterAt3_orthPlus (hO : LieOrderFormulasInput) : NoL34OuterAtThree FamOrthPlus := by
  intro P _ _ t n f _ _ hF hm ψ hψ3 hψ
  obtain ⟨rfl, hn5⟩ := hF
  have hC : StatedClassicalModel P .POmegaPlus n 3 f :=
    (lieModel_classical_iff (by decide)).mp hm
  exact OutSpOrth.noL34Layer_omega_plus_outer hO hC (by norm_num) hn5 hψ3 fun a h => hψ ⟨a, h⟩

theorem noL34OuterAt3_orthMinus (hO : LieOrderFormulasInput) :
    NoL34OuterAtThree FamOrthMinus := by
  intro P _ _ t n f _ _ hF hm ψ hψ3 hψ
  obtain rfl := hF
  have hC : StatedClassicalModel P .POmegaMinus n 3 f :=
    (lieModel_classical_iff (by decide)).mp hm
  exact OutSpOrth.noL34Layer_omega_minus_outer hO hC (by norm_num) hψ3 fun a h => hψ ⟨a, h⟩

end CFSG.HardMathSupport.Dickson.Sec6
