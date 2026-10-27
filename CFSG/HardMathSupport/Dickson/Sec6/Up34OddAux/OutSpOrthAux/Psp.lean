module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldFixed
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon

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

theorem psp_field_descent {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    {ψ : MulAut (StatedProj (StatedSp r K))} (hψ3 : ψ ^ 3 = 1) (hninn : ¬ IsInnerAut ψ) :
    ∃ (γ : MulAut (StatedProj (StatedSp r K))) (σ : K ≃+* K), orderOf σ = 3 ∧
      ψ = γ * fieldAut r K σ * γ⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, hidx, hrel, hdesc⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent hp hf hr hK
  have hidx' : (spSemilinearAutGroup r K).index ≤ 2 := Nat.le_of_dvd (by norm_num) hidx
  have hE : ψ ∈ spSemilinearAutGroup r K :=
    OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' (by decide : Odd 3)
      (by rw [hψ3]; exact Subgroup.one_mem _)
  have hD : ψ ∉ spLinearAutGroup r K := by
    intro hD
    have hrel2 : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hrel.trans (Nat.gcd_dvd_left _ _)
    haveI := inner_normal (StatedProj (StatedSp r K))
    have hmem : ψ ∈ inner (StatedProj (StatedSp r K)) := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hrel2 with hk | hk
      · exact KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow
          (H := inner (StatedProj (StatedSp r K))) (k := 0) (by rw [hk]; rfl) Nat.prime_three
          (by norm_num) hD hψ3
      · exact KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow
          (H := inner (StatedProj (StatedSp r K))) (k := 1) (by rw [hk]; rfl) Nat.prime_three
          (by norm_num) hD hψ3
    exact hninn hmem
  have hψord : orderOf ψ = 3 := by
    refine orderOf_eq_prime hψ3 ?_
    intro h1
    exact hninn (h1 ▸ ⟨1, by simp⟩)
  obtain ⟨h3f, σ, hσ, -, h, hhD, hψh⟩ := hdesc 3 Nat.prime_three ψ hE hD hψord
  exact ⟨h, σ, hσ, hψh⟩

theorem noL34Layer_fieldAut_psp (hO : LieOrderFormulasInput) {r : ℕ} (hr : 2 ≤ r) {K : Type}
    [Field K] [Finite K] {σ : K ≃+* K} (hσ : orderOf σ = 3) {p f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) :
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
  have hpk : 5 ≤ p ^ (f / 3) := hp5.trans (Nat.le_self_pow (by omega) p)
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
  exact noL34Layer_of_fixed_equiv _ eD hsk hnab
    (not_isLThreeFour_of_lieModel_odd hO (by omega) hmodel)

end CFSG.HardMathSupport.Dickson.Sec6.OutSpOrth
