module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnFieldAut
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviModel

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.RankTwoClassical
  CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
  CFSG.ComponentClassification.CatLeaf
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem noL2Layer_fieldAut_psl (hO : LieOrderFormulasInput) {n : ℕ} (hn3 : 3 ≤ n) {K : Type}
    [Field K] [Finite K] {σ : K ≃+* K} (hσ : orderOf σ = 3)
    (hcop : Nat.Coprime 3 (Nat.gcd n (Nat.card K - 1))) {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) : NoL2Layer (fieldAut n K σ) := by
  set k := semilinearFixedSubfield σ with hkdef
  have hfixset := fixedSubgroup_fieldAut_eq_range_gen hn3 Nat.prime_three hcop hσ
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) k
  have hfix : fixSubgroup (fieldAut n K σ) = (linearSubfieldInclusion n k).range := by
    ext x
    exact Iff.of_eq (congrArg (x ∈ ·) hfixset)
  let eD : ↥(fixSubgroup (fieldAut n K σ)) ≃* projectiveSL n ↥k :=
    (MulEquiv.subgroupCongr hfix).trans (MonoidHom.ofInjective hinj).symm
  haveI : IsSimpleGroup (projectiveSL n ↥k) := KCLinearSubfield.isSimpleGroup_projectiveSL hn3
  have hnabk : ∃ a b : projectiveSL n ↥k, a * b ≠ b * a := by
    have h1 := KCLinearSubfield.not_commutative_projectiveSL (n := n) (K := ↥k) hn3
    push Not at h1
    exact h1
  have hs : IsSimpleGroup ↥(fixSubgroup (fieldAut n K σ)) := eD.isSimpleGroup
  have hnab : ∃ a b : ↥(fixSubgroup (fieldAut n K σ)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabk
    exact ⟨eD.symm a, eD.symm b, fun h => hab (by
      have := congrArg eD h
      simpa using this)⟩
  obtain ⟨h3f, hkcard⟩ := card_semilinearFixedSubfield hp hf hK hσ
  have hf0 : 1 ≤ f / 3 := by
    have : 3 ≤ f := Nat.le_of_dvd (by omega) h3f
    omega
  haveI := hs
  refine noL2_of_simple_fixed _ hs hnab fun r hr hT => ?_
  have hadm : StatedLieAdmissible .PSL n p (f / 3) :=
    ⟨hp, hf0, by omega, fun hc => by have := (Prod.mk.inj hc).1; omega,
      fun hc => by have := (Prod.mk.inj hc).1; omega⟩
  have hmodel : LieModel ↥(fixSubgroup (fieldAut n K σ)) .PSL n p (f / 3) :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨hadm, ↥k, inferInstance, inferInstance, hkcard,
        ⟨eD.trans (statedProjEquiv n ↥k).symm⟩⟩
  exact not_typeL2_of_lieModel hO hadm hmodel (by decide) (by simp; omega)
    (center_eq_bot_of_simple hnab) hr hT

theorem famOK_psl (hO : LieOrderFormulasInput) {n : ℕ} (hn3 : 3 ≤ n) {K : Type} [Field K]
    [Finite K] (hcop : Nat.Coprime 3 (Nat.gcd n (Nat.card K - 1))) {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) : FamOK (projectiveSL n K) := by
  intro ψ hψ3 hninn
  have hD : ψ ∉ linearAutGroup n K := fun hD =>
    hninn (inner_of_mem_linearAut_of_pow_eq_one hn3 hcop hD hψ3)
  obtain ⟨σ, hσ, H, hψH⟩ := linear_order_three_field_descent hn3 ψ hψ3 hD
  exact ⟨conjAut n K H, fieldAut n K σ, hψH,
    noL2Layer_fieldAut_psl hO hn3 hσ hcop hp hf hK⟩

theorem y923_lieRestAt_psl (hO : LieOrderFormulasInput) : Y923_LieRestAt FamPslGood := by
  intro Y _ _ hq hcore hL2 t n p f hadm ht hF hm α h3 hnot J hJ r hr
  obtain ⟨rfl, hn3, hcop⟩ := hF
  have hC : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  rw [← hK] at hcop
  exact noL2_of_famOK hq (e0.trans (statedProjEquiv n K)) (famOK_psl hO hn3 hcop hadm.1 hadm.2.1 hK)
    h3 hnot hJ hr

end CFSG.HardMathSupport.Dickson.Sec6.I923
