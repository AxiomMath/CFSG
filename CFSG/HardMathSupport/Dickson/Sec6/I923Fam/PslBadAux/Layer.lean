module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transport
import CFSG.GroupTheory.ExtraspecialCentralizerInnerAut
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnPair
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviModel
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon

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
open Matrix
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open scoped commutatorElement

theorem commutator_fixed_mem_range {n : ℕ} (hn : 0 < n) {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} {x y : projectiveSL n K} (hx : fieldAut n K σ x = x)
    (hy : fieldAut n K σ y = y) :
    ⁅x, y⁆ ∈ (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range := by
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  obtain ⟨h, rfl⟩ := proj_surjective n K y
  rw [fieldAut_proj] at hx hy
  have hz₁ : g⁻¹ * SpecialLinearGroup.map σ.toRingHom g ∈ scalars n K :=
    proj_eq_proj_iff.mp hx.symm
  have hz₂ : h⁻¹ * SpecialLinearGroup.map σ.toRingHom h ∈ scalars n K :=
    proj_eq_proj_iff.mp hy.symm
  have hc : SpecialLinearGroup.map σ.toRingHom ⁅g, h⁆ = ⁅g, h⁆ := by
    rw [map_commutatorElement]
    have e1 : SpecialLinearGroup.map σ.toRingHom g =
        g * (g⁻¹ * SpecialLinearGroup.map σ.toRingHom g) := (mul_inv_cancel_left _ _).symm
    have e2 : SpecialLinearGroup.map σ.toRingHom h =
        h * (h⁻¹ * SpecialLinearGroup.map σ.toRingHom h) := (mul_inv_cancel_left _ _).symm
    rw [e1, e2]
    exact CFSG.GroupTheory.commutatorElement_mul_mem_center g h (scalars_le_center n K hz₁)
      (scalars_le_center n K hz₂)
  refine mem_range_linearSubfieldInclusion.mpr ⟨⁅g, h⁆, fun i j => ?_, ?_⟩
  · have := congrArg (fun z : SpecialLinearGroup (Fin n) K =>
      (z : Matrix (Fin n) (Fin n) K) i j) hc
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at this
    exact RingHom.mem_eqLocusField.mpr this
  · exact map_commutatorElement _ g h

theorem noL2Layer_fieldAut_psl_gen (hO : LieOrderFormulasInput) {n : ℕ} (hn3 : 3 ≤ n)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} (hσ : orderOf σ = 3) {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) : NoL2Layer (fieldAut n K σ) := by
  set k := semilinearFixedSubfield σ with hkdef
  have hk : ∀ x, x ∈ k ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) k
  let S : Subgroup (projectiveSL n K) := (linearSubfieldInclusion n k).range
  let eS : ↥S ≃* projectiveSL n ↥k := (MonoidHom.ofInjective hinj).symm
  haveI : IsSimpleGroup (projectiveSL n ↥k) := KCLinearSubfield.isSimpleGroup_projectiveSL hn3
  have hnabk : ∃ a b : projectiveSL n ↥k, a * b ≠ b * a := by
    have h1 := KCLinearSubfield.not_commutative_projectiveSL (n := n) (K := ↥k) hn3
    push Not at h1
    exact h1
  have hs : IsSimpleGroup ↥S := eS.isSimpleGroup
  have hnab : ∃ a b : ↥S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabk
    exact ⟨eS.symm a, eS.symm b, fun h => hab (by
      have := congrArg eS h
      simpa using this)⟩
  have hSle : S ≤ fixSubgroup (fieldAut n K σ) := by
    rintro _ ⟨y, rfl⟩
    exact fieldAut_linearSubfieldInclusion (fun c hc => (hk c).mp hc) y
  have hcomm : ⁅fixSubgroup (fieldAut n K σ), fixSubgroup (fieldAut n K σ)⁆ ≤ S :=
    Subgroup.commutator_le.2 fun a ha b hb => commutator_fixed_mem_range (by omega) ha hb
  obtain ⟨h3f, hkcard⟩ := card_semilinearFixedSubfield hp hf hK hσ
  have hf0 : 1 ≤ f / 3 := by
    have : 3 ≤ f := Nat.le_of_dvd (by omega) h3f
    omega
  refine noL2_of_simple_normal_comm _ S hSle hcomm hs hnab fun r hr hT => ?_
  have hadm : StatedLieAdmissible .PSL n p (f / 3) :=
    ⟨hp, hf0, by omega, fun hc => by have := (Prod.mk.inj hc).1; omega,
      fun hc => by have := (Prod.mk.inj hc).1; omega⟩
  have hmodel : LieModel ↥S .PSL n p (f / 3) :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨hadm, ↥k, inferInstance, inferInstance, hkcard,
        ⟨eS.trans (statedProjEquiv n ↥k).symm⟩⟩
  exact not_typeL2_of_lieModel hO hadm hmodel (by decide) (by simp; omega)
    (center_eq_bot_of_simple hnab) hr hT

end CFSG.HardMathSupport.Dickson.Sec6.I923
