module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkBase
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Field
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Lang.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.Sec6.I923 (FamTwE6 exists_twistedE6RootGroup_equiv
  chevalleyExceptionalModel_twistedE6_of_equiv congr_mem_inner_iff_of_equiv)


private theorem outerSubThree_fieldActor_twE6 {d : ℕ} (hd : 1 ≤ d) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (3 ^ (3 * d)) ^ 2) (σ : K ≃+* K)
    [Finite ↥(twistedE6RootGroup K σ)] (hσ : ∀ c, σ c = c ^ 3 ^ (3 * d)) {T ε : K ≃+* K}
    (hT : ∀ c, T c = c ^ 3 ^ d) (hε : ∀ c, ε c = c ^ 3 ^ (d * (3 + 1))) :
    OuterSubThree .twistedE6 0 (3 * d) (fixSubgroup (fieldActor (t := TwistTag.E6) σ ε)) := by
  have hKdp : Nat.card K = 3 ^ (2 * d * 3) := by rw [hK]; ring
  obtain ⟨fr, hfr, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_three (by omega) hKdp
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ 3 ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hσ₀ : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ c : K) = (c : K) ^ 3 ^ d :=
    fun c => by rw [coe_fixSubfieldRestrict, hT]
  obtain ⟨-, hcardk, hJC, -, hder, hsimple, hnc, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer Nat.prime_three hd
      le_rfl (by decide) K hKdp κ hκ σ (fun c => by rw [hσ, mul_comm])
      (fixSubfieldRestrict T κ) hσ₀ ε hε
  set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ)
  haveI : Finite (fixSubfield κ) := Subtype.finite
  haveI := hsimple
  let e1 : ↥(J.subgroupOf C) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJC
  let eJ : ↥J ≃* twistedE6RootGroup (fixSubfield κ) (fixSubfieldRestrict T κ) :=
    (Subgroup.equivMapOfInjective _ _
      (baseChangeGL_injective (τ := TwistTag.E6.tag) (fixSubfield κ).subtype)).symm
  have hM : ChevalleyExceptionalModel ↥(J.subgroupOf C) .twistedE6 3 d :=
    chevalleyExceptionalModel_twistedE6_of_equiv Nat.prime_three hd
      (by rw [hcardk, ← pow_mul, mul_comm]) (fixSubfieldRestrict T κ)
      (fun c => Subtype.ext (by rw [hσ₀ c, SubmonoidClass.coe_pow])) (e1.trans eJ)
  have hnab : ∃ a b : ↥(J.subgroupOf C), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hnc fun a b => e1.symm.injective (by rw [map_mul, map_mul]; exact hcon _ _)
  have hD : ⁅fixSubgroup (fieldActor (t := TwistTag.E6) σ ε),
      fixSubgroup (fieldActor (t := TwistTag.E6) σ ε)⁆ = J.subgroupOf C := hder
  exact outerSubThree_of_simple_normal_comm (hD.ge.trans (Subgroup.commutator_le_self _)) hD.le
    e1.isSimpleGroup hnab
    (outerLayerThree_of_field (by decide) rfl (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)))

theorem lieOuterThreeAt_twE6 : LieOuterThreeAt FamTwE6 := by
  intro P _ _ t n f hadm hF hm ψ hψ3 hψ
  obtain rfl : t = .twistedE6 := hF
  obtain ⟨-, hf, rfl⟩ := hadm
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_twistedE6RootGroup_equiv Nat.prime_three hf
    (hm.chevalleyExceptionalModel (by decide)).2
  haveI : Finite ↥(twistedE6RootGroup K σ) := Finite.of_equiv P e.symm.toEquiv
  refine outerSubThree_congr e.symm ?_
  set β := MulAut.congr e.symm ψ with hβdef
  have hβ3 : β ^ 3 = 1 := by rw [hβdef, ← map_pow, hψ3, map_one]
  have hβinn : β ∉ twistedE6Inn K σ := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv e.symm ψ).mp hin)
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_three hf K hK σ hσ
  have hpg : ¬ 3 ∣ Nat.gcd 3 (3 ^ f + 1) := fun h => by
    have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    exact absurd ((Nat.dvd_add_right h3).1 (h.trans (Nat.gcd_dvd_right 3 _))) (by norm_num)
  have hη : Θ β ≠ 1 := fun h1 => hβinn (mem_inner_of_mem_inn_sup_diag Nat.prime_three hK hσ hpg
    hcube hβ3 (by rw [← hker, MonoidHom.mem_ker]; exact h1))
  obtain ⟨d, rfl, hd, r, s, T, ε, hT, hε, hrs, δ, hδ, -⟩ :=
    twisted_E6_field_descent_data_of_prime_order Nat.prime_three hf K
      (by rw [hK, ← pow_mul, mul_comm]) σ hσ Θ hΘ Nat.prime_three (by norm_num) β hβ3 hη
  exact outerSubThree_of_conj_pow hrs hδ (outerSubThree_fieldActor_twE6 hd hK σ hσ hT hε)

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
