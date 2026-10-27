module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLow
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddD4Component
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTwisted

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

theorem oddTrialityInnerInput_holds
    : OddTrialityInnerInput := by
  classical
  intro J _ p f hp hp2 hadm hm α hα hαi L hL
  have hf : 1 ≤ f := hadm.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have htw : TwistedChevalleyModel J .D4 (p ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  have hK3 : Nat.card K = (p ^ f) ^ 3 := hK
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hCdef
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by
    rw [hβdef, ← map_pow, ← hα, pow_orderOf_eq_one, map_one]
  have hβi : β ∈ (MulAut.conj : C →* MulAut C).range := by
    change MulAut.congr e α ∈ OuterAutomorphisms.inner C
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαi
  obtain ⟨c, hc⟩ := hβi
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK3 σ hσ
  have hc2 : c ^ 2 = 1 :=
    mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hc, hβ2, map_one])
  have hc1 : c ≠ 1 := by
    rintro rfl
    have hα1 : α = 1 := (MulAut.congr e).injective (by rw [map_one, ← hβdef, ← hc, map_one])
    rw [hα1, orderOf_one] at hα
    exact absurd hα (by norm_num)
  set k := AlgebraicClosure K
  set ι := algebraMap K k with hι
  have hK3' : Nat.card K = p ^ (3 * f) := by rw [hK3, ← pow_mul, mul_comm]
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK3'
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K k).injective p
  set Fr := iterateFrobenius k p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  have halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k := by
    let _ : Algebra (ZMod p) k := ZMod.algebra k p
    refine ⟨fun y => ?_⟩
    obtain ⟨E, hEf, hyE, -⟩ := exists_finite_subfield_of_finset (K := K) ({y} : Finset k)
    have hy : y ∈ E := hyE (Finset.mem_coe.2 (Finset.mem_singleton_self y))
    have : Fintype E := Fintype.ofFinite E
    have hpow : y ^ Fintype.card E = y :=
      congrArg Subtype.val (FiniteField.pow_card (⟨y, hy⟩ : E))
    refine ⟨Polynomial.X ^ Fintype.card E - Polynomial.X,
      FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card, ?_⟩
    rw [map_sub, map_pow, Polynomial.aeval_X, hpow, sub_self]
  obtain ⟨-, -, hHR, -, -, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group TwistTag.D4
    hp hf hodd K hK3 σ.toRingHom hσ k Fr hFr
  have hRF : fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)) =
        twistedFixedGroup TwistTag.D4 k Fr := rfl
  set y := baseChangeGL ι (c : ModGL TwistTag.D4.tag K) with hydef
  have hyR : y ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)) := by
    rw [hRF]
    exact hHR ⟨c, c.2, rfl⟩
  have hy2 : y ^ 2 = 1 := by
    rw [hydef, ← map_pow, ← Subgroup.coe_pow, hc2, Subgroup.coe_one, map_one]
  have hy1 : y ≠ 1 := by
    intro h1
    refine hc1 (Subtype.ext (baseChangeGL_injective ι ?_))
    rw [Subgroup.coe_one, map_one]
    exact h1
  let φ : C →* ModGL TwistTag.D4.tag k := (baseChangeGL ι).comp C.subtype
  have hφ : Function.Injective φ := (baseChangeGL_injective ι).comp Subtype.val_injective
  have hmap : (fixedSubgroup (MulAut.conj c)).map φ =
      ⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
        (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)),
        fixedPointsIn (adjointGroup TwistTag.D4.tag k)
          (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k))⁆ ⊓
        Subgroup.centralizer {y} := by
    rw [hRF, hder]
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨a, a.2, rfl⟩, ?_⟩
      have ha' : c * a * c⁻¹ = a := ha
      have hac : a * c = c * a := by
        calc a * c = c * a * c⁻¹ * c := by rw [ha']
          _ = c * a := by group
      change baseChangeGL ι (a : ModGL TwistTag.D4.tag K) * y =
        y * baseChangeGL ι (a : ModGL TwistTag.D4.tag K)
      rw [hydef, ← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hac]
    · rintro ⟨⟨a, ha, rfl⟩, hay⟩
      refine ⟨⟨a, ha⟩, ?_, rfl⟩
      change c * ⟨a, ha⟩ * c⁻¹ = ⟨a, ha⟩
      have hac : (⟨a, ha⟩ : C) * c = c * ⟨a, ha⟩ := by
        refine Subtype.ext (baseChangeGL_injective ι ?_)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
        exact hay
      rw [← hac]
      group
  set X₀ := ⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)),
      fixedPointsIn (adjointGroup TwistTag.D4.tag k)
        (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k))⁆ ⊓
      Subgroup.centralizer {y} with hX₀def
  let Φ : fixedSubgroup (MulAut.conj c) ≃* X₀ :=
    ((fixedSubgroup (MulAut.conj c)).equivMapOfInjective φ hφ).trans
      (MulEquiv.subgroupCongr hmap)
  let Θ : fixedSubgroup α ≃* X₀ := ((fixedSubgroupCongrEquiv e α).trans
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc.symm))).trans Φ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite X₀ := Finite.of_equiv _ Φ.toEquiv
  set L' := L.map Θ.toMonoidHom with hL'def
  have hL' : IsComponent L' := LocalCores.isComponent_map_mulEquiv Θ hL
  have hL'2 : IsPComponent 2 L' := CatLeafProof.isPComponent_two_of_isComponent hL'
  have hof : (L'.map X₀.subtype).subgroupOf X₀ = L' :=
    Subgroup.comap_map_eq_self_of_injective X₀.subtype_injective L'
  obtain ⟨F₂, _, _, d, hd, hF₂, f₀, hf₀⟩ := exists_SL2_surjective_of_d4_involution_component p
    hp2 halg hf hyR hy1 hy2 (Subgroup.map_subtype_le L') (by rw [hof]; exact hL'2)
  let eL : L ≃* L'.map X₀.subtype := (L.equivMapOfInjective Θ.toMonoidHom Θ.injective).trans
    (L'.equivMapOfInjective X₀.subtype X₀.subtype_injective)
  set f₁ : SL(2, F₂) →* L := eL.symm.toMonoidHom.comp f₀ with hf₁def
  have hf₁ : Function.Surjective f₁ := eL.symm.surjective.comp hf₀
  have hd1 : 1 ≤ f * d := by rcases hd with rfl | rfl <;> omega
  have hF₂' : Nat.card F₂ = p ^ (f * d) := by rw [hF₂, ← pow_mul]
  have hF₂odd : Odd (Nat.card F₂) := by
    rw [hF₂']
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hF₂2 : Nat.card F₂ ≠ 2 := fun h => absurd (h ▸ hF₂odd) (by decide)
  by_cases hF₂3 : Nat.card F₂ = 3
  ·
    have := CatalogueBOrthogonalFourSplitComponents.specialLinearTwo_three_solvable hF₂3
    have : Group.IsSolvable L := Group.isSolvable_of_surjective hf₁
    have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hL.1
    have : Group.IsPerfect L := hL.1.1
    exact (Group.IsPerfect.not_isSolvable L inferInstance).elim
  have hS := CatalogueBGeneralLinear.specialLinear_quasisimple 2 F₂ le_rfl (Or.inr hF₂2)
    (Or.inr hF₂3)
  have hr : (L.subtype.comp f₁).range = L := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hf₁, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  obtain ⟨E⟩ := nonempty_centerQuotient_equiv_range hS (L.subtype.comp f₁)
    (by rw [hr]; exact ne_bot_of_isQuasisimple hL.1)
  let eM : L ≃* (L.subtype.comp f₁).range := MulEquiv.subgroupCongr hr.symm
  exact oddLieCentralQuotient_of_equiv_psl_two hp hd1 hF₂' hF₂2 hF₂3
    ((QuotientGroup.congr _ _ eM (Subgroup.map_center_eq eM)).trans E.symm)

end CFSG.ComponentClassification.CatLeafProof
