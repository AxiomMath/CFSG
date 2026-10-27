module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6GraphRational
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7TwistMain

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.SteinbergCE
  CFSG.LocalAnalysis.SteinbergCE.E6GraphCoset CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatLeaf
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootDiag)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem exists_mulEquiv_E6_graph_coset_fixed
    {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP (AlgebraicClosure K) p]
    (hK : Nat.card K = p ^ f) (hF : Odd (Nat.card K)) {α : MulAut (adjointGroup TwistTag.E6.tag K)}
    {g : adjointGroup TwistTag.E6.tag K} {a : Fin TwistTag.E6.tag.rank → Kˣ}
    (hαg : ∀ h : adjointGroup TwistTag.E6.tag K, (α h : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 K *
        h * (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
          (g : ModGL TwistTag.E6.tag K)⁻¹)
    (hα : α ^ 2 = 1) :
    ∃ x ∈ graphRational (AlgebraicClosure K) p f 0,
      (x * diagramMap TwistTag.E6 (AlgebraicClosure K)) ^ 2 = 1 ∧
        Nonempty (fixedSubgroup α ≃* graphCosetFixed (AlgebraicClosure K) p f 0 x) := by
  classical
  set k := AlgebraicClosure K
  set ι := algebraMap K k with hι
  set Fr := iterateFrobenius k p f with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, hK]
  have hFrι : ∀ c : K, Fr (ι c) = ι c := fun c => by
    rw [hFr, ← map_pow]
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, FiniteField.pow_card]
  set P := diagramMap TwistTag.E6 k with hPdef
  set b : Fin TwistTag.E6.tag.rank → kˣ := fun i => Units.map ι.toMonoidHom (a i) with hb_def
  set x := baseChangeGL ι (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b
    with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness TwistTag.E6.tag K hF k ι
  have hgG : baseChangeGL ι (g : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag k :=
    hHG ⟨g, g.2, rfl⟩
  have hxG : x ∈ adjointGroup TwistTag.E6.tag k :=
    mul_mem hgG (exceptional_Lang_adjoint_diagonal_lift TwistTag.E6.tag k b).1
  have hdb : baseChangeGL ι (rootDiagUnit TwistTag.E6.tag a) = rootDiagUnit TwistTag.E6.tag b :=
    baseChangeGL_rootDiagUnit ι a
  have hPι : baseChangeGL ι (diagramMap TwistTag.E6 K) = P := baseChangeGL_diagramMap ι TwistTag.E6
  have hxconj : ∀ h : adjointGroup TwistTag.E6.tag K,
      x * P * baseChangeGL ι (h : ModGL TwistTag.E6.tag K) * (x * P)⁻¹ =
        baseChangeGL ι (α h : ModGL TwistTag.E6.tag K) := by
    intro h
    rw [hαg h, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv,
      hdb, hPι, hx_def]
    group
  obtain ⟨-, hHR, -, hder⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group TwistTag.E6.tag K hF k Fr hFr
  have hgR := hHR ⟨g, g.2, rfl⟩
  have hFd : Units.map (entrywiseHom Fr) (rootDiagUnit TwistTag.E6.tag b) =
      rootDiagUnit TwistTag.E6.tag b := by
    refine Units.ext ?_
    change entrywise Fr (rootDiag b) = rootDiag b
    rw [entrywise_rootDiag]
    congr 1
    funext i
    ext
    exact hFrι _
  have hRF : graphRational k p f 0 =
        adjointGroup TwistTag.E6.tag k ⊓
          (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    ext y
    refine Subgroup.mem_inf.trans ((and_congr Iff.rfl ?_).trans Subgroup.mem_inf.symm)
    change frobTwistGL TwistTag.E6.tag k p f (P ^ 0) y = y ↔ Units.map (entrywiseHom Fr) y = y
    rw [frobTwistGL_apply, pow_zero, one_mul, inv_one, mul_one]
  have hxR : x ∈ graphRational k p f 0 := by
    rw [hRF]
    refine Subgroup.mem_inf.2 ⟨hxG, ?_⟩
    change Units.map (entrywiseHom Fr) x = x
    rw [hx_def, map_mul, hFd]
    congr 1
    exact (Subgroup.mem_inf.1 hgR).2
  have hα2 : ∀ h, α (α h) = h := fun h => by
    have := congrArg (fun φ : MulAut (adjointGroup TwistTag.E6.tag K) => φ h) hα
    simpa [sq] using this
  have hP2 : P * P = 1 := by
    have h := diagramMap_pow_order TwistTag.E6 k
    rwa [show TwistTag.E6.order = 2 from rfl, sq] at h
  have hPG : ∀ y ∈ adjointGroup TwistTag.E6.tag k,
      P * y * P⁻¹ ∈ adjointGroup TwistTag.E6.tag k := by
    have hQ := conj_mem_adjointGroup_of_map_eq (map_conj_diagramMap_zpow TwistTag.E6 k 1)
    rw [zpow_one] at hQ
    exact hQ
  have hx2 : (x * P) ^ 2 = 1 := by
    have hsqG : (x * P) ^ 2 ∈ adjointGroup TwistTag.E6.tag k := by
      have e : (x * P) ^ 2 = x * (P * x * P⁻¹) * (P * P) := by
        rw [sq]
        group
      rw [e, hP2, mul_one]
      exact mul_mem hxG (hPG x hxG)
    refine hfaith _ hsqG fun y hy => ?_
    obtain ⟨h, hh, rfl⟩ := hy
    have h1 := hxconj ⟨h, hh⟩
    have h2 := hxconj (α ⟨h, hh⟩)
    rw [hα2] at h2
    change x * P * baseChangeGL ι h * (x * P)⁻¹ = _ at h1
    change _ = baseChangeGL ι h at h2
    rw [sq]
    calc x * P * (x * P) * baseChangeGL ι h =
        (x * P * (x * P * baseChangeGL ι h * (x * P)⁻¹) * (x * P)⁻¹) * (x * P * (x * P)) := by
          group
      _ = baseChangeGL ι h * (x * P * (x * P)) := by rw [h1, h2]
  have hHder : ⁅graphRational k p f 0, graphRational k p f 0⁆ =
      (adjointGroup TwistTag.E6.tag K).map (baseChangeGL ι) := by
    rw [hRF]
    exact hder
  let φ : adjointGroup TwistTag.E6.tag K →* ModGL TwistTag.E6.tag k :=
    (baseChangeGL ι).comp (adjointGroup TwistTag.E6.tag K).subtype
  have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
  have hmap : (fixedSubgroup α).map φ = graphCosetFixed k p f 0 x := by
    rw [graphCosetFixed, hHder]
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c, c.2, rfl⟩, ?_⟩
      have h1 := hxconj c
      have hc' : α c = c := hc
      rw [hc'] at h1
      change baseChangeGL ι (c : ModGL TwistTag.E6.tag K) * (x * P) =
        x * P * baseChangeGL ι (c : ModGL TwistTag.E6.tag K)
      calc baseChangeGL ι (c : ModGL TwistTag.E6.tag K) * (x * P) =
          (x * P * baseChangeGL ι (c : ModGL TwistTag.E6.tag K) * (x * P)⁻¹) * (x * P) := by
            rw [h1]
        _ = x * P * baseChangeGL ι (c : ModGL TwistTag.E6.tag K) := by group
    · rintro ⟨⟨c, hc, rfl⟩, hcx⟩
      refine ⟨⟨c, hc⟩, ?_, rfl⟩
      have h1 := hxconj ⟨c, hc⟩
      have hcx' : baseChangeGL ι c * (x * P) = x * P * baseChangeGL ι c := hcx
      have h2 : x * P * baseChangeGL ι c * (x * P)⁻¹ = baseChangeGL ι c := by
        rw [← hcx']
        group
      rw [h2] at h1
      exact Subtype.ext (hinj h1.symm)
  exact ⟨x, hxR, hx2, ⟨(Subgroup.equivMapOfInjective _ φ hφ).trans
    (MulEquiv.subgroupCongr hmap)⟩⟩

theorem oddE6GraphInput_holds
    : OddE6GraphInput := by
  intro K _ _ p f hp hp2 hK α g a hαg hα L hL
  have hf := (one_le_and_three_le_of_card hp hp2 hK).1
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p K (AlgebraicClosure K)
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  obtain ⟨x, hxR, hx2, ⟨Φ⟩⟩ := exists_mulEquiv_E6_graph_coset_fixed hK hKodd hαg hα2
  exact oddLieCentralQuotient_of_mulEquiv (L.equivMapOfInjective Φ.toMonoidHom Φ.injective)
    (oddLieCentralQuotient_of_isComponent_graphCosetFixed p hp2 hf _ hk 0 (Or.inl rfl) hxR hx2
      (LocalCores.isComponent_map_mulEquiv Φ hL))

theorem oddExcInnerDiagInput_E7
    : OddExcInnerDiagInput .E7 :=
  oddExcInnerDiagInput_E7_of_E6Graph oddE6GraphInput_holds

theorem gls3OddFamilyInput_E7_holds
    : GLS3OddFamilyInput .E7 :=
  gls3OddFamilyInput_E7 oddExcInnerDiagInput_E7

theorem gls3OddFamilyInput_E6_holds
    : GLS3OddFamilyInput .E6 :=
  gls3OddFamilyInput_E6 oddExcInnerDiagInput_E6 oddE6GraphInput_holds

end CFSG.ComponentClassification.CatLeafProof
