module

public import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent
public import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer
public import CFSG.LieType.Chevalley.OddDiagramFixedAmbientCentralizer
public import CFSG.LieType.Chevalley.OddDiagramDerivedFieldFixedComponents
public import CFSG.LieType.AlgebraicGroups.RootCoordinateLang
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBAlmostSimple

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.AlgebraicGroups CFSG.GroupTheory
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem exists_conj_eq_of_sq_eq_twisted_frobenius_odd
    (t : TwistTag) {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hodd : Odd (p ^ f)) (K : Type) [Field K]
    (hK : Nat.card K = (p ^ f) ^ t.order) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (p ^ f)) (S : MulAut (adjointGroup t.tag L))
    (hS2 : ∀ g, ((S (S g) : adjointGroup t.tag L) : ModGL t.tag L) = twistHom t L Fr g)
    (hLang : ∀ y : adjointGroup t.tag L, ∃ h, y = h⁻¹ * S h)
    (ιH : graphFixedRootGroup t K σ →* adjointGroup t.tag L)
    (hιH : ∀ u, (ιH u : ModGL t.tag L) = baseChangeGL (algebraMap K L) u)
    (β : MulAut (graphFixedRootGroup t K σ)) (hβ : ∀ u, S (ιH u) = ιH (β u))
    (x : adjointGroup t.tag L) (α : MulAut (graphFixedRootGroup t K σ))
    (hα : ∀ u, ιH (α u) = x * S (ιH u) * x⁻¹) (hα2 : α * α = 1) :
    ∃ ψ : MulAut (graphFixedRootGroup t K σ), ψ * α * ψ⁻¹ = β := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hι : Function.Injective ιH := fun u v huv => Subtype.ext (baseChangeGL_injective
    (algebraMap K L) (by rw [← hιH, ← hιH, huv]))
  have hcomm : (algebraMap K L).comp σ = Fr.comp (algebraMap K L) := RingHom.ext fun c => by
    rw [RingHom.comp_apply, RingHom.comp_apply, hσ, hFr, map_pow]
  have hSS : ∀ u, S (S (ιH u)) = ιH u := fun u => Subtype.ext (by
    rw [hS2, hιH, twistHom_baseChangeGL (algebraMap K L) hcomm]
    congr 1
    exact (graphFixedRootGroup_le t K σ u.2).2)
  have hz : x * S x = 1 := by
    obtain ⟨-, -, hC, -⟩ :=
      odd_diagram_fixed_ambient_centralizer_trivial t hp hf hodd K hK σ hσ L (algebraMap K L)
    refine Subtype.ext (hC _ (x * S x).2 fun g hg => ?_)
    obtain ⟨u, hu, rfl⟩ := hg
    have hαα : α (α ⟨u, hu⟩) = ⟨u, hu⟩ := by rw [← MulAut.mul_apply, hα2, MulAut.one_apply]
    have h1 : ιH (α (α ⟨u, hu⟩)) = x * S x * ιH ⟨u, hu⟩ * (x * S x)⁻¹ := by
      rw [hα, hα, map_mul, map_mul, map_inv, hSS]
      group
    rw [hαα] at h1
    have h2 : x * S x * ιH ⟨u, hu⟩ = ιH ⟨u, hu⟩ * (x * S x) := by
      calc x * S x * ιH ⟨u, hu⟩ = (x * S x * ιH ⟨u, hu⟩ * (x * S x)⁻¹) * (x * S x) := by group
        _ = ιH ⟨u, hu⟩ * (x * S x) := by rw [← h1]
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul, hιH] at h3 ⊢
    exact h3
  obtain ⟨h, hR, hxh, -⟩ := exceptional_Lang_norm_one_descent S.toMonoidHom (m := 2)
    (by norm_num) hLang x (by simpa [List.range_succ] using hz)
  have hxh' : x = h⁻¹ * S h := hxh
  have hSh : S (S h) = h := hR
  have hhF : twistHom t L Fr (h : ModGL t.tag L) = h := by rw [← hS2, hSh]
  obtain ⟨-, -, -, -, -, hnorml⟩ := exceptional_ambient_twisted_Frobenius_fixed_normalizer t
    hp hf K hK σ hσ L Fr hFr
  have hmap : ((graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L))).map
      (MulAut.conj (h : ModGL t.tag L)).toMonoidHom =
        (graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L)) :=
    map_conj_eq_of_mem_normalizer (hnorml ⟨h.2, hhF⟩)
  let eH : graphFixedRootGroup t K σ ≃*
      (graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L)) :=
    Subgroup.equivMapOfInjective (graphFixedRootGroup t K σ) (baseChangeGL (algebraMap K L))
      (baseChangeGL_injective _)
  have heH : ∀ u, ((eH u : (graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L))) :
      ModGL t.tag L) = baseChangeGL (algebraMap K L) u := fun u =>
    Subgroup.coe_equivMapOfInjective_apply _ _ _ _
  let ψ : MulAut (graphFixedRootGroup t K σ) :=
    eH.trans ((mulAutRestrict _ (MulAut.conj (h : ModGL t.tag L)) hmap).trans eH.symm)
  have hψ0 : ∀ u, baseChangeGL (algebraMap K L) (ψ u : ModGL t.tag K) =
      (h : ModGL t.tag L) * baseChangeGL (algebraMap K L) u * (h : ModGL t.tag L)⁻¹ := by
    intro u
    rw [← heH, ← heH]
    change ((eH (eH.symm (mulAutRestrict _ (MulAut.conj (h : ModGL t.tag L)) hmap (eH u))) :
      (graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L))) : ModGL t.tag L) = _
    rw [MulEquiv.apply_symm_apply, coe_mulAutRestrict, MulAut.conj_apply]
  have hψ : ∀ u, ιH (ψ u) = h * ιH u * h⁻¹ := fun u => Subtype.ext (by
    rw [hιH, hψ0, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hιH])
  have hψinv : ∀ u, ιH (ψ⁻¹ u) = h⁻¹ * ιH u * h := by
    intro u
    have h1 := hψ (ψ⁻¹ u)
    rw [MulAut.apply_inv_self] at h1
    rw [h1]
    group
  refine ⟨ψ, MulEquiv.ext fun u => hι ?_⟩
  rw [MulAut.mul_apply, MulAut.mul_apply, hψ, hα, hψinv, ← hβ, map_mul, map_mul, map_inv, hxh']
  group

theorem odd_triality_field_coset_involution_fixed_p_components
    {r : ℕ} (hr : IsPrimePow r)
    (hro : Odd r) (K : Type) [Field K] [Finite K] (hK : Nat.card K = r ^ 6) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (r ^ 2)) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (r ^ 3))
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hα2 : (MulAut.conj g * fieldActor σ δ) ^ 2 = 1) :
    (∀ u, ((fieldActor σ δ u : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = Units.map (entrywiseHom δ.toRingHom) u) ∧
    (∃ ψ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      ψ * (MulAut.conj g * fieldActor σ δ) * ψ⁻¹ = fieldActor σ δ) ∧
    ∀ p : ℕ, p.Prime → ∀ J : Subgroup (fixedSubgroup (MulAut.conj g * fieldActor σ δ)),
      CFSG.IsPComponent p J → CFSG.IsQuasisimple J := by
  classical
  obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff r).1 hr
  have : Fact p.Prime := ⟨hp⟩
  set f := 2 * a with hfdef
  have hf : 1 ≤ f := by omega
  have hodd : Odd (p ^ f) := by rw [hfdef, pow_mul']; exact hro.pow
  have hK3 : Nat.card K = (p ^ f) ^ 3 := by rw [hK, hfdef, ← pow_mul, ← pow_mul]; ring_nf
  have hK6 : Nat.card K = p ^ (6 * a) := by rw [hK, ← pow_mul, mul_comm]
  have hσf : ∀ c, σ c = c ^ (p ^ f) := fun c => by rw [hσ, hfdef, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK6
  have hp2 : p ≠ 2 := fun h2 => by
    rw [h2] at hro
    exact (Nat.not_even_iff_odd.2 hro) (even_two.pow_of_ne_zero (by omega))
  have hKc : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨hcoe, -, -, -, -, hder, -, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK3 σ hσf
  set L := AlgebraicClosure K
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  set ι := algebraMap K L
  set Fe := iterateFrobenius L p a with hFedef
  have hFe : ∀ c, Fe c = c ^ p ^ a := fun c => by rw [hFedef, iterateFrobenius_def]
  have hFr : ∀ c, (Fe.comp Fe) c = c ^ (p ^ f) := fun c => by
    rw [RingHom.comp_apply, hFe, hFe, ← pow_mul, ← pow_add, hfdef, two_mul]
  set η := iterateFrobenius K p a with hηdef
  have hη : ∀ c, η c = c ^ p ^ a := fun c => by rw [hηdef, iterateFrobenius_def]
  have hFeι : Fe.comp ι = ι.comp η := RingHom.ext fun c => by
    rw [RingHom.comp_apply, RingHom.comp_apply, hFe, hη, map_pow]
  have hδησ : δ.toRingHom = η.comp σ.toRingHom := RingHom.ext fun c => by
    change δ c = η (σ c)
    rw [hδ, hσ, hη, ← pow_mul c]
    congr 1
  obtain ⟨⟨S, hS⟩, hLangS⟩ :=
    (exceptional_Lang_root_coordinate_surjectivity p L).2.1 TwistTag.D4 a ha 2
  have hLang := hLangS S hS
  have hP3 : ∀ (M : Type) [Field M], diagramMap TwistTag.D4 M ^ 3 = 1 :=
    fun M _ => diagramMap_pow_order TwistTag.D4 M
  have hPz : diagramMap TwistTag.D4 L ^ (2 : ℤ) = diagramMap TwistTag.D4 L ^ 2 := by
    rw [zpow_ofNat]
  have hS' : ∀ g', (S g' : ModGL TwistTag.D4.tag L) = diagramMap TwistTag.D4 L ^ 2 *
      Units.map (entrywiseHom Fe) (g' : ModGL TwistTag.D4.tag L) *
        (diagramMap TwistTag.D4 L ^ 2)⁻¹ := fun g' => by rw [hS, hPz]
  have hS2 : ∀ g', ((S (S g') : adjointGroup TwistTag.D4.tag L) : ModGL TwistTag.D4.tag L) =
      twistHom TwistTag.D4 L (Fe.comp Fe) g' := fun g' => by
    rw [hS', hS', map_mul, map_mul, map_inv, map_pow, units_map_entrywiseHom_diagramMap,
      units_map_entrywiseHom_comp, twistHom_apply]
    have h4 : diagramMap TwistTag.D4 L ^ 2 * diagramMap TwistTag.D4 L ^ 2 =
        diagramMap TwistTag.D4 L := by
      rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, hP3, one_mul, pow_one]
    calc diagramMap TwistTag.D4 L ^ 2 * (diagramMap TwistTag.D4 L ^ 2 *
          Units.map (entrywiseHom (Fe.comp Fe)) (g' : ModGL TwistTag.D4.tag L) *
          (diagramMap TwistTag.D4 L ^ 2)⁻¹) * (diagramMap TwistTag.D4 L ^ 2)⁻¹ =
        (diagramMap TwistTag.D4 L ^ 2 * diagramMap TwistTag.D4 L ^ 2) *
          Units.map (entrywiseHom (Fe.comp Fe)) (g' : ModGL TwistTag.D4.tag L) *
          (diagramMap TwistTag.D4 L ^ 2 * diagramMap TwistTag.D4 L ^ 2)⁻¹ := by group
      _ = _ := by rw [h4]
  have hC0le : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≤ adjointGroup TwistTag.D4.tag K :=
    (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom).trans inf_le_left
  set ιH : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* adjointGroup TwistTag.D4.tag L :=
    (adjointBaseChangeHom TwistTag.D4.tag ι).comp (Subgroup.inclusion hC0le)
  have hιH : ∀ u, (ιH u : ModGL TwistTag.D4.tag L) = baseChangeGL ι u := fun _ => rfl
  have hFeGL : ∀ u : ModGL TwistTag.D4.tag K, Units.map (entrywiseHom Fe) (baseChangeGL ι u) =
      baseChangeGL ι (Units.map (entrywiseHom η) u) := fun u => by
    rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hFeι]
  have hβ : ∀ u, S (ιH u) = ιH (fieldActor σ δ u) := fun u => by
    apply Subtype.ext
    rw [hS', hιH, hιH, hcoe, hFeGL, ← baseChangeGL_diagramMap ι TwistTag.D4, ← map_pow,
      ← map_inv, ← map_mul, ← map_mul]
    congr 1
    have hfix : twistHom TwistTag.D4 K σ.toRingHom (u : ModGL TwistTag.D4.tag K) = u :=
      (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom u.2).2
    rw [twistHom_apply] at hfix
    have hσu : Units.map (entrywiseHom σ.toRingHom) (u : ModGL TwistTag.D4.tag K) =
        (diagramMap TwistTag.D4 K)⁻¹ * u * diagramMap TwistTag.D4 K := by
      calc Units.map (entrywiseHom σ.toRingHom) (u : ModGL TwistTag.D4.tag K) =
          (diagramMap TwistTag.D4 K)⁻¹ * (diagramMap TwistTag.D4 K *
            Units.map (entrywiseHom σ.toRingHom) (u : ModGL TwistTag.D4.tag K) *
              (diagramMap TwistTag.D4 K)⁻¹) * diagramMap TwistTag.D4 K := by group
        _ = _ := by rw [hfix]
    have hPinv : (diagramMap TwistTag.D4 K)⁻¹ = diagramMap TwistTag.D4 K ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', hP3]
    have hP2inv : (diagramMap TwistTag.D4 K ^ 2)⁻¹ = diagramMap TwistTag.D4 K := by
      rw [← hPinv, inv_inv]
    rw [hP2inv, hδησ, ← units_map_entrywiseHom_comp, hσu, map_mul, map_mul, map_inv,
      units_map_entrywiseHom_diagramMap, hPinv]
  set α := MulAut.conj g * fieldActor σ δ with hαdef
  have hα : ∀ u, ιH (α u) = ιH g * S (ιH u) * (ιH g)⁻¹ := fun u => by
    rw [hβ, hαdef, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hα2' : α * α = 1 := by rw [← sq, hα2]
  obtain ⟨ψ, hψ⟩ := exists_conj_eq_of_sq_eq_twisted_frobenius_odd TwistTag.D4 hp hf hodd K hK3
    σ.toRingHom hσf L (Fe.comp Fe) hFr S hS2 hLang ιH hιH (fieldActor σ δ) hβ (ιH g) α hα hα2'
  refine ⟨hcoe δ, ⟨ψ, hψ⟩, fun p' hp' J hJ => ?_⟩
  obtain ⟨-, ⟨e₁, -⟩, -⟩ := fixed_centralizer_of_conj_eq hψ
  set D := ⁅twistedFixedGroup TwistTag.D4 K σ.toRingHom,
    twistedFixedGroup TwistTag.D4 K σ.toRingHom⁆
  let eD : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* D := MulEquiv.subgroupCongr hder.symm
  have hcongr : MulAut.congr eD (fieldActor σ δ) = derivedEntrywiseAut TwistTag.D4 σ δ :=
    MulEquiv.ext fun x => Subtype.ext (by
      change ((fieldActor σ δ (eD.symm x) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) = _
      rw [hcoe, coe_derivedEntrywiseAut]
      rfl)
  have e₂ := CFSG.ComponentClassification.CatalogueRelativeB.fixedSubgroupEquivalence
    eD (fieldActor σ δ)
  rw [hcongr] at e₂
  have hfin : ∀ J' : Subgroup (fixedSubgroup (derivedEntrywiseAut TwistTag.D4 σ δ)),
      CFSG.IsPComponent p' J' → CFSG.IsQuasisimple J' :=
    ((odd_diagram_derived_coordinate_field_fixed_p_components TwistTag.D4 K hKc σ δ).2.2 p'
      hp').1
  exact pComponents_quasisimple_of_mulEquiv hp' (e₁.trans e₂) hfin J hJ

end CFSG.LieType.Chevalley
