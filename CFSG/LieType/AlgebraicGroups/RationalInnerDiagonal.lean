module

public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
public import CFSG.LieType.AlgebraicGroups.InnerInvolutionTorus
public import CFSG.LieType.Chevalley.OddToralInvolutionFixedComponents
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped CFSG.ConvolutionPoints

section Transport

variable {τ : Tag}

theorem map_baseChangeGL_toralCentralizer
    {K L : Type} [Field K] [Field L] (ι : K →+* L)
    (b : Fin τ.rank → Kˣ) :
    (toralCentralizer τ K b).map (baseChangeGL ι) =
      (adjointGroup τ K).map (baseChangeGL ι) ⊓
        Subgroup.centralizer {rootDiagUnit τ fun i => Units.map ι.toMonoidHom (b i)} := by
  rw [← baseChangeGL_rootDiagUnit]
  ext y
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hgG, hgc⟩ := mem_toralCentralizer.1 hg
    refine ⟨⟨g, hgG, rfl⟩, ?_⟩
    rw [← map_mul, ← map_mul]
    congr 1
    calc g * rootDiagUnit τ b = (rootDiagUnit τ b * g * (rootDiagUnit τ b)⁻¹) *
        rootDiagUnit τ b := by rw [hgc]
      _ = rootDiagUnit τ b * g := by group
  · rintro ⟨⟨g, hgG, rfl⟩, hc⟩
    refine ⟨g, mem_toralCentralizer.2 ⟨hgG, ?_⟩, rfl⟩
    rw [← map_mul, ← map_mul] at hc
    have hc' := baseChangeGL_injective ι hc
    calc rootDiagUnit τ b * g * (rootDiagUnit τ b)⁻¹ =
        (g * rootDiagUnit τ b) * (rootDiagUnit τ b)⁻¹ := by rw [← hc']
      _ = g := by group

end Transport

section Main

variable (τ : Tag) (K : Type) [Field K] [Finite K] (L : Type) [Field L] [Algebra K L]
  [IsAlgClosure K L]

theorem G2_F4_E6_E8_rational_inner_diagonal_involution_fixed_p_components
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) (hK : Odd (Nat.card K)) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {x : ModGL τ L}
    (hx : x ∈ adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _))
    (hx2 : x ^ 2 = 1) :
    ∃ h ∈ adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _),
      ∃ a : Fin τ.rank → Lˣ, (∀ i, a i = 1 ∨ a i = -1) ∧
        h * x * h⁻¹ = rootDiagUnit τ a ∧
        ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).map
            (MulAut.conj h).toMonoidHom = (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) ∧
        ((adjointGroup τ K).map (baseChangeGL (algebraMap K L)) ⊓
            Subgroup.centralizer {x}).map (MulAut.conj h).toMonoidHom =
          (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) ⊓
            Subgroup.centralizer {rootDiagUnit τ a} ∧
        ∀ ℓ : ℕ, ℓ.Prime → ∀ M : Subgroup ↥((adjointGroup τ K).map
            (baseChangeGL (algebraMap K L)) ⊓ Subgroup.centralizer {x}),
          CFSG.IsPComponent ℓ M → CFSG.IsQuasisimple M := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set H := (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) with hH
  set p := ringChar K with hp_def
  have hpK : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro h2
    rw [Nat.card_eq_fintype_card, hcard, h2] at hK
    exact Nat.not_even_iff_odd.2 hK ((Nat.even_pow' n.ne_zero).2 even_two)
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hFr' : Fr = iterateFrobenius L p n := RingHom.ext fun c => by
    rw [hFr, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  subst hFr'
  obtain ⟨hxG, hxF⟩ := Subgroup.mem_inf.1 hx
  change entrywiseFrobGL τ L p n x = x at hxF
  obtain ⟨g, hg, a, ha, hgx⟩ := exceptional_Lang_inner_involution_torus_conjugacy τ hp2 L hxG hx2
  have hFt : entrywiseFrobGL τ L p n (rootDiagUnit τ a) = rootDiagUnit τ a :=
    entrywiseFrobGL_rootDiagUnit p n ha
  have hFgx : entrywiseFrobGL τ L p n g * x * (entrywiseFrobGL τ L p n g)⁻¹ =
      rootDiagUnit τ a := by
    rw [← hFt, ← hgx, map_mul, map_mul, map_inv, hxF]
  have hc : g * (entrywiseFrobGL τ L p n g)⁻¹ ∈ toralCentralizer τ L a := by
    refine mem_toralCentralizer.2 ⟨mul_mem hg (inv_mem (entrywiseFrobGL_mem p n hg)), ?_⟩
    calc rootDiagUnit τ a * (g * (entrywiseFrobGL τ L p n g)⁻¹) * (rootDiagUnit τ a)⁻¹ =
        (g * x * g⁻¹) * (g * (entrywiseFrobGL τ L p n g)⁻¹) * (rootDiagUnit τ a)⁻¹ := by
          rw [hgx]
      _ = g * (entrywiseFrobGL τ L p n g)⁻¹ *
          (entrywiseFrobGL τ L p n g * x * (entrywiseFrobGL τ L p n g)⁻¹) *
            (rootDiagUnit τ a)⁻¹ := by group
      _ = g * (entrywiseFrobGL τ L p n g)⁻¹ := by rw [hFgx]; group
  obtain ⟨-, hLang⟩ := connected_exceptional_toral_centralizer_Lang p hp2 L τ hτ a ha
  obtain ⟨-, -, -, hz⟩ := hLang n n.pos
  obtain ⟨z, hzZ, hzc⟩ := hz _ hc
  change z⁻¹ * entrywiseFrobGL τ L p n z = g * (entrywiseFrobGL τ L p n g)⁻¹ at hzc
  set h := z * g with hh_def
  have hzG : z ∈ adjointGroup τ L := (mem_toralCentralizer.1 hzZ).1
  have hFh : entrywiseFrobGL τ L p n h = h := by
    have hFz : entrywiseFrobGL τ L p n z = z * (g * (entrywiseFrobGL τ L p n g)⁻¹) := by
      rw [← hzc]
      group
    rw [hh_def, map_mul, hFz]
    group
  have hhR : h ∈ adjointGroup τ L ⊓ (Units.map (entrywiseHom (iterateFrobenius L p n))).eqLocus
      (MonoidHom.id _) := Subgroup.mem_inf.2 ⟨mul_mem hzG hg, hFh⟩
  have hzt : z * rootDiagUnit τ a * z⁻¹ = rootDiagUnit τ a := by
    have hzc' := (mem_toralCentralizer.1 hzZ).2
    calc z * rootDiagUnit τ a * z⁻¹ =
        (rootDiagUnit τ a * z * (rootDiagUnit τ a)⁻¹) * rootDiagUnit τ a * z⁻¹ := by rw [hzc']
      _ = rootDiagUnit τ a := by group
  have hhx : h * x * h⁻¹ = rootDiagUnit τ a := by
    calc h * x * h⁻¹ = z * (g * x * g⁻¹) * z⁻¹ := by rw [hh_def]; group
      _ = rootDiagUnit τ a := by rw [hgx, hzt]
  obtain ⟨-, -, hRN, -⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group τ K hK L
    (iterateFrobenius L p n) (fun c => by
      rw [iterateFrobenius_def, Nat.card_eq_fintype_card, hcard])
  have hHh : H.map (MulAut.conj h).toMonoidHom = H := map_conj_eq_of_mem_normalizer (hRN hhR)
  have hCh : (H ⊓ Subgroup.centralizer {x}).map (MulAut.conj h).toMonoidHom =
      H ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj h).injective, hHh,
      CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton, hhx]
  refine ⟨h, hhR, a, ha, hhx, hHh, hCh, fun ℓ hℓ M hM => ?_⟩
  set b : Fin τ.rank → Kˣ := fun i => if a i = 1 then 1 else -1 with hb_def
  have hb : ∀ i, b i = 1 ∨ b i = -1 := fun i => by
    by_cases h1 : a i = 1 <;> simp [hb_def, h1]
  have hab : (fun i => Units.map (algebraMap K L).toMonoidHom (b i)) = a := by
    funext i
    by_cases h1 : a i = 1
    · simp [hb_def, h1]
    · have h2 : a i = -1 := (ha i).resolve_left h1
      rw [h2]
      simp only [hb_def, h1, ↓reduceIte]
      exact Units.ext (by simp)
  have hXK := map_baseChangeGL_toralCentralizer (algebraMap K L) b
  rw [hab] at hXK
  have e1 : ↥(H ⊓ Subgroup.centralizer {x}) ≃* ↥(H ⊓ Subgroup.centralizer {rootDiagUnit τ a}) :=
    ((MulAut.conj h).subgroupMap _).trans (MulEquiv.subgroupCongr hCh)
  have e2 : ↥(toralCentralizer τ K b) ≃* ↥(H ⊓ Subgroup.centralizer {rootDiagUnit τ a}) :=
    (Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective (algebraMap K L))).trans
      (MulEquiv.subgroupCongr hXK)
  have hKodd : Odd (Nat.card K) := hK
  exact OddToralFixed.pComponent_quasisimple_of_mulEquiv (e1.trans e2.symm)
    (odd_toral_involution_fixed_p_components τ K hKodd b hb ℓ hℓ) M hM

end Main

end CFSG.LieType.AlgebraicGroups
