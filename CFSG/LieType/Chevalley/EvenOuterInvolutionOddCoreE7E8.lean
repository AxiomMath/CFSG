module

public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
public import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenGraphField

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.UnbalancedCatalog (EvenCatalog.oddCore_eq_bot_of_mulEquiv
  EvenCatalog.oddCore_eq_bot_of_normal_of_centralizer EvenCatalog.centralizerConjEquivMap
  EvenCatalog.inner_le_map_conj EvenCatalog.oddCore_eq_bot_of_isSimpleGroup)

theorem oddCore_inf_centralizer_entrywiseAdjointAut_E7_E8
    (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8)
    {e : ℕ} (he : 1 ≤ e) (K : Type) [Field K] (hK : Nat.card K = 2 ^ (2 * e)) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ e) (H : Subgroup (MulAut (adjointGroup τ K)))
    (hIH : inner (adjointGroup τ K) ≤ H) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {entrywiseAdjointAut τ σ}) = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  have : Finite (MulAut (adjointGroup τ K)) :=
    Finite.of_injective (fun β : MulAut (adjointGroup τ K) =>
      (β : adjointGroup τ K → adjointGroup τ K)) fun _ _ h => MulEquiv.ext (congrFun h)
  obtain ⟨-, -, hJC, -, ⟨hJfin, hJsimple, hJeven, -, -⟩, ⟨ι, -⟩, -, -, hNδ, hNnorm, hcent⟩ :=
    even_E7_E8_canonical_field_full_centralizer τ hτ he K hK σ hσ
  have hσ' : ∀ c, σ c = c ^ 2 ^ (2 * e / 2) := fun c => by
    rw [hσ, show 2 * e / 2 = e by omega]
  obtain ⟨hσσ, -, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.mem_zpowers_of_forall_fixed
      (by omega) ⟨e, two_mul e⟩ hK hσ'
  set N := ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map MulAut.conj with hN
  have hNcore : CFSG.oddCore N = ⊥ := by
    have hJcore := @EvenCatalog.oddCore_eq_bot_of_isSimpleGroup _ _ hJfin hJsimple hJeven
    exact EvenCatalog.oddCore_eq_bot_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hJC).symm.trans ι) hJcore
  have hδ2 : entrywiseAdjointAut τ σ * entrywiseAdjointAut τ σ = 1 := by
    rw [← entrywiseAdjointAut_mul, hσσ, entrywiseAdjointAut_one]
  refine EvenCatalog.oddCore_eq_bot_of_normal_of_centralizer (R := N) ?_ ?_ hNcore ?_
  · intro n hn
    refine Subgroup.mem_inf.2 ⟨hIH ?_, hNδ hn⟩
    obtain ⟨j, -, rfl⟩ := hn
    exact ⟨j, rfl⟩
  · intro c hc n hn
    have h := hNnorm.conj_mem ⟨n, hNδ hn⟩ (Subgroup.mem_subgroupOf.2 hn)
      ⟨c, (Subgroup.mem_inf.1 hc).2⟩
    exact Subgroup.mem_subgroupOf.1 h
  · intro c hc hcN
    have hc' : c ∈ Subgroup.centralizer {entrywiseAdjointAut τ σ} ⊓
        Subgroup.centralizer (N : Set (MulAut (adjointGroup τ K))) :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hc).2,
        Subgroup.mem_centralizer_iff.2 fun n hn => (hcN n hn).symm⟩
    rw [hcent] at hc'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
    refine ⟨1, ?_⟩
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, Nat.cast_ofNat, zpow_two, hδ2,
      one_zpow]

theorem even_E7_E8_outer_involution_full_centralizer_odd_core
    (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f)
    (H : Subgroup (MulAut (adjointGroup τ K))) (hIH : inner (adjointGroup τ K) ≤ H)
    {α : MulAut (adjointGroup τ K)} (hαI : α ∉ inner (adjointGroup τ K)) (hα : orderOf α = 2) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  obtain ⟨hNF, Θ, hΘ, -, hker, hinv⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF α
  have hΘα : Θ α = σ := hΘ α g σ hgσ
  have hσ1 : Θ α ≠ 1 := fun h1 => hαI (by
    rw [← MonoidHom.mem_ker, hker] at h1
    exact h1)
  obtain ⟨⟨e, he⟩, hσc⟩ := (hinv α hα2).resolve_left hσ1
  rw [hΘα] at hσc
  have he1 : 1 ≤ e := by omega
  have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
  have hσ' : ∀ c, σ c = c ^ 2 ^ e := fun c => by rw [hσc, show f / 2 = e by omega]
  obtain ⟨hQ1, -⟩ :=
    even_exceptional_quadratic_field_graph_field_involution_descent he1 K hK' σ.toRingHom hσ'
  obtain ⟨β, -, hdesc⟩ := hQ1 τ
  obtain ⟨-, hdα⟩ := hdesc g fun _ => 1
  have hαform : ∀ u, (α u : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ (fun _ => 1) *
      Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K) * (rootDiagUnit τ fun _ => 1)⁻¹ *
        (g : ModGL τ K)⁻¹ := by
    intro u
    rw [show (fun _ => (1 : Kˣ)) = (1 : Fin τ.rank → Kˣ) from rfl, rootDiagUnit_one, mul_one,
      inv_one, mul_one]
    exact hgσ u
  obtain ⟨ψ, hψ, -⟩ := hdα α hαform (by rw [← pow_two]; exact hα2)
  have hψα : ψ * α * ψ⁻¹ = entrywiseAdjointAut τ σ :=
    MulEquiv.ext fun u => Subtype.ext (by rw [hψ u, coe_entrywiseAdjointAut])
  have hα' : α = ψ⁻¹ * entrywiseAdjointAut τ σ * ψ⁻¹⁻¹ := by
    rw [← hψα]
    group
  rw [hα']
  exact EvenCatalog.oddCore_eq_bot_of_mulEquiv
    (EvenCatalog.centralizerConjEquivMap H ψ⁻¹ (entrywiseAdjointAut τ σ)).symm
    (oddCore_inf_centralizer_entrywiseAdjointAut_E7_E8 τ hτ he1 K hK' σ hσ' _
      (EvenCatalog.inner_le_map_conj hIH ψ⁻¹))

end CFSG.LieType.Chevalley
