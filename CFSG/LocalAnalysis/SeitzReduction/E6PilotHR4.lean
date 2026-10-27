module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4Model
public import CFSG.LieType.Chevalley.CLSEvenE6AllInvolutionFourGroup

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.LieType.Chevalley.E6GraphFullCoset (IsOrdinaryDiagGraph)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.SeitzReduction.F4Pilot (PerfectTwistedFusion PerfectTwistedFusion.of_conj
  exists_conj_ne_mem_sup_zpowers_of_fusion forall_perfectTwistedFusion_of_mulEquiv
  exists_eq_or_eq_mul_of_mem_sup_zpowers kernel orderOf_mul_eq_two_of_commute)


theorem perfectTwistedFusion_of_outer_E6 {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup .E6 K)) (hα : α ^ 2 = 1)
    (hαo : α ∉ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range) :
    PerfectTwistedFusion α := by
  change MulAut (adjointGroup TwistTag.E6.tag K) at α
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨Θ, -, hΘ, -, hinv, hfield⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K
  obtain ⟨-, -, hex⟩ := ordinary_E_exact_automorphism_normal_form TwistTag.E6.tag (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hga⟩ := hex α
  have hΘα := hΘ α g a σ ε hga
  have hε2 : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have := ε.isLt
    change (ε : ℕ) < 2 at this
    omega
  by_cases hσ1 : σ = 1
  · subst hσ1
    rcases hε2 with h0 | h1
    ·
      exfalso
      refine hαo (EvenE6AllInvolution.mem_inner_of_conj_mul_rootDiagAut (τ := TwistTag.E6.tag)
        hK hf g a ?_ hα)
      refine MulEquiv.ext fun h => Subtype.ext ?_
      have e1 : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom)
          (h : ModGL TwistTag.E6.tag K) = h := Units.ext (entrywise_id _)
      rw [hga h, h0, exactQ_zero, e1, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_inv, coe_rootDiagAut]
      group
    ·
      obtain ⟨ht, η, hη, hconj, hiff, -, -⟩ :=
        (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).1 K hK
      have hdiag : IsOrdinaryDiagGraph K α := by
        rw [hiff Θ hΘ, hΘα, h1, Nat.cast_one]
      rcases hconj α hdiag hα with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
      · exact PerfectTwistedFusion.of_conj hφ (perfectTwistedFusion_graph_E6 η hη)
      · exact PerfectTwistedFusion.of_conj hφ (perfectTwistedFusion_secondGraph_E6 ht η hη)
  ·
    have hσ2 : σ ^ 2 = 1 := hinv α g a σ ε hga hα
    have hσσ : ∀ c, σ (σ c) = c := fun c => by
      have h := congrArg (fun φ : K ≃+* K => φ c) hσ2
      simpa only [pow_two, RingAut.mul_apply, RingAut.one_apply] using h
    have hσne : ∃ c, σ c ≠ c := by
      by_contra! h
      exact hσ1 (RingEquiv.ext h)
    obtain ⟨⟨e, he⟩, hσc, -⟩ := hfield 2 f Nat.prime_two hf hK σ hσ2 hσ1
    have he1 : 1 ≤ e := by omega
    have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
    have hσ' : ∀ c, σ c = c ^ 2 ^ e := fun c => by rw [hσc, show f / 2 = e by omega]
    obtain ⟨hQ1, hQP⟩ :=
      even_exceptional_quadratic_field_graph_field_involution_descent he1 K hK' σ.toRingHom hσ'
    rcases hε2 with h0 | h1
    ·
      obtain ⟨_, -, hdesc⟩ := hQ1 TwistTag.E6.tag
      obtain ⟨-, hdα⟩ := hdesc g a
      have hαform : ∀ u, (α u : ModGL TwistTag.E6.tag K) = (g : ModGL TwistTag.E6.tag K) *
          rootDiagUnit TwistTag.E6.tag a * Units.map (entrywiseHom σ.toRingHom)
            (u : ModGL TwistTag.E6.tag K) * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
              (g : ModGL TwistTag.E6.tag K)⁻¹ := by
        intro u
        rw [hga u, h0, exactQ_zero, mul_one, inv_one, mul_one]
      obtain ⟨ψ, hψ, -⟩ := hdα α hαform (by rw [← pow_two]; exact hα)
      have hφ : ψ * α * ψ⁻¹ = entrywiseAdjointAut TwistTag.E6.tag σ :=
        MulEquiv.ext fun u => Subtype.ext (by rw [hψ u, coe_entrywiseAdjointAut])
      exact PerfectTwistedFusion.of_conj hφ (perfectTwistedFusion_field_E6 σ hσσ hσne)
    ·
      obtain ⟨_, -, hdesc⟩ := hQP
      obtain ⟨-, hdα⟩ := hdesc g a
      have hαform : ∀ u, (α u : ModGL TwistTag.E6.tag K) = (g : ModGL TwistTag.E6.tag K) *
          rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 K *
            Units.map (entrywiseHom σ.toRingHom) (u : ModGL TwistTag.E6.tag K) *
              (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
                (g : ModGL TwistTag.E6.tag K)⁻¹ := by
        intro u
        rw [hga u, h1]
        rfl
      obtain ⟨ψ, hψ, -⟩ := hdα α hαform (by rw [← pow_two]; exact hα)
      have hφ : ψ * α * ψ⁻¹ =
          diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ :=
        MulEquiv.ext fun u => Subtype.ext (by
          rw [hψ u, MulAut.mul_apply, coe_diagramConjAut, coe_entrywiseAdjointAut])
      exact PerfectTwistedFusion.of_conj hφ (perfectTwistedFusion_graphField_E6 σ hσσ)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_ne_mem_sup_zpowers_E6 (hset : StandardSetting G L) {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ g : G, g⁻¹ * t * g ≠ t ∧ g⁻¹ * t * g ∈ L ⊔ zpowers t := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hOut : Group.IsSolvable (Outer L) :=
    ⟨⟨3, derivedSeries_outer_eq_bot_of_mulEquiv e (exceptional_E_pinned_model_Schreier K).1⟩⟩
  exact exists_conj_ne_mem_sup_zpowers_of_fusion hset hOut
    (forall_perfectTwistedFusion_of_mulEquiv e (perfectTwistedFusion_of_outer_E6 hf K hK)) ht hKt

theorem exists_conj_eq_or_eq_mul_involution_E6 (hset : StandardSetting G L) {f : ℕ}
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ g : G, ∃ y ∈ L, orderOf y = 2 ∧ g⁻¹ * t * g ≠ t ∧
      (g⁻¹ * t * g = y ∨ g⁻¹ * t * g = t * y) := by
  have htC : t ∈ centralizer (L : Set G) :=
    (show t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) from hKt ▸ mem_zpowers t).1
  obtain ⟨g, hne, hmem⟩ := exists_conj_ne_mem_sup_zpowers_E6 hset hf K hK e ht hKt
  obtain ⟨y, hyL, hy⟩ := exists_eq_or_eq_mul_of_mem_sup_zpowers ht htC hmem
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hso : orderOf (g⁻¹ * t * g) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, ht]
  refine ⟨g, y, hyL, ?_, hne, hy⟩
  rcases hy with h | h
  · rw [← h, hso]
  ·
    have hs2 : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
      calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [ht2, mul_one, inv_mul_cancel]
    have hc : (g⁻¹ * t * g) * t = t * (g⁻¹ * t * g) := by
      rw [h, mul_assoc, ← mem_centralizer_iff.1 htC y hyL]
    have hy' : y = t * (g⁻¹ * t * g) := by
      rw [h, ← mul_assoc, ht2, one_mul]
    rw [hy']
    exact orderOf_mul_eq_two_of_commute ht2 hs2 hc hne

theorem exists_involution_conj_ne_mem_sup_zpowers_E6 (hset : StandardSetting G L) {f : ℕ}
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K)
    (hI : HypothesisOne (L ⧸ center L)) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ centralizer (L : Set G) ∧
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ∧
      ∃ g : G, g⁻¹ * t * g ≠ t ∧ g⁻¹ * t * g ∈ L ⊔ zpowers t := by
  have hZ : center L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ center (adjointGroup .E6 K) := (MulEquivClass.apply_mem_center_iff e).2 hz
    rw [center_adjointGroup_eq_bot_field, mem_bot] at hz'
    exact mem_bot.2 (e.injective (hz'.trans (map_one e).symm))
  obtain ⟨t, ht, htC, -, hKt, -⟩ := kernel hset hZ hI
  exact ⟨t, ht, htC, hKt, exists_conj_ne_mem_sup_zpowers_E6 hset hf K hK e ht hKt⟩

end CFSG.SeitzReduction.E6Pilot
