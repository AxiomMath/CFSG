module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalOddTwo
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISymplectic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenUnitaryComponents
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenOrthogonalComponents
public import CFSG.LieType.Chevalley.RootLocalComponentFree
public import CFSG.LieType.Ree.LargeReeInvolutionComponentFree
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.Sporadic.Schreier.TitsComponent
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedReverse
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourWitnesses

public section

namespace CFSG.ComponentClassification.CatLeaf

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def InvolutionCentralizersComponentFree (S : Type*) [Group S] : Prop :=
  ∀ t : S, orderOf t = 2 → ∀ B : Subgroup (centralizer ({t} : Set S)), ¬ IsComponent B

theorem isComponent_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) {L : Subgroup A}
    (hL : IsComponent L) : IsComponent (L.map e.toMonoidHom) :=
  ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (L.equivMapOfInjective e.toMonoidHom e.injective)).1 hL.1,
    Subgroup.IsSubnormal.map (f := e.toMonoidHom) e.surjective hL.2⟩

theorem InvolutionCentralizersComponentFree.of_mulEquiv {S T : Type*} [Group S] [Group T]
    (e : S ≃* T) (h : InvolutionCentralizersComponentFree T) :
    InvolutionCentralizersComponentFree S := by
  intro t ht B hB
  let φ : centralizer ({t} : Set S) ≃* centralizer ({e t} : Set T) :=
    ((centralizer ({t} : Set S)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (UnbalancingLocal.map_centralizer_singleton_mulEquiv e t))
  exact h (e t) (by rw [MulEquiv.orderOf_eq]; exact ht) _ (isComponent_map_mulEquiv φ hB)

theorem involutionCentralizersComponentFree_psl {S : Type} [Group S] {n f : ℕ}
    (h : StatedClassicalModel S .PSL n 2 f) : InvolutionCentralizersComponentFree S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 2 ≤ n := h.1.2.2.1
  have hf : 1 ≤ f := h.1.2.1
  obtain ⟨-, ⟨θ⟩⟩ := ClassicalModelStatedBridge.classicalModel_psl_of_stated h
  exact InvolutionCentralizersComponentFree.of_mulEquiv
    (θ.trans (LocalAnalysis.ComponentInitial.LinearFieldFour.pslModelEquivProjectiveSL n 2 f))
    fun t ht B => OutcomeLocal.even_linear_involution_centralizers_component_free hf hn
      (GaloisField.card 2 f (by omega)) t ht B

theorem involutionCentralizersComponentFree_psu {S : Type} [Group S] {n f : ℕ}
    (h : StatedClassicalModel S .PSU n 2 f) : InvolutionCentralizersComponentFree S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 3 ≤ n := h.1.2.2.1
  have hq3 : (n, 2 ^ f) ≠ (3, 2) := h.1.2.2.2
  obtain ⟨⟨-, hf, -, -⟩, ⟨θ⟩⟩ := ClassicalModelStatedBridge.classicalModel_psu_of_stated h
  let hU := CatalogueBUnitaryB.galoisField_unitaryFieldData 2 f hf
  let psi : S ≃* ClassicalGroups.UnitaryFlag.unitaryPSU hU n :=
    (θ.trans (ClassicalModelStatedBridge.psuModelEquiv n 2 f)).trans
      (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega : 1 ≤ n)).symm
  exact InvolutionCentralizersComponentFree.of_mulEquiv psi fun t ht B =>
    UnbalancingLocal.even_unitary_involution_centralizers_component_free hU hn
      (fun ⟨h1, h2⟩ => hq3 (by rw [h1, h2])) t ht B

theorem involutionCentralizersComponentFree_psp {S : Type} [Group S] {n f : ℕ}
    (h : StatedClassicalModel S .PSp n 2 f) : InvolutionCentralizersComponentFree S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 2 ≤ n := h.1.2.2.1
  obtain ⟨⟨-, hf, -, -⟩, ⟨θ⟩⟩ := ClassicalModelStatedBridge.classicalModel_psp_of_stated h
  exact InvolutionCentralizersComponentFree.of_mulEquiv
    (θ.trans (ClassicalModelStatedBridge.pspModelEquiv n 2 f)) fun t ht B =>
      OutcomeLocal.even_symplectic_involution_centralizers_component_free hf (by omega)
        (GaloisField.card 2 f (by omega)) t ht B

theorem involutionCentralizersComponentFree_orthogonal {S : Type} [Group S] {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {n f : ℕ} (h : StatedClassicalModel S t n 2 f) :
    InvolutionCentralizersComponentFree S := by
  have hn : 4 ≤ n := by rcases ht with rfl | rfl <;> exact h.1.2.2
  exact fun u hu B => UnbalancingLocal.even_orthogonal_involution_centralizers_component_free ht
    hn h.1.2.1 h u hu B

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem involutionCentralizersComponentFree_rootWeightDatum {K : Type} [Field K] [Finite K]
    [CharP K 2] (D : RootWeightDatum K) : InvolutionCentralizersComponentFree D.group := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro t ht B hB
  have hQp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ht, pow_one])
  have hQ : zpowers t ≠ ⊥ := by
    intro h
    have h1 : t = 1 := by
      rw [← mem_bot, ← h]
      exact mem_zpowers t
    rw [h1, orderOf_one] at ht
    norm_num at ht
  obtain ⟨-, hno⟩ :=
    D.defining_characteristic_root_local_groups_component_free 2 (zpowers t) hQp hQ _ (.inr rfl)
  exact hno _ (isComponent_map_mulEquiv
    (MulEquiv.subgroupCongr (UnbalancedLayer.centralizer_zpowers_eq t).symm) hB)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem involutionCentralizersComponentFree_adjointGroup {τ : Tag} {f : ℕ} (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) :
    InvolutionCentralizersComponentFree (adjointGroup τ K) := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact involutionCentralizersComponentFree_rootWeightDatum (RootWeightDatum.ordinary τ)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem involutionCentralizersComponentFree_graphFixedRootGroup (t : TwistTag) {f : ℕ}
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ t.order)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    InvolutionCentralizersComponentFree (graphFixedRootGroup t K σ.toRingHom) := by
  obtain ⟨σ', hσ', hord, -⟩ := finite_graph_field_parameter_fields t Nat.prime_two hf K hK
  have hσσ' : σ = σ' := RingEquiv.ext fun c => by rw [hσ, hσ']
  have hσo : σ ^ t.order = 1 := by
    rw [hσσ', ← hord]
    exact pow_orderOf_eq_one σ'
  have hm := t.order_pos
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))
      (show Nat.card K = 2 ^ (f * t.order) by rw [hK, ← pow_mul])
  exact involutionCentralizersComponentFree_rootWeightDatum (RootWeightDatum.fixed t σ hσo)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem involutionCentralizersComponentFree_exceptional {S : Type} [Group S] {t : StatedLieTag}
    (ht : t ∈ chevalleyExceptionalTags) {f : ℕ} (h : ChevalleyExceptionalModel S t 2 f) :
    InvolutionCentralizersComponentFree S := by
  have hf : 1 ≤ f := h.1.2.1
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 h.2
    exact .of_mulEquiv e (involutionCentralizersComponentFree_adjointGroup hf hK)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 h.2
    exact .of_mulEquiv e (involutionCentralizersComponentFree_adjointGroup hf hK)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 h.2
    exact .of_mulEquiv e (involutionCentralizersComponentFree_adjointGroup hf hK)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 h.2
    exact .of_mulEquiv e (involutionCentralizersComponentFree_adjointGroup hf hK)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 h.2
    exact .of_mulEquiv e (involutionCentralizersComponentFree_adjointGroup hf hK)
  · obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 Nat.prime_two hf h.2
    exact .of_mulEquiv e (involutionCentralizersComponentFree_graphFixedRootGroup _ hf hK σ hσ)
  · obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 Nat.prime_two hf h.2
    exact .of_mulEquiv e (involutionCentralizersComponentFree_graphFixedRootGroup _ hf hK σ hσ)

theorem involutionCentralizersComponentFree_suzuki {S : Type} [Group S] {f : ℕ}
    (h : SuzukiModel S 2 f) : InvolutionCentralizersComponentFree S := by
  obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := h
  exact .of_mulEquiv e fun t ht B =>
    Sporadic.Schreier.Tits.CTI_Suzuki_Tits_involution_centralizers_component_free.1 a K
      (by rw [hK, hf]) t ht B

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag in
theorem involutionCentralizersComponentFree_reeTits {S : Type} [Group S] {t : StatedLieTag}
    (ht : t = .twistedF4 ∨ t = .Tits) {f : ℕ} (h : ReeTitsModel S t 2 f) :
    InvolutionCentralizersComponentFree S := by
  rcases ht with rfl | rfl
  · obtain ⟨-, -, -, -, -, hiso⟩ := large_Ree_model_Schreier _ 2 f h
    obtain ⟨hadm, a, hfa, K, _, _, hK, hw⟩ := h
    have : CharP K F4.prime :=
      LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (by omega) hK
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
    have hf3 : 3 ≤ f := hadm.2.2.2.2.2
    obtain ⟨e⟩ := hiso a K hfa hK hw
    exact .of_mulEquiv e
      (LargeReeInvolution.large_Ree_involution_centralizers_component_free a (by omega) K hK').1
  · obtain ⟨e⟩ := Sporadic.Schreier.Tits.titsModelEquiv _ 2 f h
    exact .of_mulEquiv e Sporadic.Schreier.Tits.titsD_involution_centralizer_component_free

theorem involutionCentralizersComponentFree_of_evenLieType {S : Type} [Group S]
    (h : EvenLieType S) : InvolutionCentralizersComponentFree S := by
  obtain ⟨t, n, f, hadm, hm⟩ := h
  rcases hm with ⟨ht, hcl⟩ | ⟨-, ht, hex⟩ | ⟨-, ht, hrt⟩ | ⟨-, rfl, hsz⟩
  · simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact involutionCentralizersComponentFree_psl hcl
    · exact involutionCentralizersComponentFree_psu hcl
    · exact involutionCentralizersComponentFree_psp hcl
    · exact absurd rfl hcl.1.2.2.2
    · exact involutionCentralizersComponentFree_orthogonal (.inl rfl) hcl
    · exact involutionCentralizersComponentFree_orthogonal (.inr rfl) hcl
  · exact involutionCentralizersComponentFree_exceptional ht hex
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact absurd hadm.2.2.2.1 (by norm_num)
    · exact involutionCentralizersComponentFree_reeTits (.inl rfl) hrt
    · exact involutionCentralizersComponentFree_reeTits (.inr rfl) hrt
  · exact involutionCentralizersComponentFree_suzuki hsz

end CFSG.ComponentClassification.CatLeaf
