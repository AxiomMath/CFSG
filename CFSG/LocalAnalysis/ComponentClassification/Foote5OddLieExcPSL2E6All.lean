module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2E6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6GraphMain

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc
open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.SteinbergCE
  CFSG.LocalAnalysis.SteinbergCE.E6GraphCoset CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.CatLeaf
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootDiag)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Chevalley.E6SignedGraph (rootGenerated)
open CFSG.ComponentClassification.Burgoyne.X10

variable {K : Type} [Field K]

@[expose] def E6GraphNoPSL2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    ∀ (α : MulAut (adjointGroup TwistTag.E6.tag K)) (g : adjointGroup TwistTag.E6.tag K)
      (a : Fin TwistTag.E6.tag.rank → Kˣ),
      (∀ h : adjointGroup TwistTag.E6.tag K, (α h : ModGL TwistTag.E6.tag K) =
        (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
          diagramMap TwistTag.E6 K * (h : ModGL TwistTag.E6.tag K) *
            (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
              (g : ModGL TwistTag.E6.tag K)⁻¹) → orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → NoPSL2Odd L

theorem noPSL2Odd_graphFixedRootGroup_E6_id
    (hO : LieOrderFormulasInput) [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    NoPSL2Odd ↥(graphFixedRootGroup TwistTag.E6 K (RingHom.id K)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  exact noPSL2Odd_of_lieModel hO hp2 (by unfold ExcCompTag; decide) (by decide)
    (show StatedLieAdmissible .F4 0 p f from ⟨hp, hf, rfl⟩)
    (graphFixedRootGroup_E6_id_recognition hp2 hK).2

theorem noPSL2Odd_rootGenerated
    (hO : LieOrderFormulasInput) [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : NoPSL2Odd ↥(rootGenerated K) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  exact noPSL2Odd_of_lieModel hO hp2 (by unfold ExcCompTag; decide) (by decide)
    (show StatedLieAdmissible .PSp 4 p f from ⟨hp, hf, by norm_num, fun h => by simp at h⟩)
    (rootGenerated_recognition hp hp2 hK).2

theorem noPSL2Odd_rationalRootGroup
    (hO : LieOrderFormulasInput) {k : Type} [Field k] (σ : k ≃+* k) [Finite (fixSubfield σ)]
    {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card (fixSubfield σ) = p ^ f)
    {AK : ModGL TwistTag.E6.tag (fixSubfield σ)}
    (hAK : AK = diagramMap TwistTag.E6 _ ∨
      AK = rootDiagUnit TwistTag.E6.tag (E6SignedGraph.signTuple _) * diagramMap TwistTag.E6 _) :
    NoPSL2Odd ↥(rationalRootGroup σ AK) := by
  let inner : Subgroup (ModGL TwistTag.E6.tag (fixSubfield σ)) :=
    (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
      graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK) ⊔
    (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
      graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK)
  let e : ↥(rationalRootGroup σ AK) ≃* ↥inner := (inner.equivMapOfInjective _
    (baseChangeGL_injective (τ := TwistTag.E6.tag) (fixSubfield σ).subtype)).symm
  refine NoPSL2Odd.of_mulEquiv e ?_
  rcases hAK with rfl | rfl
  · have hinner : (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
        graphCentralizer TwistTag.E6.tag (fixSubfield σ) (diagramMap TwistTag.E6 _)) ⊔
          (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
            graphCentralizer TwistTag.E6.tag (fixSubfield σ) (diagramMap TwistTag.E6 _)) =
        graphFixedRootGroup TwistTag.E6 (fixSubfield σ) (RingHom.id _) := by
      rw [graphFixedRootGroup, graphFixedPosUnipotent, graphFixedNegUnipotent,
        twistedFixedGroup_id_eq]
    exact NoPSL2Odd.of_mulEquiv (MulEquiv.subgroupCongr hinner)
      (noPSL2Odd_graphFixedRootGroup_E6_id hO hp hp2 hK)
  · exact noPSL2Odd_rootGenerated hO hp hp2 hK

theorem noPSL2Odd_of_isComponent_graphCosetFixed
    (hO : LieOrderFormulasInput) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (k : Type) [Field k]
    [IsAlgClosed k] [CharP k p] (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k)
    (ε : ℕ) (hε : ε = 0 ∨ ε = 1) {x : ModGL TwistTag.E6.tag k} (hx : x ∈ graphRational k p e ε)
    (hx2 : (x * diagramMap TwistTag.E6 k) ^ 2 = 1) {L : Subgroup (graphCosetFixed k p e ε x)}
    (hL : IsComponent L) : NoPSL2Odd L := by
  obtain ⟨hfin, -⟩ := E6_rational_graph_coset_fixed_components p hp he k halg ε hε
  have : Finite (graphRational k p e ε) := hfin
  have hXR : graphCosetFixed k p e ε x ≤ graphRational k p e ε :=
    inf_le_left.trans (Subgroup.commutator_le_self _)
  have : Finite (graphCosetFixed k p e ε x) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hXR)
  set L₂ := L.map (graphCosetFixed k p e ε x).subtype with hL₂
  have hLX : L₂ ≤ graphCosetFixed k p e ε x := Subgroup.map_subtype_le L
  have hsub : L₂.subgroupOf (graphCosetFixed k p e ε x) = L :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) L
  have hL₂c : Assembly.IsComponentOf L₂ (graphCosetFixed k p e ε x) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLX).2
      (by rw [hsub]; exact hL)
  obtain ⟨AK, c, hAK, hc⟩ := exists_conj_eq_rationalRootGroup p hp he k halg ε hε hx hx2
    Nat.prime_two hLX (ExcSelector.isPComponent_two_subgroupOf hL₂c)
  have : Finite (fixSubfield (iterateFrobeniusEquiv k p e)) :=
    ExcSelector.finite_fixSubfield_frobenius p he
  let e₁ : L ≃* L₂ := L.equivMapOfInjective _ (Subgroup.subtype_injective _)
  let e₂ : L₂ ≃* L₂.map (MulAut.conj c).toMonoidHom :=
    L₂.equivMapOfInjective _ (MulAut.conj c).injective
  exact NoPSL2Odd.of_mulEquiv ((e₁.trans e₂).trans (MulEquiv.subgroupCongr hc))
    (noPSL2Odd_rationalRootGroup hO _ (Fact.out : p.Prime) hp
      (card_fixSubfield_iterateFrobeniusEquiv he) hAK)

theorem e6GraphNoPSL2_holds
    (hO : LieOrderFormulasInput) : E6GraphNoPSL2 := by
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
  exact NoPSL2Odd.of_mulEquiv (L.equivMapOfInjective Φ.toMonoidHom Φ.injective)
    (noPSL2Odd_of_isComponent_graphCosetFixed hO p hp2 hf _ hk 0 (Or.inl rfl) hxR hx2
      (LocalCores.isComponent_map_mulEquiv Φ hL))

variable [Finite K]

theorem noPSL2Odd_odd_field
    (hO : LieOrderFormulasInput) {t : StatedLieTag} {τ : Tag}
    (htτ : t = .G2 ∧ τ = .G2 ∨ t = .F4 ∧ τ = .F4 ∨ t = .E6 ∧ τ = .E6 ∨ t = .E7 ∧ τ = .E7 ∨
      t = .E8 ∧ τ = .E8) {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hKe : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e))
    {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) {X : Type} [Group X] (Ψ : X ≃* fixedSubgroup α) {L : Subgroup X}
    (hL : IsComponent L) : NoPSL2Odd L := by
  obtain ⟨E⟩ := odd_field_component_equiv hp hp2 he hKe δ hδ hαg hα Ψ hL
  have hk := card_fixSubfield_of_sq_pow hp he hKe δ hδ
  have h3 := three_le_pow_of_odd_prime hp hp2 he
  have hadm : StatedLieAdmissible t 0 p e := by
    rcases htτ with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨hp, he, rfl, h3⟩
    all_goals exact ⟨hp, he, rfl⟩
  exact noPSL2Odd_of_lieModel hO hp2 (excCompTag_of_untwisted htτ)
    (fun h => absurd h.2 (by norm_num)) hadm
    (lieModel_centralQuotient_of_mulEquiv_adjointGroup htτ hadm hk E)

theorem noPSL2Odd_graphFixedRootGroup_E6
    (hO : LieOrderFormulasInput) {M : Type} [Field M] [Finite M] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hM : Nat.card M = (p ^ e) ^ 2) (σ : M ≃+* M) (hσ : ∀ c, σ c = c ^ (p ^ e)) :
    NoPSL2Odd (graphFixedRootGroup TwistTag.E6 M σ.toRingHom) := by
  have hperf := (finite_fixed_root_group_perfect TwistTag.E6 hp he M hM σ.toRingHom hσ).2.2.1
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 M σ
  obtain ⟨e'⟩ := LieType.Chevalley.nonempty_derivedCentralQuotient_equiv hperf hZ
  have hadm : StatedLieAdmissible .twistedE6 0 p e := ⟨hp, he, rfl⟩
  exact noPSL2Odd_of_lieModel hO hp2 (by unfold ExcCompTag; decide) (by decide) hadm
    (Or.inr (Or.inl ⟨rfl, by decide, hadm, M, inferInstance, inferInstance, hM, σ.toRingHom, hσ,
      ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
        e'.symm⟩⟩))

theorem noPSL2Odd_E6_explicit
    (hO : LieOrderFormulasInput) (hinner : ExcInnerNoPSL2 .E6) (hgraph : E6GraphNoPSL2)
    {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (β : MulAut (adjointGroup .E6 K))
    (hβ : orderOf β = 2) {X : Type} [Group X] (Ψ : X ≃* fixedSubgroup β) {L : Subgroup X}
    (hL : IsComponent L) : NoPSL2Odd L := by
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have hK2 : ringChar K ≠ 2 := by rw [ringChar_eq_of_card hp hf hK]; exact hp2
  have h1 : ∀ x : ModGL Tag.E6 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hQ0 : exactQ Tag.E6 K 0 = 1 := pow_zero _
  have hQ1 : exactQ Tag.E6 K 1 = diagramMap TwistTag.E6 K := pow_one _
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) K
  obtain ⟨-, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF β
  have hσ2 := hsq β g a σ ε hgaσ hβ2
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have h2 : (ε : ℕ) < 2 := ε.isLt
    omega
  by_cases hσ1 : σ = 1
  · subst hσ1
    rcases hε with hε | hε
    · refine noPSL2Odd_of_component_equiv Ψ
        (hinner K p f hp hp2 hK β g a (fun h => ?_) hβ) hL
      rw [hgaσ h, hε, hQ0, h1, mul_one, inv_one, mul_one]
    · exact noPSL2Odd_of_component_equiv Ψ (hgraph K p f hp hp2 hK β g a
        (fun h => (hgaσ h).trans (by rw [hε, hQ1, h1]; rfl)) hβ) hL
  · obtain ⟨hev, hσc, -⟩ := hquad p f hp hf hK σ hσ2 hσ1
    have he : 1 ≤ f / 2 := by
      obtain ⟨m, rfl⟩ := hev
      omega
    have hKe : Nat.card K = (p ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hK]
    rcases hε with hε | hε
    · exact noPSL2Odd_odd_field hO (t := .E6) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hp
        hp2 he hKe σ hσc (g := g) (a := a)
        (fun h => by rw [hgaσ h, hε, hQ0, mul_one, inv_one, mul_one]) hβ2 Ψ hL
    · obtain ⟨-, β', hβ', hβα⟩ :=
        exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe σ.toRingHom hσc
      obtain ⟨-, hconj⟩ := hβα g a
      obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj β (fun h => (hgaσ h).trans (by rw [hε, hQ1]; rfl))
        ((sq β).symm.trans hβ2)
      have hβfix : (fixedSubgroup β').map (adjointGroup TwistTag.E6.tag K).subtype =
          twistedFixedGroup TwistTag.E6 K σ.toRingHom := by
        ext y
        simp only [Subgroup.mem_map, twistedFixedGroup, Subgroup.mem_inf]
        constructor
        · rintro ⟨u, hu, rfl⟩
          refine ⟨u.2, ?_⟩
          change twistHom TwistTag.E6 K σ.toRingHom (u : ModGL TwistTag.E6.tag K) = u
          rw [twistHom_apply, ← hβ' u]
          exact congrArg Subtype.val hu
        · rintro ⟨hyG, hyσ⟩
          refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
          change (β' ⟨y, hyG⟩ : ModGL TwistTag.E6.tag K) = y
          rw [hβ']
          change twistHom TwistTag.E6 K σ.toRingHom y = y at hyσ
          rw [twistHom_apply] at hyσ
          exact hyσ
      let e₂ : ↥(fixedSubgroup β') ≃* ↥(twistedFixedGroup TwistTag.E6 K σ.toRingHom) :=
        (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans
          (MulEquiv.subgroupCongr hβfix)
      have hperf := (finite_fixed_root_group_perfect TwistTag.E6 hp he K hKe σ.toRingHom
        hσc).2.2.1
      have := (odd_diagram_field_fixed_p_components TwistTag.E6 K hK2 σ).1
      have hJF := graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom
      have hJsub : (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subgroupOf
          (twistedFixedGroup TwistTag.E6 K σ.toRingHom) =
          commutator (twistedFixedGroup TwistTag.E6 K σ.toRingHom) := by
        rw [← hperf, ← Subgroup.map_subtype_commutator]
        exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
      have hJn : ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subgroupOf
          (twistedFixedGroup TwistTag.E6 K σ.toRingHom)).Normal := by
        rw [hJsub]
        exact Subgroup.commutator_normal ⊤ ⊤
      have hsolv : Group.IsSolvable (twistedFixedGroup TwistTag.E6 K σ.toRingHom ⧸
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subgroupOf
            (twistedFixedGroup TwistTag.E6 K σ.toRingHom)) := by
        have : Group.IsSolvable (Abelianization (twistedFixedGroup TwistTag.E6 K σ.toRingHom)) :=
          inferInstance
        exact Group.isSolvable_of_surjective
          (f := (QuotientGroup.quotientMulEquivOfEq hJsub.symm).toMonoidHom)
          (QuotientGroup.quotientMulEquivOfEq hJsub.symm).surjective
      obtain ⟨E⟩ := nonempty_component_equiv_of_normal_simple hJF hJn hsolv
        (Ψ.trans (e₁.trans e₂)) hL
      exact NoPSL2Odd.of_mulEquiv E
        (noPSL2Odd_graphFixedRootGroup_E6 hO hp hp2 he hKe σ hσc)

theorem noPSL2Odd_of_E6_involution
    (hO : LieOrderFormulasInput) {J : Type} [Group J] {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E6 n p f) (hm : Blueprint.LieModel J .E6 n p f)
    {α : MulAut J} (hα : orderOf α = 2) {Kc : Subgroup (fixedSubgroup α)} (hKc : IsComponent Kc) :
    NoPSL2Odd Kc := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := LieType.Chevalley.nonempty_mulEquiv_adjointGroup .E6
    ((GH74.chevalleyExceptionalModel_of_lieModel (t := .E6) (by decide) hm).2 :
      UntwistedChevalleyModel J .E6 (p ^ f))
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  exact noPSL2Odd_E6_explicit hO (excInnerNoPSL2_E6 hO) (e6GraphNoPSL2_holds hO) hp hp2
    hadm.2.1 hF _ hβ (fixedSubgroupCongrEquiv e α) hKc

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
