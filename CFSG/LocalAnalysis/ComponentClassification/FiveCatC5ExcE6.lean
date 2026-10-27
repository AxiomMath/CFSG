module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5ExcField
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormE6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormTwE6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6GraphMain

public noncomputable section

namespace CFSG.ComponentClassification.SolMax.FiveCat.C5Exc

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.SteinbergCE
  CFSG.LocalAnalysis.SteinbergCE.E6GraphCoset CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatLeaf
open Subgroup
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootDiag)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

theorem isEmpty_a5_rationalRootGroup
    (hO : LieOrderFormulasInput) {k : Type} [Field k] (σ : k ≃+* k) [Finite (fixSubfield σ)]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card (fixSubfield σ) = p ^ f)
    {AK : ModGL TwistTag.E6.tag (fixSubfield σ)}
    (hAK : AK = diagramMap TwistTag.E6 _ ∨
      AK = rootDiagUnit TwistTag.E6.tag (E6SignedGraph.signTuple _) * diagramMap TwistTag.E6 _) :
    IsEmpty (↥(rationalRootGroup σ AK) ⧸ Subgroup.center ↥(rationalRootGroup σ AK) ≃*
      alternatingGroup (Fin 5)) := by
  let inner : Subgroup (ModGL TwistTag.E6.tag (fixSubfield σ)) :=
    (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
      graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK) ⊔
    (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
      graphCentralizer TwistTag.E6.tag (fixSubfield σ) AK)
  let e : ↥(rationalRootGroup σ AK) ≃* ↥inner := (inner.equivMapOfInjective _
    (baseChangeGL_injective (τ := TwistTag.E6.tag) (fixSubfield σ).subtype)).symm
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  rcases hAK with rfl | rfl
  · have hinner : (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
        graphCentralizer TwistTag.E6.tag (fixSubfield σ) (diagramMap TwistTag.E6 _)) ⊔
          (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
            graphCentralizer TwistTag.E6.tag (fixSubfield σ) (diagramMap TwistTag.E6 _)) =
        graphFixedRootGroup TwistTag.E6 (fixSubfield σ) (RingHom.id _) := by
      rw [graphFixedRootGroup, graphFixedPosUnipotent, graphFixedNegUnipotent,
        twistedFixedGroup_id_eq]
    exact isEmpty_a5_of_lieModel hO (τ' := .F4) (n' := 0)
      (e.trans (MulEquiv.subgroupCongr hinner)) ⟨hp, hf, rfl⟩ hp2
      (graphFixedRootGroup_E6_id_recognition hp2 hK).2 (by decide)
  · exact isEmpty_a5_of_lieModel hO (τ' := .PSp) (n' := 4) e
      ⟨hp, hf, by norm_num, fun h => by simp at h⟩ hp2
      (rootGenerated_recognition hp hp2 hK).2 (by decide)

theorem noLitA5_graphCosetFixed
    (hO : LieOrderFormulasInput) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k)
    (ε : ℕ) (hε : ε = 0 ∨ ε = 1) {x : ModGL TwistTag.E6.tag k} (hx : x ∈ graphRational k p e ε)
    (hx2 : (x * diagramMap TwistTag.E6 k) ^ 2 = 1) :
    NoLitA5 (graphCosetFixed k p e ε x) := by
  rintro L hL ⟨eA⟩
  exfalso
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
  refine (isEmpty_a5_rationalRootGroup hO _ (Fact.out : p.Prime) hp
    (card_fixSubfield_iterateFrobeniusEquiv he) hAK).false ?_
  let E := (e₁.trans e₂).trans (MulEquiv.subgroupCongr hc)
  exact (QuotientGroup.congr _ _ E (Subgroup.map_center_eq E)).symm.trans eA

@[expose] def OddE6GraphNoLitA5 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    ∀ (α : MulAut (adjointGroup TwistTag.E6.tag K)) (g : adjointGroup TwistTag.E6.tag K)
      (a : Fin TwistTag.E6.tag.rank → Kˣ),
      (∀ h : adjointGroup TwistTag.E6.tag K, (α h : ModGL TwistTag.E6.tag K) =
        (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
          diagramMap TwistTag.E6 K * (h : ModGL TwistTag.E6.tag K) *
            (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
              (g : ModGL TwistTag.E6.tag K)⁻¹) → orderOf α = 2 →
      NoLitA5 (fixedSubgroup α)

theorem oddE6GraphNoLitA5_holds
    (hO : LieOrderFormulasInput) : OddE6GraphNoLitA5 := by
  intro K _ _ p f hp hp2 hK α g a hαg hα
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
  exact NoLitA5.of_mulEquiv Φ
    (noLitA5_graphCosetFixed hO p hp2 hf _ hk 0 (Or.inl rfl) hxR hx2)

theorem lieModel_graphFixedRootGroup_E6
    {M : Type} [Field M] [Finite M] {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hM : Nat.card M = (p ^ e) ^ 2) (σ : M ≃+* M) (hσ : ∀ c, σ c = c ^ (p ^ e)) :
    Blueprint.LieModel (↥(graphFixedRootGroup TwistTag.E6 M σ.toRingHom) ⧸
      center ↥(graphFixedRootGroup TwistTag.E6 M σ.toRingHom)) .twistedE6 0 p e := by
  have hperf := (finite_fixed_root_group_perfect TwistTag.E6 hp he M hM σ.toRingHom hσ).2.2.1
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 M σ
  obtain ⟨e'⟩ := LieType.Chevalley.nonempty_derivedCentralQuotient_equiv hperf hZ
  have hadm : StatedLieAdmissible .twistedE6 0 p e := ⟨hp, he, rfl⟩
  exact Or.inr (Or.inl ⟨rfl, by decide, hadm, M, inferInstance, inferInstance, hM, σ.toRingHom,
    hσ, ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
      e'.symm⟩⟩)

theorem noLitA5_E6_explicit
    (hO : LieOrderFormulasInput) (hinner : OddExcInnerDiagSLForm .E6) (hgraph : OddE6GraphNoLitA5)
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (β : MulAut (adjointGroup .E6 K)) (hβ : orderOf β = 2) :
    NoLitA5 (fixedSubgroup β) := by
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have hK2 : ringChar K ≠ 2 := by rw [ringChar_eq_of_card hp hf hK]; exact hp2
  have : Finite (ModGL Tag.E6 K) := finite_modGL
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
    · refine noLitA5_of_slComponentForm hK2
        (hinner K p f hp hp2 hK β g a (fun h => ?_) hβ).2
      rw [hgaσ h, hε, hQ0, h1, mul_one, inv_one, mul_one]
    · exact hgraph K p f hp hp2 hK β g a
        (fun h => (hgaσ h).trans (by rw [hε, hQ1, h1]; rfl)) hβ
  · obtain ⟨hev, hσc, -⟩ := hquad p f hp hf hK σ hσ2 hσ1
    have he : 1 ≤ f / 2 := by
      obtain ⟨m, rfl⟩ := hev
      omega
    have hKe : Nat.card K = (p ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hK]
    rcases hε with hε | hε
    · exact noLitA5_quadratic_field hO (t := .E6) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hp hp2
        he hKe σ hσc (g := g) (a := a)
        (fun h => by rw [hgaσ h, hε, hQ0, mul_one, inv_one, mul_one]) hβ
    · intro L hL ⟨eA⟩
      exfalso
      obtain ⟨-, β', hβ', hβα⟩ :=
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
      obtain ⟨E⟩ := nonempty_component_equiv_of_normal_simple hJF hJn hsolv (e₁.trans e₂) hL
      have hadm : StatedLieAdmissible .twistedE6 0 p (f / 2) := ⟨hp, he, rfl⟩
      exact (isEmpty_a5_of_lieModel hO E hadm hp2
        (lieModel_graphFixedRootGroup_E6 hp he hKe σ hσc) (by decide)).false eA

theorem oddLieA5For_E6
    (hO : LieOrderFormulasInput) : OddLieA5For .E6 :=
  oddLieA5For_of_explicit (τ := .E6) (by decide) (fun _ _ _ _ h => h.2)
    fun _ _ _ _ _ hp hp2 _ hf hK β hβ =>
      noLitA5_E6_explicit hO oddExcInnerDiagSLForm_E6 (oddE6GraphNoLitA5_holds hO) hp hp2 hf hK
        β hβ

theorem noLitA5_twistedE6Outer
    (hO : LieOrderFormulasInput) (J : Type) [Group J] (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .twistedE6 0 p f) (hm : Blueprint.LieModel J .twistedE6 0 p f)
    (α : MulAut J) (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    NoLitA5 (fixedSubgroup α) := by
  have hf : 1 ≤ f := hadm.2.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, σ, hF, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 hp hf
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  have hF2 : Nat.card F = (p ^ f) ^ 2 := hF
  have : CharP F p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (show 1 ≤ f * 2 by omega) (by rw [hF2, ← pow_mul])
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have halg := isAlgebraic_zmod_of_isAlgClosure p F (AlgebraicClosure F)
  have hα' : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hα'2 : MulAut.congr e α ^ 2 = 1 := by
    rw [← hα']
    exact pow_orderOf_eq_one _
  have hα'o : MulAut.congr e α ∉ twistedE6Inn F σ := by
    rintro ⟨c, hc⟩
    refine hαo ⟨e.symm c, (MulAut.congr e).injective ?_⟩
    rw [mulAut_congr_conj_twistedE6, MulEquiv.apply_symm_apply]
    exact hc
  obtain ⟨x, hxR, hx2, ⟨Φ⟩⟩ :=
    exists_mulEquiv_twisted_E6_outer_fixed hp2 hf F hF2 σ hσ _ hα'2 hα'o
  let Ψ := (fixedSubgroupCongrEquiv e α).trans Φ
  exact NoLitA5.of_mulEquiv Ψ
    (noLitA5_graphCosetFixed hO p hp2 hf _ halg 1 (Or.inr rfl) hxR hx2)

theorem oddLieA5For_twistedE6
    (hO : LieOrderFormulasInput) : OddLieA5For .twistedE6 := by
  intro J _ n p f hp hp2 _ hadm hm α hα
  obtain rfl : n = 0 := hadm.2.2
  by_cases hi : α ∈ (MulAut.conj : J →* MulAut J).range
  · obtain ⟨-, hform⟩ := oddTwistedE6InnerSLForm_holds J p f hp hp2 hadm hm α hα hi
    have : Fact p.Prime := ⟨hp⟩
    have hf : 1 ≤ f := hadm.2.1
    haveI : Finite J := (hO J .twistedE6 0 p f hadm hm).1
    exact noLitA5_of_slComponentForm (K := GaloisField p f)
      (by rw [ringChar.eq (GaloisField p f) p]; exact hp2)
      (hform (GaloisField p f) (GaloisField.card p f (by omega)))
  · exact noLitA5_twistedE6Outer hO J p f hp hp2 hadm hm α hα hi

end CFSG.ComponentClassification.SolMax.FiveCat.C5Exc
