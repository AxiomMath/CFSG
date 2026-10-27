module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Field
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Graph
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Outer

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

variable {K : Type} [Field K] [Finite K]

theorem a6_F4_E8_G2_explicit
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E8 ∨ τ = .G2) (hinner : OddExcInnerDiagA6Form τ)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : τ = .G2 → p ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (β : MulAut (adjointGroup τ K)) (hβ : orderOf β = 2) :
    A6CentreForm (fixedSubgroup β) := by
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have hchar := ringChar_eq_of_card hp hf hK
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hτ' : τ = .F4 ∨ τ = .E8 ∨ (τ = .G2 ∧ ringChar K ≠ 3) := by
    rcases hτ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h, hchar ▸ hp3 h⟩)
  rcases odd_F4_E8_G2_involution_inner_or_quadratic hτ' hKodd hβ2 with ⟨g, a, hβg⟩ |
    ⟨q, e, hq, he, hKe, δ, hδ, g, a, hβg⟩
  · exact hinner K p f hp hp2 hK β g a hβg hβ
  · have hqp : q = p := by
      have h : q ∣ p ^ f := by
        rw [← hK, hKe]
        exact dvd_pow (dvd_pow_self q (by omega)) two_ne_zero
      exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)
    subst hqp
    exact a6CentreForm_quadratic_field τ hq hp2 he hKe δ hδ hβg hβ

theorem a6_G2_ree_coset
    [CharP K ReeTag.G2.prime] (b : ℕ) (hK' : Nat.card K = 3 ^ (2 * b + 1))
    (g : adjointGroup ReeTag.G2.tag K)
    (hβ2 : (MulAut.conj g * ReeTag.G2.finiteReeAut K b) ^ 2 = 1) :
    A6CentreForm (fixedSubgroup (MulAut.conj g * ReeTag.G2.finiteReeAut K b)) := by
  intro L hL
  suffices h : IsPGroup 2 (center L) from fun _ => h
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨ψ, hψ⟩ :=
    (LieType.Ree.G2_exceptional_coset_involution_fixed_p_components b K hK' g hβ2).1
  have hc : MulAut.congr ψ (MulAut.conj g * ReeTag.G2.finiteReeAut K b) =
      ReeTag.G2.finiteReeAut K b :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr ψ (MulAut.conj g * ReeTag.G2.finiteReeAut K b) =
      ψ * (MulAut.conj g * ReeTag.G2.finiteReeAut K b) * ψ⁻¹).trans hψ
  have hmap : (fixedSubgroup (ReeTag.G2.finiteReeAut K b)).map
      (adjointGroup ReeTag.G2.tag K).subtype = ReeTag.G2.reeGamma K b := rfl
  have hFc : fixedSubgroup (MulAut.congr ψ (MulAut.conj g * ReeTag.G2.finiteReeAut K b)) =
      fixedSubgroup (ReeTag.G2.finiteReeAut K b) := by rw [hc]
  let Ψ' : fixedSubgroup (MulAut.conj g * ReeTag.G2.finiteReeAut K b) ≃*
      ReeTag.G2.reeGamma K b := (fixedSubgroupCongrEquiv ψ _).trans
    ((MulEquiv.subgroupCongr hFc).trans
      (((fixedSubgroup (ReeTag.G2.finiteReeAut K b)).equivMapOfInjective _
        Subtype.val_injective).trans (MulEquiv.subgroupCongr hmap)))
  have hDs := (CatalogueBSmallRee.small_Ree_whole_group_p_components b K hK').1
  let Γ := ReeTag.G2.reeGamma K b
  have eJ : commutator Γ ≃* (commutator Γ).map Γ.subtype :=
    (commutator Γ).equivMapOfInjective _ Subtype.val_injective
  have : IsSimpleGroup ((commutator Γ).map Γ.subtype) := (MulEquiv.isSimpleGroup_congr eJ).1 hDs
  have hJF : (commutator Γ).map Γ.subtype ≤ Γ := Subgroup.map_subtype_le _
  have hJsub : ((commutator Γ).map Γ.subtype).subgroupOf Γ = commutator Γ :=
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
  have hJn : (((commutator Γ).map Γ.subtype).subgroupOf Γ).Normal := by
    rw [hJsub]
    exact Subgroup.commutator_normal ⊤ ⊤
  have hsolv : Group.IsSolvable (Γ ⧸ ((commutator Γ).map Γ.subtype).subgroupOf Γ) := by
    have : Group.IsSolvable (Abelianization Γ) := inferInstance
    exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientMulEquivOfEq hJsub.symm).toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq hJsub.symm).surjective
  exact isPGroup_center_of_mulEquiv_simple hL.1
    (nonempty_component_equiv_of_normal_simple hJF hJn hsolv Ψ' hL).some

theorem a6_G2_three_explicit
    [CharP K ReeTag.G2.prime] (hinner : OddExcInnerDiagA6Form .G2) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 3 ^ f) (β : MulAut (adjointGroup ReeTag.G2.tag K)) (hβ : orderOf β = 2) :
    A6CentreForm (fixedSubgroup β) := by
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  rcases G2_three_involution_inner_quadratic_or_exceptional hf hK hβ2 with ⟨g, a, hβg⟩ |
    ⟨e, he, hKe, δ, hδ, g, a, hβg⟩ | ⟨b, g, hfb, rfl⟩
  · exact hinner K 3 f Nat.prime_three (by decide) hK β g a hβg hβ
  · exact a6CentreForm_quadratic_field _ Nat.prime_three (by decide) he hKe δ hδ hβg hβ
  · exact a6_G2_ree_coset b (hfb ▸ hK) g hβ2

theorem a6_E7_explicit
    (hinner : OddExcInnerDiagA6Form .E7) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (β : MulAut (adjointGroup .E7 K)) (hβ : orderOf β = 2) :
    A6CentreForm (fixedSubgroup β) := by
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have h1 : ∀ x : ModGL Tag.E7 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hQ : ∀ ε : Fin (exactE Tag.E7), exactQ Tag.E7 K ε = 1 := fun _ => rfl
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form Tag.E7 (Or.inr (Or.inl rfl)) K
  obtain ⟨-, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E7 (Or.inr (Or.inl rfl)) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF β
  have hσ2 := hsq β g a σ ε hgaσ hβ2
  by_cases hσ1 : σ = 1
  · subst hσ1
    refine hinner K p f hp hp2 hK β g a (fun h => ?_) hβ
    rw [hgaσ h, hQ, h1, mul_one, inv_one, mul_one]
  · obtain ⟨hev, hσc, -⟩ := hquad p f hp hf hK σ hσ2 hσ1
    have he : 1 ≤ f / 2 := by
      obtain ⟨m, rfl⟩ := hev
      omega
    have hKe : Nat.card K = (p ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hK]
    exact a6CentreForm_quadratic_field .E7 hp hp2 he hKe σ hσc (g := g) (a := a)
      (fun h => by rw [hgaσ h, hQ, mul_one, inv_one, mul_one]) hβ

theorem a6_E6_explicit
    (hinner : OddExcInnerDiagA6Form .E6) (hgraph : OddE6GraphA6Form) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (β : MulAut (adjointGroup .E6 K))
    (hβ : orderOf β = 2) : A6CentreForm (fixedSubgroup β) := by
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
    · refine hinner K p f hp hp2 hK β g a (fun h => ?_) hβ
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
    · exact a6CentreForm_quadratic_field .E6 hp hp2 he hKe σ hσc (g := g) (a := a)
        (fun h => by rw [hgaσ h, hε, hQ0, mul_one, inv_one, mul_one]) hβ
    · intro L hL
      suffices h : IsPGroup 2 (center L) from fun _ => h
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
      exact isPGroup_center_of_mulEquiv_simple hL.1 E

end CFSG.ComponentClassification.CatLeafProof
