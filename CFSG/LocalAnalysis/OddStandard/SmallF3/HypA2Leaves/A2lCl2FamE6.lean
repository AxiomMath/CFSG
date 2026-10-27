module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamE6Graph
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamE6Toral

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

section


variable {K : Type} [Field K] [Finite K]

theorem cl24_odd_E6_explicit
    (hinner : Cl24ExcInnerDiag .E6) (hgraph : Cl24E6Graph) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (β : MulAut (adjointGroup .E6 K))
    (hβ : orderOf β = 2) {X : Type} [Group X] (Ψ : X ≃* fixedSubgroup β) {L : Subgroup X}
    (hL : IsComponent L) : Cl24Q p (fun f' => f' = f ∨ f = 2 * f') L := by
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
    · refine (cl24_of_component_equiv Ψ
        (hinner K p f hp hp2 hK β g a (fun h => ?_) hβ) hL).mono fun _ h => Or.inl h
      rw [hgaσ h, hε, hQ0, h1, mul_one, inv_one, mul_one]
    · exact (cl24_of_component_equiv Ψ (hgraph K p f hp hp2 hK β g a
        (fun h => (hgaσ h).trans (by rw [hε, hQ1, h1]; rfl)) hβ) hL).mono
        fun _ h => Or.inl h
  · obtain ⟨hev, hσc, -⟩ := hquad p f hp hf hK σ hσ2 hσ1
    have he : 1 ≤ f / 2 := by
      obtain ⟨m, rfl⟩ := hev
      omega
    have hKe : Nat.card K = (p ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hK]
    rcases hε with hε | hε
    · have hf2 := cl24_exp_eq_two_mul hp hK hKe
      exact (cl24_odd_field (t := .E6) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hp
        hp2 he hKe σ hσc (g := g) (a := a)
        (fun h => by rw [hgaσ h, hε, hQ0, mul_one, inv_one, mul_one]) hβ2 Ψ hL).mono
        fun _ h => Or.inr (by omega)
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
      have hf2 := cl24_exp_eq_two_mul hp hK hKe
      exact cl24_of_mulEquiv E
        (cl24_oddLieCentralQuotient_graphFixedRootGroup_E6 hp he hKe σ hσc
          (Rel := fun f' => f' = f ∨ f = 2 * f') (fun _ h => Or.inr (by omega)))

theorem cl24_family_E6_of_inner
    (hinner : Cl24ExcInnerDiag .E6) (hgraph : Cl24E6Graph) : Cl24OddFamily .E6 :=
  cl24_family_of_explicit (τ := .E6) (by decide) (fun _ _ _ _ h => h.2)
    fun K _ _ p f hp hp2 hf hK β hβ _ _ Ψ _ hL =>
      cl24_odd_E6_explicit hinner hgraph hp hp2 hf hK β hβ Ψ hL

end

section


theorem cl24_family_E6 : Cl24OddFamily .E6 :=
  cl24_family_E6_of_inner cl24_excInnerDiag_E6 cl24_oddE6GraphInput_holds

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
