module

public import CFSG.LieType.Chevalley.GraphFixedBruhatDecomposition
public import CFSG.LieType.Chevalley.GraphFixedRankOneScalar

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise commutatorElement

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

variable (σ) in
theorem orbitXProd_one_eq_orbitX
    (a : Fin t.foldedTag.rank) :
    orbitXProd t a (fun _ => (1 : K)) = (orbitX t K σ a 1 : ModGL t.tag K) := by
  rw [coe_orbitX_eq_orbitXProd]
  refine orbitXProd_congr t fun j hj => ?_
  obtain ⟨k, hk, rfl⟩ := t.exists_eq_perm_pow_orbitMin hj
  rw [orbitParam_pow t σ _ hk, Subfield.coe_one, map_one]

variable (σ) in
theorem orbitYProd_neg_one_eq_orbitY
    (a : Fin t.foldedTag.rank) :
    orbitYProd t a (fun _ => (-1 : K)) = (orbitY t K σ a (-1) : ModGL t.tag K) := by
  rw [coe_orbitY_eq_orbitYProd]
  refine congrArg List.prod (List.map_congr_left fun j hj => ?_)
  obtain ⟨k, hk, rfl⟩ := t.exists_eq_perm_pow_orbitMin ((t.mem_orbitWord).1 hj)
  rw [orbitParam_pow t σ _ hk, Subfield.coe_neg, Subfield.coe_one, map_neg, map_one]

theorem orbitXProd_one_mem_graphFixedPosUnipotent
    (a : Fin t.foldedTag.rank) :
    orbitXProd t a (fun _ => (1 : K)) ∈ graphFixedPosUnipotent t K σ := by
  rw [orbitXProd_one_eq_orbitX σ]
  exact orbitX_mem_graphFixedPosUnipotent t σ a 1

theorem orbitYProd_neg_one_mem_graphFixedNegUnipotent
    (a : Fin t.foldedTag.rank) :
    orbitYProd t a (fun _ => (-1 : K)) ∈ graphFixedNegUnipotent t K σ := by
  rw [orbitYProd_neg_one_eq_orbitY σ]
  exact orbitY_mem_graphFixedNegUnipotent t σ a (-1)

theorem canonicalRep_orbitReflection_eq_mul
    (a : Fin t.foldedTag.rank) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) =
      orbitXProd t a (fun _ => (1 : K)) * orbitYProd t a (fun _ => (-1 : K)) *
        orbitXProd t a (fun _ => (1 : K)) := by
  rw [canonicalRep_orbitReflection_eq_orbitN t (RingHom.id K) a, orbitN, Subgroup.coe_mul,
    Subgroup.coe_mul, orbitXProd_one_eq_orbitX (RingHom.id K),
    orbitYProd_neg_one_eq_orbitY (RingHom.id K)]
  simp only [inv_one, Units.val_one]

theorem canonicalRep_orbitReflection_mem_graphFixedRootGroup
    (a : Fin t.foldedTag.rank) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ graphFixedRootGroup t K σ := by
  rw [canonicalRep_orbitReflection_eq_orbitN t σ a]
  exact orbitN_mem_graphFixedRootGroup t σ a 1

theorem conj_mem_graphFixedRootGroup_of_mem_graphFixedTorus
    {g : ModGL t.tag K}
    (hg : g ∈ graphFixedTorus t K σ) {c : ModGL t.tag K} (hc : c ∈ graphFixedRootGroup t K σ) :
    g * c * g⁻¹ ∈ graphFixedRootGroup t K σ := by
  obtain ⟨hgH, hgΓ⟩ := Subgroup.mem_inf.1 hg
  have hle : graphFixedRootGroup t K σ ≤
      (graphFixedRootGroup t K σ).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun u hu => ?_) (fun u hu => ?_)
    · obtain ⟨huU, huΓ⟩ := Subgroup.mem_inf.1 hu
      refine graphFixedPosUnipotent_le_graphFixedRootGroup t K σ (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
      · exact (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_posUnipotent hgH) u).1 huU
      · exact mul_mem (mul_mem hgΓ huΓ) (inv_mem hgΓ)
    · obtain ⟨huU, huΓ⟩ := Subgroup.mem_inf.1 hu
      refine graphFixedNegUnipotent_le_graphFixedRootGroup t K σ (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
      · exact (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_negUnipotent hgH) u).1 huU
      · exact mul_mem (mul_mem hgΓ huΓ) (inv_mem hgΓ)
  exact hle hc

theorem graphFixedTorus_le_normalizer :
    graphFixedTorus t K σ ≤
      Subgroup.normalizer (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => conj_mem_graphFixedRootGroup_of_mem_graphFixedTorus hg hc, fun hc => ?_⟩
  have h := conj_mem_graphFixedRootGroup_of_mem_graphFixedTorus (inv_mem hg) hc
  rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at h

variable (hσ : Function.Surjective σ)
include hσ

theorem twistedFixedGroup_eq_sup_graphFixedTorus :
    twistedFixedGroup t K σ = graphFixedTorus t K σ ⊔ graphFixedRootGroup t K σ := by
  refine le_antisymm ?_ (sup_le (graphFixedTorus_le t K σ) (graphFixedRootGroup_le t K σ))
  rw [twistedFixedGroup_eq_sup_closure hσ]
  refine sup_le (fun b hb => ?_) ((Subgroup.closure_le _).2 ?_)
  · have hb' : b ∈ (graphFixedBorel t K σ : Set (ModGL t.tag K)) := hb
    rw [graphFixedBorel_eq_mul hσ] at hb'
    obtain ⟨h, hh, u, hu, rfl⟩ := hb'
    exact mul_mem (Subgroup.mem_sup_left hh)
      (Subgroup.mem_sup_right (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ hu))
  · rintro _ ⟨a, rfl⟩
    exact Subgroup.mem_sup_right (canonicalRep_orbitReflection_mem_graphFixedRootGroup a)

theorem coe_twistedFixedGroup_eq_mul :
    (twistedFixedGroup t K σ : Set (ModGL t.tag K)) =
      (graphFixedTorus t K σ : Set (ModGL t.tag K)) *
        (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) := by
  rw [twistedFixedGroup_eq_sup_graphFixedTorus hσ]
  exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ graphFixedTorus_le_normalizer

theorem twistedFixedGroup_le_normalizer :
    twistedFixedGroup t K σ ≤
      Subgroup.normalizer (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) := by
  rw [twistedFixedGroup_eq_sup_graphFixedTorus hσ]
  exact sup_le graphFixedTorus_le_normalizer Subgroup.le_normalizer

theorem graphFixedRootGroup_subgroupOf_normal :
    ((graphFixedRootGroup t K σ).subgroupOf (twistedFixedGroup t K σ)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (graphFixedRootGroup_le t K σ)).2
    (twistedFixedGroup_le_normalizer hσ)

theorem commutator_twistedFixedGroup_le :
    ⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ ≤ graphFixedRootGroup t K σ := by
  have hN : ∀ g ∈ twistedFixedGroup t K σ, ∀ c ∈ graphFixedRootGroup t K σ,
      g * c * g⁻¹ ∈ graphFixedRootGroup t K σ := fun g hg c hc =>
    (Subgroup.mem_normalizer_iff.1 (twistedFixedGroup_le_normalizer hσ hg) c).1 hc
  rw [Subgroup.commutator_le]
  intro g hg g' hg'
  have hg₁ : g ∈ (graphFixedTorus t K σ : Set (ModGL t.tag K)) *
      (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) := by
    rw [← coe_twistedFixedGroup_eq_mul hσ]
    exact hg
  have hg'₁ : g' ∈ (graphFixedTorus t K σ : Set (ModGL t.tag K)) *
      (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) := by
    rw [← coe_twistedFixedGroup_eq_mul hσ]
    exact hg'
  obtain ⟨h, hh, c, hc, rfl⟩ := hg₁
  obtain ⟨h', hh', c', hc', rfl⟩ := hg'₁
  have hhΓ := graphFixedTorus_le t K σ hh
  have hh'Γ := graphFixedTorus_le t K σ hh'
  have hcΓ := graphFixedRootGroup_le t K σ hc
  have hc'Γ := graphFixedRootGroup_le t K σ hc'
  have hcomm : ⁅h, h'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
    (graphFixedTorus_mul_comm hh hh')
  have e₁ : ⁅h * c, h' * c'⁆ = h * ⁅c, h' * c'⁆ * h⁻¹ * ⁅h, h' * c'⁆ := by
    simp only [commutatorElement_def]
    group
  have e₂ : ⁅h, h' * c'⁆ = ⁅h, h'⁆ * (h' * ⁅h, c'⁆ * h'⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hx : h' * c' ∈ twistedFixedGroup t K σ := mul_mem hh'Γ hc'Γ
  have h₁ : ⁅c, h' * c'⁆ ∈ graphFixedRootGroup t K σ := by
    rw [show ⁅c, h' * c'⁆ = c * ((h' * c') * c⁻¹ * (h' * c')⁻¹) by
      rw [commutatorElement_def]; group]
    exact mul_mem hc (hN _ hx _ (inv_mem hc))
  have h₂ : ⁅h, c'⁆ ∈ graphFixedRootGroup t K σ := by
    rw [commutatorElement_def]
    exact mul_mem (hN _ hhΓ _ hc') (inv_mem hc')
  rw [e₁, e₂, hcomm, one_mul]
  exact mul_mem (hN _ hhΓ _ h₁) (hN _ hh'Γ _ h₂)

omit hσ

theorem fixed_root_generated_normal_subgroup
    (t : TwistTag) (K : Type) [Field K]
    (σ : K ≃+* K) :
    ((graphFixedRootGroup t K σ.toRingHom).subgroupOf (twistedFixedGroup t K σ.toRingHom)).Normal ∧
    (twistedFixedGroup t K σ.toRingHom : Set (ModGL t.tag K)) =
      (graphFixedTorus t K σ.toRingHom : Set (ModGL t.tag K)) *
        (graphFixedRootGroup t K σ.toRingHom : Set (ModGL t.tag K)) ∧
    ⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆ ≤
      graphFixedRootGroup t K σ.toRingHom ∧
    (∀ a : Fin t.foldedTag.rank,
      orbitXProd t a (fun _ => (1 : K)) ∈ graphFixedPosUnipotent t K σ.toRingHom ∧
      orbitYProd t a (fun _ => (-1 : K)) ∈ graphFixedNegUnipotent t K σ.toRingHom ∧
      canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) =
        orbitXProd t a (fun _ => (1 : K)) * orbitYProd t a (fun _ => (-1 : K)) *
          orbitXProd t a (fun _ => (1 : K)) ∧
      canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
        graphFixedRootGroup t K σ.toRingHom) ∧
    (⁅graphFixedRootGroup t K σ.toRingHom, graphFixedRootGroup t K σ.toRingHom⁆ =
        graphFixedRootGroup t K σ.toRingHom →
      ⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆ =
        graphFixedRootGroup t K σ.toRingHom) := by
  refine ⟨graphFixedRootGroup_subgroupOf_normal σ.surjective,
    coe_twistedFixedGroup_eq_mul σ.surjective, commutator_twistedFixedGroup_le σ.surjective,
    fun a => ⟨orbitXProd_one_mem_graphFixedPosUnipotent a,
      orbitYProd_neg_one_mem_graphFixedNegUnipotent a,
      canonicalRep_orbitReflection_eq_mul a,
      canonicalRep_orbitReflection_mem_graphFixedRootGroup a⟩, fun hperf => ?_⟩
  refine le_antisymm (commutator_twistedFixedGroup_le σ.surjective) ?_
  calc graphFixedRootGroup t K σ.toRingHom =
        ⁅graphFixedRootGroup t K σ.toRingHom, graphFixedRootGroup t K σ.toRingHom⁆ :=
        hperf.symm
    _ ≤ ⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆ :=
        Subgroup.commutator_mono (graphFixedRootGroup_le t K _) (graphFixedRootGroup_le t K _)

end CFSG.LieType.Chevalley
