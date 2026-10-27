module

public import CFSG.LieType.Chevalley.GraphFixedParabolicIntersection

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem perm_mem_orbitUnion {J : Set (Fin t.foldedTag.rank)} {i : Fin t.tag.rank}
    (hi : i ∈ t.orbitUnion J) : t.perm i ∈ t.orbitUnion J := by
  rw [mem_orbitUnion_iff_orbitIndex] at hi ⊢
  rwa [t.orbitIndex_perm]

theorem perm_symm_mem_orbitUnion {J : Set (Fin t.foldedTag.rank)} {i : Fin t.tag.rank}
    (hi : i ∈ t.orbitUnion J) : t.perm.symm i ∈ t.orbitUnion J := by
  rw [mem_orbitUnion_iff_orbitIndex] at hi ⊢
  rwa [← t.orbitIndex_perm, Equiv.apply_symm_apply]

theorem image_permLattice_eq
    {S : Set (Fin t.tag.rank → ℤ)}
    (h₁ : ∀ α ∈ S, permLattice t.perm α ∈ S) (h₂ : ∀ α ∈ S, permLattice t.perm.symm α ∈ S) :
    permLattice t.perm '' S = S := by
  refine Set.Subset.antisymm ?_ fun α hα => ⟨_, h₂ α hα, permLattice_permLattice_symm _ _⟩
  rintro _ ⟨α, hα, rfl⟩
  exact h₁ α hα

theorem permLattice_mem_parabolicRadicalRoots
    {J : Set (Fin t.foldedTag.rank)}
    {α : Fin t.tag.rank → ℤ} (hα : α ∈ parabolicRadicalRoots t.tag (t.orbitUnion J)) :
    permLattice t.perm α ∈ parabolicRadicalRoots t.tag (t.orbitUnion J) := by
  obtain ⟨⟨hr, hp⟩, hnot⟩ := hα
  refine ⟨⟨hr.permLattice t.cartan_perm, by rwa [height_permLattice]⟩, fun h => hnot ?_⟩
  have := permLattice_symm_mem_parabolicPosRoots h
  rwa [permLattice_symm_permLattice] at this

theorem permLattice_symm_mem_parabolicRadicalRoots
    {J : Set (Fin t.foldedTag.rank)}
    {α : Fin t.tag.rank → ℤ} (hα : α ∈ parabolicRadicalRoots t.tag (t.orbitUnion J)) :
    permLattice t.perm.symm α ∈ parabolicRadicalRoots t.tag (t.orbitUnion J) := by
  obtain ⟨⟨hr, hp⟩, hnot⟩ := hα
  refine ⟨⟨hr.permLattice (cartan_perm_symm t.cartan_perm), by rwa [height_permLattice]⟩,
    fun h => hnot ?_⟩
  have := permLattice_mem_parabolicPosRoots h
  rwa [permLattice_permLattice_symm] at this

variable (hσ : Function.Surjective σ)
include hσ

theorem map_twistHom_rootSpan_of_stable
    {S : Set (Fin t.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot t.tag α) (h₁ : ∀ α ∈ S, permLattice t.perm α ∈ S)
    (h₂ : ∀ α ∈ S, permLattice t.perm.symm α ∈ S) :
    (rootSpan t.tag K S).map (twistHom t K σ) = rootSpan t.tag K S := by
  rw [map_twistHom_rootSpan t K hσ hS, image_permLattice_eq h₁ h₂]

theorem map_twistHom_parabolicRadical
    (J : Set (Fin t.foldedTag.rank)) :
    (parabolicRadical t.tag K (t.orbitUnion J)).map (twistHom t K σ) =
      parabolicRadical t.tag K (t.orbitUnion J) :=
  map_twistHom_rootSpan_of_stable hσ (fun _ h => h.1.1)
    (fun _ h => permLattice_mem_parabolicRadicalRoots h)
    fun _ h => permLattice_symm_mem_parabolicRadicalRoots h

theorem map_twistHom_parabolicLeviUnipotent
    (J : Set (Fin t.foldedTag.rank)) :
    (parabolicLeviUnipotent t.tag K (t.orbitUnion J)).map (twistHom t K σ) =
      parabolicLeviUnipotent t.tag K (t.orbitUnion J) :=
  map_twistHom_rootSpan_of_stable hσ (fun _ h => h.2.1)
    (fun _ h => permLattice_mem_parabolicPosRoots h)
    fun _ h => permLattice_symm_mem_parabolicPosRoots h

theorem map_twistHom_parabolicRadicalGe
    (J : Set (Fin t.foldedTag.rank)) (h : ℤ) :
    (parabolicRadicalGe t.tag K (t.orbitUnion J) h).map (twistHom t K σ) =
      parabolicRadicalGe t.tag K (t.orbitUnion J) h :=
  map_twistHom_rootSpan_of_stable hσ (fun _ hα => hα.1.1.1)
    (fun _ hα => ⟨permLattice_mem_parabolicRadicalRoots hα.1,
      by rw [height_permLattice]; exact hα.2⟩)
    fun _ hα => ⟨permLattice_symm_mem_parabolicRadicalRoots hα.1,
      by rw [height_permLattice]; exact hα.2⟩

theorem map_twistHom_parabolicLevi
    (J : Set (Fin t.foldedTag.rank)) :
    (parabolicLevi t.tag K (t.orbitUnion J)).map (twistHom t K σ) =
      parabolicLevi t.tag K (t.orbitUnion J) := by
  rw [parabolicLevi, Subgroup.map_sup, map_twistHom_torusGroup t K hσ, MonoidHom.map_closure]
  congr 2
  ext g
  constructor
  · rintro ⟨_, ⟨j, hj, c, rfl | rfl⟩, rfl⟩
    · exact ⟨t.perm j, perm_mem_orbitUnion hj, σ c, Or.inl (twistHom_xUnit t K σ j c)⟩
    · exact ⟨t.perm j, perm_mem_orbitUnion hj, σ c, Or.inr (twistHom_yUnit t K σ j c)⟩
  · rintro ⟨j, hj, c, rfl | rfl⟩
    · obtain ⟨c', rfl⟩ := hσ c
      refine ⟨xUnit t.tag K (t.perm.symm j) c', ⟨_, perm_symm_mem_orbitUnion hj, c', Or.inl rfl⟩,
        ?_⟩
      rw [twistHom_xUnit, Equiv.apply_symm_apply]
    · obtain ⟨c', rfl⟩ := hσ c
      refine ⟨yUnit t.tag K (t.perm.symm j) c', ⟨_, perm_symm_mem_orbitUnion hj, c', Or.inr rfl⟩,
        ?_⟩
      rw [twistHom_yUnit, Equiv.apply_symm_apply]

theorem map_twistHom_parabolicSubgroup
    (J : Set (Fin t.foldedTag.rank)) :
    (parabolicSubgroup t.tag K (t.orbitUnion J)).map (twistHom t K σ) =
      parabolicSubgroup t.tag K (t.orbitUnion J) := by
  rw [parabolicSubgroup, Subgroup.map_sup, map_twistHom_borelGroup t K hσ, MonoidHom.map_closure]
  congr 2
  ext g
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨t.perm j, perm_mem_orbitUnion hj, (twistHom_weylElt_one t K σ j).symm⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨weylElt t.tag K (t.perm.symm j) 1, ⟨_, perm_symm_mem_orbitUnion hj, rfl⟩, ?_⟩
    change twistHom t K σ (weylElt t.tag K (t.perm.symm j) 1) = _
    rw [twistHom_weylElt_one, Equiv.apply_symm_apply]

omit hσ

theorem twistHom_mem_of_map_eq {X : Subgroup (ModGL t.tag K)}
    (hX : X.map (twistHom t K σ) = X) {g : ModGL t.tag K} (hg : g ∈ X) : twistHom t K σ g ∈ X :=
  hX ▸ Subgroup.mem_map_of_mem _ hg

theorem coe_parabolicSubgroup_eq_mul
    (A : Set (Fin t.tag.rank)) :
    (parabolicSubgroup t.tag K A : Set (ModGL t.tag K)) =
      (parabolicRadical t.tag K A : Set (ModGL t.tag K)) * (parabolicLevi t.tag K A : Set _) := by
  rw [← parabolicRadical_sup_parabolicLevi A, Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (le_trans (parabolicLevi_le_parabolicSubgroup A)
      (parabolicSubgroup_le_normalizer_parabolicRadical A))]

include hσ

theorem exists_fixed_parabolic_factor
    (J : Set (Fin t.foldedTag.rank)) {g : ModGL t.tag K}
    (hg : g ∈ parabolicSubgroup t.tag K (t.orbitUnion J) ⊓ twistedFixedGroup t K σ) :
    ∃ q ∈ graphFixedParabolicRadical t K σ J,
      ∃ m ∈ parabolicLevi t.tag K (t.orbitUnion J) ⊓ twistedFixedGroup t K σ, q * m = g := by
  obtain ⟨hgP, hgΓ⟩ := Subgroup.mem_inf.1 hg
  have hgP' : g ∈ (parabolicSubgroup t.tag K (t.orbitUnion J) : Set (ModGL t.tag K)) := hgP
  rw [coe_parabolicSubgroup_eq_mul] at hgP'
  obtain ⟨q, hq, m, hm, rfl⟩ := hgP'
  have hfix := ((mem_twistedFixedGroup_iff_twistHom t K σ).1 hgΓ).2
  rw [map_mul] at hfix
  obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_parabolic
    (twistHom_mem_of_map_eq (map_twistHom_parabolicRadical hσ J) hq) hq
    (twistHom_mem_of_map_eq (map_twistHom_parabolicLevi hσ J) hm) hm hfix
  have hqC : q ∈ adjointGroup t.tag K :=
    rootSpan_le_adjointGroup K _ hq
  have hmC : m ∈ adjointGroup t.tag K := parabolicLevi_le_adjointGroup t.tag K _ hm
  exact ⟨q, Subgroup.mem_inf.2 ⟨hq, (mem_twistedFixedGroup_iff_twistHom t K σ).2 ⟨hqC, h1⟩⟩, m,
    Subgroup.mem_inf.2 ⟨hm, (mem_twistedFixedGroup_iff_twistHom t K σ).2 ⟨hmC, h2⟩⟩, rfl⟩

omit hσ

theorem graphFixedParabolicRadical_le_graphFixedPosUnipotent
    (J : Set (Fin t.foldedTag.rank)) :
    graphFixedParabolicRadical t K σ J ≤ graphFixedPosUnipotent t K σ :=
  inf_le_inf_right _ (parabolicRadical_le_posUnipotent _)

theorem diagram_fixed_parabolic_root_radical_Levi_factors
    (t : TwistTag) (K : Type) [Field K]
    (σ : K ≃+* K) (J : Set (Fin t.foldedTag.rank)) :
    (parabolicRadical t.tag K (t.orbitUnion J)).map (twistHom t K σ.toRingHom) =
      parabolicRadical t.tag K (t.orbitUnion J) ∧
    (parabolicLevi t.tag K (t.orbitUnion J)).map (twistHom t K σ.toRingHom) =
      parabolicLevi t.tag K (t.orbitUnion J) ∧
    (parabolicLeviUnipotent t.tag K (t.orbitUnion J)).map (twistHom t K σ.toRingHom) =
      parabolicLeviUnipotent t.tag K (t.orbitUnion J) ∧
    (parabolicSubgroup t.tag K (t.orbitUnion J)).map (twistHom t K σ.toRingHom) =
      parabolicSubgroup t.tag K (t.orbitUnion J) ∧
    (∀ h : ℤ, (parabolicRadicalGe t.tag K (t.orbitUnion J) h).map (twistHom t K σ.toRingHom) =
      parabolicRadicalGe t.tag K (t.orbitUnion J) h) ∧
    ((graphFixedParabolicRadical t K σ.toRingHom J).subgroupOf
      (parabolicSubgroup t.tag K (t.orbitUnion J) ⊓ twistedFixedGroup t K σ.toRingHom)).Normal ∧
    graphFixedParabolicRadical t K σ.toRingHom J ⊓
        (parabolicLevi t.tag K (t.orbitUnion J) ⊓ twistedFixedGroup t K σ.toRingHom) = ⊥ ∧
    (∀ g ∈ parabolicSubgroup t.tag K (t.orbitUnion J) ⊓ twistedFixedGroup t K σ.toRingHom,
      ∃! qm : ModGL t.tag K × ModGL t.tag K, qm.1 ∈ graphFixedParabolicRadical t K σ.toRingHom J ∧
        qm.2 ∈ parabolicLevi t.tag K (t.orbitUnion J) ⊓ twistedFixedGroup t K σ.toRingHom ∧
        g = qm.1 * qm.2) ∧
    graphFixedParabolicRadical t K σ.toRingHom J ≤ graphFixedParabolic t K σ.toRingHom J ∧
    ((graphFixedParabolicRadical t K σ.toRingHom J).subgroupOf
      (graphFixedParabolic t K σ.toRingHom J)).Normal ∧
    graphFixedParabolicLevi t K σ.toRingHom J ≤ graphFixedParabolic t K σ.toRingHom J ∧
    (∀ g ∈ graphFixedParabolic t K σ.toRingHom J,
      ∃! qm : ModGL t.tag K × ModGL t.tag K, qm.1 ∈ graphFixedParabolicRadical t K σ.toRingHom J ∧
        qm.2 ∈ graphFixedParabolicLevi t K σ.toRingHom J ∧ g = qm.1 * qm.2) ∧
    (graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) =
      (graphFixedParabolicRadical t K σ.toRingHom J : Set (ModGL t.tag K)) *
        ((graphFixedRootTorus t K σ.toRingHom : Set (ModGL t.tag K)) *
          (graphFixedParabolicLeviUnipotent t K σ.toRingHom J : Set (ModGL t.tag K))) ∧
    (∀ q ∈ graphFixedParabolicRadical t K σ.toRingHom J,
      ∀ q' ∈ graphFixedParabolicRadical t K σ.toRingHom J,
      ∀ x ∈ (graphFixedRootTorus t K σ.toRingHom : Set (ModGL t.tag K)) *
          (graphFixedParabolicLeviUnipotent t K σ.toRingHom J : Set (ModGL t.tag K)),
      ∀ x' ∈ (graphFixedRootTorus t K σ.toRingHom : Set (ModGL t.tag K)) *
          (graphFixedParabolicLeviUnipotent t K σ.toRingHom J : Set (ModGL t.tag K)),
        q * x = q' * x' → q = q' ∧ x = x') ∧
    (graphFixedRootTorus t K σ.toRingHom : Set (ModGL t.tag K)) *
        (graphFixedParabolicLeviUnipotent t K σ.toRingHom J : Set (ModGL t.tag K)) ⊆
      (graphFixedParabolicLevi t K σ.toRingHom J : Set (ModGL t.tag K)) ∧
    (∀ h : ℤ, graphFixedRootBorel t K σ.toRingHom ≤ Subgroup.normalizer
      (graphFixedParabolicRadicalGe t K σ.toRingHom J h : Set (ModGL t.tag K))) ∧
    (∀ [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p],
      IsPGroup p (graphFixedParabolicRadical t K σ.toRingHom J)) ∧
    (J ≠ Set.univ → graphFixedParabolicRadical t K σ.toRingHom J ≠ ⊥) := by
  have hσ := σ.surjective
  set A := t.orbitUnion J
  set Q₀ := graphFixedParabolicRadical t K σ.toRingHom J
  have hQ₀ : Q₀ = parabolicRadical t.tag K A ⊓ twistedFixedGroup t K σ.toRingHom := rfl
  have hQP : parabolicRadical t.tag K A ≤ parabolicSubgroup t.tag K A :=
    le_trans (parabolicRadical_le_posUnipotent A) (posUnipotent_le_parabolicSubgroup A)
  have hQN := parabolicSubgroup_le_normalizer_parabolicRadical (K := K) A
  have hQC : Q₀ ≤ graphFixedRootGroup t K σ.toRingHom :=
    (graphFixedParabolicRadical_le_graphFixedPosUnipotent J).trans
      (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ.toRingHom)
  have hP1 := parabolicSubgroup_inf_graphFixedRootGroup (K := K) (σ := σ.toRingHom) hσ J
  have hnormal : ∀ X : Subgroup (ModGL t.tag K), X ≤ parabolicSubgroup t.tag K A →
      X ≤ twistedFixedGroup t K σ.toRingHom → Q₀ ≤ X → (Q₀.subgroupOf X).Normal := by
    intro X hXP hXΓ hQX
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnQ, hnΓ⟩ := Subgroup.mem_inf.1 hn
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hQN (hXP g.2)) n).1 hnQ,
      mul_mem (mul_mem (hXΓ g.2) hnΓ) (inv_mem (hXΓ g.2))⟩
  have hinf : Q₀ ⊓ (parabolicLevi t.tag K A ⊓ twistedFixedGroup t K σ.toRingHom) = ⊥ :=
    eq_bot_iff.2 fun g hg => by
      rw [← parabolicRadical_inf_parabolicLevi (K := K) A]
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).1,
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).2).1⟩
  have huniq : ∀ {q q' m m' : ModGL t.tag K}, q ∈ Q₀ → q' ∈ Q₀ → m ∈ parabolicLevi t.tag K A →
      m' ∈ parabolicLevi t.tag K A → q * m = q' * m' → q = q' ∧ m = m' :=
    fun hq hq' hm hm' h => eq_of_mul_eq_of_parabolic (Subgroup.mem_inf.1 hq).1
      (Subgroup.mem_inf.1 hq').1 hm hm' h
  have hHVM : (graphFixedRootTorus t K σ.toRingHom : Set (ModGL t.tag K)) *
      (graphFixedParabolicLeviUnipotent t K σ.toRingHom J : Set (ModGL t.tag K)) ⊆
        (graphFixedParabolicLevi t K σ.toRingHom J : Set (ModGL t.tag K)) := by
    rintro _ ⟨h, hh, v, hv, rfl⟩
    refine Subgroup.mem_inf.2 ⟨mul_mem (torusGroup_le_parabolicLevi A
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1)
      (parabolicLeviUnipotent_le_parabolicLevi A (Subgroup.mem_inf.1 hv).1),
      mul_mem (Subgroup.mem_inf.1 hh).2 ?_⟩
    exact (graphFixedParabolicLeviUnipotent_le_graphFixedRootGroup t K σ.toRingHom J) hv
  have hB : (graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) =
      (Q₀ : Set (ModGL t.tag K)) * ((graphFixedRootTorus t K σ.toRingHom : Set (ModGL t.tag K)) *
        (graphFixedParabolicLeviUnipotent t K σ.toRingHom J : Set (ModGL t.tag K))) := by
    refine Set.Subset.antisymm (fun b hb => ?_) ?_
    · obtain ⟨⟨hbB, hbΓ⟩, hbC⟩ := Subgroup.mem_inf.1 hb
      have hbB' : b ∈ (borelGroup t.tag K : Set (ModGL t.tag K)) := hbB
      rw [borelGroup_eq_mul_parabolic A] at hbB'
      obtain ⟨q, hq, _, ⟨h, hh, v, hv, rfl⟩, rfl⟩ := hbB'
      have hfix := ((mem_twistedFixedGroup_iff_twistHom t K σ.toRingHom).1 hbΓ).2
      rw [map_mul, map_mul] at hfix
      have hFh : twistHom t K σ.toRingHom h ∈ torusGroup t.tag K :=
        twistHom_mem_of_map_eq (map_twistHom_torusGroup t K hσ) hh
      have hFv : twistHom t K σ.toRingHom v ∈ parabolicLeviUnipotent t.tag K A :=
        twistHom_mem_of_map_eq (map_twistHom_parabolicLeviUnipotent hσ J) hv
      obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_parabolic
        (twistHom_mem_of_map_eq (map_twistHom_parabolicRadical hσ J) hq) hq
        (mul_mem (torusGroup_le_parabolicLevi A hFh)
          (parabolicLeviUnipotent_le_parabolicLevi A hFv))
        (mul_mem (torusGroup_le_parabolicLevi A hh)
          (parabolicLeviUnipotent_le_parabolicLevi A hv))
        hfix
      obtain ⟨h3, h4⟩ := (triangular_borel_structure.{0, 0} t.tag K).2.2.2.2.2.2.1 _ hFh _ hh _
        (parabolicLeviUnipotent_le_posUnipotent A hFv) _
        (parabolicLeviUnipotent_le_posUnipotent A hv) h2
      have hqΓ : q ∈ twistedFixedGroup t K σ.toRingHom :=
        (mem_twistedFixedGroup_iff_twistHom t K σ.toRingHom).2
          ⟨rootSpan_le_adjointGroup K _ hq, h1⟩
      have hhΓ : h ∈ twistedFixedGroup t K σ.toRingHom :=
        (mem_twistedFixedGroup_iff_twistHom t K σ.toRingHom).2
          ⟨borelGroup_le_adjointGroup (torusGroup_le_borelGroup hh), h3⟩
      have hvΓ : v ∈ twistedFixedGroup t K σ.toRingHom :=
        (mem_twistedFixedGroup_iff_twistHom t K σ.toRingHom).2
          ⟨rootSpan_le_adjointGroup K _ hv, h4⟩
      have hqQ : q ∈ Q₀ := Subgroup.mem_inf.2 ⟨hq, hqΓ⟩
      have hvV : v ∈ graphFixedParabolicLeviUnipotent t K σ.toRingHom J :=
        Subgroup.mem_inf.2 ⟨hv, hvΓ⟩
      have hhC : h ∈ graphFixedRootGroup t K σ.toRingHom := by
        have e : h = q⁻¹ * (q * (h * v)) * v⁻¹ := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem (hQC hqQ)) hbC)
          (inv_mem (graphFixedParabolicLeviUnipotent_le_graphFixedRootGroup t K σ.toRingHom J hvV))
      exact ⟨q, hqQ, h * v, ⟨h, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hh, hhΓ⟩, hhC⟩, v, hvV,
        rfl⟩, rfl⟩
    · rintro _ ⟨q, hq, _, ⟨h, hh, v, hv, rfl⟩, rfl⟩
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨mul_mem ?_ (mul_mem ?_ ?_), mul_mem
        (Subgroup.mem_inf.1 hq).2 (mul_mem (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).2 ?_)⟩,
        mul_mem (hQC hq) (mul_mem (graphFixedRootTorus_le t K σ.toRingHom hh) ?_)⟩
      · exact Subgroup.mem_sup_right (parabolicRadical_le_posUnipotent A (Subgroup.mem_inf.1 hq).1)
      · exact torusGroup_le_borelGroup (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1
      · exact Subgroup.mem_sup_right (parabolicLeviUnipotent_le_posUnipotent A
          (Subgroup.mem_inf.1 hv).1)
      · exact (Subgroup.mem_inf.1 hv).2
      · exact graphFixedParabolicLeviUnipotent_le_graphFixedRootGroup t K σ.toRingHom J hv
  have hQP1 : Q₀ ≤ graphFixedParabolic t K σ.toRingHom J :=
    hP1 ▸ le_inf (inf_le_left.trans hQP) hQC
  have hP1A : graphFixedParabolic t K σ.toRingHom J ≤ parabolicSubgroup t.tag K A :=
    hP1 ▸ inf_le_left
  have hP1Γ : graphFixedParabolic t K σ.toRingHom J ≤ twistedFixedGroup t K σ.toRingHom :=
    (graphFixedParabolic_le t K σ.toRingHom J).trans (graphFixedRootGroup_le t K σ.toRingHom)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfin⟩ := parabolic_root_radical_Levi_factors t.tag K A
  refine ⟨map_twistHom_parabolicRadical hσ J, map_twistHom_parabolicLevi hσ J,
    map_twistHom_parabolicLeviUnipotent hσ J, map_twistHom_parabolicSubgroup hσ J,
    map_twistHom_parabolicRadicalGe hσ J,
    hnormal _ inf_le_left inf_le_right (inf_le_inf_right _ hQP), hinf, fun g hg => ?_, hQP1,
    hnormal _ hP1A hP1Γ hQP1, hP1 ▸ inf_le_inf_right _ (parabolicLevi_le_parabolicSubgroup A),
    fun g hg => ?_, hB, fun q hq q' hq' x hx x' hx' h =>
      huniq hq hq' (Subgroup.mem_inf.1 (hHVM hx)).1 (Subgroup.mem_inf.1 (hHVM hx')).1 h, hHVM,
    fun h => ?_, fun p _ _ => (hfin p).2.1.to_le inf_le_left, fun hJ => ?_⟩
  · obtain ⟨q, hq, m, hm, rfl⟩ := exists_fixed_parabolic_factor hσ J hg
    refine ⟨(q, m), ⟨hq, hm, rfl⟩, fun qm ⟨hq', hm', h⟩ => ?_⟩
    obtain ⟨h1, h2⟩ := huniq hq' hq (Subgroup.mem_inf.1 hm').1 (Subgroup.mem_inf.1 hm).1 h.symm
    exact Prod.ext h1 h2
  · have hgA : g ∈ parabolicSubgroup t.tag K A ⊓ twistedFixedGroup t K σ.toRingHom :=
      Subgroup.mem_inf.2 ⟨hP1A hg, hP1Γ hg⟩
    obtain ⟨q, hq, m, hm, rfl⟩ := exists_fixed_parabolic_factor hσ J hgA
    have hmC : m ∈ graphFixedRootGroup t K σ.toRingHom := by
      have e : m = q⁻¹ * (q * m) := by group
      rw [e]
      exact mul_mem (inv_mem (hQC hq)) (graphFixedParabolic_le t K σ.toRingHom J hg)
    refine ⟨(q, m), ⟨hq, Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hm).1, hmC⟩, rfl⟩,
      fun qm ⟨hq', hm', h⟩ => ?_⟩
    obtain ⟨h1, h2⟩ := huniq hq' hq (Subgroup.mem_inf.1 hm').1 (Subgroup.mem_inf.1 hm).1 h.symm
    exact Prod.ext h1 h2
  · intro b hb
    obtain ⟨⟨hbB, hbΓ⟩, -⟩ := Subgroup.mem_inf.1 hb
    have hN := borelGroup_le_normalizer_parabolicRadicalGe (K := K) A h hbB
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro x
    constructor
    · intro hx
      obtain ⟨hxQ, hxΓ⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_inf.2 ⟨(hN x).1 hxQ, mul_mem (mul_mem hbΓ hxΓ) (inv_mem hbΓ)⟩
    · intro hx
      obtain ⟨hxQ, hxΓ⟩ := Subgroup.mem_inf.1 hx
      refine Subgroup.mem_inf.2 ⟨(hN x).2 hxQ, ?_⟩
      have e : x = b⁻¹ * (b * x * b⁻¹) * b := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hbΓ) hxΓ) hbΓ
  · obtain ⟨a, ha⟩ : ∃ a, a ∉ J := by
      by_contra h
      push Not at h
      exact hJ (Set.eq_univ_of_forall h)
    have hx := orbitX_mem t σ.toRingHom a 1
    obtain ⟨hxS, hxΓ⟩ := Subgroup.mem_inf.1 hx
    have hxQ : (orbitX t K σ.toRingHom a 1 : ModGL t.tag K) ∈ Q₀ := by
      refine Subgroup.mem_inf.2 ⟨rootSpan_mono ?_ hxS, hxΓ⟩
      rintro _ ⟨i, hi, rfl⟩
      refine mem_parabolicRadicalRoots_iff.2 ⟨isRoot_single _ i,
        by rw [height_single]; exact one_pos, i, fun hiA => ha ?_, by simp⟩
      rw [mem_orbitUnion_iff_orbitIndex, (t.mem_orbit_iff).1 hi] at hiA
      exact hiA
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hxQ
    have h' : orbitX t K σ.toRingHom a 1 = orbitX t K σ.toRingHom a 0 := by
      rw [orbitX_zero]
      exact Subtype.ext hxQ
    exact one_ne_zero (orbitX_injective σ.toRingHom a h')

end CFSG.LieType.Chevalley
