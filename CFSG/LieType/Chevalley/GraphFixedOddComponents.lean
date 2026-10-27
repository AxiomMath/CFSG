module

public import CFSG.LieType.Chevalley.GraphFixedNoncentralSolvable
public import CFSG.LieType.Chevalley.GraphFixedOddPerfect
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientComponents
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped commutatorElement
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
open CFSG.LocalAnalysis.ComponentInitial (isQuasisimple_congr quasisimple_subnormal_subgroups)

theorem odd_diagram_field_fixed_p_components
    (t : TwistTag) (K : Type) [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (σ : K ≃+* K) :
    IsSimpleGroup (graphFixedRootGroup t K σ.toRingHom) ∧
    (∃ x y : graphFixedRootGroup t K σ.toRingHom, x * y ≠ y * x) ∧
    ∀ p : ℕ, p.Prime → ∀ L : Subgroup (twistedFixedGroup t K σ.toRingHom),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L ∧
        L = (graphFixedRootGroup t K σ.toRingHom).subgroupOf
          (twistedFixedGroup t K σ.toRingHom) := by
  obtain ⟨hperf, ⟨x, hx, y, hy, hxy⟩, -⟩ := odd_diagram_fixed_root_group_perfect t K hK σ
  have hnc : ∃ a b : graphFixedRootGroup t K σ.toRingHom, a * b ≠ b * a :=
    ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  have : Group.IsPerfect (graphFixedRootGroup t K σ.toRingHom) := Subgroup.isPerfect_iff.2 hperf
  have : Nontrivial (graphFixedRootGroup t K σ.toRingHom) := by
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨⟨a * b, b * a, hab⟩⟩
  have hZ := exceptional_fixed_center_trivial t K σ
  have hsimple : IsSimpleGroup (graphFixedRootGroup t K σ.toRingHom) := by
    refine IsSimpleGroup.mk fun M hM => ?_
    by_cases hbot : M = ⊥
    · exact Or.inl hbot
    · right
      have hnot : ¬ M ≤ Subgroup.center (graphFixedRootGroup t K σ.toRingHom) := by
        rw [hZ]
        exact fun h => hbot (le_bot_iff.1 h)
      have hsolv := fixed_noncentral_normal_solvable_quotient t K σ M hnot
      by_contra htop
      have : Nontrivial (graphFixedRootGroup t K σ.toRingHom ⧸ M) := by
        rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
        exact htop
      exact Group.IsPerfect.not_isSolvable _ hsolv
  have hquasi := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  refine ⟨hsimple, hnc, fun p hp L hL => ?_⟩
  have hCΓ : graphFixedRootGroup t K σ.toRingHom ≤ twistedFixedGroup t K σ.toRingHom :=
    graphFixedRootGroup_le t K σ.toRingHom
  have hfin : Finite (ModGL t.tag K) := finite_modGL
  obtain ⟨hNnormal, -, hcomm, -, -⟩ := fixed_root_generated_normal_subgroup t K σ
  have : Group.IsSolvable (twistedFixedGroup t K σ.toRingHom ⧸
      (graphFixedRootGroup t K σ.toRingHom).subgroupOf (twistedFixedGroup t K σ.toRingHom)) :=
    Group.isSolvable_of_comm fun a b => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have e : ((a * b)⁻¹ * (b * a) : twistedFixedGroup t K σ.toRingHom) = ⁅b⁻¹, a⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact hcomm (Subgroup.commutator_mem_commutator (inv_mem b.2) (inv_mem a.2))
  obtain ⟨hLN, hLN'⟩ :=
    (p_components_solvable_quotient_invariance
      p hp ((graphFixedRootGroup t K σ.toRingHom).subgroupOf (twistedFixedGroup t K σ.toRingHom))
        L).1 hL
  let e : (graphFixedRootGroup t K σ.toRingHom).subgroupOf (twistedFixedGroup t K σ.toRingHom) ≃*
      graphFixedRootGroup t K σ.toRingHom := Subgroup.subgroupOfEquivOfLe hCΓ
  have hNq : CFSG.IsQuasisimple
      ((graphFixedRootGroup t K σ.toRingHom).subgroupOf (twistedFixedGroup t K σ.toRingHom)) :=
    (isQuasisimple_congr e).2
    hquasi
  have hNZ : Subgroup.center
      ((graphFixedRootGroup t K σ.toRingHom).subgroupOf (twistedFixedGroup t K σ.toRingHom)) =
        ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center (graphFixedRootGroup t K σ.toRingHom) :=
      Subgroup.mem_center_iff.2 fun g => by
        obtain ⟨g', rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g']
    rw [hZ, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (e.injective (hz'.trans (map_one e).symm))
  have hLsub : (L.subgroupOf ((graphFixedRootGroup t K σ.toRingHom).subgroupOf
      (twistedFixedGroup t K σ.toRingHom))).IsSubnormal :=
    hLN'.choose_spec.2.1
  have hLnt := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_nontrivial hLN'
  rcases quasisimple_subnormal_subgroups hNq hLsub with h | h
  · have hLeq : L = (graphFixedRootGroup t K σ.toRingHom).subgroupOf
        (twistedFixedGroup t K σ.toRingHom) := by
      refine le_antisymm hLN fun g hg => ?_
      have : (⟨g, hg⟩ : (graphFixedRootGroup t K σ.toRingHom).subgroupOf
          (twistedFixedGroup t K σ.toRingHom)) ∈ L.subgroupOf
            ((graphFixedRootGroup t K σ.toRingHom).subgroupOf
              (twistedFixedGroup t K σ.toRingHom)) := by
        rw [h]
        trivial
      exact this
    refine ⟨?_, hLeq⟩
    rw [hLeq]
    exact hNq
  · rw [hNZ] at h
    exfalso
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := hLnt
    apply hab
    have ha' := le_bot_iff.1 h ▸ ha
    have hb' := le_bot_iff.1 h ▸ hb
    rw [Subgroup.mem_bot] at ha' hb'
    exact Subtype.ext (ha'.trans hb'.symm)

end CFSG.LieType.Chevalley
