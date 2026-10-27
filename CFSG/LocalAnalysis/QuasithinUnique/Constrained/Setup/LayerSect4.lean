module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect3
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect1

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.QuasithinUnique
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

section ActA

variable {L A : Subgroup (V ≃ₗ[k] V)} {I : Submodule k V}
  (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[k] V)))
  (hinvL : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) L I)
  (hinvA : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) A I)

theorem resSub_sup_A (a : ↥A) :
    resSub (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) I (isInvariant_sup_subgroup hinvL hinvA)
        ⟨a, Subgroup.mem_sup_right a.2⟩ =
      resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA a := by
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  rw [resSub_apply, resSub_apply]

theorem actOn_A_mk (a : ↥A) (u : ↥I) :
    actOn L A I hAn (isInvariant_sup_subgroup hinvL hinvA) A le_sup_right a
        (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA a u) := by
  show actW L A I hAn (isInvariant_sup_subgroup hinvL hinvA) ⟨a, Subgroup.mem_sup_right a.2⟩
      (Submodule.Quotient.mk u) = _
  rw [actW_mk, resSub_sup_A hinvL hinvA]

end ActA

variable [CharP k 2] [Finite V]

theorem component_section (hQ : QuadBestOffendersNormalize k V)
    {G L A : Subgroup (V ≃ₗ[k] V)} (hL : IsComponentIn L G) (hAG : A ≤ G)
    (hAel : CFSG.IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (hoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) A)
    (hstrict : ∀ B : Subgroup (V ≃ₗ[k] V), ⊥ < B → B < A →
      weight (MonoidHom.id (V ≃ₗ[k] V)) B < weight (MonoidHom.id (V ≃ₗ[k] V)) A)
    (hcomm : ⁅L, A⁆ ≠ ⊥) : ∃ I : Submodule k V, ComponentSection L A I := by
  classical
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  have hLq : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1) hL.2.1
  obtain ⟨hquad, hnorm⟩ := minimal_best_offenders_normalize_components hQ
    (hAG.trans Subgroup.le_normalizer) hAel hAne hoff hstrict
  have hAL : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[k] V)) := fun a ha =>
    mem_normalizer_of_conjSub_le (le_of_eq (hnorm L hL a ha))
      (le_of_eq (hnorm L hL a⁻¹ (A.inv_mem ha)))
  have hLperf : ⁅L, A⁆ = L := comm_eq_of_quasisimple hLq hAL hcomm
  obtain ⟨I, hgood⟩ := exists_good_perfect (MonoidHom.id (V ≃ₗ[k] V)) L hLq.1
    (not_top_le_fix_of_quasisimple hLq)
  obtain ⟨hno, hch⟩ := noPQuotient_centralPChief_of_quasisimple hLq Nat.prime_two
  have hmax : ∀ B : Subgroup (V ≃ₗ[k] V), B ≤ A →
      weight (MonoidHom.id (V ≃ₗ[k] V)) B ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) A := by
    intro B hB
    rcases hB.lt_or_eq with hlt | heq
    · by_cases hbot : B = ⊥
      · rw [hbot, weight_bot]
        exact hoff
      · exact (hstrict B (bot_lt_iff_ne_bot.2 hbot) hlt).le
    · rw [heq]
  have hinvA : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) A I :=
    bestOffender_invariance_strict (MonoidHom.id (V ≃ₗ[k] V)) L A hAL hAel hLperf hno hch hmax
      hstrict hgood.inv hgood.comm hgood.irr
  have hLA : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) I :=
    isInvariant_sup_subgroup hgood.inv hinvA
  have hX : L ⊔ A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[k] V)) :=
    sup_le Subgroup.le_normalizer hAL
  have hinj : ∀ x : ↥(L ⊔ A), actW L A I hAL hLA x = 1 →
      resSub (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) I hLA x = 1 := by
    intro x hx
    have key := detect_of_trivial_mod (MonoidHom.id (V ≃ₗ[k] V)) L (L ⊔ A) hX hno hch I
      hgood.inv hLA hgood.comm x.2 (disp_mem_fix_of_actW_eq_one hAL hLA hx)
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [resSub_apply]
    exact key w w.2
  have hLbar_ne : (actOn L A I hAL hLA L le_sup_left).range ≠ ⊥ := by
    intro h
    have h1 : actOn L A I hAL hLA L le_sup_left = 1 := MonoidHom.range_eq_bot_iff.1 h
    apply hgood.irr.1
    calc I = commSub (MonoidHom.id (V ≃ₗ[k] V)) L I := hgood.comm.symm
      _ ≤ fixSub (MonoidHom.id (V ≃ₗ[k] V)) L := by
        rw [commSub_le_iff]
        intro l hl u hu
        have h2 : actW L A I hAL hLA ⟨l, Subgroup.mem_sup_left hl⟩ = 1 := by
          have := congrArg (fun φ => φ ⟨l, hl⟩) h1
          exact this
        exact disp_mem_fix_of_actW_eq_one hAL hLA h2 u hu
  have hLbar_qs : CFSG.IsQuasisimple ↥(actOn L A I hAL hLA L le_sup_left).range := by
    set f := actOn L A I hAL hLA L le_sup_left with hf
    have hker : f.rangeRestrict.ker ≤ Subgroup.center ↥L := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq
        (MonoidHom.normal_ker f.rangeRestrict) with h | h
      · exfalso
        apply hLbar_ne
        rw [MonoidHom.range_eq_bot_iff]
        refine MonoidHom.ext fun x => ?_
        have hx : x ∈ f.rangeRestrict.ker := by rw [h]; trivial
        rw [MonoidHom.ker_rangeRestrict] at hx
        exact MonoidHom.mem_ker.1 hx
      · exact h
    exact CFSG.LocalCores.isQuasisimple_of_surjective hLq f.rangeRestrict
      f.rangeRestrict_surjective hker
  have hAbar_ne : (actOn L A I hAL hLA A le_sup_right).range ≠ ⊥ := by
    intro h
    have h1 : actOn L A I hAL hLA A le_sup_right = 1 := MonoidHom.range_eq_bot_iff.1 h
    apply hLbar_ne
    rw [MonoidHom.range_eq_bot_iff]
    have hLle' : ⁅L, A⁆ ≤ (actW L A I hAL hLA).ker.map (L ⊔ A).subtype := by
      refine Subgroup.commutator_le.2 fun l hl a ha => ?_
      have h2 : actW L A I hAL hLA ⟨a, Subgroup.mem_sup_right ha⟩ = 1 := by
        have := congrArg (fun φ => φ ⟨a, ha⟩) h1
        exact this
      have hmem : ⁅(⟨l, Subgroup.mem_sup_left hl⟩ : ↥(L ⊔ A)), ⟨a, Subgroup.mem_sup_right ha⟩⁆ ∈
          (actW L A I hAL hLA).ker := by
        rw [MonoidHom.mem_ker, map_commutatorElement, h2, commutatorElement_one_right]
      exact ⟨_, hmem, rfl⟩
    have hLle : L ≤ (actW L A I hAL hLA).ker.map (L ⊔ A).subtype :=
      (le_of_eq hLperf.symm).trans hLle'
    refine MonoidHom.ext fun ⟨l, hl⟩ => ?_
    obtain ⟨y, hy, hyl⟩ := hLle hl
    have : y = ⟨l, Subgroup.mem_sup_left hl⟩ := Subtype.ext hyl
    rw [this] at hy
    exact MonoidHom.mem_ker.1 hy
  have hAbar_elem : CFSG.IsElementaryAbelian 2
      ↥(actOn L A I hAL hLA A le_sup_right).range := isElementaryAbelian_range _ hAel
  have hAbar_quad : QuadAct (MonoidHom.id ((↥I ⧸ fixIn L I) ≃ₗ[k] _))
      (actOn L A I hAL hLA A le_sup_right).range := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩ w
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    show actOn L A I hAL hLA A le_sup_right a'
        (actOn L A I hAL hLA A le_sup_right a (Submodule.Quotient.mk u) - Submodule.Quotient.mk u) =
      actOn L A I hAL hLA A le_sup_right a (Submodule.Quotient.mk u) - Submodule.Quotient.mk u
    have hq : resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA a'
        (resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA a u - u) =
        resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA a u - u := by
      apply Subtype.ext
      rw [resSub_apply, Submodule.coe_sub, resSub_apply]
      exact hquad a a.2 a' a'.2 (u : V)
    have hq' := congrArg (Submodule.Quotient.mk (p := fixIn L I)) hq
    rw [map_sub, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub] at hq'
    rw [map_sub, actOn_A_mk hAL hgood.inv hinvA a u, actOn_A_mk hAL hgood.inv hinvA a' u,
      actOn_A_mk hAL hgood.inv hinvA a' _]
    exact hq'
  let ρA : ↥A →* (V ≃ₗ[k] V) := (MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype
  have hρW : ∀ a : ↥A, ∀ w ∈ I, ρA a w ∈ I := fun a w hw => hinvA a a.2 w hw
  have hmaxρ : ∀ B : Subgroup ↥A, weight ρA B ≤ weight ρA ⊤ := by
    intro B
    show weight ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) B ≤
      weight ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) ⊤
    rw [weight_comp_subtype, weight_comp_subtype, map_subtype_top]
    exact hmax _ (Subgroup.map_subtype_le B)
  have hstrictρ : ∀ B : Subgroup ↥A, ⊥ < B → B < ⊤ → weight ρA B < weight ρA ⊤ := by
    intro B hB1 hB2
    show weight ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) B <
      weight ((MonoidHom.id (V ≃ₗ[k] V)).comp A.subtype) ⊤
    rw [weight_comp_subtype, weight_comp_subtype, map_subtype_top]
    refine hstrict _ ?_ ?_
    · rw [bot_lt_iff_ne_bot, Ne, Subgroup.map_eq_bot_iff_of_injective B A.subtype_injective]
      exact bot_lt_iff_ne_bot.1 hB1
    · exact ((Subgroup.map_lt_map_iff_of_injective A.subtype_injective).2 hB2).trans_eq
        (map_subtype_top A)
  have hWA : commSub ρA ⊤ I ≠ ⊥ := by
    intro h
    have hAtriv : ∀ a ∈ A, ∀ u ∈ I, a u = u := fun a ha u hu =>
      (commSub_eq_bot_iff ρA ⊤ I).1 h ⟨a, ha⟩ (Subgroup.mem_top _) u hu
    have := trivial_of_trivial_A hLperf hgood.inv hAtriv
    exact hgood.irr.1 (fun u hu l hl => this l hl u hu)
  obtain ⟨hAI_max, hAI_strict, -⟩ :=
    minimal_fixedWeight_restriction_faithful_splitting ρA I hρW hmaxρ hstrictρ hWA
  have hAbar_off : Nat.card (↥I ⧸ fixIn L I) ≤
      weight (MonoidHom.id ((↥I ⧸ fixIn L I) ≃ₗ[k] _))
        (actOn L A I hAL hLA A le_sup_right).range := by
    let AI := (resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA).range
    have h1 : Nat.card ↥I ≤ weight (MonoidHom.id (↥I ≃ₗ[k] ↥I)) AI :=
      natCard_le_weight_res (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA hmax
    let ρ' : ↥AI →* (↥I ≃ₗ[k] ↥I) := (MonoidHom.id (↥I ≃ₗ[k] ↥I)).comp AI.subtype
    have hρ'w : weight ρ' ⊤ = weight (MonoidHom.id (↥I ≃ₗ[k] ↥I)) AI := by
      show weight ((MonoidHom.id (↥I ≃ₗ[k] ↥I)).comp AI.subtype) ⊤ = _
      rw [weight_comp_subtype, map_subtype_top]
    have hZ' : ∀ x : ↥AI, ∀ z ∈ fixIn L I, ρ' x z ∈ fixIn L I := by
      rintro ⟨_, a, rfl⟩ z hz
      exact fixIn_invariant hAL hinvA a z hz
    have h2 := natCard_quotient_le_weight ρ' (fixIn L I) hZ' (by rw [hρ'w]; exact h1)
    let π := quotHom ρ' (fixIn L I) hZ'
    let s : ↥A →* ↥AI := (resSub (MonoidHom.id (V ≃ₗ[k] V)) A I hinvA).rangeRestrict
    have hs : Function.Surjective s := MonoidHom.rangeRestrict_surjective _
    have hcomp : π.comp s = actOn L A I hAL hLA A le_sup_right := by
      refine MonoidHom.ext fun a => LinearEquiv.ext fun w => ?_
      obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
      rw [MonoidHom.comp_apply, quotHom_mk, actOn_A_mk hAL hgood.inv hinvA a u]
      rfl
    have hπinj : Function.Injective π := by
      rw [injective_iff_map_eq_one]
      intro y hy
      obtain ⟨a, rfl⟩ := hs y
      have h3 : actW L A I hAL hLA ⟨a, Subgroup.mem_sup_right a.2⟩ = 1 := by
        have h4 : (π.comp s) a = 1 := hy
        rw [hcomp] at h4
        exact h4
      have h5 := hinj _ h3
      rw [resSub_sup_A hgood.inv hinvA] at h5
      exact Subtype.ext h5
    have hrange : π.range = (actOn L A I hAL hLA A le_sup_right).range := by
      rw [← hcomp, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hs]
      exact MonoidHom.range_eq_map π
    calc Nat.card (↥I ⧸ fixIn L I) ≤ weight π ⊤ := h2
      _ = weight (MonoidHom.id ((↥I ⧸ fixIn L I) ≃ₗ[k] _)) π.range :=
        (weight_range_of_injective π hπinj).symm
      _ = _ := by rw [hrange]
  exact ⟨I,
    { A_norm := hAL
      L_perf := hLperf
      inv_L := hgood.inv
      inv_A := hinvA
      comm := hgood.comm
      irr := hgood.irr
      inj := hinj
      Lbar_ne := hLbar_ne
      Lbar_qs := hLbar_qs
      Abar_ne := hAbar_ne
      Abar_elem := hAbar_elem
      Abar_off := hAbar_off
      Abar_quad := hAbar_quad
      AI_max := hAI_max
      AI_strict := hAI_strict }⟩

end CFSG.QuasithinUnique.Setup.Layer
