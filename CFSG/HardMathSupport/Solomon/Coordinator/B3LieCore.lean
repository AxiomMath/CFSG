module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Core

variable {G : Type*} [Group G]

theorem b3Lie_subnormal_subgroupOf_of_open {X U : Subgroup G} (hUX : U ≤ X)
    (h : CFSG.Open.IsSubnormal U X) : (U.subgroupOf X).IsSubnormal :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_top_iff_mathlib _).1
    ((CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open _ _).2
      ((CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hUX).2 h))

theorem b3Lie_exists_noncomm_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : Subgroup.center Q = ⊤ :=
    (Subgroup.eq_top_iff' _).2 fun a => Subgroup.mem_center_iff.2 fun b => h b a
  have := hQ.2.toNontrivial
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact hxy (QuotientGroup.eq.2 (by rw [hc]; trivial))

variable [Finite G]

theorem b3Lie_comp_le_or_comm {X E U : Subgroup G} (hE : CFSG.Open.IsComponentOf E X)
    (hUX : U ≤ X) (hU : CFSG.Open.IsSubnormal U X) : E ≤ U ∨ ⁅E, U⁆ = ⊥ := by
  have hE' := (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open E X).2 hE
  have hK := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hE.1).1 hE'
  rcases CFSG.LocalCores.component_subnormal_subgroup hK
      (b3Lie_subnormal_subgroupOf_of_open hUX hU) with h | h
  · exact Or.inl (CFSG.LocalCores.le_of_subgroupOf_le hE.1 h)
  · right
    have := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hE.1 h
    rwa [inf_of_le_left hUX] at this

theorem b3Lie_isSubnormal_core (p : ℕ) (X : Subgroup G) :
    CFSG.Open.IsSubnormal (GLAPPrimeCoreOf p X) X := by
  have hnorm : ((GLAPPrimeCoreOf p X).subgroupOf X).Normal := by
    have : (GLAPPrimeCoreOf p X).subgroupOf X = GLAPPrimeCore p ↥X :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    rw [this]
    infer_instance
  exact CFSG.Open.IsSubnormal.step (Subgroup.map_subtype_le _) hnorm
    (CFSG.Open.IsSubnormal.refl X)

theorem glaPComponent_isComponent_of_le_layer {p : ℕ} {X J : Subgroup G}
    (hJ : GLAPComponent p X J) (hle : J ≤ GLALayer X) :
    CFSG.Open.IsComponentOf J X ∧ ¬ J ≤ GLAPPrimeCoreOf p X := by
  set N : Subgroup G := GLAPPrimeCoreOf p X with hN
  let π : ↥X →* (↥X ⧸ GLAPPrimeCore p ↥X) := QuotientGroup.mk' (GLAPPrimeCore p ↥X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hJX : J ≤ X := hJ.1
  have hbar : CFSG.Open.IsComponentOf (barX p X J) ⊤ := hJ.2.2.1
  have hmemN : ∀ x : ↥X, π x = 1 → (x : G) ∈ N := fun x hx =>
    ⟨x, (QuotientGroup.eq_one_iff x).1 hx, rfl⟩
  have hNmem : ∀ x : ↥X, (x : G) ∈ N → π x = 1 := by
    rintro x ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    subst this
    exact (QuotientGroup.eq_one_iff y).2 hy
  have hA : ∃ K : Subgroup G, CFSG.Open.IsComponentOf K X ∧ K ≤ J ∧ ¬ K ≤ N := by
    by_contra hno
    push Not at hno
    set Jb := barX p X J with hJb
    let Kc : Subgroup G := ((Subgroup.centralizer (Jb : Set _)).comap π).map X.subtype
    have h1 : N ≤ Kc := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨y, ?_, rfl⟩
      show π y ∈ Subgroup.centralizer _
      have h1 : π y = 1 := (QuotientGroup.eq_one_iff y).2 hy
      rw [h1]
      exact Subgroup.one_mem _
    have h2 : X ⊓ Subgroup.centralizer (J : Set G) ≤ Kc := by
      rintro z ⟨hzX, hzc⟩
      refine ⟨⟨z, hzX⟩, ?_, rfl⟩
      show π ⟨z, hzX⟩ ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨a, ha, rfl⟩
      show π a * π ⟨z, hzX⟩ = π ⟨z, hzX⟩ * π a
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hzc a.1 ha)
    have h3 : GLALayer X ≤ Kc := by
      refine sSup_le fun K hK => ?_
      by_cases hKN : K ≤ N
      · exact hKN.trans h1
      · have hKJ : ¬ K ≤ J := fun h => hKN (hno K hK h)
        rcases b3Lie_comp_le_or_comm hK hJX hJ.2.1 with h | h
        · exact absurd h hKJ
        · exact (le_inf hK.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h)).trans h2
    have hab : ∀ u ∈ Jb, ∀ v ∈ Jb, u * v = v * u := by
      rintro _ ⟨a, ha, rfl⟩ v hv
      obtain ⟨y, hy, hya⟩ := h3 (hle (show (a : G) ∈ J from ha))
      have hya' : y = a := Subtype.ext hya
      subst hya'
      exact ((Subgroup.mem_centralizer_iff.1 hy) v hv).symm
    obtain ⟨a, b, hab'⟩ := b3Lie_exists_noncomm_of_isQuasisimple hbar.2.2
    exact hab' (Subtype.ext (hab a a.2 b b.2))
  obtain ⟨K, hK, hKJ, hKN⟩ := hA
  have hKX : K ≤ X := hK.1
  have hKb_sn : (barX p X K).IsSubnormal :=
    (b3Lie_subnormal_subgroupOf_of_open hKX hK.2.1).map hπ
  have hJc : CFSG.IsComponent (barX p X J) := (CFSG.isComponent_iff_open _).2 hbar
  have hKbJb : barX p X K ≤ barX p X J :=
    Subgroup.map_mono (Subgroup.comap_mono hKJ)
  have hJK : J = K := by
    rcases CFSG.LocalCores.component_subnormal_subgroup hJc hKb_sn with h | h
    · by_contra hne
      exact hJ.2.2.2 K (lt_of_le_of_ne hKJ (Ne.symm hne)) hK.2.1 (le_antisymm hKbJb h)
    · exfalso
      apply hKN
      have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨hK.2.2.1⟩
      calc K = ⁅K, K⁆ := hperf.symm
        _ ≤ N := by
          refine Subgroup.commutator_le.2 fun a ha b hb => ?_
          have h0 : ⁅π ⟨a, hKX ha⟩, π ⟨b, hKX hb⟩⁆ = 1 := by
            have hm : ⁅π ⟨a, hKX ha⟩, π ⟨b, hKX hb⟩⁆ ∈ ⁅barX p X J, barX p X K⁆ :=
              Subgroup.commutator_mem_commutator
                (hKbJb ⟨⟨a, hKX ha⟩, ha, rfl⟩) ⟨⟨b, hKX hb⟩, hb, rfl⟩
            rw [h] at hm
            exact hm
          rw [← map_commutatorElement] at h0
          exact hmemN _ h0
  subst hJK
  exact ⟨hK, hKN⟩

theorem commutator_glaPLayer_eq_bot_of_perfect_le_layer {p : ℕ} {X : Subgroup G}
    (h : ∀ P : Subgroup G, P ≤ X → ⁅P, P⁆ = P → P ≤ GLALayer X) :
    ⁅GLAPLayer p X, GLAPPrimeCoreOf p X⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine sSup_le fun J hJ => ?_
  obtain ⟨hK, hKN⟩ := glaPComponent_isComponent_of_le_layer hJ
    (h J hJ.1 (glaPComponent_perfect hJ))
  rcases b3Lie_comp_le_or_comm hK (Subgroup.map_subtype_le _) (b3Lie_isSubnormal_core p X)
    with h' | h'
  · exact absurd h' hKN
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h'

end Core

end CFSG.HardMathSupport.Solomon.Coordinator
