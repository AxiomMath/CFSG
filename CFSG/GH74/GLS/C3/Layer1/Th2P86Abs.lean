module

public import CFSG.GH74.GLS.C3.Layer1.Th2P85Defs
public import CFSG.GH74.GLS.C3.Layer1.EvenCore
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.GH74.GLS.C3.Layer1.EvenCoreSC

public section

namespace CFSG.GH74.GLS.Th2.P85

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification CFSG.GH74.GLS.EvenCore
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem isSimpleSocle_top_of_component (hcore : pPrimeCore 2 X = ⊥) {Λ : Subgroup X}
    (hΛ : CFSG.IsComponent Λ)
    (hno : ∀ b : X, orderOf b = 2 → ¬ Λ ≤ centralizer ({b} : Set X)) :
    IsSimpleSocle Λ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΛlayer : Λ ≤ CFSG.layer X := CFSG.LocalCores.component_le_layer hΛ
  have hcent : ∀ b : X, orderOf b = 2 → ¬ (∀ l ∈ Λ, b * l = l * b) := fun b hb2 h =>
    hno b hb2 fun l hl => mem_centralizer_singleton_iff.2 (h l hl).symm
  have hF : fittingSubgroup X = ⊥ := by
    by_contra hne
    have hFn : (fittingSubgroup X).Normal := inferInstance
    have hFp : IsPGroup 2 ↥(fittingSubgroup X) :=
      isPGroup_of_nilpotent_normal (fittingSubgroup X) hFn inferInstance hcore
    obtain ⟨b, hbF, hb2⟩ := Th2.exists_involution_mem hFp hne
    have hcomm : ⁅fittingSubgroup X, CFSG.layer X⁆ = ⊥ := CFSG.LocalCores.fitting_layer_commute
    refine hcent b hb2 fun l hl => ?_
    have h1 := Subgroup.commutator_mem_commutator hbF (hΛlayer hl)
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hall : ∀ M : Subgroup X, CFSG.IsComponent M → M = Λ := by
    intro M hM
    by_contra hne
    have hcomm : ⁅M, Λ⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hM hΛ).resolve_left hne
    obtain ⟨b, hbM, hb2⟩ := exists_involution_of_isComponent hM
    refine hcent b hb2 fun l hl => ?_
    have h1 := Subgroup.commutator_mem_commutator hbM hl
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hlayer : CFSG.layer X = Λ := by
    simp only [CFSG.layer.eq_sSup]
    have hset : {M : Subgroup X | CFSG.IsComponent M} = {Λ} := by
      ext M
      exact ⟨fun hM => hall M hM, fun h => by rw [Set.mem_singleton_iff] at h; rw [h]; exact hΛ⟩
    rw [hset, sSup_singleton]
  have hLn : Λ.Normal := by
    rw [← hlayer]
    have := CFSG.LocalCores.layer_characteristic (G := X)
    infer_instance
  have hZ : center ↥Λ = ⊥ := by
    have := hLn
    have hnormal : ((center ↥Λ).map Λ.subtype).Normal := inferInstance
    have : Group.IsNilpotent ↥((center ↥Λ).map Λ.subtype) :=
      Group.nilpotent_of_mulEquiv ((center ↥Λ).equivMapOfInjective Λ.subtype Λ.subtype_injective)
    have hle : (center ↥Λ).map Λ.subtype ≤ fittingSubgroup X := le_sSup ⟨hnormal, inferInstance⟩
    rw [hF, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ Λ.subtype_injective).mp hle
  have hLsimple : IsSimpleGroup ↥Λ := by
    have hs : IsSimpleGroup (↥Λ ⧸ center ↥Λ) := hΛ.1.2.1
    let e : ↥Λ ≃* (↥Λ ⧸ center ↥Λ) :=
      (QuotientGroup.quotientBot (G := ↥Λ)).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    exact e.isSimpleGroup
  have hFstar : CFSG.Open.genFittingFStar X = Λ := by
    have h1 : CFSG.Open.genFittingFitting X = ⊥ := by
      have : CFSG.Open.genFittingFitting X = fittingSubgroup X := rfl
      rw [this, hF]
    have h2 : CFSG.Open.genFittingLayer X = Λ := by
      simp only [CFSG.Open.genFittingLayer.eq_sSup]
      apply le_antisymm
      · refine sSup_le fun M hM => ?_
        exact (hall M ((CFSG.isComponent_iff_open M).mpr hM)).le
      · exact le_sSup ((CFSG.isComponent_iff_open Λ).mp hΛ)
    simp only [CFSG.Open.genFittingFStar.eq_sup]
    rw [h1, h2, bot_sup_eq]
  have hCent : ∀ n : X, (∀ l ∈ Λ, n * l = l * n) → n = 1 := by
    intro n hn
    have hmem : n ∈ centralizer (CFSG.Open.genFittingFStar X : Set X) := by
      rw [hFstar, mem_centralizer_iff]
      intro l hl
      exact (hn l hl).symm
    have hnL : n ∈ Λ := by
      have := CFSG.Adapters.generalized_fitting_self_centralizing X hmem
      rwa [hFstar] at this
    have hnz : (⟨n, hnL⟩ : ↥Λ) ∈ center ↥Λ := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hn g g.2).symm
    rw [hZ, Subgroup.mem_bot] at hnz
    exact congrArg Subtype.val hnz
  exact ⟨le_top, fun n _ l hl => hLn.conj_mem l hl n, hLsimple, fun n _ hnc => hCent n hnc⟩

omit [Finite X] in
theorem orderOf_mul_eq_two_of_commute {u v : X} (hu : orderOf u = 2) (hv : orderOf v = 2)
    (huv : u * v = v * u) (hne : u ≠ v) : orderOf (u * v) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · have h1 : u * u = 1 := by rw [← pow_two, ← hu]; exact pow_orderOf_eq_one u
    have h2 : v * v = 1 := by rw [← pow_two, ← hv]; exact pow_orderOf_eq_one v
    calc (u * v) ^ 2 = u * v * (u * v) := pow_two _
      _ = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [huv]
      _ = u * u * (v * v) := by group
      _ = 1 := by rw [h1, h2, one_mul]
  · intro h
    apply hne
    have hv' : v⁻¹ = v := inv_eq_self_of_orderOf_eq_two hv
    rw [mul_eq_one_iff_eq_inv, hv'] at h
    exact h

theorem exists_component_ge_of_terminal (hcore : pPrimeCore 2 X = ⊥) {K : Subgroup X}
    (hterm : IsTerminalSub K) {u v : X} (hu : orderOf u = 2) (hv : orderOf v = 2)
    (huv : u * v = v * u) (hne : u ≠ v) (huK : ∀ k ∈ K, u * k = k * u)
    (hvK : ∀ k ∈ K, v * k = k * v) : ∃ Λ : Subgroup X, CFSG.IsComponent Λ ∧ K ≤ Λ := by
  have hw : orderOf (u * v) = 2 := orderOf_mul_eq_two_of_commute hu hv huv hne
  have hwK : ∀ k ∈ K, (u * v) * k = k * (u * v) := by
    intro k hk
    rw [mul_assoc, hvK k hk, ← mul_assoc, huK k hk, mul_assoc]
  have key : ∀ b : X, orderOf b = 2 → (∀ k ∈ K, b * k = k * b) →
      K ≤ centralizer ({b} : Set X) ∧
        TwoComponents.IsTwoComponent (K.subgroupOf (centralizer ({b} : Set X))) := by
    intro b hb2 hbK
    have h := hterm b hb2 hbK
    exact TwoThin.isPCompIn_two_iff.1
      ⟨h.1, CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent h.2⟩
  exact exists_component_ge_of_fourGroup hcore hu hv huv hne (key u hu huK) (key v hv hvK)
    (key _ hw hwK)

omit [Finite X] in
theorem eq_component_of_minSubnormal {K L Λ : Subgroup X} (hKq : CFSG.IsQuasisimple ↥K)
    (hKΛ : K ≤ Λ) (hΛ : CFSG.IsComponent Λ) (hKL : K ≤ L) (hLsub : L.IsSubnormal)
    (hmin : ∀ J : Subgroup X, K ≤ J → J ≤ L → J.IsSubnormal → J = L) : L = Λ := by
  have hLΛ : L ≤ Λ := inf_eq_left.1 (hmin (L ⊓ Λ) (le_inf hKL hKΛ) inf_le_left (hLsub.inf hΛ.2))
  have hsub : (L.subgroupOf Λ).IsSubnormal := hLsub.subgroupOf
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hΛ.1 hsub with h | h
  · exact le_antisymm hLΛ (Subgroup.subgroupOf_eq_top.1 h)
  · exfalso
    have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hKq.1
    have hKcomm : ⁅K, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro k1 hk1
      rw [mem_centralizer_iff]
      intro k2 hk2
      have h1 : (⟨k1, hKΛ hk1⟩ : ↥Λ) ∈ L.subgroupOf Λ := hKL hk1
      have h2 := Subgroup.mem_center_iff.mp (h h1) ⟨k2, hKΛ hk2⟩
      exact congrArg Subtype.val h2
    have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
    have hbot : K = ⊥ := by rw [← hKperf]; exact hKcomm
    exact (Subgroup.nontrivial_iff_ne_bot K).1 this hbot

omit [Finite X] in
theorem not_le_centralizer_of_minSubnormal {K L : Subgroup X} (hKL : K ≤ L) (hLsub : L.IsSubnormal)
    (hmin : ∀ J : Subgroup X, K ≤ J → J ≤ L → J.IsSubnormal → J = L) (hne : K ≠ L)
    (hterm : IsTerminalSub K) {b : X} (hb2 : orderOf b = 2) :
    ¬ L ≤ centralizer ({b} : Set X) := by
  intro hLC
  have hbK : ∀ k ∈ K, b * k = k * b := fun k hk =>
    (mem_centralizer_singleton_iff.1 (hLC (hKL hk))).symm
  have hcomp := hterm b hb2 hbK
  have hsubC : (K.subgroupOf (centralizer ({b} : Set X))).IsSubnormal := hcomp.2.2
  have hKsubL : (K.subgroupOf L).IsSubnormal := by
    have h1 := hsubC.comap (Subgroup.inclusion hLC)
    have heq : (K.subgroupOf (centralizer ({b} : Set X))).comap (Subgroup.inclusion hLC) =
        K.subgroupOf L := by
      ext l
      rfl
    rwa [heq] at h1
  have hKsub : K.IsSubnormal := Subgroup.IsSubnormal.trans hKL hKsubL hLsub
  exact hne (hmin K le_rfl hKL hKsub)

theorem isSimpleSocle_of_terminal (hcore : pPrimeCore 2 X = ⊥) {K L : Subgroup X}
    (hKq : CFSG.IsQuasisimple ↥K) (hterm : IsTerminalSub K) {u v : X} (hu : orderOf u = 2)
    (hv : orderOf v = 2) (huv : u * v = v * u) (hne : u ≠ v) (huK : ∀ k ∈ K, u * k = k * u)
    (hvK : ∀ k ∈ K, v * k = k * v) (hKL : K ≤ L) (hLsub : L.IsSubnormal)
    (hmin : ∀ J : Subgroup X, K ≤ J → J ≤ L → J.IsSubnormal → J = L) (hKne : K ≠ L) :
    IsSimpleSocle L ⊤ := by
  obtain ⟨Λ, hΛ, hKΛ⟩ := exists_component_ge_of_terminal hcore hterm hu hv huv hne huK hvK
  have hLΛ : L = Λ := eq_component_of_minSubnormal hKq hKΛ hΛ hKL hLsub hmin
  subst hLΛ
  exact isSimpleSocle_top_of_component hcore hΛ fun b hb2 =>
    not_le_centralizer_of_minSubnormal hKL hLsub hmin hKne hterm hb2

end CFSG.GH74.GLS.Th2.P85
