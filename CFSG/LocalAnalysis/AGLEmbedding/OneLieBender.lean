module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
import CFSG.GroupTheory.GroupAction.CyclicPrimePower

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Abstract

variable {X : Type*} [Group X] [Finite X]

theorem mem_centralizer_of_isCyclic_of_coprime {p : ℕ} (hp : p.Prime) {O W : Subgroup X}
    [O.Normal] (hOc : IsCyclic O) (hO : IsPGroup p O) (hWO : W ≤ O) (hW : W ≠ ⊥) {y : X}
    (hyW : y ∈ Subgroup.centralizer (W : Set X)) (hy : (orderOf y).Coprime p) :
    y ∈ Subgroup.centralizer (O : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  have := hOc
  set E : Subgroup (MulAut O) := (Subgroup.zpowers y).map (MulAut.conjNormal (H := O))
  have hcop : Nat.Coprime (Nat.card E) (Nat.card O) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hO
    rw [hk]
    have hEy : Nat.card E ∣ orderOf y := by
      rw [← Nat.card_zpowers y]
      exact Subgroup.card_map_dvd (H := Subgroup.zpowers y) _
    exact Nat.Coprime.pow_right k (Nat.Coprime.coprime_dvd_left hEy hy)
  have hfix : CFSG.fixedPointSubgroup E O ≠ ⊥ := by
    obtain ⟨⟨w, hwW⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hW
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨⟨w, hWO hwW⟩, fun e => ?_⟩, ?_⟩
    · obtain ⟨_, g, hg, rfl⟩ := e
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      apply Subtype.ext
      change ((MulAut.conjNormal (y ^ j) ⟨w, hWO hwW⟩ : O) : X) = w
      rw [MulAut.conjNormal_apply]
      have hyj : y ^ j ∈ Subgroup.centralizer (W : Set X) := Subgroup.zpow_mem _ hyW j
      rw [← Subgroup.mem_centralizer_iff.mp hyj w hwW, mul_inv_cancel_right]
    · intro h1
      apply hw1
      exact Subtype.ext (congrArg (fun x : CFSG.fixedPointSubgroup E O => ((x : O) : X)) h1)
  have htriv := CFSG.actsTrivially_of_cyclic_pGroup_of_nontrivial_fixedPointSubgroup
    (Q := O) (E := E) p hp hO hcop hfix
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 := congrArg Subtype.val
    (htriv ⟨MulAut.conjNormal y, Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers y)⟩ ⟨x, hx⟩)
  change ((MulAut.conjNormal y ⟨x, hx⟩ : O) : X) = x at h1
  rw [MulAut.conjNormal_apply] at h1
  calc x * y = y * x * y⁻¹ * y := by rw [h1]
    _ = y * x := by group

theorem centralizer_pCore_le_pCore_of_forall {p : ℕ}
    (hcomp : ∀ L : Subgroup X, ¬ IsComponentOf L ⊤)
    (hcore : ∀ q : ℕ, q.Prime → q ≠ p → CFSG.pCore q X = ⊥) :
    Subgroup.centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X := by
  have hF : ComponentClassification.GeneralizedFitting.subgroup X ≤ CFSG.pCore p X := by
    refine sup_le (sSup_le fun N hN => ?_) (sSup_le fun L hL => (hcomp L hL).elim)
    refine (CFSG.normal_nilpotent_le_sup_pCore hN.1 hN.2).trans (iSup_le fun q => ?_)
    by_cases hq : (q.1 : ℕ) = p
    · rw [hq]
    · rw [hcore _ (Nat.prime_of_mem_primeFactors q.1.2) hq]
      exact bot_le
  exact (Subgroup.centralizer_le hF).trans
    ((ComponentClassification.GeneralizedFitting.centralizer_le X).trans hF)

end Abstract

section Reduced

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem le_inf_of_normal_subgroupOf {C W : Subgroup Y} [C.Normal] [Fact p.Prime] (R : Sylow p Y)
    (hWC : W ≤ C) (hWp : IsPGroup p W) (hCW : C ≤ Subgroup.normalizer (W : Set Y)) :
    W ≤ (R : Subgroup Y) ⊓ C := by
  obtain ⟨P₀, hP₀⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R
    (inferInstance : C.Normal).isSubnormal
  have : (W.subgroupOf C).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWC).mpr hCW
  rw [← hP₀, ← Subgroup.map_subgroupOf_eq_of_le hWC]
  exact Subgroup.map_mono (IsPGroup.le_sylow_of_normal (N := W.subgroupOf C) hWp.comap_subtype P₀)

theorem ReducedNongeneration.false_of_isComponentOf_le (h : ReducedNongeneration p Y Rb Y₀)
    {C W L : Subgroup Y} [C.Normal]
    (hcyc : ∀ A : Subgroup Y, A ≤ C → IsPGroup p A → IsCyclic A) (hWC : W ≤ C) (hW1 : W ≠ ⊥)
    (hWp : IsPGroup p W) (hCW : C ≤ Subgroup.normalizer (W : Set Y))
    (hL : IsComponentOf L ⊤) (hLC : L ≤ C) : False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ⟨htR, htL⟩, ht, htC⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot Rb hL
  have hWS := le_inf_of_normal_subgroupOf Rb hWC hWp hCW
  have hS : IsCyclic ((Rb : Subgroup Y) ⊓ C : Subgroup Y) :=
    hcyc _ inf_le_right (Rb.isPGroup'.to_le inf_le_left)
  obtain ⟨w, hw⟩ : ∃ w : W, orderOf w = p := by
    have : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hW1
    obtain ⟨k, hk, hWk⟩ := hWp.nontrivial_iff_card.mp this
    exact exists_prime_orderOf_dvd_card' p (hWk ▸ dvd_pow_self p (Nat.ne_of_gt hk))
  have htW : t ∈ W := by
    have hts : t ∈ (Rb : Subgroup Y) ⊓ C := ⟨htR, hLC htL⟩
    have hws : (w : Y) ∈ (Rb : Subgroup Y) ⊓ C := hWS w.2
    have heq : Subgroup.zpowers (⟨t, hts⟩ : ((Rb : Subgroup Y) ⊓ C : Subgroup Y)) =
        Subgroup.zpowers ⟨w, hws⟩ := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
        Subgroup.orderOf_mk, Subgroup.orderOf_mk, ht, Subgroup.orderOf_coe, hw]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (heq ▸ Subgroup.mem_zpowers _ :
      (⟨t, hts⟩ : ((Rb : Subgroup Y) ⊓ C : Subgroup Y)) ∈ Subgroup.zpowers ⟨w, hws⟩)
    have hk' : (w : Y) ^ k = t := congrArg Subtype.val hk
    rw [← hk']
    exact W.zpow_mem w.2 k
  have hV : ((W ⊓ L).subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    exact le_trans (le_inf (hLC.trans hCW) Subgroup.le_normalizer)
      Subgroup.inf_normalizer_le_normalizer_inf
  apply htC
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  rcases ComponentClassification.Quasisimple.normal_le_center_or_eq_top hL.2.2
      ((W ⊓ L).subgroupOf L) with hc | htop
  · have htZ : (⟨t, htL⟩ : L) ∈ Subgroup.center L := hc (Subgroup.mem_subgroupOf.mpr ⟨htW, htL⟩)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp htZ ⟨l, hl⟩)
  · have hlW : l ∈ W := ((Subgroup.subgroupOf_eq_top.mp htop) hl).1
    have : IsCyclic W := hcyc W hWC hWp
    exact congrArg Subtype.val
      ((isMulCommutative_iff.mp inferInstance) (⟨l, hlW⟩ : W) ⟨t, htW⟩)

theorem ReducedNongeneration.pCore_eq_bot_of_ne (h : ReducedNongeneration p Y Rb Y₀)
    (C : Subgroup Y) [C.Normal] {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) : CFSG.pCore q C = ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  have hcop : p.Coprime (Nat.card ((CFSG.pCore q C).map C.subtype)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((CFSG.pCore_isPGroup (p := q) (G := C)).map C.subtype)
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes h.prime hq).mpr (Ne.symm hqp))
  have hle := normal_coprime_le_primeComplementCore p _ inferInstance hcop
  rwa [h.core_eq_bot, le_bot_iff,
    Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective] at hle

theorem ReducedNongeneration.inf_centralizer_le_of_isCyclic (h : ReducedNongeneration p Y Rb Y₀)
    {C W : Subgroup Y} [C.Normal]
    (hcyc : ∀ A : Subgroup Y, A ≤ C → IsPGroup p A → IsCyclic A) (hWC : W ≤ C) (hW1 : W ≠ ⊥)
    (hWp : IsPGroup p W) (hCW : C ≤ Subgroup.normalizer (W : Set Y)) :
    C ⊓ Subgroup.centralizer (W : Set Y) ≤ Rb := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcomp : ∀ L : Subgroup C, ¬ IsComponentOf L ⊤ := fun L hL =>
    h.false_of_isComponentOf_le hcyc hWC hW1 hWp hCW
      (ComponentClassification.LocalComponents.of_subnormal_subgroup C
        (ComponentClassification.Components.chain_of_mathlib_subnormal
          (inferInstance : C.Normal).isSubnormal) L hL) (Subgroup.map_subtype_le L)
  have hB := centralizer_pCore_le_pCore_of_forall (p := p) hcomp
    fun q hq hqp => h.pCore_eq_bot_of_ne C hq hqp
  have hOp : IsPGroup p (CFSG.pCore p C) := CFSG.pCore_isPGroup
  have hOc : IsCyclic (CFSG.pCore p C) := by
    have := hcyc _ (Subgroup.map_subtype_le (CFSG.pCore p C)) (hOp.map C.subtype)
    exact isCyclic_of_surjective ((CFSG.pCore p C).equivMapOfInjective C.subtype
      C.subtype_injective).symm.toMonoidHom (MulEquiv.surjective _)
  have hWn : (W.subgroupOf C).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWC).mpr hCW
  have hWO : W.subgroupOf C ≤ CFSG.pCore p C := le_sSup ⟨hWn, hWp.comap_subtype⟩
  have hW1' : W.subgroupOf C ≠ ⊥ := by
    intro hbot
    apply hW1
    rw [← Subgroup.map_subgroupOf_eq_of_le hWC, hbot, Subgroup.map_bot]
  have hDp : IsPGroup p (C ⊓ Subgroup.centralizer (W : Set Y) : Subgroup Y) := by
    refine isPGroup_of_forall_coprime_eq_one hp _ fun y hy hcop => ?_
    have hyW : (⟨y, hy.1⟩ : C) ∈
        Subgroup.centralizer ((W.subgroupOf C : Subgroup C) : Set C) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hy.2 w hw)
    have hcop' : (orderOf (⟨y, hy.1⟩ : C)).Coprime p := by
      rwa [Subgroup.orderOf_mk]
    have hyO := mem_centralizer_of_isCyclic_of_coprime hp hOc hOp hWO hW1' hyW hcop'
    exact congrArg Subtype.val (eq_one_of_mem_of_coprime hOp (hB hyO) hcop')
  have hDn : ((C ⊓ Subgroup.centralizer (W : Set Y) : Subgroup Y).subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    refine le_trans (le_inf Subgroup.le_normalizer (hCW.trans ?_))
      Subgroup.inf_normalizer_le_normalizer_inf
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have hDO : (C ⊓ Subgroup.centralizer (W : Set Y) : Subgroup Y).subgroupOf C ≤
      CFSG.pCore p C := le_sSup ⟨hDn, hDp.comap_subtype⟩
  calc C ⊓ Subgroup.centralizer (W : Set Y)
      = ((C ⊓ Subgroup.centralizer (W : Set Y) : Subgroup Y).subgroupOf C).map C.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le inf_le_left).symm
    _ ≤ (CFSG.pCore p C).map C.subtype := Subgroup.map_mono hDO
    _ ≤ Rb := (hOp.map C.subtype).le_sylow_of_normal Rb

theorem ReducedNongeneration.inf_centralizer_le_of_rankOne (h : ReducedNongeneration p Y Rb Y₀)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) (_hZ : Subgroup.center K = ⊥)
    (hnc : ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y))
    (hz : ∃ z ∈ (Rb : Subgroup Y), z ∉ K ∧ orderOf z = p ∧
      z ∈ Subgroup.centralizer (K : Set Y))
    {W : Subgroup Y} (hWC : W ≤ Subgroup.centralizer (K : Set Y)) (hW1 : W ≠ ⊥)
    (hWp : IsPGroup p W)
    (hCW : Subgroup.centralizer (K : Set Y) ≤ Subgroup.normalizer (W : Set Y)) :
    Subgroup.centralizer (K : Set Y) ⊓ Subgroup.centralizer (W : Set Y) ≤ Rb := by
  have hKn : K.Normal := h.normal_of_rankOne hK hnc
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hz
  have hKY₀ := (h.rankOne_principle hK hnc hzR hzK hzp hzc).2
  exact h.inf_centralizer_le_of_isCyclic
    (fun A hAC hA => h.isCyclic_of_le_centralizer hK hKY₀ hA hAC) hWC hW1 hWp hCW

end Reduced

end CFSG.AGLEmbedding
