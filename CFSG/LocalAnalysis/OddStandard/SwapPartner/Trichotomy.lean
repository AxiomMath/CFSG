module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TrichotomyDefs
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TrichotomySetup
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient
import CFSG.LocalAnalysis.OddStandard.SwapPartner.WPrimeShapeTable
import CFSG.GroupTheory.LocalCores.Components
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

private theorem wt_perfect_le_abar {X : Type*} [Group X] {t : X} {Sg V : Subgroup X}
    (h : SwapShape t Sg V) {P : Subgroup X} (hP : Group.IsPerfect P)
    (hPC : P ≤ centralizer ({t} : Set X)) : P ≤ (⁅Sg, Sg⁆ : Subgroup X) := by
  calc P = ⁅P, P⁆ := (Subgroup.isPerfect_iff.mp hP).symm
    _ ≤ ⁅centralizer ({t} : Set X), centralizer ({t} : Set X)⁆ :=
        Subgroup.commutator_mono hPC hPC
    _ = ⁅Sg, Sg⁆ := h.commutator_centralizer_eq

private theorem wt_no_component_centralizing_in_C {X : Type*} [Group X] {t : X}
    {Sg V : Subgroup X} (h : SwapShape t Sg V) {J : Subgroup X} (hJ : CFSG.IsComponent J)
    (hAJ : ⁅(⁅Sg, Sg⁆ : Subgroup X), J⁆ = ⊥)
    (hJC : J ≤ centralizer ({t} : Set X)) : False := by
  have hJA : J ≤ (⁅Sg, Sg⁆ : Subgroup X) := wt_perfect_le_abar h hJ.1.1 hJC
  have hJcent : J ≤ Subgroup.centralizer ((⁅Sg, Sg⁆ : Subgroup X) : Set X) := by
    have hAJ' : ⁅J, (⁅Sg, Sg⁆ : Subgroup X)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact hAJ
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAJ'
  have hsub : J.subgroupOf (⁅Sg, Sg⁆ : Subgroup X) ≤
      center ↥(⁅Sg, Sg⁆ : Subgroup X) := by
    intro j hj
    rw [Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hJcent hj) (a : X) a.2
  rw [h.center_abar_eq_bot] at hsub
  have hbot : J.subgroupOf (⁅Sg, Sg⁆ : Subgroup X) = ⊥ := le_bot_iff.mp hsub
  rw [Subgroup.subgroupOf_eq_bot] at hbot
  have hJbot : J = ⊥ := by
    have h1 : J ⊓ (⁅Sg, Sg⁆ : Subgroup X) = ⊥ := disjoint_iff.mp hbot
    rwa [inf_eq_left.mpr hJA] at h1
  exact (Subgroup.nontrivial_iff_ne_bot J).mp
    (CFSG.LocalCores.isQuasisimple_nontrivial hJ.1) hJbot

private theorem wt_stray_comm {X : Type*} [Group X] [Finite X] {t : X} {Sg V L M : Subgroup X}
    (h : SwapShape t Sg V) (hL : CFSG.IsComponent L) (hM : CFSG.IsComponent M)
    (hAL : ⁅(⁅Sg, Sg⁆ : Subgroup X), L⁆ = ⊥)
    (hAM : ⁅(⁅Sg, Sg⁆ : Subgroup X), M⁆ ≠ ⊥) (htL : t ∈ L) :
    M ≤ centralizer ({t} : Set X) := by
  have hLM : L ≠ M := by
    intro hEq
    exact hAM (hEq ▸ hAL)
  have hcomm : ⁅M, L⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hM hL with hEq | hc
    · exact absurd hEq.symm hLM
    · exact hc
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
  intro m hm
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (hcomm hm) t htL).symm

private theorem wt_card_map_conj_inf_centralizer_ge {X : Type*} [Group X] [Finite X] {t y : X}
    {Sg V : Subgroup X} (h : SwapShape t Sg V)
    (htA' : t ∈ (⁅Sg, Sg⁆ : Subgroup X).map (MulAut.conj y).toMonoidHom) :
    48 ≤ Nat.card ↥((⁅Sg, Sg⁆ : Subgroup X).map (MulAut.conj y).toMonoidHom ⊓
      centralizer ({t} : Set X)) := by
  let A : Subgroup X := ⁅Sg, Sg⁆
  let A' : Subgroup X := A.map (MulAut.conj y).toMonoidHom
  have htA'' : t ∈ A' := htA'
  let eA' : ↥A ≃* ↥A' :=
    Subgroup.equivMapOfInjective A (MulAut.conj y).toMonoidHom (MulAut.conj y).injective
  let eA : ↥A ≃* alternatingGroup (Fin 8) := Classical.choice h.nonempty_equiv_abar
  let e : ↥A' ≃* alternatingGroup (Fin 8) := eA'.symm.trans eA
  let τ0 : ↥A' := ⟨t, htA''⟩
  let τ : alternatingGroup (Fin 8) := e τ0
  let σ : Equiv.Perm (Fin 8) := (τ : Equiv.Perm (Fin 8))
  have hτ0 : τ0 * τ0 = 1 := by
    apply Subtype.ext
    show t * t = 1
    rw [← pow_two]
    exact h.sq_eq_one
  have hτ : τ * τ = 1 := by
    show e τ0 * e τ0 = 1
    rw [← map_mul, hτ0, map_one]
  have hσ : σ * σ = 1 := by
    show (τ : Equiv.Perm (Fin 8)) * (τ : Equiv.Perm (Fin 8)) = 1
    simpa using congrArg Subtype.val hτ
  let g : ↥(alternatingGroup (Fin 8) ⊓
      centralizer ({σ} : Set (Equiv.Perm (Fin 8)))) → ↥A' :=
    fun w => e.symm ⟨w.1, w.2.1⟩
  have hg_comm : ∀ w, g w * τ0 = τ0 * g w := by
    intro w
    apply e.injective
    show e (g w * τ0) = e (τ0 * g w)
    rw [map_mul, map_mul]
    simp only [g, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp w.2.2
  have hmem : ∀ w, (g w : X) ∈ (A' ⊓ centralizer ({t} : Set X) : Subgroup X) := by
    intro w
    refine ⟨(g w).2, ?_⟩
    show (g w : X) ∈ Subgroup.centralizer ({t} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext_iff.mp (hg_comm w)
  let f : ↥(alternatingGroup (Fin 8) ⊓
      centralizer ({σ} : Set (Equiv.Perm (Fin 8)))) →
      ↥(A' ⊓ centralizer ({t} : Set X)) := fun w => ⟨(g w : X), hmem w⟩
  have hf_inj : Function.Injective f := by
    intro w w' hww'
    have h1 : (g w : X) = (g w' : X) :=
      congrArg (fun z : ↥(A' ⊓ centralizer ({t} : Set X)) => (z : X)) hww'
    have hg : g w = g w' := Subtype.ext h1
    have h2 : (⟨w.1, w.2.1⟩ : ↥(alternatingGroup (Fin 8))) = ⟨w'.1, w'.2.1⟩ :=
      e.symm.injective hg
    have h2' : (w.1 : Equiv.Perm (Fin 8)) = w'.1 :=
      congrArg (fun z : ↥(alternatingGroup (Fin 8)) => (z : Equiv.Perm (Fin 8))) h2
    exact Subtype.ext h2'
  calc 48 ≤ altCentCard8 σ := forty_eight_le_altCentCard8 hσ
    _ = Nat.card ↥(alternatingGroup (Fin 8) ⊓
          centralizer ({σ} : Set (Equiv.Perm (Fin 8)))) := rfl
    _ ≤ Nat.card ↥(A' ⊓ centralizer ({t} : Set X)) := Nat.card_le_card_of_injective f hf_inj
    _ = Nat.card ↥(A' ⊓ centralizer ({t} : Set X)) := rfl

private theorem wt_abar_normal_of_eq_component {X : Type*} [Group X] [Finite X] {t : X}
    {Sg V K : Subgroup X} (h : SwapShape t Sg V)
    (hStray : ∀ J : Subgroup X, CFSG.IsComponent J →
      ⁅(⁅Sg, Sg⁆ : Subgroup X), J⁆ = ⊥ → t ∈ J)
    (hK : CFSG.IsComponent K)
    (hiff : ∀ L : Subgroup X, CFSG.IsComponent L →
      (⁅(⁅Sg, Sg⁆ : Subgroup X), L⁆ ≠ ⊥ ↔
        L = K ∨ L = K.map (MulAut.conj t).toMonoidHom))
    (hKt_eq : K.map (MulAut.conj t).toMonoidHom = K)
    (hAK_eq : (⁅Sg, Sg⁆ : Subgroup X) = K) :
    (⁅Sg, Sg⁆ : Subgroup X).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro y
  have hAcomp : CFSG.IsComponent (⁅Sg, Sg⁆ : Subgroup X) := by
    rw [hAK_eq]; exact hK
  have hA'comp : CFSG.IsComponent ((⁅Sg, Sg⁆ : Subgroup X).map
      (MulAut.conj y).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj y) hAcomp
  by_contra hne
  have hAA' : ⁅(⁅Sg, Sg⁆ : Subgroup X), (⁅Sg, Sg⁆ : Subgroup X).map
      (MulAut.conj y).toMonoidHom⁆ = ⊥ := by
    by_contra hne'
    rcases (hiff _ hA'comp).mp hne' with h | h
    · exact hne (h.trans hAK_eq.symm)
    · exact hne (h.trans (hKt_eq.trans hAK_eq.symm))
  have hA'cent : (⁅Sg, Sg⁆ : Subgroup X).map (MulAut.conj y).toMonoidHom ≤
      Subgroup.centralizer ((⁅Sg, Sg⁆ : Subgroup X) : Set X) := by
    have hAA'' : ⁅(⁅Sg, Sg⁆ : Subgroup X).map (MulAut.conj y).toMonoidHom,
        (⁅Sg, Sg⁆ : Subgroup X)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact hAA'
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAA''
  have htA' : t ∈ (⁅Sg, Sg⁆ : Subgroup X).map (MulAut.conj y).toMonoidHom :=
    hStray _ hA'comp hAA'
  let Z : Subgroup X := (⁅Sg, Sg⁆ : Subgroup X).map (MulAut.conj y).toMonoidHom ⊓
    centralizer ({t} : Set X)
  have hZleV : Z ≤ V := by
    calc Z ≤ Subgroup.centralizer ((⁅Sg, Sg⁆ : Subgroup X) : Set X) ⊓
          centralizer ({t} : Set X) := inf_le_inf hA'cent le_rfl
      _ = V := h.centralizer_abar_inf_centralizer
  have hcardZ_le : Nat.card Z ≤ 4 := by
    calc Nat.card Z ≤ Nat.card V := Subgroup.card_le_of_le hZleV
      _ = 4 := h.card_v
  have hcardZ_ge : 48 ≤ Nat.card Z :=
    wt_card_map_conj_inf_centralizer_ge h htA'
  have hcon : 48 ≤ 4 := le_trans hcardZ_ge hcardZ_le
  exact absurd hcon (by norm_num)

theorem trichotomy {X : Type} [Group X] [Finite X] (hO : CFSG.oddCore X = ⊥) {t : X}
    {Sg V : Subgroup X} (h : SwapShape t Sg V)
    (hStray : ∀ J : Subgroup X, CFSG.IsComponent J → ⁅(⁅Sg, Sg⁆ : Subgroup X), J⁆ = ⊥ → t ∈ J) :
    (CFSG.IsComponent (⁅Sg, Sg⁆ : Subgroup X) ∧ (⁅Sg, Sg⁆ : Subgroup X).Normal ∧
      ∀ J : Subgroup X, CFSG.IsComponent J → J ≠ ⁅Sg, Sg⁆ →
        t ∈ J ∧ ⁅(⁅Sg, Sg⁆ : Subgroup X), J⁆ = ⊥ ∧
          ∀ J' : Subgroup X, CFSG.IsComponent J' → J' ≠ ⁅Sg, Sg⁆ → J' = J) ∨
    (∃ K : Subgroup X, WreathCase t Sg V K) ∨
    (∃ K : Subgroup X, K = CFSG.layer X ∧ CFSG.IsComponent K ∧ ⁅Sg, Sg⁆ ≤ K ∧ ⁅Sg, Sg⁆ ≠ K ∧
      K.map (MulAut.conj t).toMonoidHom = K) := by
  have hO2 : CFSG.pPrimeCore 2 X = ⊥ := by
    rw [← CFSG.ClassicalInvolution.QuaternionStructure.oddCore_eq_pPrimeCore_two X]
    exact hO
  obtain ⟨hAle_layer, K, hK, hAK, hAleKKt, hAKC, hiff, hKt_eq, hKt_ne⟩ :=
    CFSG.SeitzReduction.exists_isComponent_orbit_of_isComponent_centralizer
      hO2 h.sq_eq_one h.commutator_sg_le_centralizer
        h.isComponent_abar_subgroupOf_centralizer
  by_cases hKeq : K.map (MulAut.conj t).toMonoidHom = K
  · obtain ⟨hAleK, hAKCinf⟩ := hKt_eq hKeq
    by_cases hAKeq : (⁅Sg, Sg⁆ : Subgroup X) = K
    · left
      have hAcomp : CFSG.IsComponent (⁅Sg, Sg⁆ : Subgroup X) := by
        rw [hAKeq]; exact hK
      have hAnormal : (⁅Sg, Sg⁆ : Subgroup X).Normal :=
        wt_abar_normal_of_eq_component h hStray hK hiff hKeq hAKeq
      refine ⟨hAcomp, hAnormal, ?_⟩
      intro J hJ hJne
      have hAJ : ⁅(⁅Sg, Sg⁆ : Subgroup X), J⁆ = ⊥ := by
        by_contra hne
        rcases (hiff J hJ).mp hne with h | h
        · exact hJne (h.trans hAKeq.symm)
        · exact hJne (h.trans (hKeq.trans hAKeq.symm))
      have htJ : t ∈ J := hStray J hJ hAJ
      refine ⟨htJ, hAJ, ?_⟩
      intro J' hJ' hJ'ne
      by_contra hne
      have hAJ' : ⁅(⁅Sg, Sg⁆ : Subgroup X), J'⁆ = ⊥ := by
        by_contra hne'
        rcases (hiff J' hJ').mp hne' with h | h
        · exact hJ'ne (h.trans hAKeq.symm)
        · exact hJ'ne (h.trans (hKeq.trans hAKeq.symm))
      have htJ' : t ∈ J' := hStray J' hJ' hAJ'
      have hJJ' : ⁅J, J'⁆ = ⊥ := by
        rcases CFSG.LocalCores.distinct_components_commute hJ hJ' with hEq | hc
        · exact absurd hEq.symm hne
        · exact hc
      have hJC : J ≤ centralizer ({t} : Set X) := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hJJ'
        intro j hj
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hJJ' hj) t htJ').symm
      exact wt_no_component_centralizing_in_C h hJ hAJ hJC
    · right; right
      have hset : {L : Subgroup X | CFSG.IsComponent L} = {K} := by
        ext L
        rw [Set.mem_singleton_iff]
        constructor
        · intro hL
          by_cases hAL : ⁅(⁅Sg, Sg⁆ : Subgroup X), L⁆ = ⊥
          · exfalso
            have htL : t ∈ L := hStray L hL hAL
            have hLC : K ≤ centralizer ({t} : Set X) :=
              wt_stray_comm h hL hK hAL hAK htL
            have hKA : K ≤ (⁅Sg, Sg⁆ : Subgroup X) :=
              wt_perfect_le_abar h hK.1.1 hLC
            exact hAKeq (le_antisymm hAleK hKA)
          · rcases (hiff L hL).mp hAL with h | h
            · exact h
            · exact h.trans hKeq
        · intro hL
          rw [hL]; exact hK
      have hlayer : CFSG.layer X = K := by
        rw [CFSG.layer.eq_sSup, hset, sSup_singleton]
      exact ⟨K, hlayer.symm, hK, hAleK, hAKeq, hKeq⟩
  · right; left
    obtain ⟨hKKt_comm, hDKcenter, hdiag, hiso⟩ := hKt_ne hKeq
    have heq_or_eq : ∀ L : Subgroup X, CFSG.IsComponent L →
        L = K ∨ L = K.map (MulAut.conj t).toMonoidHom := by
      intro L hL
      by_cases hAL : ⁅(⁅Sg, Sg⁆ : Subgroup X), L⁆ = ⊥
      · exfalso
        have htL : t ∈ L := hStray L hL hAL
        have hKC : K ≤ centralizer ({t} : Set X) :=
          wt_stray_comm h hL hK hAL hAK htL
        have hfix : K.map (MulAut.conj t).toMonoidHom = K := by
          ext x
          rw [Subgroup.mem_map]
          constructor
          · rintro ⟨k, hk, rfl⟩
            change t * k * t⁻¹ ∈ K
            have hcomm : k * t = t * k :=
              Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
            rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
            exact hk
          · intro hx
            refine ⟨x, hx, ?_⟩
            change t * x * t⁻¹ = x
            have hcomm : x * t = t * x :=
              Subgroup.mem_centralizer_singleton_iff.mp (hKC hx)
            rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
        exact hKeq hfix
      · exact (hiff L hL).mp hAL
    have hKt_comp : CFSG.IsComponent (K.map (MulAut.conj t).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hK
    have hset : {L : Subgroup X | CFSG.IsComponent L} =
        {K, K.map (MulAut.conj t).toMonoidHom} := by
      ext L
      constructor
      · intro hL
        rcases heq_or_eq L hL with h | h <;> simp [h]
      · intro hL
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL
        rcases hL with h | h
        · rw [h]; exact hK
        · rw [h]; exact hKt_comp
    have hlayer : CFSG.layer X = K ⊔ K.map (MulAut.conj t).toMonoidHom := by
      rw [CFSG.layer.eq_sSup, hset, sSup_pair]
    have hisoAlt : Nonempty (↥K ⧸ center ↥K ≃* alternatingGroup (Fin 8)) := by
      obtain ⟨e1⟩ := hiso
      obtain ⟨e2⟩ := h.nonempty_equiv_abar
      have hq : (↥(⁅Sg, Sg⁆ : Subgroup X)) ⧸ center ↥(⁅Sg, Sg⁆ : Subgroup X) ≃*
          ↥(⁅Sg, Sg⁆ : Subgroup X) :=
        (QuotientGroup.quotientMulEquivOfEq h.center_abar_eq_bot).trans
          QuotientGroup.quotientBot
      exact ⟨e1.symm.trans (hq.trans e2)⟩
    exact ⟨K, h, hK, hKeq, hKKt_comm, heq_or_eq, hlayer, hisoAlt, hdiag⟩

end CFSG.OddStandard.AltStdSec.SwapPartner
