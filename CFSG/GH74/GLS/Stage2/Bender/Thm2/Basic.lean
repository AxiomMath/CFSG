module

import CFSG.Adapters.WholeGroupLayer
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Growth

variable {G : Type} [Group G] [Finite G]

theorem lt_inf_normalizer_of_lt {p : ℕ} (hp : p.Prime) {Y W : Subgroup G} (hW : IsPGroup p ↥W) (hYW : Y < W) :
    Y < W ⊓ normalizer (Y : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsNilpotent ↥W := hW.isNilpotent
  have hle : Y ≤ W := hYW.le
  have hlt : Y.subgroupOf W < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact absurd hYW (not_lt_of_ge h)
  have h2 := Group.normalizerCondition_of_isNilpotent (G := ↥W) (Y.subgroupOf W) hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hle] at h2
  obtain ⟨x, hx1, hx2⟩ := (IsConcreteLE.lt_iff_le_and_exists.mp h2).2
  refine lt_of_le_of_ne (le_inf hle Subgroup.le_normalizer) ?_
  intro heq
  apply hx2
  have hxm : (x : G) ∈ W ⊓ normalizer (Y : Set G) := ⟨x.2, hx1⟩
  rw [← heq] at hxm
  exact hxm

theorem eq_of_inf_normalizer_le {p : ℕ} (hp : p.Prime) {Y W : Subgroup G} (hW : IsPGroup p ↥W) (hYW : Y ≤ W)
    (h : W ⊓ normalizer (Y : Set G) ≤ Y) : Y = W := by
  by_contra hne
  have hlt := lt_inf_normalizer_of_lt hp hW (lt_of_le_of_ne hYW hne)
  exact absurd h (not_le_of_gt hlt)

end Growth

section Fstar

variable {G : Type} [Group G]

theorem not_quasisimple_of_pgroup {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hK : CFSG.IsQuasisimple K) (hpg : IsPGroup p K) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hnil : Group.IsNilpotent K := hpg.isNilpotent
  obtain ⟨hperf, hsimple, -⟩ := hK
  have : Group.IsPerfect K := hperf
  have : Nontrivial (K ⧸ center K) := hsimple.toNontrivial
  have : Nontrivial K := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center K))
  exact Group.IsPerfect.not_isNilpotent (G := K) hnil

theorem Fs_eq_map (D : Subgroup G) : Fs D = (generalizedFitting ↥D).map D.subtype := rfl

theorem Op_eq_map (p : ℕ) (D : Subgroup G) : Op p D = (pCore p ↥D).map D.subtype := rfl

theorem Em_def' (D : Subgroup G) : Em D = (layer ↥D).map D.subtype := rfl

theorem Fs_eq_Op_iff (D : Subgroup G) (p : ℕ) : Fs D = Op p D ↔ generalizedFitting ↥D = pCore p ↥D :=
  ⟨fun h => Subgroup.map_injective D.subtype_injective h, fun h => by rw [Fs_eq_map, Op_eq_map, h]⟩

theorem centralizer_generalizedFitting_le_fitting'' (A : Type) [Group A] [Finite A] :
    centralizer ((generalizedFitting A : Subgroup A) : Set A) ≤ fittingSubgroup A :=
  CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup A

end Fstar

section Orders

variable {G : Type} [Group G]

theorem eq_one_of_coprime_pow {p : ℕ} (hp : p.Prime) {x : G} {k : ℕ} (hk : orderOf x = p ^ k)
    (hc : Nat.Coprime p (orderOf x)) : x = 1 := by
  rw [hk] at hc
  have hk0 : k = 0 := by
    by_contra hk0
    exact hp.ne_one (hc.eq_one_of_dvd (dvd_pow_self p hk0))
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.mp hk

theorem coprime_orderOf_of_mem_pPrimeCoreOf [Finite G] {p : ℕ} (hp : p.Prime) {N : Subgroup G} {x : G}
    (hx : x ∈ pPrimeCoreOf p N) : Nat.Coprime p (orderOf x) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 : orderOf y ∣ Nat.card (pPrimeCore p ↥N) := by
    have := orderOf_dvd_natCard (⟨y, hy⟩ : pPrimeCore p ↥N)
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf ((y : ↥N) : G) = orderOf y := Subgroup.orderOf_coe y
  show Nat.Coprime p (orderOf ((y : ↥N) : G))
  rw [h2]
  exact Nat.Coprime.coprime_dvd_right h1 (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥N))

theorem exists_orderOf_pow_of_mem_Op {p : ℕ} (hp : p.Prime) {D : Subgroup G} {x : G} (hx : x ∈ Op p D) :
    ∃ k : ℕ, orderOf x = p ^ k := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hpg : IsPGroup p (pCore p ↥D) := CFSG.pCore_isPGroup
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hpg) ⟨y, hy⟩
  refine ⟨k, ?_⟩
  show orderOf ((y : ↥D) : G) = p ^ k
  rw [Subgroup.orderOf_coe, ← Subgroup.orderOf_mk y hy]
  exact hk

theorem conj_mem_pPrimeCoreOf {p : ℕ} {N : Subgroup G} {n x : G} (hn : n ∈ N) (hx : x ∈ pPrimeCoreOf p N) :
    n * x * n⁻¹ ∈ pPrimeCoreOf p N := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨n, hn⟩ * y * ⟨n, hn⟩⁻¹, (CFSG.pPrimeCore_normal (p := p) (G := ↥N)).conj_mem y hy _, rfl⟩

theorem conj_mem_Op {p : ℕ} {D : Subgroup G} {n x : G} (hn : n ∈ D) (hx : x ∈ Op p D) :
    n * x * n⁻¹ ∈ Op p D := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨n, hn⟩ * y * ⟨n, hn⟩⁻¹, (CFSG.pCore_normal (p := p) (G := ↥D)).conj_mem y hy _, rfl⟩

theorem Op_le' (p : ℕ) (N : Subgroup G) : Op p N ≤ N := Subgroup.map_subtype_le _

theorem le_normalizer_Op' (p : ℕ) (N : Subgroup G) : N ≤ normalizer ((Op p N : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact conj_mem_Op hn
  · intro hx
    have := conj_mem_Op (inv_mem hn) hx
    simpa [mul_assoc] using this

theorem op_isPGroup {p : ℕ} (N : Subgroup G) : IsPGroup p ↥(Op p N) :=
  (CFSG.pCore_isPGroup (G := ↥N) (p := p)).map N.subtype

end Orders

section Fstar2

variable {G : Type} [Group G] [Finite G]

theorem layer_eq_bot_of_pgroup {A : Type} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    (h : generalizedFitting A = pCore p A) : layer A = ⊥ := by
  have hempty : {K : Subgroup A | IsComponent K} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun K hK => ?_
    have hKF : K ≤ generalizedFitting A := le_sup_right.trans' (le_sSup hK)
    rw [h] at hKF
    have hKp : IsPGroup p ↥K := (CFSG.pCore_isPGroup (G := A) (p := p)).to_le hKF
    exact not_quasisimple_of_pgroup hp hK.1 hKp
  simp only [CFSG.layer.eq_sSup]
  rw [hempty, sSup_empty]

theorem Em_eq_bot_of_Fs_eq {p : ℕ} (hp : p.Prime) {D : Subgroup G} (h : Fs D = Op p D) : Em D = ⊥ := by
  have h1 := layer_eq_bot_of_pgroup hp ((Fs_eq_Op_iff D p).mp h)
  rw [Em_def', h1, Subgroup.map_bot]

theorem pPrimeCoreOf_inf_eq_bot {p : ℕ} (hp : p.Prime) {D N : Subgroup G} (hDN : D ≤ N)
    (hD : Fs D = Op p D) : pPrimeCoreOf p N ⊓ D = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hD' : generalizedFitting ↥D = pCore p ↥D := (Fs_eq_Op_iff D p).mp hD
  rw [eq_bot_iff]
  rintro z ⟨hzO, hzD⟩
  rw [Subgroup.mem_bot]
  have hcop := coprime_orderOf_of_mem_pPrimeCoreOf hp hzO
  have hcen : (⟨z, hzD⟩ : ↥D) ∈ centralizer ((generalizedFitting ↥D : Subgroup ↥D) : Set ↥D) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    rw [hD'] at hf
    have hfOp : (f : G) ∈ Op p D := ⟨f, hf, rfl⟩
    have hc1 : (f : G) * z * (f : G)⁻¹ * z⁻¹ ∈ pPrimeCoreOf p N :=
      mul_mem (conj_mem_pPrimeCoreOf (hDN f.2) hzO) (inv_mem hzO)
    have hc2 : (f : G) * z * (f : G)⁻¹ * z⁻¹ ∈ Op p D := by
      have : (f : G) * z * (f : G)⁻¹ * z⁻¹ = (f : G) * (z * (f : G)⁻¹ * z⁻¹) := by group
      rw [this]
      exact mul_mem hfOp (conj_mem_Op hzD (inv_mem hfOp))
    obtain ⟨k, hk⟩ := exists_orderOf_pow_of_mem_Op hp hc2
    have h1 := eq_one_of_coprime_pow hp hk (coprime_orderOf_of_mem_pPrimeCoreOf hp hc1)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have h2 : (f : G) * z = z * (f : G) := by
      have : (f : G) * z * (f : G)⁻¹ * z⁻¹ = 1 := h1
      calc (f : G) * z = ((f : G) * z * (f : G)⁻¹ * z⁻¹) * (z * (f : G)) := by group
        _ = z * (f : G) := by rw [this, one_mul]
    exact h2
  have hF : (⟨z, hzD⟩ : ↥D) ∈ fittingSubgroup ↥D := centralizer_generalizedFitting_le_fitting'' ↥D hcen
  have hFs : (⟨z, hzD⟩ : ↥D) ∈ pCore p ↥D := by
    rw [← hD']
    have hle : fittingSubgroup ↥D ≤ generalizedFitting ↥D := le_sup_left
    exact hle hF
  have hzOp : z ∈ Op p D := ⟨⟨z, hzD⟩, hFs, rfl⟩
  obtain ⟨k, hk⟩ := exists_orderOf_pow_of_mem_Op hp hzOp
  exact eq_one_of_coprime_pow hp hk hcop

end Fstar2

end CFSG.GH74.GLS.Stage2.Bender.Thm2
