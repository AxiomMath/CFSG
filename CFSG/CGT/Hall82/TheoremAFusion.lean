module

public import CFSG.CGT.Hall82.TheoremASetting
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.BookkeepingCocycle
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.CGT.Hall82.TheoremA

open CFSG.RankThree.PartTwo (altHeart)
open CFSG.HardMathSupport.Cooperstein.Coordinator (altAct)
open CFSG.CGT.Timmesfeld75 (WeaklyClosedIn conjSubgroup mem_conjSubgroup)
open CFSG.ABGLocalTools (IsSylowOf)
open Equiv

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {θ : ↥M →* Perm (Fin 6)} {z : G}
  {π : ↥(CFSG.Open.pCoreOf 2 M) →* Multiplicative (altHeart 6)}

structure Steps12 (G : Type) [Group G] [Finite G] (M : Subgroup G) (θ : ↥M →* Perm (Fin 6))
    (π : ↥(CFSG.Open.pCoreOf 2 M) →* Multiplicative (altHeart 6)) : Prop where
  elem : CFSG.Open.IsElemAbelian 2 (CFSG.Open.pCoreOf 2 M)
  fix : ∀ (m : ↥M) (q : ↥(CFSG.Open.pCoreOf 2 M)),
    altAct (θ m) (Multiplicative.toAdd (π q)) = Multiplicative.toAdd (π q) →
      (m : G) * q * (m : G)⁻¹ = q

namespace Setting

theorem toAdd_π_eq_zero_iff (S : Setting G M θ z π) (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    Multiplicative.toAdd (π q) = 0 ↔ (q : G) = 1 ∨ (q : G) = z := by
  rw [← S.π_eq_one_iff]
  exact Iff.rfl

theorem card_zpowers (S : Setting G M θ z π) : Nat.card (Subgroup.zpowers z) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [sq, S.z_sq]) S.z_ne

theorem card_V (S : Setting G M θ z π) (F : Facts) :
    Nat.card (CFSG.Open.pCoreOf 2 M) = 32 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  have h2 : Nat.card (↥(CFSG.Open.pCoreOf 2 M) ⧸ π.ker) = 16 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π S.surj_π).toEquiv]
    exact F.card
  have h3 : Nat.card π.ker = 2 := by
    have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((Subgroup.zpowers_le).mpr S.z_mem)).toEquiv
    rw [S.ker_π]
    exact h.trans S.card_zpowers
  rw [h1, h2, h3]

theorem conj_eq_self_iff (S : Setting G M θ z π) (H : Steps12 G M θ π) (m : ↥M)
    (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    (m : G) * q * (m : G)⁻¹ = q ↔
      altAct (θ m) (Multiplicative.toAdd (π q)) = Multiplicative.toAdd (π q) := by
  constructor
  · intro h
    exact (S.equiv m q q h.symm).symm
  · exact H.fix m q

theorem commute_iff (S : Setting G M θ z π) (H : Steps12 G M θ π) (m : ↥M)
    (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    (m : G) * q = q * m ↔
      altAct (θ m) (Multiplicative.toAdd (π q)) = Multiplicative.toAdd (π q) := by
  rw [← S.conj_eq_self_iff H]
  constructor
  · intro h
    rw [h, mul_inv_cancel_right]
  · intro h
    calc (m : G) * q = (m : G) * q * (m : G)⁻¹ * m := by group
      _ = q * m := by rw [h]

theorem centralizer_V_le (S : Setting G M θ z π) (F : Facts) :
    Subgroup.centralizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) ≤
      CFSG.Open.pCoreOf 2 M := by
  intro x hx
  have hxM : x ∈ M := by
    rw [← S.centralizer_eq, Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hx) z S.z_mem).symm
  have h1 : θ ⟨x, hxM⟩ = 1 := by
    refine F.faithful _ fun v => ?_
    obtain ⟨q, hq⟩ := S.surj_π (Multiplicative.ofAdd v)
    have hc : (x : G) * q * x⁻¹ = q := by
      rw [← (Subgroup.mem_centralizer_iff.mp hx) q q.2, mul_inv_cancel_right]
    have h2 := S.equiv ⟨x, hxM⟩ q q hc.symm
    rw [hq] at h2
    exact h2.symm
  exact (S.θ_eq_one_iff _).mp h1

theorem centralizer_subgroupOf_eq (S : Setting G M θ z π) (H : Steps12 G M θ π)
    (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    (Subgroup.centralizer {(q : G)}).subgroupOf M =
      (stabSub (Multiplicative.toAdd (π q))).comap θ := by
  ext m
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, mem_stabSub,
    Subgroup.mem_centralizer_singleton_iff, ← S.commute_iff H]

theorem index_centralizer (S : Setting G M θ z π) (F : Facts) (H : Steps12 G M θ π)
    (q : ↥(CFSG.Open.pCoreOf 2 M)) (hq : Multiplicative.toAdd (π q) ≠ 0) :
    ((Subgroup.centralizer {(q : G)}).subgroupOf M).index = 15 := by
  rw [S.centralizer_subgroupOf_eq H, Subgroup.index_comap_of_surjective _ S.surj_θ]
  exact F.index_stabSub _ hq

theorem exists_isSylowOf_le_centralizer (S : Setting G M θ z π) (F : Facts)
    (H : Steps12 G M θ π) (q : ↥(CFSG.Open.pCoreOf 2 M))
    (hq : Multiplicative.toAdd (π q) ≠ 0) :
    ∃ P : Subgroup G, IsSylowOf 2 P M ∧ P ≤ Subgroup.centralizer {(q : G)} := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (M ⊓ Subgroup.centralizer {(q : G)})
  refine ⟨P, ?_, hP.le.trans inf_le_right⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hP ⊢
  obtain ⟨hle, hp, hdvd⟩ := hP
  refine ⟨hle.trans inf_le_left, hp, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P (M ⊓ Subgroup.centralizer {(q : G)}) M hle
    inf_le_left]
  have h15 : (M ⊓ Subgroup.centralizer {(q : G)}).relIndex M = 15 := by
    rw [Subgroup.inf_relIndex_left]
    exact S.index_centralizer F H q hq
  rw [h15]
  intro h2
  exact hdvd ((Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) h2))

theorem card_inf_centralizer (S : Setting G M θ z π) (F : Facts) (H : Steps12 G M θ π)
    (m : ↥M) :
    Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer {(m : G)}) =
      2 * Nat.card (fixSub (θ m)) := by
  set A : Subgroup (Multiplicative (altHeart 6)) := AddSubgroup.toSubgroup (fixSub (θ m))
  have hB : (CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer {(m : G)}).subgroupOf
      (CFSG.Open.pCoreOf 2 M) = A.comap π := by
    ext q
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    show _ ↔ Multiplicative.toAdd (π q) ∈ fixSub (θ m)
    rw [mem_fixSub, ← S.commute_iff H]
    exact ⟨fun h => h.2.symm, fun h => ⟨q.2, h.symm⟩⟩
  have h1 : Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer {(m : G)}) =
      Nat.card (A.comap π) := by
    rw [← hB]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  have h2 := Subgroup.card_mul_index (A.comap π)
  rw [Subgroup.index_comap_of_surjective _ S.surj_π, S.card_V F] at h2
  have h3 := Subgroup.card_mul_index A
  have hcardU : Nat.card (Multiplicative (altHeart 6)) = 16 := F.card
  rw [hcardU] at h3
  have hA : Nat.card A = Nat.card (fixSub (θ m)) := rfl
  rw [h1, ← hA]
  have hi : A.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : Nat.card (A.comap π) * A.index = (2 * Nat.card A) * A.index := by
    rw [h2, mul_assoc, h3]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) this

theorem V_comm (H : Steps12 G M θ π) {a b : G} (ha : a ∈ CFSG.Open.pCoreOf 2 M)
    (hb : b ∈ CFSG.Open.pCoreOf 2 M) : a * b = b * a := by
  have h := H.elem.1.is_comm.comm (⟨a, ha⟩ : ↥(CFSG.Open.pCoreOf 2 M)) ⟨b, hb⟩
  exact congrArg Subtype.val h

theorem V_sq (H : Steps12 G M θ π) {a : G} (ha : a ∈ CFSG.Open.pCoreOf 2 M) : a * a = 1 := by
  rw [← sq]
  exact H.elem.2 a ha

theorem mem_centralizer_conj_iff (S : Setting G M θ z π) (g x : G) :
    x ∈ Subgroup.centralizer {g * z * g⁻¹} ↔ g⁻¹ * x * g ∈ M := by
  rw [← S.centralizer_eq, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [h]
      _ = z * (g⁻¹ * x * g) := by group
  · intro h
    calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = g * z * g⁻¹ * x := by group

theorem conj_mem_conjSubgroup (S : Setting G M θ z π) {g x w : G} (hx : g⁻¹ * x * g ∈ M)
    (hw : w ∈ conjSubgroup g (CFSG.Open.pCoreOf 2 M)) :
    x * w * x⁻¹ ∈ conjSubgroup g (CFSG.Open.pCoreOf 2 M) := by
  rw [mem_conjSubgroup] at hw ⊢
  have h := S.conj_mem hx hw
  have e : g⁻¹ * (x * w * x⁻¹) * g =
      (g⁻¹ * x * g) * (g⁻¹ * w * g) * (g⁻¹ * x * g)⁻¹ := by group
  rw [e]
  exact h

theorem conj_comm (H : Steps12 G M θ π) {g a b : G}
    (ha : a ∈ conjSubgroup g (CFSG.Open.pCoreOf 2 M))
    (hb : b ∈ conjSubgroup g (CFSG.Open.pCoreOf 2 M)) : a * b = b * a := by
  rw [mem_conjSubgroup] at ha hb
  have h := V_comm H ha hb
  calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
    _ = b * a := by group

theorem conj_sq (H : Steps12 G M θ π) {g a : G}
    (ha : a ∈ conjSubgroup g (CFSG.Open.pCoreOf 2 M)) : a * a = 1 := by
  rw [mem_conjSubgroup] at ha
  have h := V_sq H ha
  calc a * a = g * ((g⁻¹ * a * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem card_conjSubgroup (g : G) (T : Subgroup G) : Nat.card (conjSubgroup g T) = Nat.card T :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

section Hall14

variable (S : Setting G M θ z π) (F : Facts) (H : Steps12 G M θ π)
  {c : ↥(CFSG.Open.pCoreOf 2 M)} {i j : Fin 6} (hij : i ≠ j)
  (hc : Multiplicative.toAdd (π c) = pc i j) {g : G} (hg : (c : G) = g * z * g⁻¹)
include S F H hij hc hg

theorem conj_le_M : conjSubgroup g (CFSG.Open.pCoreOf 2 M) ≤ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc0 : Multiplicative.toAdd (π c) ≠ 0 := by rw [hc]; exact F.pc_ne_zero i j hij
  obtain ⟨P, hP, hPC⟩ := S.exists_isSylowOf_le_centralizer F H c hc0
  rw [hg] at hPC
  have hP'M : conjSubgroup g⁻¹ P ≤ M := by
    intro x hx
    rw [mem_conjSubgroup, inv_inv] at hx
    have h := (S.mem_centralizer_conj_iff g (g * x * g⁻¹)).mp (hPC hx)
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e] at h
  have hP' : IsSylowOf 2 (conjSubgroup g⁻¹ P) M := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hP'M ?_
    rw [card_conjSubgroup]
    exact hP.card_eq
  have hVP' : CFSG.Open.pCoreOf 2 M ≤ conjSubgroup g⁻¹ P :=
    CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_le_of_le_normalizer hP' S.isPGroup
      S.V_le S.le_normalizer
  intro w hw
  rw [mem_conjSubgroup] at hw
  have h := hVP' hw
  rw [mem_conjSubgroup, inv_inv] at h
  have e : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
  rw [e] at h
  exact hP.le h

theorem conj_le_centralizer :
    conjSubgroup g (CFSG.Open.pCoreOf 2 M) ≤ Subgroup.centralizer {(c : G)} := by
  intro w hw
  rw [hg, S.mem_centralizer_conj_iff]
  rw [mem_conjSubgroup] at hw
  exact S.V_le hw

theorem θ_conj_eq (w : G) (hw : w ∈ conjSubgroup g (CFSG.Open.pCoreOf 2 M)) (hwM : w ∈ M) :
    θ ⟨w, hwM⟩ = 1 ∨ θ ⟨w, hwM⟩ = swap i j := by
  have hWM := conj_le_M S F H hij hc hg
  have hWC := conj_le_centralizer S F H hij hc hg
  set W := conjSubgroup g (CFSG.Open.pCoreOf 2 M) with hWdef
  set E : Subgroup (Perm (Fin 6)) := (W.subgroupOf M).map θ with hEdef
  have hfixW : ∀ (x : ↥M), (x : G) ∈ W →
      altAct (θ x) (Multiplicative.toAdd (π c)) = Multiplicative.toAdd (π c) := by
    intro x hx
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hWC hx)
    exact (S.commute_iff H x c).mp h
  have hpres : ∀ e ∈ E, Pres e i j := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hfixW x hx
    rw [hc] at h
    exact (F.fixed_pc_iff _ i j hij).mp h
  have hnorm : ∀ h : Perm (Fin 6), Pres h i j → ∀ e ∈ E, h * e * h⁻¹ ∈ E := by
    rintro h hh _ ⟨x, hx, rfl⟩
    obtain ⟨m, rfl⟩ := S.surj_θ h
    have hm : altAct (θ m) (Multiplicative.toAdd (π c)) = Multiplicative.toAdd (π c) := by
      rw [hc]
      exact (F.fixed_pc_iff _ i j hij).mpr hh
    have hmc : (m : G) * c = c * m := (S.commute_iff H m c).mpr hm
    have hmC : (m : G) ∈ Subgroup.centralizer {g * z * g⁻¹} := by
      rw [← hg, Subgroup.mem_centralizer_singleton_iff]
      exact hmc
    have hgm := (S.mem_centralizer_conj_iff g m).mp hmC
    refine ⟨m * x * m⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    show m * x * m⁻¹ ∈ W.subgroupOf M
    rw [Subgroup.mem_subgroupOf]
    have h' := S.conj_mem_conjSubgroup hgm (Subgroup.mem_subgroupOf.mp hx)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h'
  have hsq : ∀ e ∈ E, e * e = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul]
    have h := conj_sq H (Subgroup.mem_subgroupOf.mp hx)
    have h1 : x * x = 1 := Subtype.ext (by simpa using h)
    rw [h1, map_one]
  have hquad : ∀ e ∈ E, ∀ e' ∈ E, ∀ v : altHeart 6,
      altAct e' (altAct e v + v) + (altAct e v + v) = 0 := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ v
    have hxW : (x : G) ∈ W := Subgroup.mem_subgroupOf.mp hx
    have hyW : (y : G) ∈ W := Subgroup.mem_subgroupOf.mp hy
    obtain ⟨q, hq⟩ := S.surj_π (Multiplicative.ofAdd v)
    have hxq : (x : G) * q * (x : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M := S.conj_mem x.2 q.2
    have hrV : (x : G) * q * (x : G)⁻¹ * (q : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
      Subgroup.mul_mem _ hxq (Subgroup.inv_mem _ q.2)
    have hqC : (q : G) ∈ Subgroup.centralizer {g * z * g⁻¹} := by
      rw [← hg, Subgroup.mem_centralizer_singleton_iff]
      exact V_comm H q.2 c.2
    have hgq := (S.mem_centralizer_conj_iff g q).mp hqC
    have hrW : (x : G) * q * (x : G)⁻¹ * (q : G)⁻¹ ∈ W := by
      have h1 := S.conj_mem_conjSubgroup hgq (Subgroup.inv_mem _ hxW)
      have e : (x : G) * q * (x : G)⁻¹ * (q : G)⁻¹ = x * ((q : G) * (x : G)⁻¹ * (q : G)⁻¹) := by
        group
      rw [e]
      exact Subgroup.mul_mem _ hxW h1
    set r : ↥(CFSG.Open.pCoreOf 2 M) := ⟨_, hrV⟩ with hrdef
    have hπr : Multiplicative.toAdd (π r) = altAct (θ x) v + v := by
      have e : r = ⟨(x : G) * q * (x : G)⁻¹, hxq⟩ * q⁻¹ := Subtype.ext rfl
      rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, S.equiv x q _ rfl, hq]
      show altAct (θ x) v + -v = altAct (θ x) v + v
      rw [neg_eq_of_add_eq_zero_left
        (CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.altHeart_add_self v)]
    have hyr : (y : G) * r = r * y := conj_comm H hyW hrW
    have h := (S.commute_iff H y r).mp hyr
    rw [hπr] at h
    rw [h]
    exact CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.altHeart_add_self _
  have hmemE : θ ⟨w, hwM⟩ ∈ E := ⟨⟨w, hwM⟩, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
  exact F.quad i j hij E hpres hnorm hsq hquad _ hmemE

theorem exists_t : ∃ t ∈ conjSubgroup g (CFSG.Open.pCoreOf 2 M), ∃ htM : t ∈ M,
    θ ⟨t, htM⟩ = swap i j := by
  have hWM := conj_le_M S F H hij hc hg
  by_contra hno
  push Not at hno
  have hWV : conjSubgroup g (CFSG.Open.pCoreOf 2 M) ≤ CFSG.Open.pCoreOf 2 M := by
    intro w hw
    rcases θ_conj_eq S F H hij hc hg w hw (hWM hw) with h | h
    · exact (S.θ_eq_one_iff _).mp h
    · exact absurd h (hno w hw (hWM hw))
  have hWeq : conjSubgroup g (CFSG.Open.pCoreOf 2 M) = CFSG.Open.pCoreOf 2 M :=
    Subgroup.eq_of_le_of_card_ge hWV (by rw [card_conjSubgroup])
  have hgN : g ∈ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hWeq, mem_conjSubgroup]
      simpa [mul_assoc] using hh
    · intro hh
      rw [← hWeq, mem_conjSubgroup] at hh
      simpa [mul_assoc] using hh
  rw [S.normalizer_eq] at hgN
  have hcz : (c : G) = z := by rw [hg, S.conj_z hgN]
  have h0 : Multiplicative.toAdd (π c) = 0 := (S.toAdd_π_eq_zero_iff c).mpr (Or.inr hcz)
  rw [hc] at h0
  exact F.pc_ne_zero i j hij h0

theorem conj_inf_V_eq (t : G) (ht : t ∈ conjSubgroup g (CFSG.Open.pCoreOf 2 M)) (htM : t ∈ M)
    (hθt : θ ⟨t, htM⟩ = swap i j) :
    conjSubgroup g (CFSG.Open.pCoreOf 2 M) ⊓ CFSG.Open.pCoreOf 2 M =
      CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer {t} := by
  have hWM := conj_le_M S F H hij hc hg
  set W := conjSubgroup g (CFSG.Open.pCoreOf 2 M) with hWdef
  have hle : W ⊓ CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer {t} := by
    rintro w ⟨hwW, hwV⟩
    exact ⟨hwV, Subgroup.mem_centralizer_singleton_iff.mpr (conj_comm H hwW ht)⟩
  have hcardC : Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer {t}) = 16 := by
    have h := S.card_inf_centralizer F H ⟨t, htM⟩
    rw [hθt, F.card_fix_swap i j hij] at h
    exact h
  set f : ↥(W.subgroupOf M) →* Perm (Fin 6) := θ.comp (W.subgroupOf M).subtype with hfdef
  have hker := Subgroup.card_ker_mul_card_range f
  have hcardW : Nat.card ↥(W.subgroupOf M) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWM).toEquiv, card_conjSubgroup,
      S.card_V F]
  have hrange : Nat.card f.range ≤ 2 := by
    have hle2 : f.range ≤ Subgroup.zpowers (swap i j) := by
      rintro _ ⟨x, rfl⟩
      rcases θ_conj_eq S F H hij hc hg _ (Subgroup.mem_subgroupOf.mp x.2) (x : ↥M).2 with h | h
      · show θ (x : ↥M) ∈ _
        have e : (⟨((x : ↥M) : G), (x : ↥M).2⟩ : ↥M) = (x : ↥M) := rfl
        rw [e] at h
        rw [h]
        exact Subgroup.one_mem _
      · show θ (x : ↥M) ∈ _
        have e : (⟨((x : ↥M) : G), (x : ↥M).2⟩ : ↥M) = (x : ↥M) := rfl
        rw [e] at h
        rw [h]
        exact Subgroup.mem_zpowers _
    have hswap : orderOf (swap i j) = 2 := by
      refine orderOf_eq_prime (by rw [sq, Equiv.swap_mul_self]) ?_
      intro h
      have h1 := congrArg (fun σ : Perm (Fin 6) => σ i) h
      simp only [Equiv.swap_apply_left, Perm.one_apply] at h1
      exact hij h1.symm
    calc Nat.card f.range ≤ Nat.card (Subgroup.zpowers (swap i j)) :=
          Subgroup.card_le_of_le hle2
      _ = 2 := by rw [Nat.card_zpowers, hswap]
  rw [hcardW] at hker
  have hkerge : 16 ≤ Nat.card f.ker := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card f.ker * Nat.card f.range ≤ 15 * 2 :=
      Nat.mul_le_mul (by omega) hrange
    omega
  have hinj : Nat.card f.ker ≤ Nat.card ↥(W ⊓ CFSG.Open.pCoreOf 2 M) := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨(((x : ↥(W.subgroupOf M)) : ↥M) : G),
        Subgroup.mem_subgroupOf.mp (x : ↥(W.subgroupOf M)).2,
        (S.θ_eq_one_iff _).mp (MonoidHom.mem_ker.mp x.2)⟩) ?_
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hxy
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardC]; omega)

end Hall14

theorem toAdd_π_ne_zero_of_conj (S : Setting G M θ z π) (q : ↥(CFSG.Open.pCoreOf 2 M)) {g : G}
    (hg : (q : G) = g * z * g⁻¹) (hqz : (q : G) ≠ z) : Multiplicative.toAdd (π q) ≠ 0 := by
  intro h
  rcases (S.toAdd_π_eq_zero_iff q).mp h with h1 | h1
  · apply S.z_ne
    rw [hg] at h1
    have e : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [e, h1]
    group
  · exact hqz h1

theorem card_eq_two_mul (S : Setting G M θ z π) (F : Facts) {T : Subgroup G}
    (hTV : T ≤ CFSG.Open.pCoreOf 2 M) (A : AddSubgroup (altHeart 6))
    (hT : ∀ q : ↥(CFSG.Open.pCoreOf 2 M), (q : G) ∈ T ↔ Multiplicative.toAdd (π q) ∈ A) :
    Nat.card T = 2 * Nat.card A := by
  set A' : Subgroup (Multiplicative (altHeart 6)) := AddSubgroup.toSubgroup A
  have hB : T.subgroupOf (CFSG.Open.pCoreOf 2 M) = A'.comap π := by
    ext q
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact hT q
  have h1 : Nat.card T = Nat.card (A'.comap π) := by
    rw [← hB]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTV).toEquiv).symm
  have h2 := Subgroup.card_mul_index (A'.comap π)
  rw [Subgroup.index_comap_of_surjective _ S.surj_π, S.card_V F] at h2
  have h3 := Subgroup.card_mul_index A'
  have hcardU : Nat.card (Multiplicative (altHeart 6)) = 16 := F.card
  rw [hcardU] at h3
  have hA : Nat.card A' = Nat.card A := rfl
  rw [h1, ← hA]
  have hi : A'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : Nat.card (A'.comap π) * A'.index = (2 * Nat.card A') * A'.index := by
    rw [h2, mul_assoc, h3]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) this

theorem card_inf_centralizer₂ (S : Setting G M θ z π) (F : Facts) (H : Steps12 G M θ π)
    (m₁ m₂ : ↥M) :
    Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer {(m₁ : G)} ⊓
        Subgroup.centralizer {(m₂ : G)}) =
      2 * Nat.card ↥(fixSub (θ m₁) ⊓ fixSub (θ m₂)) := by
  refine S.card_eq_two_mul F (inf_le_left.trans inf_le_left) _ fun q => ?_
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, AddSubgroup.mem_inf,
    mem_fixSub]
  rw [← S.commute_iff H, ← S.commute_iff H]
  exact ⟨fun h => ⟨h.1.2.symm, h.2.symm⟩, fun h => ⟨⟨q.2, h.1.symm⟩, h.2.symm⟩⟩

theorem conj_eq_z (S : Setting G M θ z π) (F : Facts) (H : Steps12 G M θ π) {x : G}
    (hxV : x ∈ CFSG.Open.pCoreOf 2 M) {g : G} (hx : x = g * z * g⁻¹) : x = z := by
  by_contra hxz
  have hx0 : Multiplicative.toAdd (π ⟨x, hxV⟩) ≠ 0 :=
    S.toAdd_π_ne_zero_of_conj ⟨x, hxV⟩ hx hxz
  have hover : ∀ u : altHeart 6, u ≠ 0 → ∃ q : ↥(CFSG.Open.pCoreOf 2 M),
      Multiplicative.toAdd (π q) = u ∧ ∃ h : G, (q : G) = h * z * h⁻¹ := by
    intro u hu
    obtain ⟨σ, hσ⟩ := F.trans _ u hx0 hu
    obtain ⟨m, rfl⟩ := S.surj_θ σ
    refine ⟨⟨m * x * m⁻¹, S.conj_mem m.2 hxV⟩, ?_, m * g, ?_⟩
    · rw [S.equiv m ⟨x, hxV⟩ _ rfl]
      exact hσ
    · show (m : G) * x * (m : G)⁻¹ = m * g * z * (m * g)⁻¹
      rw [hx]
      group
  have h45 : (4 : Fin 6) ≠ 5 := by decide
  have h02 : (0 : Fin 6) ≠ 2 := by decide
  obtain ⟨x45, hx45π, g45, hg45⟩ := hover (pc 4 5) (F.pc_ne_zero 4 5 h45)
  obtain ⟨c02, hc02π, k, hk⟩ := hover (pc 0 2) (F.pc_ne_zero 0 2 h02)
  obtain ⟨t45, ht45W, ht45M, hθt45⟩ := exists_t S F H h45 hx45π hg45
  have hW45 := conj_inf_V_eq S F H h45 hx45π hg45 t45 ht45W ht45M hθt45
  obtain ⟨t02, ht02W, ht02M, hθt02⟩ := exists_t S F H h02 hc02π hk
  have hW02 := conj_inf_V_eq S F H h02 hc02π hk t02 ht02W ht02M hθt02
  set W := conjSubgroup g45 (CFSG.Open.pCoreOf 2 M) with hWdef
  set W02 := conjSubgroup k (CFSG.Open.pCoreOf 2 M) with hW02def
  have hc02C : (c02 : G) ∈ CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer {t45} := by
    refine ⟨c02.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hfix : altAct (θ ⟨t45, ht45M⟩) (Multiplicative.toAdd (π c02)) =
        Multiplicative.toAdd (π c02) := by
      rw [hθt45, hc02π]
      exact (F.fixed_pc_iff _ 0 2 h02).mpr (Or.inl ⟨by decide, by decide⟩)
    exact ((S.commute_iff H ⟨t45, ht45M⟩ c02).mpr hfix).symm
  have hc02W : (c02 : G) ∈ W := by
    rw [← hW45] at hc02C
    exact hc02C.1
  have hcV : g45⁻¹ * c02 * g45 ∈ CFSG.Open.pCoreOf 2 M := mem_conjSubgroup.mp hc02W
  set c : ↥(CFSG.Open.pCoreOf 2 M) := ⟨g45⁻¹ * c02 * g45, hcV⟩ with hcdef
  have hcg : (c : G) = (g45⁻¹ * k) * z * (g45⁻¹ * k)⁻¹ := by
    show g45⁻¹ * c02 * g45 = _
    rw [hk]
    group
  have hcz : (c : G) ≠ z := by
    intro h
    have h1 : (c02 : G) = x45 := by
      have e : (c02 : G) = g45 * c * g45⁻¹ := by
        show (c02 : G) = g45 * (g45⁻¹ * c02 * g45) * g45⁻¹
        group
      rw [e, h, hg45]
    have h2 : pc 0 2 = pc 4 5 := by
      rw [← hc02π, ← hx45π, Subtype.ext h1]
    have h3 := (F.fixed_pc_iff (swap 0 1) 4 5 h45).mpr (Or.inl ⟨by decide, by decide⟩)
    rw [← h2] at h3
    rcases (F.fixed_pc_iff (swap 0 1) 0 2 h02).mp h3 with ⟨h4, -⟩ | ⟨h4, -⟩
    · exact absurd h4 (by decide)
    · exact absurd h4 (by decide)
  have hc0 := S.toAdd_π_ne_zero_of_conj c hcg hcz
  obtain ⟨a, b, hab, hcab⟩ := F.exists_pc _ hc0
  obtain ⟨tc, htcW, htcM, hθtc⟩ := exists_t S F H hab hcab hcg
  have hWc := conj_inf_V_eq S F H hab hcab hcg tc htcW htcM hθtc
  set Wc := conjSubgroup (g45⁻¹ * k) (CFSG.Open.pCoreOf 2 M) with hWcdef
  have hcard16 : Nat.card ↥(Wc ⊓ CFSG.Open.pCoreOf 2 M) = 16 := by
    rw [hWc, S.card_inf_centralizer F H ⟨tc, htcM⟩, hθtc, F.card_fix_swap a b hab]
  have hmap : conjSubgroup g45 (Wc ⊓ CFSG.Open.pCoreOf 2 M) = W02 ⊓ W := by
    ext w
    rw [mem_conjSubgroup, Subgroup.mem_inf, Subgroup.mem_inf, hWcdef, hW02def, hWdef,
      mem_conjSubgroup, mem_conjSubgroup, mem_conjSubgroup]
    have e : (g45⁻¹ * k)⁻¹ * (g45⁻¹ * w * g45) * (g45⁻¹ * k) = k⁻¹ * w * k := by group
    rw [e]
  have hcardA : Nat.card ↥(W02 ⊓ W) = 16 := by
    rw [← hmap, card_conjSubgroup, hcard16]
  have hle : W02 ⊓ W ≤ CFSG.Open.pCoreOf 2 M := by
    rintro w ⟨hw02, hw45⟩
    have hwM := conj_le_M S F H h45 hx45π hg45 hw45
    rcases θ_conj_eq S F H h45 hx45π hg45 w hw45 hwM with h | h
    · exact (S.θ_eq_one_iff _).mp h
    · rcases θ_conj_eq S F H h02 hc02π hk w hw02 hwM with h' | h'
      · exact (S.θ_eq_one_iff _).mp h'
      · exfalso
        rw [h] at h'
        have h4 := congrArg (fun σ : Perm (Fin 6) => σ 4) h'
        simp only [Equiv.swap_apply_left] at h4
        exact absurd h4 (by decide)
  have heq : W02 ⊓ W = CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer {t02} ⊓
      Subgroup.centralizer {t45} := by
    ext w
    constructor
    · intro hw
      have hwV := hle hw
      have h1 : w ∈ W02 ⊓ CFSG.Open.pCoreOf 2 M := ⟨hw.1, hwV⟩
      have h2 : w ∈ W ⊓ CFSG.Open.pCoreOf 2 M := ⟨hw.2, hwV⟩
      rw [hW02] at h1
      rw [hW45] at h2
      exact ⟨h1, h2.2⟩
    · rintro ⟨h1, h2⟩
      have h1' : w ∈ W02 ⊓ CFSG.Open.pCoreOf 2 M := by rw [hW02]; exact h1
      have h2' : w ∈ W ⊓ CFSG.Open.pCoreOf 2 M := by rw [hW45]; exact ⟨h1.1, h2⟩
      exact ⟨h1'.1, h2'.1⟩
  have hcard8 : Nat.card ↥(W02 ⊓ W) = 8 := by
    rw [heq, S.card_inf_centralizer₂ F H ⟨t02, ht02M⟩ ⟨t45, ht45M⟩, hθt02, hθt45, inf_comm,
      F.card_fix_two]
  rw [hcardA] at hcard8
  exact absurd hcard8 (by norm_num)

theorem conjSubgroup_eq_of_mem (S : Setting G M θ z π) {g : G} (hg : g ∈ M) :
    conjSubgroup g (CFSG.Open.pCoreOf 2 M) = CFSG.Open.pCoreOf 2 M := by
  ext x
  rw [mem_conjSubgroup]
  constructor
  · intro h
    have h1 := S.conj_mem hg h
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at h1
  · intro h
    have h1 := S.conj_mem (inv_mem hg) h
    rwa [inv_inv] at h1

theorem weaklyClosedIn_V (S : Setting G M θ z π) (F : Facts) (H : Steps12 G M θ π) :
    WeaklyClosedIn (CFSG.Open.pCoreOf 2 M) M := by
  refine ⟨S.V_le, fun g hg => ?_⟩
  have hzC : g⁻¹ * z * g ∈ Subgroup.centralizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) :
      Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hgv : g * v * g⁻¹ ∈ conjSubgroup g (CFSG.Open.pCoreOf 2 M) := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hv
    have h1 : g * v * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [S.centralizer_eq]
      exact hg hgv
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    calc v * (g⁻¹ * z * g) = g⁻¹ * ((g * v * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * v * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * z * g * v := by group
  have hzV := S.centralizer_V_le F hzC
  have hz := conj_eq_z S F H hzV (g := g⁻¹) (by rw [inv_inv])
  have hgM : g ∈ M := by
    rw [← S.centralizer_eq, Subgroup.mem_centralizer_singleton_iff]
    calc g * z = g * (g⁻¹ * z * g) := by rw [hz]
      _ = z * g := by group
  exact S.conjSubgroup_eq_of_mem hgM

theorem weaklyClosedIn_z (S : Setting G M θ z π) (F : Facts) (H : Steps12 G M θ π) :
    WeaklyClosedIn (Subgroup.zpowers z) (CFSG.Open.pCoreOf 2 M) := by
  refine ⟨(Subgroup.zpowers_le).mpr S.z_mem, fun g hg => ?_⟩
  have hmem : g * z * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
    apply hg
    rw [mem_conjSubgroup]
    have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    rw [e]
    exact Subgroup.mem_zpowers z
  have hz := conj_eq_z S F H hmem rfl
  rw [conjSubgroup, MonoidHom.map_zpowers]
  show Subgroup.zpowers (g * z * g⁻¹) = _
  rw [hz]

theorem exists_sylow_le (S : Setting G M θ z π) (F : Facts) (H : Steps12 G M θ π) :
    ∃ P : Sylow 2 G, (P : Subgroup G) ≤ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 M
  have hVS : CFSG.Open.pCoreOf 2 M ≤ S₀ :=
    CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_le_of_le_normalizer hS₀ S.isPGroup S.V_le
      S.le_normalizer
  have hN : Subgroup.normalizer ((S₀ : Subgroup G) : Set G) ⊓ ⊤ ≤ M := by
    rintro t ⟨ht, -⟩
    have hC : t * z * t⁻¹ ∈ Subgroup.centralizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) :
        Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : t⁻¹ * v * t ∈ S₀ := by
        have h := (Subgroup.mem_normalizer_iff.mp (inv_mem ht) v).mp (hVS hv)
        simpa [mul_assoc] using h
      have hzc := S.z_comm _ (hS₀.le hv')
      calc v * (t * z * t⁻¹) = t * ((t⁻¹ * v * t) * z) * t⁻¹ := by group
        _ = t * (z * (t⁻¹ * v * t)) * t⁻¹ := by rw [hzc]
        _ = t * z * t⁻¹ * v := by group
    have hzV := S.centralizer_V_le F hC
    have hz := conj_eq_z S F H hzV rfl
    rw [← S.centralizer_eq, Subgroup.mem_centralizer_singleton_iff]
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [hz]
  have hS₀' : IsSylowOf 2 S₀ (M ⊓ ⊤) := by rwa [inf_top_eq]
  have hT := CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le hS₀' hN
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hT
  obtain ⟨-, hp, hdvd⟩ := hT
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hp.toSylow hdvd, by rw [IsPGroup.toSylow_coe]; exact hS₀.le⟩

theorem conclusion (S : Setting G M θ z π) (F : Facts) (H : Steps12 G M θ π) :
    CFSG.Open.IsElemAbelian 2 (CFSG.Open.pCoreOf 2 M) ∧
      WeaklyClosedIn (CFSG.Open.pCoreOf 2 M) M ∧
      WeaklyClosedIn (Subgroup.zpowers z) (CFSG.Open.pCoreOf 2 M) ∧
      ∃ P : Sylow 2 G, (P : Subgroup G) ≤ M :=
  ⟨H.elem, S.weaklyClosedIn_V F H, S.weaklyClosedIn_z F H, S.exists_sylow_le F H⟩

end Setting

end CFSG.CGT.Hall82.TheoremA
