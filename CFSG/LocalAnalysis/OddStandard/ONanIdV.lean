module

public import CFSG.LocalAnalysis.OddStandard.ONanLocOne

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris

@[expose] def InWE (w : AlpE) : Prop := w.d = 0 ∧ w * w = 1

instance (w : AlpE) : Decidable (InWE w) := inferInstanceAs (Decidable (_ ∧ _))

@[expose] def InXWE (w : AlpE) : Prop := InWE w ∨ InWE (xE⁻¹ * w)

instance (w : AlpE) : Decidable (InXWE w) := inferInstanceAs (Decidable (_ ∨ _))

@[expose] def s2E : AlpE := gen 3 ^ 2

@[expose] def tE : AlpE := gen 4

theorem xE_comm_s2E : s2E * xE = xE * s2E := by decide
theorem xE_comm_tE : tE * xE = xE * tE := by decide

theorem pat_s2E : InWE (xE⁻¹ * ((gen 0)⁻¹ * (s2E * gen 0 * s2E⁻¹))) ∧
    InWE (xE⁻¹ * ((gen 1)⁻¹ * (s2E * gen 1 * s2E⁻¹))) ∧
    InWE (xE⁻¹ * ((gen 2)⁻¹ * (s2E * gen 2 * s2E⁻¹))) := by decide

theorem pat_tE : InWE (xE⁻¹ * ((gen 0)⁻¹ * (tE * gen 0 * tE⁻¹))) ∧
    InWE ((gen 1)⁻¹ * (tE * gen 1 * tE⁻¹)) ∧
    InWE (xE⁻¹ * ((gen 2)⁻¹ * (tE * gen 2 * tE⁻¹))) := by decide

theorem pat_s2tE : InWE ((gen 0)⁻¹ * (s2E * tE * gen 0 * (s2E * tE)⁻¹)) ∧
    InWE (xE⁻¹ * ((gen 1)⁻¹ * (s2E * tE * gen 1 * (s2E * tE)⁻¹))) ∧
    InWE ((gen 2)⁻¹ * (s2E * tE * gen 2 * (s2E * tE)⁻¹)) := by decide

set_option maxRecDepth 100000 in
theorem fix_xW_E : ∀ y : AlpE, InWE (xE⁻¹ * y) → s2E * y = y * s2E → tE * y = y * tE →
    y = xE ∨ y = xE⁻¹ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sq_WE : ∀ w : AlpE, InWE w → ∃ v : AlpE, v.d = 0 ∧ v * v = w := by
  decide +kernel

theorem xE_sq_W : InWE (xE * xE) := by decide

set_option maxRecDepth 100000 in
theorem sq_V_WE : ∀ y : AlpE, y.d = 0 → InWE (y * y) := by decide +kernel

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

theorem mem_W_phi (y : AlpE) : D.E.φ y ∈ alpW v1 v2 v3 ↔ InWE y := by
  rw [D.mem_W_iff, AlpEmb.alpV_eq_map D.E, Subgroup.mem_map_iff_mem D.E.inj, mem_Vsub]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, D.E.inj (by rw [map_mul, h2, map_one])⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [← map_mul, h2, map_one]⟩

theorem x_mem_V : xel v1 v2 v3 ∈ alpV v1 v2 v3 := by
  rw [← AlpEmb.φ_xE D.E, AlpEmb.alpV_eq_map D.E]
  exact Subgroup.mem_map_of_mem _ (mem_Vsub.2 rfl)

theorem x_eq : xel v1 v2 v3 = D.E.φ xE := (AlpEmb.φ_xE D.E).symm

theorem x_sq_mem_W : xel v1 v2 v3 * xel v1 v2 v3 ∈ alpW v1 v2 v3 := by
  rw [D.x_eq, ← map_mul, D.mem_W_phi]
  exact xE_sq_W

theorem exists_sq_eq {w : G} (hw : w ∈ alpW v1 v2 v3) : ∃ v ∈ alpV v1 v2 v3, v * v = w := by
  have hwV := D.W_le_V hw
  rw [AlpEmb.alpV_eq_map D.E] at hwV
  obtain ⟨w', -, rfl⟩ := Subgroup.mem_map.1 hwV
  obtain ⟨v', hv'd, hv'⟩ := sq_WE w' ((D.mem_W_phi w').1 hw)
  refine ⟨D.E.φ v', ?_, by rw [← map_mul, hv']⟩
  rw [AlpEmb.alpV_eq_map D.E]
  exact Subgroup.mem_map_of_mem _ (mem_Vsub.2 hv'd)

theorem sq_mem_W {v : G} (hv : v ∈ alpV v1 v2 v3) : v * v ∈ alpW v1 v2 v3 := by
  rw [AlpEmb.alpV_eq_map D.E] at hv
  obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.1 hv
  rw [← map_mul, D.mem_W_phi]
  exact sq_V_WE v' (mem_Vsub.1 hv')

omit [Finite G] D in
theorem conj_mem_V {n v : G} (hn : n ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hv : v ∈ alpV v1 v2 v3) : n * v * n⁻¹ ∈ alpV v1 v2 v3 :=
  (mem_normalizer_iff.1 hn v).1 hv

omit [Finite G] D in
theorem conj_inv_mem_V {n v : G} (hn : n ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hv : v ∈ alpV v1 v2 v3) : n⁻¹ * v * n ∈ alpV v1 v2 v3 := by
  have := conj_mem_V (inv_mem hn) hv
  rwa [inv_inv] at this

theorem conj_mem_W {n w : G} (hn : n ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hw : w ∈ alpW v1 v2 v3) : n * w * n⁻¹ ∈ alpW v1 v2 v3 :=
  (mem_normalizer_iff.1 (D.normalizer_V_le_W hn) w).1 hw

theorem conj_inv_mem_W {n w : G} (hn : n ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hw : w ∈ alpW v1 v2 v3) : n⁻¹ * w * n ∈ alpW v1 v2 v3 := by
  have := D.conj_mem_W (inv_mem hn) hw
  rwa [inv_inv] at this

theorem comm_V {u v : G} (hu : u ∈ alpV v1 v2 v3) (hv : v ∈ alpV v1 v2 v3) : u * v = v * u :=
  mem_centralizer_iff.1 (D.V_le_centralizer_V hv) u hu

theorem sq_mem_centralizer_V {n : G} (hn : n ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hnW : n ∈ centralizer (alpW v1 v2 v3 : Set G)) :
    n * n ∈ centralizer (alpV v1 v2 v3 : Set G) := by
  rw [mem_centralizer_iff]
  intro v hv
  set u := v⁻¹ * (n * v * n⁻¹) with hu
  have hnv := conj_mem_V hn hv
  have huV : u ∈ alpV v1 v2 v3 := mul_mem (inv_mem hv) hnv
  have hvv := D.sq_mem_W hv
  have hnvv : n * (v * v) * n⁻¹ = v * v := by
    rw [← mem_centralizer_iff.1 hnW _ hvv, mul_inv_cancel_right]
  have hc := D.comm_V hv huV
  have e1 : n * v * n⁻¹ = v * u := by rw [hu]; group
  have hu2 : u * u = 1 := by
    have e2 : n * (v * v) * n⁻¹ = (v * v) * (u * u) := by
      calc n * (v * v) * n⁻¹ = (n * v * n⁻¹) * (n * v * n⁻¹) := by group
        _ = (v * u) * (v * u) := by rw [e1]
        _ = v * (u * v) * u := by group
        _ = v * (v * u) * u := by rw [hc]
        _ = (v * v) * (u * u) := by group
    rw [hnvv] at e2
    calc u * u = (v * v)⁻¹ * ((v * v) * (u * u)) := by group
      _ = 1 := by rw [← e2, inv_mul_cancel]
  have huW : u ∈ alpW v1 v2 v3 := D.mem_W_iff.2 ⟨huV, hu2⟩
  have hnu : n * u * n⁻¹ = u := by rw [← mem_centralizer_iff.1 hnW _ huW, mul_inv_cancel_right]
  have e3 : n * n * v * (n * n)⁻¹ = v := by
    calc n * n * v * (n * n)⁻¹ = n * (n * v * n⁻¹) * n⁻¹ := by group
      _ = n * (v * u) * n⁻¹ := by rw [e1]
      _ = (n * v * n⁻¹) * (n * u * n⁻¹) := by group
      _ = v * u * u := by rw [e1, hnu]
      _ = v := by rw [mul_assoc, hu2, mul_one]
  calc v * (n * n) = (n * n * v * (n * n)⁻¹) * (n * n) := by rw [e3]
    _ = n * n * v := by group

theorem mem_centralizer_V_of_W {n : G} (hn : n ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hnW : n ∈ centralizer (alpW v1 v2 v3 : Set G)) :
    n ∈ centralizer (alpV v1 v2 v3 : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (alpV v1 v2 v3 : Set G) with hN
  set Q := N ⊓ centralizer (alpW v1 v2 v3 : Set G) with hQ
  set K := centralizer (alpV v1 v2 v3 : Set G) ⊓ Q with hK
  have hVK : alpV v1 v2 v3 ≤ K := fun v hv =>
    ⟨D.V_le_centralizer_V hv, D.P_le_normalizer_V (D.V_le_P hv), D.V_le_centralizer_W hv⟩
  have hKQ : K ≤ Q := inf_le_right
  have hQn : N ≤ normalizer (Q : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      obtain ⟨hq1, hq2⟩ := Subgroup.mem_inf.1 hq
      refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hq1)
        (Subgroup.inv_mem _ hg), ?_⟩
      exact conj_mem_centralizer_W (D.normalizer_V_le_W hg) hq2
    · intro hq
      obtain ⟨hq1, hq2⟩ := Subgroup.mem_inf.1 hq
      have h1 : q = g⁻¹ * (g * q * g⁻¹) * g⁻¹⁻¹ := by group
      rw [h1]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hq1)
        (Subgroup.inv_mem _ (Subgroup.inv_mem _ hg)), ?_⟩
      exact conj_mem_centralizer_W (D.normalizer_V_le_W (Subgroup.inv_mem _ hg)) hq2
  have hPN : alpP v1 v2 v3 s t ≤ N := D.P_le_normalizer_V
  have hSylN : IsSylowOf 2 (alpP v1 v2 v3 s t) N := D.isSylowOf_P.of_le hPN le_top
  have hSylQ := hSylN.inf_of_le_normalizer inf_le_left hQn
  have hPQ : alpP v1 v2 v3 s t ⊓ Q = alpV v1 v2 v3 := by
    rw [hQ, ← inf_assoc, inf_of_le_left hPN, D.P_inf_centralizer_W]
  rw [hPQ] at hSylQ
  have hodd : ¬ 2 ∣ (alpV v1 v2 v3).relIndex Q := ((isSylowOf_iff).1 hSylQ).2.2
  have hKn : (K.subgroupOf Q).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨g', hg'⟩ := g
    have ha1 : (a : G) ∈ centralizer (alpV v1 v2 v3 : Set G) := (Subgroup.mem_inf.1 ha).1
    have hg : g' ∈ N := (Subgroup.mem_inf.1 hg').1
    have e : ((⟨g', hg'⟩ * a * (⟨g', hg'⟩ : Q)⁻¹ : Q) : G) = g' * a * g'⁻¹ := rfl
    rw [e]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_centralizer_iff] at ha1 ⊢
      intro v hv
      have h1 := ha1 _ (conj_inv_mem_V hg hv)
      calc v * (g' * a * g'⁻¹) = g' * ((g'⁻¹ * v * g') * a) * g'⁻¹ := by group
        _ = g' * (a * (g'⁻¹ * v * g')) * g'⁻¹ := by rw [h1]
        _ = g' * a * g'⁻¹ * v := by group
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg' a.2) (Subgroup.inv_mem _ hg')
  have hrel := Subgroup.relIndex_mul_relIndex (alpV v1 v2 v3) K Q hVK hKQ
  have hrodd : ¬ 2 ∣ K.relIndex Q := fun h2 => hodd (hrel ▸ Dvd.dvd.mul_left h2 _)
  obtain ⟨j, hj⟩ : ∃ j, K.relIndex Q = 2 * j + 1 := ⟨K.relIndex Q / 2, by omega⟩
  have hnQ : n ∈ Q := ⟨hn, hnW⟩
  have hpow : (⟨n, hnQ⟩ : Q) ^ (K.subgroupOf Q).index ∈ K.subgroupOf Q :=
    Subgroup.pow_index_mem _ _
  rw [Subgroup.mem_subgroupOf] at hpow
  have hpow' : n ^ (2 * j + 1) ∈ K := by
    have e : ((⟨n, hnQ⟩ : Q) ^ (K.subgroupOf Q).index : Q) = (n : G) ^ (K.relIndex Q) := by
      rw [Subgroup.coe_pow]
      rfl
    rw [e, hj] at hpow
    exact hpow
  have hsq : n * n ∈ K := ⟨D.sq_mem_centralizer_V hn hnW, mul_mem hnQ hnQ⟩
  have e2 : n = n ^ (2 * j + 1) * ((n * n) ^ j)⁻¹ := by
    rw [← sq, ← pow_mul, pow_succ]
    group
  have hnK : n ∈ K := by
    rw [e2]
    exact mul_mem hpow' (inv_mem (pow_mem hsq j))
  exact hnK.1

theorem mem_centralizer_V_of_agree {n n' : G} (hn : n ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hn' : n' ∈ normalizer (alpV v1 v2 v3 : Set G))
    (h : ∀ v ∈ alpV v1 v2 v3, (n * v * n⁻¹)⁻¹ * (n' * v * n'⁻¹) ∈ alpW v1 v2 v3) :
    n⁻¹ * n' ∈ centralizer (alpV v1 v2 v3 : Set G) := by
  set m := n⁻¹ * n' with hm
  have hmN : m ∈ normalizer (alpV v1 v2 v3 : Set G) := mul_mem (inv_mem hn) hn'
  refine D.mem_centralizer_V_of_W hmN ?_
  rw [mem_centralizer_iff]
  intro w hw
  obtain ⟨v, hv, rfl⟩ := D.exists_sq_eq hw
  have hu : v⁻¹ * (m * v * m⁻¹) ∈ alpW v1 v2 v3 := by
    have h1 := D.conj_inv_mem_W hn (h v hv)
    have e : n⁻¹ * ((n * v * n⁻¹)⁻¹ * (n' * v * n'⁻¹)) * n = v⁻¹ * (m * v * m⁻¹) := by
      rw [hm]; group
    rwa [e] at h1
  set u := v⁻¹ * (m * v * m⁻¹) with hu'
  have huV : u ∈ alpV v1 v2 v3 := D.W_le_V hu
  have hu2 : u * u = 1 := (D.mem_W_iff.1 hu).2
  have e1 : m * v * m⁻¹ = v * u := by rw [hu']; group
  have hc := D.comm_V hv huV
  have e2 : m * (v * v) * m⁻¹ = v * v := by
    calc m * (v * v) * m⁻¹ = (m * v * m⁻¹) * (m * v * m⁻¹) := by group
      _ = (v * u) * (v * u) := by rw [e1]
      _ = v * (u * v) * u := by group
      _ = v * (v * u) * u := by rw [hc]
      _ = v * v * (u * u) := by group
      _ = v * v := by rw [hu2, mul_one]
  calc v * v * m = (m * (v * v) * m⁻¹) * m := by rw [e2]
    _ = m * (v * v) := by group

theorem agree_of_gens {k p : G} (hk : k ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hp : p ∈ normalizer (alpV v1 v2 v3 : Set G)) (S : Set G)
    (hS : closure S = alpV v1 v2 v3)
    (h : ∀ v ∈ S, (k * v * k⁻¹)⁻¹ * (p * v * p⁻¹) ∈ alpW v1 v2 v3) :
    ∀ v ∈ alpV v1 v2 v3, (k * v * k⁻¹)⁻¹ * (p * v * p⁻¹) ∈ alpW v1 v2 v3 := by
  intro v hv
  rw [← hS] at hv
  have hSV : ∀ {u : G}, u ∈ closure S → u ∈ alpV v1 v2 v3 := fun hu => hS ▸ hu
  induction hv using Subgroup.closure_induction with
  | mem v hv => exact h v hv
  | one => simp
  | mul u v hu hv ihu ihv =>
    have hku := conj_mem_V hk (hSV hu)
    have hkv := conj_mem_V hk (hSV hv)
    have hpu := conj_mem_V hp (hSV hu)
    have hpv := conj_mem_V hp (hSV hv)
    have e : (k * (u * v) * k⁻¹)⁻¹ * (p * (u * v) * p⁻¹) =
        ((k * u * k⁻¹)⁻¹ * (p * u * p⁻¹)) * ((k * v * k⁻¹)⁻¹ * (p * v * p⁻¹)) := by
      have c1 : (k * v * k⁻¹)⁻¹ * (k * u * k⁻¹)⁻¹ = (k * u * k⁻¹)⁻¹ * (k * v * k⁻¹)⁻¹ :=
        D.comm_V (inv_mem hkv) (inv_mem hku)
      have c2 : (k * v * k⁻¹)⁻¹ * (p * u * p⁻¹) = (p * u * p⁻¹) * (k * v * k⁻¹)⁻¹ :=
        D.comm_V (inv_mem hkv) hpu
      calc (k * (u * v) * k⁻¹)⁻¹ * (p * (u * v) * p⁻¹) =
          ((k * v * k⁻¹)⁻¹ * (k * u * k⁻¹)⁻¹) * ((p * u * p⁻¹) * (p * v * p⁻¹)) := by group
        _ = ((k * u * k⁻¹)⁻¹ * (k * v * k⁻¹)⁻¹) * ((p * u * p⁻¹) * (p * v * p⁻¹)) := by rw [c1]
        _ = (k * u * k⁻¹)⁻¹ * ((k * v * k⁻¹)⁻¹ * (p * u * p⁻¹)) * (p * v * p⁻¹) := by group
        _ = (k * u * k⁻¹)⁻¹ * ((p * u * p⁻¹) * (k * v * k⁻¹)⁻¹) * (p * v * p⁻¹) := by rw [c2]
        _ = ((k * u * k⁻¹)⁻¹ * (p * u * p⁻¹)) * ((k * v * k⁻¹)⁻¹ * (p * v * p⁻¹)) := by group
    rw [e]
    exact mul_mem ihu ihv
  | inv u hu ihu =>
    have hku := conj_mem_V hk (hSV hu)
    have hpu := conj_mem_V hp (hSV hu)
    have c : (k * u * k⁻¹) * (p * u * p⁻¹)⁻¹ = (p * u * p⁻¹)⁻¹ * (k * u * k⁻¹) :=
      D.comm_V hku (inv_mem hpu)
    have e : (k * u⁻¹ * k⁻¹)⁻¹ * (p * u⁻¹ * p⁻¹) = ((k * u * k⁻¹)⁻¹ * (p * u * p⁻¹))⁻¹ := by
      calc (k * u⁻¹ * k⁻¹)⁻¹ * (p * u⁻¹ * p⁻¹) = (k * u * k⁻¹) * (p * u * p⁻¹)⁻¹ := by group
        _ = (p * u * p⁻¹)⁻¹ * (k * u * k⁻¹) := c
        _ = ((k * u * k⁻¹)⁻¹ * (p * u * p⁻¹))⁻¹ := by group
    rw [e]
    exact inv_mem ihu

@[expose] def XW : Subgroup G where
  carrier := {y | y ∈ alpV v1 v2 v3 ∧
    (y ∈ alpW v1 v2 v3 ∨ (xel v1 v2 v3)⁻¹ * y ∈ alpW v1 v2 v3)}
  one_mem' := ⟨one_mem _, Or.inl (one_mem _)⟩
  mul_mem' := by
    rintro y1 y2 ⟨h1V, h1⟩ ⟨h2V, h2⟩
    refine ⟨mul_mem h1V h2V, ?_⟩
    have hxV := D.x_mem_V
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Or.inl (mul_mem h1 h2)
    · right
      have c := D.comm_V (inv_mem hxV) h1V
      have e : (xel v1 v2 v3)⁻¹ * (y1 * y2) = y1 * ((xel v1 v2 v3)⁻¹ * y2) := by
        rw [← mul_assoc, c, mul_assoc]
      rw [e]
      exact mul_mem h1 h2
    · right
      rw [← mul_assoc]
      exact mul_mem h1 h2
    · left
      have c := D.comm_V (mul_mem (inv_mem hxV) h1V) hxV
      have e : y1 * y2 = (xel v1 v2 v3 * xel v1 v2 v3) *
          (((xel v1 v2 v3)⁻¹ * y1) * ((xel v1 v2 v3)⁻¹ * y2)) := by
        calc y1 * y2 = xel v1 v2 v3 * ((xel v1 v2 v3)⁻¹ * y1) * xel v1 v2 v3 *
            ((xel v1 v2 v3)⁻¹ * y2) := by group
          _ = xel v1 v2 v3 * (xel v1 v2 v3 * ((xel v1 v2 v3)⁻¹ * y1)) *
            ((xel v1 v2 v3)⁻¹ * y2) := by rw [mul_assoc (xel v1 v2 v3), c]
          _ = _ := by group
      rw [e]
      exact mul_mem D.x_sq_mem_W (mul_mem h1 h2)
  inv_mem' := by
    rintro y ⟨hyV, hy⟩
    refine ⟨inv_mem hyV, ?_⟩
    rcases hy with hy | hy
    · exact Or.inl (inv_mem hy)
    · right
      have hxV := D.x_mem_V
      have c := D.comm_V hyV hxV
      have e : (xel v1 v2 v3)⁻¹ * y⁻¹ =
          ((xel v1 v2 v3)⁻¹ * y)⁻¹ * (xel v1 v2 v3 * xel v1 v2 v3)⁻¹ := by
        calc (xel v1 v2 v3)⁻¹ * y⁻¹ = (y * xel v1 v2 v3)⁻¹ := by group
          _ = (xel v1 v2 v3 * y)⁻¹ := by rw [c]
          _ = _ := by group
      rw [e]
      exact mul_mem (inv_mem hy) (inv_mem D.x_sq_mem_W)

theorem f_mem_of_gens {p : G} (hp : p ∈ normalizer (alpV v1 v2 v3 : Set G)) (S : Subgroup G)
    (h : ∀ v ∈ ({v1, v2, v3} : Set G), v⁻¹ * (p * v * p⁻¹) ∈ S) :
    ∀ v ∈ alpV v1 v2 v3, v⁻¹ * (p * v * p⁻¹) ∈ S := by
  intro v hv
  induction hv using Subgroup.closure_induction with
  | mem v hv => exact h v hv
  | one => simp
  | mul u v hu hv ihu ihv =>
    have hpu := conj_mem_V hp hu
    have c : v⁻¹ * u⁻¹ * (p * u * p⁻¹) = u⁻¹ * (p * u * p⁻¹) * v⁻¹ := by
      rw [mul_assoc]
      exact D.comm_V (inv_mem hv) (mul_mem (inv_mem hu) hpu)
    have e : (u * v)⁻¹ * (p * (u * v) * p⁻¹) =
        (u⁻¹ * (p * u * p⁻¹)) * (v⁻¹ * (p * v * p⁻¹)) := by
      calc (u * v)⁻¹ * (p * (u * v) * p⁻¹) = (v⁻¹ * u⁻¹ * (p * u * p⁻¹)) * (p * v * p⁻¹) := by
            group
        _ = (u⁻¹ * (p * u * p⁻¹) * v⁻¹) * (p * v * p⁻¹) := by rw [c]
        _ = _ := by group
    rw [e]
    exact mul_mem ihu ihv
  | inv u hu ihu =>
    have hpu := conj_mem_V hp hu
    have c : u * (p * u * p⁻¹)⁻¹ = (p * u * p⁻¹)⁻¹ * u := D.comm_V hu (inv_mem hpu)
    have e : u⁻¹⁻¹ * (p * u⁻¹ * p⁻¹) = (u⁻¹ * (p * u * p⁻¹))⁻¹ := by
      calc u⁻¹⁻¹ * (p * u⁻¹ * p⁻¹) = u * (p * u * p⁻¹)⁻¹ := by group
        _ = (p * u * p⁻¹)⁻¹ * u := c
        _ = _ := by group
    rw [e]
    exact inv_mem ihu

theorem closure_v1_v2_x : closure ({v1, v2, xel v1 v2 v3} : Set G) = alpV v1 v2 v3 := by
  apply le_antisymm
  · rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact D.x_mem_V
  · rw [alpV, closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have h1 : v1 ∈ closure ({v1, v2, xel v1 v2 v3} : Set G) := subset_closure (by simp)
    have h2 : v2 ∈ closure ({v1, v2, xel v1 v2 v3} : Set G) := subset_closure (by simp)
    have h3 : xel v1 v2 v3 ∈ closure ({v1, v2, xel v1 v2 v3} : Set G) := subset_closure (by simp)
    rcases hg with h | h | h
    · rw [h]; exact h1
    · rw [h]; exact h2
    · have e : v3 = (xel v1 v2 v3)⁻¹ * v1 * (v2 * v2) := by
        unfold xel
        group
      have h4 := mul_mem (mul_mem (inv_mem h3) h1) (mul_mem h2 h2)
      rw [← e] at h4
      rw [h]
      exact h4

theorem phi_f (q y : AlpE) {qG yG : G} (hq : D.E.φ q = qG) (hy : D.E.φ y = yG) :
    D.E.φ (y⁻¹ * (q * y * q⁻¹)) = yG⁻¹ * (qG * yG * qG⁻¹) := by
  rw [← hq, ← hy]
  simp only [map_mul, map_inv]

theorem phi_xf (q y : AlpE) {qG yG : G} (hq : D.E.φ q = qG) (hy : D.E.φ y = yG) :
    D.E.φ (xE⁻¹ * (y⁻¹ * (q * y * q⁻¹))) = (xel v1 v2 v3)⁻¹ * (yG⁻¹ * (qG * yG * qG⁻¹)) := by
  rw [map_mul, D.phi_f q y hq hy, map_inv, AlpEmb.φ_xE D.E]

theorem phi_s2 : D.E.φ s2E = s ^ 2 := by rw [s2E, map_pow, AlpEmb.φ_s D.E]

theorem phi_t : D.E.φ tE = t := by rw [tE, AlpEmb.φ_t D.E]

theorem phi_s2t : D.E.φ (s2E * tE) = s ^ 2 * t := by rw [map_mul, D.phi_s2, D.phi_t]

omit [Finite G] D in
theorem s_mem_P : s ∈ alpP v1 v2 v3 s t := subset_closure (by simp)

omit [Finite G] D in
theorem t_mem_P : t ∈ alpP v1 v2 v3 s t := subset_closure (by simp)

theorem s2_mem_N : s ^ 2 ∈ normalizer (alpV v1 v2 v3 : Set G) :=
  D.P_le_normalizer_V (pow_mem s_mem_P 2)

theorem t_mem_N : t ∈ normalizer (alpV v1 v2 v3 : Set G) := D.P_le_normalizer_V t_mem_P

theorem s2_fix_x : s ^ 2 * xel v1 v2 v3 * (s ^ 2)⁻¹ = xel v1 v2 v3 := by
  have h := congrArg D.E.φ xE_comm_s2E
  rw [map_mul, map_mul, D.phi_s2, AlpEmb.φ_xE D.E] at h
  rw [h, mul_inv_cancel_right]

theorem t_fix_x : t * xel v1 v2 v3 * t⁻¹ = xel v1 v2 v3 := by
  have h := congrArg D.E.φ xE_comm_tE
  rw [map_mul, map_mul, D.phi_t, AlpEmb.φ_xE D.E] at h
  rw [h, mul_inv_cancel_right]

theorem pat_s2 : ∀ v ∈ ({v1, v2, v3} : Set G),
    (xel v1 v2 v3)⁻¹ * (v⁻¹ * (s ^ 2 * v * (s ^ 2)⁻¹)) ∈ alpW v1 v2 v3 := by
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  obtain ⟨h0, h1, h2⟩ := pat_s2E
  rcases hv with h | h | h <;> rw [h]
  · have := (D.mem_W_phi _).2 h0
    rwa [D.phi_xf _ _ D.phi_s2 (AlpEmb.φ_v1 D.E)] at this
  · have := (D.mem_W_phi _).2 h1
    rwa [D.phi_xf _ _ D.phi_s2 (AlpEmb.φ_v2 D.E)] at this
  · have := (D.mem_W_phi _).2 h2
    rwa [D.phi_xf _ _ D.phi_s2 (AlpEmb.φ_v3 D.E)] at this

theorem pat_t : (xel v1 v2 v3)⁻¹ * (v1⁻¹ * (t * v1 * t⁻¹)) ∈ alpW v1 v2 v3 ∧
    v2⁻¹ * (t * v2 * t⁻¹) ∈ alpW v1 v2 v3 ∧
    (xel v1 v2 v3)⁻¹ * (v3⁻¹ * (t * v3 * t⁻¹)) ∈ alpW v1 v2 v3 := by
  obtain ⟨h0, h1, h2⟩ := pat_tE
  refine ⟨?_, ?_, ?_⟩
  · have := (D.mem_W_phi _).2 h0
    rwa [D.phi_xf _ _ D.phi_t (AlpEmb.φ_v1 D.E)] at this
  · have := (D.mem_W_phi _).2 h1
    rwa [D.phi_f _ _ D.phi_t (AlpEmb.φ_v2 D.E)] at this
  · have := (D.mem_W_phi _).2 h2
    rwa [D.phi_xf _ _ D.phi_t (AlpEmb.φ_v3 D.E)] at this

theorem pat_s2t : v1⁻¹ * (s ^ 2 * t * v1 * (s ^ 2 * t)⁻¹) ∈ alpW v1 v2 v3 ∧
    (xel v1 v2 v3)⁻¹ * (v2⁻¹ * (s ^ 2 * t * v2 * (s ^ 2 * t)⁻¹)) ∈ alpW v1 v2 v3 := by
  obtain ⟨h0, h1, -⟩ := pat_s2tE
  refine ⟨?_, ?_⟩
  · have := (D.mem_W_phi _).2 h0
    rwa [D.phi_f _ _ D.phi_s2t (AlpEmb.φ_v1 D.E)] at this
  · have := (D.mem_W_phi _).2 h1
    rwa [D.phi_xf _ _ D.phi_s2t (AlpEmb.φ_v2 D.E)] at this

theorem pat_t_XW : ∀ v ∈ ({v1, v2, v3} : Set G), v⁻¹ * (t * v * t⁻¹) ∈ D.XW := by
  obtain ⟨h0, h1, h2⟩ := D.pat_t
  intro v hv
  have hV : v⁻¹ * (t * v * t⁻¹) ∈ alpV v1 v2 v3 := by
    have hv' : v ∈ alpV v1 v2 v3 := subset_closure hv
    exact mul_mem (inv_mem hv') (conj_mem_V D.t_mem_N hv')
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl
  · exact ⟨hV, Or.inr h0⟩
  · exact ⟨hV, Or.inl h1⟩
  · exact ⟨hV, Or.inr h2⟩

theorem pat_s2_XW : ∀ v ∈ ({v1, v2, v3} : Set G), v⁻¹ * (s ^ 2 * v * (s ^ 2)⁻¹) ∈ D.XW := by
  intro v hv
  have hv' : v ∈ alpV v1 v2 v3 := subset_closure hv
  exact ⟨mul_mem (inv_mem hv') (conj_mem_V D.s2_mem_N hv'), Or.inr (D.pat_s2 v hv)⟩

omit [Finite G] D in
theorem inv_mul_mem_xW {a b : G} (ha : (xel v1 v2 v3)⁻¹ * a ∈ alpW v1 v2 v3)
    (hb : (xel v1 v2 v3)⁻¹ * b ∈ alpW v1 v2 v3) : a⁻¹ * b ∈ alpW v1 v2 v3 := by
  have e : a⁻¹ * b = ((xel v1 v2 v3)⁻¹ * a)⁻¹ * ((xel v1 v2 v3)⁻¹ * b) := by group
  rw [e]
  exact mul_mem (inv_mem ha) hb

omit [Finite G] D in
theorem conj_eq_mul (k v : G) : k * v * k⁻¹ = v * (v⁻¹ * (k * v * k⁻¹)) := by group

theorem fix_x_of_pattern {k : G} (hk : k ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hkx : (xel v1 v2 v3)⁻¹ * (k * xel v1 v2 v3 * k⁻¹) ∈ alpW v1 v2 v3)
    (h1 : v1⁻¹ * (k * v1 * k⁻¹) ∈ D.XW) (h2 : v2⁻¹ * (k * v2 * k⁻¹) ∈ D.XW) :
    k * xel v1 v2 v3 * k⁻¹ = xel v1 v2 v3 := by
  set x := xel v1 v2 v3 with hx
  have main : ∀ p : G, p ∈ normalizer (alpV v1 v2 v3 : Set G) → p * x * p⁻¹ = x →
      (k * v1 * k⁻¹)⁻¹ * (p * v1 * p⁻¹) ∈ alpW v1 v2 v3 →
      (k * v2 * k⁻¹)⁻¹ * (p * v2 * p⁻¹) ∈ alpW v1 v2 v3 → k * x * k⁻¹ = x := by
    intro p hp hpx a1 a2
    have hag := D.agree_of_gens hk hp _ D.closure_v1_v2_x (by
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with h | h | h
      · rw [h]; exact a1
      · rw [h]; exact a2
      · rw [h, hpx]
        have e : (k * x * k⁻¹)⁻¹ * x = (x⁻¹ * (k * x * k⁻¹))⁻¹ := by group
        rw [e]
        exact inv_mem hkx)
    have hc := D.mem_centralizer_V_of_agree hk hp hag
    have h3 := mem_centralizer_iff.1 hc x D.x_mem_V
    calc k * x * k⁻¹ = k * (x * (k⁻¹ * p)) * p⁻¹ := by group
      _ = k * ((k⁻¹ * p) * x) * p⁻¹ := by rw [h3]
      _ = p * x * p⁻¹ := by group
      _ = x := hpx
  have e1 := conj_eq_mul k v1
  have e2 := conj_eq_mul k v2
  have key : ∀ (p : G) (f1 f2 : G), (k * v1 * k⁻¹) = v1 * f1 → (k * v2 * k⁻¹) = v2 * f2 →
      (p * v1 * p⁻¹) = v1 * (v1⁻¹ * (p * v1 * p⁻¹)) →
      f1⁻¹ * (v1⁻¹ * (p * v1 * p⁻¹)) ∈ alpW v1 v2 v3 →
      f2⁻¹ * (v2⁻¹ * (p * v2 * p⁻¹)) ∈ alpW v1 v2 v3 →
      (k * v1 * k⁻¹)⁻¹ * (p * v1 * p⁻¹) ∈ alpW v1 v2 v3 ∧
        (k * v2 * k⁻¹)⁻¹ * (p * v2 * p⁻¹) ∈ alpW v1 v2 v3 := by
    intro p f1 f2 hf1 hf2 _ b1 b2
    refine ⟨?_, ?_⟩
    · rw [hf1, show (p * v1 * p⁻¹) = v1 * (v1⁻¹ * (p * v1 * p⁻¹)) by group,
        show (v1 * f1)⁻¹ * (v1 * (v1⁻¹ * (p * v1 * p⁻¹))) = f1⁻¹ * (v1⁻¹ * (p * v1 * p⁻¹)) by
          group]
      exact b1
    · rw [hf2, show (p * v2 * p⁻¹) = v2 * (v2⁻¹ * (p * v2 * p⁻¹)) by group,
        show (v2 * f2)⁻¹ * (v2 * (v2⁻¹ * (p * v2 * p⁻¹))) = f2⁻¹ * (v2⁻¹ * (p * v2 * p⁻¹)) by
          group]
      exact b2
  obtain ⟨-, h1⟩ := h1
  obtain ⟨-, h2⟩ := h2
  obtain ⟨t1, t2, -⟩ := D.pat_t
  obtain ⟨u1, u2⟩ := D.pat_s2t
  have s1 := D.pat_s2 v1 (by simp)
  have s2' := D.pat_s2 v2 (by simp)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  ·
    obtain ⟨a1, a2⟩ := key 1 _ _ e1 e2 (by group)
      (by rw [show v1⁻¹ * (1 * v1 * 1⁻¹) = 1 by group, mul_one]; exact inv_mem h1)
      (by rw [show v2⁻¹ * (1 * v2 * 1⁻¹) = 1 by group, mul_one]; exact inv_mem h2)
    exact main 1 (one_mem _) (by group) a1 a2
  ·
    obtain ⟨a1, a2⟩ := key (s ^ 2 * t) _ _ e1 e2 (by group)
      (mul_mem (inv_mem h1) u1) (inv_mul_mem_xW h2 u2)
    refine main (s ^ 2 * t) (mul_mem D.s2_mem_N D.t_mem_N) ?_ a1 a2
    calc s ^ 2 * t * x * (s ^ 2 * t)⁻¹ = s ^ 2 * (t * x * t⁻¹) * (s ^ 2)⁻¹ := by group
      _ = x := by rw [D.t_fix_x, D.s2_fix_x]
  ·
    obtain ⟨a1, a2⟩ := key t _ _ e1 e2 (by group) (inv_mul_mem_xW h1 t1)
      (mul_mem (inv_mem h2) t2)
    exact main t D.t_mem_N D.t_fix_x a1 a2
  ·
    obtain ⟨a1, a2⟩ := key (s ^ 2) _ _ e1 e2 (by group) (inv_mul_mem_xW h1 s1)
      (inv_mul_mem_xW h2 s2')
    exact main (s ^ 2) D.s2_mem_N D.s2_fix_x a1 a2

theorem inv_conj_x {n : G} (hn : n ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hx : (xel v1 v2 v3)⁻¹ * (n * xel v1 v2 v3 * n⁻¹) ∈ alpW v1 v2 v3) :
    (xel v1 v2 v3)⁻¹ * (n⁻¹ * xel v1 v2 v3 * n) ∈ alpW v1 v2 v3 := by
  have e : (xel v1 v2 v3)⁻¹ * (n⁻¹ * xel v1 v2 v3 * n) =
      (n⁻¹ * ((xel v1 v2 v3)⁻¹ * (n * xel v1 v2 v3 * n⁻¹)) * n)⁻¹ := by group
  rw [e]
  exact inv_mem (D.conj_inv_mem_W hn hx)

theorem conj_inv_mem_XW {n y : G} (hn : n ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hx : (xel v1 v2 v3)⁻¹ * (n * xel v1 v2 v3 * n⁻¹) ∈ alpW v1 v2 v3) (hy : y ∈ D.XW) :
    n⁻¹ * y * n ∈ D.XW := by
  obtain ⟨hyV, hy⟩ := hy
  refine ⟨conj_inv_mem_V hn hyV, ?_⟩
  rcases hy with hy | hy
  · exact Or.inl (D.conj_inv_mem_W hn hy)
  · right
    have e : (xel v1 v2 v3)⁻¹ * (n⁻¹ * y * n) =
        ((xel v1 v2 v3)⁻¹ * (n⁻¹ * xel v1 v2 v3 * n)) * (n⁻¹ * ((xel v1 v2 v3)⁻¹ * y) * n) := by
      group
    rw [e]
    exact mul_mem (D.inv_conj_x hn hx) (D.conj_inv_mem_W hn hy)

theorem conj_x_of_normalizer {n : G} (hn : n ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hx : (xel v1 v2 v3)⁻¹ * (n * xel v1 v2 v3 * n⁻¹) ∈ alpW v1 v2 v3) :
    n * xel v1 v2 v3 * n⁻¹ = xel v1 v2 v3 ∨ n * xel v1 v2 v3 * n⁻¹ = (xel v1 v2 v3)⁻¹ := by
  set x := xel v1 v2 v3 with hxdef
  set y := n * x * n⁻¹ with hy
  have hq : ∀ q : G, q ∈ normalizer (alpV v1 v2 v3 : Set G) → q * x * q⁻¹ = x →
      (∀ v ∈ ({v1, v2, v3} : Set G), v⁻¹ * (q * v * q⁻¹) ∈ D.XW) → q * y * q⁻¹ = y := by
    intro q hqN hqx hpat
    set k := n⁻¹ * q * n with hk
    have hkN : k ∈ normalizer (alpV v1 v2 v3 : Set G) := mul_mem (mul_mem (inv_mem hn) hqN) hn
    have hf : ∀ v ∈ alpV v1 v2 v3, v⁻¹ * (k * v * k⁻¹) ∈ D.XW := by
      intro v hv
      have h1 := D.f_mem_of_gens hqN D.XW hpat _ (conj_mem_V hn hv)
      have e : v⁻¹ * (k * v * k⁻¹) =
          n⁻¹ * ((n * v * n⁻¹)⁻¹ * (q * (n * v * n⁻¹) * q⁻¹)) * n := by
        rw [hk]
        group
      rw [e]
      exact D.conj_inv_mem_XW hn hx h1
    have hkx : x⁻¹ * (k * x * k⁻¹) ∈ alpW v1 v2 v3 := by
      set w0 := x⁻¹ * (n * x * n⁻¹) with hw0
      have hqw : q * w0 * q⁻¹ ∈ alpW v1 v2 v3 := D.conj_mem_W hqN hx
      have e1 : n * x * n⁻¹ = x * w0 := by rw [hw0]; group
      have e : x⁻¹ * (k * x * k⁻¹) = (x⁻¹ * (n⁻¹ * x * n)) * (n⁻¹ * (q * w0 * q⁻¹) * n) := by
        calc x⁻¹ * (k * x * k⁻¹) = x⁻¹ * (n⁻¹ * (q * (n * x * n⁻¹) * q⁻¹) * n) := by
              rw [hk]; group
          _ = x⁻¹ * (n⁻¹ * (q * (x * w0) * q⁻¹) * n) := by rw [e1]
          _ = x⁻¹ * (n⁻¹ * ((q * x * q⁻¹) * (q * w0 * q⁻¹)) * n) := by group
          _ = x⁻¹ * (n⁻¹ * (x * (q * w0 * q⁻¹)) * n) := by rw [hqx]
          _ = (x⁻¹ * (n⁻¹ * x * n)) * (n⁻¹ * (q * w0 * q⁻¹) * n) := by group
      rw [e]
      exact mul_mem (D.inv_conj_x hn hx) (D.conj_inv_mem_W hn hqw)
    have hfix := D.fix_x_of_pattern hkN hkx (hf v1 (subset_closure (by simp)))
      (hf v2 (subset_closure (by simp)))
    calc q * y * q⁻¹ = n * (k * x * k⁻¹) * n⁻¹ := by rw [hy, hk]; group
      _ = n * x * n⁻¹ := by rw [hfix]
  have hs := hq (s ^ 2) D.s2_mem_N D.s2_fix_x D.pat_s2_XW
  have ht := hq t D.t_mem_N D.t_fix_x D.pat_t_XW
  have hyV : y ∈ alpV v1 v2 v3 := conj_mem_V hn D.x_mem_V
  rw [AlpEmb.alpV_eq_map D.E] at hyV
  obtain ⟨y', -, hy'⟩ := Subgroup.mem_map.1 hyV
  have h1 : InWE (xE⁻¹ * y') := by
    rw [← D.mem_W_phi, map_mul, map_inv, ← D.x_eq, hy']
    exact hx
  have h2 : s2E * y' = y' * s2E := by
    apply D.E.inj
    rw [map_mul, map_mul, D.phi_s2, hy']
    calc s ^ 2 * y = (s ^ 2 * y * (s ^ 2)⁻¹) * s ^ 2 := by group
      _ = y * s ^ 2 := by rw [hs]
  have h3 : tE * y' = y' * tE := by
    apply D.E.inj
    rw [map_mul, map_mul, D.phi_t, hy']
    calc t * y = (t * y * t⁻¹) * t := by group
      _ = y * t := by rw [ht]
  rcases fix_xW_E y' h1 h2 h3 with h | h
  · left
    rw [← hy', h, ← D.x_eq]
  · right
    rw [← hy', h, map_inv, ← D.x_eq]

theorem conj_x_of_mem {g : G}
    (hg : (xel v1 v2 v3)⁻¹ * (g * xel v1 v2 v3 * g⁻¹) ∈ alpW v1 v2 v3) :
    g * xel v1 v2 v3 * g⁻¹ = xel v1 v2 v3 ∨ g * xel v1 v2 v3 * g⁻¹ = (xel v1 v2 v3)⁻¹ := by
  set x := xel v1 v2 v3 with hxdef
  have hxV := D.x_mem_V
  have hyV : g * x * g⁻¹ ∈ alpV v1 v2 v3 := by
    have e : g * x * g⁻¹ = x * (x⁻¹ * (g * x * g⁻¹)) := by group
    rw [e]
    exact mul_mem hxV (D.W_le_V hg)
  obtain ⟨n, hn, hnx⟩ := D.fuse_V (D.V_le_centralizer_V hxV) (D.V_le_centralizer_V hyV) ⟨g, rfl⟩
  have e : n⁻¹ * x * n⁻¹⁻¹ = g * x * g⁻¹ := by rw [inv_inv, hnx]
  rw [← e]
  rw [← e] at hg
  exact D.conj_x_of_normalizer (inv_mem hn) hg

end FusCtx

end CFSG.OddStandard.ONanRec
