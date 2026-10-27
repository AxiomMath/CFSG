module

public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def IsCentralIn (P : Subgroup G) (u : G) : Prop :=
  u ∈ P ∧ ∀ b ∈ P, u * b = b * u

private def u_Z2 (T : Subgroup G) (p : G) : Prop :=
  p ∈ T ∧ ∀ t ∈ T, IsCentralIn T ⁅p, t⁆

private lemma u_commutator_mem_of_mem {H : Subgroup G} {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

private lemma u_centralIn_one (T : Subgroup G) : IsCentralIn T (1 : G) :=
  ⟨T.one_mem, fun b _ => by simp⟩

private lemma u_isCentralIn_of_commutes {T D Q : Subgroup G} {x : G}
    (hDT : D ≤ T) (hT : ∀ t ∈ T, ∃ d ∈ D, ∃ q ∈ Q, t = d * q)
    (hDQ : ∀ d ∈ D, ∀ q ∈ Q, d * q = q * d) (hxD : ∀ d ∈ D, d * x = x * d)
    (hxD_mem : x ∈ D) : IsCentralIn T x := by
  refine ⟨hDT hxD_mem, fun t ht => ?_⟩
  obtain ⟨d, hd, q, hq, rfl⟩ := hT t ht
  calc x * (d * q) = (x * d) * q := (mul_assoc x d q).symm
    _ = (d * x) * q := by rw [hxD d hd]
    _ = d * (x * q) := mul_assoc d x q
    _ = d * (q * x) := by rw [hDQ x hxD_mem q hq]
    _ = (d * q) * x := (mul_assoc d q x).symm

private lemma u_Z2_of_mem_D {T D Q : Subgroup G} {a x : G}
    (hDT : D ≤ T) (hT : ∀ t ∈ T, ∃ d ∈ D, ∃ q ∈ Q, t = d * q)
    (hDQ : ∀ d ∈ D, ∀ q ∈ Q, d * q = q * d) (ha : a ∈ D)
    (hD2 : ∀ d₁ ∈ D, ∀ d₂ ∈ D, ⁅d₁, d₂⁆ = 1 ∨ ⁅d₁, d₂⁆ = x)
    (hxcent : IsCentralIn T x) : u_Z2 T a := by
  refine ⟨hDT ha, fun t ht => ?_⟩
  obtain ⟨d, hd, q, hq, rfl⟩ := hT t ht
  have hcalc : ⁅a, d * q⁆ = ⁅a, d⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_mul_comm.mpr (hDQ a ha q hq), mul_one,
      mul_inv_cancel_right]
  rw [hcalc]
  rcases hD2 a ha d hd with h | h
  · rw [h]; exact u_centralIn_one T
  · rw [h]; exact hxcent

private lemma u_Z2_conj {T : Subgroup G} {p n : G} (hn : n ∈ normalizer (T : Set G))
    (hp : u_Z2 T p) : u_Z2 T (n * p * n⁻¹) := by
  obtain ⟨hpT, hpcent⟩ := hp
  have hn_mem : ∀ h, h ∈ T ↔ n * h * n⁻¹ ∈ T :=
    (Subgroup.mem_set_normalizer_iff).mp hn
  have hn_mem' : ∀ h, h ∈ T ↔ n⁻¹ * h * n ∈ T :=
    (Subgroup.mem_set_normalizer_iff'').mp hn
  refine ⟨(hn_mem p).mp hpT, fun t ht => ?_⟩
  have hntn : n⁻¹ * t * n ∈ T := (hn_mem' t).mp ht
  obtain ⟨hpcT, hpc_comm⟩ := hpcent (n⁻¹ * t * n) hntn
  have hconj : ⁅n * p * n⁻¹, t⁆ = n * ⁅p, n⁻¹ * t * n⁆ * n⁻¹ := by
    simp only [commutatorElement_def]
    group
  refine ⟨?_, fun u hu => ?_⟩
  · rw [hconj]
    exact (hn_mem _).mp hpcT
  · rw [hconj]
    have hcu : ⁅p, n⁻¹ * t * n⁆ * (n⁻¹ * u * n) = (n⁻¹ * u * n) * ⁅p, n⁻¹ * t * n⁆ :=
      hpc_comm _ ((hn_mem' u).mp hu)
    calc n * ⁅p, n⁻¹ * t * n⁆ * n⁻¹ * u
        = n * (⁅p, n⁻¹ * t * n⁆ * (n⁻¹ * u * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * u * n) * ⁅p, n⁻¹ * t * n⁆) * n⁻¹ := by rw [hcu]
      _ = u * (n * ⁅p, n⁻¹ * t * n⁆ * n⁻¹) := by group

private lemma u_commutator_mul_eq {d₁ q₁ d₂ q₂ : G}
    (h1 : q₁ * d₂ = d₂ * q₁) (h2 : d₁ * q₂ = q₂ * d₁) (h3 : q₁ * q₂ = q₂ * q₁) :
    ⁅d₁ * q₁, d₂ * q₂⁆ = ⁅d₁, d₂⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hA : ⁅q₁, d₂ * q₂⁆ = 1 := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_mul_comm.mpr h1,
      commutatorElement_eq_one_iff_mul_comm.mpr h3]
    group
  have hB : ⁅d₁, d₂ * q₂⁆ = ⁅d₁, d₂⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_mul_comm.mpr h2, mul_one, mul_inv_cancel_right]
  rw [hA, hB]
  group

private lemma u_Z2_commutator_eq {T D Q : Subgroup G} {x : G}
    (hQT : Q ≤ T) (hT : ∀ t ∈ T, ∃ d ∈ D, ∃ q ∈ Q, t = d * q)
    (hDQ : ∀ d ∈ D, ∀ q ∈ Q, d * q = q * d)
    (hD2 : ∀ d₁ ∈ D, ∀ d₂ ∈ D, ⁅d₁, d₂⁆ = 1 ∨ ⁅d₁, d₂⁆ = x)
    (hQ : ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, (∀ q ∈ Q, IsCentralIn Q ⁅q₁, q⁆) →
      (∀ q ∈ Q, IsCentralIn Q ⁅q₂, q⁆) → q₁ * q₂ = q₂ * q₁)
    {s₁ s₂ : G} (hs₁ : u_Z2 T s₁) (hs₂ : u_Z2 T s₂) :
    ⁅s₁, s₂⁆ = 1 ∨ ⁅s₁, s₂⁆ = x := by
  obtain ⟨hs₁T, hs₁c⟩ := hs₁
  obtain ⟨hs₂T, hs₂c⟩ := hs₂
  obtain ⟨d₁, hd₁, q₁, hq₁, rfl⟩ := hT s₁ hs₁T
  obtain ⟨d₂, hd₂, q₂, hq₂, rfl⟩ := hT s₂ hs₂T
  have hq1_cent : ∀ q ∈ Q, IsCentralIn Q ⁅q₁, q⁆ := by
    intro q hq
    have hq1q_mem : ⁅q₁, q⁆ ∈ Q := u_commutator_mem_of_mem hq₁ hq
    have h_eq : ⁅d₁ * q₁, q⁆ = ⁅q₁, q⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul,
        commutatorElement_eq_one_iff_mul_comm.mpr (hDQ d₁ hd₁ q hq), mul_one,
        hDQ d₁ hd₁ ⁅q₁, q⁆ hq1q_mem]
      group
    refine ⟨hq1q_mem, fun q' hq' => ?_⟩
    have hc := (hs₁c q (hQT hq)).2 q' (hQT hq')
    simpa only [h_eq] using hc
  have hq2_cent : ∀ q ∈ Q, IsCentralIn Q ⁅q₂, q⁆ := by
    intro q hq
    have hq2q_mem : ⁅q₂, q⁆ ∈ Q := u_commutator_mem_of_mem hq₂ hq
    have h_eq : ⁅d₂ * q₂, q⁆ = ⁅q₂, q⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul,
        commutatorElement_eq_one_iff_mul_comm.mpr (hDQ d₂ hd₂ q hq), mul_one,
        hDQ d₂ hd₂ ⁅q₂, q⁆ hq2q_mem]
      group
    refine ⟨hq2q_mem, fun q' hq' => ?_⟩
    have hc := (hs₂c q (hQT hq)).2 q' (hQT hq')
    simpa only [h_eq] using hc
  have hq12 : q₁ * q₂ = q₂ * q₁ := hQ q₁ hq₁ q₂ hq₂ hq1_cent hq2_cent
  rw [u_commutator_mul_eq (hDQ d₂ hd₂ q₁ hq₁).symm (hDQ d₁ hd₁ q₂ hq₂) hq12]
  exact hD2 d₁ hd₁ d₂ hd₂

theorem conj_eq_of_mem_normalizer {T D Q : Subgroup G} {a b x : G}
    (hDT : D ≤ T) (hQT : Q ≤ T) (hT : ∀ t ∈ T, ∃ d ∈ D, ∃ q ∈ Q, t = d * q)
    (hDQ : ∀ d ∈ D, ∀ q ∈ Q, d * q = q * d) (ha : a ∈ D) (hb : b ∈ D) (hab : ⁅a, b⁆ = x)
    (hx : x ≠ 1) (hD2 : ∀ d₁ ∈ D, ∀ d₂ ∈ D, ⁅d₁, d₂⁆ = 1 ∨ ⁅d₁, d₂⁆ = x)
    (hxD : ∀ d ∈ D, d * x = x * d)
    (hQ : ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, (∀ q ∈ Q, IsCentralIn Q ⁅q₁, q⁆) →
      (∀ q ∈ Q, IsCentralIn Q ⁅q₂, q⁆) → q₁ * q₂ = q₂ * q₁)
    {n : G} (hn : n ∈ normalizer (T : Set G)) : n * x * n⁻¹ = x := by
  have hxD_mem : x ∈ D := hab ▸ u_commutator_mem_of_mem ha hb
  have hxcent : IsCentralIn T x := u_isCentralIn_of_commutes hDT hT hDQ hxD hxD_mem
  have haS : u_Z2 T a := u_Z2_of_mem_D hDT hT hDQ ha hD2 hxcent
  have hbS : u_Z2 T b := u_Z2_of_mem_D hDT hT hDQ hb hD2 hxcent
  have hnaS : u_Z2 T (n * a * n⁻¹) := u_Z2_conj hn haS
  have hnbS : u_Z2 T (n * b * n⁻¹) := u_Z2_conj hn hbS
  have hcomm := u_Z2_commutator_eq hQT hT hDQ hD2 hQ hnaS hnbS
  have hkey : n * x * n⁻¹ = ⁅n * a * n⁻¹, n * b * n⁻¹⁆ := by
    rw [← conjugate_commutatorElement (g₃ := n) (g₁ := a) (g₂ := b), hab]
  have hcases : n * x * n⁻¹ = 1 ∨ n * x * n⁻¹ = x := by
    rw [hkey]
    exact hcomm
  rcases hcases with h | h
  · exfalso
    have hx1 : x = 1 := by
      calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
        _ = n⁻¹ * 1 * n := by rw [h]
        _ = 1 := by group
    exact hx hx1
  · exact h

theorem normalizer_le_centralizer {T D Q : Subgroup G} {a b x : G}
    (hDT : D ≤ T) (hQT : Q ≤ T) (hT : ∀ t ∈ T, ∃ d ∈ D, ∃ q ∈ Q, t = d * q)
    (hDQ : ∀ d ∈ D, ∀ q ∈ Q, d * q = q * d) (ha : a ∈ D) (hb : b ∈ D) (hab : ⁅a, b⁆ = x)
    (hx : x ≠ 1) (hD2 : ∀ d₁ ∈ D, ∀ d₂ ∈ D, ⁅d₁, d₂⁆ = 1 ∨ ⁅d₁, d₂⁆ = x)
    (hxD : ∀ d ∈ D, d * x = x * d)
    (hQ : ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, (∀ q ∈ Q, IsCentralIn Q ⁅q₁, q⁆) →
      (∀ q ∈ Q, IsCentralIn Q ⁅q₂, q⁆) → q₁ * q₂ = q₂ * q₁) :
    normalizer (T : Set G) ≤ centralizer ({x} : Set G) := by
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := conj_eq_of_mem_normalizer hDT hQT hT hDQ ha hb hab hx hD2 hxD hQ hn
  calc n * x = n * x * n⁻¹ * n := by group
    _ = x * n := by rw [h]

end CFSG.OddStandard.AltStdSec.SwapPartner
