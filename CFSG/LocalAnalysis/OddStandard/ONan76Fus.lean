module

public import CFSG.LocalAnalysis.OddStandard.ONan76Loc
public import CFSG.LocalAnalysis.OddStandard.ONan76Ext
import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.ONan76

open Subgroup CFSG.ABGLocalTools

section Conj

variable {G : Type*} [Group G] [Finite G]

theorem conj_inv_mem_of_conj_mem {A : Subgroup G} {g : G} (h : ∀ a ∈ A, g * a * g⁻¹ ∈ A) :
    ∀ a ∈ A, g⁻¹ * a * g ∈ A := by
  have hN := mem_normalizer_of_conj_mem h
  intro a ha
  have := (mem_normalizer_iff.1 (inv_mem hN) a).1 ha
  rwa [inv_inv] at this

omit [Finite G] in
theorem map_conj_centralizer (x a : G) :
    (centralizer ({a} : Set G)).map (MulAut.conj x).toMonoidHom =
      centralizer ({x * a * x⁻¹} : Set G) := by
  ext y
  rw [mem_map_conj, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc y * (x * a * x⁻¹) = x * (x⁻¹ * y * x * a) * x⁻¹ := by group
      _ = x * (a * (x⁻¹ * y * x)) * x⁻¹ := by rw [h]
      _ = x * a * x⁻¹ * y := by group
  · intro h
    calc x⁻¹ * y * x * a = x⁻¹ * (y * (x * a * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * a * x⁻¹ * y) * x := by rw [h]
      _ = a * (x⁻¹ * y * x) := by group

theorem isSylowOf_top (P : Sylow 2 G) : IsSylowOf 2 (P : Subgroup G) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_of_card le_top ?_
  rw [Sylow.card_eq_multiplicity, card_top]

end Conj

namespace AlperinFrame

variable {G : Type*} [Group G] [Finite G] {n : ℕ} {v₁ v₂ v₃ s t : G}
  (hF : AlperinFrame n v₁ v₂ v₃ s t)

include hF

theorem V_isPGroup (hPs : IsSylowOf 2 hF.P ⊤) : IsPGroup 2 hF.V :=
  hPs.isPGroup.to_le hF.V_le_P

omit [Finite G] in
theorem pow_two_pow_eq_one (hn : 1 ≤ n) {v : G} (hv : v ∈ hF.V) : v ^ 2 ^ n = 1 := by
  obtain ⟨p, rfl⟩ := hF.exists_vec_of_mem_V hn hv
  have h0 : (2 : ZMod (2 ^ n)) ^ n = 0 := by exact_mod_cast ZMod.natCast_self (2 ^ n)
  rw [← hF.vec_nsmul]
  convert hF.vec_zero
  ext <;> simp [nsmul_eq_mul, h0]

omit [Finite G] in
theorem mul_self_pow_pred (hn : 1 ≤ n) {v : G} (hv : v ∈ hF.V) :
    v ^ 2 ^ (n - 1) * v ^ 2 ^ (n - 1) = 1 := by
  rw [← pow_add, ← two_mul, ← pow_succ', show n - 1 + 1 = n by omega]
  exact hF.pow_two_pow_eq_one hn hv

theorem exists_normalizer_conj (hn : 3 ≤ n) (hPs : IsSylowOf 2 hF.P ⊤) {a g : G}
    (ha : a ∈ hF.V) (hga : g * a * g⁻¹ ∈ hF.V) :
    ∃ m : G, (∀ v ∈ hF.V, m * v * m⁻¹ ∈ hF.V) ∧ m * a * m⁻¹ = g * a * g⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by omega
  set a' := g * a * g⁻¹ with ha'
  set C := centralizer ({a'} : Set G) with hC
  have hVC : hF.V ≤ C := fun v hv => mem_centralizer_singleton_iff.2 (hF.V_comm hn1 hv hga)
  have hgVC : hF.V.map (MulAut.conj g).toMonoidHom ≤ C := by
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_centralizer_singleton_iff]
    show g * v * g⁻¹ * (g * a * g⁻¹) = g * a * g⁻¹ * (g * v * g⁻¹)
    rw [show g * v * g⁻¹ * (g * a * g⁻¹) = g * (v * a) * g⁻¹ by group, hF.V_comm hn1 hv ha]
    group
  have hV2 := hF.V_isPGroup hPs
  obtain ⟨Q, hQ, hVQ⟩ := exists_isSylowOf_ge hVC hV2
  obtain ⟨c, hcC, hc⟩ := exists_conj_le hQ hgVC (hV2.map _)
  obtain ⟨y, -, hy⟩ := exists_conj_le hPs le_top hQ.isPGroup
  have hyV : ∀ v ∈ hF.V, y * v * y⁻¹ ∈ hF.V := hF.weakly_closed hn fun v hv => hy v (hVQ hv)
  have hycg : ∀ v ∈ hF.V, y * c * g * v * (y * c * g)⁻¹ ∈ hF.V :=
    hF.weakly_closed hn fun v hv => by
      have := hy _ (hc _ ⟨v, hv, rfl⟩)
      rwa [show y * (c * (MulAut.conj g).toMonoidHom v * c⁻¹) * y⁻¹ =
        y * c * g * v * (y * c * g)⁻¹ by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group] at this
  refine ⟨c * g, fun v hv => ?_, ?_⟩
  · have h1 := conj_inv_mem_of_conj_mem hyV _ (hycg v hv)
    rwa [show y⁻¹ * (y * c * g * v * (y * c * g)⁻¹) * y = c * g * v * (c * g)⁻¹ by group] at h1
  · have hcw : c * a' = a' * c := mem_centralizer_singleton_iff.1 hcC
    calc c * g * a * (c * g)⁻¹ = c * a' * c⁻¹ := by rw [ha']; group
      _ = a' := by rw [hcw, mul_inv_cancel_right]

theorem exists_extremal (hn : 3 ≤ n) (hPs : IsSylowOf 2 hF.P ⊤) {a : G} (ha : a ∈ hF.V) :
    ∃ x : G, (∀ v ∈ hF.V, x * v * x⁻¹ ∈ hF.V) ∧
      IsSylowOf 2 (hF.P ⊓ centralizer ({x * a * x⁻¹} : Set G))
        (centralizer ({x * a * x⁻¹} : Set G)) ∧
      ∀ c ∈ hF.P ⊓ centralizer ({a} : Set G),
        x * c * x⁻¹ ∈ hF.P ⊓ centralizer ({x * a * x⁻¹} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by omega
  set C := centralizer ({a} : Set G) with hC
  obtain ⟨Q, hQ, hle⟩ := exists_isSylowOf_ge (inf_le_right : hF.P ⊓ C ≤ C)
    (hPs.isPGroup.to_le inf_le_left)
  obtain ⟨x, -, hx⟩ := exists_conj_le hPs le_top hQ.isPGroup
  have hVPC : hF.V ≤ hF.P ⊓ C := fun v hv =>
    mem_inf.2 ⟨hF.V_le_P hv, mem_centralizer_singleton_iff.2 (hF.V_comm hn1 hv ha)⟩
  have hxV : ∀ v ∈ hF.V, x * v * x⁻¹ ∈ hF.V :=
    hF.weakly_closed hn fun v hv => hx v (hle (hVPC hv))
  have hQ' := isSylowOf_map_conj hQ x
  rw [map_conj_centralizer] at hQ'
  have hle' : Q.map (MulAut.conj x).toMonoidHom ≤
      hF.P ⊓ centralizer ({x * a * x⁻¹} : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    refine mem_inf.2 ⟨hx q hq, ?_⟩
    rw [← map_conj_centralizer]
    exact ⟨q, hQ.le hq, rfl⟩
  have heq := hQ'.eq_of_le hle' inf_le_right (hPs.isPGroup.to_le inf_le_left)
  refine ⟨x, hxV, ?_, fun c hc => ?_⟩
  · rw [heq]
    exact hQ'
  · rw [heq]
    exact ⟨c, hle hc, rfl⟩

theorem exists_conj_P (hn : 3 ≤ n) (hPs : IsSylowOf 2 hF.P ⊤) {j g : G}
    (hgj : g * j * g⁻¹ ∈ hF.V) :
    ∃ g' : G, g' * j * g'⁻¹ ∈ hF.V ∧ ∀ u ∈ hF.V, u * j = j * u → g' * u * g'⁻¹ ∈ hF.P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by omega
  set w := g * j * g⁻¹ with hw
  set C := centralizer ({w} : Set G) with hC
  set U := hF.V ⊓ centralizer ({j} : Set G) with hU
  have hVC : hF.V ≤ C := fun v hv => mem_centralizer_singleton_iff.2 (hF.V_comm hn1 hv hgj)
  have hUC : U.map (MulAut.conj g).toMonoidHom ≤ C := by
    rintro _ ⟨u, hu, rfl⟩
    have huj : u * j = j * u := mem_centralizer_singleton_iff.1 (mem_inf.1 hu).2
    rw [mem_centralizer_singleton_iff]
    show g * u * g⁻¹ * (g * j * g⁻¹) = g * j * g⁻¹ * (g * u * g⁻¹)
    rw [show g * u * g⁻¹ * (g * j * g⁻¹) = g * (u * j) * g⁻¹ by group, huj]
    group
  have hV2 := hF.V_isPGroup hPs
  obtain ⟨Q, hQ, hVQ⟩ := exists_isSylowOf_ge hVC hV2
  obtain ⟨c, hcC, hc⟩ := exists_conj_le hQ hUC ((hV2.to_le inf_le_left).map _)
  obtain ⟨d, -, hd⟩ := exists_conj_le hPs le_top hQ.isPGroup
  have hdV : ∀ v ∈ hF.V, d * v * d⁻¹ ∈ hF.V := hF.weakly_closed hn fun v hv => hd v (hVQ hv)
  have hcw : c * w = w * c := mem_centralizer_singleton_iff.1 hcC
  refine ⟨d * c * g, ?_, fun u hu huj => ?_⟩
  · rw [show d * c * g * j * (d * c * g)⁻¹ = d * (c * w * c⁻¹) * d⁻¹ by rw [hw]; group, hcw,
      mul_inv_cancel_right]
    exact hdV w hgj
  · have h1 := hd _ (hc _ ⟨u, mem_inf.2 ⟨hu, mem_centralizer_singleton_iff.2 huj⟩, rfl⟩)
    rwa [show d * (c * (MulAut.conj g).toMonoidHom u * c⁻¹) * d⁻¹ =
      d * c * g * u * (d * c * g)⁻¹ by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group] at h1

end AlperinFrame

end CFSG.OddStandard.ONan76
