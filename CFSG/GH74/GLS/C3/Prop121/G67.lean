module

public import CFSG.GH74.GLS.C3.Prop121.Coord
public import CFSG.GH74.GLS.C3.Prop121.FinPos
public import CFSG.GH74.GLS.C3.Layer2.ModelBridge
public import CFSG.GH74.GLS.C3.Layer2.Terminal

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

section Coordinatized

variable {G : Type} [Group G] [Finite G] {n : ℕ} [NeZero n] {x : G} {K T Q S : Subgroup G}
  {a : G} {h : IsAConfig n x K T Q S a}

theorem alpha_snd_eq_one
    (c : Coord h) (hn : n = 6 ∨ n = 7)
    (hW2 : ∀ q ∈ Q, q ≠ 1 → (Nat.card ↥(centralizer ({q} : Set G))).factorization 2 ≤
      (Nat.card ↥(centralizer ({x} : Set G))).factorization 2) :
    ∀ q : ↥(T0 n), (q : Amb n).1 = 1 → ((c.alpha q : ↥(T0 n)) : Amb n).2 = 1 :=
  fin_pos n hn c.alpha c.uElt c.XSet c.VSet c.alpha_x0T_ne c.alpha_uElt c.alpha_alpha
    (fun _ => c.hext) c.x0T_mem_XSet c.x0T_mul_alpha_mem_VSet (c.disjoint_XV hn)
    (fun s t _ hst hs => (c.isConj_of_model s t hst).symm.trans hs)
    (fun s t _ hst hs => (c.isConj_of_model s t hst).symm.trans hs) (c.hQ_model hn hW2)

end Coordinatized

variable {G : Type} [Group G] [Finite G]

theorem exists_g_six_seven
    (hG : pRank 2 G ≤ 4) {n : ℕ} (hn : n = 6 ∨ n = 7)
    {x : G} {K T Q S : Subgroup G} {a : G} (h : IsAConfig n x K T Q S a) :
    ∃ g : G, g ^ 2 = 1 ∧ ∀ q ∈ Q, g * q * g⁻¹ ∈ K := by
  have hn' : NeZero n := ⟨by rcases hn with rfl | rfl <;> norm_num⟩
  have hn3 : n = 5 ∨ n = 6 ∨ n = 7 := by omega
  have hG4 : pRank 2 G ≤ 4 := hG
  have hnt := h.exists_noncomm hn hG4
  obtain ⟨ι, hι1, hιQ, hιT⟩ := h.exists_equiv_Fgrp_T0 hn hnt
  let c : Coord h := ⟨ι, hι1, hιQ, hιT⟩
  have hW2 : ∀ q ∈ Q, q ≠ 1 →
      (Nat.card ↥(centralizer ({q} : Set G))).factorization 2 ≤
        (Nat.card ↥(centralizer ({x} : Set G))).factorization 2 := fun q hq hq1 =>
    h.factorization_centralizer_le (by rcases hn with rfl | rfl <;> norm_num) hG4 hnt q hq hq1
  obtain ⟨φ, a₀, s, -, hsum, -⟩ := (c.modelIso hn hW2).data
  have hpos := alpha_snd_eq_one c hn hW2
  obtain ⟨t₀, rfl⟩ := c.tau.surjective s
  have hgsq : ((t₀ : G) * a) ^ 2 = 1 := by
    have h1 : (t₀ * conjAutT h.a_mem.2.1 t₀ * ⟨a ^ 2, h.a_mem.2.2.2⟩ : ↥T) = 1 := by
      apply c.tau.injective
      rw [map_mul, map_mul, map_one, ← c.alpha_tau t₀]
      exact hsum
    have h3 : (t₀ : G) * (a * t₀ * a⁻¹) * a ^ 2 = 1 := congrArg Subtype.val h1
    calc ((t₀ : G) * a) ^ 2 = (t₀ : G) * (a * t₀ * a⁻¹) * a ^ 2 := by rw [sq, sq]; group
      _ = 1 := h3
  refine ⟨(t₀ : G) * a, hgsq, fun q hq => ?_⟩
  have hqT : q ∈ T := h.Q_le_T hq
  have hyT : a * q * a⁻¹ ∈ T := (mem_normalizer_iff.1 h.a_mem.2.1 q).1 hqT
  have hyC : a * q * a⁻¹ ∈ centralizer ({x} : Set G) := h.T_le_C hyT
  have hq1 : ((c.tau ⟨q, hqT⟩ : ↥(T0 n)) : Amb n).1 = 1 := (hιQ ⟨q, h.T_le_C hqT⟩).2 hq
  have hy2 : ((c.tau (conjAutT h.a_mem.2.1 ⟨q, hqT⟩) : ↥(T0 n)) : Amb n).2 = 1 := by
    rw [← c.alpha_tau]
    exact hpos _ hq1
  have hy3 : ((ι ⟨a * q * a⁻¹, hyC⟩ : ↥(Fgrp n)) : Amb n).2 = 1 := hy2
  have hyK : a * q * a⁻¹ ∈ K := by
    refine (K_iff hn3 h hιQ ⟨a * q * a⁻¹, hyC⟩).2 ⟨?_, hy3⟩
    have h1 : Equiv.Perm.sign ((ι ⟨a * q * a⁻¹, hyC⟩ : ↥(Fgrp n)) : Amb n).1 =
        Equiv.Perm.sign ((ι ⟨a * q * a⁻¹, hyC⟩ : ↥(Fgrp n)) : Amb n).2 := (ι ⟨a * q * a⁻¹, hyC⟩).2.2
    rw [h1, hy3, map_one]
  have hconj := h.normalInC (t₀ : G) (h.T_le_C t₀.2) _ hyK
  have e : (t₀ : G) * a * q * ((t₀ : G) * a)⁻¹ = (t₀ : G) * (a * q * a⁻¹) * (t₀ : G)⁻¹ := by
    group
  rw [e]
  exact hconj

end CFSG.GH74.GLS.C3.Prop121
