module

public import CFSG.GH74.GLS.C3.Prop121.Interfaces
public import CFSG.GH74.GLS.C3.Layer2.FinModelCard
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2.Model

namespace FnAux

def Bgrp (d : Perm (Fin 4)) : Subgroup (Perm (Fin 4)) :=
  Subgroup.centralizer ({x4} : Set (Perm (Fin 4))) ⊓ Subgroup.centralizer ({d} : Set (Perm (Fin 4)))

theorem F1 : ∀ d : Perm (Fin 4), d * x4 = x4 * d →
    ((∀ e : Perm (Fin 4), e * x4 = x4 * e → sign e = 1 → d * e = e * d) ↔ sign d = 1) := by
  decide

theorem F3 : ∀ d : Perm (Fin 4), d * x4 = x4 * d → d ≠ 1 → d ≠ x4 →
    (Finset.univ.filter (fun g : Perm (Fin 4) => g * x4 = x4 * g ∧ g * d = d * g)).card = 4 := by
  decide

theorem card_Bgrp_of_ne {d : Perm (Fin 4)} (hd : d * x4 = x4 * d) (h1 : d ≠ 1) (h2 : d ≠ x4) :
    Nat.card (Bgrp d) = 4 := by
  have e : ↥(Bgrp d) ≃ {g : Perm (Fin 4) // g * x4 = x4 * g ∧ g * d = d * g} :=
    Equiv.subtypeEquivRight (fun g => by
      simp [Bgrp, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact F3 d hd h1 h2

theorem card_Bgrp_one : Nat.card (Bgrp 1) = 8 := by
  have : Bgrp 1 = Subgroup.centralizer ({x4} : Set (Perm (Fin 4))) := by
    ext g
    simp [Bgrp, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  rw [this, card_centralizer_x4]

theorem card_Bgrp_x4 : Nat.card (Bgrp x4) = 8 := by
  have : Bgrp x4 = Subgroup.centralizer ({x4} : Set (Perm (Fin 4))) := inf_idem _
  rw [this, card_centralizer_x4]

theorem card_Hgrp_one {n : ℕ} (hn : 2 ≤ n) (d : Perm (Fin 4)) :
    Nat.card (Hgrp n ((1 : Perm (Fin n)), d)) * 2 = n.factorial * Nat.card (Bgrp d) := by
  classical
  let ψ : Perm (Fin n) × Bgrp d →* ℤˣ :=
    (sign.comp (MonoidHom.fst _ _)) * (sign.comp ((Bgrp d).subtype.comp (MonoidHom.snd _ _)))
  have hψ : ∀ p, ψ p = sign p.1 * sign (p.2 : Perm (Fin 4)) := fun p => rfl
  have hrange : ψ.range = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rcases Int.units_eq_one_or z with rfl | rfl
    · exact ψ.range.one_mem
    · refine ⟨(swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩, 1), ?_⟩
      rw [hψ]
      simp [sign_swap (show (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ by simp [Fin.ext_iff])]
  have h1 : Nat.card ψ.ker * ψ.ker.index = Nat.card (Perm (Fin n) × Bgrp d) :=
    Subgroup.card_mul_index ψ.ker
  have h2 : ψ.ker.index = 2 := by
    rw [Subgroup.index_ker, hrange]
    simp [Nat.card_eq_fintype_card]
  have h3 : Nat.card (Perm (Fin n) × Bgrp d) = n.factorial * Nat.card (Bgrp d) := by
    rw [Nat.card_prod, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
  have h4 : Nat.card (Hgrp n ((1 : Perm (Fin n)), d)) = Nat.card ψ.ker := by
    refine Nat.card_congr ?_
    have key : ∀ (a : ℤˣ) (b : ℤˣ), a = b ↔ a * b = 1 := by
      intro a b
      rcases Int.units_eq_one_or a with rfl | rfl <;>
        rcases Int.units_eq_one_or b with rfl | rfl <;> decide
    refine
      { toFun := fun p => ⟨(p.1.1, ⟨p.1.2, Subgroup.mem_inf.2
            ⟨Subgroup.mem_centralizer_singleton_iff.2 p.2.1.1,
              Subgroup.mem_centralizer_singleton_iff.2
                (congrArg Prod.snd (Subgroup.mem_centralizer_singleton_iff.1 p.2.2))⟩⟩), ?_⟩
        invFun := fun q =>
          ⟨(q.1.1, (q.1.2 : Perm (Fin 4))), Subgroup.mem_inf.2
            ⟨⟨Subgroup.mem_centralizer_singleton_iff.1 q.1.2.2.1, ?_⟩,
              Subgroup.mem_centralizer_singleton_iff.2
                (Prod.ext (by simp) (Subgroup.mem_centralizer_singleton_iff.1 q.1.2.2.2))⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · rw [MonoidHom.mem_ker, hψ, ← key]
      exact p.2.1.2
    · have := q.2
      rw [MonoidHom.mem_ker, hψ, ← key] at this
      exact this
    · intro p; rfl
    · intro q; rfl
  rw [h3, h2] at h1
  rw [h4]
  exact h1

theorem card_Hgrp_le (n : ℕ) (σ : Perm (Fin n)) (d : Perm (Fin 4)) :
    Nat.card (Hgrp n (σ, d)) ≤ Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin n)))) * 8 := by
  let f : Hgrp n (σ, d) → ↥(Subgroup.centralizer ({σ} : Set (Perm (Fin n)))) ×
      ↥(Subgroup.centralizer ({x4} : Set (Perm (Fin 4)))) := fun p =>
    (⟨p.1.1, Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Prod.fst (Subgroup.mem_centralizer_singleton_iff.1 p.2.2))⟩,
     ⟨p.1.2, Subgroup.mem_centralizer_singleton_iff.2 p.2.1.1⟩)
  have hinj : Function.Injective f := by
    intro p q h
    have h1 := congrArg (fun z => (z.1 : Perm (Fin n))) h
    have h2 := congrArg (fun z => (z.2 : Perm (Fin 4))) h
    exact Subtype.ext (Prod.ext h1 h2)
  calc Nat.card (Hgrp n (σ, d))
      ≤ Nat.card (↥(Subgroup.centralizer ({σ} : Set (Perm (Fin n)))) ×
          ↥(Subgroup.centralizer ({x4} : Set (Perm (Fin 4))))) :=
        Nat.card_le_card_of_injective f hinj
    _ = _ := by rw [Nat.card_prod, card_centralizer_x4]

theorem card_centralizer_invol_lt {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7) {σ : Perm (Fin n)}
    (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin n)))) * 4 < n.factorial := by
  have hp : orderOf σ = 2 := orderOf_eq_prime (by rwa [sq]) h1
  obtain ⟨k, hk⟩ := cycleType_prime_order (σ := σ) (by rw [hp]; exact Nat.prime_two)
  rw [hp] at hk
  have hsum := sum_cycleType_le σ
  rw [hk, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  have hk2 : k ≤ 2 := by omega
  rw [nat_card_centralizer, hk, Fintype.card_fin]
  rcases hn with rfl | rfl | rfl <;> interval_cases k <;> first | (exfalso; omega) | decide

theorem card_C_q {n : ℕ} (hn : 2 ≤ n) : ∀ q : Amb n, q ∈ Fgrp n → q.1 = 1 → q ≠ 1 → q ≠ x0 n →
    Nat.card ↥(Hgrp n q) = 2 * n.factorial := by
  rintro ⟨σ, τ⟩ ⟨hτ, hs⟩ hσ hq1 hq0
  have hσ' : σ = 1 := hσ
  subst hσ'
  have hτ1 : τ ≠ 1 := fun h => hq1 (by rw [h]; rfl)
  have hτx : τ ≠ x4 := fun h => hq0 (by rw [h]; rfl)
  have hB := card_Bgrp_of_ne hτ hτ1 hτx
  have h := card_Hgrp_one hn τ
  rw [hB] at h
  omega

theorem card_C_inv {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7) :
    ∀ w : Amb n, w ∈ Fgrp n → w * w = 1 → Nat.card ↥(Hgrp n w) = 2 * n.factorial →
      w.1 = 1 ∧ w ≠ 1 ∧ w ≠ x0 n := by
  rintro ⟨σ, d⟩ ⟨hd, hs⟩ hww hcard
  have hσσ : σ * σ = 1 := congrArg Prod.fst hww
  by_cases hσ : σ = 1
  · subst hσ
    have h := card_Hgrp_one (n := n) (by omega) d
    rw [hcard] at h
    have hpos : 0 < n.factorial := Nat.factorial_pos n
    have hB : Nat.card (Bgrp d) = 4 := by
      have : n.factorial * Nat.card (Bgrp d) = n.factorial * 4 := by omega
      exact Nat.eq_of_mul_eq_mul_left hpos this
    refine ⟨rfl, ?_, ?_⟩
    · intro h1
      have hd1 : d = 1 := congrArg Prod.snd h1
      rw [hd1, card_Bgrp_one] at hB
      omega
    · intro h1
      have hd1 : d = x4 := congrArg Prod.snd h1
      rw [hd1, card_Bgrp_x4] at hB
      omega
  · exfalso
    have h1 := card_Hgrp_le n σ d
    have h2 := card_centralizer_invol_lt hn hσσ hσ
    omega

theorem not_dvd (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 7) :
    ¬ (2 * n.factorial ∣ 192 * (n - 4).factorial) := by
  rcases hn with rfl | rfl | rfl <;> decide

theorem centralizes_iff (n : ℕ) : ∀ g ∈ Fgrp n,
    (∀ q ∈ Fgrp n, q.1 = 1 → g * q = q * g) ↔ sign g.1 = 1 := by
  rintro ⟨σ, d⟩ ⟨hd, hs⟩
  have key := F1 d hd
  show (∀ q ∈ Fgrp n, q.1 = 1 → (σ, d) * q = q * (σ, d)) ↔ sign σ = 1
  rw [hs, ← key]
  constructor
  · intro h e he1 he2
    have := h (1, e) ⟨he1, by simp [he2]⟩ rfl
    exact congrArg Prod.snd this
  · intro h q hq hq1
    obtain ⟨a, e⟩ := q
    have hq1' : a = 1 := hq1
    subst hq1'
    obtain ⟨he, hse⟩ := hq
    have := h e he (by simpa using hse.symm)
    exact Prod.ext (by simp) this

end FnAux

theorem fnFacts (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 7) : FnFacts n :=
  ⟨FnAux.centralizes_iff n, FnAux.card_C_q (by omega), FnAux.card_C_inv hn,
    FnAux.not_dvd n hn⟩

end CFSG.GH74.GLS.C3.Prop121
