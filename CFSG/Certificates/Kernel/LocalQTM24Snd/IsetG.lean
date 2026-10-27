module

public import Certificates.Data.Kernel.LocalQT.M24L
public import CFSG.Certificates.Kernel.LocalQTM24Snd.Base
public import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.LQT.M24Snd

open Equiv CFSG.KC.LQT.M24 CFSG.KC.LQT.P

variable {n : ℕ}

@[expose] def conjP (g0 g1 g2 g3 σ : Perm (Fin n)) : List (Perm (Fin n)) :=
  [g0 * σ * g2, g1 * σ * g3, g2 * σ * g0, g3 * σ * g1]

private theorem aux_isetg_shl (x : ℕ) : Nat.shiftLeft x 5 = x * 32 :=
  Nat.shiftLeft_eq x 5

private theorem aux_isetg_shr (e : ℕ) : Nat.shiftRight e 5 = e / 32 :=
  Nat.shiftRight_eq_div_pow e 5

private theorem aux_isetg_land31 (x : ℕ) : Nat.land x 31 = x % 32 :=
  Nat.and_two_pow_sub_one_eq_mod x 5

private theorem aux_isetg_land3 (h : ℕ) : Nat.land h 3 < 4 := by
  have h4 : Nat.land h 3 = h % 4 := Nat.and_two_pow_sub_one_eq_mod h 2
  omega

private theorem aux_isetg_entry (x j : ℕ) (hj : j < 32) :
    Nat.land (Nat.add (Nat.shiftLeft x 5) j) 31 = j ∧
      codeE (Nat.add (Nat.shiftLeft x 5) j) = x := by
  have e1 : Nat.add (Nat.shiftLeft x 5) j = x * 32 + j := by
    rw [aux_isetg_shl] <;> rfl
  rw [e1]
  refine ⟨?_, ?_⟩
  · rw [aux_isetg_land31]
    omega
  · unfold codeE
    rw [aux_isetg_shr]
    omega

private theorem aux_isetg_codeE_shl (s : ℕ) : codeE (Nat.shiftLeft s 5) = s := by
  unfold codeE
  rw [aux_isetg_shr, aux_isetg_shl]
  omega

private theorem aux_isetg_ball_succ {α : Type*} {f : α → List α} {seeds : Set α} {k : ℕ}
    {σ : α} : σ ∈ ball f seeds (k + 1) ↔ σ ∈ ball f seeds k ∨ ∃ τ ∈ ball f seeds k, σ ∈ f τ :=
  Iff.rfl

theorem cimgK_code (hn : n ≤ 32) (g0 g1 g2 g3 σ : Perm (Fin n)) :
    cimgK n (P.code g0) (P.code g1) (P.code g2) (P.code g3) (P.code σ) =
      (conjP g0 g1 g2 g3 σ).map P.code := by
  simp only [cimgK, conjP, List.map_cons, List.map_nil, P.code_mul hn]

theorem cimgAt_mem (n g0 g1 g2 g3 k x : ℕ) (hk : k < 4) :
    cimgAt n g0 g1 g2 g3 k x ∈ cimgK n g0 g1 g2 g3 x := by
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk' with rfl | rfl | rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem iset_set (hn : n ≤ 32) (g0 g1 g2 g3 : Perm (Fin n)) (S IL : List ℕ) (r : ℕ)
    (seeds : Set (Perm (Fin n))) (hseeds : ∀ σ, σ ∈ seeds ↔ P.code σ ∈ S)
    (hS : ∀ c ∈ S, ∃ σ : Perm (Fin n), P.code σ = c)
    (hin : ∀ s ∈ S, Nat.shiftLeft s 5 ∈ IL)
    (hclo : ∀ e ∈ IL, ∀ y ∈ cimgK n (P.code g0) (P.code g1) (P.code g2) (P.code g3) (codeE e),
      y ∈ IL.map codeE)
    (hreach : ∀ e ∈ IL, ∃ hh : ℕ,
      (Nat.land e 31 = 0 ∧ codeE e ∈ S) ∨
      (Nat.land e 31 ≠ 0 ∧ Nat.land e 31 ≤ r ∧
        cimgAt n (P.code g0) (P.code g1) (P.code g2) (P.code g3) (Nat.land hh 3)
          (Nat.shiftRight hh 2) = codeE e ∧
        Nat.add (Nat.shiftLeft (Nat.shiftRight hh 2) 5) (Nat.sub (Nat.land e 31) 1) ∈ IL)) :
    (∀ σ : Perm (Fin n), P.code σ ∈ IL.map codeE ↔ σ ∈ ball (conjP g0 g1 g2 g3) seeds r) ∧
      ∀ c ∈ IL.map codeE, ∃ σ : Perm (Fin n), P.code σ = c := by
  have hdepth : ∀ k : ℕ, ∀ e ∈ IL, Nat.land e 31 = k →
      ∃ σ : Perm (Fin n), σ ∈ ball (conjP g0 g1 g2 g3) seeds k ∧ P.code σ = codeE e := by
    intro k
    refine Nat.strong_induction_on k fun k ih => ?_
    intro e he hk
    obtain ⟨hh, h⟩ := hreach e he
    rcases h with ⟨h0, hSe⟩ | ⟨hne, _, hcim, hpar⟩
    ·
      have hk0 : k = 0 := by omega
      obtain ⟨σ, hσ⟩ := hS (codeE e) hSe
      refine ⟨σ, ?_, hσ⟩
      rw [hk0]
      exact mem_ball_zero ((hseeds σ).2 (by rw [hσ]; exact hSe))
    ·
      have hk0 : k ≠ 0 := by omega
      have hlt : Nat.land e 31 < 32 := by
        rw [aux_isetg_land31]
        omega
      have hjlt : Nat.sub (Nat.land e 31) 1 < 32 := by
        show Nat.land e 31 - 1 < 32
        omega
      have hjeq : Nat.sub (Nat.land e 31) 1 = k - 1 := by
        show Nat.land e 31 - 1 = k - 1
        omega
      obtain ⟨hp1, hp2⟩ :=
        aux_isetg_entry (Nat.shiftRight hh 2) (Nat.sub (Nat.land e 31) 1) hjlt
      obtain ⟨τ, hτ, hτc⟩ := ih (k - 1) (by omega) _ hpar (hp1.trans hjeq)
      have hmem : codeE e ∈
          cimgK n (P.code g0) (P.code g1) (P.code g2) (P.code g3) (P.code τ) := by
        rw [hτc.trans hp2, ← hcim]
        exact cimgAt_mem n _ _ _ _ _ _ (aux_isetg_land3 hh)
      rw [cimgK_code hn] at hmem
      obtain ⟨σ, hσ, hσc⟩ := List.mem_map.1 hmem
      refine ⟨σ, ?_, hσc⟩
      have hstep := ball_step hτ hσ
      rwa [show k - 1 + 1 = k by omega] at hstep
  have hle_r : ∀ e ∈ IL, Nat.land e 31 ≤ r := by
    intro e he
    obtain ⟨_, h⟩ := hreach e he
    rcases h with ⟨h0, _⟩ | ⟨_, hle, _⟩
    · omega
    · exact hle
  have hsub : ∀ σ : Perm (Fin n), P.code σ ∈ IL.map codeE →
      σ ∈ ball (conjP g0 g1 g2 g3) seeds r := by
    intro σ hσ
    obtain ⟨e, he, hec⟩ := List.mem_map.1 hσ
    obtain ⟨σ', hσ'b, hσ'c⟩ := hdepth (Nat.land e 31) e he rfl
    have hσσ' : σ' = σ := P.code_inj hn (hσ'c.trans hec)
    rw [hσσ'] at hσ'b
    exact ball_mono (hle_r e he) hσ'b
  have hcl : ∀ k : ℕ, ∀ σ : Perm (Fin n), σ ∈ ball (conjP g0 g1 g2 g3) seeds k →
      P.code σ ∈ IL.map codeE := by
    intro k
    induction k with
    | zero =>
      intro σ hσ
      have hσS : P.code σ ∈ S := (hseeds σ).1 hσ
      exact List.mem_map.2
        ⟨Nat.shiftLeft (P.code σ) 5, hin _ hσS, aux_isetg_codeE_shl (P.code σ)⟩
    | succ k ih =>
      intro σ hσ
      rcases aux_isetg_ball_succ.1 hσ with hσk | ⟨τ, hτ, hστ⟩
      · exact ih σ hσk
      · obtain ⟨e, he, hec⟩ := List.mem_map.1 (ih τ hτ)
        refine hclo e he (P.code σ) ?_
        rw [hec, cimgK_code hn]
        exact List.mem_map.2 ⟨σ, hστ, rfl⟩
  refine ⟨fun σ => ⟨hsub σ, hcl r σ⟩, ?_⟩
  intro c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
  obtain ⟨σ, _, hσ⟩ := hdepth (Nat.land e 31) e he rfl
  exact ⟨σ, hσ⟩

end CFSG.KC.LQT.M24Snd

end
