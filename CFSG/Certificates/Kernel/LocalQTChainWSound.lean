module

public import CFSG.Certificates.Kernel.LocalQTChainGSound

public section

namespace CFSG.KC.LQT.CM

open Equiv CFSG.KC.LQT.L CFSG.KC.LQT.S

variable {n : ℕ}

@[expose] def LvW (n : ℕ) (lv : Lvl) : Prop :=
  0 < n ∧ ∀ j < n, getK lv.2.1 j ≠ 0 → (∃ σ : Perm (Fin n), P.code σ = getK lv.2.1 j) ∧
    getK lv.2.2.1 j < lv.2.2.2

theorem lvW_of {lv : Lvl} {prev : List ℕ} (hn0 : 0 < n)
    (h1 : P.allN n (fun j => P.impB (CFSG.KC.Ord.notB (Nat.beq (getK lv.2.1 j) 0))
          (P.letB (getK lv.2.1 j) fun u => CFSG.KC.Ord.andB (P.permK n u)
            (CFSG.KC.Ord.andB (P.allL prev fun b => Nat.beq (P.img u b) b)
              (CFSG.KC.Ord.andB (Nat.beq (P.img u lv.1) j)
                (Nat.blt (getK lv.2.2.1 j) lv.2.2.2))))) = true) :
    LvW n lv := by
  refine ⟨hn0, fun j hj e => ?_⟩
  rw [P.allN_iff] at h1
  have := h1 j hj
  rw [P.impB_iff, P.notB_iff, P.beq_iff, P.letB_eq, P.andB_iff, P.andB_iff, P.andB_iff,
    P.blt_iff] at this
  obtain ⟨hp, -, -, hlt⟩ := this e
  exact ⟨P.exists_of_permK hp, hlt⟩

theorem lvW_okFrom (hn0 : 0 < n) : ∀ (C : List Lvl) (prev : List ℕ), okFrom n C prev = true →
    ∀ lv ∈ C, LvW n lv
  | [], _, _ => fun _ h => absurd h List.not_mem_nil
  | lv :: C, prev, h => by
    change CFSG.KC.Ord.andB (CFSG.KC.Ord.andB _ (Nat.beq (posMask lv n) _))
      (okFrom n C (lv.1 :: prev)) = true at h
    rw [P.andB_iff, P.andB_iff] at h
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact lvW_of hn0 h.1.1
    · exact lvW_okFrom hn0 C _ h.2 l hl

theorem lvW_of_chainOK (hn0 : 0 < n) {C : List Lvl} (hok : chainOK n C = true) :
    ∀ lv ∈ C, LvW n lv :=
  lvW_okFrom hn0 C [] (by rw [← chainOK_eq]; exact hok)

theorem sift_cons_code_w (hn : n ≤ 32) {lv : Lvl} {C : List Lvl} (hlv : LvW n lv)
    (σ : Perm (Fin n)) {k : ℕ} (h : sift n (lv :: C) (P.code σ) = some k) :
    ∃ j < n, ∃ τ : Perm (Fin n), P.code τ = getK lv.2.1 j ∧ getK lv.2.1 j ≠ 0 ∧
      P.img (P.code σ) lv.1 = j ∧ ∃ k', sift n C (P.code (τ⁻¹ * σ)) = some k' ∧
        k = getK lv.2.2.1 j + lv.2.2.2 * k' := by
  simp only [sift] at h
  split_ifs at h with e
  obtain ⟨k', h', rfl⟩ := Option.map_eq_some_iff.1 h
  have hj := img_lt hn (fc_code hn σ) hlv.1 lv.1
  obtain ⟨⟨τ, hτ⟩, -⟩ := hlv.2 _ hj e
  refine ⟨_, hj, τ, hτ, e, rfl, k', ?_, rfl⟩
  rw [← hτ, code_inv_mul hn] at h'
  exact h'

theorem sift_lt_w (hn : n ≤ 32) : ∀ (C : List Lvl), (∀ lv ∈ C, LvW n lv) →
    ∀ {x k : ℕ}, FC n x → sift n C x = some k → k < chainF C
  | [], _, x, k, _, h => by
    simp only [sift] at h
    split_ifs at h
    cases h
    exact Nat.one_pos
  | lv :: C, hC, x, k, hx, h => by
    obtain ⟨hn0, hv⟩ := hC lv (List.mem_cons_self ..)
    simp only [sift] at h
    split_ifs at h with e
    obtain ⟨k', h', rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨⟨σ, hσ⟩, hp⟩ := hv _ (img_lt hn hx hn0 lv.1) e
    rw [← hσ] at h'
    have hk' := sift_lt_w hn C (fun l hl => hC l (List.mem_cons_of_mem _ hl))
      (fc_mul hn (by rw [P.code_inv hn]; exact fc_code hn _) hx) h'
    change _ < lv.2.2.2 * chainF C
    nlinarith

theorem inC_iff_w (hn : n ≤ 32) {C : List Lvl} (hC : ∀ lv ∈ C, LvW n lv) (σ : Perm (Fin n)) :
    inC n C (chainF C) (P.code σ) = true ↔ InC n C σ := by
  unfold inC InC
  rw [P.blt_iff, idxM_sift]
  cases e : sift n C (P.code σ) with
  | none => simp
  | some k =>
    simp only [Option.elim_some, id, Option.isSome_some, iff_true]
    exact sift_lt_w hn C hC (fc_code hn σ) e

theorem chainFrom_sound_w (hn : n ≤ 32) (f : ℕ → Bool) : ∀ {C : List Lvl}, (∀ lv ∈ C, LvW n lv) →
    ∀ (π σ : Perm (Fin n)), chainFrom n C f (P.code π) = true → InC n C σ →
      f (P.code (π * σ)) = true
  | [], _, π, σ, h, hσ => by
    simp only [InC, sift] at hσ
    split_ifs at hσ with e
    · rw [P.code_one] at e
      rw [P.code_inj hn e, mul_one]
      exact h
    · exact absurd hσ (by simp)
  | lv :: C, hC, π, σ, h, hσ => by
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hσ
    obtain ⟨j, hj, τ, hτ, e, -, k', h', -⟩ :=
      sift_cons_code_w hn (hC lv (List.mem_cons_self ..)) σ hk
    change P.allN n (fun j => P.impB (CFSG.KC.Ord.notB (Nat.beq (getK lv.2.1 j) 0))
      (P.letB (P.mul n (P.code π) (getK lv.2.1 j)) (chainFrom n C f))) = true at h
    rw [P.allN_iff] at h
    have := h j hj
    rw [P.impB_iff, P.notB_iff, P.beq_iff, P.letB_eq, ← hτ, P.code_mul hn] at this
    have := chainFrom_sound_w hn f (fun l hl => hC l (List.mem_cons_of_mem _ hl)) (π * τ)
      (τ⁻¹ * σ) (this (by rwa [hτ])) (by rw [InC, h']; rfl)
    rwa [mul_assoc, mul_inv_cancel_left] at this

theorem allChain_sound_w (hn : n ≤ 32) {C : List Lvl} (hC : ∀ lv ∈ C, LvW n lv) (f : ℕ → Bool)
    (h : allChain n C f = true) (σ : Perm (Fin n)) (hσ : InC n C σ) : f (P.code σ) = true := by
  have := chainFrom_sound_w hn f hC 1 σ (by rw [← P.code_one]; exact h) hσ
  rwa [one_mul] at this

theorem allChain_of_chunks {C : List Lvl} {f : ℕ → Bool} (hn0 : 0 < n)
    (h : ∀ j < n, chainChunk n C f j = true) : allChain n C f = true := by
  cases C with
  | nil => exact h 0 hn0
  | cons lv C => exact (P.allN_iff n _).2 h

theorem inC_of_mem_closure {C : List Lvl} {G : List (Perm (Fin n))} {g₀ : Perm (Fin n)}
    (hg₀ : g₀ ∈ G) (hgen : InC n C g₀) (hmul : ∀ σ, InC n C σ → ∀ g ∈ G, InC n C (σ * g))
    {σ : Perm (Fin n)} (hσ : σ ∈ Subgroup.closure {g | g ∈ G}) : InC n C σ := by
  have hone : InC n C 1 := by
    have := inC_pow hmul hgen hg₀ (orderOf g₀ - 1)
    rwa [← pow_succ', Nat.sub_add_cancel (orderOf_pos g₀), pow_orderOf_eq_one] at this
  induction hσ using Subgroup.closure_induction_right with
  | one => exact hone
  | mul_right x _ y hy ih => exact hmul x ih y hy
  | mul_inv_cancel x _ y hy ih =>
    have e : y⁻¹ = y ^ (orderOf y - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos y),
        pow_orderOf_eq_one]
    rw [e]
    exact inC_pow hmul ih hy _

end CFSG.KC.LQT.CM

end
