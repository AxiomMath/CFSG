module

public import CFSG.Certificates.Kernel.LocalQTChainWSound

public section

namespace CFSG.KC.LQT.PHSnd

open Equiv CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.KC.LQT.CM

variable {n : ℕ}

@[expose] def ChainW (n : ℕ) : List ℕ → List Lvl → Prop
  | _, [] => True
  | prev, lv :: C => LvW n lv ∧
      (∀ j < n, getK lv.2.1 j ≠ 0 →
        (∀ b ∈ prev, P.img (getK lv.2.1 j) b = b) ∧ P.img (getK lv.2.1 j) lv.1 = j) ∧
      ChainW n (lv.1 :: prev) C

private theorem chainW_of (hn0 : 0 < n) : ∀ (C : List Lvl) (prev : List ℕ),
    okFrom n C prev = true → ChainW n prev C
  | [], _, _ => trivial
  | lv :: C, prev, h => by
    change CFSG.KC.Ord.andB (CFSG.KC.Ord.andB _ (Nat.beq (posMask lv n) _))
      (okFrom n C (lv.1 :: prev)) = true at h
    rw [P.andB_iff, P.andB_iff] at h
    obtain ⟨⟨h1, -⟩, h3⟩ := h
    refine ⟨lvW_of hn0 h1, fun j hj e => ?_, chainW_of hn0 C _ h3⟩
    rw [P.allN_iff] at h1
    have := h1 j hj
    rw [P.impB_iff, P.notB_iff, P.beq_iff, P.letB_eq, P.andB_iff, P.andB_iff, P.andB_iff,
      P.allL_iff, P.beq_iff] at this
    obtain ⟨-, hb, hj', -⟩ := this e
    exact ⟨fun b hb' => P.beq_iff.1 (hb b hb'), hj'⟩

theorem chainW_of_ok (hn0 : 0 < n) {C : List Lvl} (hok : chainOK n C = true) : ChainW n [] C :=
  chainW_of hn0 C [] (by rw [← chainOK_eq]; exact hok)

theorem fix_of_inC_w (hn : n ≤ 32) : ∀ {prev : List ℕ} {C : List Lvl}, ChainW n prev C →
    ∀ {σ : Perm (Fin n)}, InC n C σ → ∀ b ∈ prev, ∀ hb : b < n, σ ⟨b, hb⟩ = ⟨b, hb⟩
  | _, [], _, σ, h, b, _, hb => by
    simp only [InC, sift] at h
    split_ifs at h with e
    · rw [P.code_one] at e
      have e' := P.code_inj hn e
      subst e'
      rfl
    · exact absurd h (by simp)
  | prev, lv :: C, hC, σ, h, b, hb, hbn => by
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨j, hj, τ, hτ, e, -, k', h', -⟩ := sift_cons_code_w hn hC.1 σ hk
    have hfix := fix_of_inC_w hn hC.2.2 (σ := τ⁻¹ * σ) (by rw [InC, h']; rfl) b
      (List.mem_cons_of_mem _ hb) hbn
    have hτb := (hC.2.1 j hj e).1 b hb
    rw [← hτ, img_code_fix hn _ hbn] at hτb
    have hτb' : τ ⟨b, hbn⟩ = ⟨b, hbn⟩ := Fin.ext hτb
    have e1 : σ = τ * (τ⁻¹ * σ) := (mul_inv_cancel_left τ σ).symm
    rw [e1, Perm.mul_apply, hfix, hτb']

theorem inC_cons_w (hn : n ≤ 32) {prev : List ℕ} {lv : Lvl} {C : List Lvl}
    (h : ChainW n prev (lv :: C)) {σ : Perm (Fin n)} (hσ : InC n (lv :: C) σ) :
    ∃ j < n, ∃ τ : Perm (Fin n), P.code τ = getK lv.2.1 j ∧ getK lv.2.1 j ≠ 0 ∧
      InC n C (τ⁻¹ * σ) ∧ P.img (P.code σ) lv.1 = j := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hσ
  obtain ⟨j, hj, τ, hτ, e, himg, k', h', -⟩ := sift_cons_code_w hn h.1 σ hk
  exact ⟨j, hj, τ, hτ, e, by rw [InC, h']; rfl, himg⟩

theorem inC_rep_mul_w (hn : n ≤ 32) {prev : List ℕ} {lv : Lvl} {C : List Lvl}
    (h : ChainW n prev (lv :: C)) {j : ℕ} (hj : j < n) {τ : Perm (Fin n)}
    (hτ : P.code τ = getK lv.2.1 j) (hne : getK lv.2.1 j ≠ 0) {ρ : Perm (Fin n)}
    (hρ : InC n C ρ) : InC n (lv :: C) (τ * ρ) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hρ
  have himg : P.img (P.code (τ * ρ)) lv.1 = j := by
    have hb := (h.2.1 j hj hne).2
    rw [← hτ] at hb
    by_cases hbn : lv.1 < n
    · have hfix := fix_of_inC_w hn h.2.2 hρ lv.1 List.mem_cons_self hbn
      rw [img_code_fix hn _ hbn] at hb ⊢
      rw [Perm.mul_apply, hfix]
      exact hb
    · rw [img_ge hn (fc_code hn _) (not_lt.1 hbn)]
      rw [img_ge hn (fc_code hn _) (not_lt.1 hbn)] at hb
      exact hb
  have hs : sift n (lv :: C) (P.code (τ * ρ)) = some (getK lv.2.2.1 j + lv.2.2.2 * k) := by
    simp only [sift, himg, hne, ↓reduceIte]
    rw [← hτ, code_inv_mul hn, inv_mul_cancel_left, hk]
    rfl
  rw [InC, hs]
  rfl

theorem chainFrom_complete_w (hn : n ≤ 32) (f : ℕ → Bool) : ∀ {prev : List ℕ} {C : List Lvl},
    ChainW n prev C → ∀ π : Perm (Fin n), (∀ σ, InC n C σ → f (P.code (π * σ)) = true) →
      chainFrom n C f (P.code π) = true
  | _, [], _, π, h => by
    have := h 1 (by simp only [InC, sift]; rw [P.code_one]; simp)
    rwa [mul_one] at this
  | prev, lv :: C, hC, π, h => by
    change P.allN n (fun j => P.impB (CFSG.KC.Ord.notB (Nat.beq (getK lv.2.1 j) 0))
      (P.letB (P.mul n (P.code π) (getK lv.2.1 j)) (chainFrom n C f))) = true
    rw [P.allN_iff]
    intro j hj
    rw [P.impB_iff, P.notB_iff, P.beq_iff, P.letB_eq]
    intro hne
    obtain ⟨τ, hτ⟩ := (hC.1.2 j hj hne).1
    rw [← hτ, P.code_mul hn]
    refine chainFrom_complete_w hn f hC.2.2 (π * τ) fun σ hσ => ?_
    have := h (τ * σ) (inC_rep_mul_w hn hC hj hτ hne hσ)
    rwa [← mul_assoc] at this

theorem allChain_complete_w (hn : n ≤ 32) {prev : List ℕ} {C : List Lvl} (hC : ChainW n prev C)
    (f : ℕ → Bool) (h : ∀ σ, InC n C σ → f (P.code σ) = true) : allChain n C f = true := by
  change chainFrom n C f (P.one n) = true
  rw [P.code_one]
  exact chainFrom_complete_w hn f hC 1 fun σ hσ => by rw [one_mul]; exact h σ hσ

end CFSG.KC.LQT.PHSnd

end
