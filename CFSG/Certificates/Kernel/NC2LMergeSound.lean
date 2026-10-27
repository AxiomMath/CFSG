module

public import Certificates.Data.Kernel.NC2L
public import CFSG.Certificates.Kernel.LocalQTSecLemmas

public section

namespace CFSG.KC.NC2L

open CFSG.KC.LQT CFSG.KC.LQT.SecS

theorem orB_true {a b : Bool} (h : CFSG.KC.Ord.orB a b = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem memB_spec {k : Nat} : ∀ {ns : List Nat}, memB k ns = true → k ∈ ns
  | [], h => absurd h Bool.false_ne_true
  | h :: t, hm => by
    rcases orB_true hm with e | e
    · rw [Nat.eq_of_beq_eq_true e]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (memB_spec e)

theorem dropLt_cons (f : Nat → Nat) (v h : Nat) (t : List Nat) (k : List Nat → Bool) :
    dropLt f v (h :: t) k =
      Bool.rec (motive := fun _ => Bool) (k (h :: t)) (dropLt f v t k) (Nat.blt (f h) v) := by
  have e : dropLt f v (h :: t) k = strictB (f h) fun w =>
      Bool.rec (motive := fun _ => Bool) (k (h :: t)) (dropLt f v t k) (Nat.blt w v) := rfl
  rw [e, strictB_eq]

theorem dropLt_spec (f : Nat → Nat) (v : Nat) : ∀ (σ : List Nat) (k : List Nat → Bool),
    dropLt f v σ k = true → ∃ σ', k σ' = true ∧ (∃ p, σ = p ++ σ' ∧ ∀ h ∈ p, f h < v) ∧
      ∀ h t, σ' = h :: t → v ≤ f h
  | [], _, hk => ⟨[], hk, ⟨[], rfl, fun _ hh => absurd hh List.not_mem_nil⟩,
      fun _ _ e => nomatch e⟩
  | h :: t, k, hk => by
    rw [dropLt_cons] at hk
    cases hb : Nat.blt (f h) v
    · rw [hb] at hk
      refine ⟨h :: t, hk, ⟨[], rfl, fun _ hh => absurd hh List.not_mem_nil⟩, fun h' t' e => ?_⟩
      rw [List.cons.inj e |>.1] at hb
      exact Nat.le_of_not_lt fun hlt => absurd (Nat.blt_eq.mpr hlt) (by rw [hb]; decide)
    · rw [hb] at hk
      obtain ⟨σ', h1, ⟨p, hp, hp'⟩, h3⟩ := dropLt_spec f v t k hk
      refine ⟨σ', h1, ⟨h :: p, by rw [hp]; rfl, fun x hx => ?_⟩, h3⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Nat.blt_eq.mp hb
      · exact hp' x hx

theorem mergeRun_cons (N : Nat) (fc fs : Nat → Nat) (ns : List Nat) (k : Nat) (τ : List Nat)
    (lo mask : Nat) (σ : List Nat) :
    mergeRun N fc fs ns (k :: τ) lo mask σ = CFSG.KC.Ord.andB (Nat.blt k N)
      (CFSG.KC.Ord.andB (Nat.beq (mask &&& 1 <<< k) 0) (CFSG.KC.Ord.andB (Nat.ble lo (fc k))
        (dropLt fs (fc k) σ fun σ' => CFSG.KC.Ord.andB (headOK fs (fc k) (memB k ns) σ')
          (mergeRun N fc fs ns τ (fc k) (mask ||| 1 <<< k) σ')))) := by
  have e : mergeRun N fc fs ns (k :: τ) lo mask σ = strictB (fc k) fun v =>
      CFSG.KC.Ord.andB (Nat.blt k N) (CFSG.KC.Ord.andB (Nat.beq (mask &&& 1 <<< k) 0)
        (CFSG.KC.Ord.andB (Nat.ble lo v) (dropLt fs v σ fun σ' =>
          CFSG.KC.Ord.andB (headOK fs v (memB k ns) σ')
            (strictB (mask ||| 1 <<< k) fun m1 => mergeRun N fc fs ns τ v m1 σ')))) := rfl
  rw [e, strictB_eq]
  simp only [strictB_eq]

theorem mergeRun_spec (N : Nat) (fc fs : Nat → Nat) (ns : List Nat) :
    ∀ (τ : List Nat) (lo mask : Nat) (σ : List Nat), mergeRun N fc fs ns τ lo mask σ = true →
      σ.Pairwise (fun a b => fs a < fs b) →
      (∀ n < N, mask.testBit n = true ∨ n ∈ τ) ∧ (∀ k ∈ τ, lo ≤ fc k) ∧
        ∀ k ∈ τ, ∀ j ∈ σ, fc k = fs j → k ∈ ns
  | [], lo, mask, σ, h, _ => by
    have e : mask = 2 ^ N - 1 := by
      have h' : Nat.beq mask (1 <<< N - 1) = true := h
      rw [Nat.eq_of_beq_eq_true h', Nat.shiftLeft_eq, Nat.one_mul]
    refine ⟨fun n hn => Or.inl ?_, fun k hk => absurd hk List.not_mem_nil,
      fun k hk => absurd hk List.not_mem_nil⟩
    rw [e, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hn
  | k :: τ, lo, mask, σ, h, hσ => by
    rw [mergeRun_cons] at h
    obtain ⟨-, h⟩ := andT h
    obtain ⟨-, h⟩ := andT h
    obtain ⟨hlo, h⟩ := andT h
    obtain ⟨σ', hk, ⟨p, hp, hp'⟩, hhd⟩ := dropLt_spec fs (fc k) σ _ h
    obtain ⟨hh, hrest⟩ := andT hk
    rw [hp] at hσ
    have hσ' := (List.pairwise_append.1 hσ).2.1
    obtain ⟨h1, h2, h3⟩ := mergeRun_spec N fc fs ns τ _ _ σ' hrest hσ'
    have hlo' := Nat.le_of_ble_eq_true hlo
    refine ⟨fun n hn => ?_, fun m hm => ?_, fun m hm j hj e => ?_⟩
    · rcases h1 n hn with h4 | h4
      · rw [Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow, Bool.or_eq_true,
          decide_eq_true_eq] at h4
        rcases h4 with h4 | rfl
        · exact Or.inl h4
        · exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ h4)
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact hlo'
      · exact Nat.le_trans hlo' (h2 m hm)
    · rw [hp] at hj
      have hjσ : j ∈ σ' := by
        rcases List.mem_append.1 hj with hj | hj
        · have hv := hp' j hj
          rcases List.mem_cons.1 hm with rfl | hm
          · exact absurd e (Nat.ne_of_gt hv)
          · exact absurd e (Nat.ne_of_gt (Nat.lt_of_lt_of_le hv (h2 m hm)))
        · exact hj
      rcases List.mem_cons.1 hm with rfl | hm
      · obtain ⟨hd, t, rfl⟩ : ∃ hd t, σ' = hd :: t := by
          cases σ' with
          | nil => exact absurd hjσ List.not_mem_nil
          | cons hd t => exact ⟨hd, t, rfl⟩
        have hge := hhd hd t rfl
        have heq : fs hd = fc m := by
          rcases List.mem_cons.1 hjσ with rfl | hjt
          · exact e.symm
          · exact absurd (List.rel_of_pairwise_cons hσ' hjt) (by omega)
        rcases orB_true hh with hn | hn
        · exact absurd heq (ne_of_notB hn)
        · exact memB_spec hn
      · exact h3 m hm j hjσ e

theorem merge_sound {N : Nat} {fc fs : Nat → Nat} {ns σ τ : List Nat}
    (hs : sortRun N fs σ 0 0 = true) (hm : mergeRun N fc fs ns τ 0 0 σ = true) {k j : Nat}
    (hk : k < N) (hj : j < N) (h : fc k = fs j) : k ∈ ns := by
  obtain ⟨s1, -, s3⟩ := sortRun_spec N fs σ 0 0 hs
  obtain ⟨m1, -, m3⟩ := mergeRun_spec N fc fs ns τ 0 0 σ hm s3
  exact m3 k ((m1 k hk).resolve_left (by simp)) j ((s1 j hj).resolve_left (by simp)) h

end CFSG.KC.NC2L

end
