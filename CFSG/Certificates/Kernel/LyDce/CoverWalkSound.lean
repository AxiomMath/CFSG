module

public import Certificates.Data.Kernel.LyDce.CoverWalk

public section

namespace CFSG.KC.LyDce

open CFSG.KC CFSG.KC.Loop

theorem cwS_andB {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  revert h
  cases a <;> cases b <;> decide

theorem cwS_strictBN (y : Nat) (k : Nat → Bool) : strictBN y k = k y := by
  cases y <;> rfl

theorem cwS_walk {Nc Nd P K Tc Td : Nat} {Q : Nat → Prop} (hc : ∀ X, Q X → Q (net2 Nc X))
    (hd : ∀ X, Q X → Q (net2 Nd X)) : ∀ (es st : List (Nat × Nat × Nat)),
      (∀ t ∈ st, Q t.1 ∧ t.2.1 = net2 Nc t.1 ∧ t.2.2 = net2 Nd t.1) →
      walkS Nc Nd P K Tc Td es st = true →
      ∀ e ∈ es, ∃ X, Q X ∧ lineS P K Tc Td e.1 X (net2 Nc X) (net2 Nd X) = true
  | [], _, _, _ => fun _ he => absurd he List.not_mem_nil
  | e :: es, st, hst, h => by
    unfold walkS at h
    dsimp only at h
    cases hdr : st.drop e.2.1 with
    | nil =>
      rw [hdr] at h
      exact absurd h Bool.false_ne_true
    | cons top rest =>
      rw [hdr] at h
      dsimp only at h
      rw [cwS_strictBN] at h
      beta_reduce at h
      rw [cwS_strictBN] at h
      beta_reduce at h
      rw [cwS_strictBN] at h
      beta_reduce at h
      obtain ⟨h1, h2⟩ := cwS_andB h
      have hmem : ∀ t ∈ top :: rest, t ∈ st := fun t ht => List.mem_of_mem_drop (hdr ▸ ht)
      obtain ⟨hq, hqc, hqd⟩ := hst top (hmem top List.mem_cons_self)
      have hX : Q (selG e.2.2 top) := by
        unfold selG
        cases Nat.beq e.2.2 0
        · cases Nat.beq e.2.2 1
          · exact hq
          · change Q top.2.2
            rw [hqd]
            exact hd _ hq
        · change Q top.2.1
          rw [hqc]
          exact hc _ hq
      have hpop : ∀ t ∈ popG e.2.2 (top :: rest), t ∈ top :: rest := by
        unfold popG
        cases Nat.beq e.2.2 2
        · exact fun t ht => ht
        · exact fun t ht => List.mem_of_mem_tail ht
      intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact ⟨_, hX, h1⟩
      · refine cwS_walk (Nc := Nc) (Nd := Nd) (P := P) (K := K) (Tc := Tc) (Td := Td) hc hd es
          ((selG e.2.2 top, net2 Nc (selG e.2.2 top), net2 Nd (selG e.2.2 top)) ::
            popG e.2.2 (top :: rest)) ?_ h2 e' he'
        intro t ht
        rcases List.mem_cons.1 ht with rfl | ht
        · exact ⟨hX, rfl, rfl⟩
        · exact hst t (hmem t (hpop t ht))

theorem walkSFrom_sound {Nc Nd P K Tc Td M₀ : Nat} {es : List (Nat × Nat × Nat)}
    {Q : Nat → Prop} (h0 : Q (saltOf M₀)) (hc : ∀ X, Q X → Q (net2 Nc X))
    (hd : ∀ X, Q X → Q (net2 Nd X)) (h : walkSFrom Nc Nd P K Tc Td M₀ es = true) :
    ∀ e ∈ es, ∃ X, Q X ∧ lineS P K Tc Td e.1 X (net2 Nc X) (net2 Nd X) = true := by
  unfold walkSFrom at h
  rw [cwS_strictBN] at h
  refine cwS_walk hc hd es _ ?_ h
  intro t ht
  rcases List.mem_singleton.1 ht with rfl
  exact ⟨h0, rfl, rfl⟩

end CFSG.KC.LyDce

end
