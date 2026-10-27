module

public import CFSG.Certificates.Kernel.A6CK.Bridge

public section

namespace CFSG.KC.A6CK

theorem mergeK_nil_left (M : List Nat) : mergeK [] M = M := rfl

theorem mergeK_cons_nil (x : Nat) (xs : List Nat) : mergeK (x :: xs) [] = x :: xs := rfl

theorem mergeK_cons_cons (x y : Nat) (xs ys : List Nat) : mergeK (x :: xs) (y :: ys) =
    Bool.rec (motive := fun _ => List Nat) (y :: mergeK (x :: xs) ys) (x :: mergeK xs (y :: ys))
      (Nat.blt x y) := rfl

theorem mergeK_perm : ∀ (L M : List Nat), (mergeK L M).Perm (L ++ M)
  | [], M => by rw [mergeK_nil_left]; exact List.Perm.refl _
  | x :: xs, [] => by rw [mergeK_cons_nil, List.append_nil]
  | x :: xs, y :: ys => by
    rw [mergeK_cons_cons]
    cases Nat.blt x y
    · have ih := mergeK_perm (x :: xs) ys
      exact (ih.cons y).trans (List.perm_middle).symm
    · exact (mergeK_perm xs (y :: ys)).cons x

@[expose] noncomputable def pairGo (Ls : List (List Nat)) : List Nat → Nat → List (List Nat) :=
  List.rec (motive := fun _ => List Nat → Nat → List (List Nat))
    (fun pend f => Nat.rec (motive := fun _ => List (List Nat)) [] (fun _ _ => [pend]) f)
    (fun x _ ih pend f => Nat.rec (motive := fun _ => List (List Nat)) (ih x 1)
      (fun _ _ => mergeK pend x :: ih [] 0) f) Ls

theorem pairGo_spec : ∀ (Ls : List (List Nat)) (pend : List Nat),
    ((pairGo Ls pend 0).flatten.Perm Ls.flatten ∧ (pairGo Ls pend 0).length = (Ls.length + 1) / 2) ∧
    ((pairGo Ls pend 1).flatten.Perm (pend ++ Ls.flatten) ∧
      (pairGo Ls pend 1).length = (Ls.length + 2) / 2)
  | [], pend => by
    refine ⟨⟨List.Perm.refl _, rfl⟩, ?_, rfl⟩
    change [pend].flatten.Perm (pend ++ [])
    simp
  | x :: Ls, pend => by
    have ih := pairGo_spec Ls x
    have ih0 := pairGo_spec Ls []
    have e0 : pairGo (x :: Ls) pend 0 = pairGo Ls x 1 := rfl
    have e1 : pairGo (x :: Ls) pend 1 = mergeK pend x :: pairGo Ls [] 0 := rfl
    rw [e0, e1]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [List.flatten_cons]
      exact ih.2.1
    · rw [ih.2.2, List.length_cons]
    · rw [List.flatten_cons, List.flatten_cons, ← List.append_assoc]
      exact (mergeK_perm pend x).append ih0.1.1
    · rw [List.length_cons, List.length_cons, ih0.1.2]
      omega

theorem pairK_perm (Ls : List (List Nat)) : (pairK Ls).flatten.Perm Ls.flatten :=
  (pairGo_spec Ls []).1.1

theorem pairK_length (Ls : List (List Nat)) : (pairK Ls).length = (Ls.length + 1) / 2 :=
  (pairGo_spec Ls []).1.2

@[expose] noncomputable def runsK (d : Nat) (L : List Nat) : List (List Nat) :=
  Nat.rec (motive := fun _ => List (List Nat))
    (List.rec (motive := fun _ => List (List Nat)) [] (fun x _ ih => [x] :: ih) L)
    (fun _ ih => pairK ih) d

theorem runs0 (L : List Nat) :
    (List.rec (motive := fun _ => List (List Nat)) [] (fun x _ ih => [x] :: ih) L).flatten = L ∧
    (List.rec (motive := fun _ => List (List Nat)) [] (fun x _ ih => [x] :: ih) L).length =
      L.length := by
  induction L with
  | nil => exact ⟨rfl, rfl⟩
  | cons x L ih =>
    change ([x] :: _ : List (List Nat)).flatten = _ ∧ ([x] :: _ : List (List Nat)).length = _
    rw [List.flatten_cons, ih.1, List.length_cons, List.length_cons, ih.2]
    exact ⟨rfl, rfl⟩

theorem runsK_perm (L : List Nat) : ∀ d, (runsK d L).flatten.Perm L
  | 0 => List.Perm.of_eq (runs0 L).1
  | d + 1 => (pairK_perm (runsK d L)).trans (runsK_perm L d)

theorem runsK_length (L : List Nat) : ∀ d m, L.length ≤ 2 ^ (d + m) → (runsK d L).length ≤ 2 ^ m
  | 0, m, h => by
    have h0 : (runsK 0 L).length = L.length := (runs0 L).2
    rw [h0]
    rwa [Nat.zero_add] at h
  | d + 1, m, h => by
    have ih := runsK_length L d (m + 1) (by rwa [Nat.add_assoc, Nat.add_comm 1 m] at h)
    change (pairK (runsK d L)).length ≤ _
    rw [pairK_length]
    rw [Nat.pow_succ] at ih
    omega

theorem keysK_eq (E : List Nat) :
    List.rec (motive := fun _ => List Nat) [] (fun x _ ih => keyK x :: ih) E = E.map keyK := by
  induction E with
  | nil => rfl
  | cons x E ih =>
    change keyK x :: _ = _
    rw [ih, List.map_cons]

theorem incK_go : ∀ (L : List Nat) (b : Nat), List.rec (motive := fun _ => Nat → Bool)
    (fun _ => true) (fun x _ ih b => andB (Nat.ble b x) (ih (Nat.succ x))) L b = true →
    L.Pairwise (· < ·) ∧ ∀ x ∈ L, b ≤ x
  | [], _, _ => ⟨List.Pairwise.nil, by simp⟩
  | x :: L, b, h => by
    change andB (Nat.ble b x) _ = true at h
    rw [andB_eq, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨h1, h2⟩ := incK_go L (Nat.succ x) h.2
    refine ⟨List.Pairwise.cons (fun y hy => by have := h2 y hy; omega) h1, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h.1
    · have := h2 y hy
      omega

theorem incK_spec {L : List Nat} (h : incK L = true) : L.Nodup :=
  ((incK_go L 0 h).1).imp (fun h => Nat.ne_of_lt h)

theorem nodupK_spec {E : List Nat} (h : nodupK E = true) (hl : E.length ≤ 2 ^ 14) :
    (E.map keyK).Nodup := by
  unfold nodupK at h
  rw [keysK_eq] at h
  have hlen := runsK_length (E.map keyK) 14 0 (by rw [List.length_map]; exact hl)
  have hp := runsK_perm (E.map keyK) 14
  have e : sortK 14 (E.map keyK) = List.rec (motive := fun _ => List Nat) [] (fun x _ _ => x)
      (runsK 14 (E.map keyK)) := rfl
  rw [e] at h
  generalize runsK 14 (E.map keyK) = R at h hlen hp
  match R, hlen with
  | [], _ =>
    rw [List.flatten_nil] at hp
    have h0 := List.Perm.nil_eq hp
    rw [← h0]
    exact List.nodup_nil
  | [s], _ =>
    rw [List.flatten_cons, List.flatten_nil, List.append_nil] at hp
    exact hp.nodup_iff.1 (incK_spec h)
  | _ :: _ :: _, hR => simp at hR

end CFSG.KC.A6CK
