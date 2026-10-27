module

public import Certificates.Data.Kernel.Cert690.Enum
public import CFSG.Certificates.Kernel.Cert690.BfsSound
public import CFSG.Certificates.Kernel.Cert690.TreeSound

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62

theorem orK_eq (a b : Bool) : orK a b = (a || b) := by cases a <;> rfl

theorem enumParK_spec (getE : ℕ → ℕ) (gs : List ℕ) : ∀ (E : List ℕ) (P : List (ℕ × ℕ)) (s : ℕ),
    enumParK getE gs E P s = true → P.length = E.length ∧ ∀ i (hi : i < E.length)
      (hp : i < P.length), s + i = 0 ∨ ((P[i].1 < s + i ∧ P[i].2 < gs.length) ∧
        E[i] = mulF (getE P[i].1) (gs.getD P[i].2 0))
  | [], [], _, _ => ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | [], _ :: _, _, h => absurd h (by simp [enumParK])
  | _ :: _, [], _, h => absurd h (by simp [enumParK])
  | x :: E, p :: P, s, h => by
    have h' : andK (orK (Nat.beq s 0) (andK (Nat.blt p.1 s)
        (andK (Nat.blt p.2 gs.length) (Nat.beq x (mulF (getE p.1) (gs.getD p.2 0))))))
        (enumParK getE gs E P (s + 1)) = true := h
    simp only [andK_eq, orK_eq, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at h'
    obtain ⟨hl, hr⟩ := enumParK_spec getE gs E P (s + 1) h'.2
    refine ⟨by simp [hl], fun i hi hp => ?_⟩
    cases i with
    | zero =>
      rcases h'.1 with h0 | ⟨h1, h2, h3⟩
      · exact Or.inl (by simpa using h0)
      · exact Or.inr ⟨⟨by simpa using h1, by simpa using h2⟩, by simpa using h3⟩
    | succ i =>
      rcases hr i (by simpa using hi) (by simpa using hp) with h0 | h1
      · exact absurd h0 (by omega)
      · right
        simp only [List.getElem_cons_succ]
        refine ⟨⟨?_, h1.1.2⟩, h1.2⟩
        have := h1.1.1
        omega

theorem enumClG_spec (ix : ℕ → ℕ) (n x : ℕ) :
    ∀ gs : List ℕ, enumClG ix n x gs = true → ∀ g ∈ gs, ix (mulF x g) < n
  | [], _, g, hg => absurd hg (by simp)
  | g' :: gs, h, g, hg => by
    have h' : andK (Nat.blt (ix (mulF x g')) n) (enumClG ix n x gs) = true := h
    rw [andK_eq, Bool.and_eq_true, Nat.blt_eq] at h'
    rcases List.mem_cons.1 hg with rfl | hg
    · exact h'.1
    · exact enumClG_spec ix n x gs h'.2 g hg

theorem enumClK_spec (ix : ℕ → ℕ) (n : ℕ) (gs : List ℕ) :
    ∀ E : List ℕ, enumClK ix n gs E = true → ∀ x ∈ E, ∀ g ∈ gs, ix (mulF x g) < n
  | [], _, x, hx => absurd hx (by simp)
  | y :: E, h, x, hx => by
    have h' : andK (enumClG ix n y gs) (enumClK ix n gs E) = true := h
    rw [andK_eq, Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hx with rfl | hx
    · exact enumClG_spec ix n x gs h'.1
    · exact enumClK_spec ix n gs E h'.2 x hx

theorem enumInvG_spec (g : ℕ) : ∀ E : List ℕ, enumInvG g E = true → ∃ e ∈ E, mulF g e = oneF
  | [], h => absurd h (by simp [enumInvG])
  | e :: E, h => by
    have h' : orK (Nat.beq (mulF g e) oneF) (enumInvG g E) = true := h
    rw [orK_eq, Bool.or_eq_true, Nat.beq_eq] at h'
    rcases h' with h1 | h2
    · exact ⟨e, List.mem_cons_self, h1⟩
    · obtain ⟨e', he, h3⟩ := enumInvG_spec g E h2
      exact ⟨e', List.mem_cons_of_mem _ he, h3⟩

theorem enumInvK_spec (E : List ℕ) :
    ∀ gs : List ℕ, enumInvK gs E = true → ∀ g ∈ gs, ∃ e ∈ E, mulF g e = oneF
  | [], _, g, hg => absurd hg (by simp)
  | g' :: gs, h, g, hg => by
    have h' : andK (enumInvG g' E) (enumInvK gs E) = true := h
    rw [andK_eq, Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hg with rfl | hg
    · exact enumInvG_spec g E h'.1
    · exact enumInvK_spec E gs h'.2 g hg

theorem invMulK_spec (getE : ℕ → ℕ) (n : ℕ) : ∀ (E inv : List ℕ), invMulK getE n E inv = true →
    inv.length = E.length ∧ ∀ i (hi : i < E.length) (hj : i < inv.length),
      inv[i] < n ∧ mulF E[i] (getE inv[i]) = oneF
  | [], [], _ => ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | [], _ :: _, h => absurd h (by simp [invMulK])
  | _ :: _, [], h => absurd h (by simp [invMulK])
  | x :: E, j :: inv, h => by
    have h' : andK (andK (Nat.blt j n) (Nat.beq (mulF x (getE j)) oneF)) (invMulK getE n E inv) =
      true := h
    simp only [andK_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
    obtain ⟨hl, hr⟩ := invMulK_spec getE n E inv h'.2
    refine ⟨by simp [hl], fun i hi hj => ?_⟩
    cases i with
    | zero => exact h'.1
    | succ i => exact hr i (by simpa using hi) (by simpa using hj)

theorem enumOK_of {gs E : List ℕ} {P : List (ℕ × ℕ)} {S : List (ℕ × ℕ)} (hix : ixOK S E = true)
    (hlen : E.length ≤ 65535) (h0 : E.head? = some oneF)
    (hpar : enumParK (fun i => (posT E).find i 0) gs E P 0 = true)
    (hcl : enumClK (fun y => (idxT S).find y E.length) E.length gs E = true)
    (hinv : enumInvK gs E = true) : enumOK gs E.toArray P.toArray = true := by
  obtain ⟨hnd, hT⟩ := find_idxT_eq_idxOf hix
  obtain ⟨hPl, hP⟩ := enumParK_spec _ gs E P 0 hpar
  have hcl' := enumClK_spec _ _ gs E hcl
  have hinv' := enumInvK_spec E gs hinv
  have hne : E ≠ [] := by
    intro e
    rw [e] at h0
    exact absurd h0 (by simp)
  have hget : ∀ i, (posT E).find i 0 = E[i]! := fun i => by
    rw [find_posT hlen, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rfl
  unfold enumOK
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.size_toArray,
    List.getElem!_toArray, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    List.all_toArray, List.any_toArray, List.all_toArray', List.any_toArray', List.any_eq_true,
    hashSetOfArray_size,
    hashSetOfArray_contains, List.toList_toArray, List.contains_iff_mem]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simpa using hne
  · obtain ⟨e, E', rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.head?_cons, Option.some.injEq] at h0
    rw [← oneF_eq, ← h0]
    rfl
  · exact hPl
  · intro i hi
    have hp : i < P.length := by rw [hPl]; exact hi
    rcases hP i hi hp with h | ⟨⟨h1, h2⟩, h3⟩
    · exact Or.inl (by simpa using h)
    · right
      rw [getElem!_pos P i hp, getElem!_pos E i hi]
      refine ⟨⟨by simpa using h1, h2⟩, ?_⟩
      rw [h3, mulF_eq, hget, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem!_eq_getElem?_getD]
      rfl
  · rw [List.toFinset_card_of_nodup hnd]
  · intro i hi g hg
    rw [getElem!_pos E i hi, ← mulF_eq]
    have := hcl' _ (List.getElem_mem hi) g hg
    rw [hT] at this
    exact List.idxOf_lt_length_iff.1 this
  · intro g hg
    obtain ⟨e, he, h⟩ := hinv' g hg
    exact ⟨e, he, by rw [← mulF_eq, h, oneF_eq]⟩

end CFSG.KC.C690

end
