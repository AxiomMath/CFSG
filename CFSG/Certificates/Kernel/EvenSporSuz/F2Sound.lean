module

public import Certificates.Data.Kernel.EvenSporSuz.F2
public import CFSG.Certificates.Kernel.EvenSporSuz.SylowTreeSound

public section

namespace CFSG.KC.EvenSporSuz.F2

open CFSG.KC.ONanSmall CFSG.KC.M24G CFSG.KC.Misc.G24 CFSG.KC.Misc.Spec CFSG.KC.EvenSporSuz.Syl

abbrev Mat12 := Matrix (Fin 12) (Fin 12) (ZMod 3)

theorem allBelow_eq {p : Nat → Bool} : ∀ {n : Nat}, allBelow n p = true → ∀ k < n, p k = true
  | 0, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, h, k, hk => by
    have h' : (p n && allBelow n p) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact allBelow_eq h'.2 k hk
    · exact h'.1

theorem getD_one3_mem {L : List Nat} {H : Submonoid Mat12}
    (h : ∀ k < L.length, Canon3 (L.getD k 0) ∧ pkMat3 (L.getD k 0) ∈ H) (k : Nat) :
    Canon3 (L.getD k one3) ∧ pkMat3 (L.getD k one3) ∈ H := by
  by_cases hk : k < L.length
  · have := h k hk
    rwa [List.getD_eq_getElem _ _ hk] at this ⊢
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨canon3_one3.1, canon3_one3.2 ▸ H.one_mem⟩

theorem foldl_mem {H : Submonoid Mat12} (f : Nat → Nat) (hf : ∀ c, Canon3 (f c) ∧ pkMat3 (f c) ∈ H) :
    ∀ (w : List Nat) (acc : Nat), Canon3 acc → pkMat3 acc ∈ H →
      Canon3 (w.foldl (fun acc c => mulF3 acc (f c)) acc) ∧
        pkMat3 (w.foldl (fun acc c => mulF3 acc (f c)) acc) ∈ H
  | [], _, h1, h2 => ⟨h1, h2⟩
  | c :: w, acc, h1, h2 => by
    rw [List.foldl_cons]
    obtain ⟨hc, hm⟩ := canon3_mulF3 h1 (hf c).1
    exact foldl_mem f hf w _ hc (hm ▸ H.mul_mem h2 (hf c).2)

theorem evalL_mem {M I : List Nat} {H : Submonoid Mat12}
    (hM : ∀ k < M.length, Canon3 (M.getD k 0) ∧ pkMat3 (M.getD k 0) ∈ H)
    (hI : ∀ k < I.length, Canon3 (I.getD k 0) ∧ pkMat3 (I.getD k 0) ∈ H) (w : List Nat) :
    Canon3 (evalL M I w) ∧ pkMat3 (evalL M I w) ∈ H := by
  refine foldl_mem (fun c => bif Nat.beq (c % 2) 0 then M.getD (c / 2) one3
    else I.getD (c / 2) one3) (fun c => ?_) w one3 canon3_one3.1 (canon3_one3.2 ▸ H.one_mem)
  cases Nat.beq (c % 2) 0
  · exact getD_one3_mem hI _
  · exact getD_one3_mem hM _

theorem invK_sound {M I : List Nat} {n : Nat} (h : invK M I n = true) :
    M.length = n ∧ I.length = n ∧ ∀ k < n, Canon3 (M.getD k 0) ∧ Canon3 (I.getD k 0) ∧
      pkMat3 (M.getD k 0) * pkMat3 (I.getD k 0) = 1 := by
  simp only [invK, Bool.and_eq_true, Nat.beq_eq] at h
  refine ⟨h.1.1, h.1.2, fun k hk => ?_⟩
  have hk' := allBelow_eq h.2 k hk
  simp only [Bool.and_eq_true, Nat.beq_eq] at hk'
  have hM := canon3_of_canonK hk'.1.1
  have hI := canon3_of_canonK hk'.1.2
  refine ⟨hM, hI, ?_⟩
  rw [← (canon3_mulF3 hM hI).2, hk'.2, canon3_one3.2]

theorem comK_sound {MU IU MV IV : List Nat} {WU WV : List (List Nat)} {N : List Nat} {n : Nat}
    (h : comK MU IU MV IV WU WV N n = true) :
    N.length = n ∧ ∀ j < n, Canon3 (N.getD j 0) ∧
      mulF3 (mulF3 (N.getD j 0) (evalL MV IV (WV.getD j []))) (evalL MU IU (WU.getD j [])) =
        mulF3 (evalL MU IU (WU.getD j [])) (evalL MV IV (WV.getD j [])) := by
  simp only [comK, Bool.and_eq_true, Nat.beq_eq] at h
  refine ⟨h.1, fun j hj => ?_⟩
  have hj' := allBelow_eq h.2 j hj
  simp only [letN_eq, Bool.and_eq_true, Nat.beq_eq] at hj'
  exact ⟨canon3_of_canonK hj'.1, hj'.2⟩

theorem memK_sound {M I : List Nat} {W : List (List Nat)} {f : Nat → Nat} {n : Nat}
    (h : memK M I W f n = true) : ∀ t < n, evalL M I (W.getD t []) = f t := by
  intro t ht
  have := allBelow_eq h t ht
  simpa only [Nat.beq_eq] using this

theorem cenB_sound {G : List Nat} {n e : Nat} (h : cenB G n e = true) :
    ∀ k < n, mulF3 e (G.getD k 0) = mulF3 (G.getD k 0) e := by
  intro k hk
  have := allBelow_eq h k hk
  simpa only [Nat.beq_eq] using this

theorem hasK_sound {x : Nat} : ∀ {E : List (Nat × Nat)}, hasK x E = true → ∃ p ∈ E, p.1 = x
  | [], h => by cases h
  | p :: E, h => by
    have h' : (Nat.beq p.1 x || hasK x E) = true := h
    rw [Bool.or_eq_true, Nat.beq_eq] at h'
    rcases h' with h' | h'
    · exact ⟨p, List.mem_cons_self, h'⟩
    · obtain ⟨q, hq, hq'⟩ := hasK_sound h'
      exact ⟨q, List.mem_cons_of_mem _ hq, hq'⟩

theorem entsK_sound {T : KTree (Nat × Nat)} {G GI : List Nat} {n : Nat} :
    ∀ {E : List (Nat × Nat)}, entsK T G GI n E = true → ∀ p ∈ E, entK T G GI n p.1 p.2 = true
  | [], _, p, hp => absurd hp List.not_mem_nil
  | q :: E, h, p, hp => by
    have h' : (entK T G GI n q.1 q.2 && entsK T G GI n E) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h'.1
    · exact entsK_sound h'.2 p hp

theorem enum_mem {E : List (Nat × Nat)} {G GI : List Nat} {n : Nat}
    (hG : ∀ k < n, Canon3 (GI.getD k 0) ∧ pkMat3 (GI.getD k 0) * pkMat3 (G.getD k 0) = 1)
    (hall : ∀ p ∈ E, entK (treeOf E) G GI n p.1 p.2 = true) {H : Submonoid Mat12}
    (hH : ∀ k < n, pkMat3 (G.getD k 0) ∈ H) :
    ∀ d, ∀ p ∈ E, p.2 / 8 = d → Canon3 p.1 ∧ pkMat3 p.1 ∈ H := by
  intro d
  induction d with
  | zero =>
    intro p hp hd
    have h := hall p hp
    simp only [entK, Bool.and_eq_true, hd, Nat.beq_refl, cond_true, Nat.beq_eq] at h
    refine ⟨canon3_of_canonK h.1.1, ?_⟩
    rw [h.2, canon3_one3.2]
    exact H.one_mem
  | succ d ih =>
    intro p hp hd
    have h := hall p hp
    have hb : Nat.beq (p.2 / 8) 0 = false := by rw [hd]; rfl
    simp only [entK, Bool.and_eq_true, hb, cond_false, Nat.blt_eq] at h
    obtain ⟨⟨hc, -⟩, hk, hpar⟩ := h
    have hce := canon3_of_canonK hc
    obtain ⟨hgi, hm⟩ := hG _ hk
    rcases hf : findK (mulF3 p.1 (GI.getD (p.2 % 8) 0)) (treeOf E) with _ | c
    · rw [hf] at hpar
      cases hpar
    · rw [hf] at hpar
      have hmem := findK_treeOf hf
      have hpar' : c / 8 + 1 = p.2 / 8 := Nat.eq_of_beq_eq_true hpar
      obtain ⟨-, hq⟩ := ih _ hmem (by simp only; omega)
      refine ⟨hce, ?_⟩
      have hmul := (canon3_mulF3 hce hgi).2
      have : pkMat3 p.1 =
          pkMat3 (mulF3 p.1 (GI.getD (p.2 % 8) 0)) * pkMat3 (G.getD (p.2 % 8) 0) := by
        rw [hmul, Matrix.mul_assoc, hm, Matrix.mul_one]
      rw [this]
      exact H.mul_mem hq (hH _ hk)

theorem enumK_sound {E : List (Nat × Nat)} {G GI : List Nat} {n m : Nat}
    (h : enumK (treeOf E) G GI n m E = true)
    (hG : ∀ k < n, Canon3 (GI.getD k 0) ∧ pkMat3 (GI.getD k 0) * pkMat3 (G.getD k 0) = 1) :
    E.length = m ∧ (E.map Prod.fst).Nodup ∧ (∃ p ∈ E, p.1 = one3) ∧ (∀ p ∈ E, Canon3 p.1) ∧
      (∀ H : Submonoid Mat12, (∀ k < n, pkMat3 (G.getD k 0) ∈ H) → ∀ p ∈ E, pkMat3 p.1 ∈ H) ∧
      ∀ p ∈ E, ∀ k < n, ∃ q ∈ E, q.1 = mulF3 p.1 (G.getD k 0) := by
  simp only [enumK, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨hl, hinc⟩, hone⟩, hents⟩ := h
  have hall := entsK_sound hents
  refine ⟨hl, nodup_of_incK hinc, hasK_sound hone, fun p hp => ?_, fun H hH p hp =>
    (enum_mem hG hall hH _ p hp rfl).2, fun p hp k hk => ?_⟩
  · have h := hall p hp
    simp only [entK, Bool.and_eq_true] at h
    exact canon3_of_canonK h.1.1
  · have h := hall p hp
    simp only [entK, Bool.and_eq_true] at h
    have h2 := allBelow_eq h.1.2 k hk
    obtain ⟨v, hv⟩ := isSome_findK_treeOf h2
    exact ⟨_, hv, rfl⟩

theorem cenK_sound {G : List Nat} {n : Nat} : ∀ {E : List (Nat × Nat)} {a : Nat},
    cenK G n E a = true → E.countP (fun p => cenB G n p.1) = a ∧
      ∀ p ∈ E, cenB G n p.1 = true → mulF3 p.1 p.1 = one3
  | [], a, h => by
    have h' : Nat.beq a 0 = true := h
    rw [Nat.beq_eq] at h'
    simp [h']
  | p :: E, a, h => by
    have h' : Bool.rec (motive := fun _ => Bool) (cenK G n E a)
        (Nat.beq (mulF3 p.1 p.1) one3 && Nat.blt 0 a && letN (Nat.sub a 1) (cenK G n E))
        (cenB G n p.1) = true := h
    rcases hp : cenB G n p.1 with _ | _
    · rw [hp] at h'
      obtain ⟨h1, h2⟩ := cenK_sound h'
      refine ⟨by rw [List.countP_cons, h1, hp]; rfl, fun q hq hc => ?_⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · rw [hp] at hc
        cases hc
      · exact h2 q hq hc
    · rw [hp] at h'
      simp only [letN_eq, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Nat.sub_eq] at h'
      obtain ⟨⟨hsq, ha⟩, hE⟩ := h'
      obtain ⟨h1, h2⟩ := cenK_sound hE
      refine ⟨by rw [List.countP_cons, h1, hp]; simp only [if_true]; omega, fun q hq hc => ?_⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hsq
      · exact h2 q hq hc

end CFSG.KC.EvenSporSuz.F2
