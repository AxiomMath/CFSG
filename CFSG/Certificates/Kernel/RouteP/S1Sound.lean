module

public import Certificates.Data.Kernel.RouteP.S1Sets
public import CFSG.Certificates.Kernel.RouteP.MonoSet

public section

namespace CFSG.KS.RouteP

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.RouteP CFSG.KC.Benes CFSG.KS.Fi24Net

theorem s1_and {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

theorem s1_or {a b : Bool} (h : orB a b = true) : a = true ∨ b = true := by
  cases a <;> cases b <;> first | exact Or.inl rfl | exact Or.inr rfl | exact absurd h (by decide)

theorem s1_not {a : Bool} (h : notB a = true) : a = false := by
  cases a <;> first | rfl | exact absurd h (by decide)

theorem s1_letB (v : Nat) (k : Nat → Bool) : letB v k = k v := by cases v <;> rfl

theorem s1_memS_land (a b N : Nat) : memS (Nat.land a b) N = (memS a N && memS b N) := by
  unfold memS
  change (a &&& b).testBit _ = _
  rw [Nat.testBit_and]

theorem s1_memS_xor (a b N : Nat) : memS (Nat.xor a b) N = (memS a N ^^ memS b N) := by
  unfold memS
  change (a ^^^ b).testBit _ = _
  rw [Nat.testBit_xor]

theorem s1_memS_zero (N : Nat) : memS 0 N = false := Nat.zero_testBit _

theorem s1_subP {a b : Nat} (h : subP a b = true) {N : Nat} (hN : memS a N = true) :
    memS b N = true := by
  have e : Nat.land a b = a := Nat.eq_of_beq_eq_true h
  have h2 := s1_memS_land a b N
  rw [e, hN] at h2
  simpa using h2.symm

theorem s1_allL {α : Type} {f : α → Bool} : ∀ {l : List α}, allL l f = true → ∀ a ∈ l, f a = true
  | [], _, a, ha => absurd ha List.not_mem_nil
  | b :: l, h, a, ha => by
    obtain ⟨h1, h2⟩ := s1_and h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h1
    · exact s1_allL h2 a ha

theorem s1CoverCore_spec {NWP : Nat → Nat → Nat} {KAP KBP : Nat → Nat} {NWO : Nat → Nat → Nat}
    {KAO KBO : Nat → Nat} {ag tY : List Int} {y G0 A O : Nat}
    (h : s1CoverCore NWP KAP KBP NWO KAO KBO ag tY y G0 A O = true) :
    ptOK NWP KAP KBP tY 1479 y = true ∧ memS G0 y = true ∧ memS A y = false ∧
      closedS NWO KAO KBO ag O = true ∧ Nat.land A O = 0 ∧ memS A 1479 = false ∧
      memS O 1479 = false ∧ (∀ N, memS A N = true → memS G0 N = true) ∧
      (∀ N, memS O N = true → memS G0 N = true) ∧
      ∀ N, memS G0 N = true →
        memS (single 1479) N = true ∨ memS A N = true ∨ memS O N = true := by
  unfold s1CoverCore at h
  obtain ⟨h1, h⟩ := s1_and h
  obtain ⟨h2, h⟩ := s1_and h
  obtain ⟨h3, h⟩ := s1_and h
  obtain ⟨h4, h⟩ := s1_and h
  obtain ⟨h5, h⟩ := s1_and h
  obtain ⟨h6, h⟩ := s1_and h
  obtain ⟨h7, h⟩ := s1_and h
  obtain ⟨h8, h⟩ := s1_and h
  obtain ⟨h9, h10⟩ := s1_and h
  refine ⟨h1, h2, s1_not h3, h4, Nat.eq_of_beq_eq_true h5, s1_not h6, s1_not h7,
    fun N hN => s1_subP h8 hN, fun N hN => s1_subP h9 hN, fun N hN => ?_⟩
  have h11 := s1_subP h10 hN
  rw [memS_lor, memS_lor] at h11
  simpa only [Bool.or_eq_true] using h11

theorem s1HubsGo_spec {NWO : Nat → Nat → Nat} {KAO KBO : Nat → Nat} {B2 A By : Nat}
    {fin : Nat → Bool} : ∀ (hs : List (Nat × Nat × List Int)) (prev : List Nat) (U : Nat),
    s1HubsGo NWO KAO KBO B2 A By fin hs prev U = true →
    (∀ i (hi : i < hs.length), ptOK NWO KAO KBO hs[i].2.2 99705 hs[i].1 = true ∧
      memS A hs[i].1 = true ∧ memS By hs[i].1 = true ∧
      (prev.length + i = 0 ∨ (hs[i].2.1 < prev.length + i ∧
        memS ((prev ++ hs.map fun e => imgW NWO KAO KBO e.2.2 B2).getD hs[i].2.1 0) hs[i].1 =
          true))) ∧
    ∃ V, (∀ N, memS V N = true →
      memS U N = true ∨ ∃ e ∈ hs, memS (imgW NWO KAO KBO e.2.2 B2) N = true) ∧ fin V = true
  | [], prev, U, h => ⟨fun i hi => absurd hi (Nat.not_lt_zero _), U, fun _ hN => Or.inl hN, h⟩
  | e :: hs, prev, U, h => by
    have h' : letB (imgW NWO KAO KBO e.2.2 B2) (fun N =>
        andB (ptOK NWO KAO KBO e.2.2 99705 e.1)
          (andB (memP A e.1) (andB (memP By e.1)
            (andB (orB (Nat.beq prev.length 0)
                (andB (Nat.blt e.2.1 prev.length) (memP (prev.getD e.2.1 0) e.1)))
              (s1HubsGo NWO KAO KBO B2 A By fin hs (prev ++ [N]) (Nat.lor U N)))))) = true := h
    rw [s1_letB] at h'
    obtain ⟨h1, h'⟩ := s1_and h'
    obtain ⟨h2, h'⟩ := s1_and h'
    obtain ⟨h3, h'⟩ := s1_and h'
    obtain ⟨h4, h5⟩ := s1_and h'
    obtain ⟨ih1, V, hV, hfin⟩ := s1HubsGo_spec hs _ _ h5
    have happ : prev ++ (e :: hs).map (fun e => imgW NWO KAO KBO e.2.2 B2) =
        (prev ++ [imgW NWO KAO KBO e.2.2 B2]) ++ hs.map fun e => imgW NWO KAO KBO e.2.2 B2 := by
      simp
    refine ⟨fun i hi => ?_, V, fun N hN => ?_, hfin⟩
    · rcases i with _ | i
      · refine ⟨h1, h2, h3, ?_⟩
        rcases s1_or h4 with h4 | h4
        · exact Or.inl (by simpa using Nat.eq_of_beq_eq_true h4)
        · obtain ⟨h6, h7⟩ := s1_and h4
          have hlt : e.2.1 < prev.length := Eq.mp Nat.blt_eq h6
          refine Or.inr ⟨by simpa using hlt, ?_⟩
          change memS ((prev ++ _).getD e.2.1 0) e.1 = true
          rw [List.getD_append _ _ _ _ hlt]
          exact h7
      · have hi' : i < hs.length := by simpa using hi
        obtain ⟨g1, g2, g3, g4⟩ := ih1 i hi'
        refine ⟨g1, g2, g3, ?_⟩
        rw [happ]
        simp only [List.length_append, List.length_singleton] at g4
        rcases g4 with g4 | g4
        · omega
        · right
          refine ⟨by simp only [List.getElem_cons_succ]; omega, ?_⟩
          simpa only [List.getElem_cons_succ] using g4.2
    · rcases hV N hN with hU | ⟨e', he', hm⟩
      · rw [memS_lor, Bool.or_eq_true] at hU
        rcases hU with hU | hU
        · exact Or.inl hU
        · exact Or.inr ⟨e, List.mem_cons_self, hU⟩
      · exact Or.inr ⟨e', List.mem_cons_of_mem e he', hm⟩

theorem s1HubsOK_spec {NWP : Nat → Nat → Nat} {KAP KBP : Nat → Nat} {NWO : Nat → Nat → Nat}
    {KAO KBO : Nat → Nat} {ag tY t2 : List Int} {w : Nat} {hs : List (Nat × Nat × List Int)}
    (h : s1HubsOK NWP KAP KBP NWO KAO KBO ag tY t2 w hs = true) :
    ptOK NWP KAP KBP t2 1479 99705 = true ∧
      memS (closeS NWO KAO KBO ag 10 (single 99705)) w = true ∧
      memS (imgW NWP KAP KBP tY (closeS NWO KAO KBO ag 10 (single 99705))) w = true ∧
      s1HubsGo NWO KAO KBO (imgW NWP KAP KBP t2 (closeS NWO KAO KBO ag 10 (single 99705)))
        (closeS NWO KAO KBO ag 10 (single 99705))
        (imgW NWP KAP KBP tY (closeS NWO KAO KBO ag 10 (single 99705)))
        (fun U => andB (subP (Nat.land (closeS NWO KAO KBO ag 10 (single 99705))
            (imgW NWP KAP KBP tY (closeS NWO KAO KBO ag 10 (single 99705))))
            (Nat.lor (single (hs.headD (0, 0, [])).1) U))
          (subP (Nat.xor (imgW NWP KAP KBP tY (closeS NWO KAO KBO ag 10 (single 99705)))
            (Nat.land (closeS NWO KAO KBO ag 10 (single 99705))
              (imgW NWP KAP KBP tY (closeS NWO KAO KBO ag 10 (single 99705))))) U)) hs [] 0 =
        true := by
  unfold s1HubsOK at h
  rw [s1_letB, s1_letB, s1_letB, s1_letB, s1_letB] at h
  obtain ⟨h1, h⟩ := s1_and h
  obtain ⟨h2, h⟩ := s1_and h
  obtain ⟨h3, h4⟩ := s1_and h
  exact ⟨h1, h2, h3, h4⟩

theorem s1StabOK_spec {NWP : Nat → Nat → Nat} {KAP KBP : Nat → Nat} {NWO : Nat → Nat → Nat}
    {KAO KBO : Nat → Nat} {ag t2 : List Int} {ss : List (List Int)} {c0 rC : Nat}
    (h : s1StabOK NWP KAP KBP NWO KAO KBO ag t2 ss c0 rC = true) :
    ptOK NWP KAP KBP t2 1479 99705 = true ∧ (∀ s ∈ ss, ptOK NWO KAO KBO s 99705 99705 = true) ∧
      ∀ N, memS (closeS NWO KAO KBO ag 10 (single 99705)) N = true →
        memS (imgW NWP KAP KBP t2 (closeS NWO KAO KBO ag 10 (single 99705))) N = true →
        memS (closeW NWO KAO KBO ss rC (single c0)) N = true := by
  unfold s1StabOK at h
  rw [s1_letB, s1_letB] at h
  obtain ⟨h1, h⟩ := s1_and h
  obtain ⟨h2, h3⟩ := s1_and h
  refine ⟨h1, s1_allL h2, fun N hA hB => s1_subP h3 ?_⟩
  rw [s1_memS_land, hA, hB]
  rfl

end CFSG.KS.RouteP

end
