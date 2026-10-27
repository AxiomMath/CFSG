
module

public import CFSG.Certificates.Kernel.M24L2.L2FaSound

public section

namespace CFSG.KC.M24L2

open CFSG.Sporadic.Th.Native CFSG.CGT.M24R CFSG.KC.Enum

theorem kList_tabC (x : Nat) : kList (tabC x) = (kListC x).map tabC := by
  unfold kList kListC
  rw [idT_tabC, b0T_eq, compT_tabC]
  simp only [List.map_cons, List.map_nil]

theorem conjIn_tabC (x p : Nat) (L : List Nat) :
    conjIn (tabC x) (tabC p) (L.map tabC) = conjInK x p L := by
  unfold conjIn conjInK
  rw [List.any_map]
  refine congrArg (List.any L) (funext fun k => ?_)
  change (compT 16 (tabC x) (tabC p) == compT 16 (tabC k) (tabC x)) = _
  rw [compT_tabC, compT_tabC, beq_tabC (mulC_lt x p) (mulC_lt k x)]

theorem conjInR_tabC (x p : Nat) (L : List Nat) :
    conjInR (tabC x) (tabC p) (L.map tabC) = conjInRK x p L := by
  unfold conjInR conjInRK
  rw [List.any_map]
  refine congrArg (List.any L) (funext fun k => ?_)
  change (compT 16 (tabC p) (tabC x) == compT 16 (tabC x) (tabC k)) = _
  rw [compT_tabC, compT_tabC, beq_tabC (mulC_lt p x) (mulC_lt x k)]

theorem normK_tabC (L : List Nat) (p q x : Nat) :
    normK (L.map tabC) (tabC p) (tabC q) (tabC x) = normKK L p q x := by
  unfold normK normKK
  rw [conjIn_tabC, conjIn_tabC, conjInR_tabC, conjInR_tabC]

theorem kleinPre_tabC {x : Nat} (hx : x < 2 ^ 20) :
    (mkCtx ()).kleinPre (tabC x) = kleinPreK x := by
  unfold Ctx8.kleinPre kleinPreK
  rw [compT_tabC, idT_beq (mulC_lt x x), b0T_eq, commT_tabC', isTt_tabC hx, compT_tabC,
    isTt_tabC (mulC_lt b0C x), beq_tabC hx b0C_lt]

theorem kleinCheap_tabC (x : Nat) : (mkCtx ()).kleinCheap (tabC x) = kleinCheapK x := by
  unfold Ctx8.kleinCheap kleinCheapK
  have e1 : ∀ k ∈ List.range 16, normK (kList (tabC x)) b0T (tabC x) (mkCtx ()).tt[k]! =
      normKK (kListC x) b0C x (ttC k) := by
    intro k hk
    rw [ctx_tt_tabC (range16 hk), kList_tabC, b0T_eq, normK_tabC]
  have e2 : ∀ k ∈ List.range 16, commT (mkCtx ()).tt[k]! b0T = commK (ttC k) b0C := by
    intro k hk
    rw [ctx_tt_tabC (range16 hk), b0T_eq, commT_tabC']
  have e3 : ∀ k ∈ List.range 16, commT (mkCtx ()).tt[k]! (tabC x) = commK (ttC k) x := by
    intro k hk
    rw [ctx_tt_tabC (range16 hk), commT_tabC']
  have e4 : ∀ k ∈ List.range 16,
      commT (mkCtx ()).tt[k]! (compT 16 b0T (tabC x)) = commK (ttC k) (mulC b0C x) := by
    intro k hk
    rw [ctx_tt_tabC (range16 hk), b0T_eq, compT_tabC, commT_tabC']
  have hC : (List.range 16).countP (fun k =>
      normK (kList (tabC x)) b0T (tabC x) (mkCtx ()).tt[k]!) =
      (List.range 16).countP (fun k => normKK (kListC x) b0C x (ttC k)) :=
    List.countP_congr (fun k hk => by rw [e1 k hk])
  have hA : ((List.range 16).all fun k => !(normK (kList (tabC x)) b0T (tabC x)
      (mkCtx ()).tt[k]!) || (commT (mkCtx ()).tt[k]! b0T && commT (mkCtx ()).tt[k]! (tabC x))) =
      ((List.range 16).all fun k => !(normKK (kListC x) b0C x (ttC k)) ||
        (commK (ttC k) b0C && commK (ttC k) x)) :=
    all_mem_congr fun k hk => by rw [e1 k hk, e2 k hk, e3 k hk]
  have hB : ((List.range 16).all fun k => !(commT (mkCtx ()).tt[k]! b0T ||
      commT (mkCtx ()).tt[k]! (tabC x) || commT (mkCtx ()).tt[k]! (compT 16 b0T (tabC x))) ||
      normK (kList (tabC x)) b0T (tabC x) (mkCtx ()).tt[k]!) =
      ((List.range 16).all fun k => !(commK (ttC k) b0C || commK (ttC k) x ||
        commK (ttC k) (mulC b0C x)) || normKK (kListC x) b0C x (ttC k)) :=
    all_mem_congr fun k hk => by rw [e1 k hk, e2 k hk, e3 k hk, e4 k hk]
  rw [hC, hA, hB]

theorem contains_tabC (L : List Nat) (hL : ∀ a ∈ L, a < 2 ^ 20) {x : Nat} (hx : x < 2 ^ 20) :
    (L.map tabC).contains (tabC x) = L.contains x := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨a, ha, he⟩
    rwa [← tabC_inj (hL a ha) hx he]
  · intro h
    exact ⟨x, h, rfl⟩

theorem isBt_tabC {x : Nat} (hx : x < 2 ^ 20) : isBt (tabC x) = isBtK x := by
  unfold isBt isBtK bList
  rw [idT_tabC, b0T_eq, b1T_eq, b01T_eq]
  exact contains_tabC [idC, b0C, b1C, b01C] (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · decide
    · exact b0C_lt
    · exact b1C_lt
    · exact b01C_lt) hx

theorem refutes_tabC (x y : Nat) : refutes (tabC x) (tabC y) = refutesK x y := by
  unfold refutes refutesK
  rw [b0T_eq, commT_tabC', commT_tabC', compT_tabC, commT_tabC', kList_tabC, normK_tabC]

theorem fbM_spec {G : Nat} {W : List (Nat × Nat)} {m : Nat} (h : fbM G W m = true) :
    ∀ v < 16, fbBody G W (v + 16 * m) = true := by
  intro v hv
  unfold fbM at h
  rcases hl : sqLin m with _ | _
  · unfold fbBody
    have : kleinPreK (v + 16 * m) = false := by
      unfold kleinPreK
      have : Nat.beq (mulC (v + 16 * m) (v + 16 * m)) idC = false := by
        rw [Bool.eq_false_iff]
        intro h1
        have h2 := mulC_lin_eq (Nat.eq_of_beq_eq_true h1)
        rw [show (v + 16 * m) / 16 = m by omega] at h2
        unfold sqLin at hl
        change Nat.beq (mulC (16 * m) (16 * m)) idC = false at hl
        rw [h2] at hl
        simp at hl
      rw [this]
      rfl
    rw [this]
  · rw [hl] at h
    change allN 16 _ = true at h
    rw [CFSG.KS.Raw.Orb.allN_iff] at h
    have := h v hv
    rw [letN_eq] at this
    exact this

theorem fbCheck_of {L : List Nat} (hR : ReachL L) (hL : ∀ m ∈ L, m < 65536) {G : Nat}
    {W : List (Nat × Nat)} (hG : ∀ n, validK G n = true → n ∈ (mkCtx ()).codes)
    (h : ∀ m ∈ L, fbM G W m = true) : fbCheck (mkCtx ()) = true := by
  unfold fbCheck
  simp only [List.all_eq_true]
  intro c hc
  have hlt := ((mem_codes_iff hR).1 hc).1
  have hb := forall_codes hR hL (P := fun c => fbBody G W c = true)
    (fun m hm v hv => fbM_spec (h m hm) v hv) c hc
  rw [tab_of_mem hR hc, kleinPre_tabC hlt, kleinCheap_tabC, isBt_tabC hlt]
  unfold fbBody at hb
  rcases h1 : kleinPreK c with _ | _
  · simp
  rcases h2 : kleinCheapK c with _ | _
  · simp
  rcases h3 : isBtK c with _ | _
  · rw [h1, h2, h3] at hb
    change fbWit G W c = true at hb
    unfold fbWit at hb
    rw [anyL_eq, List.any_eq_true] at hb
    obtain ⟨e, _, he⟩ := hb
    simp only [Bool.and_eq_true, Nat.beq_eq] at he
    obtain ⟨⟨rfl, hv⟩, hr⟩ := he
    have hy := hG e.2 hv
    simp only [Bool.not_true, Bool.false_or, List.any_eq_true]
    exact ⟨e.2, hy, by rw [tab_of_mem hR hy, refutes_tabC]; exact hr⟩
  · simp

end CFSG.KC.M24L2
