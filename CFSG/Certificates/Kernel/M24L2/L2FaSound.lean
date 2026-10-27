
module

public import CFSG.Certificates.Kernel.M24L2.L2Sound
public import CFSG.Certificates.Kernel.M24L2.GrpSound
public import CFSG.Certificates.Kernel.M24L2.R3Sound

public section

namespace CFSG.KC.M24L2

open CFSG.Sporadic.Th.Native CFSG.CGT.M24R CFSG.KC.Enum

theorem mulC_lin_eq {c : Nat} (h : mulC c c = idC) :
    mulC (16 * (c / 16)) (16 * (c / 16)) = idC := by
  have e1 := mulC_div16 c c
  rw [h] at e1
  have h3 := mulC_mod16_lin (c / 16) (c / 16)
  have h4 := mulC_lt (16 * (c / 16)) (16 * (c / 16))
  change 541200 / 16 = _ at e1
  change _ = 541200
  omega

theorem faM_spec {G : Nat} {W : List (Nat × Nat)} {m : Nat} (h : faM G W m = true) :
    ∀ v < 16, faBody G W (v + 16 * m) = true := by
  intro v hv
  unfold faM at h
  rcases hl : sqLin m with _ | _
  · unfold faBody
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
  · rw [hl] at h
    change allN 16 _ = true at h
    rw [CFSG.KS.Raw.Orb.allN_iff] at h
    have := h v hv
    rw [letN_eq] at this
    exact this

theorem commCount_tabC (c : Nat) : (mkCtx ()).commCount (tabC c) = commCountK c := by
  unfold Ctx8.commCount commCountK
  refine List.countP_congr fun k hk => ?_
  rw [ctx_tt_tabC (range16 hk), commT_tabC']

theorem faMap_eq (vc : List Nat) : faMap (mkCtx ()) vc = vc.foldl (fun arr c =>
    arr.set! (codeOf (compT 16 (compT 16 ((mkCtx ()).tab c) b0T)
      (invT 16 ((mkCtx ()).tab c)))) c) (Array.replicate 1048576 0) := rfl

theorem witK_spec {G p : Nat} {W : List (Nat × Nat)} {x : Nat} (h : witK G p W x = true) :
    ∃ n, validK G n = true ∧ mulC n p = mulC x n := by
  unfold witK at h
  rw [anyL_eq, List.any_eq_true] at h
  obtain ⟨e, _, he⟩ := h
  simp only [Bool.and_eq_true, Nat.beq_eq] at he
  exact ⟨e.2, he.1.2, he.2⟩

theorem faCheck_of {L : List Nat} (hR : ReachL L) (hL : ∀ m ∈ L, m < 65536) {G : Nat}
    {W : List (Nat × Nat)} (hG : ∀ n, validK G n = true → n ∈ (mkCtx ()).codes)
    (h : ∀ m ∈ L, faM G W m = true) : faCheck (mkCtx ()) = true := by
  unfold faCheck
  simp only [List.all_eq_true]
  intro c hc
  have hlt := ((mem_codes_iff hR).1 hc).1
  have hb := forall_codes hR hL (P := fun c => faBody G W c = true)
    (fun m hm v hv => faM_spec (h m hm) v hv) c hc
  rw [tab_of_mem hR hc, compT_tabC, idT_beq (mulC_lt _ _), isTt_tabC hlt, commCount_tabC,
    codeOf_tabC hlt]
  unfold faBody at hb
  rcases h1 : Nat.beq (mulC c c) idC with _ | _
  · simp
  rcases h2 : isTtK c with _ | _
  · rcases h3 : decide (4 < commCountK c) with _ | _
    · rw [h1, h2] at hb
      have h3' : Nat.blt 4 (commCountK c) = false := by
        rw [Bool.eq_false_iff]
        intro h4
        rw [Nat.blt_eq] at h4
        simp [h4] at h3
      rw [h3'] at hb
      obtain ⟨n0, hv0, hn0⟩ := witK_spec hb
      have hn0c := hG n0 hv0
      have hkey : ∀ n ∈ (mkCtx ()).codes, codeOf (compT 16 (compT 16 ((mkCtx ()).tab n) b0T)
          (invT 16 ((mkCtx ()).tab n))) = conjKey n (tabC b0C) := by
        intro n hn
        rw [tab_of_mem hR hn, b0T_eq]
        rfl
      obtain ⟨n', hn', hk', hfm⟩ := foldSet_get (key := fun n => codeOf (compT 16 (compT 16
        ((mkCtx ()).tab n) b0T) (invT 16 ((mkCtx ()).tab n)))) (mkCtx ()).codes
        (Array.replicate 1048576 0) (by simpa using hlt)
        ⟨n0, hn0c, by rw [hkey n0 hn0c]; exact (conjKey_eq hR hn0c b0C_lt hlt).2 hn0⟩
      rw [hkey n' hn'] at hk'
      have hconj := (conjKey_eq hR hn' b0C_lt hlt).1 hk'
      rw [faMap_eq, hfm, tab_of_mem hR hn', b0T_eq, compT_tabC, compT_tabC,
        beq_tabC (mulC_lt _ _) (mulC_lt _ _), hconj]
      have hn'lt := ((mem_codes_iff hR).1 hn').1
      simp only [Bool.not_true, Bool.false_or, Nat.beq_refl, Bool.and_true, decide_eq_true_eq]
      exact hn'lt
    · simp
  · simp

end CFSG.KC.M24L2
