module

public import Certificates.Data.Kernel.McLThree.Defs
public import CFSG.Certificates.Kernel.McLNineSound

public section

namespace CFSG.KS.McLThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.McLAS CFSG.KS.Mathieu CFSG.KS.McLNine

@[expose] def p0 : Fin 275 := ⟨200, by decide⟩

@[expose] def q0 : Fin 275 := ⟨262, by decide⟩

@[expose] def q1 : Fin 275 := ⟨272, by decide⟩

@[expose] def O2 : Set (Fin 275) := {q0, q1}

@[expose] def S3 : Set (Fin 275) := {p0, q0, q1}

theorem bIfF_iff {b r : Bool} : bIf(b, false, r) = true ↔ b = false ∧ r = true := by
  cases b <;> cases r <;> decide

theorem mem_O2 {x : Fin 275} (h : inO2 x.val = true) : x ∈ O2 := by
  unfold inO2 at h
  simp only [O2, q0, q1, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff]
  cases e : Nat.beq x.val 262
  · rw [e] at h
    exact Or.inr (Nat.eq_of_beq_eq_true h)
  · exact Or.inl (Nat.eq_of_beq_eq_true e)

theorem mem_S3 {x : Fin 275} (h : inS x.val = true) : x ∈ S3 := by
  unfold inS at h
  cases e : Nat.beq x.val 200
  · rw [e] at h
    have h2 := mem_O2 h
    simp only [O2, Set.mem_insert_iff, Set.mem_singleton_iff] at h2
    simp only [S3, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr h2
  · simp only [S3, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inl (Fin.ext (Nat.eq_of_beq_eq_true e))

theorem ne3_spec {x y z : Nat} (h : ne3 x y z = true) : x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  unfold ne3 at h
  obtain ⟨h1, h2⟩ := bIfF_iff.1 h
  obtain ⟨h3, h4⟩ := bIfF_iff.1 h2
  obtain ⟨h5, -⟩ := bIfF_iff.1 h4
  exact ⟨fun e => by rw [e, Nat.beq_refl] at h1; exact absurd h1 (by decide),
    fun e => by rw [e, Nat.beq_refl] at h3; exact absurd h3 (by decide),
    fun e => by rw [e, Nat.beq_refl] at h5; exact absurd h5 (by decide)⟩

variable {F G : Nat → Nat} {g : Nat → Equiv.Perm (Fin 275)}

theorem walk_fin (hF : ∀ k, 4 ≤ k → k ≤ 6 → PR (F k) (g k)) {w : List Nat} (hw : Letters w)
    (x : Fin 275) : walkK F w x.val = (wP g w x : Nat) :=
  walk_eq hF w hw x.2

theorem gpt_eq {ws : List (List Nat)} (hws : ws.length = 3)
    (hG : ∀ j < 3, PR (G j) (wP g (ws.getD j []))) {j : Nat} (hj : j < 4) (x : Fin 275) :
    gpt G j x.val = (wP g (ws.getD j []) x : Nat) := by
  unfold gpt
  cases hb : Nat.beq j 3
  · have hj3 : j < 3 := by
      rcases Nat.lt_or_ge j 3 with h | h
      · exact h
      · have : j = 3 := by omega
        rw [this] at hb
        exact absurd hb (by decide)
    exact (hG j hj3).pg x.2
  · have e : j = 3 := Nat.eq_of_beq_eq_true hb
    subst e
    rw [List.getD_eq_default _ _ (by omega)]
    simp [wP]

theorem fixK_spec : ∀ ws : List (List Nat), fixK F ws = true →
    ∀ w ∈ ws, walkK F w 200 = 200
  | [], _, w, hw => absurd hw List.not_mem_nil
  | v :: vs, h, w, hw => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    rcases List.mem_cons.1 hw with rfl | hw'
    · exact Nat.eq_of_beq_eq_true h1
    · exact fixK_spec vs h2 w hw'

theorem difAllK_spec {w : List Nat} : ∀ vs : List (List Nat), difAllK F w vs = true →
    ∀ v ∈ vs, difK F w v = true
  | [], _, v, hv => absurd hv List.not_mem_nil
  | u :: us, h, v, hv => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    rcases List.mem_cons.1 hv with rfl | hv'
    · exact h1
    · exact difAllK_spec us h2 v hv'

theorem pairK_spec : ∀ ws : List (List Nat), pairK F ws = true →
    ws.Pairwise (fun w v => difK F w v = true)
  | [], _ => List.Pairwise.nil
  | w :: ws, h => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    exact List.Pairwise.cons (difAllK_spec ws h1) (pairK_spec ws h2)

theorem difK_spec {w v : List Nat} (h : difK F w v = true) :
    ¬(walkK F w 262 = walkK F v 262 ∧ walkK F w 272 = walkK F v 272) ∧
      ¬(walkK F w 262 = walkK F v 272 ∧ walkK F w 272 = walkK F v 262) := by
  unfold difK at h
  obtain ⟨h1, h2⟩ := bIfF_iff.1 h
  obtain ⟨h3, -⟩ := bIfF_iff.1 h2
  refine ⟨fun ⟨e1, e2⟩ => ?_, fun ⟨e1, e2⟩ => ?_⟩
  · have e1' : Nat.beq (walkK F w (nat_lit 262)) (walkK F v (nat_lit 262)) = true :=
      Nat.beq_eq.mpr e1
    have e2' : Nat.beq (walkK F w (nat_lit 272)) (walkK F v (nat_lit 272)) = true :=
      Nat.beq_eq.mpr e2
    rw [e1', e2'] at h1
    exact absurd h1 (by decide)
  · have e1' : Nat.beq (walkK F w (nat_lit 262)) (walkK F v (nat_lit 272)) = true :=
      Nat.beq_eq.mpr e1
    have e2' : Nat.beq (walkK F w (nat_lit 272)) (walkK F v (nat_lit 262)) = true :=
      Nat.beq_eq.mpr e2
    rw [e1', e2'] at h3
    exact absurd h3 (by decide)

theorem stabK_spec (hF : ∀ k, 4 ≤ k → k ≤ 6 → PR (F k) (g k)) {w : List Nat} (hw : Letters w)
    (h : stabK F w = true) : ∀ s ∈ S3, wP g w s ∈ S3 := by
  obtain ⟨h1, h2, h3⟩ := (by simpa only [stabK, bAnd_iff] using h :
    inS (walkK F w 200) = true ∧ inS (walkK F w 262) = true ∧ inS (walkK F w 272) = true)
  intro s hs
  simp only [S3, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl
  · exact mem_S3 (by rw [← walk_fin hF hw]; exact h1)
  · exact mem_S3 (by rw [← walk_fin hF hw]; exact h2)
  · exact mem_S3 (by rw [← walk_fin hF hw]; exact h3)

theorem mcl3K_sound {ws : List (List Nat)} {WA WB WC : List Nat} {jw : Nat}
    {p0w : List (List Nat)} {m0 m1 wa wg : List Nat}
    (hF : ∀ k, 4 ≤ k → k ≤ 6 → PR (F k) (g k)) (hws : ws.length = 3)
    (hwl : ∀ w ∈ ws, Letters w) (hp : ∀ w ∈ p0w, Letters w) (hm0 : Letters m0)
    (hm1 : Letters m1) (hwa : Letters wa) (hwg : Letters wg)
    (h : mcl3K F G ws WA WB WC jw p0w m0 m1 wa wg = true) :
    (∀ j < 3, wP g (ws.getD j []) q0 ∈ O2 ∧ wP g (ws.getD j []) q1 ∈ O2) ∧
    (jw < 3 ∧ wP g (ws.getD jw []) q0 = q1) ∧
    (∀ q : Fin 275, q ∉ O2 → (∀ j < 3, wP g (ws.getD j []) q = q) ∨
      ∃ a < 4, ∃ b < 4, ∃ c < 4, q ≠ wP g (ws.getD a []) q ∧
        q ≠ wP g (ws.getD b []) (wP g (ws.getD c []) q) ∧
        wP g (ws.getD a []) q ≠ wP g (ws.getD b []) (wP g (ws.getD c []) q)) ∧
    (∀ w ∈ p0w, wP g w p0 = p0) ∧
    p0w.Pairwise (fun w v => ¬(wP g w q0 = wP g v q0 ∧ wP g w q1 = wP g v q1) ∧
      ¬(wP g w q0 = wP g v q1 ∧ wP g w q1 = wP g v q0)) ∧
    (∀ s ∈ S3, wP g m0 s ∈ S3) ∧ (∀ s ∈ S3, wP g m1 s ∈ S3) ∧
    wP g m0 p0 = q0 ∧ wP g m1 p0 = q1 ∧
    (∀ s ∈ S3, wP g wa s ∈ S3) ∧ wP g wa ^ 3 = 1 ∧ wP g wa ≠ 1 ∧
    wP g wg * wP g wa = wP g wa * wP g wa * wP g wg := by
  obtain ⟨hw, ho2, horb, hfix, hpair, hs0, hs1, hm0p, hm1p, hag⟩ :=
    (by simpa only [mcl3K, bAnd_iff] using h :
      wordsK F G ws 0 = true ∧ o2K G jw = true ∧
      allN 275 (fun q => orbQ G q (nget WA q) (nget WB q) (nget WC q)) = true ∧
      fixK F p0w = true ∧ pairK F p0w = true ∧ stabK F m0 = true ∧ stabK F m1 = true ∧
      Nat.beq (walkK F m0 200) 262 = true ∧ Nat.beq (walkK F m1 200) 272 = true ∧
      agK F wa wg = true)
  have hG : ∀ j < 3, PR (G j) (wP g (ws.getD j [])) := by
    intro j hj
    have e := wordsK_spec ws 0 hw j (by omega)
    rw [Nat.zero_add] at e
    rw [e]
    exact PR.word hF _ (by
      have hm : ws.getD j [] ∈ ws := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      exact hwl _ hm)
  obtain ⟨ho2a, hjw, hjw2⟩ := (by simpa only [o2K, bAnd_iff] using ho2 :
    allN 3 (fun j => bAnd(inO2 (gpt G j 262), inO2 (gpt G j 272))) = true ∧
      Nat.blt jw 3 = true ∧ Nat.beq (gpt G jw 262) 272 = true)
  have hjw' : jw < 3 := Nat.blt_eq.mp hjw
  refine ⟨?_, ⟨hjw', ?_⟩, ?_, ?_, ?_, stabK_spec hF hm0 hs0, stabK_spec hF hm1 hs1, ?_, ?_, ?_⟩
  ·
    intro j hj
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec ho2a j hj)
    exact ⟨mem_O2 (by rw [← gpt_eq hws hG (by omega)]; exact h1),
      mem_O2 (by rw [← gpt_eq hws hG (by omega)]; exact h2)⟩
  ·
    apply Fin.ext
    rw [← gpt_eq hws hG (by omega)]
    exact Nat.eq_of_beq_eq_true hjw2
  ·
    intro q hq
    have hb := allN_spec horb q.val q.2
    have hq2 : inO2 q.val = false := by
      cases e : inO2 q.val
      · rfl
      · exact absurd (mem_O2 e) hq
    unfold orbQ at hb
    rw [hq2] at hb
    cases e4 : Nat.beq (nget WA q.val) 4
    · rw [e4] at hb
      obtain ⟨ha, hb', hc, hne⟩ := (by simpa only [bAnd_iff] using hb :
        Nat.blt (nget WA q.val) 4 = true ∧ Nat.blt (nget WB q.val) 4 = true ∧
          Nat.blt (nget WC q.val) 4 = true ∧
          ne3 q.val (gpt G (nget WA q.val) q.val)
            (gpt G (nget WB q.val) (gpt G (nget WC q.val) q.val)) = true)
      have ha' := Nat.blt_eq.mp ha
      have hb'' := Nat.blt_eq.mp hb'
      have hc' := Nat.blt_eq.mp hc
      right
      refine ⟨_, ha', _, hb'', _, hc', ?_⟩
      rw [gpt_eq hws hG hc' q, gpt_eq hws hG hb'' (wP g (ws.getD (nget WC q.val) []) q),
        gpt_eq hws hG ha' q] at hne
      obtain ⟨n1, n2, n3⟩ := ne3_spec hne
      exact ⟨fun e => n1 (congrArg Fin.val e), fun e => n2 (congrArg Fin.val e),
        fun e => n3 (congrArg Fin.val e)⟩
    · rw [e4] at hb
      left
      intro j hj
      apply Fin.ext
      rw [← gpt_eq hws hG (by omega)]
      exact Nat.eq_of_beq_eq_true (allN_spec hb j hj)
  ·
    intro w hw'
    apply Fin.ext
    rw [← walk_fin hF (hp w hw')]
    exact fixK_spec p0w hfix w hw'
  ·
    refine (pairK_spec p0w hpair).imp_of_mem fun {w v} hw' hv' hd => ?_
    obtain ⟨d1, d2⟩ := difK_spec hd
    have ew0 := walk_fin hF (hp w hw') q0
    have ew1 := walk_fin hF (hp w hw') q1
    have ev0 := walk_fin hF (hp v hv') q0
    have ev1 := walk_fin hF (hp v hv') q1
    refine ⟨fun ⟨e1, e2⟩ => d1 ⟨?_, ?_⟩, fun ⟨e1, e2⟩ => d2 ⟨?_, ?_⟩⟩
    · exact ew0.trans ((congrArg Fin.val e1).trans ev0.symm)
    · exact ew1.trans ((congrArg Fin.val e2).trans ev1.symm)
    · exact ew0.trans ((congrArg Fin.val e1).trans ev1.symm)
    · exact ew1.trans ((congrArg Fin.val e2).trans ev0.symm)
  · apply Fin.ext
    rw [← walk_fin hF hm0]
    exact Nat.eq_of_beq_eq_true hm0p
  · apply Fin.ext
    rw [← walk_fin hF hm1]
    exact Nat.eq_of_beq_eq_true hm1p
  ·
    obtain ⟨hsa, hrest⟩ := (bAnd_iff _ _).1 hag
    rw [CFSG.KS.MulH.strictB_eq''] at hrest
    obtain ⟨e3, e1, hg⟩ := (by simpa only [bAnd_iff] using hrest :
      Nat.beq (pwK 3 (wK F wa)) idK = true ∧ bIf(Nat.beq (wK F wa) idK, false, true) = true ∧
        strictB (wK F wg) (fun g' => Nat.beq (pcK g' (wK F wa))
          (pcK (pcK (wK F wa) (wK F wa)) g')) = true)
    rw [CFSG.KS.MulH.strictB_eq''] at hg
    have pA := PR.word hF wa hwa
    have pG := PR.word hF wg hwg
    refine ⟨stabK_spec hF hwa hsa, (pA.pow 3).beq PR.one |>.1 e3, fun hh => ?_,
      (pG.mul pA).beq ((pA.mul pA).mul pG) |>.1 hg⟩
    have := (pA.beq PR.one).2 hh
    rw [(bIfF_iff.1 e1).1] at this
    exact absurd this (by decide)

end CFSG.KS.McLThree

end
