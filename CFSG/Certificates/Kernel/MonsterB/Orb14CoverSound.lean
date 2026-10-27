
module

public import CFSG.Certificates.Kernel.MonsterB.Orb14CoverSoundBase

public import CFSG.Certificates.Kernel.MonsterB.Orb14NetSound
public import CFSG.Certificates.Kernel.MonsterB.Orb14TreeSound

public section

namespace CFSG.KC.Orb14

open CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA.Census CFSG.KLie.CT CFSG.KC.U6Orb CFSG.KC.Bfs

theorem coverStep_sound {gen : Array (Array ℕ)} {N NW : ℕ}
    (hg : ∀ k < 17, NetPerm (fun x => (gen[k]!)[x]!) N (nw NW k)) (htr : TreeShape)
    (hpl : TreeBits) (hed : SelEdges) {sel : Array (ℕ × ℕ)} (hsel : sel = selL) {root : ℕ} {R : ℕ}
    (hR : ∀ x, R.testBit x = true →
      x < N ∧ Reach (selAct gen (transArr gen N) ((transArr gen N).map invPermArr) sel) 7 root x) :
    ∀ y, (coverStep NW R).testBit y = true →
      y < N ∧ Reach (selAct gen (transArr gen N) ((transArr gen N).map invPermArr) sel) 7 root y := by
  subst hsel
  obtain ⟨p1, l1, p2, l2, p4, l4, p8, l8, p13, l13⟩ := hpl
  obtain ⟨e2, e4, e6, e7, e14, e16, e13⟩ := hed
  have hpg : PermGens gen N := ⟨fun k hk x hx => (hg k hk).lt x hx,
    fun k hk x hx y hy e => (hg k hk).inj hx hy e⟩
  have hT := transArr_perm hpg htr
  let g : ℕ → ℕ → ℕ := fun k x => (gen[k]!)[x]!
  have T0 : ∀ x < N, ((transArr gen N)[0]!)[x]! = x := fun x hx => transArr_zero htr hx
  have Tstep : ∀ i, 0 < i → i < 1408 → ∀ x < N,
      ((transArr gen N)[i]!)[x]! = g (tauLab i) (((transArr gen N)[tauPar i]!)[x]!) :=
    fun i h0 hi x hx => transArr_step htr h0 hi
      (hT _ ((htr i h0 hi).1.trans hi)).size hx
  have Iget : ∀ e < 1408, ∀ z : ℕ, (((transArr gen N).map invPermArr)[e]!)[z]! =
      (invPermArr (transArr gen N)[e]!)[z]! := fun e he z => by
    rw [getElem!_map' invPermArr (by rw [transArr_size]; exact he)]
  have Ileft : ∀ e < 1408, ∀ y < N,
      (((transArr gen N).map invPermArr)[e]!)[((transArr gen N)[e]!)[y]!]! = y := by
    intro e he y hy
    rw [Iget e he]
    exact invPermArr_left (hT e he) hy
  have T1 : ∀ x < N, ((transArr gen N)[1]!)[x]! = g 0 x := by
    intro x hx
    rw [Tstep 1 (by decide) (by decide) x hx, p1, l1, T0 x hx]
  have Tl : ∀ e, 0 < e → e < 1408 → tauPar e = 0 → ∀ y < N,
      (((transArr gen N).map invPermArr)[e]!)[g (tauLab e) y]! = y := by
    intro e h0 he hp y hy
    have := Ileft e he y hy
    rwa [Tstep e h0 he y hy, hp, T0 y hy] at this
  have I0 : ∀ z < N, (((transArr gen N).map invPermArr)[0]!)[z]! = z := by
    intro z hz
    have := Ileft 0 (by decide) z hz
    rwa [T0 z hz] at this
  have bK : ∀ k < 17, ∀ R', (∀ x, R'.testBit x = true → x < N) →
      ∀ y, (netK (nw NW k) R').testBit y = true → ∃ x, R'.testBit x = true ∧ x < N ∧ g k x = y := by
    intro k hk R' hR' y h
    obtain ⟨x, hx, e⟩ := ((hg k hk).netK_mask hR' y).1 h
    exact ⟨x, hx, hR' x hx, e⟩
  have bKlt : ∀ k < 17, ∀ R', (∀ x, R'.testBit x = true → x < N) →
      ∀ y, (netK (nw NW k) R').testBit y = true → y < N := by
    intro k hk R' hR' y h
    obtain ⟨x, -, hx, rfl⟩ := bK k hk R' hR' y h
    exact (hg k hk).lt x hx
  have bR : ∀ k < 17, ∀ R', (∀ x, R'.testBit x = true → x < N) →
      ∀ y, (netR (nw NW k) R').testBit y = true → y < N ∧ R'.testBit (g k y) = true :=
    fun k hk R' hR' y h => ((hg k hk).netR_mask hR' y).1 h
  have hRlt : ∀ x, R.testBit x = true → x < N := fun x hx => (hR x hx).1
  let act := selAct gen (transArr gen N) ((transArr gen N).map invPermArr) selL
  have step : ∀ r < 7, ∀ x, R.testBit x = true → ∀ y, y < N → act r x = y →
      y < N ∧ Reach act 7 root y := by
    intro r hr x hx y hy e
    exact ⟨hy, e ▸ Reach.step r hr (hR x hx).2⟩
  intro y hy
  change (R ||| (netR (nw NW 1) (netK (nw NW 2) R) ||| (netK (nw NW 4) R |||
    (netK (nw NW 6) R ||| (netK (nw NW 7) R ||| (netR (nw NW 12) (netK (nw NW 14) R) |||
    (netK (nw NW 16) R ||| netR (nw NW 5) (netK (nw NW 3) (netK (nw NW 2)
      (netK (nw NW 0) R)))))))))).testBit y = true at hy
  simp only [Nat.testBit_or, Bool.or_eq_true] at hy
  rcases hy with hy | hy | hy | hy | hy | hy | hy | hy
  · exact hR y hy
  ·
    obtain ⟨hyN, hb⟩ := bR 1 (by decide) _ (bKlt 2 (by decide) R hRlt) y hy
    obtain ⟨x, hx, hxN, e⟩ := bK 2 (by decide) R hRlt _ hb
    refine step 0 (by decide) x hx y hyN ?_
    change (((transArr gen N).map invPermArr)[tauEdge 0 2]!)[g 2 (((transArr gen N)[0]!)[x]!)]! = y
    rw [e2, T0 x hxN, e]
    have := Tl 2 (by decide) (by decide) p2 y hyN
    rwa [l2] at this
  · obtain ⟨x, hx, hxN, e⟩ := bK 4 (by decide) R hRlt y hy
    refine step 1 (by decide) x hx y (e ▸ (hg 4 (by decide)).lt x hxN) ?_
    change (((transArr gen N).map invPermArr)[tauEdge 0 4]!)[g 4 (((transArr gen N)[0]!)[x]!)]! = y
    rw [e4, T0 x hxN, e, I0 y (e ▸ (hg 4 (by decide)).lt x hxN)]
  · obtain ⟨x, hx, hxN, e⟩ := bK 6 (by decide) R hRlt y hy
    refine step 2 (by decide) x hx y (e ▸ (hg 6 (by decide)).lt x hxN) ?_
    change (((transArr gen N).map invPermArr)[tauEdge 0 6]!)[g 6 (((transArr gen N)[0]!)[x]!)]! = y
    rw [e6, T0 x hxN, e, I0 y (e ▸ (hg 6 (by decide)).lt x hxN)]
  · obtain ⟨x, hx, hxN, e⟩ := bK 7 (by decide) R hRlt y hy
    refine step 3 (by decide) x hx y (e ▸ (hg 7 (by decide)).lt x hxN) ?_
    change (((transArr gen N).map invPermArr)[tauEdge 0 7]!)[g 7 (((transArr gen N)[0]!)[x]!)]! = y
    rw [e7, T0 x hxN, e, I0 y (e ▸ (hg 7 (by decide)).lt x hxN)]
  ·
    obtain ⟨hyN, hb⟩ := bR 12 (by decide) _ (bKlt 14 (by decide) R hRlt) y hy
    obtain ⟨x, hx, hxN, e⟩ := bK 14 (by decide) R hRlt _ hb
    refine step 4 (by decide) x hx y hyN ?_
    change (((transArr gen N).map invPermArr)[tauEdge 0 14]!)[g 14 (((transArr gen N)[0]!)[x]!)]! = y
    rw [e14, T0 x hxN, e]
    have := Tl 8 (by decide) (by decide) p8 y hyN
    rwa [l8] at this
  · obtain ⟨x, hx, hxN, e⟩ := bK 16 (by decide) R hRlt y hy
    refine step 5 (by decide) x hx y (e ▸ (hg 16 (by decide)).lt x hxN) ?_
    change (((transArr gen N).map invPermArr)[tauEdge 0 16]!)[g 16 (((transArr gen N)[0]!)[x]!)]! = y
    rw [e16, T0 x hxN, e, I0 y (e ▸ (hg 16 (by decide)).lt x hxN)]
  ·
    have h1 := bKlt 0 (by decide) R hRlt
    have h2 := bKlt 2 (by decide) _ h1
    obtain ⟨hyN, hb⟩ := bR 5 (by decide) _ (bKlt 3 (by decide) _ h2) y hy
    obtain ⟨b, hb', hbN, eb⟩ := bK 3 (by decide) _ h2 _ hb
    obtain ⟨a, ha, haN, ea⟩ := bK 2 (by decide) _ h1 _ hb'
    obtain ⟨x, hx, hxN, ex⟩ := bK 0 (by decide) R hRlt _ ha
    refine step 6 (by decide) x hx y hyN ?_
    change (((transArr gen N).map invPermArr)[tauEdge 13 3]!)[g 3 (((transArr gen N)[13]!)[x]!)]! = y
    rw [e13, Tstep 13 (by decide) (by decide) x hxN, p13, l13, T1 x hxN, ex, ea, eb]
    have := Tl 4 (by decide) (by decide) p4 y hyN
    rwa [l4] at this

theorem cover_sound {gen : Array (Array ℕ)} {N NW : ℕ}
    (hg : ∀ k < 17, NetPerm (fun x => (gen[k]!)[x]!) N (nw NW k)) (htr : TreeShape)
    (hpl : TreeBits) (hed : SelEdges) {sel : Array (ℕ × ℕ)} (hsel : sel = selL) {root : ℕ} :
    ∀ (L R : ℕ), (∀ x, R.testBit x = true →
      x < N ∧ Reach (selAct gen (transArr gen N) ((transArr gen N).map invPermArr) sel) 7 root x) →
    ∀ y, (cover NW R L).testBit y = true →
      y < N ∧ Reach (selAct gen (transArr gen N) ((transArr gen N).map invPermArr) sel) 7 root y
  | 0, _, hR => hR
  | L + 1, R, hR => coverStep_sound hg htr hpl hed hsel (cover_sound hg htr hpl hed hsel L R hR)

end CFSG.KC.Orb14

end
