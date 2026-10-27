module

public import Certificates.Data.CFSGNative.Fi22.LH
public import Certificates.Data.Kernel.F3Bfs
import CFSG.Certificates.Kernel.Fi22LH.OrbSets
import CFSG.Certificates.Kernel.Fi22LH.Loops
import CFSG.Certificates.Kernel.Fi22LH.TreeSpec
import CFSG.F3.ConjBFS
import CFSG.Certificates.Kernel.Fi22LH.Prim

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.KC.F3Bfs CFSG.F3.Native.BfsSpec

@[expose] def OInv (sets : Nat → Bits) (fp fl : Nat → Nat) (m : Nat) (s : Array Bits)
    (t : Std.HashMap Bits Nat) (par lab : Array Nat) : Prop :=
  s.size = m ∧ (∀ i < m, s[i]! = sets i) ∧
    t = (List.range m).foldl (fun t k => t.insert (sets k) k) ∅ ∧
    par.size = m ∧ (∀ i < m, par[i]! = fp i) ∧ lab.size = m ∧ (∀ i < m, lab[i]! = fl i)

@[expose] def NInv (f : Nat → Nat) (a : Array Nat) (h : Nat) : Prop :=
  a.size = h ∧ ∀ i < h, a[i]! = f i

theorem ninv_push {f : Nat → Nat} {a : Array Nat} {h : Nat} (H : NInv f a h) {v : Nat}
    (hv : f h = v) : NInv f (a.push v) (h + 1) := by
  refine ⟨by rw [Array.size_push, H.1], fun i hi => ?_⟩
  rcases Nat.lt_or_ge i h with h1 | h1
  · rw [get!_push_lt _ _ (by rw [H.1]; exact h1), H.2 i h1]
  · have e : i = a.size := by rw [H.1]; omega
    rw [e, get!_push_eq, ← hv, H.1]

theorem oinv_found {sets : Nat → Bits} {fp fl : Nat → Nat} {N m : Nat} {s : Array Bits}
    {t : Std.HashMap Bits Nat} {par lab : Array Nat} (H : OInv sets fp fl m s t par lab)
    (hinj : ∀ i < N, ∀ j < N, sets i = sets j → i = j) (hm : m ≤ N) {x k : Nat} (hx : x < N)
    (hk : t.get? (sets x) = some k) : k = x ∧ x < m := by
  rw [Std.HashMap.get?_eq_getElem?, H.2.2.1] at hk
  rcases Nat.lt_or_ge x m with h | h
  · rw [foldl_insert_of sets (fun i hi j hj e => hinj i (by omega) j (by omega) e) h] at hk
    exact ⟨(Option.some.inj hk).symm, h⟩
  · rw [foldl_insert_none sets fun i hi e => absurd (hinj i (by omega) x hx e) (by omega)] at hk
    exact absurd hk (by simp)

theorem oinv_absent {sets : Nat → Bits} {fp fl : Nat → Nat} {N m : Nat} {s : Array Bits}
    {t : Std.HashMap Bits Nat} {par lab : Array Nat} (H : OInv sets fp fl m s t par lab)
    (hinj : ∀ i < N, ∀ j < N, sets i = sets j → i = j) (hm : m ≤ N) {x : Nat} (hx : x < m)
    (hk : t.get? (sets x) = none) : False := by
  rw [Std.HashMap.get?_eq_getElem?, H.2.2.1,
    foldl_insert_of sets (fun i hi j hj e => hinj i (by omega) j (by omega) e) hx] at hk
  exact absurd hk (by simp)

theorem oinv_new {sets : Nat → Bits} {fp fl : Nat → Nat} {m : Nat} {s : Array Bits}
    {t : Std.HashMap Bits Nat} {par lab : Array Nat} (H : OInv sets fp fl m s t par lab)
    {p l : Nat} (hp : fp m = p) (hl : fl m = l) :
    OInv sets fp fl (m + 1) (s.push (sets m)) (t.insert (sets m) s.size) (par.push p)
      (lab.push l) := by
  obtain ⟨hs, hk, ht, hps, hpk, hls, hlk⟩ := H
  refine ⟨by rw [Array.size_push, hs], fun i hi => ?_, ?_, by rw [Array.size_push, hps],
    fun i hi => ?_, by rw [Array.size_push, hls], fun i hi => ?_⟩
  · rcases Nat.lt_or_ge i m with h1 | h1
    · rw [get!_push_lt _ _ (by rw [hs]; exact h1), hk i h1]
    · have e : i = s.size := by rw [hs]; omega
      rw [e, get!_push_eq, hs]
  · rw [ht, hs, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  · rcases Nat.lt_or_ge i m with h1 | h1
    · rw [get!_push_lt _ _ (by rw [hps]; exact h1), hpk i h1]
    · have e : i = par.size := by rw [hps]; omega
      rw [e, get!_push_eq, hps, hp]
  · rcases Nat.lt_or_ge i m with h1 | h1
    · rw [get!_push_lt _ _ (by rw [hls]; exact h1), hlk i h1]
    · have e : i = lab.size := by rw [hls]; omega
      rw [e, get!_push_eq, hls, hl]

theorem lhOrbitBFS_eq_of {alpha beta : Table} {S0 : Bits} {limit N : Nat} {sets : Nat → Bits}
    {fa fb fp fl : Nat → Nat} (hN : 0 < N) (hlim : N ≤ limit) (h0 : sets 0 = S0)
    (hinj : ∀ i < N, ∀ j < N, sets i = sets j → i = j)
    (ha : ∀ k < N, fa k < N ∧ imgBits alpha (sets k) = sets (fa k))
    (hb : ∀ k < N, fb k < N ∧ imgBits beta (sets k) = sets (fb k))
    (hbfs : bfsOrderOK fa fb fp fl N = true) :
    lhOrbitBFS alpha beta S0 limit =
      ⟨Array.ofFn (n := N) fun k => sets k.val, Array.ofFn (n := N) fun k => fa k.val,
        Array.ofFn (n := N) fun k => fb k.val, Array.ofFn (n := N) fun k => fp k.val,
        Array.ofFn (n := N) fun k => fl k.val,
        (List.range N).foldl (fun t k => t.insert (sets k) k) ∅⟩ := by
  simp only [bfsOrderOK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hbfs
  obtain ⟨hp0, hl0, hfold⟩ := hbfs
  have hCN : cnt fa fb fp fl N = N := by
    rw [foldUp_eq] at hfold
    exact hfold
  have hCz : ∀ t h, cnt fa fb fp fl h = 0 → cnt fa fb fp fl (h + t) = 0 := by
    intro t
    induction t with
    | zero => intro h e; exact e
    | succ t ih =>
      intro h e
      rw [← Nat.add_assoc, cnt_succ, ih h e]
      exact bfsStep_zero _ _ _ _ _
  have hCne : ∀ h ≤ N, cnt fa fb fp fl h ≠ 0 := by
    intro h hh e
    have := hCz (N - h) h e
    rw [Nat.add_sub_cancel' hh, hCN] at this
    omega
  obtain ⟨s, hs, hK, hTa, hTb⟩ : ∃ s : Array Bits × Std.HashMap Bits Nat × Array Nat ×
      Array Nat × Array Nat × Array Nat, lhOrbitBFS alpha beta S0 limit =
        ⟨s.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2, s.2.1⟩ ∧
      OInv sets fp fl N s.1 s.2.1 s.2.2.2.2.1 s.2.2.2.2.2 ∧ NInv fa s.2.2.1 N ∧
      NInv fb s.2.2.2.1 N := by
    unfold lhOrbitBFS
    refine ⟨_, rfl, ?_⟩
    refine range_loop (fun q (s : Array Bits × Std.HashMap Bits Nat × Array Nat × Array Nat ×
        Array Nat × Array Nat) => q ≤ N ∧ cnt fa fb fp fl q ≤ N ∧
        OInv sets fp fl (cnt fa fb fp fl q) s.1 s.2.1 s.2.2.2.2.1 s.2.2.2.2.2 ∧
        NInv fa s.2.2.1 q ∧ NInv fb s.2.2.2.1 q)
      (fun (s : Array Bits × Std.HashMap Bits Nat × Array Nat × Array Nat × Array Nat ×
        Array Nat) => OInv sets fp fl N s.1 s.2.1 s.2.2.2.2.1 s.2.2.2.2.2 ∧
        NInv fa s.2.2.1 N ∧ NInv fb s.2.2.2.1 N) _ limit _ ?_ ?_ ?_
    ·
      intro q s hq hI
      obtain ⟨hqN, hcN, hKs, hTas, hTbs⟩ := hI
      rcases Nat.lt_or_ge q N with hlt | hge
      · have hn0 : cnt fa fb fp fl (q + 1) ≠ 0 := hCne (q + 1) (by omega)
        have hCs := cnt_succ fa fb fp fl q
        rw [bfsStep_eq] at hCs
        have hqn : q < cnt fa fb fp fl q := by
          by_contra hqn
          rw [if_neg hqn] at hCs
          exact hn0 hCs
        rw [if_pos hqn] at hCs
        have hn1z : bfsHit fp fl q 1 (fa q) (cnt fa fb fp fl q) ≠ 0 := by
          intro e
          rw [e, bfsHit_zero] at hCs
          exact hn0 hCs
        have hA := bfsHit_spec hn1z
        rw [hCs] at hn0
        have hB := bfsHit_spec hn0
        obtain ⟨haN, hcA⟩ := ha q hlt
        obtain ⟨hbN, hcB⟩ := hb q hlt
        have hqs : q < s.1.size := by rw [hKs.1]; exact hqn
        have hX : s.1[q]! = sets q := hKs.2.1 q hqn
        simp only [hqs, ↓reduceIte, hX, hcA, hcB]
        set n := cnt fa fb fp fl q with hn
        set n1 := bfsHit fp fl q 1 (fa q) n with hn1
        have hsz : s.1.size = n := hKs.1
        split
        ·
          rename_i k hka
          obtain ⟨hkx, hxn⟩ := oinv_found hKs hinj hcN haN hka
          subst hkx
          have hn1e : n1 = n := by
            rcases hA with h | h
            · exact h.2
            · omega
          split
          · rename_i k' hkb
            obtain ⟨hky, hyn⟩ := oinv_found hKs hinj hcN hbN hkb
            subst hky
            have hc : cnt fa fb fp fl (q + 1) = n := by
              rcases hB with h | h
              · rw [hCs, h.2, hn1e]
              · omega
            exact ⟨by omega, by omega, hc ▸ hKs, ninv_push hTas rfl, ninv_push hTbs rfl⟩
          · rename_i hkb
            have hB2 : fb q = n ∧ fp n = q ∧ fl n = 2 ∧ cnt fa fb fp fl (q + 1) = n + 1 := by
              rcases hB with h | h
              · exact absurd (oinv_absent hKs hinj hcN (by omega) hkb) id
              · exact ⟨by omega, hn1e ▸ h.2.1, hn1e ▸ h.2.2.1, by rw [hCs, h.2.2.2, hn1e]⟩
            obtain ⟨hye, hfp, hfl, hc⟩ := hB2
            have hK1 := oinv_new hKs hfp hfl
            rw [hc]
            refine ⟨by omega, by omega, ?_, ninv_push hTas rfl, ninv_push hTbs ?_⟩
            · rw [hye]
              exact hK1
            · rw [hsz, hye]
        ·
          rename_i hka
          have hA2 : fa q = n ∧ fp n = q ∧ fl n = 1 ∧ n1 = n + 1 := by
            rcases hA with h | h
            · exact absurd (oinv_absent hKs hinj hcN h.1 hka) id
            · exact h
          obtain ⟨hxe, hfp, hfl, hn1e⟩ := hA2
          have hK1 := oinv_new hKs hfp hfl
          have hTa2 : NInv fa (s.2.2.1.push s.1.size) (q + 1) :=
            ninv_push hTas (by rw [hsz, hxe])
          rw [hxe]
          rw [hxe] at hka
          split
          · rename_i k' hkb
            obtain ⟨hky, hyn⟩ := oinv_found hK1 hinj (by omega) hbN hkb
            subst hky
            have hc : cnt fa fb fp fl (q + 1) = n + 1 := by
              rcases hB with h | h
              · rw [hCs, h.2, hn1e]
              · omega
            exact ⟨by omega, by omega, hc ▸ hK1, hTa2, ninv_push hTbs rfl⟩
          · rename_i hkb
            have hB2 : fb q = n + 1 ∧ fp (n + 1) = q ∧ fl (n + 1) = 2 ∧
                cnt fa fb fp fl (q + 1) = n + 2 := by
              rcases hB with h | h
              · exact absurd (oinv_absent hK1 hinj (by omega) (by omega) hkb) id
              · exact ⟨by omega, hn1e ▸ h.2.1, hn1e ▸ h.2.2.1, by rw [hCs, h.2.2.2, hn1e]⟩
            obtain ⟨hye, hfp2, hfl2, hc⟩ := hB2
            have hK2 := oinv_new hK1 hfp2 hfl2
            rw [hc]
            refine ⟨by omega, by omega, ?_, hTa2, ninv_push hTbs ?_⟩
            · rw [hye]
              exact hK2
            · rw [Array.size_push, hsz, hye]
      ·
        have e : q = N := by omega
        have hqs : ¬ q < s.1.size := by rw [hKs.1, e, hCN]; omega
        simp only [hqs, ↓reduceIte]
        rw [e, hCN] at hKs
        rw [e] at hTas hTbs
        exact ⟨hKs, hTas, hTbs⟩
    ·
      intro b hb
      have e : limit = N := by omega
      rw [e, hCN] at hb
      exact hb.2.2
    ·
      have hc0 : cnt fa fb fp fl 0 = 1 := rfl
      refine ⟨Nat.zero_le _, by rw [hc0]; omega, ⟨rfl, fun i hi => ?_, ?_, rfl, fun i hi => ?_,
        rfl, fun i hi => ?_⟩, ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩,
        ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩⟩
      all_goals dsimp only at *
      · have hi0 : i = 0 := by rw [hc0] at hi; omega
        subst hi0
        simp [h0]
      · rw [hc0, ← h0]
        rfl
      · have hi0 : i = 0 := by rw [hc0] at hi; omega
        subst hi0
        simp [hp0]
      · have hi0 : i = 0 := by rw [hc0] at hi; omega
        subst hi0
        simp [hl0]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hK
  have hof : ∀ {α : Type} [Inhabited α] (a : Array α) (g : Nat → α), a.size = N →
      (∀ k < N, a[k]! = g k) → a = Array.ofFn (n := N) fun k => g k.val := by
    intro α _ a g hs hg
    apply Array.ext (by rw [hs, Array.size_ofFn])
    intro i hi1 hi2
    rw [Array.getElem_ofFn, ← getElem!_pos a i hi1, hg i (by omega)]
  rw [hs, h3, hof _ sets h1 h2, hof _ fa hTa.1 hTa.2, hof _ fb hTb.1 hTb.2, hof _ fp h4 h5,
    hof _ fl h6 h7]

end CFSG.KS.Fi22LH
