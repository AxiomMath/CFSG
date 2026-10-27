module

public import CFSG.Certificates.Kernel.Spor.ONSevenOrbit
public import Certificates.Data.Kernel.ONSevenR
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.Spor.PWord
import CFSG.Sporadic.Schreier.ONPermArr

public section

namespace CFSG.KS.ONR

open CFSG.KC.ONR CFSG.KC.Enum CFSG.KS CFSG.KS.ONOrb CFSG.KS.Raw CFSG.RankThree.Native
  CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.KC.BfsPin

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := by simpa using h

theorem resK_spec {N w : Nat} {T F : Nat → Nat} {G : Nat} (h : resK N w T F G = true) :
    ∀ i < N, ent w G i < N ∧ T (ent w G i) = F (T i) := by
  intro i hi
  have := allN_spec h i hi
  rw [strictB_eq, bAnd_iff] at this
  exact ⟨lt_of_blt this.1, Nat.eq_of_beq_eq_true this.2⟩

structure OFacts (N w k : Nat) (T G D : Nat → Nat) : Prop where
  k_pos : 0 < k
  three_le : 3 ≤ N
  le_n : N ≤ 245520
  t0 : T 0 = 0
  t1 : T 1 = 227759
  t2 : T 2 = 100817
  inj : ∀ a < N, ∀ b < N, T a = T b → a = b
  lt : ∀ i < N, T i < 245520
  tree : ∀ i, 3 ≤ i → i < N → D i / k < i ∧ ent w (G (D i % k)) (D i / k) = i ∧
    (i + 1 < N → D i < D (i + 1))
  close : ∀ i < N, ∀ j < k, ent w (G j) i < N ∧ (3 ≤ ent w (G j) i → D (ent w (G j) i) ≤ k * i + j)

theorem orbK_spec {N w k : Nat} {T G D S : Nat → Nat} (h : orbK N w k T G D S = true) :
    OFacts N w k T G D := by
  unfold orbK at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hp := allN_spec h8
  refine ⟨lt_of_blt h1, Nat.le_of_ble_eq_true h2, Nat.le_of_ble_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6,
    distinctK_inj h7, fun i hi => ?_, fun i h3i hi => ?_, fun i hi j hj => ?_⟩
  · have := hp i hi
    unfold orbPtK at this
    rw [bAnd_iff] at this
    exact lt_of_blt this.1
  · have := hp i hi
    unfold orbPtK at this
    rw [bAnd_iff, bAnd_iff] at this
    have h9 := this.2.1
    have hn : Nat.blt i 3 = false := by
      rw [Bool.eq_false_iff]
      intro e
      have := lt_of_blt e
      omega
    rw [hn] at h9
    change strictB (D i) _ = true at h9
    rw [strictB_eq, bAnd_iff, bAnd_iff] at h9
    obtain ⟨a, b, c⟩ := h9
    refine ⟨lt_of_blt a, Nat.eq_of_beq_eq_true b, fun hl => ?_⟩
    have hl' : Nat.blt (Nat.succ i) N = true := by simpa using hl
    rw [hl'] at c
    exact lt_of_blt c
  · have := hp i hi
    unfold orbPtK at this
    rw [bAnd_iff, bAnd_iff] at this
    have h9 := allN_spec this.2.2 j hj
    rw [strictB_eq, bAnd_iff] at h9
    refine ⟨lt_of_blt h9.1, fun h3q => ?_⟩
    have hn : Nat.blt (ent w (G j) i) 3 = false := by
      rw [Bool.eq_false_iff]
      intro e
      have := lt_of_blt e
      omega
    have h10 := h9.2
    rw [hn] at h10
    exact Nat.le_of_ble_eq_true h10

theorem orec_of {gs : Array (Array Nat)} {N w k : Nat} {T G D S : Nat → Nat} {F : Nat → Nat → Nat}
    (hk : gs.size = k) (hF : ∀ s < k, ∀ x < 245520, (gs[s]!)[x]! = F s x)
    (ho : orbK N w k T G D S = true) (hr : ∀ s < k, resK N w T (F s) (G s) = true) :
    ORec gs N T D := by
  have O := orbK_spec ho
  subst hk
  refine ⟨O.k_pos, O.three_le, O.le_n, O.t0, O.t1, O.t2, O.inj, fun i h3 hi => ?_,
    fun i h3 hi => (O.tree i h3 (by omega)).2.2 hi, fun h hh j hj => ?_⟩
  · obtain ⟨a, b, -⟩ := O.tree i h3 hi
    have hj : D i % gs.size < gs.size := Nat.mod_lt _ O.k_pos
    refine ⟨a, ?_⟩
    rw [hF _ hj _ (O.lt _ (by omega)), ← (resK_spec (hr _ hj) _ (by omega)).2, b]
  · obtain ⟨a, b⟩ := O.close h hh j hj
    refine ⟨ent w (G j) h, a, ?_, ?_⟩
    · rw [hF j hj _ (O.lt h hh), (resK_spec (hr j hj) h hh).2]
    · by_cases h3 : ent w (G j) h < 3
      · exact Or.inl h3
      · exact Or.inr (b (by omega))

theorem ofFn_get {N : Nat} {T : Nat → Nat} {i : Nat} (hi : i < N) :
    (Array.ofFn (n := N) fun i => T i.val)[i]! = T i := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem unpack_get' {n w P x : Nat} (hx : x < n) : (unpack n w P)[x]! = ent w P x := by
  unfold unpack
  rw [getElem!_pos _ x (by rw [Array.size_ofFn]; exact hx), Array.getElem_ofFn]
  rfl

theorem pos_spec {N : Nat} {T : Nat → Nat} (hb : ∀ i < N, T i < 245520)
    (hd : ∀ a < N, ∀ b < N, T a = T b → a = b) :
    (posArr nPts (Array.ofFn (n := N) fun i => T i.val)).size = nPts ∧
      ∀ i < N, (posArr nPts (Array.ofFn (n := N) fun i => T i.val))[T i]! = i := by
  have h := CFSG.KS.PW.posArr_spec (n := nPts) (R := Array.ofFn (n := N) fun i => T i.val)
    (fun i hi => by
      rw [Array.size_ofFn] at hi
      rw [ofFn_get hi]
      exact hb i hi)
    (fun i hi j hj e => by
      rw [Array.size_ofFn] at hi
      rw [ofFn_get hi, ofFn_get (by omega)] at e
      have := hd j (by omega) i hi e
      omega)
  refine ⟨h.1, fun i hi => ?_⟩
  have := h.2 i (by simpa using hi)
  rwa [ofFn_get hi] at this

theorem tab_eq {N w : Nat} {T F : Nat → Nat} {G : Nat} {g : Array Nat}
    (hg : ∀ x < 245520, g[x]! = F x) (hb : ∀ i < N, T i < 245520)
    (hd : ∀ a < N, ∀ b < N, T a = T b → a = b) (hr : resK N w T F G = true) :
    onSevenTab (Array.ofFn (n := N) fun i => T i.val) g = unpack N w G := by
  apply Array.ext
  · simp [onSevenTab, restrictTab, unpack]
  · intro i h1 h2
    have hi : i < N := by simpa [onSevenTab, restrictTab] using h1
    have e1 : (onSevenTab (Array.ofFn (n := N) fun i => T i.val) g)[i] =
        (onSevenTab (Array.ofFn (n := N) fun i => T i.val) g)[i]! := (getElem!_pos _ i h1).symm
    have e2 : (unpack N w G)[i] = (unpack N w G)[i]! := (getElem!_pos _ i h2).symm
    rw [e1, e2, unpack_get' hi]
    unfold onSevenTab restrictTab
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, Array.getElem_ofFn]
    obtain ⟨hl, he⟩ := resK_spec hr i hi
    rw [hg _ (hb i hi), ← he]
    exact (pos_spec hb hd).2 _ hl

theorem resOK_of {N w k : Nat} {T G D S : Nat → Nat} {gs : Array (Array Nat)} {F : Nat → Nat → Nat}
    {GR : Nat → Nat} (ho : orbK N w k T G D S = true)
    (hF : ∀ s < gs.size, ∀ x < 245520, (gs[s]!)[x]! = F s x)
    (hr : ∀ s < gs.size, resK N w T (F s) (GR s) = true) :
    onSevenResOK (Array.ofFn (n := N) fun i => T i.val) gs = true := by
  have O := orbK_spec ho
  have hP := pos_spec O.lt O.inj
  unfold onSevenResOK pointsOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.size_ofFn]
  refine ⟨⟨⟨⟨⟨⟨hP.1, ?_⟩, O.three_le⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [CFSG.ONSchreier.allBelowN_iff]
    intro i hi
    rw [ofFn_get hi]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨O.lt i hi, hP.2 i hi⟩
  · rw [ofFn_get (by have := O.three_le; omega), O.t0]
  · rw [ofFn_get (by have := O.three_le; omega), O.t1]
  · rw [ofFn_get (by have := O.three_le; omega), O.t2]
  · rw [CFSG.ONSchreier.allBelowN_iff]
    intro s hs
    rw [tab_eq (hF s hs) O.lt O.inj (hr s hs)]
    unfold restrictOK
    rw [CFSG.ONSchreier.allBelowN_iff]
    intro i hi
    rw [Array.size_ofFn] at hi
    simp only [Array.size_ofFn, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    obtain ⟨hl, he⟩ := resK_spec (hr s hs) i hi
    rw [unpack_get' hi, ofFn_get hl, ofFn_get hi, he, hF s hs _ (O.lt i hi)]
    exact ⟨hl, rfl⟩

end CFSG.KS.ONR

end
