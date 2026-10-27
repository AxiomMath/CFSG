module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Chain
public import CFSG.Certificates.Kernel.U6Sec3Defs
public import CFSG.Certificates.Kernel.Spor.PackWord

public section

namespace CFSG.KC.U6Sec3

open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.Certificates.Native

theorem W_eq (c : ChainData) :
    c.W = CFSG.Sporadic.Schreier.Co3.Native.wordsArr c.gens.length
      (c.gens.length + c.words.length) c.words := by
  apply Array.ext
  · simp [ChainData.W, CFSG.Sporadic.Schreier.Co3.Native.wordsArr]
  · intro j h1 h2
    simp only [ChainData.W, CFSG.Sporadic.Schreier.Co3.Native.wordsArr, List.getElem_toArray,
      Array.getElem_ofFn]
    rw [List.getElem_append]
    split_ifs with h3 h4 h4
    · simp
    · simp at h3; omega
    · simp at h3; omega
    · simp only [List.length_replicate] at h3 ⊢
      rw [List.getD_eq_getElem]

theorem ok_of_rawChainOK (c : ChainData) {SA : Array (Array ℕ)} (hS : c.S = SA)
    (hraw : rawChainOK 693 (SA.extract 0 c.gens.length) SA c.B
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr c.gens.length SA.size c.words) 1 = true)
    (hsize : SA.size = c.gens.length + c.words.length) : c.ok = true := by
  rw [ChainData.ok, hS, W_eq, ← hsize]
  exact hraw

theorem order_of_rawChainOK (c : ChainData) {SA : Array (Array ℕ)} (hS : c.S = SA) :
    c.order = (rawOrbitSizes 693 SA c.B).prod := by
  rw [ChainData.order, hS]

open CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native

theorem unpackAll_get {kS : ℕ} {PS : ℕ → ℕ} {j : ℕ} (hj : j < kS) :
    (unpackAll kS PS)[j]! = unpack 693 10 (PS j) := by
  rw [unpackAll, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem unpack_eq_of_all {a : Array ℕ} {P : ℕ} (hs : a.size = 693)
    (h : (List.range 693).all (fun i => Nat.beq a[i]! (pg 10 (mask 10) P i)) = true) :
    a = unpack 693 10 P := by
  apply Array.ext (by simp [unpack, hs])
  intro i h1 h2
  have hi : i < 693 := by omega
  have := Nat.eq_of_beq_eq_true (List.all_eq_true.mp h i (List.mem_range.mpr hi))
  rw [getElem!_pos a i h1] at this
  simp only [unpack, Array.getElem_ofFn]
  exact this

theorem wA_unpack {G : ℕ → ℕ} (hG : ∀ k < 18, gA k = unpack 693 10 (G k))
    (hc : ∀ k < 18, canonK 693 10 (mask 10) (693 * 10) (G k) = true)
    (hid : canonK 693 10 (mask 10) (693 * 10) (pidn 693 10) = true)
    (hidA : CFSG.Monster.B.Co2.Native.idA 693 = unpack 693 10 (pidn 693 10)) :
    ∀ w : List ℕ, (∀ k ∈ w, k < 18) →
      wA w = unpack 693 10 (wordGA G w) ∧ canonK 693 10 (mask 10) (693 * 10) (wordGA G w) = true
  | [], _ => by
    simp only [wA, wordGA, List.foldr_nil]
    exact ⟨hidA, hid⟩
  | k :: w, hw => by
    obtain ⟨ih, ihc⟩ := wA_unpack hG hc hid hidA w fun j hj => hw j (List.mem_cons_of_mem _ hj)
    have hk := hw k List.mem_cons_self
    have e1 : wA (k :: w) = CFSG.Monster.B.Co2.Native.compA 693 (gA k) (wA w) := by
      simp only [wA, List.foldr_cons]
    have e2 : wordGA G (k :: w) = pcomp 693 10 (mask 10) (G k) (wordGA G w) := by
      simp only [wordGA, List.foldr_cons]
    rw [e1, e2, ih, hG k hk, compA_unpack (hc k hk) ihc]
    exact ⟨rfl, canonK_pcomp (hc k hk) ihc⟩

theorem O_of_wordGA (c : ChainData) {G PS : ℕ → ℕ} (hgen : c.GensOK)
    (hG : ∀ k < 18, gA k = unpack 693 10 (G k))
    (hc : ∀ k < 18, canonK 693 10 (mask 10) (693 * 10) (G k) = true)
    (hid : canonK 693 10 (mask 10) (693 * 10) (pidn 693 10) = true)
    (hidA : CFSG.Monster.B.Co2.Native.idA 693 = unpack 693 10 (pidn 693 10))
    (h : ∀ j < c.gens.length, PS j = wordGA G (c.gens.getD j [])) :
    ∀ j < c.gens.length, unpack 693 10 (PS j) = c.O[j]! := by
  intro j hj
  rw [ChainData.O_getElem c hj, h j hj, List.getD_eq_getElem _ _ hj]
  exact ((wA_unpack hG hc hid hidA _ (hgen _ (List.getElem_mem hj))).1).symm

end CFSG.KC.U6Sec3
