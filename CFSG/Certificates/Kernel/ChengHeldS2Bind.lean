module

public import Certificates.Data.Kernel.ChengHeldSec2K
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelClosure
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelAut
public import CFSG.Certificates.Kernel.Spor.PEnumSound
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.ChengHeldS2

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel
open CFSG.OddStandard.ChengHeld.Model
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KS.PEnum

@[expose] noncomputable def mK (n w : ℕ) (T IX : ℕ → ℕ) (a b : ℕ) : ℕ :=
  if a * n + b < n * n then pg w (mask w) (T (IX ((a * n + b) / n))) ((a * n + b) % n) else 0

variable {n w : ℕ} {gens : Array Tab} {E : Enum} {p : ℕ → Equiv.Perm (Fin n)} {T PL IX : ℕ → ℕ}

theorem tabs_get (hE : E = penumRec n w n T PL) {i : ℕ} (hi : i < n) :
    E.tabs[i]! = unpack n w (T i) := by
  subst hE
  rw [penumRec_eq, getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]

theorem m_eq_mK (hd : RegData n gens E p) (hE : E = penumRec n w n T PL)
    (hIX : ∀ a < n, IX a < n ∧ pg w (mask w) (T (IX a)) 0 = a) (a b : ℕ) :
    (mkRegGen n gens E).m a b = mK n w T IX a b := by
  have hn : 0 < n := hd.pos
  unfold mK
  by_cases hk : a * n + b < n * n
  · rw [if_pos hk]
    have hj : (a * n + b) / n < n := (Nat.div_lt_iff_lt_mul hn).2 hk
    have hr : (a * n + b) % n < n := Nat.mod_lt _ hn
    obtain ⟨hi, h0⟩ := hIX _ hj
    have e0 : (E.tabs[IX ((a * n + b) / n)]!)[0]! = (a * n + b) / n := by
      rw [tabs_get hE hi, unpack_get' hn, h0]
    have hpe := peArr_get hd.hdist hd.hlt (i := IX ((a * n + b) / n)) (by rw [hd.size]; exact hi)
    rw [e0, tabs_get hE hi] at hpe
    unfold RegModel.m mkRegGen
    simp only
    rw [getElem!_pos _ _ (by simpa using hk), Array.getElem_ofFn]
    simp only
    rw [hpe, unpack_get' hr]
  · rw [if_neg hk]
    unfold RegModel.m mkRegGen
    simp only
    rw [getElem!_neg _ _ (by simpa using hk)]
    rfl

theorem inv_eq (hd : RegData n gens E p) {INV : ℕ → ℕ}
    (hINV : ∀ a < n, INV a < n ∧ (mkRegGen n gens E).m a (INV a) = 0) (a : ℕ) :
    (mkRegGen n gens E).inv[a]! = if a < n then INV a else 0 := by
  by_cases ha : a < n
  · rw [if_pos ha]
    obtain ⟨g, rfl⟩ := hd.ptOf_surj ha
    rw [hd.inv_ptOf]
    obtain ⟨h1, h2⟩ := hINV _ ha
    obtain ⟨g', hg'⟩ := hd.ptOf_surj h1
    rw [← hg', hd.m_ptOf, ← hd.ptOf_one] at h2
    have := hd.ptOf_inj h2
    rw [← hg', eq_inv_of_mul_eq_one_right this]
  · rw [if_neg ha]
    unfold mkRegGen
    simp only
    rw [getElem!_neg _ _ (by simpa using ha)]
    rfl

theorem testBit_foldl_or (l : List ℕ) (f : ℕ → ℕ) (acc z : ℕ) :
    (l.foldl (fun acc g => acc ||| (1 <<< f g)) acc).testBit z = true ↔
      acc.testBit z = true ∨ ∃ g ∈ l, f g = z := by
  induction l generalizing acc with
  | nil => simp
  | cons g l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ((h | h) | ⟨g', hg', rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨g, List.mem_cons_self, h⟩
      · exact Or.inr ⟨g', List.mem_cons_of_mem _ hg', rfl⟩
    · rintro (h | ⟨g', hg', rfl⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 hg' with rfl | hg'
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr ⟨g', hg', rfl⟩

theorem testBit_clStepK (N : ℕ) (m : ℕ → ℕ → ℕ) (gs : List ℕ) (B z : ℕ) :
    (clStepK N m gs B).testBit z = true ↔
      B.testBit z = true ∨ ∃ x < N, B.testBit x = true ∧ ∃ g ∈ gs, m x g = z := by
  unfold clStepK
  suffices key : ∀ (l : List ℕ) acc, (∀ x ∈ l, x < N) →
      ((l.foldl (fun acc x =>
        if B.testBit x then gs.foldl (fun acc g => acc ||| (1 <<< m x g)) acc else acc) acc).testBit
          z = true ↔
        acc.testBit z = true ∨ ∃ x ∈ l, B.testBit x = true ∧ ∃ g ∈ gs, m x g = z) by
    rw [key (List.range N) B (fun x hx => List.mem_range.1 hx)]
    simp only [List.mem_range]
  intro l
  induction l with
  | nil => simp
  | cons x l ih =>
    intro acc hl
    rw [List.foldl_cons, ih _ fun y hy => hl y (List.mem_cons_of_mem _ hy)]
    by_cases hb : B.testBit x = true
    · rw [if_pos hb, testBit_foldl_or]
      constructor
      · rintro ((h | ⟨g, hg, rfl⟩) | ⟨y, hy, hby, g, hg, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨x, List.mem_cons_self, hb, g, hg, rfl⟩
        · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hby, g, hg, rfl⟩
      · rintro (h | ⟨y, hy, hby, g, hg, rfl⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact Or.inl (Or.inr ⟨g, hg, rfl⟩)
          · exact Or.inr ⟨y, hy, hby, g, hg, rfl⟩
    · rw [if_neg hb]
      constructor
      · rintro (h | ⟨y, hy, hby, g, hg, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hby, g, hg, rfl⟩
      · rintro (h | ⟨y, hy, hby, g, hg, rfl⟩)
        · exact Or.inl h
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact absurd hby hb
          · exact Or.inr ⟨y, hy, hby, g, hg, rfl⟩

theorem closure_get {M : RegModel} {gs : List ℕ} (hgs : ∀ g ∈ gs, g < M.N)
    (hstep : ∀ g ∈ gs, ∀ y < M.N, M.m y g < M.N) (hN0 : 0 < M.N) {K : ℕ}
    (hfix : clStepK M.N M.m gs (clIterK M.N M.m gs K) = clIterK M.N M.m gs K) :
    (M.closure gs).size = M.N ∧
      ∀ z, (M.closure gs)[z]! = (decide (z < M.N) && (clIterK M.N M.m gs K).testBit z) := by
  obtain ⟨hsz, hmem, -, hlt, h0, hcl, hmin⟩ := bfsRun_spec gs (fun g y => M.m y g) (x0 := 0) hN0
    (fun g hg y hy => hstep g hg y hy)
  rw [closure_eq_bfsRun]
  refine ⟨hsz, fun z => ?_⟩
  set Q := (bfsRun M.N gs (fun g y => M.m y g) 0).2.toList with hQ
  have reach : ∀ k z, (clIterK M.N M.m gs k).testBit z = true → z ∈ Q := by
    intro k
    induction k with
    | zero =>
      intro z hz
      have : z = 0 := by
        have e : clIterK M.N M.m gs 0 = 2 ^ 0 := rfl
        rw [e, Nat.testBit_two_pow] at hz
        exact (of_decide_eq_true hz).symm
      rw [this]
      exact h0
    | succ k ih =>
      intro z hz
      rcases (testBit_clStepK _ _ _ _ _).1 hz with h | ⟨x, -, hx, g, hg, rfl⟩
      · exact ih z h
      · exact hcl x (ih x hx) g hg
  have marked : ∀ z ∈ Q, z < M.N ∧ (clIterK M.N M.m gs K).testBit z = true := by
    refine hmin (fun z => z < M.N ∧ (clIterK M.N M.m gs K).testBit z = true) ⟨hN0, ?_⟩ ?_
    · have : ∀ k, (clIterK M.N M.m gs k).testBit 0 = true := by
        intro k
        induction k with
        | zero =>
          have e : clIterK M.N M.m gs 0 = 2 ^ 0 := rfl
          rw [e, Nat.testBit_two_pow]
          rfl
        | succ k ih => exact (testBit_clStepK _ _ _ _ _).2 (Or.inl ih)
      exact this K
    · rintro g hg y ⟨hy, hb⟩
      refine ⟨hstep g hg y hy, ?_⟩
      rw [← hfix]
      exact (testBit_clStepK _ _ _ _ _).2 (Or.inr ⟨y, hy, hb, g, hg, rfl⟩)
  rw [Bool.eq_iff_iff, hmem, Bool.and_eq_true, decide_eq_true_iff]
  exact ⟨fun h => marked z h, fun h => reach K z h.2⟩

theorem autMap_get {M : RegModel} (hT : TreeSpec M) (hN : 0 < M.N) (img : Array ℕ) {f : ℕ → ℕ}
    (hf0 : f 0 = 0)
    (hrec : ∀ i, 0 < i → i < M.N → f M.order[i]! = M.m img[M.label[i]!]! (f M.parent[i]!)) :
    ∀ x, (M.autMap img)[x]! = if x < M.N then f x else 0 := by
  have inv : ∀ k, k + 1 ≤ M.N →
      ((List.range' 1 k).foldl
        (fun a i => a.set! M.order[i]! (M.m img[M.label[i]!]! a[M.parent[i]!]!))
        (Array.replicate M.N 0)).size = M.N ∧
      ∀ i ≤ k, ((List.range' 1 k).foldl
          (fun a i => a.set! M.order[i]! (M.m img[M.label[i]!]! a[M.parent[i]!]!))
          (Array.replicate M.N 0))[M.order[i]!]! = f M.order[i]! := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨by simp, fun i hi => ?_⟩
      obtain rfl : i = 0 := by omega
      rw [hT.order_zero, List.range'_zero, List.foldl_nil, getElem!_replicate_zero, hf0]
    | succ k ih =>
      intro hk
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
        show 1 + 1 * k = k + 1 by omega]
      refine ⟨by rw [Array.size_set!, ih1], fun i hi => ?_⟩
      rcases Nat.lt_or_eq_of_le hi with hi | rfl
      · have hne : M.order[k + 1]! ≠ M.order[i]! :=
          fun he => by have := hT.order_inj _ _ (by omega) (by omega) he; omega
        rw [Array.getElem!_set!_ne _ _ _ _ hne, ih2 i (by omega)]
      · rw [Array.getElem!_set!_self _ _ _ (by rw [ih1]; exact hT.order_lt _ (by omega))]
        obtain ⟨q, hq, hpar, -, -⟩ := hT.step (k + 1) (by omega) (by omega)
        rw [hpar, ih2 q (by omega), ← hpar, hrec (k + 1) (by omega) (by omega)]
  obtain ⟨h1, h2⟩ := inv (M.N - 1) (by omega)
  intro x
  rw [autMap_eq_foldl, hT.size_order]
  by_cases hx : x < M.N
  · rw [if_pos hx]
    have hsurj : Function.Surjective (fun i : Fin M.N => (⟨M.order[i.1]!, hT.order_lt i.1 i.2⟩ :
        Fin M.N)) := Finite.surjective_of_injective fun i j hij =>
      Fin.ext (hT.order_inj i j i.2 j.2 (congrArg Fin.val hij))
    obtain ⟨i, hi⟩ := hsurj ⟨x, hx⟩
    have e : M.order[i.1]! = x := congrArg Fin.val hi
    rw [← e]
    exact h2 i (by omega)
  · rw [if_neg hx, getElem!_neg _ _ (by rw [h1]; exact hx)]
    rfl

theorem tabImgs_get {M : RegModel} {m : ℕ → ℕ → ℕ} {inv g : ℕ → ℕ}
    (hm : ∀ a b, M.m a b = m a b) (hinv : ∀ a, M.inv[a]! = inv a) (hg : ∀ j, M.g j = g j)
    {α k : ℕ} (hα : α ≠ 2) {j : ℕ} (hj : j < 7) :
    (M.tabImgs α k)[j]! = imgK m inv g α k j := by
  have hev : ∀ t : Tm, M.evalT t = evalK m inv g t := by
    intro t
    induction t with
    | var i => exact hg i
    | one => rfl
    | mul a b iha ihb => simp only [RegModel.evalT, evalK, iha, ihb, hm]
    | inv a iha => simp only [RegModel.evalT, evalK, iha, hinv]
  unfold RegModel.tabImgs imgK
  rw [getElem!_pos _ _ (by simpa using hj), Array.getElem_map, Array.getElem_range]
  simp only [hα, if_false]
  cases (actRels α k).find? (fun e => e.1 == j) with
  | none => rfl
  | some e => exact hev e.2

end CFSG.KC.ChengHeldS2

end
