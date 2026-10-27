module

public import CFSG.Certificates.Kernel.Misc.OqSound
public import Certificates.Data.Kernel.Misc.OqBlk

public section

namespace CFSG.KC.Misc.Oq

open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

theorem getLL_eq (L : List (List ℕ)) (i : ℕ) : getLL L i = L.getD i [] := by
  have h : ∀ M : List (List ℕ),
      List.rec (motive := fun _ => List ℕ) List.nil (fun x _ _ => x) M = M.head?.getD [] := by
    intro M
    cases M <;> rfl
  rw [getLL, h, dropK_eq, List.head?_drop, List.getD_eq_getElem?_getD]

theorem certLetK_sound {CD : List (List (List ℕ) × ℕ × ℕ)} (h : certLetK CD = true) :
    ∀ c ∈ CD, ∀ x ∈ c.1, ∀ a ∈ x, a < 4 := by
  induction CD with
  | nil => simp
  | cons c t ih =>
    change andB (allLL c.1 fun x => allL x fun a => Nat.blt a 4) (certLetK t) = true at h
    rw [andB_iff] at h
    have hc : ∀ (W : List (List ℕ)), allLL W (fun x => allL x fun a => Nat.blt a 4) = true →
        ∀ x ∈ W, ∀ a ∈ x, a < 4 := by
      intro W
      induction W with
      | nil => simp
      | cons y W ihW =>
        intro hW x hx a ha
        change andB (allL y fun a => Nat.blt a 4)
          (allLL W fun x => allL x fun a => Nat.blt a 4) = true at hW
        rw [andB_iff] at hW
        rcases List.mem_cons.1 hx with rfl | hx
        · have h4 := allL_iff'.1 hW.1 a ha
          rwa [Nat.blt_eq] at h4
        · exact ihW hW.2 x hx a ha
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact hc _ h.1
    · exact ih h.2 d hd

theorem certsK_let_sound {u : ℕ} {KR : List ℕ} {CD : List (List (List ℕ) × ℕ × ℕ)}
    (h : certsK u KR CD = true) (hl : ∀ c ∈ CD, ∀ x ∈ c.1, ∀ a ∈ x, a < 4) :
    ∀ P ∈ KR, validK u P = true ∧
      ∃ ws v w, (∀ x ∈ ws, ∀ a ∈ x, a < 4) ∧ certK u P ws v w = true := by
  induction KR generalizing CD with
  | nil => simp
  | cons P t ih =>
    cases CD with
    | nil =>
      change false = true at h
      exact absurd h (by decide)
    | cons c s =>
      change andB (andB (validK u P) (certK u P c.1 c.2.1 c.2.2)) (certsK u t s) = true at h
      rw [andB_iff, andB_iff] at h
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨h.1.1, c.1, c.2.1, c.2.2, hl c List.mem_cons_self, h.1.2⟩
      · exact ih h.2 (fun d hd => hl d (List.mem_cons_of_mem _ hd)) x hx

theorem blocks_eq (u b : ℕ) (L : List (ℕ × List ℕ × List ℕ)) (n : ℕ) :
    ∀ (a : ℕ) (P : ℕ → List ℕ), L.drop (a + b * n) = [] →
      (∀ i < n, fstsK (levels2K u 4 (takeK b (dropK (a + b * i) L))) = P i) →
      fstsK (levels2K u 4 (L.drop a)) = ((List.range n).map P).flatten := by
  have e : ∀ a m : ℕ, a + b * (m + 1) = a + b + b * m := fun a m => by
    rw [Nat.mul_succ, Nat.add_comm (b * m) b, Nat.add_assoc]
  induction n with
  | zero =>
    intro a P h0 _
    rw [Nat.mul_zero, Nat.add_zero] at h0
    rw [h0]
    rfl
  | succ n ih =>
    intro a P h0 hP
    rw [drop_split L a b, fin_append, List.range_succ_eq_map, List.map_cons, List.flatten_cons,
      List.map_map]
    have h1 := hP 0 (Nat.succ_pos n)
    rw [Nat.mul_zero, Nat.add_zero] at h1
    rw [h1, ih (a + b) (P ∘ Nat.succ) (by rw [← e]; exact h0) fun i hi => by
      have h2 := hP (i + 1) (Nat.succ_lt_succ hi)
      rw [e] at h2
      exact h2]

theorem facts_of (u : Bool) (b n nR nS nV : ℕ) (parts : List (List ℕ)) (hn : parts.length = n)
    (hst : stabP u = parts.flatten) (hV : nV = b * n)
    (hR : nR = (if u then 63 else 49)) (hS : nS = (if u then 5760 else 1152))
    (hblk : ∀ i < n, blkK (b2n u) b (repP u) (brP u) (fstIK (invD u)) (parts.getD i []) i = true)
    (hrep : repOK (b2n u) (repP u) (brP u) (krP u) (stabP u) (invD u) (certD u) nR nS nV = true)
    (hkr : ∀ k, k < (killReps u).length →
      unpack6 ((krP u).getD k 0) = ((killReps u).getD k ([], [])).1)
    (hkl : (krP u).length = (killReps u).length) :
    oqFrom u 1 = (stabP u).map unpack6 ∧
    (∀ t, t < 64 → (∀ r ∈ repP u, r % 64 ≠ t) → oqFrom u t = []) ∧
    ((repP u).map (· % 64)).Nodup ∧
    (repP u).length = (if u then 63 else 49) ∧
    (stabP u).length = (if u then 5760 else 1152) ∧
    strictSorted ((stabP u).map fun x => codeT (unpack6 x)) = true ∧
    (∀ x ∈ repP u, validT u (unpack6 x) = true ∧ sgnOK u (unpack6 x) = true) ∧
    (∀ x ∈ stabP u, validT u (unpack6 x) = true ∧ sgnOK u (unpack6 x) = true) ∧
    (∀ r ∈ repP u, ∀ s ∈ stabP u,
      (u = true → bMul (bOf u (unpack6 r)) (bOf u (unpack6 s)) = idE →
        compT (unpack6 r) (unpack6 s) = idT ∨ compT (unpack6 r) (unpack6 s) = omT ∨
          compT (unpack6 r) (unpack6 s) = compT omT omT) ∧
      (isInvT (compT (unpack6 r) (unpack6 s)) = true →
        presT u (compT (unpack6 r) (unpack6 s)) = true →
          compT (unpack6 r) (unpack6 s) ∈ (invD u).map fun e => unpack6 e.1)) ∧
    (∀ e ∈ invD u, (∀ a ∈ e.2.1, a < 3) ∧ ∃ k, k < (killReps u).length ∧
      compT (evalW (unpack6 e.1) e.2.1) (unpack6 e.1) =
        compT ((killReps u).getD k ([], [])).1 (evalW (unpack6 e.1) e.2.1)) ∧
    (∀ k, k < (killReps u).length → validT u ((killReps u).getD k ([], [])).1 = true ∧
      ∃ c, validCert u ((killReps u).getD k ([], [])).1 c = true) := by
  unfold repOK at hrep
  simp only [andB_iff] at hrep
  obtain ⟨hsort, hhead, hbad, hinv, hconj, hcert, hlet, hlR, hlS, hnil, hRv⟩ := hrep
  have hblocks : ∀ i < n, fstsK (levels2K (b2n u) 4 (takeK b (dropK (0 + b * i) (lev3K (b2n u))))) =
      parts.getD i [] := by
    intro i hi
    have h := hblk i hi
    unfold blkK at h
    rw [andB_iff] at h
    rw [Nat.zero_add]
    exact eqLN_sound h.1
  have hnil' : (lev3K (b2n u)).drop (0 + b * n) = [] := by
    rw [Nat.zero_add, ← hV, ← dropK_eq]
    exact isNilK_iff.1 hnil
  have hrange : ((List.range parts.length).map fun i => parts.getD i []) = parts := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [List.getElem?_eq_getElem h2]
  have hsearch : search2K (b2n u) 1 = stabP u := by
    rw [search2K_one, ← List.drop_zero (l := lev3K (b2n u)),
      blocks_eq _ b _ n 0 (fun i => parts.getD i []) hnil' hblocks, ← hn, hrange, hst]
  have hstab : ∀ s ∈ stabP u, andB (andB (validK (b2n u) s) (sgnK (b2n u) s))
      (elemT (b2n u) (rtK (repP u) (brP u)) (fstIK (invD u)) (tabK s) (bOfK (b2n u) s)) = true := by
    intro s hs
    rw [hst, List.mem_flatten] at hs
    obtain ⟨l, hl, hsl⟩ := hs
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hl
    have h := hblk i (hn ▸ hi)
    unfold blkK at h
    rw [andB_iff, List.getD_eq_getElem _ _ hi] at h
    exact allL_iff'.1 h.2 s hsl
  refine ⟨?_, fun t ht hR => badK_sound u hbad ht hR, ?_, ?_, ?_, sortedK_sound hsort,
    fun x hx => ?_, fun x hx => ?_, fun r hr s hs => ?_, fun e he => ?_, fun k hk => ?_⟩
  · rw [← search2K_sound u (by decide : 1 < 64), hsearch]
  · rw [← headK_eq]
    exact nodupK_sound hhead
  · rw [← lenK_eq, Nat.eq_of_beq_eq_true hlR, hR]
  · rw [← lenK_eq, Nat.eq_of_beq_eq_true hlS, hS]
  · have h := allL_iff'.1 hRv x hx
    rw [andB_iff] at h
    exact ⟨validK_sound u h.1, sgnK_sound u h.2⟩
  · have h := hstab x hx
    rw [andB_iff, andB_iff] at h
    exact ⟨validK_sound u h.1.1, sgnK_sound u h.1.2⟩
  · have h := elem_sound u (R := repP u) (S := stabP u) hinv
      (fun s hs => (andB_iff.1 (hstab s hs)).2) r hr s hs
    rw [fstIK_eq, List.map_map] at h
    exact h
  · obtain ⟨hk, hc⟩ := conjsK_sound hconj e he
    obtain ⟨h3, heq⟩ := conjK_sound hc
    rw [hkl] at hk
    refine ⟨h3, e.2.2, hk, ?_⟩
    rw [heq, hkr _ hk]
  · have hmem : (krP u).getD k 0 ∈ krP u := by
      rw [List.getD_eq_getElem _ _ (by rw [hkl]; exact hk)]
      exact List.getElem_mem _
    obtain ⟨hv, ws, v, w, hws, hc⟩ :=
      certsK_let_sound hcert (certLetK_sound hlet) _ hmem
    rw [← hkr _ hk]
    exact ⟨validK_sound u hv, (ws, v, w), certK_sound u hws hc⟩

end CFSG.KC.Misc.Oq

end
