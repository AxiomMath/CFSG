module

public import CFSG.Certificates.Kernel.Spor.NKeyBfs
public import CFSG.Certificates.Kernel.Spor.NFDecode

public section

namespace CFSG.KS.SporSch.ClR

open CFSG.KS CFSG.KS.Raw.Dec CFSG.KS.NKey CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Sporadic.Schreier.PairNative

theorem imgKey_cons (n a : Nat) (l : List Nat) : imgKey n (a :: l) = a + n * imgKey n l := rfl

theorem imgKey_inj {n : Nat} : ∀ {l₁ l₂ : List Nat}, l₁.length = l₂.length →
    (∀ x ∈ l₁, x < n) → (∀ x ∈ l₂, x < n) → imgKey n l₁ = imgKey n l₂ → l₁ = l₂
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, hl, _, _, _ => absurd hl (by simp)
  | _ :: _, [], hl, _, _, _ => absurd hl (by simp)
  | a :: l₁, b :: l₂, hl, h1, h2, he => by
    have ha := h1 a List.mem_cons_self
    have hb := h2 b List.mem_cons_self
    have hn : 0 < n := by omega
    rw [imgKey_cons, imgKey_cons] at he
    have e1 : a = b := by
      have := congrArg (· % n) he
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
      exact this
    have e2 : imgKey n l₁ = imgKey n l₂ := by
      have := congrArg (· / n) he
      simp only [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb,
        Nat.zero_add] at this
      exact this
    rw [e1, imgKey_inj (by simpa using hl) (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
      (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) e2]

theorem mem_base_lt {n nb : Nat} {base : Array Nat} (hbs : base.size = nb)
    (hbl : ∀ t < nb, base[t]! < n) {b : Nat} (hm : b ∈ base.toList) : b < n := by
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hm
  have ht' : t < base.size := by simpa using ht
  have := hbl t (by rw [← hbs]; exact ht')
  rw [Array.getElem_toList]
  rwa [getElem!_pos base t ht'] at this

theorem getElem!_ofFn_gen {β : Type} [Inhabited β] {m : Nat} (f : Fin m → β) {i : Nat}
    (hi : i < m) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem conjClosureNF_eq (n : Nat) (L : Array Level) (bs : List Nat)
    (gens gensInv : Array (Array Nat)) (nf₀ : Array Nat) (cap : Nat) :
    conjClosureNF n L bs gens gensInv nf₀ cap =
      nkbfs (fun l nf => imgKey n (conjImgs bs gens[l]! gensInv[l]! (nfWord L nf)))
        (fun l nf => decodeNF L (conjImgs bs gens[l]! gensInv[l]! (nfWord L nf)).toArray)
        gens.size nf₀ (imgKey n (baseImgs bs (nfWord L nf₀))) cap := rfl

theorem closure_replay {n : Nat} {L : Array Level} {bs : List Nat}
    {gens gensInv : Array (Array Nat)} {rep : List (Array Nat)} {c cap fl M H : Nat}
    {T : Nat → Array Nat} {P Lb K C : Nat → Nat} {KS pos : Nat → Nat → Nat}
    {f : Nat → Nat → Nat → Nat}
    (hLv : LvOK n L bs) (hbn : ∀ b ∈ bs, b < n)
    (hgr : ∀ l < gens.size, ∀ y < n, (gens[l]!)[y]! < n ∧ (gensInv[l]!)[y]! < n)
    (hrr : ∀ x ∈ baseImgs bs rep, x < n)
    (hc0 : 0 < c) (hcap : c ≤ cap) (hcM : c ≤ M * H) (hfl : c ≠ fl)
    (hC0 : C 0 = 1) (hCM : C M = c) (hrun : ∀ t < M, runC f gens.size H (t * H) (C t) = C (t + 1))
    (habs : ∀ h l, l < gens.size → f h l fl = fl)
    (hT : ∀ i < c, nfOK L (T i) = true)
    (hκ : ∀ i < c, imgKey n (baseImgs bs (nfWord L (T i))) = K i)
    (hsk : ∀ h < c, ∀ l < gens.size, imgKey n (conjImgs bs gens[l]! gensInv[l]! (nfWord L (T h))) =
      KS h l)
    (hinj : ∀ a < c, ∀ b < c, K a = K b → a = b)
    (hk0 : imgKey n (baseImgs bs rep) = K 0) (hP0 : P 0 = 0) (hL0 : Lb 0 = 0)
    (hstep : ∀ h l cur, l < gens.size → f h l cur ≠ fl →
      (h < cur ∧ pos h l < cur ∧ K (pos h l) = KS h l ∧ f h l cur = cur) ∨
      (h < cur ∧ pos h l = cur ∧ K (pos h l) = KS h l ∧ P (pos h l) = h ∧ Lb (pos h l) = l ∧
        f h l cur = cur + 1) ∨
      (cur ≤ h ∧ cur = c ∧ f h l cur = cur)) :
    closureOK L bs gens gensInv rep
        (conjClosureNF n L bs gens gensInv (decodeNF L (baseImgs bs rep).toArray) cap).1
        (conjClosureNF n L bs gens gensInv (decodeNF L (baseImgs bs rep).toArray) cap).2.1
        (conjClosureNF n L bs gens gensInv (decodeNF L (baseImgs bs rep).toArray) cap).2.2 = true ∧
      (conjClosureNF n L bs gens gensInv (decodeNF L (baseImgs bs rep).toArray) cap).1.size = c ∧
      (conjClosureNF n L bs gens gensInv (decodeNF L (baseImgs bs rep).toArray) cap).1.toList.map
          (fun nf => imgKey n (baseImgs bs (nfWord L nf))) = (List.range c).map K := by
  have hBI : ∀ nf, nfOK L nf = true → ∀ x ∈ baseImgs bs (nfWord L nf), x < n := by
    intro nf hnf' x hx
    obtain ⟨b, hm, rfl⟩ := List.mem_map.1 hx
    rw [nfWord_eq_hw]
    exact evR_hw_lt hLv hnf' _ (Nat.le_refl _) b (hbn b hm)
  have hCI : ∀ l < gens.size, ∀ nf, nfOK L nf = true →
      ∀ x ∈ conjImgs bs gens[l]! gensInv[l]! (nfWord L nf), x < n := by
    intro l hl' nf hnf' x hx
    obtain ⟨b, hm, rfl⟩ := List.mem_map.1 hx
    have hy := (hgr l hl' b (hbn b hm)).2
    refine (hgr l hl' _ ?_).1
    rw [nfWord_eq_hw]
    exact evR_hw_lt hLv hnf' _ (Nat.le_refl _) _ hy
  have hdec : ∀ (l : List Nat), ∀ i < c, l.length = bs.length → (∀ x ∈ l, x < n) →
      imgKey n l = K i → l = baseImgs bs (nfWord L (T i)) ∧ decodeNF L l.toArray = T i := by
    intro l i hi hlen hlt hk
    have e := imgKey_inj (by rw [hlen, baseImgs, List.length_map]) hlt (hBI _ (hT i hi))
      (hk.trans (hκ i hi).symm)
    refine ⟨e, ?_⟩
    rw [e]
    exact decodeNF_nfWord hLv (hT i hi)
  have hroot : T 0 = decodeNF L (baseImgs bs rep).toArray :=
    ((hdec _ 0 hc0 (by simp [baseImgs]) hrr hk0).2).symm
  have R : NKRec (fun l nf => imgKey n (conjImgs bs gens[l]! gensInv[l]! (nfWord L nf)))
      (fun l nf => decodeNF L (conjImgs bs gens[l]! gensInv[l]! (nfWord L nf)).toArray)
      (fun nf => imgKey n (baseImgs bs (nfWord L nf))) gens.size
      (decodeNF L (baseImgs bs rep).toArray)
      (imgKey n (baseImgs bs (nfWord L (decodeNF L (baseImgs bs rep).toArray)))) c T P Lb pos := by
    refine runC_rec (f := f) (fl := fl) (M := M) (H := H) (C := C) hc0 hcM hfl hC0 hCM hrun habs
      (fun h l cur hl' hne => ?_) hroot rfl hP0 hL0 (fun a ha b hb' e => ?_)
    · rcases hstep h l cur hl' hne with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3⟩
      · refine Or.inl ⟨h1, h2, h4, fun hcur => ?_⟩
        dsimp only
        rw [hsk h (by omega) l hl', hκ _ (by omega), h3]
      · refine Or.inr (Or.inl ⟨h1, h2, h6, fun hcur => ?_⟩)
        rw [h2] at h3 h4 h5
        have hk : imgKey n (conjImgs bs gens[l]! gensInv[l]! (nfWord L (T h))) = K cur := by
          rw [hsk h (by omega) l hl', h3]
        refine ⟨hk.trans (hκ cur hcur).symm, (hdec _ cur hcur (by simp [conjImgs])
          (hCI l hl' _ (hT h (by omega))) hk).2, h4, h5⟩
      · exact Or.inr (Or.inr ⟨h1, h2, h3⟩)
    · exact hinj a ha b hb' (by rw [← hκ a ha, ← hκ b hb']; exact e)
  rw [conjClosureNF_eq, nkbfs_rec R hcap]
  have hTa : ∀ i < c, (Array.ofFn (n := c) fun i => T i.val)[i]! = T i :=
    fun i hi => getElem!_ofFn_gen _ hi
  have hPa : ∀ i < c, (Array.ofFn (n := c) fun i => P i.val)[i]! = P i :=
    fun i hi => getElem!_ofFn_gen _ hi
  have hLa : ∀ i < c, (Array.ofFn (n := c) fun i => Lb i.val)[i]! = Lb i :=
    fun i hi => getElem!_ofFn_gen _ hi
  refine ⟨?_, Array.size_ofFn, ?_⟩
  · unfold closureOK allFrom
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allLt_iff, Array.size_ofFn,
      Bool.or_eq_true]
    refine ⟨⟨⟨hc0, fun i hi => by rw [hTa i hi]; exact hT i hi⟩, ?_⟩, fun i hi => ?_⟩
    · rw [hTa 0 hc0]
      exact (hdec _ 0 hc0 (by simp [baseImgs]) hrr hk0).1.symm
    · rcases Nat.lt_or_ge i 1 with h1 | h1
      · exact Or.inl h1
      · right
        obtain ⟨a1, a2, a3, -⟩ := R.tree i (by omega) hi
        rw [hTa i hi, hPa i hi, hLa i hi, hTa _ (by omega)]
        refine ⟨⟨a1, a2⟩, ?_⟩
        exact (imgKey_inj (by simp [baseImgs, conjImgs]) (hBI _ (hT i hi))
          (hCI _ a2 _ (hT _ (by omega))) a3.symm)
  · apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, Array.getElem_toList, Array.getElem_ofFn, List.getElem_range]
      exact hκ i (by simpa using h2)

end CFSG.KS.SporSch.ClR

end
