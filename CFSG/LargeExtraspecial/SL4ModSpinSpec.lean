module

public import CFSG.Sporadic.HS.SmallF2Spec
public import CFSG.LargeExtraspecial.SL4ModNativeSpin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.SL4Mod

open Module CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Native

abbrev vec (x : ℕ) : Fin 105 → ZMod 2 := toVecD 105 x

@[expose] def tauF (t : Array ℕ) (k : Fin 105) : Fin 105 :=
  ⟨t[k.val]! % 105, Nat.mod_lt _ (by norm_num)⟩

theorem vec_actV (t : Array ℕ) (x : ℕ) : vec (actV t x) = vec x ∘ tauF t := by
  funext k
  rw [vec, actV, toVecD_ofBits, Function.comp_apply]
  rfl

theorem vec_xorSel (mask : ℕ) (L : Array ℕ) :
    vec (xorSel mask L) = ∑ i ∈ Finset.range L.size, if mask.testBit i then vec L[i]! else 0 := by
  rw [vec, xorSel, foldl_xor_toVecD 105 (fun i => mask.testBit i = true) (fun i => L[i]!) L.size 0,
    toVecD_zero, zero_add]

theorem vec_ne_zero_of_nz {x : ℕ} (h : nz x = true) : vec x ≠ 0 := by
  intro hx
  have hbits : ∀ k < 105, x.testBit k = false := by
    intro k hk
    have := congrFun hx ⟨k, hk⟩
    rw [vec, toVecD_apply] at this
    by_contra hb
    rw [Bool.not_eq_false] at hb
    simp [hb] at this
  have h0 : x &&& (2 ^ 105 - 1) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.zero_testBit]
    by_cases hk : k < 105
    · rw [hbits k hk, Bool.false_and]
    · simp [hk]
  rw [nz, h0] at h
  exact absurd h (by decide)

@[expose] def spanB (B : Array ℕ) : Submodule (ZMod 2) (Fin 105 → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range fun i : Fin B.size => vec B[i.val]!)

theorem xorSel_mem {X : Submodule (ZMod 2) (Fin 105 → ZMod 2)} (mask : ℕ) {L : Array ℕ}
    (hL : ∀ i < L.size, vec L[i]! ∈ X) : vec (xorSel mask L) ∈ X := by
  rw [vec_xorSel]
  refine Submodule.sum_mem _ fun i hi => ?_
  split_ifs
  · exact hL i (Finset.mem_range.mp hi)
  · exact X.zero_mem

theorem mem_spanB_of_inSpan {x : ℕ} {B : Array ℕ} (h : inSpan x B = true) : vec x ∈ spanB B := by
  rw [inSpan, List.any_eq_true] at h
  obtain ⟨mask, -, hmask⟩ := h
  rw [beq_iff_eq] at hmask
  rw [← hmask]
  exact xorSel_mem mask fun i hi => Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩

theorem finrank_spanB_le (B : Array ℕ) : finrank (ZMod 2) (spanB B) ≤ B.size := by
  have := finrank_range_le_card (R := ZMod 2) (b := fun i : Fin B.size => vec B[i.val]!)
  rwa [Fintype.card_fin] at this

@[expose] def IsTauInv (taus : Array (Array ℕ)) (X : Submodule (ZMod 2) (Fin 105 → ZMod 2)) :
    Prop :=
  ∀ s < 6, ∀ F ∈ X, F ∘ tauF taus[s]! ∈ X

theorem mem_of_derivOK {taus : Array (Array ℕ)} {X : Submodule (ZMod 2) (Fin 105 → ZMod 2)}
    (hX : IsTauInv taus X) {m : ℕ} (hm : vec m ∈ X) {L : Array ℕ} {src : Array (ℕ × ℕ)}
    (h : derivOK taus m L src = true) : ∀ t < L.size, vec L[t]! ∈ X := by
  rw [derivOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨h0, h⟩ := h
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · rw [h0]
      exact hm
    · have := h t (List.mem_range.mpr ht)
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
      rcases this with h' | ⟨⟨hs, hp⟩, heq⟩
      · omega
      · rw [heq, vec_actV]
        exact hX _ hs _ (ih _ hp (lt_trans hp ht))

theorem isTauInv_spanB {taus : Array (Array ℕ)} {B : Array ℕ} (h : closedOK taus B = true) :
    IsTauInv taus (spanB B) := by
  intro s hs F hF
  rw [closedOK, List.all_eq_true] at h
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨i, rfl⟩ := hF
    have hi := h i.val (List.mem_range.mpr i.isLt)
    rw [List.all_eq_true] at hi
    have := mem_spanB_of_inSpan (hi s (List.mem_range.mpr hs))
    rwa [vec_actV] at this
  | zero => exact (spanB B).zero_mem
  | add F G _ _ hF hG => exact (spanB B).add_mem hF hG
  | smul c F _ hF => exact (spanB B).smul_mem c hF

theorem linearIndependent_of_indep9 {L : Array ℕ} (h : indep9 L = true) (hL : 9 ≤ L.size) :
    LinearIndependent (ZMod 2) fun t : Fin 9 => vec L[t.val]! := by
  rw [Fintype.linearIndependent_iff]
  intro g hg t₀
  by_contra ht₀
  have hg1 : ∀ t, g t ≠ 0 → g t = 1 := fun t => by
    generalize g t = x
    revert x
    decide
  let f : ℕ → Bool := fun t => if ht : t < 9 then g ⟨t, ht⟩ == 1 else false
  set mask := ofBits 9 f with hmask
  have hbit : ∀ i, mask.testBit i = (decide (i < 9) && f i) := fun i => ofBits_testBit 9 f i
  have hlt : mask < 512 := ofBits_lt 9 f
  have hne : mask ≠ 0 := by
    intro h0
    have := hbit t₀.val
    rw [h0, Nat.zero_testBit] at this
    simp [f, t₀.isLt, hg1 t₀ ht₀] at this
  rw [indep9, List.all_eq_true] at h
  have hm := h mask (List.mem_range.mpr hlt)
  rw [Bool.or_eq_true, beq_iff_eq] at hm
  have hnz := vec_ne_zero_of_nz (hm.resolve_left hne)
  apply hnz
  rw [vec_xorSel]
  have hsub : Finset.range 9 ⊆ Finset.range L.size := Finset.range_subset_range.mpr hL
  rw [← Finset.sum_subset hsub fun i _ hi => by
    rw [hbit i, decide_eq_false (by simpa using hi), Bool.false_and]; rfl]
  rw [← Fin.sum_univ_eq_sum_range (fun i => if mask.testBit i = true then vec L[i]! else 0)]
  have hsum : (∑ t : Fin 9, if mask.testBit t.val = true then vec L[t.val]! else 0) =
      ∑ t : Fin 9, g t • vec L[t.val]! := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hbit t.val]
    simp only [t.isLt, decide_true, Bool.true_and, f, ↓reduceDIte, Fin.eta]
    by_cases h1 : g t = 1
    · simp [h1]
    · have h0 : g t = 0 := by
        by_contra h0
        exact h1 (hg1 t h0)
      simp [h0]
  rw [hsum, hg]

theorem false_of_valid {taus : Array (Array ℕ)} {X : Submodule (ZMod 2) (Fin 105 → ZMod 2)}
    (hX : IsTauInv taus X) (hdim : finrank (ZMod 2) X = 8)
    (hirr : ∀ Y : Submodule (ZMod 2) (Fin 105 → ZMod 2), IsTauInv taus Y → Y ≤ X → Y ≠ ⊥ →
      X ≤ Y)
    {m : ℕ} (hm : vec m ∈ X) {c : SpinCert} (hc : valid taus m c = true) : False := by
  rw [valid, Bool.and_eq_true] at hc
  obtain ⟨hd, hc⟩ := hc
  have hL := mem_of_derivOK hX hm hd
  by_cases hbig : c.big = true
  · rw [ite_eq_left hbig, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨h9, hind⟩ := hc
    have hli := linearIndependent_of_indep9 hind h9
    let v : Fin 9 → X := fun t => ⟨vec c.L[t.val]!, hL t.val (lt_of_lt_of_le t.isLt h9)⟩
    have hv : LinearIndependent (ZMod 2) v := LinearIndependent.of_comp X.subtype hli
    have := hv.fintype_card_le_finrank
    rw [Fintype.card_fin, hdim] at this
    omega
  · rw [ite_eq_right hbig] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hnz, hB⟩, hin⟩, hcl⟩ := hc
    have hm'X := xorSel_mem c.sel hL
    have hm'0 := vec_ne_zero_of_nz hnz
    have hm'Y := mem_spanB_of_inSpan hin
    have hY := isTauInv_spanB hcl
    have hinv : IsTauInv taus (X ⊓ spanB c.B) := fun s hs F hF =>
      ⟨hX s hs F hF.1, hY s hs F hF.2⟩
    have hne : X ⊓ spanB c.B ≠ ⊥ := by
      intro h0
      apply hm'0
      have : vec (xorSel c.sel c.L) ∈ X ⊓ spanB c.B := ⟨hm'X, hm'Y⟩
      rw [h0, Submodule.mem_bot] at this
      exact this
    have hle := hirr _ hinv inf_le_left hne
    have h1 : finrank (ZMod 2) X ≤ finrank (ZMod 2) (spanB c.B) :=
      Submodule.finrank_mono (le_trans hle inf_le_right)
    have h2 := finrank_spanB_le c.B
    omega

theorem iterPar_eq {d : CosetData} {i : ℕ} {od : OrbData} {F : Fin 105 → ZMod 2}
    (hF : ∀ s ∈ orbGens i, F ∘ tauF d.tau[s]! = F)
    (hpar : ∀ k : Fin 105, od.par[k.val]! % 105 = k.val ∨
      ∃ s ∈ orbGens i, od.par[k.val]! % 105 = (d.tau[s]!)[k.val]! % 105) :
    ∀ (n : ℕ) (k : Fin 105), F k = F ⟨iterPar od.par n k.val % 105, Nat.mod_lt _ (by norm_num)⟩
  | 0, k => by
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt k.isLt).symm
  | n + 1, k => by
    have hstep : F k = F ⟨od.par[k.val]! % 105, Nat.mod_lt _ (by norm_num)⟩ := by
      rcases hpar k with h | ⟨s, hs, h⟩
      · congr 1
        exact Fin.ext h.symm
      · have := congrFun (hF s hs) k
        rw [Function.comp_apply] at this
        rw [← this]
        congr 1
        exact Fin.ext h.symm
    rw [hstep, iterPar_eq hF hpar n ⟨od.par[k.val]! % 105, Nat.mod_lt _ (by norm_num)⟩]
    rfl

theorem eq_vec_expand {d : CosetData} {i : ℕ} {od : OrbData} (h : checkOrb d i od = true)
    {F : Fin 105 → ZMod 2} (hF : ∀ s ∈ orbGens i, F ∘ tauF d.tau[s]! = F) :
    ∃ c < 128, F = vec (expand od c) ∧ (F ≠ 0 → c ≠ 0) := by
  rw [checkOrb, List.all_eq_true] at h
  have hk : ∀ k : Fin 105, (od.par[k.val]! % 105 = k.val ∨
      ∃ s ∈ orbGens i, od.par[k.val]! % 105 = (d.tau[s]!)[k.val]! % 105) ∧
      od.lab[k.val]! < 7 ∧ iterPar od.par 105 k.val = od.orep[od.lab[k.val]!]! % 105 := by
    intro k
    have := h k.val (List.mem_range.mpr k.isLt)
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
      decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hF' := iterPar_eq hF (fun k => (hk k).1) 105
  let orepF : ℕ → ZMod 2 := fun r => F ⟨od.orep[r]! % 105, Nat.mod_lt _ (by norm_num)⟩
  let c := ofBits 7 fun r => orepF r == 1
  have hc : ∀ k : Fin 105, F k = vec (expand od c) k := by
    intro k
    obtain ⟨-, hlab, hit⟩ := hk k
    rw [hF' k, vec, expand, toVecD_ofBits, ofBits_testBit]
    have e : (⟨iterPar od.par 105 k.val % 105, Nat.mod_lt _ (by norm_num)⟩ : Fin 105) =
        ⟨od.orep[od.lab[k.val]!]! % 105, Nat.mod_lt _ (by norm_num)⟩ := by
      apply Fin.ext
      simp only
      rw [hit, Nat.mod_mod]
    rw [e]
    simp only [hlab, decide_true, Bool.true_and]
    have key : ∀ x : ZMod 2, x = if (x == 1) = true then 1 else 0 := by decide
    exact key _
  refine ⟨c, ofBits_lt 7 _, funext hc, fun hF0 hc0 => hF0 (funext fun k => ?_)⟩
  rw [hc k, hc0]
  simp [vec, expand, toVecD_ofBits]

end CFSG.LargeExtraspecial.SL4Mod
