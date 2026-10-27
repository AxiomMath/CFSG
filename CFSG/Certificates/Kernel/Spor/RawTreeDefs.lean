module

public import Certificates.Data.Kernel.Spor.RawTree
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Co2

@[expose] def TreeOK (n w : Nat) (PS PSI LR : Nat → Nat) (kS nb BP : Nat) : Prop :=
  ∀ i < nb, lvHdTK n w (mask w) kS (pg w (mask w) BP i) (stepsAt n w PS kS BP i) (LR i) = true ∧
    ∀ k < n, lvPtTK n w (mask w) (n * w) PS PSI kS (stepsAt n w PS kS BP i) (LR i) (rcnt (LR i))
      (stCnt (stepsAt n w PS kS BP i)) k = true

@[expose] def StepsOK (n w : Nat) (PS ST : Nat → Nat) (kS nb BP : Nat) : Prop :=
  ∀ l < nb, ST l = stepsAt n w PS kS BP l

@[expose] def SchBOK (n w nb : Nat) (PS PSI LR ST : Nat → Nat) (kS BP : Nat) : Prop :=
  ∀ i < nb, ∀ h < rcnt (LR i), schBPt n w (mask w) (n * w) nb PS PSI LR ST kS BP i h = true

@[expose] def Sep (n : Nat) (S : Array (Array Nat)) (base : Array Nat) : Prop :=
  ∀ G ∈ Subgroup.closure {g : Equiv.Perm (Fin n) | ∃ j < S.size, permOfArr n S[j]! = g},
    (∀ t < base.size, ∀ h : base[t]! < n, G ⟨base[t]!, h⟩ = ⟨base[t]!, h⟩) → G = 1

@[expose] def rawHeadOK (n : Nat) (O S : Array (Array Nat)) (base : Array Nat)
    (W : Array (List Int)) : Bool :=
  let Sinv := rawInvs n S
  decide (O.size ≤ S.size) && W.size == S.size &&
    allLt S.size (fun j => isInvA n S[j]! Sinv[j]!) &&
    allLt O.size (fun k => eqA n S[k]! O[k]!) &&
    allLt S.size (fun j => decide (j < O.size) ||
      (lettersOK j W[j]! && eqA n S[j]! (wordA n S Sinv W[j]!))) &&
    allLt S.size (fun j => !(fixesFirst base S[j]! base.size) || eqA n S[j]! (idA n)) &&
    allLt base.size (fun i => decide (base[i]! < n))

@[expose] def levelOKT (n root : Nat) (steps : Array (Array Nat)) (L : Level) : Bool :=
  let m := L.pts.size
  let r := steps.size
  decide (0 < m) && decide (m ≤ n) && L.pts[0]! == root &&
    allLt m (fun k => decide (L.pts[k]! < n) && L.pos[L.pts[k]!]! == k) &&
    allLt n (fun z => !(decide (L.pos[z]! < m)) || L.pts[L.pos[z]!]! == z) &&
    allLt m (fun k => k == 0 || (decide (L.par[k]! < k) && decide (L.lab[k]! < r) &&
      (steps[L.lab[k]!]!)[L.pts[L.par[k]!]!]! == L.pts[k]!)) &&
    allLt m (fun k => k == 0 || !(decide (k + 1 < m)) ||
      lexLt L.par[k]! L.lab[k]! L.par[k + 1]! L.lab[k + 1]!) &&
    allLt m (fun h => allLt r fun j =>
      let k := L.pos[(steps[j]!)[L.pts[h]!]!]!
      decide (k < m) && (k == 0 || !(lexLt h j L.par[k]! L.lab[k]!)))

@[expose] def levelTrOK (n : Nat) (steps : Array (Array Nat)) (L : Level) : Bool :=
  let m := L.pts.size
  eqA n L.tr[0]! (idA n) &&
    allLt m (fun k => k == 0 || eqA n L.tr[k]! (compA n steps[L.lab[k]!]! L.tr[L.par[k]!]!)) &&
    allLt m (fun k => isInvA n L.tr[k]! L.trInv[k]!)

theorem levelOK_of {n root : Nat} {steps : Array (Array Nat)} {L : Level}
    (h1 : levelOKT n root steps L = true) (h2 : levelTrOK n steps L = true) :
    levelOK n root steps L = true := by
  unfold levelOKT at h1
  unfold levelTrOK at h2
  unfold levelOK
  simp only [Bool.and_eq_true] at h1 h2 ⊢
  tauto

theorem stepsOK_of {n w : Nat} {PS ST : Nat → Nat} {kS nb BP : Nat}
    (h : allN nb (fun l => Nat.beq (ST l) (stepsAt n w PS kS BP l)) = true) :
    StepsOK n w PS ST kS nb BP := fun l hl => Nat.eq_of_beq_eq_true (allN_spec h l hl)

theorem slice_cover {n NS CH k : Nat} (hN : n ≤ NS * CH) (hk : k < n) :
    0 < CH ∧ k / CH < NS ∧ Nat.add (k / CH * CH) (k % CH) = k := by
  have hCH : 0 < CH := by
    rcases Nat.eq_zero_or_pos CH with h0 | h0
    · rw [h0, Nat.mul_zero] at hN
      omega
    · exact h0
  refine ⟨hCH, ?_, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul hCH]
    omega
  · rw [Nat.add_eq]
    exact Nat.div_add_mod' k CH

theorem treeLv_of_sl {n w m nw kS root T R NS CH : Nat} {S SI : Nat → Nat}
    (hh : lvHdTK n w m kS root T R = true)
    (hs : ∀ s < NS, lvSlTK n w m nw S SI kS T R (s * CH) CH = true) (hN : n ≤ NS * CH) :
    lvHdTK n w m kS root T R = true ∧
      ∀ k < n, lvPtTK n w m nw S SI kS T R (rcnt R) (stCnt T) k = true := by
  refine ⟨hh, fun k hk => ?_⟩
  obtain ⟨hCH, hsk, e⟩ := slice_cover hN hk
  have h1 := allN_spec (hs (k / CH) hsk) (k % CH) (Nat.mod_lt _ hCH)
  rwa [e] at h1

theorem schB_of_sl {n w m nw nb kS BP i NS CH : Nat} {S SI LR ST : Nat → Nat}
    (hN : rcnt (LR i) ≤ NS * CH)
    (hs : ∀ s < NS, schBK n w m nw nb S SI LR ST kS BP i (s * CH) CH = true) :
    ∀ h < rcnt (LR i), schBPt n w m nw nb S SI LR ST kS BP i h = true := by
  intro h hh
  obtain ⟨hCH, hsk, e⟩ := slice_cover hN hh
  have h0 := hs (h / CH) hsk
  unfold schBK at h0
  rw [strictB_eq] at h0
  have h1 := allN_spec h0 (h % CH) (Nat.mod_lt _ hCH)
  rw [strictB_eq, e] at h1
  exact bIf_of_true (Nat.blt_eq ▸ hh) h1

theorem isInvA_of_rep {n : Nat} {t r : Array Nat} {g : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hr : Rep n r g⁻¹) : isInvA n t r = true := by
  unfold isInvA
  rw [allLt_iff]
  intro i hi
  rw [ht.apply hi, hr (g ⟨i, hi⟩)]
  simp

theorem invCand_eq_foldl (n : Nat) (t : Array Nat) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem rep_invCand {n : Nat} {t : Array Nat} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [invCand_eq_foldl]
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e, hi _ (g⁻¹ x).2]

theorem forIn_list_inv {β : Type} (l : List Nat) (init : β) (f : Nat → β → Id (ForInStep β))
    (I : β → Prop) (h0 : I init) (hf : ∀ a ∈ l, ∀ b, I b → I (Id.run (f a b)).value) :
    I (Id.run (forIn l init f)) := by
  induction l generalizing init with
  | nil => exact h0
  | cons a l ih =>
    rw [List.forIn_cons]
    have h1 := hf a List.mem_cons_self init h0
    cases e : f a init with
    | done b =>
      rw [e] at h1
      exact h1
    | yield b =>
      rw [e] at h1
      exact ih b h1 fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')

theorem forIn_range_inv {β : Type} (n : Nat) (init : β) (f : Nat → β → Id (ForInStep β))
    (I : β → Prop) (h0 : I init) (hf : ∀ a < n, ∀ b, I b → I (Id.run (f a b)).value) :
    I (Id.run (forIn [0:n] init f)) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine forIn_list_inv _ init f I h0 fun a ha b hb => hf a ?_ b hb
  rw [List.mem_range'] at ha
  simp [Std.Legacy.Range.size] at ha
  omega

theorem eqA_self {n : Nat} (a : Array Nat) : eqA n a a = true := by
  unfold eqA
  rw [allLt_iff]
  intro i _
  simp

@[expose] def TrInv (n : Nat) (steps : Array (Array Nat)) (pts par lab : Array Nat)
    (tr : Array (Array Nat)) : Prop :=
  tr.size = pts.size ∧ par.size = pts.size ∧ lab.size = pts.size ∧ 0 < pts.size ∧
    tr[0]! = idA n ∧ ∀ k, 0 < k → k < pts.size →
      par[k]! < k ∧ lab[k]! < steps.size ∧ tr[k]! = compA n steps[lab[k]!]! tr[par[k]!]!

theorem push_get_lt {α : Type} [Inhabited α] {xs : Array α} {x : α} {i : Nat}
    (h : i < xs.size) : (xs.push x)[i]! = xs[i]! := by
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos _ i h, Array.getElem_push_lt h]

theorem push_get_eq {α : Type} [Inhabited α] {xs : Array α} {x : α} {i : Nat} (h : i = xs.size) :
    (xs.push x)[i]! = x := by
  subst h
  rw [getElem!_pos _ _ (by simp)]
  exact Array.getElem_push_eq

theorem trInv_push {n : Nat} {steps : Array (Array Nat)} {pts par lab : Array Nat}
    {tr : Array (Array Nat)} (hI : TrInv n steps pts par lab tr) {h j y : Nat}
    (hh : h < pts.size) (hj : j < steps.size) :
    TrInv n steps (pts.push y) (par.push h) (lab.push j) (tr.push (compA n steps[j]! tr[h]!)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI
  refine ⟨by simp [h1], by simp [h2], by simp [h3], by simp, ?_, fun k hk0 hk => ?_⟩
  · rw [push_get_lt (by omega)]
    exact h5
  · rw [Array.size_push] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hlt | e
    · obtain ⟨a1, a2, a3⟩ := h6 k hk0 hlt
      rw [push_get_lt (by omega), push_get_lt (by omega), push_get_lt (by omega),
        push_get_lt (by omega)]
      exact ⟨a1, a2, a3⟩
    · rw [push_get_eq (by omega), push_get_eq (by omega), push_get_eq (by omega),
        push_get_lt (by omega)]
      exact ⟨by omega, hj, rfl⟩

theorem levelTrOK_of_inv {n : Nat} {steps : Array (Array Nat)} {pts pos par lab : Array Nat}
    {tr : Array (Array Nat)} (hI : TrInv n steps pts par lab tr)
    (hs : ∀ j < steps.size, ∃ g : Equiv.Perm (Fin n), Rep n steps[j]! g) :
    levelTrOK n steps ⟨pts, pos, par, lab, tr, tr.map (invCand n)⟩ = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI
  have hrep : ∀ k < pts.size, ∃ g : Equiv.Perm (Fin n), Rep n tr[k]! g := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [h5]
        exact ⟨1, rep_idA⟩
      · obtain ⟨a1, a2, a3⟩ := h6 k hk0 hk
        obtain ⟨g, hg⟩ := hs _ a2
        obtain ⟨g', hg'⟩ := ih _ a1 (by omega)
        rw [a3]
        exact ⟨_, rep_compA hg hg'⟩
  unfold levelTrOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨by rw [h5]; exact eqA_self _, allLt_iff.2 fun k hk => ?_⟩, allLt_iff.2 fun k hk => ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rfl
    · rw [(h6 k hk0 hk).2.2]
      simp [eqA_self]
  · obtain ⟨g, hg⟩ := hrep k hk
    rw [getElem!_pos (tr.map (invCand n)) k (by simp [h1, hk]), Array.getElem_map,
      ← getElem!_pos tr k (by rw [h1]; exact hk)]
    exact isInvA_of_rep hg (rep_invCand hg)

theorem levelTrOK_bfs {n root : Nat} {steps : Array (Array Nat)}
    (hs : ∀ j < steps.size, ∃ g : Equiv.Perm (Fin n), Rep n steps[j]! g) :
    levelTrOK n steps (CFSG.Monster.B.Co2.Native.bfs n root steps) = true := by
  unfold CFSG.Monster.B.Co2.Native.bfs
  simp only [Id.run_bind, Id.run_pure]
  refine levelTrOK_of_inv ?_ hs
  refine forIn_range_inv n _ _
    (fun st : Array Nat × Array Nat × Array Nat × Array Nat × Array (Array Nat) =>
      TrInv n steps st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2) ?_ ?_
  · refine ⟨rfl, rfl, rfl, by simp, rfl, fun k hk0 hk => ?_⟩
    simp at hk
    omega
  · intro a _ b hb
    split
    · rename_i hab
      simp only [Id.run_bind, Id.run_pure]
      refine (forIn_range_inv steps.size _ _
        (fun st : Array Nat × Array Nat × Array Nat × Array Nat × Array (Array Nat) =>
          TrInv n steps st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2 ∧ a < st.2.1.size)
        ⟨hb, hab⟩ ?_).1
      intro j hj c hc
      split
      · exact ⟨trInv_push hc.1 hc.2 hj, by simp; omega⟩
      · exact hc
    · exact hb

theorem rep_of_mem_levelSteps {n : Nat} {S Sinv : Array (Array Nat)} {base : Array Nat} {i : Nat}
    (h : ∀ j < S.size, isInvA n S[j]! Sinv[j]! = true) {t : Array Nat}
    (ht : t ∈ levelSteps S Sinv base i) : ∃ g : Equiv.Perm (Fin n), Rep n t g := by
  unfold levelSteps at ht
  rw [Array.mem_append, List.mem_toArray, List.mem_toArray, List.mem_map, List.mem_map] at ht
  rcases ht with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · have hj' : j < S.size := by
      unfold levelIdx at hj
      exact List.mem_range.1 (List.mem_filter.1 hj).1
    exact ⟨_, (rep_permOfArr (h j hj')).1⟩
  · have hj' : j < S.size := by
      unfold levelIdx at hj
      exact List.mem_range.1 (List.mem_filter.1 hj).1
    exact ⟨_, (rep_permOfArr (h j hj')).2⟩

theorem rawLevels_get {n : Nat} {S : Array (Array Nat)} {base : Array Nat} {i : Nat}
    (hi : i < base.size) :
    (rawLevels n S base)[i]! = CFSG.Monster.B.Co2.Native.bfs n base[i]! (rawSteps n S base i) := by
  unfold rawLevels
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

end CFSG.KS.Raw

end
