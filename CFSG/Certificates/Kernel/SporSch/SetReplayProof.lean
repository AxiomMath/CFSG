
module

public import CFSG.Certificates.Kernel.SporSch.SetReplaySound
public import CFSG.Certificates.Kernel.SporSch.HashSearch
public import CFSG.Certificates.Kernel.SporSch.SetTreeSound
public import CFSG.Certificates.Kernel.Spor.NKeyBfs
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KS.SporSch.SRP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.SporSch.KeySearch
open CFSG.KS.SporSch.SetTree CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native

@[expose] def StepB (key : Nat → Nat) (img pos : Nat → Nat → Nat) (P L : Nat → Nat)
    (c B h l cur v : Nat) : Prop :=
  (h < cur ∧ pos h l < cur ∧ v = cur ∧ img h l = key (pos h l)) ∨
    (h < cur ∧ pos h l = cur ∧ v = cur + 1 ∧ img h l = key cur ∧ P cur = h ∧ L cur = l) ∨
    (cur ≤ h ∧ cur = c ∧ v = cur) ∨ (B ≤ cur ∧ v = cur)

theorem runC_tree {f : Nat → Nat → Nat → Nat} {k c M H fl B : Nat} {C : Nat → Nat}
    {key : Nat → Nat} {img pos : Nat → Nat → Nat} {P L : Nat → Nat}
    (hc0 : 0 < c) (hcM : c ≤ M * H) (hfl : c < fl) (hC0 : C 0 = 1) (hCM : C M = c)
    (hrun : ∀ t < M, NKey.runC f k H (t * H) (C t) = C (t + 1))
    (hup : ∀ h l cur, l < k → fl ≤ cur → fl ≤ f h l cur)
    (hstep : ∀ h l cur, l < k → cur < fl → f h l cur < fl →
      StepB key img pos P L c B h l cur (f h l cur)) :
    (∀ i, 0 < i → i < c → P i < i ∧ L i < k ∧ img (P i) (L i) = key i) ∧
      (c < B → ∀ h < c, ∀ j < k, pos h j < c ∧ img h j = key (pos h j)) := by
  have hs0 : NKey.curE f k 1 0 = 1 := rfl
  have hsS : ∀ e, NKey.curE f k 1 (e + 1) = f (e / k) (e % k) (NKey.curE f k 1 e) :=
    NKey.curE_succ f k 1
  have hslice : ∀ t ≤ M, NKey.curE f k 1 (k * (t * H)) = C t := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [Nat.zero_mul, Nat.mul_zero, hC0]
      rfl
    | succ t ih =>
      intro ht
      rw [← hrun t (by omega), ← ih (by omega), NKey.runC_curE]
      congr 1
      rw [Nat.add_mul, Nat.one_mul]
  have hE : NKey.curE f k 1 (k * (M * H)) = c := by rw [hslice M (Nat.le_refl M), hCM]
  clear hslice hrun
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    rw [Nat.zero_mul] at hE
    have hc1 : c = 1 := by rw [← hE]; rfl
    subst hc1
    exact ⟨fun i hi0 hic => by omega, fun _ h hh j hj => by omega⟩
  have hEc : k * c ≤ k * (M * H) := Nat.mul_le_mul_left k hcM
  generalize k * (M * H) = E at hE hEc
  generalize NKey.curE f k 1 = s at hs0 hsS hE
  have hmod : ∀ e, e % k < k := fun e => Nat.mod_lt _ hk
  have hnf : ∀ e ≤ E, s e < fl := by
    intro e he
    refine Nat.lt_of_not_le fun hse => ?_
    have : ∀ d, e + d ≤ E → fl ≤ s (e + d) := by
      intro d
      induction d with
      | zero => intro _; exact hse
      | succ d ih =>
        intro hd
        rw [← Nat.add_assoc, hsS]
        exact hup _ _ _ (hmod _) (ih (by omega))
    have := this (E - e) (by omega)
    rw [Nat.add_sub_cancel' he, hE] at this
    omega
  have hok : ∀ e < E, StepB key img pos P L c B (e / k) (e % k) (s e) (s (e + 1)) := by
    intro e he
    rw [hsS]
    exact hstep _ _ _ (hmod e) (hnf e (by omega)) (by rw [← hsS]; exact hnf (e + 1) (by omega))
  have hstep1 : ∀ e < E, s e ≤ s (e + 1) ∧ s (e + 1) ≤ s e + 1 := by
    intro e he
    rcases hok e he with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, -, h3⟩ | ⟨-, h3⟩ <;> rw [h3] <;> omega
  have hmono : ∀ e e', e ≤ e' → e' ≤ E → s e ≤ s e' := fun e e' h h' =>
    NKey.mono_le (fun e he => (hstep1 e he).1) h h'
  have hle : ∀ e ≤ E, s e ≤ c := fun e he => hE ▸ hmono e E he (Nat.le_refl E)
  refine ⟨fun i hi0 hic => ?_, fun hcB h hh j hj => ?_⟩
  · obtain ⟨e, he, h1, h2⟩ := NKey.ivt (s := s) (i := i) E hstep1 (by rw [hs0]; omega)
      (by rw [hE]; exact hic)
    rcases hok e he with ⟨-, -, h3, -⟩ | ⟨hh, -, -, a4, a5, a6⟩ | ⟨-, -, h3⟩ | ⟨-, h3⟩
    · omega
    · rw [h1] at hh a4 a5 a6
      rw [a5, a6]
      exact ⟨hh, hmod e, a4⟩
    · omega
    · omega
  · have hd := NKey.divmod_eq h hj
    have he : k * h + j < E := by
      have : k * (h + 1) ≤ k * c := Nat.mul_le_mul_left k hh
      rw [Nat.mul_succ] at this
      omega
    have hsc := hle (k * h + j) (Nat.le_of_lt he)
    have hsc1 := hle (k * h + j + 1) he
    have hO := hok _ he
    rw [hd.1, hd.2] at hO
    rcases hO with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4, -⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2⟩
    · exact ⟨by omega, a4⟩
    · exact ⟨by omega, by rw [a2]; exact a4⟩
    · omega
    · omega

@[expose] noncomputable def posR (W : Nat → Nat) (h l : Nat) : Nat :=
  fld(W h, Nat.mul (nat_lit 20) l, nat_lit 1048575)

theorem nIf_v (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem bAnd_v (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem stepR_eq (w s : Nat) (G X W : Nat → Nat) (c bound h l cur : Nat) :
    stepR w s G X W c bound h l cur =
      if cur = bound then cur else if h < cur then
        (if posR W h l < cur ∧ keyK w s (X (posR W h l)) = imgK w s (G l) (X h) then cur
        else if posR W h l = cur ∧ keyK w s (X (posR W h l)) = imgK w s (G l) (X h) ∧
          parX w s (X (posR W h l)) = h ∧ labX w s (X (posR W h l)) = l then cur + 1 else failC)
      else if cur = c then cur else failC := by
  unfold stepR posR
  simp only [strictN_eq', nIf_v, bAnd_v, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq]

theorem stepR_up {w s c bound h l cur : Nat} {G X W : Nat → Nat} (hc : failC ≤ cur) :
    failC ≤ stepR w s G X W c bound h l cur := by
  rw [stepR_eq]
  split_ifs <;> omega

theorem stepR_step {w s c bound h l cur : Nat} {G X W : Nat → Nat}
    (hf : stepR w s G X W c bound h l cur < failC) :
    StepB (fun j => keyK w s (X j)) (fun h l => imgK w s (G l) (X h)) (posR W)
      (fun j => parX w s (X j)) (fun j => labX w s (X j)) c bound h l cur
      (stepR w s G X W c bound h l cur) := by
  generalize hv : stepR w s G X W c bound h l cur = v at hf ⊢
  rw [stepR_eq] at hv
  unfold StepB
  split_ifs at hv with h1 h2 h3 h4 h5
  · exact Or.inr (Or.inr (Or.inr ⟨by omega, hv.symm⟩))
  · exact Or.inl ⟨h2, h3.1, hv.symm, h3.2.symm⟩
  · obtain ⟨a, b, c', d⟩ := h4
    refine Or.inr (Or.inl ⟨h2, a, hv.symm, ?_, ?_, ?_⟩)
    · rw [← a]
      exact b.symm
    · rw [← a]
      exact c'
    · rw [← a]
      exact d
  · omega
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, h5, hv.symm⟩))
  · omega

theorem saltOf_lt (x : Nat) : saltOf x < 2 ^ 64 := by
  unfold saltOf
  change x &&& 18446744073709551615 < 2 ^ 64
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem keyK_bit (w s x b : Nat) :
    (keyK w s x).testBit (64 + b) = decide (b ∈ ptsOf w s x) := by
  unfold keyK
  simp only [strictN_eq', CFSG.KC.Pack.foldN_eq]
  rw [testBit_foldr, tag_bit (saltOf_lt _), Bool.false_or]
  rfl

theorem imgK_bit (w s G x b : Nat) :
    (imgK w s G x).testBit (64 + b) = decide (b ∈ (ptsOf w s x).map (pg w (mask w) G)) := by
  unfold imgK
  simp only [strictN_eq', CFSG.KC.Pack.foldN_eq]
  rw [testBit_foldr (fun q => pg w (mask w) G (pg w (mask w) x q)), tag_bit (saltOf_lt _),
    Bool.false_or]
  unfold ptsOf
  rw [List.map_map]
  rfl

theorem foldr_congr2 {f g : Nat → Nat → Nat} :
    ∀ (l : List Nat) {a b : Nat}, (∀ q ∈ l, ∀ acc, f q acc = g q acc) → a = b →
      l.foldr f a = l.foldr g b
  | [], _, _, _, e => e
  | q :: l, a, b, h, e => by
    rw [List.foldr_cons, List.foldr_cons,
      foldr_congr2 l (fun r hr => h r (List.mem_cons_of_mem q hr)) e, h q List.mem_cons_self]

theorem keyK_congr {w s x y : Nat} (h : ptsOf w s x = ptsOf w s y) : keyK w s x = keyK w s y := by
  have hq : ∀ q < s, pg w (mask w) x q = pg w (mask w) y q := by
    intro q hq
    have := congrArg (fun l => l[q]?) h
    simpa [ptsOf, hq] using this
  unfold keyK
  simp only [strictN_eq', CFSG.KC.Pack.foldN_eq]
  refine foldr_congr2 _ (fun q hq' acc => ?_) ?_
  · rw [hq q (List.mem_range.1 hq')]
  · refine congrArg saltOf (foldr_congr2 _ (fun q hq' acc => ?_) rfl)
    rw [hq q (List.mem_range.1 hq')]

theorem permA_of_permOK {n w P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) :
    PermA n (unpack n w P) := by
  obtain ⟨-, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  refine ⟨fun x hx => ?_, fun x hx y hy e => ?_⟩
  · rw [CFSG.KC.Misc.PairCount.unpack_get hx]
    exact (h3 x hx).1
  · rw [CFSG.KC.Misc.PairCount.unpack_get hx, CFSG.KC.Misc.PairCount.unpack_get hy] at e
    rw [← (h3 x hx).2, ← (h3 y hy).2, e]

theorem pts_of_key {n w s kg : Nat} {G : Nat → Nat} {gens : Array (Array Nat)}
    (hg : ∀ k < kg, gens[k]! = unpack n w (G k)) (hperm : ∀ k < kg, PermA n gens[k]!) {k x y : Nat}
    (hk : k < kg) (hx : Good n (ptsOf w s x)) (hy : Good n (ptsOf w s y))
    (he : imgK w s (G k) y = keyK w s x) :
    ptsOf w s x = imgSorted gens[k]! (ptsOf w s y) := by
  refine eq_of_mem_iff hx (imgSorted_good (hperm k hk) hy) fun q => ?_
  have hb := keyK_bit w s x q
  rw [← he, imgK_bit] at hb
  have e1 : q ∈ ptsOf w s x ↔ q ∈ (ptsOf w s y).map (pg w (mask w) (G k)) :=
    (decide_eq_decide.1 hb).symm
  rw [e1]
  have hmap : (ptsOf w s y).map (pg w (mask w) (G k)) = (ptsOf w s y).map fun r => (gens[k]!)[r]! :=
    List.map_congr_left fun r hr => by
      rw [hg k hk, CFSG.KC.Misc.PairCount.unpack_get (hy.2 r hr)]
  rw [hmap, imgSorted, (List.mergeSort_perm _ _).mem_iff]

theorem eltAt_spec {n w s c i : Nat} {X : Nat → Nat} (hi : i < c)
    (h : eltAt n w s X c i = true) : eltK n w s (X i) = true := by
  unfold eltAt at h
  have hb : Nat.blt i c = true := Nat.blt_eq.mpr hi
  rw [hb] at h
  change strictB (X i) _ = true at h
  rwa [strictB_eq'] at h

theorem sortAt_spec {w s c i : Nat} {X SO SOI : Nat → Nat} (hi : i < c)
    (h : sortAt w s X SO SOI c i = true) :
    SO i < c ∧ (i + 1 < c → keyK w s (X (SO i)) < keyK w s (X (SO (i + 1)))) := by
  unfold sortAt at h
  have hb : Nat.blt i c = true := Nat.blt_eq.mpr hi
  rw [hb] at h
  change sortK w s X SO SOI c i = true at h
  unfold sortK at h
  rw [strictB_eq'] at h
  obtain ⟨a, b⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, b⟩ := (bAnd_iff _ _).1 b
  refine ⟨by rwa [Nat.blt_eq] at a, fun hi1 => ?_⟩
  have hb1 : Nat.blt (Nat.succ i) c = true := by rwa [Nat.blt_eq]
  rw [hb1] at b
  change Nat.blt _ _ = true at b
  rwa [Nat.blt_eq] at b

theorem replay_facts {n w s kg c bound nS H nB B R : Nat} {G GI X W SO SOI C : Nat → Nat}
    {start : List Nat} {gens : Array (Array Nat)}
    (hg : gens.size = kg ∧ ∀ k < kg, gens[k]! = unpack n w (G k))
    (h : SetReplayOK n w s kg c bound nS H nB B R G GI X W SO SOI C start) :
    0 < c ∧ c ≤ bound ∧ (∀ k < gens.size, PermA n gens[k]!) ∧
      (∀ i < c, Good n (ptsOf w s (X i))) ∧ ptsOf w s (X 0) = start ∧
      (∀ i, 0 < i → i < c → parX w s (X i) < i ∧ labX w s (X i) < gens.size ∧
        ptsOf w s (X i) = imgSorted gens[labX w s (X i)]! (ptsOf w s (X (parX w s (X i))))) ∧
      (∀ a < c, ∀ b < c, ptsOf w s (X a) = ptsOf w s (X b) → a = b) ∧
      (c < bound → ∀ i < c, ∀ k < gens.size, ∃ j < c,
        imgSorted gens[k]! (ptsOf w s (X i)) = ptsOf w s (X j)) := by
  obtain ⟨hgs, hgu⟩ := hg
  obtain ⟨-, -, -, hc0, hcb, hcS, hcB, hc20, -, hperm, hst, helt, hsrt, hC0, hCM, hrun⟩ := h
  have hpA : ∀ k < kg, PermA n gens[k]! := fun k hk => by
    rw [hgu k hk]
    exact permA_of_permOK (hperm k hk)
  have hgood : ∀ i < c, Good n (ptsOf w s (X i)) := fun i hi =>
    eltK_good (eltAt_spec hi (NKey.all_of_blocks hcB helt i hi))
  have hrun' : ∀ t < nS * R, NKey.runC (fun h l cur => stepR w s G X W c bound h l cur) kg H
      (t * H) (C t) = C (t + 1) := fun t ht => NKey.slices_of_groups hrun t ht
  have hfl : c < failC := by
    have e : failC = 1099511627776 := rfl
    rw [e]
    omega
  obtain ⟨htree, hclose⟩ := runC_tree (B := bound) hc0 hcS hfl hC0 hCM hrun'
    (fun h l cur _ hc => stepR_up hc) (fun h l cur _ _ hf => stepR_step hf)
  have hsrt' := fun i hi => sortAt_spec hi (NKey.all_of_blocks hcB hsrt i hi)
  have hinjK := CFSG.KC.Co2InvS.sorted_inj (f := fun i => keyK w s (X i))
    (fun i hi => (hsrt' i hi).1) (fun i hi => (hsrt' i (by omega)).2 hi)
  refine ⟨hc0, hcb, fun k hk => hpA k (hgs ▸ hk), hgood, startK_spec hst, fun i hi0 hic => ?_,
    fun a ha b hb e => hinjK a ha b hb (keyK_congr e), fun hcb' i hi k hk => ?_⟩
  · obtain ⟨a1, a2, a3⟩ := htree i hi0 hic
    exact ⟨a1, hgs ▸ a2, pts_of_key hgu hpA a2 (hgood i hic) (hgood _ (by omega)) a3⟩
  · rw [hgs] at hk
    obtain ⟨a1, a2⟩ := hclose hcb' i hi k hk
    exact ⟨_, a1, (pts_of_key hgu hpA hk (hgood _ a1) (hgood i hi) a2).symm⟩

theorem assemble {n : Nat} {gens : Array (Array Nat)} {start : List Nat} {bound c : Nat}
    {S : Array (List Nat)} {PA LA : Array Nat} {hd : Nat} {T : Nat → List Nat} {P L : Nat → Nat}
    (h0 : 0 < S.size) (hbd : S.size ≤ bound)
    (hz : S[0]! = start)
    (hrec : ∀ k, 0 < k → k < S.size →
      PA[k]! < k ∧ LA[k]! < gens.size ∧ S[k]! = imgSorted gens[LA[k]!]! S[PA[k]!]!)
    (hgood : ∀ i < S.size, Good n S[i]!)
    (hdist : ∀ i < S.size, ∀ j < S.size, S[i]! = S[j]! → i = j)
    (hle : hd ≤ S.size) (hor : S.size = bound ∨ hd = bound ∨ hd = S.size)
    (hcl : S.size < bound → ∀ i < hd, ∀ k < gens.size,
      ∃ i' < S.size, S[i']! = imgSorted gens[k]! S[i]!)
    (hc0 : 0 < c) (hcb : c ≤ bound) (hT0 : T 0 = start)
    (htree : ∀ i, 0 < i → i < c → P i < i ∧ L i < gens.size ∧ T i = imgSorted gens[L i]! (T (P i)))
    (hinj : ∀ a < c, ∀ b < c, T a = T b → a = b)
    (hclose : c < bound → ∀ h < c, ∀ k < gens.size, ∃ j < c, imgSorted gens[k]! (T h) = T j) :
    translatesOK gens start S PA LA = true ∧ keysSortedOK S = true ∧ S.size = c := by
  have hget : ∀ i (hi : i < S.toList.length), S.toList[i] = S[i]! := fun i hi => by
    rw [Array.getElem_toList, getElem!_pos S i (by simpa using hi)]
  have hnd : S.toList.Nodup := by
    refine List.pairwise_iff_getElem.2 fun i j hi hj hij e => ?_
    rw [hget i hi, hget j hj] at e
    have := hdist i (by simpa using hi) j (by simpa using hj) e
    omega
  have hmem : ∀ x ∈ S.toList, ∃ i < S.size, S[i]! = x := fun x hx => by
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hx
    exact ⟨i, by simpa using hi, by rw [← hget i hi, e]⟩
  have hmemS : ∀ i < S.size, S[i]! ∈ S.toList := fun i hi => by
    rw [← hget i (by simpa using hi)]
    exact List.getElem_mem _
  have hcard : S.toList.toFinset.card = S.size := by
    rw [List.toFinset_card_of_nodup hnd, Array.length_toList]
  refine ⟨?_, ?_, ?_⟩
  · unfold translatesOK
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨h0, hz⟩, allLt_true fun k hk => ?_⟩
    rcases Nat.eq_zero_or_pos k with e | e
    · simp [e]
    · obtain ⟨a, b, c'⟩ := hrec k e hk
      simp [a, b, c']
  · unfold keysSortedOK sortedKeys
    apply strictlyIncreasing_of
    have hle' := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (S.toList.map setKey)
    have hnd' : (S.toList.map setKey).Nodup := by
      refine List.Nodup.map_on (fun x hx y hy e => ?_) hnd
      obtain ⟨i, hi, rfl⟩ := hmem x hx
      obtain ⟨j, hj, rfl⟩ := hmem y hy
      exact eq_of_setKey (hgood i hi) (hgood j hj) e
    have hp := List.mergeSort_perm (S.toList.map setKey) (fun a b : Nat => decide (a ≤ b))
    exact (hle'.and (hp.nodup_iff.2 hnd')).imp fun ⟨h1, h2⟩ => lt_of_le_of_ne (by simpa using h1) h2
  ·
    have hlow : ∀ F : Finset (List Nat), start ∈ F →
        (∀ t ∈ F, ∀ k < gens.size, imgSorted gens[k]! t ∈ F) → c ≤ F.card := by
      intro F h0F hF
      have hTF : ∀ i < c, T i ∈ F := by
        intro i
        induction i using Nat.strong_induction_on with
        | _ i ih =>
          intro hi
          rcases Nat.eq_zero_or_pos i with rfl | hi0
          · rw [hT0]
            exact h0F
          · obtain ⟨a, b, e⟩ := htree i hi0 hi
            rw [e]
            exact hF _ (ih _ a (by omega)) _ b
      have := Finset.card_le_card_of_injOn (s := Finset.range c) (t := F) T
        (fun i hi => hTF i (Finset.mem_range.1 hi))
        (fun a ha b hb e => hinj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) e)
      rwa [Finset.card_range] at this
    have hup : c < bound → S.size ≤ c := by
      intro hcb'
      have hin : ∀ i < S.size, ∃ j < c, S[i]! = T j := by
        intro i
        induction i using Nat.strong_induction_on with
        | _ i ih =>
          intro hi
          rcases Nat.eq_zero_or_pos i with rfl | hi0
          · exact ⟨0, hc0, by rw [hz, hT0]⟩
          · obtain ⟨a, b, e⟩ := hrec i hi0 hi
            obtain ⟨j, hj, ej⟩ := ih _ a (by omega)
            obtain ⟨j', hj', ej'⟩ := hclose hcb' j hj _ b
            exact ⟨j', hj', by rw [e, ej, ej']⟩
      have hsub : S.toList.toFinset ⊆ (Finset.range c).image T := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := hmem x (List.mem_toFinset.1 hx)
        obtain ⟨j, hj, e⟩ := hin i hi
        exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, e.symm⟩
      have := (Finset.card_le_card hsub).trans Finset.card_image_le
      rwa [hcard, Finset.card_range] at this
    by_cases hlt : S.size < bound
    · have hhd : hd = S.size := by rcases hor with e | e | e <;> omega
      have hge : c ≤ S.size := by
        rw [← hcard]
        refine hlow _ (by rw [List.mem_toFinset, ← hz]; exact hmemS 0 h0) fun x hx k hk => ?_
        obtain ⟨i, hi, rfl⟩ := hmem x (List.mem_toFinset.1 hx)
        obtain ⟨i', hi', e⟩ := hcl hlt i (by omega) k hk
        rw [List.mem_toFinset, ← e]
        exact hmemS i' hi'
      rcases Nat.lt_or_ge c bound with h1 | h1
      · have := hup h1
        omega
      · omega
    · rcases Nat.lt_or_ge c bound with h1 | h1
      · have := hup h1
        omega
      · omega

theorem setReplay_proved {n w s kg c bound nS H nB B R : Nat} {G GI X W SO SOI C : Nat → Nat}
    {start : List Nat} {gens : Array (Array Nat)}
    (hg : gens.size = kg ∧ ∀ k < kg, gens[k]! = unpack n w (G k))
    (h : SetReplayOK n w s kg c bound nS H nB B R G GI X W SO SOI C start) :
    translatesOK gens start (hashSearch gens start bound).1 (hashSearch gens start bound).2.1
        (hashSearch gens start bound).2.2 = true ∧
      keysSortedOK (hashSearch gens start bound).1 = true ∧
      (hashSearch gens start bound).1.size = c := by
  obtain ⟨hc0, hcb, hpA, hgood, hT0, htree, hinj, hclose⟩ := replay_facts hg h
  have hs : Good n start := hT0 ▸ hgood 0 hc0
  rw [HashSearch.search_eq]
  obtain ⟨hI, hle, hor, hcl⟩ := HashSearch.outer_spec (bound := bound) (by omega) hpA hs
  generalize Id.run (forIn (List.range' 0 bound) (HashSearch.oinit start)
    (HashSearch.outerBody gens bound)) = st at hI hle hor hcl ⊢
  obtain ⟨-, -, h0, hbd, hz, hrec, -, hgd, hdist⟩ := hI
  exact assemble h0 hbd hz hrec hgd hdist hle hor hcl hc0 hcb hT0 htree hinj hclose

theorem setReplay_key_proved {n w s kg c bound nS H nB B R : Nat} {G GI X W SO SOI C : Nat → Nat}
    {start : List Nat} {gens : Array (Array Nat)}
    (hg : gens.size = kg ∧ ∀ k < kg, gens[k]! = unpack n w (G k))
    (h : SetReplayOK n w s kg c bound nS H nB B R G GI X W SO SOI C start) :
    translatesOK gens start (co3KeySearch gens start bound).1 (co3KeySearch gens start bound).2.1
        (co3KeySearch gens start bound).2.2 = true ∧
      keysSortedOK (co3KeySearch gens start bound).1 = true ∧
      (co3KeySearch gens start bound).1.size = c := by
  obtain ⟨hc0, hcb, hpA, hgood, hT0, htree, hinj, hclose⟩ := replay_facts hg h
  have hs : Good n start := hT0 ▸ hgood 0 hc0
  rw [KeySearch.search_eq]
  obtain ⟨hI, hle, hor, hcl⟩ := KeySearch.outer_spec (bound := bound) (by omega) hpA hs
  generalize Id.run (forIn (List.range' 0 bound) (KeySearch.oinit start)
    (KeySearch.outerBody gens bound)) = st at hI hle hor hcl ⊢
  obtain ⟨-, -, h0, hbd, hz, hrec, -, hgd, hdist⟩ := hI
  exact assemble h0 hbd hz hrec hgd hdist hle hor hcl hc0 hcb hT0 htree hinj hclose

end CFSG.KS.SporSch.SRP

end
