module

public import Certificates.Data.Kernel.EvenSporSuz.SylowTree
public import CFSG.Certificates.Kernel.EvenSporSuz.SylowSound
public import CFSG.Certificates.Kernel.EvenSporSuz.Sound

public section

namespace CFSG.KC.EvenSporSuz.Syl

open CFSG.KC.ONanSmall CFSG.KC.M24G CFSG.KC.Misc.G24

theorem letN_eq {α : Sort _} (y : Nat) (k : Nat → α) : letN y k = k y := by
  cases y <;> rfl

theorem idxL_cons {α : Type} (f : α → Nat) (a : α) (L : List α) (i : Nat) :
    idxL f (a :: L) i = (i, f a) :: idxL f L (i + 1) :=
  letN_eq i (fun j => (j, f a) :: idxL f L (Nat.succ j))

theorem mem_idxL {α : Type} (f : α → Nat) :
    ∀ (L : List α) (i k v : Nat), (k, v) ∈ idxL f L i → ∃ t, ∃ h : t < L.length, k = i + t ∧ v = f L[t]
  | [], _, _, _, h => by simp [idxL] at h
  | a :: L, i, k, v, h => by
    rw [idxL_cons, List.mem_cons] at h
    rcases h with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨0, by simp, by simp, rfl⟩
    · obtain ⟨t, ht, rfl, rfl⟩ := mem_idxL f L (i + 1) k v h
      exact ⟨t + 1, by simp [ht], by omega, rfl⟩

theorem findK_idxL {α : Type} {f : α → Nat} {L : List α} {k v : Nat}
    (h : findK k (treeOf (idxL f L 0)) = some v) : ∃ h : k < L.length, v = f L[k] := by
  obtain ⟨t, ht, hk, hv⟩ := mem_idxL f L 0 k v (findK_treeOf h)
  have e : k = t := by omega
  subst e
  exact ⟨ht, hv⟩

theorem elemT_sound {QT ET : KTree (Nat × Nat)} {G : List Nat} {j q : Nat} {e : Nat × Nat}
    (h : elemT QT ET G j q e = true) : ∃ b, findK q ET = some b ∧ (j = 0 → b = one3) ∧
      (j ≠ 0 → e.1 < j ∧ e.2 < 4 ∧ ∃ qp a, findK e.1 QT = some qp ∧ findK qp ET = some a ∧
        b = mulF3 a (G.getD e.2 0)) := by
  unfold elemT at h
  rcases hq : findK q ET with _ | b
  · rw [hq] at h
    cases h
  rw [hq] at h
  refine ⟨b, rfl, ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h0 : Nat.beq b one3 = true := h
    exact ⟨fun _ => Nat.eq_of_beq_eq_true h0, fun h0 => absurd rfl h0⟩
  have hb : Nat.beq j 0 = false :=
    Bool.eq_false_iff.2 fun h0 => absurd (Nat.eq_of_beq_eq_true h0) (by omega)
  rw [hb] at h
  have h' : (Nat.blt e.1 j && Nat.blt e.2 4 &&
      Option.rec (motive := fun _ => Bool) false (fun qp =>
        Option.rec (motive := fun _ => Bool) false (fun a => Nat.beq b (mulF3 a (G.getD e.2 0)))
          (findK qp ET)) (findK e.1 QT)) = true := h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h'
  obtain ⟨⟨h1, h2⟩, h3⟩ := h'
  refine ⟨fun h0 => by omega, fun _ => ⟨h1, h2, ?_⟩⟩
  rcases hp : findK e.1 QT with _ | qp
  · rw [hp] at h3
    cases h3
  rw [hp] at h3
  have h4 : Option.rec (motive := fun _ => Bool) false
      (fun a => Nat.beq b (mulF3 a (G.getD e.2 0))) (findK qp ET) = true := h3
  rcases ha : findK qp ET with _ | a
  · rw [ha] at h4
    cases h4
  rw [ha] at h4
  have h5 : Nat.beq b (mulF3 a (G.getD e.2 0)) = true := h4
  exact ⟨qp, a, rfl, ha, Nat.eq_of_beq_eq_true h5⟩

theorem treeGo_sound {QT ET : KTree (Nat × Nat)} {G : List Nat} :
    ∀ (P : List Nat) (T : List (Nat × Nat)) (i : Nat), treeGo QT ET G P T i = true →
      P.length ≤ T.length ∧ ∀ t (hP : t < P.length) (hT : t < T.length),
        elemT QT ET G (i + t) P[t] T[t] = true
  | [], _, _, _ => ⟨by simp, fun t hP => absurd hP (by simp)⟩
  | q :: P, [], i, h => by cases h
  | q :: P, e :: T, i, h => by
    have he : treeGo QT ET G (q :: P) (e :: T) i =
        (elemT QT ET G i q e && treeGo QT ET G P T (i + 1)) :=
      letN_eq i (fun j => elemT QT ET G j q e && treeGo QT ET G P T (Nat.succ j))
    rw [he, Bool.and_eq_true] at h
    obtain ⟨hl, ht⟩ := treeGo_sound P T (i + 1) h.2
    refine ⟨by simp [hl], fun t hP hT => ?_⟩
    rcases t with _ | t
    · simpa using h.1
    · have := ht t (by simpa using hP) (by simpa using hT)
      have e : i + 1 + t = i + (t + 1) := by omega
      rw [e] at this
      simpa using this

theorem posGo_sound {QT : KTree (Nat × Nat)} :
    ∀ (V : List Nat) (j : Nat), posGo QT V j = true →
      ∀ t (hV : t < V.length), findK V[t] QT = some (j + t)
  | [], _, _, t, hV => absurd hV (by simp)
  | p :: V, j, h, t, hV => by
    have he : posGo QT (p :: V) j =
        (Option.rec (motive := fun _ => Bool) false (fun v => Nat.beq v j) (findK p QT) &&
          posGo QT V (j + 1)) :=
      letN_eq j (fun j' => Option.rec (motive := fun _ => Bool) false (fun v => Nat.beq v j')
        (findK p QT) && posGo QT V (Nat.succ j'))
    rw [he, Bool.and_eq_true] at h
    rcases t with _ | t
    · rcases hp : findK p QT with _ | v
      · rw [hp] at h
        cases h.1
      · rw [hp] at h
        simp only [List.getElem_cons_zero, hp, Nat.add_zero]
        exact congrArg some (Nat.eq_of_beq_eq_true h.1)
    · have := posGo_sound V (j + 1) h.2 t (by simpa using hV)
      have e : j + 1 + t = j + (t + 1) := by omega
      rw [e] at this
      simpa using this

theorem slice_length {α : Type} {L : List α} {c : Nat} (h : 4096 * (c + 1) ≤ L.length) :
    (slice4 L c).length = 4096 := by
  simp only [slice4, List.length_take, List.length_drop]
  omega

theorem slice_getElem {α : Type} {L : List α} {c t : Nat} (h : t < (slice4 L c).length) :
    (slice4 L c)[t] = L[4096 * c + t]'(by simp [slice4] at h; omega) := by
  simp [slice4]

theorem tree_sound {ED : List (Nat × Nat)} {G PS IV : List Nat} {TP : List (Nat × Nat)}
    (hc : ∀ c < 4, treeChunkK (treeOf (idxL id PS 0)) (treeOf (idxL Prod.fst ED 0)) G PS TP IV c =
      true)
    (hP : PS.length = 16384) (hI : IV.length = 16384) (hT : TP.length = 16383) :
    (∃ h : PS.getD 0 0 < ED.length, (ED[PS.getD 0 0]).1 = one3) ∧
      (∀ i < 16384, i ≠ 0 → (TP.getD (i - 1) (0, 0)).1 < i ∧ (TP.getD (i - 1) (0, 0)).2 < 4 ∧
        ∃ (h : PS.getD i 0 < ED.length) (h' : PS.getD (TP.getD (i - 1) (0, 0)).1 0 < ED.length),
          (ED[PS.getD i 0]).1 = mulF3 (ED[PS.getD (TP.getD (i - 1) (0, 0)).1 0]).1
            (G.getD (TP.getD (i - 1) (0, 0)).2 0)) ∧
      (∀ j < 16384, ∃ h : IV.getD j 0 < 16384, PS.getD (IV.getD j 0) 0 = j) := by
  have hPT : ((0, 0) :: TP).length = 16384 := by simp [hT]
  have hel : ∀ i < 16384, elemT (treeOf (idxL id PS 0)) (treeOf (idxL Prod.fst ED 0)) G i
      (PS.getD i 0) (((0, 0) :: TP).getD i (0, 0)) = true := by
    intro i hi
    have hc' := hc (i / 4096) (by omega)
    simp only [treeChunkK, Bool.and_eq_true] at hc'
    have hs1 : (slice4 PS (i / 4096)).length = 4096 := slice_length (by omega)
    have hs2 : (slice4 ((0, 0) :: TP) (i / 4096)).length = 4096 := slice_length (by omega)
    have := (treeGo_sound _ _ _ hc'.1).2 (i % 4096) (by omega) (by omega)
    rw [slice_getElem, slice_getElem] at this
    have e : 4096 * (i / 4096) + i % 4096 = i := Nat.div_add_mod i 4096
    simp only [e] at this
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    exact this
  have look : ∀ {q b : Nat}, findK q (treeOf (idxL Prod.fst ED 0)) = some b →
      ∃ h : q < ED.length, b = (ED[q]).1 := fun h => findK_idxL h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨b, hb, h0, -⟩ := elemT_sound (hel 0 (by norm_num))
    obtain ⟨hq, rfl⟩ := look hb
    exact ⟨hq, (h0 rfl)⟩
  · intro i hi hi0
    obtain ⟨b, hb, -, h1⟩ := elemT_sound (hel i hi)
    have hg : ((0, 0) :: TP).getD i (0, 0) = TP.getD (i - 1) (0, 0) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      simp
    rw [hg] at h1
    obtain ⟨hp, hg4, qp, a, hqp, ha, hbe⟩ := h1 hi0
    obtain ⟨hq, rfl⟩ := look hb
    obtain ⟨hqp', rfl⟩ := findK_idxL hqp
    obtain ⟨ha', rfl⟩ := look ha
    refine ⟨hp, hg4, hq, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ hqp']
      exact ha'
    · rw [hbe]
      simp only [id, List.getD_eq_getElem _ _ hqp']
  · intro j hj
    have hc' := hc (j / 4096) (by omega)
    simp only [treeChunkK, Bool.and_eq_true] at hc'
    have hs : (slice4 IV (j / 4096)).length = 4096 := slice_length (by omega)
    have := posGo_sound _ _ hc'.2 (j % 4096) (by omega)
    rw [slice_getElem] at this
    have e : 4096 * (j / 4096) + j % 4096 = j := Nat.div_add_mod j 4096
    simp only [e] at this
    obtain ⟨hk, hv⟩ := findK_idxL this
    rw [List.getD_eq_getElem _ _ (by omega)]
    refine ⟨by omega, ?_⟩
    rw [List.getD_eq_getElem _ _ hk]
    exact hv.symm

theorem nilK_eq {β : Type} : ∀ {L : List β}, nilK L = true → L = []
  | [], _ => rfl
  | _ :: _, h => by cases h

theorem toNat?_nil : (String.ofList []).toNat? = none :=
  String.toNat?_eq_none (Bool.eq_false_iff.2 fun h => (String.isNat_iff.1 h).1 String.ofList_nil)

def flatP (TP : List (Nat × Nat)) : List Nat := TP.flatMap fun e => [e.1, e.2]

theorem filterMap_of_bindTP : ∀ (TP : List (Nat × Nat)) (toks : List (List Char)),
    bindTP TP toks = true → toks.filterMap (fun p => (String.ofList p).toNat?) = flatP TP
  | [], toks, h => by
    rcases toks with _ | ⟨t, r⟩
    · cases h
    · have h' : (nilK t && nilK r) = true := h
      rw [Bool.and_eq_true] at h'
      rw [nilK_eq h'.1, nilK_eq h'.2, List.filterMap_cons, toNat?_nil]
      rfl
  | e :: TP, toks, h => by
    rcases toks with _ | ⟨t1, _ | ⟨t2, r⟩⟩
    · cases h
    · cases h
    · have h' : (digitsK t1 && digitsK t2 && Nat.beq (CFSG.KC.Str.decVal t1) e.1 &&
          Nat.beq (CFSG.KC.Str.decVal t2) e.2 && bindTP TP r) = true := h
      simp only [Bool.and_eq_true, Nat.beq_eq] at h'
      obtain ⟨⟨⟨⟨d1, d2⟩, e1⟩, e2⟩, hr⟩ := h'
      rw [List.filterMap_cons, toNat?_ofList d1, List.filterMap_cons, toNat?_ofList d2,
        filterMap_of_bindTP TP r hr, e1, e2]
      rfl

theorem parseNats_of_bindTP {TP : List (Nat × Nat)} {L : List Char}
    (h : bindTP TP (L.splitOn ' ') = true) :
    CFSG.EvenSporadicStandard.TwoSuz.parseNats (String.ofList L) = flatP TP := by
  unfold CFSG.EvenSporadicStandard.TwoSuz.parseNats
  rw [space_eq, CFSG.KC.Str.splitOn_ofList, List.filterMap_map]
  exact filterMap_of_bindTP TP _ h

theorem flatP_length (TP : List (Nat × Nat)) : (flatP TP).length = 2 * TP.length := by
  induction TP with
  | nil => rfl
  | cons e TP ih => simp [flatP] at ih ⊢; omega

theorem flatP_getD : ∀ (TP : List (Nat × Nat)) (i : Nat),
    (flatP TP).getD (2 * i) 0 = (TP.getD i (0, 0)).1 ∧
      (flatP TP).getD (2 * i + 1) 0 = (TP.getD i (0, 0)).2
  | [], i => by simp [flatP]
  | e :: TP, 0 => by simp [flatP]
  | e :: TP, i + 1 => by
    have := flatP_getD TP i
    have h1 : 2 * (i + 1) = 2 * i + 2 := by ring
    have h2 : 2 * (i + 1) + 1 = 2 * i + 1 + 2 := by ring
    simp only [flatP, List.flatMap_cons, h1, h2] at this ⊢
    simpa using this

open CFSG.EvenSporadicStandard.TwoSuz

def bStep (gens : Array Mt) (par : Array (ℕ × ℕ)) (E : Array Mt) (i : ℕ) : Array Mt :=
  E.push (mulM (E.getD (par.getD i (0, 0)).1 oneM) (gens.getD (par.getD i (0, 0)).2 oneM))

def bPre (gens : Array Mt) (par : Array (ℕ × ℕ)) (m : ℕ) : Array Mt :=
  (List.range' 1 m).foldl (bStep gens par) #[oneM]

theorem buildE_eq (gens : Array Mt) (par : Array (ℕ × ℕ)) :
    buildE gens par = bPre gens par (par.size - 1) := by
  unfold buildE bPre
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.div_one, List.forIn_pure_yield_eq_foldl]
  congr 1

theorem bPre_succ (gens : Array Mt) (par : Array (ℕ × ℕ)) (m : ℕ) :
    bPre gens par (m + 1) = bStep gens par (bPre gens par m) (m + 1) := by
  unfold bPre
  rw [List.range'_concat, List.foldl_append]
  simp [Nat.add_comm]

theorem bPre_size (gens : Array Mt) (par : Array (ℕ × ℕ)) : ∀ m, (bPre gens par m).size = m + 1
  | 0 => rfl
  | m + 1 => by rw [bPre_succ, bStep, Array.size_push, bPre_size gens par m]

theorem getD_push_lt {a : Array Mt} {x : Mt} {i : ℕ} (h : i < a.size) :
    (a.push x).getD i oneM = a.getD i oneM := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt h, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem h]

theorem getD_push_size {a : Array Mt} {x : Mt} {i : ℕ} (h : i = a.size) :
    (a.push x).getD i oneM = x := by
  subst h
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_size, Option.getD_some]

theorem bPre_getD_le (gens : Array Mt) (par : Array (ℕ × ℕ)) {i : ℕ} :
    ∀ m, i ≤ m → (bPre gens par m).getD i oneM = (bPre gens par i).getD i oneM
  | 0, h => by rw [Nat.le_zero.1 h]
  | m + 1, h => by
    rcases Nat.lt_or_ge i (m + 1) with hi | hi
    · rw [bPre_succ, bStep, getD_push_lt (by rw [bPre_size]; omega)]
      exact bPre_getD_le gens par m (by omega)
    · obtain rfl : i = m + 1 := by omega
      rfl

theorem canonB_mem_bPre (gens : Array Mt) (par : Array (ℕ × ℕ)) :
    ∀ m, ∀ x ∈ bPre gens par m, canonB x = true
  | 0, x, hx => by
    have e : bPre gens par 0 = #[oneM] := rfl
    rw [e, Array.mem_singleton] at hx
    rw [hx]
    exact canonB_oneM
  | m + 1, x, hx => by
    rw [bPre_succ, bStep, Array.mem_push] at hx
    rcases hx with hx | rfl
    · exact canonB_mem_bPre gens par m x hx
    · exact canonB_mulM _ _

theorem canonB_buildE (gens : Array Mt) (par : Array (ℕ × ℕ)) (i : ℕ) :
    canonB ((buildE gens par).getD i oneM) = true := by
  rw [buildE_eq, Array.getD_eq_getD_getElem?]
  rcases h : (bPre gens par (par.size - 1))[i]? with _ | x
  · rw [Option.getD_none]
    exact canonB_oneM
  · rw [Option.getD_some]
    exact canonB_mem_bPre gens par _ x (Array.mem_of_getElem? h)

theorem buildE_size (gens : Array Mt) {par : Array (ℕ × ℕ)} (h : 0 < par.size) :
    (buildE gens par).size = par.size := by
  rw [buildE_eq, bPre_size]
  omega

theorem buildE_getD_zero (gens : Array Mt) (par : Array (ℕ × ℕ)) :
    (buildE gens par).getD 0 oneM = oneM := by
  have e : bPre gens par 0 = #[oneM] := rfl
  rw [buildE_eq, bPre_getD_le gens par _ (Nat.zero_le _), e]
  simp [Array.getD_eq_getD_getElem?]

theorem buildE_getD (gens : Array Mt) {par : Array (ℕ × ℕ)} {i : ℕ} (hi : i < par.size)
    (hi0 : i ≠ 0) (hp : (par.getD i (0, 0)).1 < i) :
    (buildE gens par).getD i oneM = mulM ((buildE gens par).getD (par.getD i (0, 0)).1 oneM)
      (gens.getD (par.getD i (0, 0)).2 oneM) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi0
  rw [buildE_eq, bPre_getD_le gens par _ (by omega), bPre_succ, bStep,
    getD_push_size (by rw [bPre_size]),
    bPre_getD_le gens par (par.size - 1) (i := (par.getD (k + 1) (0, 0)).1) (by omega),
    bPre_getD_le gens par k (i := (par.getD (k + 1) (0, 0)).1) (by omega)]

end CFSG.KC.EvenSporSuz.Syl
