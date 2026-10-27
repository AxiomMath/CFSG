module

public import CFSG.Certificates.Kernel.TS8.BfsTSound
public import Certificates.Data.Kernel.TS8.Defs

public section

namespace CFSG.KC.TS8

open CFSG.EvenSporadicStandard.Fin76b.TS8D8 CFSG.EvenSporadicStandard.Fin76b.TS8EA16
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
  CFSG.KC.S63K CFSG.KS.PinvS CFSG.KS.SporSch.M24

variable {n w : ℕ}

theorem foldPush {β : Type} (f : ℕ → β) : ∀ (m s : ℕ) (out : Array β),
    ((List.range' s m).foldl (fun out k => out.push (f k)) out).toList =
      out.toList ++ (List.range' s m).map f
  | 0, _, out => by simp
  | m + 1, s, out => by
    rw [List.range'_succ, List.foldl_cons, foldPush f m (s + 1), Array.toList_push,
      List.map_cons, List.append_assoc, List.singleton_append]

theorem foldPush_get {β : Type} [Inhabited β] (f : ℕ → β) (m : ℕ) :
    ((List.range' 0 m).foldl (fun out k => out.push (f k)) #[]).size = m ∧
      ∀ i < m, ((List.range' 0 m).foldl (fun out k => out.push (f k)) #[])[i]! = f i := by
  have h := foldPush f m 0 #[]
  simp only [List.toList_toArray, List.nil_append, Array.toList_empty] at h
  have hs : ((List.range' 0 m).foldl (fun out k => out.push (f k)) #[]).size = m := by
    rw [← Array.length_toList, h, List.length_map, List.length_range']
  refine ⟨hs, fun i hi => ?_⟩
  rw [getElem!_pos _ i (by omega), ← Array.getElem_toList]
  simp only [h, List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]

theorem idxT_eq (E : Array (Array ℕ)) :
    idxT E = (List.range' 0 E.size).foldl
      (fun (m : Std.HashMap (Array ℕ) ℕ) k => m.insert E[k]! k) ∅ := by
  unfold idxT
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, pure_bind]
  rfl

theorem idx_fold {E : Array (Array ℕ)} {EP : ℕ → ℕ} (he : ∀ i < 256, E[i]! = unpack n w (EP i))
    (hPP : ∀ i < 256, PP n w (EP i)) (hd : ∀ a < 256, ∀ b < 256, EP a = EP b → a = b) (d : ℕ) :
    ∀ m ≤ 256, ∀ j < m, ((List.range' 0 m).foldl
      (fun (m : Std.HashMap (Array ℕ) ℕ) k => m.insert E[k]! k) ∅).getD (unpack n w (EP j)) d =
        j := by
  intro m
  induction m with
  | zero => intro _ j hj; omega
  | succ m ih =>
    intro hm j hj
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Nat.one_mul, Std.HashMap.getD_insert, he m (by omega)]
    by_cases e : j = m
    · subst e
      simp
    · have hne : (unpack n w (EP m) == unpack n w (EP j)) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h => e (hd j (by omega) m (by omega)
          (unpack_inj (hPP j (by omega)) (hPP m (by omega)) h.symm))
      rw [hne]
      exact ih (by omega) j (by omega)

theorem idxT_getD {E : Array (Array ℕ)} {EP : ℕ → ℕ} (hs : E.size = 256)
    (he : ∀ i < 256, E[i]! = unpack n w (EP i)) (hPP : ∀ i < 256, PP n w (EP i))
    (hd : ∀ a < 256, ∀ b < 256, EP a = EP b → a = b) (d : ℕ) {j : ℕ} (hj : j < 256) :
    (idxT E).getD (unpack n w (EP j)) d = j := by
  rw [idxT_eq, hs]
  exact idx_fold he hPP hd d 256 (le_refl _) j hj

theorem mulTabT_eq (E : Array (Array ℕ)) (idx : Std.HashMap (Array ℕ) ℕ) :
    mulTabT n E idx = (List.range' 0 256).foldl (fun T a => T.push
      ((List.range' 0 256).foldl (fun r b => r.push (idx.getD (compA n E[a]! E[b]!) 0)) #[])) #[] := by
  unfold mulTabT
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, pure_bind]
  rfl

theorem invTabT_eq (E : Array (Array ℕ)) (idx : Std.HashMap (Array ℕ) ℕ) :
    invTabT n E idx = (List.range' 0 256).foldl
      (fun T a => T.push (idx.getD (invCand n E[a]!) 0)) #[] := by
  unfold invTabT
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, pure_bind]
  rfl

theorem mulTabT_get (E : Array (Array ℕ)) (idx : Std.HashMap (Array ℕ) ℕ) (a b : ℕ) :
    ((mulTabT n E idx)[a]!)[b]! =
      if a < 256 ∧ b < 256 then idx.getD (compA n E[a]! E[b]!) 0 else 0 := by
  rw [mulTabT_eq]
  obtain ⟨h1, h2⟩ := foldPush_get (fun a =>
    (List.range' 0 256).foldl (fun r b => r.push (idx.getD (compA n E[a]! E[b]!) 0)) #[]) 256
  by_cases ha : a < 256
  · rw [h2 a ha]
    obtain ⟨g1, g2⟩ := foldPush_get (fun b => idx.getD (compA n E[a]! E[b]!) 0) 256
    by_cases hb : b < 256
    · rw [g2 b hb, if_pos ⟨ha, hb⟩]
    · rw [getElem!_neg _ b (by omega), if_neg (by omega)]
      rfl
  · rw [getElem!_neg _ a (by omega), if_neg (by omega)]
    rfl

theorem invTabT_get (E : Array (Array ℕ)) (idx : Std.HashMap (Array ℕ) ℕ) (a : ℕ) :
    (invTabT n E idx)[a]! = if a < 256 then idx.getD (invCand n E[a]!) 0 else 0 := by
  rw [invTabT_eq]
  obtain ⟨h1, h2⟩ := foldPush_get (fun a => idx.getD (invCand n E[a]!) 0) 256
  by_cases ha : a < 256
  · rw [h2 a ha, if_pos ha]
  · rw [getElem!_neg _ a (by omega), if_neg ha]
    rfl

theorem unpack_lt {p : ℕ} (hp : PP n w p) {x : ℕ} (hx : x < n) : (unpack n w p)[x]! < n := by
  rw [unpack_getElem!, if_pos hx]
  exact hp.2.1 x hx

theorem compA_assoc {t u v : Array ℕ} (ht : t.size = n) (hv : ∀ x < n, v[x]! < n) :
    compA n t (compA n u v) = compA n (compA n t u) v := by
  apply Array.ext
  · simp [compA]
  · intro i h1 _
    have hi : i < n := by simpa [compA] using h1
    simp only [compA, Array.getElem_ofFn]
    rw [getElem!_pos (Array.ofFn fun i : Fin n => u[v[i.val]!]!) i (by simp [hi]),
      Array.getElem_ofFn, getElem!_pos (Array.ofFn fun i : Fin n => t[u[i.val]!]!) (v[i]!)
        (by simp [hv i hi]), Array.getElem_ofFn]

theorem pcomp_assoc {p q r : ℕ} (hp : PP n w p) (hq : PP n w q) (hr : PP n w r) :
    pcomp n w (mask w) p (pcomp n w (mask w) q r) =
      pcomp n w (mask w) (pcomp n w (mask w) p q) r := by
  apply unpack_inj (hp.mul (hq.mul hr)) ((hp.mul hq).mul hr)
  rw [← compA_PP hp (hq.mul hr), ← compA_PP hq hr, ← compA_PP (hp.mul hq) hr, ← compA_PP hp hq]
  exact compA_assoc (by simp [unpack]) (fun x hx => unpack_lt hr hx)

theorem pcomp_id {p : ℕ} (hsz : szOK n w = true) (hp : PP n w p) :
    pcomp n w (mask w) p (pidn n w) = p := by
  apply unpack_inj (hp.mul (PP.id hsz)) hp
  rw [← compA_PP hp (PP.id hsz), ← idA_eq hsz]
  apply Array.ext
  · simp [compA, unpack]
  · intro i h1 _
    have hi : i < n := by simpa [compA] using h1
    simp only [compA, Array.getElem_ofFn]
    rw [getElem!_pos (idA n) i (by simp [idA, hi])]
    simp [idA, ← getElem!_pos (unpack n w p) i (by simp [unpack, hi])]

variable {ng : ℕ} {GW EP W Pa La MT : ℕ → ℕ}

theorem mtK_parts {MT : ℕ → ℕ → ℕ} (h : mtK MT W Pa La ng = true) :
    ∀ a < 256, MT a 0 = a ∧ ∀ b, 0 < b → b < 256 → MT a b = W (ng * MT a (Pa b) + La b) := by
  unfold mtK at h
  intro a ha
  have h1 := MatL.allN_iff.1 h a ha
  rw [MatL.bAnd_eq, Bool.and_eq_true] at h1
  refine ⟨Nat.eq_of_beq_eq_true h1.1, fun b hb0 hb => ?_⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  exact Nat.eq_of_beq_eq_true (MatL.allN_iff.1 h1.2 b' (by omega))

theorem hMT {MT : ℕ → ℕ → ℕ} (hsz : szOK n w = true) (hPP : ∀ i < 256, PP n w (EP i))
    (hGP : ∀ k < ng, PP n w (GW k)) (h0 : EP 0 = pidn n w)
    (ht : TTree n w ng GW EP Pa La 256)
    (hact : ∀ h < 256, ∀ k < ng, W (ng * h + k) < 256 ∧
      pcomp n w (mask w) (EP h) (GW k) = EP (W (ng * h + k)))
    (hmt : mtK MT W Pa La ng = true) :
    ∀ b < 256, ∀ a < 256, MT a b < 256 ∧ pcomp n w (mask w) (EP a) (EP b) = EP (MT a b) := by
  have hm := mtK_parts hmt
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb a ha
    by_cases hb0 : b = 0
    · subst hb0
      rw [(hm a ha).1, h0, pcomp_id hsz (hPP a ha)]
      exact ⟨ha, rfl⟩
    · obtain ⟨hpb, hlb, heb⟩ := ht b (by omega) hb
      obtain ⟨i1, i2⟩ := ih (Pa b) hpb (by omega) a ha
      obtain ⟨a1, a2⟩ := hact (MT a (Pa b)) i1 (La b) hlb
      rw [(hm a ha).2 b (by omega) hb, ← heb,
        pcomp_assoc (hPP a ha) (hPP (Pa b) (by omega)) (hGP (La b) hlb), i2, a2]
      exact ⟨a1, rfl⟩

theorem letP_PP {PA PB PU : ℕ} (hA : PP n w PA) (hB : PP n w PB) (hU : PP n w PU) (l : ℕ) :
    PP n w (letP n w PA PB PU l) := by
  unfold letP
  split
  · exact hA
  · split
    · exact hB
    · split
      · exact hA.inv
      · split
        · exact hB.inv
        · exact hU

theorem letT_eq {PA PB PU : ℕ} (hA : PP n w PA) (hB : PP n w PB) (l : ℕ) :
    letT n (unpack n w PA) (unpack n w PB) (unpack n w PU) l = unpack n w (letP n w PA PB PU l) := by
  unfold letT letP
  split
  · rfl
  · split
    · rfl
    · split
      · exact invCand_PP hA
      · split
        · exact invCand_PP hB
        · rfl

theorem wordT_fold {PA PB PU : ℕ} (hA : PP n w PA) (hB : PP n w PB) (hU : PP n w PU) :
    ∀ (ws : List ℕ) (acc : ℕ), PP n w acc →
      ws.foldl (fun t l => compA n t (letT n (unpack n w PA) (unpack n w PB) (unpack n w PU) l))
          (unpack n w acc) =
        unpack n w (ws.foldl (fun acc l => pcomp n w (mask w) acc (letP n w PA PB PU l)) acc) ∧
      PP n w (ws.foldl (fun acc l => pcomp n w (mask w) acc (letP n w PA PB PU l)) acc)
  | [], acc, h => ⟨rfl, h⟩
  | l :: ws, acc, h => by
    simp only [List.foldl_cons]
    rw [letT_eq hA hB l, compA_PP h (letP_PP hA hB hU l)]
    exact wordT_fold hA hB hU ws _ (h.mul (letP_PP hA hB hU l))

theorem wordT_eq {PA PB PU : ℕ} (hsz : szOK n w = true) (hA : PP n w PA) (hB : PP n w PB)
    (hU : PP n w PU) (ws : List ℕ) :
    wordT n (unpack n w PA) (unpack n w PB) (unpack n w PU) ws = unpack n w (wordP n w PA PB PU ws) ∧
      PP n w (wordP n w PA PB PU ws) := by
  unfold wordT wordP
  rw [idA_eq hsz]
  exact wordT_fold hA hB hU ws _ (PP.id hsz)

end CFSG.KC.TS8

end
