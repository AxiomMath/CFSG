module

public import CFSG.Certificates.Kernel.LocalQTEnumWProved

public section

namespace CFSG.KC.LQT.BW.App

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.LQT.BW.Pf
open CFSG.KC.LQT.BW.Cl
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

@[expose] def AR (n : Nat) (app : Nat → List Nat → List Nat) (c : Nat) (s : Array Nat) : Prop :=
  (∀ q < n, img s q < n) ∧ ∀ l : List Nat, (∀ x ∈ l, x < n) → app c l = applyTab s l

theorem ar_app {n : Nat} {app : Nat → List Nat → List Nat} {c : Nat} {s : Array Nat}
    (h : AR n app c s) {l : List Nat} (hl : ∀ x ∈ l, x < n) : app c l = applyTab s l := h.2 l hl

theorem ar_lt {n : Nat} {app : Nat → List Nat → List Nat} {c : Nat} {s : Array Nat}
    (h : AR n app c s) {l : List Nat} (hl : ∀ x ∈ l, x < n) : ∀ x ∈ applyTab s l, x < n := by
  intro x hx
  rw [applyTab, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact h.1 y (hl y hy)

section Sim

variable {n w nb L : Nat} {G : List (Array Nat)} {app : Nat → List Nat → List Nat}

theorem step_corrA (hw : n ≤ 2 ^ w) {es : ES} {S : St} (hc : Corr n w nb L G es S) {i : Nat}
    (hi : i < S.1.size) {g : Nat} {s : Array Nat} (hg : AR n app g s) (hsG : s ∈ G) :
    Corr n w nb L G
      (if memTT es.kt (keyW w nb (app g S.1[i]!)) = true
        then foundE es (keyW w nb (app g S.1[i]!)) (app g S.1[i]!)
        else newE i es (keyW w nb (app g S.1[i]!)) (app g S.1[i]!))
      (bodyB n nb i S.1[i]! S s) ∧
    ∃ new, Ext S (bodyB n nb i S.1[i]! S s) new ∧
      (if memTT es.kt (keyW w nb (app g S.1[i]!)) = true
        then foundE es (keyW w nb (app g S.1[i]!)) (app g S.1[i]!)
        else newE i es (keyW w nb (app g S.1[i]!)) (app g S.1[i]!)).fr =
          new.reverse ++ es.fr ∧
      ((if memTT es.kt (keyW w nb (app g S.1[i]!)) = true
        then foundE es (keyW w nb (app g S.1[i]!)) (app g S.1[i]!)
        else newE i es (keyW w nb (app g S.1[i]!)) (app g S.1[i]!)).ok = true →
        es.ok = true ∧ ∃ j < (bodyB n nb i S.1[i]! S s).1.size,
          (bodyB n nb i S.1[i]! S s).1[j]! = applyTab s S.1[i]!) := by
  obtain ⟨hr, hp, hcnt, hps, hv, ho, hm, hl, hmc, hmg, hpar⟩ := hc
  have hT := val_get hv hi
  have hcv : Val n L (applyTab s S.1[i]!) :=
    ⟨by rw [applyTab, List.length_map]; exact hT.1, ar_lt hg hT.2⟩
  rw [ar_app hg hT.2]
  generalize hcdef : applyTab s S.1[i]! = c at hcv
  have hiff : memTT es.kt (keyW w nb c) = true ↔ S.2.2.contains (keyNat n nb c) = true := by
    rw [memTT_eq, memG_iff ltK_iff ho, hm, hmc]
    constructor
    · rintro ⟨j, hj, e⟩
      exact ⟨j, hj, (keyW_iff_keyNat hw (val_get hv hj) hcv).1 e⟩
    · rintro ⟨j, hj, e⟩
      exact ⟨j, hj, (keyW_iff_keyNat hw (val_get hv hj) hcv).2 e⟩
  unfold bodyB
  rw [hcdef]
  by_cases hfound : memTT es.kt (keyW w nb c) = true
  · rw [ite_eq_left hfound, ite_eq_left (hiff.1 hfound)]
    refine ⟨⟨hr, hp, hcnt, hps, hv, ho, hm, hl, hmc, hmg, hpar⟩, [], by simp [Pf.Ext], by simp [foundE],
      fun hok => ?_⟩
    simp only [foundE, Bool.and_eq_true] at hok
    refine ⟨hok.1, ?_⟩
    obtain ⟨j, hj, e⟩ := (hm _).1 ((memG_iff ltK_iff ho _).1 (by rwa [memTT_eq] at hfound))
    refine ⟨j, hj, ?_⟩
    have := (hl j hj).2
    rw [e, ← tabTT_eq, (eqLW_iff _ _).1 hok.2] at this
    exact this.symm
  · rw [ite_eq_right hfound, ite_eq_right (fun h => hfound (hiff.2 h))]
    have hnot : ¬ memKT es.kt (keyW w nb c) := fun h =>
      hfound (by rw [memTT_eq]; exact (memG_iff ltK_iff ho _).2 h)
    have hnotN : ∀ j < S.1.size, keyNat n nb S.1[j]! ≠ keyNat n nb c := fun j hj e =>
      hfound (hiff.2 ((hmc _).2 ⟨j, hj, e⟩))
    have hnotW : ∀ j < S.1.size, keyW w nb S.1[j]! ≠ keyW w nb c := fun j hj e =>
      hnot ((hm _).2 ⟨j, hj, e⟩)
    have hext : Ext S (S.1.push c, S.2.1.push i, S.2.2.insert (keyNat n nb c) S.1.size) [c] := by
      simp [Pf.Ext]
    have hgetS : ∀ j < S.1.size, (S.1.push c)[j]! = S.1[j]! := fun j hj => ext_get hext hj
    have hgetN : (S.1.push c)[S.1.size]! = c := by
      rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, [c], hext, by simp [newE], fun hok => ?_⟩
    · simp [newE, hr]
    · simp [newE, hp]
    · simp [newE, hcnt]
    · simp [hps]
    · intro T hT'
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hT'
      rcases hT' with hT' | rfl
      · exact hv T hT'
      · exact hcv
    · simp only [newE]
      rw [insTT_eq]
      exact ord_insG ltK_iff _ _ _ ho
    · intro y
      simp only [newE]
      rw [insTT_eq, mem_insG ltK_iff, hm]
      constructor
      · rintro (rfl | ⟨j, hj, e⟩)
        · exact ⟨S.1.size, by simp, by rw [hgetN]⟩
        · exact ⟨j, by simp; omega, by rw [hgetS j hj, e]⟩
      · rintro ⟨j, hj, e⟩
        simp only [Array.size_push] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact Or.inr ⟨j, hj, by rw [← hgetS j hj, e]⟩
        · exact Or.inl (by rw [← e, hgetN])
    · intro j hj
      simp only [newE]
      rw [insTT_eq]
      simp only [Array.size_push] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hgetS j hj, (look_insG_ne _ _ _ (hnotW j hj) _).1, (look_insG_ne _ _ _ (hnotW j hj) _).2]
        exact hl j hj
      · rw [hgetN, (look_insG_self _ _ _ hnot).1, (look_insG_self _ _ _ hnot).2, hcnt]
        exact ⟨rfl, rfl⟩
    · intro y
      rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, hmc]
      constructor
      · rintro (rfl | ⟨j, hj, e⟩)
        · exact ⟨S.1.size, by simp, by rw [hgetN]⟩
        · exact ⟨j, by simp; omega, by rw [hgetS j hj, e]⟩
      · rintro ⟨j, hj, e⟩
        simp only [Array.size_push] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact Or.inr ⟨j, hj, by rw [← hgetS j hj, e]⟩
        · exact Or.inl (by rw [← e, hgetN])
    · intro j hj
      rw [Std.HashMap.getD_insert]
      simp only [Array.size_push] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hgetS j hj, ite_eq_right (by rw [beq_iff_eq]; exact fun e => hnotN j hj e.symm)]
        exact hmg j hj
      · rw [hgetN, ite_eq_left (by rw [beq_iff_eq])]
    · intro j hj hj0
      simp only [Array.size_push] at hj
      have hpget : ∀ k < S.1.size, (S.2.1.push i)[k]! = S.2.1[k]! := by
        intro k hk
        rw [arr_getN, arr_getN, Array.toList_push, getD_append_left (by simp; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · obtain ⟨h1, s', hs', h2⟩ := hpar j hj hj0
        rw [hpget j hj, hgetS j hj, hgetS _ (by omega)]
        exact ⟨h1, s', hs', h2⟩
      · have e : (S.2.1.push i)[S.1.size]! = i := by
          rw [arr_getN, Array.toList_push, ← hps]
          rw [show S.2.1.size = S.2.1.toList.length by simp, getD_append_len]
        rw [e, hgetN, hgetS i hi, ← hcdef]
        exact ⟨hi, s, hsG, rfl⟩
    · exact ⟨by simpa [newE] using hok, S.1.size, by simp, by rw [hgetN]⟩

theorem kids_corrA (hw : n ≤ 2 ^ w) {T : List Nat} {i : Nat} : ∀ (Gp : List (Nat × Array Nat))
    (es : ES) (S : St), (∀ p ∈ Gp, AR n app p.1 p.2 ∧ p.2 ∈ G) → Corr n w nb L G es S →
    i < S.1.size → S.1[i]! = T →
    Corr n w nb L G (kidsW w nb (app) (Gp.map Prod.fst) i T es)
      ((Gp.map Prod.snd).foldl (bodyB n nb i T) S) ∧
    ∃ new, Ext S ((Gp.map Prod.snd).foldl (bodyB n nb i T) S) new ∧
      (kidsW w nb (app) (Gp.map Prod.fst) i T es).fr = new.reverse ++ es.fr ∧
      ((kidsW w nb (app) (Gp.map Prod.fst) i T es).ok = true → es.ok = true ∧
        ∀ p ∈ Gp, ∃ j < ((Gp.map Prod.snd).foldl (bodyB n nb i T) S).1.size,
          ((Gp.map Prod.snd).foldl (bodyB n nb i T) S).1[j]! = applyTab p.2 T)
  | [], es, S, _, hc, _, _ => ⟨hc, [], by simp [Pf.Ext], by simp [kidsW_nil], fun h =>
      ⟨by simpa [kidsW_nil] using h, fun p hp => by simp at hp⟩⟩
  | p :: Gp, es, S, hG, hc, hi, hT => by
    rw [List.map_cons, List.map_cons, kidsW_cons, List.foldl_cons]
    have hp := hG p (List.mem_cons_self ..)
    obtain ⟨hc1, new1, he1, hf1, hok1⟩ := step_corrA hw hc hi hp.1 hp.2
    rw [hT] at hc1 he1 hf1 hok1
    have hi1 : i < (bodyB n nb i T S p.2).1.size := by rw [ext_size he1]; omega
    have hT1 : (bodyB n nb i T S p.2).1[i]! = T := by rw [ext_get he1 hi, hT]
    obtain ⟨hc2, new2, he2, hf2, hok2⟩ := kids_corrA hw Gp _ _
      (fun q hq => hG q (List.mem_cons_of_mem _ hq)) hc1 hi1 hT1
    refine ⟨hc2, new1 ++ new2, ext_trans he1 he2, by rw [hf2, hf1, List.reverse_append,
      List.append_assoc], fun hok => ?_⟩
    obtain ⟨h1, h2⟩ := hok2 hok
    obtain ⟨h3, j, hj, h4⟩ := hok1 h1
    refine ⟨h3, fun q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · refine ⟨j, by rw [ext_size he2]; omega, ?_⟩
      rw [ext_get he2 hj, h4]
    · exact h2 q hq

theorem round_corrA (hw : n ≤ 2 ^ w) {gi : Nat} {Gp : List (Nat × Array Nat)}
    (hG : ∀ p ∈ Gp, AR n app p.1 p.2 ∧ p.2 ∈ G) (hGs : Gp.map Prod.snd = G) :
    ∀ (F : List (List Nat)) (i : Nat) (es : ES) (S : St), Corr n w nb L G es S →
    (∀ t < F.length, i + t < S.1.size ∧ S.1[i + t]! = F.getD t []) →
    ∃ S', Corr n w nb L G (roundW w nb gi (app) (Gp.map Prod.fst) F i es) S' ∧
      (∀ f, bfsLoopB n nb G (F.length + f) i S = bfsLoopB n nb G f (i + F.length) S') ∧
      ∃ new, Ext S S' new ∧
        (roundW w nb gi (app) (Gp.map Prod.fst) F i es).fr = new.reverse ++ es.fr ∧
        ((roundW w nb gi (app) (Gp.map Prod.fst) F i es).ok = true → es.ok = true ∧
          ∀ t < F.length, ∀ s ∈ G, ∃ j < S'.1.size, S'.1[j]! = applyTab s S'.1[i + t]!)
  | [], i, es, S, hc, _ => ⟨S, hc, fun f => by simp, [], by simp [Pf.Ext], by simp [roundW_nil],
      fun h => ⟨by simpa [roundW_nil] using h, fun t ht => by simp at ht⟩⟩
  | T :: F, i, es, S, hc, hF => by
    rw [roundW_cons]
    have h0 := hF 0 (by simp)
    simp only [Nat.add_zero, List.getD_cons_zero] at h0
    obtain ⟨hc1, new1, he1, hf1, hok1⟩ := kids_corrA (L := L) hw Gp es S hG hc h0.1 h0.2
    rw [hGs] at hc1 he1 hok1
    have hF1 : ∀ t < F.length, i + 1 + t < (G.foldl (bodyB n nb i T) S).1.size ∧
        (G.foldl (bodyB n nb i T) S).1[i + 1 + t]! = F.getD t [] := by
      intro t ht
      have := hF (t + 1) (by simp; omega)
      rw [List.getD_cons_succ, show i + (t + 1) = i + 1 + t by omega] at this
      exact ⟨by rw [ext_size he1]; omega, by rw [ext_get he1 this.1, this.2]⟩
    obtain ⟨S2, hc2, hb2, new2, he2, hf2, hok2⟩ := round_corrA hw hG hGs F (i + 1)
      (clfix gi (kidsW w nb (app) (Gp.map Prod.fst) i T es)) _ hc1 hF1
    refine ⟨S2, hc2, fun f => ?_, new1 ++ new2, ext_trans he1 he2, ?_, fun hok => ?_⟩
    · rw [List.length_cons, show F.length + 1 + f = (F.length + f) + 1 by omega, bfsLoopB_succ,
        ite_eq_left h0.1, h0.2, hb2, show i + 1 + F.length = i + (F.length + 1) by omega]
    · rw [hf2]
      change new2.reverse ++ (kidsW w nb (app) (Gp.map Prod.fst) i T es).fr = _
      rw [hf1, List.reverse_append, List.append_assoc]
    · obtain ⟨h1, h2⟩ := hok2 hok
      obtain ⟨h3, h4⟩ := hok1 h1
      refine ⟨h3, fun t ht s hs => ?_⟩
      cases t with
      | zero =>
        rw [← hGs] at hs
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
        obtain ⟨j, hj, e⟩ := h4 p hp
        refine ⟨j, by rw [ext_size he2]; omega, ?_⟩
        rw [ext_get he2 hj, e, Nat.add_zero, ext_get (ext_trans he1 he2) h0.1, h0.2]
      | succ t =>
        have := h2 t (by simpa using ht) s hs
        rwa [show i + 1 + t = i + (t + 1) by omega] at this

theorem enum_corrA (hw : n ≤ 2 ^ w) {gi : Nat} {Gp : List (Nat × Array Nat)}
    (hG : ∀ p ∈ Gp, AR n app p.1 p.2 ∧ p.2 ∈ G) (hGs : Gp.map Prod.snd = G) {o : List Nat}
    (ho : Val n L o) : ∀ dd, ∃ S,
      Corr n w nb L G (enumW w nb gi (app) (Gp.map Prod.fst) o dd).1 S ∧
      (∀ f, bfsLoopB n nb G ((enumW w nb gi (app) (Gp.map Prod.fst) o dd).2.1 + f) 0
          (S0 n nb o) =
        bfsLoopB n nb G f (enumW w nb gi (app) (Gp.map Prod.fst) o dd).2.1 S) ∧
      (enumW w nb gi (app) (Gp.map Prod.fst) o dd).2.2 =
        S.1.toList.drop (enumW w nb gi (app) (Gp.map Prod.fst) o dd).2.1 ∧
      (enumW w nb gi (app) (Gp.map Prod.fst) o dd).2.1 ≤ S.1.size ∧
      ((enumW w nb gi (app) (Gp.map Prod.fst) o dd).1.ok = true →
        ∀ j < (enumW w nb gi (app) (Gp.map Prod.fst) o dd).2.1, ∀ s ∈ G,
          ∃ k < S.1.size, S.1[k]! = applyTab s S.1[j]!) ∧
      ∃ new, Ext (S0 n nb o) S new
  | 0 => by
    rw [enumW_zero]
    have hget : ∀ i < (S0 n nb o).1.size, (S0 n nb o).1[i]! = o := by
      intro i hi
      have hi0 : i = 0 := by simpa [S0] using hi
      subst hi0
      rfl
    have hsz : (S0 n nb o).1.size = 1 := rfl
    refine ⟨S0 n nb o, ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun f => by simp, by
      simp [S0], by simp [S0], fun _ j hj => by simp at hj, [], by simp [Pf.Ext]⟩
    · intro T hT
      simp only [S0, List.mem_singleton] at hT
      rw [hT]
      exact ho
    · change OrdT (insTT TT.lf (keyW w nb o) 0 o)
      rw [insTT_eq]
      exact ord_insG ltK_iff _ _ _ trivial
    · intro y
      change memKT (insTT TT.lf (keyW w nb o) 0 o) y ↔ _
      rw [insTT_eq, mem_insG ltK_iff]
      simp only [memKT, or_false, hsz]
      constructor
      · rintro rfl
        exact ⟨0, by omega, by rw [hget 0 (by rw [hsz]; omega)]⟩
      · rintro ⟨i, hi, rfl⟩
        rw [hget i (by rw [hsz]; omega)]
    · intro i hi
      change idxG ltK (insTT TT.lf (keyW w nb o) 0 o) _ = i ∧
        tabG ltK (insTT TT.lf (keyW w nb o) 0 o) _ = _
      have hn : ¬ memKT TT.lf (keyW w nb o) := fun h => h
      rw [hget i hi, insTT_eq, (look_insG_self _ _ _ hn).1, (look_insG_self _ _ _ hn).2]
      rw [hsz] at hi
      exact ⟨by omega, rfl⟩
    · intro y
      simp only [S0, Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false,
        beq_iff_eq]
      constructor
      · rintro rfl
        exact ⟨0, by simp, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        rfl
    · intro i hi
      rw [hget i hi]
      simp only [S0, Std.HashMap.getD_insert, beq_self_eq_true, ite_true]
      rw [hsz] at hi
      omega
    · intro i hi hi0
      rw [hsz] at hi
      omega
  | dd + 1 => by
    obtain ⟨S, hc, hb, hF, hle, hok, new0, he0⟩ := enum_corrA hw hG hGs ho dd
    rcases hE : enumW w nb gi (app) (Gp.map Prod.fst) o dd with ⟨st, i, F⟩
    rw [hE] at hc hb hF hle hok
    dsimp only at hc hb hF hle hok
    rw [enumW_succ w nb gi (app) (Gp.map Prod.fst) o dd st i F hE]
    have hc0 : Corr n w nb L G (ES.mk st.kt st.cnt st.rev st.par st.cl [] st.ok) S := hc
    have hFi : ∀ t < F.length, i + t < S.1.size ∧ S.1[i + t]! = F.getD t [] := by
      intro t ht
      rw [hF] at ht ⊢
      simp only [List.length_drop, Array.length_toList] at ht
      refine ⟨by omega, ?_⟩
      rw [arr_getL, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
    obtain ⟨S', hc', hb', new, he, hf, hok'⟩ := round_corrA (gi := gi) hw hG hGs F i _ S hc0 hFi
    have hlen : i + F.length = S.1.size := by
      rw [hF, List.length_drop, Array.length_toList]
      omega
    have hcnt : st.cnt = S.1.size := hc.2.2.1
    refine ⟨S', hc', fun f => ?_, ?_, ?_, fun hk j hj s hs => ?_, new0 ++ new, ext_trans he0 he⟩
    · dsimp only
      rw [hcnt, ← hlen, Nat.add_assoc, hb, hb', hlen]
    · dsimp only
      rw [revOn_eq, List.append_nil, hf, List.append_nil, List.reverse_reverse, hcnt, he,
        List.drop_left' (by simp)]
    · dsimp only
      rw [ext_size he, hcnt]
      omega
    · dsimp only at hk hj
      obtain ⟨h1, h2⟩ := hok' hk
      rw [hcnt] at hj
      rcases Nat.lt_or_ge j i with hji | hji
      · obtain ⟨k, hk, e⟩ := hok h1 j hji s hs
        refine ⟨k, by rw [ext_size he]; omega, ?_⟩
        rw [ext_get he hk, ext_get he (by omega), e]
      · have := h2 (j - i) (by omega) s hs
        rwa [show i + (j - i) = j by omega] at this

end Sim

@[expose] def ClIA (w nb gg : Nat) (app : Nat → List Nat → List Nat) (Gc : List Nat) (es : ES) : Prop :=
  OrdT es.kt ∧ ∀ t j, j < Gc.length → t * gg + j < es.cl.length →
    t < es.rev.length ∧
    memKT es.kt (keyW w nb (app (Gc.getD j 0) (es.rev.reverse.getD t []))) ∧
    idxG ltK es.kt (keyW w nb (app (Gc.getD j 0) (es.rev.reverse.getD t []))) =
      es.cl.reverse.getD (t * gg + j) 0

section Inv

variable {w nb gg : Nat} {app : Nat → List Nat → List Nat} {Gc : List Nat}

theorem step_clA {es : ES} (hc : ClIA w nb gg app Gc es) {i j0 : Nat} {T : List Nat} (hj0 : j0 < Gc.length)
    (hg : Gc.length ≤ gg) (hi : i < es.rev.length) (hT : es.rev.reverse.getD i [] = T)
    (hl : es.cl.length = i * gg + j0) :
    ClIA w nb gg app Gc (if memTT es.kt (keyW w nb (app (Gc.getD j0 0) T)) = true
        then foundE es (keyW w nb (app (Gc.getD j0 0) T)) (app (Gc.getD j0 0) T)
        else newE i es (keyW w nb (app (Gc.getD j0 0) T)) (app (Gc.getD j0 0) T)) ∧
    (if memTT es.kt (keyW w nb (app (Gc.getD j0 0) T)) = true
        then foundE es (keyW w nb (app (Gc.getD j0 0) T)) (app (Gc.getD j0 0) T)
        else newE i es (keyW w nb (app (Gc.getD j0 0) T)) (app (Gc.getD j0 0) T)).cl.length =
      es.cl.length + 1 ∧
    ∃ new, (if memTT es.kt (keyW w nb (app (Gc.getD j0 0) T)) = true
        then foundE es (keyW w nb (app (Gc.getD j0 0) T)) (app (Gc.getD j0 0) T)
        else newE i es (keyW w nb (app (Gc.getD j0 0) T)) (app (Gc.getD j0 0) T)).rev.reverse =
      es.rev.reverse ++ new := by
  obtain ⟨ho, hcl⟩ := hc
  generalize hc' : app (Gc.getD j0 0) T = c
  have hpos : ∀ t j, j < Gc.length → t * gg + j = es.cl.length → t = i ∧ j = j0 := by
    intro t j hj e
    rw [hl] at e
    exact pos_uniq (Nat.lt_of_lt_of_le hj hg) (Nat.lt_of_lt_of_le hj0 hg) e
  by_cases hf : memTT es.kt (keyW w nb c) = true
  · rw [ite_eq_left hf]
    refine ⟨⟨ho, fun t j hj ht => ?_⟩, by simp [foundE], [], by simp [foundE]⟩
    simp only [foundE, List.length_cons] at ht ⊢
    rw [List.reverse_cons]
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
    · rw [getD_append_left (by simpa using ht)]
      exact hcl t j hj ht
    · obtain ⟨rfl, rfl⟩ := hpos t j hj ht
      rw [ht, show es.cl.length = es.cl.reverse.length by simp, getD_append_len, hT, hc',
        ← idxTT_eq]
      refine ⟨hi, ?_, rfl⟩
      rw [memTT_eq, memG_iff ltK_iff ho] at hf
      exact hf
  · rw [ite_eq_right hf]
    have hnot : ¬ memKT es.kt (keyW w nb c) := fun h =>
      hf (by rw [memTT_eq]; exact (memG_iff ltK_iff ho _).2 h)
    refine ⟨⟨?_, fun t j hj ht => ?_⟩, by simp [newE], [c], by simp [newE]⟩
    · simp only [newE]
      rw [insTT_eq]
      exact ord_insG ltK_iff _ _ _ ho
    · simp only [newE, List.length_cons] at ht ⊢
      rw [List.reverse_cons, List.reverse_cons, insTT_eq]
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
      · obtain ⟨h1, h2, h3⟩ := hcl t j hj ht
        rw [getD_append_left (by simpa using h1), getD_append_left (by simpa using ht)]
        have hne : keyW w nb (app (Gc.getD j 0) (es.rev.reverse.getD t [])) ≠ keyW w nb c :=
          fun e => hnot (e ▸ h2)
        refine ⟨by omega, (mem_insG ltK_iff _ _ _ _ _).2 (Or.inr h2), ?_⟩
        rw [(look_insG_ne _ _ _ hne _).1]
        exact h3
      · obtain ⟨rfl, rfl⟩ := hpos t j hj ht
        rw [ht, show es.cl.length = es.cl.reverse.length by simp, getD_append_len,
          getD_append_left (by simpa using hi), hT, hc']
        exact ⟨by omega, (mem_insG ltK_iff _ _ _ _ _).2 (Or.inl rfl),
          (look_insG_self _ _ _ hnot).1⟩

theorem kids_clA {i : Nat} {T : List Nat} (hg : Gc.length ≤ gg) : ∀ (Gs : List Nat) (j0 : Nat)
    (es : ES), Gc.drop j0 = Gs → ClIA w nb gg app Gc es → es.cl.length = i * gg + j0 →
    i < es.rev.length → es.rev.reverse.getD i [] = T →
    ClIA w nb gg app Gc (kidsW w nb (app) Gs i T es) ∧
    (kidsW w nb (app) Gs i T es).cl.length = i * gg + j0 + Gs.length ∧
    ∃ new, (kidsW w nb (app) Gs i T es).rev.reverse = es.rev.reverse ++ new
  | [], _, es, _, hc, hl, _, _ => ⟨hc, by rw [kidsW_nil, hl]; rfl, [], by simp [kidsW_nil]⟩
  | s :: Gs, j0, es, hd, hc, hl, hi, hT => by
    have hj0 : j0 < Gc.length := by
      have := congrArg List.length hd
      simp at this
      omega
    have hs : Gc.getD j0 0 = s := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj0, Option.getD_some]
      have := congrArg List.head? hd
      rw [List.head?_drop, List.head?_cons] at this
      rw [List.getElem?_eq_getElem hj0] at this
      exact Option.some.inj this
    have hd' : Gc.drop (j0 + 1) = Gs := by
      rw [← List.drop_drop, hd, List.drop_one, List.tail_cons]
    rw [kidsW_cons]
    rw [← hs]
    obtain ⟨hc1, hl1, new1, hr1⟩ := step_clA hc hj0 hg hi hT hl
    have hi1 : i < (if memTT es.kt (keyW w nb (app (Gc.getD j0 0) T)) = true
        then foundE es (keyW w nb (app (Gc.getD j0 0) T)) (app (Gc.getD j0 0) T)
        else newE i es (keyW w nb (app (Gc.getD j0 0) T)) (app (Gc.getD j0 0) T)).rev.length := by
      have := congrArg List.length hr1
      simp only [List.length_reverse, List.length_append] at this
      omega
    have hT1 : (if memTT es.kt (keyW w nb (app (Gc.getD j0 0) T)) = true
        then foundE es (keyW w nb (app (Gc.getD j0 0) T)) (app (Gc.getD j0 0) T)
        else newE i es (keyW w nb (app (Gc.getD j0 0) T)) (app (Gc.getD j0 0) T)).rev.reverse.getD
          i [] = T := by
      rw [hr1, getD_append_left (by simpa using hi), hT]
    rw [hs] at hc1 hl1 hr1 hi1 hT1 ⊢
    obtain ⟨hc2, hl2, new2, hr2⟩ := kids_clA hg Gs (j0 + 1) _ hd' hc1 (by rw [hl1, hl]; omega) hi1 hT1
    refine ⟨hc2, by rw [hl2, List.length_cons]; omega, new1 ++ new2, by
      rw [hr2, hr1, List.append_assoc]⟩

theorem clfix_clA {gi : Nat} (hgg : gg = Gc.length + gi) {es : ES} {i : Nat}
    (hc : ClIA w nb gg app Gc es) (hl : es.cl.length = i * gg + Gc.length) :
    ClIA w nb gg app Gc (clfix gi es) ∧ (clfix gi es).cl.length = (i + 1) * gg := by
  obtain ⟨ho, hcl⟩ := hc
  have hlen : (clfix gi es).cl.length = (i + 1) * gg := by
    simp only [clfix, zerosOn_eq, List.length_append, List.length_replicate, hl, Nat.succ_mul]
    omega
  refine ⟨⟨ho, fun t j hj ht => ?_⟩, hlen⟩
  rw [hlen] at ht
  have hrev : (clfix gi es).cl.reverse = es.cl.reverse ++ List.replicate gi 0 := by
    simp [clfix, zerosOn_eq]
  have hold : t * gg + j < es.cl.length := by
    apply Nat.lt_of_not_le
    intro hge
    rw [hl] at hge
    exact pos_gap hj (by omega) hge ht
  rw [hrev, getD_append_left (by simpa using hold)]
  exact hcl t j hj hold

theorem round_clA {gi : Nat} (hgg : gg = Gc.length + gi) : ∀ (F : List (List Nat)) (i : Nat)
    (es : ES), ClIA w nb gg app Gc es → es.cl.length = i * gg →
    (∀ t < F.length, i + t < es.rev.length ∧ es.rev.reverse.getD (i + t) [] = F.getD t []) →
    ClIA w nb gg app Gc (roundW w nb gi (app) Gc F i es) ∧
    (roundW w nb gi (app) Gc F i es).cl.length = (i + F.length) * gg ∧
    ∃ new, (roundW w nb gi (app) Gc F i es).rev.reverse = es.rev.reverse ++ new
  | [], i, es, hc, hl, _ => ⟨hc, by rw [roundW_nil, hl]; rfl, [], by simp [roundW_nil]⟩
  | T :: F, i, es, hc, hl, hF => by
    rw [roundW_cons]
    have h0 := hF 0 (by simp)
    simp only [Nat.add_zero, List.getD_cons_zero] at h0
    obtain ⟨hc1, hl1, new1, hr1⟩ := kids_clA (T := T) (by omega) Gc 0 es rfl hc
      (by rw [hl]; omega) h0.1 h0.2
    rw [Nat.add_zero] at hl1
    obtain ⟨hc2, hl2⟩ := clfix_clA hgg hc1 hl1
    have hF1 : ∀ t < F.length, i + 1 + t < (clfix gi (kidsW w nb (app) Gc i T es)).rev.length ∧
        (clfix gi (kidsW w nb (app) Gc i T es)).rev.reverse.getD (i + 1 + t) [] = F.getD t [] := by
      intro t ht
      have := hF (t + 1) (by simp; omega)
      rw [List.getD_cons_succ, show i + (t + 1) = i + 1 + t by omega] at this
      have hr1' : (clfix gi (kidsW w nb (app) Gc i T es)).rev.reverse = es.rev.reverse ++ new1 :=
        hr1
      refine ⟨?_, ?_⟩
      · have := congrArg List.length hr1'
        simp only [List.length_reverse, List.length_append] at this
        omega
      · rw [hr1', getD_append_left (by simpa using this.1), this.2]
    obtain ⟨hc3, hl3, new2, hr3⟩ := round_clA hgg F (i + 1) _ hc2 hl2 hF1
    refine ⟨hc3, by rw [hl3, List.length_cons]; congr 1; omega, new1 ++ new2, ?_⟩
    rw [hr3, ← List.append_assoc]
    exact congrArg (· ++ new2) hr1

end Inv

theorem enum_clA {n w nb L gg : Nat} {G : List (Array Nat)} {app : Nat → List Nat → List Nat}
    (hw : n ≤ 2 ^ w) {gi : Nat}
    {Gp : List (Nat × Array Nat)} (hG : ∀ p ∈ Gp, AR n app p.1 p.2 ∧ p.2 ∈ G)
    (hGs : Gp.map Prod.snd = G) {o : List Nat} (ho : Val n L o) (hgg : gg = Gp.length + gi) :
    ∀ dd, ClIA w nb gg app (Gp.map Prod.fst) (enumW w nb gi (app) (Gp.map Prod.fst) o dd).1 ∧
      (enumW w nb gi (app) (Gp.map Prod.fst) o dd).1.cl.length =
        (enumW w nb gi (app) (Gp.map Prod.fst) o dd).2.1 * gg
  | 0 => by
    rw [enumW_zero]
    refine ⟨⟨?_, fun t j _ ht => by simp at ht⟩, by simp⟩
    change OrdT (insTT TT.lf (keyW w nb o) 0 o)
    rw [insTT_eq]
    exact ord_insG ltK_iff _ _ _ trivial
  | dd + 1 => by
    obtain ⟨S, hc, -, hF, hle, -, -, -⟩ := enum_corrA (nb := nb) (gi := gi) hw hG hGs ho dd
    obtain ⟨ih1, ih2⟩ := enum_clA hw hG hGs ho hgg dd
    rcases hE : enumW w nb gi (app) (Gp.map Prod.fst) o dd with ⟨st, i, F⟩
    rw [hE] at hc hF hle ih1 ih2
    dsimp only at hc hF hle ih1 ih2
    rw [enumW_succ w nb gi (app) (Gp.map Prod.fst) o dd st i F hE]
    have hr : S.1.toList = st.rev.reverse := hc.1
    have hcnt : st.cnt = S.1.size := hc.2.2.1
    rw [hr] at hF
    have hrl : st.rev.length = S.1.size := by
      have := congrArg List.length hr
      simp only [Array.length_toList, List.length_reverse] at this
      omega
    have hFl : F.length = st.rev.length - i := by rw [hF, List.length_drop, List.length_reverse]
    obtain ⟨h1, h2, -⟩ := round_clA (gi := gi) (by rw [List.length_map]; exact hgg) F i
      (ES.mk st.kt st.cnt st.rev st.par st.cl [] st.ok) ih1 ih2 (by
        intro t ht
        rw [hFl] at ht
        refine ⟨by dsimp only; omega, ?_⟩
        dsimp only
        rw [hF, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop])
    refine ⟨h1, ?_⟩
    dsimp only
    rw [h2, hFl]
    congr 1
    omega

theorem enumA_bfs {n w : Nat} (hw : n ≤ 2 ^ w) {B : List Nat} (hB' : ∀ b ∈ B, b < n)
    {G Gi : List (Array Nat)} {app : Nat → List Nat → List Nat} {Gp : List (Nat × Array Nat)}
    (hGp : ∀ p ∈ Gp, AR n app p.1 p.2) (hGs : Gp.map Prod.snd = G) (hGil : Gi.length = G.length)
    (hinv : ∀ j < G.length, ∀ q < n, img Gi[j]! (img G[j]! q) = q) {k fuel dd : Nat}
    (X : Array (List Nat) × Array Nat × Array Nat) (hX : bfsEnumB n B G Gi fuel = X)
    (E : ES × Nat × List (List Nat))
    (hEd : enumW w B.length G.length app (Gp.map Prod.fst) (ptsOf B G) dd = E)
    (hE : enumOK k fuel E = true) :
    BaseEnumOK n B G Gi X.1 X.2.1 X.2.2 ∧
    X.1.size = 2 ^ k ∧ E.1.cnt = X.1.size ∧ E.1.par.length = X.1.size ∧
    (∀ i < X.1.size, X.2.1[i]! = E.1.par.reverse.getD i 0) ∧
    E.1.cl.length = X.1.size * (G.length + G.length) ∧
    (∀ t < X.1.size, ∀ j < G.length, X.2.2[t * (G.length + G.length) + j]! =
      E.1.cl.reverse.getD (t * (G.length + G.length) + j) 0) ∧
    (∀ i < X.1.size, Val n (ptsOf B G).length X.1[i]!) ∧ X.1.toList = E.1.rev.reverse := by
  subst hX hEd
  have hGp' : ∀ p ∈ Gp, AR n app p.1 p.2 ∧ p.2 ∈ G := fun p hp =>
    ⟨hGp p hp, by rw [← hGs]; exact List.mem_map_of_mem hp⟩
  have hGlt : ∀ s ∈ G, ∀ q < n, img s q < n := by
    intro s hs
    rw [← hGs, List.mem_map] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    exact (hGp p hp).1
  have hov : Val n (ptsOf B G).length (ptsOf B G) := by
    refine ⟨rfl, fun x hx => ?_⟩
    rw [ptsOf, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨s, hs, hx⟩
    · exact hB' x hx
    · rw [List.mem_map] at hx
      obtain ⟨b, hb, rfl⟩ := hx
      exact hGlt s hs b (hB' b hb)
  have hGpl : Gp.length = G.length := by rw [← hGs, List.length_map]
  have hfst : G.length = (Gp.map Prod.fst).length := by rw [List.length_map, hGpl]
  obtain ⟨S, hc, hb, hF, hle, hok, new0, he0⟩ :=
    enum_corrA (nb := B.length) (L := (ptsOf B G).length) (gi := G.length) (app := app) hw hGp' hGs
      hov dd
  obtain ⟨hcl, hcll⟩ := enum_clA (nb := B.length) (gg := G.length + G.length) (gi := G.length)
    (app := app) hw hGp' hGs hov (by rw [hGpl]) dd
  generalize enumW w B.length G.length app (Gp.map Prod.fst) (ptsOf B G) dd = E
    at hE hc hb hF hle hok hcl hcll ⊢
  obtain ⟨hE1, hE2, hE3, hE4⟩ := enumOK_spec hE
  have hcnt : E.1.cnt = S.1.size := hc.2.2.1
  have hiS : E.2.1 = S.1.size := by
    rw [hE1] at hF
    have : S.1.toList.length ≤ E.2.1 := List.drop_eq_nil_iff.1 hF.symm
    simp at this
    omega
  have hloop : bfsLoopB n B.length G fuel 0 (S0 n B.length (ptsOf B G)) = S := by
    have := hb (fuel - E.2.1)
    rw [show E.2.1 + (fuel - E.2.1) = fuel by omega, hiS, bfsLoopB_stop] at this
    exact this
  unfold S0 at hloop
  have hbe : bfsEnumB n B G Gi fuel = (S.1, S.2.1, (List.range S.1.size).foldl (fun acc i =>
      (G ++ Gi).foldl (fun acc' s =>
        acc'.push (S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0)) acc) #[]) := by
    simp only [bfsEnumB, hloop]
  rw [hbe]
  dsimp only
  have hc' := hc
  obtain ⟨hr, hp, -, hps, hv, -, hm, hl, -, hmg, hpar⟩ := hc'
  have hokc := hok hE4
  rw [hiS] at hokc
  have hclget : ∀ i < S.1.size, ∀ j < (G ++ Gi).length,
      ((List.range S.1.size).foldl (fun acc i => (G ++ Gi).foldl (fun acc' s =>
        acc'.push (S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0)) acc)
        (#[] : Array Nat))[i * (G.length + Gi.length) + j]! =
      S.2.2.getD (keyNat n B.length (applyTab (G ++ Gi)[j]! S.1[i]!)) 0 := by
    intro i hi j hj
    rw [arr_getN, cl_fold, ← List.length_append]
    exact (flatMap_getD (G ++ Gi) _ S.1.size).2 i hi j hj
  have hidx : ∀ i < S.1.size, ∀ {s : Array Nat} {k' : Nat}, k' < S.1.size →
      S.1[k']! = applyTab s S.1[i]! →
      S.2.2.getD (keyNat n B.length (applyTab s S.1[i]!)) 0 = k' := by
    intro i _ s k' hk' e
    rw [← e]
    exact hmg k' hk'
  have hpl : E.1.par.length = S.1.size := by
    have := congrArg List.length hp
    simp only [Array.length_toList, List.length_reverse] at this
    omega
  refine ⟨⟨by rw [ext_size he0]; simp [S0], by rw [ext_get he0 (by simp [S0])]; rfl,
    hps, hpar, keys_nodup hw hc, fun i hi j hj => ?_, fun i hi j hj => ?_⟩,
    by rw [← hcnt]; exact hE3, hcnt, hpl, fun i hi => by rw [arr_getN, hp],
    by rw [hcll, hiS], fun t ht j hj => ?_, fun i hi => val_get hv hi, hr⟩
  · have hs : G[j]! ∈ G := by rw [getElem!_pos G j hj]; exact List.getElem_mem _
    obtain ⟨k', hk', e⟩ := hokc i hi _ hs
    rw [hclget i hi j (by simp; omega), getBang_append_left hj, hidx i hi hk' e]
    exact ⟨hk', e⟩
  · have hj' : j < G.length := by omega
    have hmem : applyTab Gi[j]! S.1[i]! ∈ S.1.toList := by
      apply closed_inv (s := G[j]!) (n := n)
      · exact hinv j hj'
      · exact fun U hU => (hv U hU).2
      · intro U hU
        obtain ⟨i', hi', rfl⟩ := mem_idx hU
        have hs : G[j]! ∈ G := by rw [getElem!_pos G j hj']; exact List.getElem_mem _
        obtain ⟨k', hk', e⟩ := hokc i' hi' _ hs
        rw [← e]
        exact get_mem hk'
      · exact get_mem hi
    obtain ⟨k', hk', e⟩ := mem_idx hmem
    rw [Nat.add_assoc, hclget i hi _ (by simp; omega), getBang_append_right hj,
      hidx i hi hk' e]
    exact ⟨hk', e⟩
  · have hjG : j < Gp.length := by omega
    have hpos : t * (G.length + G.length) + j < E.1.cl.length := by
      rw [hcll, hiS]
      exact pos_lt ht (by omega)
    obtain ⟨-, hmem, hix⟩ := hcl.2 t j (by rw [List.length_map]; exact hjG) hpos
    have hgd : (Gp.map Prod.fst).getD j 0 = Gp[j].1 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hjG]
      rfl
    have hGpj := hGp' Gp[j] (List.getElem_mem _)
    have hGjp : G[j]! = Gp[j].2 := by
      rw [getElem!_pos G j (by omega)]
      simp only [← hGs, List.getElem_map]
    have hrt : E.1.rev.reverse.getD t [] = S.1[t]! := by rw [← hr, arr_getL]
    rw [hgd, hrt, ar_app hGpj.1 (val_get hv ht).2, ← hGjp] at hmem hix
    have hcv : Val n (ptsOf B G).length (applyTab G[j]! S.1[t]!) :=
      ⟨by rw [applyTab, List.length_map]; exact (val_get hv ht).1,
        ar_lt (hGjp ▸ hGpj.1) (val_get hv ht).2⟩
    obtain ⟨i', hi', e⟩ := (hm _).1 hmem
    have hix' := (hl i' hi').1
    rw [e, hix] at hix'
    have e' := (keyW_iff_keyNat hw (val_get hv hi') hcv).1 e
    have hcg := hclget t ht j (by simp; omega)
    rw [hGil] at hcg
    rw [hcg, getBang_append_left (by omega), ← e', hmg i' hi', hix']

end CFSG.KC.LQT.BW.App

end
