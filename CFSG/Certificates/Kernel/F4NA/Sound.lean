module

public import Certificates.Data.Kernel.F4NA
public import Certificates.Data.F4NA
public import CFSG.Certificates.Kernel.F4SaltSound

public section

namespace CFSG.KC.F4NA

open CFSG.KC.F4Salt CFSG.KC.Loop CFSG.LieType.Simplicity.TitsBits CFSG.RankThree.PartOne.SEITZX

theorem listAnd_sound {α : Type} (f : α → Bool) :
    ∀ l : List α, List.rec (motive := fun _ => Bool) true (fun z _ ih => f z && ih) l = true →
      ∀ z ∈ l, f z = true
  | [], _, z, hz => absurd hz List.not_mem_nil
  | a :: l, h, z, hz => by
    have h' : (f a && List.rec (motive := fun _ => Bool) true (fun z _ ih => f z && ih) l) = true :=
      h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hz with rfl | hz
    · exact h'.1
    · exact listAnd_sound f l h'.2 z hz

theorem shiftRight_eq' (a b : Nat) : Nat.shiftRight a b = a / 2 ^ b :=
  Nat.shiftRight_eq_div_pow a b

theorem land_eq' (a n : Nat) : Nat.land a (2 ^ n - 1) = a % 2 ^ n :=
  Nat.and_two_pow_sub_one_eq_mod a n

theorem lenR_eq : ∀ l : List Nat, lenR l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenR l) = _
    rw [lenR_eq l, List.length_cons]

theorem enc8_cons (v : Nat) (l : List Nat) : enc8 (v :: l) = v + 8 * enc8 l := rfl

theorem pwOf_read {p : List Nat} (hl : p.length ≤ 8) :
    Nat.shiftRight (pwOf p) 4 = enc8 p ∧ Nat.land (pwOf p) 15 = p.length := by
  have e : pwOf p = p.length + 16 * enc8 p := by
    change Nat.add (lenR p) (Nat.mul 16 (enc8 p)) = _
    rw [lenR_eq]
    rfl
  have hlt : p.length < 16 := by omega
  rw [e, shiftRight_eq', show (15 : Nat) = 2 ^ 4 - 1 from rfl, land_eq']
  constructor
  · rw [show (2 : Nat) ^ 4 = 16 from rfl]
    omega
  · rw [show (2 : Nat) ^ 4 = 16 from rfl]
    omega

theorem walkP_succ (RT w L i : Nat) : walkP RT w (L + 1) i =
    walkP RT (Nat.shiftRight w 3) L (l10 RT (Nat.add (Nat.mul 6 i) (Nat.land w 7))) := rfl

theorem walk_eq (RT : Nat) : ∀ (p : List Nat), (∀ g ∈ p, g < 8) → ∀ i,
    walkP RT (enc8 p) p.length i = p.foldl (fun a g => l10 RT (6 * a + g)) i
  | [], _, i => rfl
  | g :: p, h, i => by
    have hg := h g List.mem_cons_self
    rw [List.length_cons, walkP_succ, List.foldl_cons, enc8_cons]
    have e1 : Nat.shiftRight (g + 8 * enc8 p) 3 = enc8 p := by
      rw [shiftRight_eq', show (2 : Nat) ^ 3 = 8 from rfl]
      omega
    have e2 : Nat.land (g + 8 * enc8 p) 7 = g := by
      rw [show (7 : Nat) = 2 ^ 3 - 1 from rfl, land_eq', show (2 : Nat) ^ 3 = 8 from rfl]
      omega
    rw [e1, e2]
    exact walk_eq RT p (fun g hg => h g (List.mem_cons_of_mem _ hg)) _

theorem na_bAnd {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem na_bIf {c t : Bool} (h : bIf(c, t, true) = true) (hc : c = true) : t = true := by
  subst hc
  exact h

theorem brec_eq {c y : Bool} (h : Bool.rec (motive := fun _ => Bool) (!y) y c = true) : c = y := by
  cases c <;> cases y <;> first | rfl | exact absurd h (by decide)

theorem brec_true {x y c : Bool} (h : Bool.rec (motive := fun _ => Bool) x y c = true) :
    (c = true → y = true) ∧ (c = false → x = true) := by
  cases c
  · exact ⟨fun h' => absurd h' (by decide), fun _ => h⟩
  · exact ⟨fun _ => h, fun h' => absurd h' (by decide)⟩

theorem allBelow_sound {m hi : Nat} {f : Nat → Bool} (h : allBelow m hi f = true)
    (hm : m ≤ 64 * hi) : ∀ i < m, f i = true := by
  have inner : ∀ (hh n : Nat), Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) n = true →
      ∀ l < n, Nat.add (Nat.shiftLeft hh 6) l < m → f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro hh n
    induction n with
    | zero => intro _ l hl; omega
    | succ n ih =>
      intro hn l hl hlm
      obtain ⟨h1, h2⟩ := na_bAnd hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · exact ih h2 l hl hlm
      · exact na_bIf h1 (Nat.blt_eq.mpr hlm)
  have outer : ∀ n, Nat.rec (motive := fun _ => Bool) true (fun hh ih => bAnd(
      Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
        bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) 64,
        ih)) n = true → ∀ hh < n, ∀ l < 64, Nat.add (Nat.shiftLeft hh 6) l < m →
          f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro n
    induction n with
    | zero => intro _ hh hhh; omega
    | succ n ih =>
      intro hn hh hhh l hl hlm
      obtain ⟨h1, h2⟩ := na_bAnd hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hhh with hhh | rfl
      · exact ih h2 hh hhh l hl hlm
      · exact inner _ 64 h1 l hl hlm
  intro i him
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have := outer hi h (i / 64) (by omega) (i % 64) (Nat.mod_lt _ (by norm_num)) (by rw [e]; exact him)
  rwa [e] at this

theorem e3_sound {RT PW E3 : Nat} (h : e3B RT PW E3 = true) :
    ∀ i < 729, bt E3 i = cubeI RT PW i := by
  unfold e3B at h
  intro i hi
  exact brec_eq (allBelow_sound h (by norm_num) i hi)

theorem cubeWt_sound {E3 WT : Nat} (h : cubeWtB E3 WT = true) :
    ∀ i < 729, bt E3 i = true ↔ (l2 WT i 0 = 0 ∨ l2 WT i 1 = 0 ∨ l2 WT i 2 = 0) := by
  unfold cubeWtB at h
  intro i hi
  rw [brec_eq (allBelow_sound h (by norm_num) i hi)]
  simp only [Bool.or_eq_true, Nat.beq_eq, or_assoc]

theorem allLt_sound {b : Nat} : ∀ {l : List Nat}, allLt b l = true → ∀ v ∈ l, v < b
  | [], _, v, hv => absurd hv List.not_mem_nil
  | a :: l, h, v, hv => by
    have h' : (Nat.blt a b && allLt b l) = true := h
    rw [Bool.and_eq_true, Nat.blt_eq] at h'
    rcases List.mem_cons.1 hv with rfl | hv
    · exact h'.1
    · exact allLt_sound h'.2 v hv

theorem decW8_eq (W : Nat) : ∀ L, decW8 W L = (List.range L).map fun k => W / 2 ^ (3 * k) % 8
  | 0 => rfl
  | L + 1 => by
    change decW8 W L ++ [W / 2 ^ (3 * L) % 8] = _
    rw [decW8_eq W L, List.range_succ, List.map_append, List.map_singleton]

theorem enc8_digit : ∀ w : List Nat, (∀ g ∈ w, g < 8) → ∀ k,
    enc8 w / 2 ^ (3 * k) % 8 = w.getD k 0
  | [], _, k => by
    change 0 / 2 ^ (3 * k) % 8 = _
    simp
  | v :: l, h, 0 => by
    have hv := h v List.mem_cons_self
    rw [enc8_cons, Nat.mul_zero, pow_zero, Nat.div_one, List.getD_cons_zero]
    omega
  | v :: l, h, k + 1 => by
    have hv := h v List.mem_cons_self
    have e1 : (v + 8 * enc8 l) / 2 ^ (3 * (k + 1)) = enc8 l / 2 ^ (3 * k) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm (3 * k) 3, pow_add, ← Nat.div_div_eq_div_mul,
        show (2 : Nat) ^ 3 = 8 from rfl]
      congr 1
      omega
    rw [enc8_cons, e1, List.getD_cons_succ]
    exact enc8_digit l (fun g hg => h g (List.mem_cons_of_mem _ hg)) k

theorem decW8_enc8 (w : List Nat) (h : ∀ g ∈ w, g < 8) : decW8 (enc8 w) w.length = w := by
  rw [decW8_eq]
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    rw [List.getElem_map, List.getElem_range, enc8_digit w h k]
    simp [h2]

theorem gw_sound {ws : List (List Nat)} {gw : List (Nat × Nat)} (h : gwB ws gw = true) :
    ∀ g, decW8 (gw.getD g (0, 0)).1 (gw.getD g (0, 0)).2 = ws.getD g [] := by
  induction ws generalizing gw with
  | nil =>
    cases gw with
    | nil =>
      intro g
      simp only [List.getD_nil]
      rfl
    | cons p t => exact absurd (show false = true from h) (by decide)
  | cons w ws ih =>
    cases gw with
    | nil => exact absurd (show false = true from h) (by decide)
    | cons p t =>
      have h' : (Nat.beq (enc8 w) p.1 && Nat.beq (lenR w) p.2 && allLt 8 w && gwB ws t) = true := h
      simp only [Bool.and_eq_true, Nat.beq_eq] at h'
      obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := h'
      intro g
      cases g with
      | zero =>
        simp only [List.getD_cons_zero]
        rw [← e1, ← e2, lenR_eq]
        exact decW8_enc8 w (allLt_sound e3)
      | succ g =>
        simp only [List.getD_cons_succ]
        exact ih (gw := t) e4 g

theorem wt_sound {PW WT wc k : Nat} (h : wtB PW WT wc k = true) :
    ∀ j < 729, l2 WT j k =
      wsum wc (Nat.shiftRight (l32 PW j) 4) (Nat.land (l32 PW j) 15) % 3 := by
  unfold wtB at h
  intro j hj
  exact Nat.eq_of_beq_eq_true (allBelow_sound h (by norm_num) j hj)

@[expose] noncomputable def wsR (wc : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun a _ => a)
    (fun _ ih a c => ih (Nat.add a (Nat.land (Nat.shiftRight wc (Nat.mul 2 (Nat.land c 7))) 3))
      (Nat.shiftRight c 3))

theorem wsR_succ (wc L a c : Nat) : wsR wc (L + 1) a c =
    wsR wc L (Nat.add a (Nat.land (Nat.shiftRight wc (Nat.mul 2 (Nat.land c 7))) 3))
      (Nat.shiftRight c 3) := rfl

theorem wsR_eq (wc : Nat) : ∀ (p : List Nat), (∀ g ∈ p, g < 8) → ∀ a,
    wsR wc p.length a (enc8 p) = a + (p.map fun g => Nat.land (Nat.shiftRight wc (2 * g)) 3).sum
  | [], _, a => rfl
  | g :: p, h, a => by
    have hg := h g List.mem_cons_self
    rw [List.length_cons, wsR_succ, enc8_cons]
    have e1 : Nat.shiftRight (g + 8 * enc8 p) 3 = enc8 p := by
      rw [shiftRight_eq', show (2 : Nat) ^ 3 = 8 from rfl]
      omega
    have e2 : Nat.land (g + 8 * enc8 p) 7 = g := by
      rw [show (7 : Nat) = 2 ^ 3 - 1 from rfl, land_eq', show (2 : Nat) ^ 3 = 8 from rfl]
      omega
    rw [e1, e2]
    have e3 : Nat.add a (Nat.land (Nat.shiftRight wc (Nat.mul 2 g)) 3) =
        a + Nat.land (Nat.shiftRight wc (2 * g)) 3 := rfl
    rw [e3, wsR_eq wc p (fun g hg => h g (List.mem_cons_of_mem _ hg)), List.map_cons,
      List.sum_cons, Nat.add_assoc]

theorem wsum_eq (wc : Nat) (p : List Nat) (hp : ∀ g ∈ p, g < 8) :
    wsum wc (enc8 p) p.length =
      (p.map fun g => Nat.land (Nat.shiftRight wc (2 * g)) 3).sum := by
  have := wsR_eq wc p hp 0
  rw [Nat.zero_add] at this
  exact this

theorem hom_sound {RT WT wc k : Nat} (h : homB RT WT wc k = true) :
    ∀ i < 729, ∀ g < 6, l2 WT (l10 RT (6 * i + g)) k =
      (l2 WT i k + Nat.land (Nat.shiftRight wc (2 * g)) 3) % 3 := by
  unfold homB at h
  intro i hi g hg
  have h1 := Nat.eq_of_beq_eq_true (allBelow_sound h (by norm_num) (6 * i + g) (by omega))
  have e1 : Nat.div (6 * i + g) 6 = i := by
    change (6 * i + g) / 6 = i
    omega
  have e2 : Nat.mod (6 * i + g) 6 = g := by
    change (6 * i + g) % 6 = g
    omega
  rw [e1, e2] at h1
  exact h1

theorem cent_sound {RT PW WT k z : Nat} (h : centB RT PW WT k z = true) :
    ∀ j < 729, l2 WT j k = 0 → commI RT PW z j = true := by
  unfold centB at h
  intro j hj hz
  have hb : Nat.beq (l2 WT j k) 0 = true := by
    rw [Nat.beq_eq]
    exact hz
  exact (brec_true (allBelow_sound h (by norm_num) j hj)).1 hb

theorem rec_sum (G : Nat → Nat) : ∀ k : Nat,
    Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 => Nat.add (G l) ih2) k =
      ((List.range k).map G).sum
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, ← rec_sum G k]
    change G k + _ = _
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem sumBelow_eq (m : Nat) (f : Nat → Nat) : ∀ h : Nat,
    sumBelow m h f = ((List.range (64 * h)).map fun i => if i < m then f i else 0).sum
  | 0 => rfl
  | h + 1 => by
    have htop : ((List.range 64).map fun l =>
        (fun i => Bool.rec (motive := fun _ => Nat) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l)).sum =
        ((List.range 64).map ((fun i => if i < m then f i else 0) ∘ fun x => 64 * h + x)).sum := by
      refine congrArg List.sum (List.map_congr_left fun l _ => ?_)
      have e : Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
        change h <<< 6 + l = 64 * h + l
        rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 6 = 64 from rfl]
        omega
      change Bool.rec (motive := fun _ => Nat) 0 (f (Nat.add (Nat.shiftLeft h 6) l))
        (Nat.blt (Nat.add (Nat.shiftLeft h 6) l) m) = (if 64 * h + l < m then f (64 * h + l) else 0)
      rw [e]
      by_cases hlt : 64 * h + l < m
      · have hb : Nat.blt (64 * h + l) m = true := by rw [Nat.blt_eq]; exact hlt
        rw [hb, if_pos hlt]
      · have hb : Nat.blt (64 * h + l) m = false := by
          cases hc : Nat.blt (64 * h + l) m
          · rfl
          · rw [Nat.blt_eq] at hc
            exact absurd hc hlt
        rw [hb, if_neg hlt]
    change Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      Nat.add ((fun i => Bool.rec (motive := fun _ => Nat) 0 (f i) (Nat.blt i m))
        (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64 + sumBelow m h f = _
    rw [rec_sum, htop, sumBelow_eq m f h, show 64 * (h + 1) = 64 * h + 64 by ring,
      List.range_add, List.map_append, List.sum_append, List.map_map]
    exact Nat.add_comm _ _

theorem sum_ind_eq (p : Nat → Bool) : ∀ n : Nat,
    ((List.range n).map fun i => Bool.rec (motive := fun _ => Nat) 0 1 (p i)).sum =
      ((List.range n).filter p).length
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, List.filter_append,
      List.length_append, sum_ind_eq p n]
    cases h : p n <;> simp [List.filter, h]

theorem cnt_eq (p : Nat → Bool) : cnt p = ((List.range 729).filter p).length := by
  unfold cnt
  rw [sumBelow_eq, show 64 * 12 = 729 + 39 by rfl, List.range_add, List.map_append,
    List.sum_append, List.map_map]
  have h0 : ((List.range 39).map ((fun i => if i < 729 then
      Bool.rec (motive := fun _ => Nat) 0 1 (p i) else 0) ∘ fun x => 729 + x)).sum = 0 := by
    rw [List.sum_eq_zero]
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    simp
  rw [h0, Nat.add_zero, ← sum_ind_eq p 729]
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  rw [if_pos (List.mem_range.1 hi)]

theorem pk_cons (w v : Nat) (l : List Nat) : pk w (v :: l) = v + pk w l * 2 ^ w := by
  change v + pk w l <<< w = _
  rw [Nat.shiftLeft_eq]

theorem pk_lane (w : Nat) : ∀ l : List Nat, (∀ v ∈ l, v < 2 ^ w) → ∀ k,
    pk w l / 2 ^ (w * k) % 2 ^ w = l.getD k 0
  | [], _, k => by
    change 0 / 2 ^ (w * k) % 2 ^ w = _
    simp
  | v :: l, h, 0 => by
    have hv := h v List.mem_cons_self
    rw [pk_cons, Nat.mul_zero, pow_zero, Nat.div_one, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hv, List.getD_cons_zero]
  | v :: l, h, k + 1 => by
    have hv := h v List.mem_cons_self
    rw [pk_cons, Nat.mul_add, Nat.mul_one, pow_add, Nat.mul_comm (2 ^ (w * k)) (2 ^ w),
      ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt hv,
      Nat.zero_add, List.getD_cons_succ]
    exact pk_lane w l (fun u hu => h u (List.mem_cons_of_mem _ hu)) k

theorem bind_sound {w X : Nat} {l : List Nat} (h : bindB w X l = true) :
    ∀ k, Nat.land (Nat.shiftRight X (w * k)) (2 ^ w - 1) = l.getD k 0 := by
  have h' : (Nat.beq (pk w l) X && allLt (2 ^ w) l) = true := h
  rw [Bool.and_eq_true, Nat.beq_eq] at h'
  intro k
  rw [shiftRight_eq', land_eq', ← h'.1]
  exact pk_lane w l (allLt_sound h'.2) k

theorem getD_map_pwOf (ps : List (List Nat)) (j : Nat) :
    (ps.map pwOf).getD j 0 = pwOf (ps.getD j []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ps[j]? <;> rfl

theorem pwList_sound : ∀ ps : List (List Nat), List.rec (motive := fun _ => Bool) true
    (fun p _ ih => Nat.blt (lenR p) 9 && allLt 8 p && ih) ps = true →
    ∀ j, (ps.getD j []).length ≤ 8 ∧ ∀ g ∈ ps.getD j [], g < 8
  | [], _, j => by simp
  | p :: ps, h, j => by
    have h' : (Nat.blt (lenR p) 9 && allLt 8 p && List.rec (motive := fun _ => Bool) true
        (fun p _ ih => Nat.blt (lenR p) 9 && allLt 8 p && ih) ps) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, lenR_eq] at h'
    cases j with
    | zero =>
      rw [List.getD_cons_zero]
      exact ⟨by omega, allLt_sound h'.1.2⟩
    | succ j =>
      rw [List.getD_cons_succ]
      exact pwList_sound ps h'.2 j

theorem pw_sound {PW : Nat} {ps : List (List Nat)} (h : pwB PW ps = true) :
    ∀ j, l32 PW j = pwOf (ps.getD j []) ∧ (ps.getD j []).length ≤ 8 ∧
      ∀ g ∈ ps.getD j [], g < 8 := by
  unfold pwB at h
  rw [Bool.and_eq_true] at h
  intro j
  refine ⟨?_, pwList_sound ps h.2 j⟩
  have e := bind_sound h.1 j
  rw [getD_map_pwOf] at e
  exact e

theorem gen_sound {PW MSP g W L : Nat} (h : genB PW MSP g W L = true) :
    l32 PW (g + 1) = 1 + 16 * g ∧ dataS (lS MSP (g + 1)) = codeBits (decW8 W L) % 2 ^ 2704 := by
  unfold genB at h
  rw [Bool.and_eq_true, Nat.beq_eq, eqS_iff, wordS_data] at h
  exact ⟨h.1, h.2.symm⟩

theorem edge_arith (x q g : Nat) (hl : Nat.land q 15 < 15)
    (hw : x = Nat.add (Nat.succ (Nat.land q 15)) (Nat.shiftLeft (Nat.add (Nat.shiftRight q 4)
        (Nat.shiftLeft g (Nat.mul 3 (Nat.land q 15)))) 4)) :
    Nat.land x 15 = Nat.land q 15 + 1 ∧
      Nat.shiftRight x 4 = Nat.shiftRight q 4 + g * 8 ^ Nat.land q 15 := by
  have e1 : Nat.shiftLeft g (Nat.mul 3 (Nat.land q 15)) = g * 8 ^ Nat.land q 15 := by
    change g <<< (3 * Nat.land q 15) = _
    rw [Nat.shiftLeft_eq, pow_mul]
    norm_num
  have e2 : ∀ a, Nat.shiftLeft a 4 = a * 16 := fun a => by
    change a <<< 4 = _
    rw [Nat.shiftLeft_eq]
  have L15 : ∀ a, Nat.land a 15 = a % 16 := fun a => land_eq' a 4
  have S4 : ∀ a, Nat.shiftRight a 4 = a / 16 := fun a => shiftRight_eq' a 4
  rw [e1, e2] at hw
  generalize g * 8 ^ Nat.land q 15 = G at hw ⊢
  simp only [L15, S4, Nat.add_eq, Nat.succ_eq_add_one] at hl hw ⊢
  subst hw
  constructor <;> omega

theorem land7_lt (y : Nat) : Nat.land y 7 < 8 := by
  rw [show (7 : Nat) = 2 ^ 3 - 1 from rfl, land_eq']
  exact Nat.mod_lt _ (by norm_num)

theorem edge_sound {PW PAR MSP j : Nat} (h : edgeB PW PAR MSP j = true)
    (hl : Nat.land (l32 PW (l10 PAR j)) 15 < 15) :
    ∃ g < 8, l10 PAR j < j ∧
      Nat.land (l32 PW j) 15 = Nat.land (l32 PW (l10 PAR j)) 15 + 1 ∧
      Nat.shiftRight (l32 PW j) 4 = Nat.shiftRight (l32 PW (l10 PAR j)) 4 +
        g * 8 ^ Nat.land (l32 PW (l10 PAR j)) 15 ∧
      dataS (lS MSP j) = mul (dataS (lS MSP (l10 PAR j))) (dataS (lS MSP (g + 1))) % 2 ^ 2704 := by
  unfold edgeB at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, eqS_iff, mulS_data] at h
  obtain ⟨⟨hp, hw⟩, hm⟩ := h
  obtain ⟨a1, a2⟩ := edge_arith _ _ _ hl hw
  exact ⟨Nat.land (Nat.shiftRight (l32 PW j) (Nat.add 4 (Nat.mul 3 (Nat.land (l32 PW (l10 PAR j))
    15)))) 7, land7_lt _, hp, a1, a2, hm.symm⟩

theorem edges_sound {PW PAR MSP lo n : Nat} (h : edgesB PW PAR MSP lo n = true) :
    ∀ k < n, edgeB PW PAR MSP (lo + k) = true := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    obtain ⟨h1, h2⟩ := na_bAnd h
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact ih h2 k hk
    · exact h1

theorem bt_eq (A n : Nat) : bt A n = A.testBit n := by
  rw [Bool.eq_iff_iff, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  unfold bt
  have e : ∀ x, Nat.land x 1 = x % 2 := fun x => land_eq' x 1
  rw [Nat.beq_eq, e, shiftRight_eq']

theorem trS_fold (A : Nat) : ∀ l : List Nat, (∀ p ∈ l, p < 52) →
    trS l A = l.foldr (fun p b => xor ((dataS A).testBit (52 * p + p)) b) false
  | [], _ => rfl
  | p :: l, hl => by
    have hp := hl p List.mem_cons_self
    rw [List.foldr_cons, ← trS_fold A l (fun q hq => hl q (List.mem_cons_of_mem _ hq))]
    change xor (bt A (Nat.add 128 (Nat.mul 53 p))) (trS l A) = _
    unfold dataS
    rw [bt_eq, Nat.testBit_mod_two_pow, decide_eq_true (by omega : 52 * p + p < 2704),
      Bool.true_and, Nat.testBit_div_two_pow]
    congr 2
    change 128 + 53 * p = 52 * p + p + 128
    omega

theorem trS_eq (A : Nat) : trS CFSG.RankThree.PartOne.F106.f4ShortPos A =
    CFSG.RankThree.PartOne.F106.trIB (dataS A) := by
  have hpos : ∀ p ∈ CFSG.RankThree.PartOne.F106.f4ShortPos, p < 52 := by decide
  unfold CFSG.RankThree.PartOne.F106.trIB
  exact trS_fold A _ hpos

theorem tr_sound {MSP TR lo n : Nat}
    (h : trB CFSG.RankThree.PartOne.F106.f4ShortPos MSP TR lo n = true) :
    ∀ k < n, bt TR (lo + k) = trS CFSG.RankThree.PartOne.F106.f4ShortPos (lS MSP (lo + k)) := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    obtain ⟨h1, h2⟩ := na_bAnd h
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact ih h2 k hk
    · exact brec_eq h1

theorem land1_eq (a : Nat) : Nat.land a 1 = a % 2 := land_eq' a 1

theorem conjs_sound (RT PW INV x : Nat) : ∀ us : List Nat,
    (conjsB RT PW INV x us).2.1 = us.length ∧
    (∀ c, (conjsB RT PW INV x us).2.2.testBit c = true ↔
      c ∈ us.map fun u => conjI RT PW INV u x) ∧
    ((conjsB RT PW INV x us).1 = true →
      (∀ u ∈ us, u < 729) ∧ (us.map fun u => conjI RT PW INV u x).Nodup)
  | [] => by
    refine ⟨rfl, fun c => ?_, fun _ => ⟨by simp, by simp⟩⟩
    change Nat.testBit 0 c = true ↔ _
    simp
  | u :: us => by
    obtain ⟨ih1, ih2, ih3⟩ := conjs_sound RT PW INV x us
    have e : conjsB RT PW INV x (u :: us) = ((conjsB RT PW INV x us).1 && Nat.blt u 729 &&
        Nat.beq (Nat.land (Nat.shiftRight (conjsB RT PW INV x us).2.2 (conjI RT PW INV u x)) 1) 0,
        Nat.succ (conjsB RT PW INV x us).2.1,
        Nat.lor (conjsB RT PW INV x us).2.2 (Nat.shiftLeft 1 (conjI RT PW INV u x))) := rfl
    rw [e, List.map_cons, List.length_cons]
    generalize conjsB RT PW INV x us = s at ih1 ih2 ih3 ⊢
    generalize conjI RT PW INV u x = c0
    obtain ⟨b, n, M⟩ := s
    simp only at ih1 ih2 ih3 ⊢
    refine ⟨by rw [ih1], fun c => ?_, fun hb => ?_⟩
    · change (M ||| 1 <<< c0).testBit c = true ↔ _
      rw [Nat.testBit_or, Bool.or_eq_true, ih2, Nat.one_shiftLeft, Nat.testBit_two_pow,
        List.mem_cons, decide_eq_true_eq]
      exact ⟨fun h => h.elim Or.inr (fun e => Or.inl e.symm),
        fun h => h.elim (fun e => Or.inr e.symm) Or.inl⟩
    · rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hb
      obtain ⟨⟨hb1, hu⟩, hbit⟩ := hb
      obtain ⟨hall, hnd⟩ := ih3 hb1
      refine ⟨fun v hv => ?_, List.nodup_cons.2 ⟨fun hmem => ?_, hnd⟩⟩
      · rcases List.mem_cons.1 hv with rfl | hv
        · exact hu
        · exact hall v hv
      · have h1 := (ih2 c0).2 hmem
        rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at h1
        rw [land1_eq, shiftRight_eq', h1] at hbit
        exact absurd hbit (by decide)

theorem wit_sound {RT PW INV : Nat} {r : Nat × List Nat × Nat × Nat}
    (h : witB RT PW INV r = true) :
    r.1 < 729 ∧ (∀ u ∈ r.2.1, u < 729) ∧
      (r.2.1.map fun u => conjI RT PW INV u r.1).Nodup ∧
      (r.2.1.length = 10 ∨ (r.2.1.length = 4 ∧ r.2.2.1 < 729 ∧ r.2.2.2 < 729 ∧
        cubeI RT PW r.2.2.1 = true ∧ cubeI RT PW r.2.2.2 = true ∧
        commI RT PW r.2.2.1 r.1 = true ∧ commI RT PW r.2.2.2 r.1 = true ∧
        commI RT PW r.2.2.1 r.2.2.2 = false)) := by
  unfold witB at h
  obtain ⟨c1, -, c3⟩ := conjs_sound RT PW INV r.1 r.2.1
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq, Bool.not_eq_true',
    and_assoc] at h
  obtain ⟨hx, hc, hor⟩ := h
  obtain ⟨hall, hnd⟩ := c3 hc
  rw [c1] at hor
  exact ⟨hx, hall, hnd, hor⟩

theorem wits_sound {RT PW INV : Nat} {l : List (Nat × List Nat × Nat × Nat)}
    (h : witsB RT PW INV l = true) : ∀ r ∈ l, witB RT PW INV r = true := by
  induction l with
  | nil => intro r hr; exact absurd hr List.not_mem_nil
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := na_bAnd h
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h1
    · exact ih h2 r hr

theorem recMask_sound : ∀ (l : List (Nat × List Nat × Nat × Nat)) (i : Nat),
    (recMask l).testBit i = true → ∃ r ∈ l, r.1 = i
  | [], i, h => by
    have e : recMask [] = 0 := rfl
    rw [e, Nat.zero_testBit] at h
    exact absurd h (by decide)
  | r :: l, i, h => by
    have e : recMask (r :: l) = recMask l ||| 1 <<< r.1 := rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow] at h
    rcases h with h | h
    · obtain ⟨s, hs, e⟩ := recMask_sound l i h
      exact ⟨s, List.mem_cons_of_mem _ hs, e⟩
    · exact ⟨r, List.mem_cons_self, of_decide_eq_true h⟩

theorem cover_sound {E3 WT : Nat} {l : List (Nat × List Nat × Nat × Nat)}
    (h : coverB E3 WT (recMask l) = true) :
    ∀ i < 729, bt E3 i = true → ¬ (l2 WT i 0 = 0 ∧ l2 WT i 3 = 0) → ∃ r ∈ l, r.1 = i := by
  unfold coverB at h
  intro i hi he hne
  have h1 := brec_true (allBelow_sound h (by norm_num) i hi)
  have hc : (bt E3 i && !(Nat.beq (l2 WT i 0) 0 && Nat.beq (l2 WT i 3) 0)) = true := by
    rw [he]
    cases h0 : Nat.beq (l2 WT i 0) 0 <;> cases h3 : Nat.beq (l2 WT i 3) 0 <;> try rfl
    exact absurd ⟨Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h3⟩ hne
  have hb := h1.1 hc
  rw [bt_eq] at hb
  exact recMask_sound l i hb

end CFSG.KC.F4NA

end
