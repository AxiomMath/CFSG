module

public import CFSG.Certificates.Kernel.Fi22Snd.Rows
public import CFSG.Certificates.Kernel.Fi22Snd.Orbit
public import Certificates.Data.Kernel.Fi22Search2071

public section

namespace CFSG.KC.Fi22Snd

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KC.S2071 CFSG.KS CFSG.KS.Raw CFSG.Certificates.Native
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore.Native

private theorem allL_iff {l : List Nat} {f : Nat → Bool} :
    allL l f = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => simp [allL]
  | cons a l ih =>
    have e : allL (a :: l) f = bAnd(f a, allL l f) := rfl
    rw [e, Orb.bAnd_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

private theorem lenL_eq (l : List Nat) : lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : lenL (a :: l) = Nat.add (lenL l) (nat_lit 1) := rfl
    rw [e, ih]
    rfl

private theorem getL_eq (l : List Nat) (i : Nat) : getL l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    have e : getL (a :: l) i = nIf(Nat.beq i (nat_lit 0), a, getL l (Nat.sub i (nat_lit 1))) := rfl
    rw [e]
    cases i with
    | zero => rfl
    | succ i =>
      have hb : Nat.beq (i + 1) (nat_lit 0) = false := rfl
      rw [hb]
      exact (ih i).trans (List.getD_cons_succ).symm

private theorem beq_iff' (a b : Nat) : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

private theorem memL_iff (l : List Nat) (x : Nat) : memL l x = true ↔ x ∈ l := by
  induction l with
  | nil => simp [memL]
  | cons a l ih =>
    have e : memL (a :: l) x = bIf(Nat.beq a x, true, memL l x) := rfl
    rw [e, Orb.bIf_eq, List.mem_cons]
    by_cases h : Nat.beq a x = true
    · rw [if_pos h]
      have := (beq_iff' a x).1 h
      simp [this]
    · rw [if_neg h, ih]
      have : ¬ a = x := fun h' => h ((beq_iff' a x).2 h')
      have h2 : ¬ x = a := fun h' => this h'.symm
      simp [h2]

private theorem eqL_iff (l m : List Nat) : eqL l m = true ↔ l = m := by
  induction l generalizing m with
  | nil =>
    cases m with
    | nil => simp [eqL]
    | cons b m => simp [eqL]
  | cons a l ih =>
    cases m with
    | nil => simp [eqL]
    | cons b m =>
      have e : eqL (a :: l) (b :: m) = bAnd(Nat.beq a b, eqL l m) := rfl
      rw [e, Orb.bAnd_eq, Bool.and_eq_true, ih, beq_iff']
      simp

private theorem repsL_eq (N : SNode) : repsL N = N.kids.map Prod.fst := by
  unfold repsL
  induction N.kids with
  | nil => rfl
  | cons rk ks ih =>
    simp only [List.map_cons]
    rw [← ih]

private theorem land_one (s : Nat) : Nat.land s (nat_lit 1) = s % 2 := Nat.and_one_is_mod s

private theorem base_even (s w : Nat) : (Nat.lor (Nat.sub s (Nat.land s (nat_lit 1)))
    (Nat.shiftLeft (nat_lit 1) (Nat.add w (nat_lit 1)))) % 2 = 0 := by
  rw [land_one]
  change ((s - s % 2) ||| (1 <<< (w + 1))) % 2 = 0
  rw [Nat.one_shiftLeft]
  have h : ((s - s % 2) ||| 2 ^ (w + 1)).testBit 0 = false := by
    rw [Nat.testBit_or, Nat.testBit_zero, Nat.testBit_two_pow]
    have : ¬ (s - s % 2) % 2 = 1 := by omega
    simp [this]
  rw [Nat.testBit_zero] at h
  have : ¬ ((s - s % 2) ||| 2 ^ (w + 1)) % 2 = 1 := by simpa using h
  omega

private theorem succ_bit (s w q : Nat) : (Nat.add (Nat.lor (Nat.sub s (Nat.land s (nat_lit 1)))
    (Nat.shiftLeft (nat_lit 1) (Nat.add w (nat_lit 1)))) (nat_lit 1)).testBit (q + 1) =
      (s.testBit (q + 1) || decide (w = q)) := by
  have he := base_even s w
  have hX : Nat.lor (Nat.sub s (Nat.land s (nat_lit 1)))
      (Nat.shiftLeft (nat_lit 1) (Nat.add w (nat_lit 1))) = (s - s % 2) ||| 2 ^ (w + 1) := by
    rw [land_one]
    change (s - s % 2) ||| (1 <<< (w + 1)) = _
    rw [Nat.one_shiftLeft]
  rw [hX] at he ⊢
  change (((s - s % 2) ||| 2 ^ (w + 1)) + 1).testBit (q + 1) = _
  have h1 : (s - s % 2).testBit (q + 1) = s.testBit (q + 1) := by
    rw [Nat.testBit_add_one, Nat.testBit_add_one s, show (s - s % 2) / 2 = s / 2 by omega]
  rw [Nat.testBit_add_one, show (((s - s % 2) ||| 2 ^ (w + 1)) + 1) / 2 =
    ((s - s % 2) ||| 2 ^ (w + 1)) / 2 by omega, ← Nat.testBit_add_one, Nat.testBit_or, h1,
    Nat.testBit_two_pow]
  simp [eq_comm]

private def Good (M : Nat → Prop) (s : Nat) : Prop :=
  s % 2 = 1 → ∀ q, s.testBit (q + 1) = true → M q

private theorem good_of_even {M : Nat → Prop} {x : Nat} (h : x % 2 = 0) : Good M x := by
  intro h1
  omega

private theorem good_one {M : Nat → Prop} {s w : Nat} (hs : Good M s) (hodd : s % 2 = 1)
    (hw : M w) : Good M (Nat.add (Nat.lor (Nat.sub s (Nat.land s (nat_lit 1)))
      (Nat.shiftLeft (nat_lit 1) (Nat.add w (nat_lit 1)))) (nat_lit 1)) := by
  intro _ q hq
  rw [succ_bit] at hq
  rcases Bool.or_eq_true_iff.1 hq with h | h
  · exact hs hodd q h
  · exact (of_decide_eq_true h) ▸ hw

private theorem recStep_good {n : Nat} {PL : Nat → Nat} {N : SNode} {M : Nat → Prop}
    (hR : ∀ r ∈ N.kids.map Prod.fst, r < n → M r)
    (hC : ∀ x g, M x → g < N.pool.length → pg 12 4095 (PL (N.pool.getD g 0)) x < n →
      M (pg 12 4095 (PL (N.pool.getD g 0)) x))
    (e s : Nat) (hs : Good M s) : Good M (recStep n PL N e s) := by
  unfold recStep
  simp only [CFSG.KC.Pack.strictN_eq]
  generalize fld(e, nat_lit 0, nat_lit 65535) = w
  generalize fld(e, nat_lit 16, nat_lit 65535) = p
  generalize fld(e, nat_lit 32, nat_lit 65535) = g
  generalize fld(e, nat_lit 48, nat_lit 1) = f
  simp only [Orb.nIf_eq]
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  all_goals try exact good_of_even (base_even s w)
  · have hodd : s % 2 = 1 := by rw [← land_one]; exact Nat.eq_of_beq_eq_true h1
    have hw : w < n := Nat.le_of_ble_eq_true h2
    refine good_one hs hodd (hR w ?_ hw)
    rw [← repsL_eq]
    exact (memL_iff _ _).1 h4
  · have hodd : s % 2 = 1 := by rw [← land_one]; exact Nat.eq_of_beq_eq_true h1
    have hw : w < n := Nat.le_of_ble_eq_true h2
    have hp : s.testBit (p + 1) = true := by rw [← beq_bit]; exact h5
    have hg : g < N.pool.length := by rw [← lenL_eq]; exact Nat.le_of_ble_eq_true h6
    have hpg : pg 12 4095 (PL (N.pool.getD g 0)) p = w := by
      rw [← getL_eq]; exact Nat.eq_of_beq_eq_true h7
    refine good_one hs hodd ?_
    rw [← hpg]
    exact hC p g (hs hodd p hp) hg (hpg ▸ hw)

private theorem foldr_good {n : Nat} {PL : Nat → Nat} {N : SNode} {M : Nat → Prop}
    (hR : ∀ r ∈ N.kids.map Prod.fst, r < n → M r)
    (hC : ∀ x g, M x → g < N.pool.length → pg 12 4095 (PL (N.pool.getD g 0)) x < n →
      M (pg 12 4095 (PL (N.pool.getD g 0)) x))
    (E : Nat → Nat) (l : List Nat) (s : Nat) (hs : Good M s) :
    Good M (l.foldr (fun i s => recStep n PL N (E i) s) s) := by
  induction l with
  | nil => exact hs
  | cons a l ih => exact recStep_good hR hC (E a) _ ih

private theorem good_one_state (M : Nat → Prop) : Good M 1 := by
  intro _ q hq
  rw [Nat.testBit_add_one] at hq
  simp at hq

private theorem recMask_good {n : Nat} {PL : Nat → Nat} {N : SNode} {M : Nat → Prop}
    (hR : ∀ r ∈ N.kids.map Prod.fst, r < n → M r)
    (hC : ∀ x g, M x → g < N.pool.length → pg 12 4095 (PL (N.pool.getD g 0)) x < n →
      M (pg 12 4095 (PL (N.pool.getD g 0)) x))
    (D : Nat) : Good M (recMask n PL N D) := by
  unfold recMask
  rw [CFSG.KC.Pack.strictN_eq, CFSG.KC.Pack.foldN_eq]
  exact foldr_good hR hC (fun i => wd D (Nat.sub (wd D 0) i)) _ _ (good_one_state M)

private theorem kidsOK_iff {nodes : Array SNode} {N : SNode} :
    kidsOK nodes N = true ↔
      ∀ rk ∈ N.kids, rk.2 < nodes.size ∧ (nodes[rk.2]!).pre = N.pre ++ [rk.1] := by
  unfold kidsOK
  induction N.kids with
  | nil => simp
  | cons rk ks ih =>
    dsimp only
    rw [Orb.bAnd_eq, Bool.and_eq_true, Orb.bAnd_eq, Bool.and_eq_true, ih, eqL_iff,
      List.forall_mem_cons, Nat.blt_eq, and_assoc]

private theorem nodeGens_get (pool : Array (Array Nat)) (N : SNode) {g : Nat}
    (hg : g < N.pool.length) : (nodeGens pool N)[g]! = pool[N.pool.getD g 0]! := by
  unfold nodeGens
  rw [getElem!_pos _ _ (by simpa using hg)]
  simp [List.getElem?_eq_getElem hg]

private theorem nodeGens_size (pool : Array (Array Nat)) (N : SNode) :
    (nodeGens pool N).size = N.pool.length := by
  simp [nodeGens]

theorem branchOK_of_branchK {n np k col D T : Nat} {S PL : Nat → Nat} {nodes : Array SNode}
    {N : SNode} {pool : Array (Array Nat)} {c : Array Nat}
    (hpool : pool.size = np) (hPL : ∀ j < np, pool[j]! = unpack n 12 (PL j))
    (hpreN : ∀ x ∈ N.pre, x < n)
    (hc : ∀ w < n, cget (colourK n S T N.pre k) w = c[w]!)
    (h : branchK n S T PL np nodes k col D N = true) :
    branchOK n pool nodes c col N = true := by
  unfold branchK at h
  obtain ⟨h1, h'⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h2, h'⟩ := CFSG.KC.Pack.band_iff.1 h'
  obtain ⟨h3, h'⟩ := CFSG.KC.Pack.band_iff.1 h'
  obtain ⟨h4, h5⟩ := CFSG.KC.Pack.band_iff.1 h'
  rw [CFSG.KC.Pack.strictB_eq] at h5
  obtain ⟨h5a, h5b⟩ := CFSG.KC.Pack.band_iff.1 h5
  rw [CFSG.KC.Pack.strictB_eq] at h5b
  have h5c := CFSG.KC.Pack.allN_spec h5b
  have hout : N.out = 0 := Nat.eq_of_beq_eq_true h1
  have hpoolLt : ∀ j ∈ N.pool, j < np := fun j hj => Nat.le_of_ble_eq_true ((allL_iff.1 h2) j hj)
  have hfix : ∀ j ∈ N.pool, ∀ x ∈ N.pre, pg 12 4095 (PL j) x = x := fun j hj x hx =>
    Nat.eq_of_beq_eq_true (allL_iff.1 ((allL_iff.1 h3) j hj) x hx)
  have hkids := kidsOK_iff.1 h4
  have hodd : (recMask n PL N D) % 2 = 1 := by
    rw [← land_one]
    exact Nat.eq_of_beq_eq_true h5a
  have hbit : ∀ w < n, cget (colourK n S T N.pre k) w = col →
      (recMask n PL N D).testBit (w + 1) = true := by
    intro w hw hcw
    have h6 := h5c w hw
    have hb : Nat.beq (cget (colourK n S T N.pre k) w) col = true := by
      rw [hcw]
      exact Nat.beq_refl col
    rw [hb] at h6
    rw [← beq_bit]
    exact h6
  set gens := nodeGens pool N with hgens
  set reps := N.kids.map Prod.fst
  set oc := orbitCert n gens reps
  have hgen_eq : ∀ g, g < N.pool.length → ∀ x < n,
      (gens[g]!)[x]! = pg 12 4095 (PL (N.pool.getD g 0)) x := by
    intro g hg x hx
    rw [hgens, nodeGens_get pool N hg]
    have hmem : N.pool.getD g 0 ∈ N.pool := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg]
      exact List.getElem_mem hg
    rw [hPL _ (hpoolLt _ hmem), unpack12_get hx]
  have hinv : Good (fun q => q < n ∧ (oc[q]!).1 ≠ 0) (recMask n PL N D) := by
    refine recMask_good ?_ ?_ D
    · intro r hr hrn
      exact ⟨hrn, orbitCert_rep hr hrn⟩
    · rintro x g ⟨hx, hxm⟩ hg hy
      have e := hgen_eq g hg x hx
      rw [← e] at hy ⊢
      exact ⟨hy, orbitCert_closed hx hxm (by rw [hgens, nodeGens_size]; exact hg) hy⟩
  have hmark : ∀ w < n, c[w]! = col → (oc[w]!).1 ≠ 0 := by
    intro w hw hcw
    exact (hinv hodd w (hbit w hw ((hc w hw).trans hcw))).2
  unfold branchOK
  dsimp only
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact beq_iff_eq.2 hout
  · exact beq_iff_eq.2 (orbitCert_size n gens reps)
  · rw [List.all_eq_true]
    intro j hj
    exact decide_eq_true (by rw [hpool]; exact hpoolLt j hj)
  · rw [Array.all_eq_true_iff_forall_mem]
    intro g hg
    rw [nodeGens, List.mem_toArray, List.mem_map] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    rw [List.all_eq_true]
    intro x hx
    rw [hPL j (hpoolLt j hj), unpack12_get (hpreN x hx), hfix j hj x hx]
    exact beq_self_eq_true x
  · rw [List.all_eq_true]
    intro rk hrk
    obtain ⟨h7, h8⟩ := hkids rk hrk
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨h7, h8⟩
  · exact (CFSG.Monster.B.Co2.allLt_iff).2 (orbitCert_recOK n gens reps)
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro w hw
    by_cases hcw : c[w]! = col
    · have hm := hmark w hw hcw
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq]
      exact Or.inr hm
    · simp [hcw]

private theorem surj_of_inj {n : Nat} {a : Nat → Nat} (hlt : ∀ v < n, a v < n)
    (hinj : ∀ v < n, ∀ w < n, a v = a w → v = w) : ∀ x < n, ∃ v < n, a v = x := by
  have hsub : (Finset.range n).image a ⊆ Finset.range n := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_range.2 (hlt v (Finset.mem_range.1 hv))
  have hcard : ((Finset.range n).image a).card = (Finset.range n).card :=
    Finset.card_image_of_injOn fun v hv w hw e =>
      hinj v (Finset.mem_range.1 hv) w (Finset.mem_range.1 hw) e
  have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  intro x hx
  have hmem : x ∈ (Finset.range n).image a := by
    rw [heq]
    exact Finset.mem_range.2 hx
  obtain ⟨v, hv, hvx⟩ := Finset.mem_image.1 hmem
  exact ⟨v, Finset.mem_range.1 hv, hvx⟩

theorem leafOK_of_leafK {n na k D T : Nat} {S AC : Nat → Nat} {base : List Nat} {N : SNode}
    {nbr : Array (List Nat)} {t : Array Nat} {acc : Array (Array Nat)} {c src : Array Nat}
    (hacc : acc.size = na) (hAC : ∀ i < na, acc[i]! = unpack n 12 (AC i))
    (hc : ∀ w < n, cget (colourK n S T N.pre k) w = c[w]!)
    (hs : ∀ w < n, cget (colourK n S T base k) w = src[w]!)
    (hinj : ∀ v < n, ∀ w < n, src[v]! = src[w]! → v = w)
    (h : leafK n S T AC na base k D N = true) :
    leafOK n nbr t acc c src N = true := by
  unfold leafK at h
  simp only [CFSG.KC.Pack.strictB_eq] at h
  rw [Orb.bIf_eq] at h
  by_cases ho : Nat.beq N.out 1 = true
  · rw [if_pos ho] at h
    obtain ⟨hh1, hh2⟩ := CFSG.KC.Pack.band_iff.1 h
    have hout : N.out = 1 := Nat.eq_of_beq_eq_true ho
    have hnacc : N.acc < na := Nat.le_of_ble_eq_true hh1
    have hall := CFSG.KC.Pack.allN_spec hh2
    obtain ⟨a, hadef⟩ : ∃ a : Nat → Nat, ∀ v, a v = pg 12 4095 (AC N.acc) v := ⟨_, fun _ => rfl⟩
    have ha : ∀ v < n, a v < n ∧
        cget (colourK n S T N.pre k) (a v) = cget (colourK n S T base k) v := by
      intro v hv
      obtain ⟨h1, h2⟩ := CFSG.KC.Pack.band_iff.1 (hall v hv)
      rw [hadef]
      exact ⟨Nat.le_of_ble_eq_true h1, Nat.eq_of_beq_eq_true h2⟩
    have hca : ∀ v < n, c[a v]! = src[v]! := by
      intro v hv
      rw [← hc _ (ha v hv).1, (ha v hv).2, hs v hv]
    have hainj : ∀ v < n, ∀ w < n, a v = a w → v = w := by
      intro v hv w hw e
      exact hinj v hv w hw (by rw [← hca v hv, ← hca w hw, e])
    have hsurj := surj_of_inj (fun v hv => (ha v hv).1) hainj
    have hcinj : ∀ x < n, ∀ y < n, c[x]! = c[y]! → x = y := by
      intro x hx y hy e
      obtain ⟨v, hv, rfl⟩ := hsurj x hx
      obtain ⟨u, hu, rfl⟩ := hsurj y hy
      rw [hca v hv, hca u hu] at e
      rw [hinj v hv u hu e]
    have hfull : ∀ v < n, (colMatch n c src)[v]! < n ∧ c[(colMatch n c src)[v]!]! = src[v]! :=
      fun v hv => colMatch_lt hv ⟨a v, (ha v hv).1, hca v hv⟩
    have hAcc : N.acc < acc.size := by rw [hacc]; exact hnacc
    unfold leafOK
    dsimp only
    rw [if_pos (beq_iff_eq.2 hout)]
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [CFSG.Monster.B.Co2.allLt_iff]
      intro v hv
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact hfull v hv
    · exact decide_eq_true hAcc
    · unfold eqA
      rw [CFSG.Monster.B.Co2.allLt_iff]
      intro i hi
      rw [beq_iff_eq, hAC N.acc hnacc, unpack12_get hi, ← hadef]
      exact hcinj _ (hfull i hi).1 _ (ha i hi).1 (by rw [(hfull i hi).2, hca i hi])
  · rw [if_neg ho] at h
    obtain ⟨hh1, hh2⟩ := CFSG.KC.Pack.band_iff.1 h
    have hout : N.out = 2 := Nat.eq_of_beq_eq_true hh1
    obtain ⟨hh3, hh4⟩ := CFSG.KC.Pack.band_iff.1 hh2
    have hv0 : wd D 1 < n := Nat.le_of_ble_eq_true hh3
    have hall := CFSG.KC.Pack.allN_spec hh4
    have hmiss : ∀ w < n, c[w]! ≠ src[wd D 1]! := by
      intro w hw e
      have h6 : ((cget (colourK n S T N.pre k) w).beq
          (cget (colourK n S T base k) (wd D 1))) = false := by simpa using hall w hw
      exact Nat.ne_of_beq_eq_false h6 (by rw [hc w hw, hs _ hv0]; exact e)
    have hA0 : (colMatch n c src)[wd D 1]! = n := colMatch_eq_n hv0 hmiss
    unfold leafOK
    dsimp only
    have hfull_false : ¬ (allLt n fun v => decide ((colMatch n c src)[v]! < n) &&
        c[(colMatch n c src)[v]!]! == src[v]!) = true := by
      intro hf
      have hv := (CFSG.Monster.B.Co2.allLt_iff).1 hf (wd D 1) hv0
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
      rw [hA0] at hv
      exact Nat.lt_irrefl n hv.1
    have hn1 : ¬ (N.out == 1) = true := by
      rw [hout]
      decide
    have hn2 : (N.out == 2) = true := beq_iff_eq.2 hout
    rw [if_neg hn1, if_pos hn2, if_neg hfull_false]
    have hms : ∃ v < n, missSearch n (colMatch n c src) = v ∧ n ≤ (colMatch n c src)[v]! := by
      unfold missSearch
      cases hfind : (List.range n).find? (fun v => decide (n ≤ (colMatch n c src)[v]!)) with
      | none =>
        exfalso
        rw [List.find?_eq_none] at hfind
        exact hfind (wd D 1) (List.mem_range.2 hv0) (by simp [hA0])
      | some v =>
        refine ⟨v, List.mem_range.1 (List.mem_of_find?_eq_some hfind), rfl, ?_⟩
        simpa using List.find?_some hfind
    obtain ⟨v, hv, hmv, hnv⟩ := hms
    rw [hmv]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hv, ?_⟩
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro w hw
    simp only [bne_iff_ne, ne_eq]
    intro e
    have hlt := (colMatch_lt hv ⟨w, hw, e⟩).1
    omega

end CFSG.KC.Fi22Snd

end
