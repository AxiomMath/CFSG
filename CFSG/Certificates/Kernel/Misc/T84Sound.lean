module

public import Certificates.Data.Kernel.Misc.T84K
public import Certificates.Data.T84P
public import CFSG.Certificates.Kernel.Misc.GL4EltSound
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.Misc.T84

open Matrix CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.GL4 CFSG.KC.Misc.GLM.Pf
open Certificates.A5GL42 (Mat4 Vec4 ofCode vecOfCode)
open Certificates.Asc82NormA6 (rhoCode codesS0)
open Certificates.T84P

@[expose] def colE (v : Vec4) : Mat4 := Matrix.of fun i j => if j = 0 then v i else 0

@[expose] def enc (x : Elt) : ℕ := code4 (colE x.1) + 65536 * code4 x.2

theorem colE_add (v w : Vec4) : colE (v + w) = colE v + colE w := by
  ext i j
  by_cases hj : j = 0 <;> simp [colE, hj]

theorem mul_colE (A : Mat4) (v : Vec4) : A * colE v = colE (A *ᵥ v) := by
  ext i j
  by_cases hj : j = 0
  · simp [colE, Matrix.mul_apply, Matrix.mulVec, dotProduct, hj]
  · simp [colE, Matrix.mul_apply, hj]

theorem colE_inj {v w : Vec4} (h : colE v = colE w) : v = w := by
  funext i
  have := congrFun (congrFun h i) 0
  simpa [colE] using this

theorem colC_ofCodeE : ∀ u < 16, ofCode (colC u) = colE (vecOfCode u) := by
  unfold colE
  decide +kernel

theorem ofCode_xor (a b : ℕ) : ofCode (a ^^^ b) = ofCode a + ofCode b := by
  ext i j
  apply zb_inj
  rw [zb_ofCode, Nat.testBit_xor, Matrix.add_apply, zb_add, zb_ofCode, zb_ofCode]

theorem code4_add (A B : Mat4) : code4 (A + B) = code4 A ^^^ code4 B := by
  have h := code4_ofCode (Nat.xor_lt_two_pow (n := 16) (code4_lt A) (code4_lt B))
  rw [ofCode_xor, ofCode_code4, ofCode_code4] at h
  exact h

theorem p16 : (2 : ℕ) ^ 16 = 65536 := by norm_num

theorem enc_lo (x : Elt) : Nat.land (enc x) (nat_lit 65535) = code4 (colE x.1) := by
  have h := code4_lt (colE x.1)
  have e : Nat.land (enc x) (nat_lit 65535) = enc x % 2 ^ 16 := Nat.and_two_pow_sub_one_eq_mod _ 16
  rw [e, p16]
  unfold enc
  omega

theorem enc_hi (x : Elt) : Nat.shiftRight (enc x) (nat_lit 16) = code4 x.2 := by
  have h := code4_lt (colE x.1)
  have e : Nat.shiftRight (enc x) (nat_lit 16) = enc x / 2 ^ 16 := Nat.shiftRight_eq_div_pow _ _
  rw [e, p16]
  unfold enc
  omega

theorem hiT_enc (x : Elt) : hiT (enc x) = code4 x.2 := enc_hi x

theorem enc_mulE (x y : Elt) : enc (mulE x y) = mulT (enc x) (enc y) := by
  unfold mulT
  simp only [letN_eq]
  rw [enc_hi, enc_lo, enc_lo, enc_hi]
  have e : enc (mulE x y) = code4 (colE (x.1 + x.2 *ᵥ y.1)) + 65536 * code4 (x.2 * y.2) := by
    unfold enc mulE
    dsimp only
  rw [e, colE_add, code4_add, ← mul_colE, code4_mul, code4_mul]
  rfl

theorem enc_one : enc oneE = oneT := by
  have h0 : colE (0 : Vec4) = 0 := by
    ext i j
    simp [colE]
  have h1 : code4 (0 : Mat4) = 0 := by simp [code4]
  have e : enc oneE = code4 (colE 0) + 65536 * code4 1 := by
    unfold enc oneE
    dsimp only
  rw [e, h0, h1, code4_one]
  norm_num [id4, oneT]

theorem enc_inj {x y : Elt} (h : enc x = enc y) : x = y := by
  have hv : code4 (colE x.1) = code4 (colE y.1) := by rw [← enc_lo, ← enc_lo, h]
  have hm : code4 x.2 = code4 y.2 := by rw [← enc_hi, ← enc_hi, h]
  refine Prod.ext (colE_inj ?_) ?_
  · rw [← ofCode_code4 (colE x.1), hv, ofCode_code4]
  · rw [← ofCode_code4 x.2, hm, ofCode_code4]

theorem enc_injective : Function.Injective enc := fun _ _ h => enc_inj h

theorem enc_eq_iff {x y : Elt} : enc x = enc y ↔ x = y := ⟨enc_inj, congrArg enc⟩

theorem code4_colC {u : ℕ} (hu : u < 16) : code4 (colE (vecOfCode u)) = colC u := by
  rw [← colC_ofCodeE u hu, code4_ofCode (colC_lt u hu)]

theorem mkT_eq {u c : ℕ} (hu : u < 16) (hc : c < 65536) :
    mkT u c = enc (vecOfCode u, ofCode c) := by
  have e : enc (vecOfCode u, ofCode c) = code4 (colE (vecOfCode u)) + 65536 * code4 (ofCode c) := by
    unfold enc
    dsimp only
  rw [e, code4_colC hu, code4_ofCode hc]
  rfl

theorem commT_iff (x y : Elt) : commT (enc x) (enc y) = true ↔ commE x y := by
  unfold commT commE
  rw [beq_iff, ← enc_mulE, ← enc_mulE]
  exact enc_eq_iff

theorem mulT_one_iff (x y : Elt) : mulT (enc x) (enc y) = oneT ↔ mulE x y = oneE := by
  rw [← enc_mulE, ← enc_one]
  exact enc_eq_iff

theorem isInvT_iff (x : Elt) : isInvT (enc x) = true ↔ IsInvE x := by
  unfold isInvT IsInvE
  rw [andB_iff, notB_iff, beq_iff, beq_iff, mulT_one_iff, ← enc_one, enc_eq_iff]

theorem isInvT_enc (x : Elt) : isInvT (enc x) = decide (IsInvE x) := by
  rw [Bool.eq_iff_iff, isInvT_iff, decide_eq_true_iff]

theorem nodupN_iff (l : List ℕ) : nodupN l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [nodupN]
  | cons z t ih =>
    change andB (notB (memN z t)) (nodupN t) = true ↔ _
    rw [andB_iff, notB_iff, memN_iff', ih, List.nodup_cons]

theorem lenN_eq (l : List ℕ) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    change Nat.succ (lenN t) = _
    simp only [ih, List.length_cons, Nat.succ_eq_add_one]

theorem dedupN_eq (l : List ℕ) : dedupN l = l.dedup := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    change Bool.rec (motive := fun _ => List ℕ) (x :: dedupN t) (dedupN t) (memN x t) = _
    by_cases h : x ∈ t
    · have h1 : memN x t = true := (memN_iff' x t).2 h
      simp only [h1, List.dedup_cons_of_mem h, ih]
    · have h' : memN x t = false := by
        cases e : memN x t
        · rfl
        · exact absurd ((memN_iff' x t).1 e) h
      simp only [h', List.dedup_cons_of_notMem h, ih]

theorem cntIn_eq (l A : List ℕ) : cntIn l A = (l.filter fun x => decide (x ∈ A)).length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    change Bool.rec (motive := fun _ => ℕ) (cntIn t A) (Nat.succ (cntIn t A)) (memN x A) = _
    by_cases h : x ∈ A
    · have h1 : memN x A = true := (memN_iff' x A).2 h
      have e : (x :: t).filter (fun y => decide (y ∈ A)) =
          x :: t.filter (fun y => decide (y ∈ A)) := List.filter_cons_of_pos (by simpa using h)
      simp only [h1, e, List.length_cons, ih, Nat.succ_eq_add_one]
    · have h' : memN x A = false := by
        cases e : memN x A
        · rfl
        · exact absurd ((memN_iff' x A).1 e) h
      have e : (x :: t).filter (fun y => decide (y ∈ A)) =
          t.filter (fun y => decide (y ∈ A)) := List.filter_cons_of_neg (by simpa using h)
      simp only [h', e, ih]

theorem lAt_mem : ∀ (l : List ℕ) (i : ℕ), i < l.length → lAt l i ∈ l
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | x :: t, 0, _ => by
    change x ∈ x :: t
    simp
  | y :: t, i + 1, h => by
    change lAt t i ∈ y :: t
    exact List.mem_cons_of_mem _ (lAt_mem t i (by simpa using h))

theorem mem_iff {L : List Elt} {K : List ℕ} (h : L.map enc = K) {x : Elt} :
    x ∈ L ↔ enc x ∈ K := by
  rw [← h, List.mem_map]
  exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, e⟩ => enc_inj e ▸ hy⟩

theorem nodup_iff {L : List Elt} {K : List ℕ} (h : L.map enc = K) : L.Nodup ↔ K.Nodup := by
  rw [← h]
  exact ⟨fun hn => hn.map enc_injective, fun hn => hn.of_map enc⟩

theorem length_eq {L : List Elt} {K : List ℕ} (h : L.map enc = K) : L.length = K.length := by
  rw [← h, List.length_map]

theorem exists_of_mem {L : List Elt} {K : List ℕ} (h : L.map enc = K) {k : ℕ} (hk : k ∈ K) :
    ∃ x ∈ L, enc x = k := by
  rw [← h, List.mem_map] at hk
  exact hk

theorem allL_of {L : List Elt} {K : List ℕ} (h : L.map enc = K) {f : ℕ → Bool}
    (hf : allL K f = true) : ∀ x ∈ L, f (enc x) = true :=
  fun x hx => (allL_iff _ _).1 hf _ ((mem_iff h).1 hx)

theorem allL_mk {L : List Elt} {K : List ℕ} (h : L.map enc = K) {f : ℕ → Bool}
    (hf : ∀ x ∈ L, f (enc x) = true) : allL K f = true := by
  rw [allL_iff]
  intro k hk
  obtain ⟨x, hx, rfl⟩ := exists_of_mem h hk
  exact hf x hx

@[expose] def grid (C : List ℕ) : List Elt :=
  (List.range 16).flatMap fun v => C.map fun c => (vecOfCode v, ofCode c)

theorem mem_grid {C : List ℕ} (hC : ∀ c ∈ C, c < 65536) {x : Elt} :
    x ∈ grid C ↔ code4 x.2 ∈ C := by
  unfold grid
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨v, _, c, hc, rfl⟩
    change code4 (ofCode c) ∈ C
    rwa [code4_ofCode (hC c hc)]
  · intro hx
    obtain ⟨u, hu, hv⟩ := vec_surj x.1
    exact ⟨u, hu, code4 x.2, hx, Prod.ext hv (ofCode_code4 x.2)⟩

theorem map_row {u : ℕ} (hu : u < 16) : ∀ C : List ℕ, (∀ c ∈ C, c < 65536) →
    (C.map fun c => (vecOfCode u, ofCode c)).map enc = C.map (mkT u)
  | [], _ => rfl
  | c :: t, hC => by
    rw [List.map_cons, List.map_cons, List.map_cons,
      map_row hu t fun c' hc' => hC c' (List.mem_cons_of_mem _ hc'),
      mkT_eq hu (hC c (by simp))]

theorem map_rows (C : List ℕ) (hC : ∀ c ∈ C, c < 65536) : ∀ R : List ℕ, (∀ u ∈ R, u < 16) →
    (R.flatMap fun v => C.map fun c => (vecOfCode v, ofCode c)).map enc =
      R.flatMap fun u => C.map (mkT u)
  | [], _ => rfl
  | u :: t, hR => by
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append,
      map_row (hR u (by simp)) C hC,
      map_rows C hC t fun u' hu' => hR u' (List.mem_cons_of_mem _ hu')]

theorem map_grid {C : List ℕ} (hC : ∀ c ∈ C, c < 65536) :
    (grid C).map enc = (List.range 16).flatMap fun u => C.map (mkT u) :=
  map_rows C hC _ fun _ hu => List.mem_range.1 hu

theorem D0c_lt : ∀ c ∈ D0c, c < 65536 := by decide +kernel

theorem S0L_lt : ∀ c ∈ S0L, c < 65536 := by decide +kernel

theorem F0m_lt : ∀ c ∈ F0m, c < 65536 := by decide +kernel

theorem id4_lt : id4 < 65536 := by decide +kernel

section Data

variable (hd0 : ((List.range 4).flatMap fun i => (List.range 2).map fun j =>
    rhoCode (g1 ^ i * g2 ^ j)) = D0c)
variable (hs0 : ((Finset.univ.filter fun a : Equiv.Perm (Fin 6) => a.sign = 1).image
    rhoCode) = S0L.toFinset)

include hd0 in
theorem P0l_eq : P0l = grid D0c := by
  have e : D0l = D0c.map ofCode := by
    rw [← hd0, List.map_flatMap]
    unfold D0l
    simp only [List.map_map]
    rfl
  unfold P0l grid
  rw [e]
  simp only [List.map_map]
  rfl

include hd0 in
theorem P0l_map : P0l.map enc = P0K := by
  rw [P0l_eq hd0, map_grid D0c_lt]
  rfl

include hd0 in
theorem memP_iff (x : Elt) : memP (enc x) = true ↔ x ∈ P0l := by
  unfold memP
  rw [memN_iff', hiT_enc, P0l_eq hd0, mem_grid D0c_lt]

include hs0 in
theorem mem_codesS0_iff (k : ℕ) : k ∈ codesS0 ↔ k ∈ S0L := by
  have h := Finset.ext_iff.1 hs0 k
  rw [List.mem_toFinset] at h
  rw [← h]
  simp [codesS0, Finset.mem_sort]

include hs0 in
theorem mem_M0l (x : Elt) : x ∈ M0l ↔ code4 x.2 ∈ S0L := by
  have e : M0l = grid codesS0 := rfl
  rw [e, mem_grid fun c hc => S0L_lt c ((mem_codesS0_iff hs0 c).1 hc), mem_codesS0_iff hs0]

theorem M0K_eq : (grid S0L).map enc = M0K := by
  rw [map_grid S0L_lt]
  rfl

@[expose] noncomputable def IMl : List Elt := (grid S0L).filter fun x => decide (IsInvE x)

theorem map_filter_inv {L : List Elt} {K : List ℕ} (h : L.map enc = K) :
    (L.filter fun x => decide (IsInvE x)).map enc = K.filter isInvT := by
  rw [← h, List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  rw [Function.comp_apply, isInvT_enc]

theorem IMl_map : IMl.map enc = IMK := by
  rw [IMl, map_filter_inv M0K_eq]
  rfl

include hs0 in
theorem mem_InvM_iff (x : Elt) : x ∈ InvM ↔ x ∈ IMl := by
  unfold InvM IMl
  rw [List.mem_filter, List.mem_filter, mem_M0l hs0, mem_grid S0L_lt]

include hd0 in
theorem InvP_map : InvP.map enc = IPK := by
  unfold InvP
  rw [map_filter_inv (P0l_map hd0)]
  rfl

end Data

theorem Vl_map : Vl.map enc = VK := by
  unfold Vl VK
  rw [List.map_map]
  apply List.map_congr_left
  intro u hu
  rw [Function.comp_apply, mkT_eq (List.mem_range.1 hu) id4_lt, ofCode_id4]

theorem span_step (s : List Elt) (b : Elt) :
    (s ++ s.map (mulE b)).map enc = s.map enc ++ (s.map enc).map (mulT (enc b)) := by
  simp only [List.map_append, List.map_map, Function.comp_def, enc_mulE]

theorem span4_map (a b c d : Elt) :
    (span4 a b c d).map enc = span4T (enc a) (enc b) (enc c) (enc d) := by
  dsimp only [span4, span4T]
  rw [span_step, span_step, span_step, List.map_cons, List.map_cons, List.map_nil, enc_one]

theorem F0l_eq : F0l = span4 (vecOfCode 0, ofCode 32475) (vecOfCode 0, ofCode 8580)
    (vecOfCode 5, ofCode id4) (vecOfCode 10, ofCode id4) := by
  rw [ofCode_id4]
  rfl

theorem F0l_map : F0l.map enc = F0K := by
  rw [F0l_eq, span4_map]
  unfold F0K
  rw [mkT_eq (u := 0) (c := 32475) (by norm_num) (by norm_num),
    mkT_eq (u := 0) (c := 8580) (by norm_num) (by norm_num),
    mkT_eq (u := 5) (c := id4) (by norm_num) id4_lt, mkT_eq (u := 10) (c := id4) (by norm_num) id4_lt]

theorem map_flatMap_mul (L M : List Elt) :
    (L.flatMap fun x => M.map (mulE x)).map enc =
      (L.map enc).flatMap fun k => (M.map enc).map (mulT k) := by
  induction L with
  | nil => rfl
  | cons x t ih =>
    simp only [List.flatMap_cons, List.map_append, List.map_cons, ih, List.map_map,
      Function.comp_def, enc_mulE]

theorem map_dedup (l : List Elt) : l.dedup.map enc = (l.map enc).dedup := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have hm : enc x ∈ t.map enc ↔ x ∈ t := (mem_iff rfl).symm
    by_cases h : x ∈ t
    · rw [List.dedup_cons_of_mem h, List.map_cons, List.dedup_cons_of_mem (hm.2 h), ih]
    · rw [List.dedup_cons_of_notMem h, List.map_cons, List.map_cons,
        List.dedup_cons_of_notMem (fun h' => h (hm.1 h')), ih]

theorem Jl_map : Jl.map enc = JK := by
  unfold Jl JK
  rw [map_dedup, map_flatMap_mul, Vl_map, F0l_map, dedupN_eq]

theorem span4_sub {S : List Elt} (h1 : oneE ∈ S) (hm : ∀ x ∈ S, ∀ y ∈ S, mulE x y ∈ S)
    {a b c d : Elt} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) :
    ∀ x ∈ span4 a b c d, x ∈ S := by
  have step : ∀ (s : List Elt) (b : Elt), b ∈ S → (∀ x ∈ s, x ∈ S) →
      ∀ x ∈ s ++ s.map (mulE b), x ∈ S := by
    intro s b hb hs x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hs x hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hm b hb y (hs y hy)
  dsimp only [span4]
  refine step _ d hd (step _ c hc (step _ b hb ?_))
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact h1
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact ha
    · simp at hx

section Facts

variable (hd0 : ((List.range 4).flatMap fun i => (List.range 2).map fun j =>
    rhoCode (g1 ^ i * g2 ^ j)) = D0c)
variable (hs0 : ((Finset.univ.filter fun a : Equiv.Perm (Fin 6) => a.sign = 1).image
    rhoCode) = S0L.toFinset)

include hd0 in
theorem normalE16_of {A : List Elt} {K : List ℕ} (hA : A.map enc = K) (h : chNE K = true) :
    NormalE16 A := by
  unfold chNE at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h⟩ := andB_iff.1 h
  obtain ⟨h5, h⟩ := andB_iff.1 h
  obtain ⟨h6, h7⟩ := andB_iff.1 h
  have hP := P0l_map hd0
  refine ⟨(nodup_iff hA).2 ((nodupN_iff _).1 h1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [length_eq hA, ← lenN_eq]
    exact beq_iff.1 h2
  · intro x hx
    exact (memP_iff hd0 x).1 (allL_of hA h3 x hx)
  · intro x hx y hy
    have := (allL_iff _ _).1 (allL_of hA h4 x hx) _ ((mem_iff hA).1 hy)
    rw [memN_iff', ← enc_mulE] at this
    exact (mem_iff hA).2 this
  · intro x hx
    exact (mulT_one_iff x x).1 (beq_iff.1 (allL_of hA h5 x hx))
  · intro x hx y hy
    exact (commT_iff x y).1 ((allL_iff _ _).1 (allL_of hA h6 x hx) _ ((mem_iff hA).1 hy))
  · intro p hp q hq hpq x hx
    have := impB_iff.1 ((allL_iff _ _).1 (allL_of hP h7 p hp) _ ((mem_iff hP).1 hq))
      (beq_iff.2 ((mulT_one_iff p q).2 hpq))
    have := (allL_iff _ _).1 this _ ((mem_iff hA).1 hx)
    rw [memN_iff', ← enc_mulE, ← enc_mulE] at this
    exact (mem_iff hA).2 this

include hd0 hs0 in
theorem p0Group_of (h : chP0 = true) : P0Group := by
  unfold chP0 at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h5⟩ := andB_iff.1 h
  have hm := P0l_map hd0
  refine ⟨(nodup_iff hm).2 ((nodupN_iff _).1 h1), ?_, ?_, ?_, ?_⟩
  · rw [length_eq hm, ← lenN_eq]
    exact beq_iff.1 h2
  · rw [mem_iff hm, enc_one]
    exact (memN_iff' _ _).1 h3
  · intro x hx
    rw [mem_M0l hs0]
    rw [P0l_eq hd0, mem_grid D0c_lt] at hx
    exact (memN_iff' _ _).1 ((allL_iff _ _).1 h4 _ hx)
  · intro x hx y hy
    have := (allL_iff _ _).1 (allL_of hm h5 x hx) _ ((mem_iff hm).1 hy)
    rw [← enc_mulE, memP_iff hd0] at this
    exact this

include hd0 in
theorem vfGroups_of (h : chVF = true) : VFGroups := by
  unfold chVF at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h4⟩ := andB_iff.1 h
  refine ⟨normalE16_of hd0 Vl_map h1, normalE16_of hd0 F0l_map h2, ?_, ?_⟩
  · obtain ⟨k, hk, hk'⟩ := (anyL_iff _ _).1 h3
    obtain ⟨x, hx, rfl⟩ := exists_of_mem F0l_map hk
    refine ⟨x, hx, fun hv => notB_iff.1 hk' ?_⟩
    exact (memN_iff' _ _).2 ((mem_iff Vl_map).1 hv)
  · have hc : (VK.filter fun x => decide (x ∈ F0K)).length = 4 := by
      rw [← cntIn_eq]
      exact beq_iff.1 h4
    have e : (Vl.filter fun x => decide (x ∈ F0l)) =
        Vl.filter ((fun x => decide (x ∈ F0K)) ∘ enc) :=
      List.filter_congr fun x _ => by
        rw [Function.comp_apply, decide_eq_decide]
        exact mem_iff F0l_map
    rw [← hc, ← Vl_map, List.filter_map, List.length_map, e]

theorem oneE_mem_F0l : oneE ∈ F0l := by
  rw [F0l_eq]
  dsimp only [span4]
  simp

theorem memJ_iff (hj1 : allL JK memJ = true)
    (hj2 : allN 16 (fun u => allL F0m fun m => memN (mkT u m) JK) = true) (x : Elt) :
    memJ (enc x) = true ↔ x ∈ Jl := by
  constructor
  · intro h
    unfold memJ at h
    rw [memN_iff', hiT_enc] at h
    obtain ⟨u, hu, hv⟩ := vec_surj x.1
    have := (allL_iff _ _).1 ((allN_iff _ _).1 hj2 u hu) _ h
    rw [memN_iff', mkT_eq hu (F0m_lt _ h), hv, ofCode_code4] at this
    exact (mem_iff Jl_map).2 this
  · intro h
    exact allL_of Jl_map hj1 x h

include hd0 in
theorem jGroup_of (h : chJ = true) : JGroup := by
  unfold chJ at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h⟩ := andB_iff.1 h
  obtain ⟨h5, h6⟩ := andB_iff.1 h
  refine ⟨(nodup_iff Jl_map).2 ((nodupN_iff _).1 h1), ?_, ?_, ?_⟩
  · rw [length_eq Jl_map, ← lenN_eq]
    exact beq_iff.1 h2
  · intro x hx
    exact (memP_iff hd0 x).1 (allL_of Jl_map h3 x hx)
  · intro x hx y hy
    have := (allL_iff _ _).1 (allL_of Jl_map h6 x hx) _ ((mem_iff Jl_map).1 hy)
    rw [← enc_mulE] at this
    exact (memJ_iff h4 h5 _).1 this

include hd0 in
theorem centP_of (h : chCent = true) : CentP := by
  unfold chCent at h
  obtain ⟨h1, h2⟩ := andB_iff.1 h
  have hP := P0l_map hd0
  refine ⟨fun p hp hc => ?_, fun p hp hc => ?_⟩
  · have := impB_iff.1 (allL_of hP h1 p hp) (allL_mk Vl_map fun x hx => (commT_iff p x).2 (hc x hx))
    exact (mem_iff Vl_map).2 ((memN_iff' _ _).1 this)
  · have := impB_iff.1 (allL_of hP h2 p hp)
      (allL_mk F0l_map fun x hx => (commT_iff p x).2 (hc x hx))
    exact (mem_iff F0l_map).2 ((memN_iff' _ _).1 this)

include hd0 hs0 in
theorem yExists_of (hj : chJ = true) (h : chY = true) : YExists := by
  unfold chJ at hj
  obtain ⟨-, hj⟩ := andB_iff.1 hj
  obtain ⟨-, hj⟩ := andB_iff.1 hj
  obtain ⟨-, hj⟩ := andB_iff.1 hj
  obtain ⟨hj1, hj⟩ := andB_iff.1 hj
  obtain ⟨hj2, -⟩ := andB_iff.1 hj
  have hJ := memJ_iff hj1 hj2
  have hP := P0l_map hd0
  have ey : yT = enc (vecOfCode 0, ofCode 5097) := mkT_eq (by norm_num) (by norm_num)
  have es : sT = enc (vecOfCode 0, ofCode 4680) := mkT_eq (by norm_num) (by norm_num)
  unfold chY at h
  rw [letB_eq, ey, es] at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h⟩ := andB_iff.1 h
  obtain ⟨h5, h⟩ := andB_iff.1 h
  obtain ⟨h6, h⟩ := andB_iff.1 h
  obtain ⟨h7, h⟩ := andB_iff.1 h
  obtain ⟨h8, h⟩ := andB_iff.1 h
  obtain ⟨h9, h10⟩ := andB_iff.1 h
  simp only [← enc_mulE] at h3 h4 h9
  refine ⟨(vecOfCode 0, ofCode 5097), ?_, ?_, ?_, ?_, ?_, (vecOfCode 0, ofCode 4680), ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [mem_M0l hs0]
    rw [memN_iff', hiT_enc] at h1
    exact h1
  · intro e
    refine notB_iff.1 h2 (beq_iff.2 ?_)
    rw [e, enc_one]
  · rw [beq_iff, ← enc_one] at h3
    exact enc_inj h3
  · intro j hj
    have := (allL_iff _ _).1 h4 _ ((mem_iff Jl_map).1 hj)
    simp only [← enc_mulE] at this
    exact (hJ _).1 this
  · intro j hj hc
    have := impB_iff.1 ((allL_iff _ _).1 h5 _ ((mem_iff Jl_map).1 hj)) ((commT_iff _ _).2 hc)
    rw [beq_iff, ← enc_one] at this
    exact enc_inj this
  · exact (memP_iff hd0 _).1 h6
  · intro hs
    exact notB_iff.1 h7 ((hJ _).2 hs)
  · exact (mulT_one_iff _ _).1 (beq_iff.1 h8)
  · rw [beq_iff] at h9
    exact enc_inj h9
  · intro p hp
    rcases orB_iff.1 (allL_of hP h10 p hp) with hq | hq
    · exact Or.inl ((hJ _).1 hq)
    · rw [← enc_mulE] at hq
      exact Or.inr ((hJ _).1 hq)

noncomputable def rkF (IM : List ℕ) (W : List (ℕ × ℕ × ℕ)) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (fun w _ ih l => List.rec (motive := fun _ => Bool) false
      (fun s t _ => andB (rankAt IM s w.1 w.2.1 w.2.2) (ih t)) l) W L

theorem rkF_sound (IM : List ℕ) : ∀ (W : List (ℕ × ℕ × ℕ)) (L : List ℕ), rkF IM W L = true →
    ∀ s ∈ L, ∃ j k l, rankAt IM s j k l = true
  | [], [], _, s, hs => absurd hs List.not_mem_nil
  | [], _ :: _, h, _, _ => absurd h Bool.false_ne_true
  | _ :: _, [], h, _, _ => absurd h Bool.false_ne_true
  | w :: W, s :: t, h, s', hs' => by
    change andB (rankAt IM s w.1 w.2.1 w.2.2) (rkF IM W t) = true at h
    obtain ⟨h1, h2⟩ := andB_iff.1 h
    rcases List.mem_cons.1 hs' with rfl | hs'
    · exact ⟨_, _, _, h1⟩
    · exact rkF_sound IM W t h2 s' hs'

include hs0 in
theorem rankCent_of {W : List (ℕ × ℕ × ℕ)} (h : chRankOn IMK W = true) : RankCent := by
  have hr : ∀ s ∈ IMK, ∃ j k l, rankAt IMK s j k l = true := rkF_sound IMK W IMK h
  have hIM : ∀ x, x ∈ InvM ↔ enc x ∈ IMK := fun x => (mem_InvM_iff hs0 x).trans (mem_iff IMl_map)
  have get : ∀ {i : ℕ}, Nat.blt i (lenN IMK) = true → ∃ a ∈ InvM, enc a = lAt IMK i := by
    intro i hi
    rw [blt_iff, lenN_eq] at hi
    obtain ⟨a, ha, e⟩ := exists_of_mem IMl_map (lAt_mem _ _ hi)
    exact ⟨a, (mem_InvM_iff hs0 a).2 ha, e⟩
  intro s hs
  obtain ⟨j, k, l, h⟩ := hr _ ((hIM s).1 hs)
  unfold rankAt at h
  simp only [letB_eq] at h
  obtain ⟨hj, h⟩ := andB_iff.1 h
  obtain ⟨hk, h⟩ := andB_iff.1 h
  obtain ⟨hl, h⟩ := andB_iff.1 h
  obtain ⟨c1, h⟩ := andB_iff.1 h
  obtain ⟨c2, h⟩ := andB_iff.1 h
  obtain ⟨c3, h⟩ := andB_iff.1 h
  obtain ⟨c4, h⟩ := andB_iff.1 h
  obtain ⟨c5, h⟩ := andB_iff.1 h
  obtain ⟨c6, hn⟩ := andB_iff.1 h
  obtain ⟨a, ha, ea⟩ := get hj
  obtain ⟨b, hb, eb⟩ := get hk
  obtain ⟨c, hc, ec⟩ := get hl
  simp only [← ea, ← eb, ← ec] at c1 c2 c3 c4 c5 c6 hn
  rw [commT_iff] at c1 c2 c3 c4 c5 c6
  refine ⟨a, ha, c1, b, hb, c2, c4, c, hc, c3, c5, c6, ?_⟩
  rw [nodupN_iff, ← span4_map] at hn
  exact hn.of_map enc

include hd0 in
theorem onlyP_of (hvf : chVF = true) (h : chOnly = true) : OnlyP := by
  have hF := (vfGroups_of hd0 hvf).2.1
  have hI := InvP_map hd0
  intro a ha hav b hb hab c hc hac hbc d hd had hbd hcd hn x hx
  have := impB_iff.1 (allL_of hI h a ha)
    (notB_iff.2 fun e => hav ((mem_iff Vl_map).2 ((memN_iff' _ _).1 e)))
  have := impB_iff.1 (allL_of hI this b hb) ((commT_iff a b).2 hab)
  have := impB_iff.1 (allL_of hI this c hc)
    (andB_iff.2 ⟨(commT_iff a c).2 hac, (commT_iff b c).2 hbc⟩)
  have := impB_iff.1 (allL_of hI this d hd)
    (andB_iff.2 ⟨(commT_iff a d).2 had, andB_iff.2 ⟨(commT_iff b d).2 hbd, (commT_iff c d).2 hcd⟩⟩)
  rcases orB_iff.1 this with h4 | h4
  · obtain ⟨e1, h4⟩ := andB_iff.1 h4
    obtain ⟨e2, h4⟩ := andB_iff.1 h4
    obtain ⟨e3, e4⟩ := andB_iff.1 h4
    have m : ∀ y, memN (enc y) F0K = true → y ∈ F0l := fun y e =>
      (mem_iff F0l_map).2 ((memN_iff' _ _).1 e)
    exact span4_sub oneE_mem_F0l hF.2.2.2.1 (m a e1) (m b e2) (m c e3) (m d e4) x hx
  · refine absurd ?_ (notB_iff.1 h4)
    rw [nodupN_iff, ← span4_map]
    exact hn.map enc_injective

include hd0 hs0 in
theorem facts_of_kernel (hp0 : chP0 = true) (hvf : chVF = true) (hj : chJ = true)
    (hcent : chCent = true) (hy : chY = true) {W : List (ℕ × ℕ × ℕ)}
    (hrank : chRankOn IMK W = true) (honly : chOnly = true) : Facts :=
  ⟨p0Group_of hd0 hs0 hp0, vfGroups_of hd0 hvf, onlyP_of hd0 hvf honly, jGroup_of hd0 hj,
    centP_of hd0 hcent, yExists_of hd0 hs0 hj hy, rankCent_of hs0 hrank⟩

end Facts

end CFSG.KC.Misc.T84

end
