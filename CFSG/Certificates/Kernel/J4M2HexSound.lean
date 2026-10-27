module

public import Certificates.Data.Kernel.J4M2Hex
public import CFSG.Certificates.Kernel.LocalQTBfsK7Sound

public section

namespace CFSG.KC.J4M2K

open Equiv CFSG.KC.Enum CFSG.KC.LQT.L CFSG.KS.PK CFSG.Quasithin.J4M2
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat

theorem brec_and (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem brec_or (a b : Bool) : Bool.rec (motive := fun _ => Bool) b true a = (a || b) := by
  cases a <;> rfl

theorem nbeq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem strictB_eq' (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem allR_eq : ∀ (n : ℕ) (f : ℕ → Bool), allR n f = (List.range n).all f
  | 0, _ => rfl
  | n + 1, f => by
    rw [List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
      ← allR_eq n f, Bool.and_comm]
    exact brec_and (f n) (allR n f)

theorem anyR_eq : ∀ (n : ℕ) (f : ℕ → Bool), anyR n f = (List.range n).any f
  | 0, _ => rfl
  | n + 1, f => by
    rw [List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      ← anyR_eq n f, Bool.or_comm]
    exact brec_or (f n) (anyR n f)

theorem allA_eq' {α : Type} : ∀ (l : List α) (f : α → Bool), allA l f = l.all f
  | [], _ => rfl
  | x :: l, f => by
    rw [List.all_cons, ← allA_eq' l f]
    exact brec_and (f x) (allA l f)

theorem anyA_eq' {α : Type} : ∀ (l : List α) (f : α → Bool), anyA l f = l.any f
  | [], _ => rfl
  | x :: l, f => by
    rw [List.any_cons, ← anyA_eq' l f]
    change Bool.rec (motive := fun _ => Bool) (anyA l f) true (f x) = _
    exact brec_or (f x) (anyA l f)

theorem firstR_eq (p : ℕ → Bool) (d : ℕ) :
    ∀ m i, firstR p d m i = ((List.range' i m).find? p).getD d
  | 0, _ => rfl
  | m + 1, i => by
    rw [List.range'_succ, List.find?_cons]
    change Bool.rec (motive := fun _ => ℕ) (firstR p d m (i + 1)) i (p i) = _
    cases p i
    · exact firstR_eq p d m (i + 1)
    · rfl

theorem maskL_cons (x : ℕ) (l : List ℕ) : maskL (x :: l) = 2 ^ x ||| maskL l := by
  change (1 <<< x) ||| maskL l = _
  rw [Nat.one_shiftLeft]

theorem testBit_maskL (k : ℕ) : ∀ l : List ℕ, (maskL l).testBit k = decide (k ∈ l)
  | [] => by
    change Nat.testBit 0 k = _
    simp
  | x :: l => by
    rw [maskL_cons, Nat.testBit_or, Nat.testBit_two_pow, testBit_maskL k l]
    by_cases h : x = k
    · subst h
      simp
    · have h' : k ≠ x := fun e => h e.symm
      simp [h, h']

theorem maskL_eq_iff {l₁ l₂ : List ℕ} : maskL l₁ = maskL l₂ ↔ ∀ k, k ∈ l₁ ↔ k ∈ l₂ := by
  constructor
  · intro h k
    have := congrArg (fun m => m.testBit k) h
    simpa only [testBit_maskL, decide_eq_decide] using this
  · intro h
    refine Nat.eq_of_testBit_eq fun k => ?_
    rw [testBit_maskL, testBit_maskL, decide_eq_decide]
    exact h k

theorem maskL_lt {l : List ℕ} (hl : ∀ k ∈ l, k < 22) : maskL l < 2 ^ 22 := by
  refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
  rw [testBit_maskL, decide_eq_false_iff_not]
  exact fun hm => absurd (hl i hm) (by omega)

theorem imgR_succ (f : ℕ → ℕ) (m n : ℕ) :
    imgR f m (n + 1) = if m.testBit n then 2 ^ f n ||| imgR f m n else imgR f m n := by
  change Bool.rec (motive := fun _ => ℕ) (imgR f m n) ((1 <<< f n) ||| imgR f m n)
    (m.testBit n) = _
  rw [Nat.one_shiftLeft]
  cases m.testBit n <;> rfl

theorem testBit_imgR (f : ℕ → ℕ) (m x : ℕ) :
    ∀ n, (imgR f m n).testBit x = decide (∃ p < n, m.testBit p = true ∧ f p = x)
  | 0 => by
    change Nat.testBit 0 x = _
    simp
  | n + 1 => by
    rw [imgR_succ]
    apply Bool.eq_iff_iff.2
    rw [decide_eq_true_iff]
    by_cases hb : m.testBit n = true
    · rw [if_pos hb, Nat.testBit_or, Nat.testBit_two_pow, testBit_imgR f m x n, Bool.or_eq_true,
        decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro (h | ⟨p, hp, h1, h2⟩)
        · exact ⟨n, by omega, hb, h⟩
        · exact ⟨p, by omega, h1, h2⟩
      · rintro ⟨p, hp, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
        · exact Or.inr ⟨p, hp, h1, h2⟩
        · exact Or.inl h2
    · rw [if_neg hb, testBit_imgR f m x n, decide_eq_true_iff]
      constructor
      · rintro ⟨p, hp, h1, h2⟩
        exact ⟨p, by omega, h1, h2⟩
      · rintro ⟨p, hp, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
        · exact ⟨p, hp, h1, h2⟩
        · exact absurd h1 hb

theorem imgM_maskL (f : ℕ → ℕ) {l : List ℕ} (hl : ∀ k ∈ l, k < 22) :
    imgM f (maskL l) = maskL (l.map f) := by
  refine Nat.eq_of_testBit_eq fun x => ?_
  rw [imgM, testBit_imgR, testBit_maskL, decide_eq_decide, List.mem_map]
  constructor
  · rintro ⟨p, -, h1, h2⟩
    rw [testBit_maskL, decide_eq_true_iff] at h1
    exact ⟨p, h1, h2⟩
  · rintro ⟨p, h1, h2⟩
    exact ⟨p, hl p h1, by rw [testBit_maskL, decide_eq_true_iff]; exact h1, h2⟩

theorem ofNat_val22 (y : Fin 22) : Fin.ofNat 22 y.val = y :=
  Fin.ext (by rw [Fin.val_ofNat, Nat.mod_eq_of_lt y.isLt])

theorem mem_toFin {l : List ℕ} (hl : ∀ k ∈ l, k < 22) (x : Fin 22) :
    x ∈ (l.map (Fin.ofNat 22)).toFinset ↔ x.val ∈ l := by
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [Fin.val_ofNat, Nat.mod_eq_of_lt (hl a ha)]
  · intro hx
    exact ⟨x.val, hx, ofNat_val22 x⟩

theorem toFin_eq_iff {l₁ l₂ : List ℕ} (h₁ : ∀ k ∈ l₁, k < 22) (h₂ : ∀ k ∈ l₂, k < 22) :
    (l₁.map (Fin.ofNat 22)).toFinset = (l₂.map (Fin.ofNat 22)).toFinset ↔
      maskL l₁ = maskL l₂ := by
  rw [maskL_eq_iff, Finset.ext_iff]
  constructor
  · intro h k
    by_cases hk : k < 22
    · have := h ⟨k, hk⟩
      rwa [mem_toFin h₁, mem_toFin h₂] at this
    · exact ⟨fun hm => absurd (h₁ k hm) hk, fun hm => absurd (h₂ k hm) hk⟩
  · intro h x
    rw [mem_toFin h₁, mem_toFin h₂]
    exact h x.val

theorem image_toFin {l : List ℕ} (hl : ∀ k ∈ l, k < 22) (g : Perm (Fin 22)) :
    (l.map (Fin.ofNat 22)).toFinset.image g =
      ((l.map fun p => (g (Fin.ofNat 22 p)).val).map (Fin.ofNat 22)).toFinset := by
  have hl' : ∀ k ∈ l.map (fun p => (g (Fin.ofNat 22 p)).val), k < 22 := by
    intro k hk
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hk
    exact (g _).isLt
  ext x
  rw [Finset.mem_image, mem_toFin hl', List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_toFin hl] at hy
    exact ⟨y.val, hy, by rw [ofNat_val22]⟩
  · rintro ⟨p, hp, hpx⟩
    refine ⟨Fin.ofNat 22 p, ?_, Fin.ext hpx⟩
    rw [mem_toFin hl, Fin.val_ofNat, Nat.mod_eq_of_lt (hl p hp)]
    exact hp

def HexLt : Prop := ∀ i, ∀ k ∈ hexLab.getD i [], k < 22

theorem hexLt_of (h : (hexLab.all fun h => h.all (· < 22)) = true) : HexLt := by
  intro i k hk
  by_cases hi : i < hexLab.length
  · rw [List.getD_eq_getElem _ _ hi] at hk
    have h1 := List.all_eq_true.1 h _ (List.getElem_mem hi)
    simpa using List.all_eq_true.1 h1 k hk
  · rw [List.getD_eq_default _ _ (by omega)] at hk
    exact absurd hk (List.not_mem_nil)

theorem fd_hexP (hlt : HexLt) {i : ℕ} (hi : i < 77) : fd 22 hexP i = maskL (hexLab.getD i []) := by
  have hf : ∀ j < 77, maskL (hexLab.getD j []) < 2 ^ 22 := fun j _ => maskL_lt (hlt j)
  rw [hexP, pmk_eq (by norm_num) hf, fd_enc hf hi]

theorem fd_gimg (g : Perm (Fin 22)) {p : ℕ} (hp : p < 22) :
    fd 5 (gimg g) p = (g (Fin.ofNat 22 p)).val := by
  have hf : ∀ j < 22, (g (Fin.ofNat 22 j)).val < 2 ^ 5 := fun j _ =>
    lt_of_lt_of_le (g _).isLt (by norm_num)
  rw [gimg, pmk_eq (by norm_num) hf, fd_enc hf hp]

theorem image_hexB_eq_iff (hlt : HexLt) (g : Perm (Fin 22)) (i j : Fin 77) :
    (hexB i).image g = hexB j ↔ imgM (fd 5 (gimg g)) (fd 22 hexP i) = fd 22 hexP j := by
  have hmap : (hexLab.getD i.val []).map (fd 5 (gimg g)) =
      (hexLab.getD i.val []).map fun p => (g (Fin.ofNat 22 p)).val :=
    List.map_congr_left fun p hp => fd_gimg g (hlt i p hp)
  have hl' : ∀ k ∈ (hexLab.getD i.val []).map (fun p => (g (Fin.ofNat 22 p)).val), k < 22 := by
    intro k hk
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hk
    exact (g _).isLt
  rw [fd_hexP hlt i.isLt, fd_hexP hlt j.isLt, imgM_maskL _ (hlt i), hmap, hexB, hexB,
    image_toFin (hlt i), toFin_eq_iff hl' (hlt j)]

theorem hexB_eq_iff (hlt : HexLt) (i j : Fin 77) :
    hexB i = hexB j ↔ fd 22 hexP i = fd 22 hexP j := by
  rw [fd_hexP hlt i.isLt, fd_hexP hlt j.isLt, hexB, hexB, toFin_eq_iff (hlt i) (hlt j)]

theorem hexB_beq (hlt : HexLt) (i j : Fin 77) :
    (hexB i == hexB j) = Nat.beq (fd 22 hexP i) (fd 22 hexP j) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, nbeq_iff, hexB_eq_iff hlt]

theorem map_val_finRange (n : ℕ) : (List.finRange n).map Fin.val = List.range n :=
  List.ext_getElem (by simp) (by simp)

theorem permutesHex_eq (hlt : HexLt) (g : Perm (Fin 22)) :
    permutesHex g = permK hexP (fd 5 (gimg g)) := by
  have h1 : permutesHex g = (List.finRange 77).all fun i => (List.finRange 77).any fun j =>
      Nat.beq (imgM (fd 5 (gimg g)) (fd 22 hexP i.val)) (fd 22 hexP j.val) := by
    unfold permutesHex
    refine congrArg _ (funext fun i => congrArg _ (funext fun j => ?_))
    rw [Bool.eq_iff_iff, beq_iff_eq, nbeq_iff, image_hexB_eq_iff hlt]
  rw [h1, permK, allR_eq, ← map_val_finRange, List.all_map]
  refine congrArg _ (funext fun i => ?_)
  rw [Function.comp_apply, strictB_eq', anyR_eq, ← map_val_finRange, List.any_map]
  rfl

theorem find_finRange (q : ℕ → Bool) (i : Fin 77) :
    (((List.finRange 77).find? fun j => q j.val).getD i).val =
      ((List.range' 0 77).find? q).getD i.val := by
  rw [← List.range_eq_range', ← map_val_finRange, List.find?_map, Option.getD_map]
  rfl

theorem val_mk_ofFn (f : Fin 77 → Fin 77) (i : Fin 77) : (RN.mk (Vector.ofFn f)).val[i] = f i := by
  simp

theorem phiRN_val (hlt : HexLt) (g : Perm (Fin 22)) (i : Fin 77) :
    ((phiRN g).val[i] : ℕ) = phiK hexP (fd 5 (gimg g)) i := by
  have h1 : (phiRN g).val[i] = ((List.finRange 77).find? fun j =>
      Nat.beq (fd 22 hexP j.val) (imgM (fd 5 (gimg g)) (fd 22 hexP i.val))).getD i := by
    rw [phiRN, val_mk_ofFn]
    congr 2
    funext j
    rw [Bool.eq_iff_iff, beq_iff_eq, nbeq_iff, eq_comm, image_hexB_eq_iff hlt]
    exact eq_comm
  rw [h1]
  refine (find_finRange (fun j => Nat.beq (fd 22 hexP j) (imgM (fd 5 (gimg g)) (fd 22 hexP i.val)))
    i).trans ?_
  rw [phiK, strictN_eq', firstR_eq]

theorem phiK_lt (hlt : HexLt) (g : Perm (Fin 22)) {i : ℕ} (hi : i < 77) :
    phiK hexP (fd 5 (gimg g)) i < 77 := by
  have := phiRN_val hlt g ⟨i, hi⟩
  rw [← this]
  exact (Fin.isLt _)

theorem rnc7_phiRN (hlt : HexLt) (g : Perm (Fin 22)) : rnc7 (phiRN g) = phiC hexP (gimg g) := by
  have hf : ∀ i < 77, phiK hexP (fd 5 (gimg g)) i < 2 ^ 7 := fun i hi =>
    lt_of_lt_of_le (phiK_lt hlt g hi) (by norm_num)
  rw [phiC, pmk_eq (by norm_num) hf, rnc7_eq_enc]
  refine enc_congr fun i hi => ?_
  rw [rdig_of_lt _ hi]
  exact phiRN_val hlt g ⟨i, hi⟩

theorem rnc7_evalW (gens : List (RN 77)) :
    ∀ w, rnc7 (evalW gens w) = ev7 (gens.map rnc7) w
  | [] => rnc7_one (by norm_num)
  | i :: w => by
    rw [evalW, rnc7_mul (by norm_num), rnc7_evalW gens w]
    change _ = mul7 77 ((gens.map rnc7).getD i (one7 77)) (ev7 (gens.map rnc7) w)
    rw [← rnc7_one (n := 77) (by norm_num), List.getD_map]

theorem rnc7_sig (σ : Perm (Fin 77)) (n : ℕ)
    (h : ∀ i : Fin 77, (σ i : ℕ) = (sigData.getD n []).getD i 0) : rnc7 (RN.enc σ) = sigC n := by
  have hf : ∀ i < 77, (sigData.getD n []).getD i 0 < 2 ^ 7 := fun i hi => by
    rw [← h ⟨i, hi⟩]
    exact lt_of_lt_of_le (σ _).isLt (by norm_num)
  rw [rnc7_enc, code7_of_getD σ h, sigC, pmk_eq (by norm_num) hf]

theorem fix0_eq (x : RN 77) (f : ℕ → ℕ) (hx : ∀ i : Fin 77, (x.val[i] : ℕ) = f i) :
    fix0 x = fixK f := by
  have h0 : ((x.val[0] : Fin 77) : ℕ) = f 0 := hx 0
  rw [fix0, fixK, Bool.eq_iff_iff, beq_iff_eq, nbeq_iff, Fin.ext_iff, h0, Fin.val_zero]

theorem i5List_lt : ∀ k ∈ i5List, k < 77 := by
  intro k hk
  simp only [i5List, List.mem_cons, List.not_mem_nil, or_false] at hk
  omega

theorem presI5_eq (x : RN 77) (f : ℕ → ℕ) (hx : ∀ i : Fin 77, (x.val[i] : ℕ) = f i) :
    presI5 x = presK f := by
  rw [presI5, presK, allA_eq', i5Fin, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h i hi
    rw [anyA_eq', List.any_eq_true]
    have := h (Fin.ofNat 77 i) (List.mem_map_of_mem hi)
    rw [List.contains_iff_mem, List.mem_map] at this
    obtain ⟨j, hj, hji⟩ := this
    refine ⟨j, hj, nbeq_iff.2 ?_⟩
    have e := congrArg Fin.val hji
    rw [Fin.val_ofNat, Nat.mod_eq_of_lt (i5List_lt j hj), hx, Fin.val_ofNat,
      Nat.mod_eq_of_lt (i5List_lt i hi)] at e
    exact e.symm
  · intro h y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
    have := h i hi
    rw [anyA_eq', List.any_eq_true] at this
    obtain ⟨j, hj, hji⟩ := this
    rw [List.contains_iff_mem, List.mem_map]
    refine ⟨j, hj, Fin.ext ?_⟩
    rw [Fin.val_ofNat, Nat.mod_eq_of_lt (i5List_lt j hj), hx, Fin.val_ofNat,
      Nat.mod_eq_of_lt (i5List_lt i hi)]
    exact (nbeq_iff.1 hji).symm

end CFSG.KC.J4M2K

end
