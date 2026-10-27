module

public import Certificates.Data.Kernel.D42K

public section

namespace CFSG.KC.D42K

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two CFSG.AGLEmbedding.ChevOuter

theorem toNat_add (a b : GF8) : (a + b).toNat = a.toNat ^^^ b.toNat := by
  revert a b
  decide

theorem toNat_mul (a b : GF8) : (a * b).toNat = gmK a.toNat b.toNat := by
  revert a b
  decide

theorem toNat_frobF (a : GF8) : (frobF a).toNat = frK a.toNat := by
  revert a
  decide

theorem toNat_inj {a b : GF8} (h : a.toNat = b.toNat) : a = b := by
  cases a with | mk a => cases b with | mk b => exact congrArg GF8.mk (Fin.ext h)

theorem entK_encM (A : Array GF8) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    entK (encM A) i j = (A.getD (8 * i + j) 0).toNat := by
  unfold entK encM
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hi, hj]

theorem getD_mulArr (A B : Array GF8) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    (mulArr A B).getD (8 * i + j) 0 =
      A.getD (8 * i + 0) 0 * B.getD (8 * 0 + j) 0 + A.getD (8 * i + 1) 0 * B.getD (8 * 1 + j) 0 +
      A.getD (8 * i + 2) 0 * B.getD (8 * 2 + j) 0 + A.getD (8 * i + 3) 0 * B.getD (8 * 3 + j) 0 +
      A.getD (8 * i + 4) 0 * B.getD (8 * 4 + j) 0 + A.getD (8 * i + 5) 0 * B.getD (8 * 5 + j) 0 +
      A.getD (8 * i + 6) 0 * B.getD (8 * 6 + j) 0 + A.getD (8 * i + 7) 0 * B.getD (8 * 7 + j) 0 := by
  unfold mulArr
  rw [getD_ofFn _ _ (by omega)]
  have h1 : (8 * i + j) / 8 = i := by omega
  have h2 : (8 * i + j) % 8 = j := by omega
  simp only [h1, h2, Nat.add_zero, Nat.mul_zero, Nat.zero_add, Nat.mul_one]

theorem encM_mulArr (A B : Array GF8) : encM (mulArr A B) = mulMK (encM A) (encM B) := by
  unfold mulMK
  conv_lhs => unfold encM
  refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hi hj
  unfold dotK
  simp only [entK_encM _ hi (by omega : (0 : Nat) < 8), entK_encM _ hi (by omega : (1 : Nat) < 8),
    entK_encM _ hi (by omega : (2 : Nat) < 8), entK_encM _ hi (by omega : (3 : Nat) < 8),
    entK_encM _ hi (by omega : (4 : Nat) < 8), entK_encM _ hi (by omega : (5 : Nat) < 8),
    entK_encM _ hi (by omega : (6 : Nat) < 8), entK_encM _ hi (by omega : (7 : Nat) < 8),
    entK_encM _ (by omega : (0 : Nat) < 8) hj, entK_encM _ (by omega : (1 : Nat) < 8) hj,
    entK_encM _ (by omega : (2 : Nat) < 8) hj, entK_encM _ (by omega : (3 : Nat) < 8) hj,
    entK_encM _ (by omega : (4 : Nat) < 8) hj, entK_encM _ (by omega : (5 : Nat) < 8) hj,
    entK_encM _ (by omega : (6 : Nat) < 8) hj, entK_encM _ (by omega : (7 : Nat) < 8) hj,
    getD_mulArr A B hi hj, toNat_add, toNat_mul]

theorem encM_frobArr (A : Array GF8) : encM (frobArr A) = frobK (encM A) := by
  unfold frobK encM
  simp only [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_def, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  rw [getD_frobArr, toNat_frobF]

theorem encM_frobPow (n : Nat) (A : Array GF8) : encM (frobPow n A) = frobPowK n (encM A) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [frobPow, frobPowK, encM_frobArr, ih]

theorem encP_mulP (p q : Pr) : encP (mulP p q) = mulPK (encP p) (encP q) := by
  unfold encP mulP mulPK
  rw [encM_mulArr, encM_frobPow]

theorem encP_powP (p : Pr) (n : Nat) : encP (powP p n) = powPK (encP p) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [powP, powPK, encP_mulP, ih]

theorem encP_wordP (w : List Nat) : encP (wordP w) = wordPK w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    unfold wordP wordPK at *
    rw [List.foldr_cons, List.foldr_cons, encP_mulP, ih]
    rfl

theorem eK_eq (i : Nat) : eK i = encP (d42eP i) := (encP_wordP _).symm

theorem nK_eq (j : Nat) : nK j = encP (d42nP j) := (encP_wordP _).symm

theorem nInvK_eq (j : Nat) : nInvK j = encP (d42nInvP j) := (encP_wordP _).symm

theorem slpEltK_eq (i : Nat) : slpEltK i = encP (d42slpElt i) := by
  unfold slpEltK d42slpElt nListK nInvListK d42nList d42nInvList
  have e1 : (List.range (d42N1 + d42N2)).map nK = ((List.range (d42N1 + d42N2)).map d42nP).map encP := by
    rw [List.map_map]
    exact List.map_congr_left fun j _ => nK_eq j
  have e2 : (List.range (d42N1 + d42N2)).map nInvK =
      ((List.range (d42N1 + d42N2)).map d42nInvP).map encP := by
    rw [List.map_map]
    exact List.map_congr_left fun j _ => nInvK_eq j
  rw [e1, e2]
  split
  · exact List.getD_map ..
  · exact List.getD_map ..

theorem encP_foldl (ids : List Nat) (acc : Pr) :
    encP (ids.foldl (fun acc i => mulP acc (d42slpElt i)) acc) =
      ids.foldl (fun acc i => mulPK acc (slpEltK i)) (encP acc) := by
  induction ids generalizing acc with
  | nil => rfl
  | cons i ids ih => rw [List.foldl_cons, List.foldl_cons, ih, encP_mulP, slpEltK_eq]

theorem encP_slpP (ids : List Nat) : encP (d42slpP ids) = slpPK ids := encP_foldl ids oneP

theorem encM_inj {A B : Array GF8} (hA : A.size = 64) (hB : B.size = 64) (h : encM A = encM B) :
    A = B := by
  refine Array.ext (by rw [hA, hB]) fun t h1 h2 => ?_
  have ht : t < 64 := hA ▸ h1
  have hi : t / 8 < 8 := by omega
  have hj : t % 8 < 8 := Nat.mod_lt _ (by omega)
  have e := congrArg (fun C => entK C (t / 8) (t % 8)) h
  simp only [entK_encM _ hi hj] at e
  rw [Nat.div_add_mod] at e
  have e2 := toNat_inj e
  rwa [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some] at e2

theorem encP_inj {p q : Pr} (hp : p.1.size = 64) (hq : q.1.size = 64) (h : encP p = encP q) :
    p = q := by
  unfold encP at h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  exact Prod.ext (encM_inj hp hq h1) h2

theorem size_mulP (p q : Pr) : (mulP p q).1.size = 64 := size_mulArr _ _

theorem size_oneP : oneP.1.size = 64 := size_oneArr

theorem size_powP (p : Pr) (n : Nat) : (powP p n).1.size = 64 := by
  cases n with
  | zero => exact size_oneP
  | succ n => exact size_mulP _ _

theorem size_foldl (ids : List Nat) (acc : Pr) (h : acc.1.size = 64) :
    (ids.foldl (fun acc i => mulP acc (d42slpElt i)) acc).1.size = 64 := by
  induction ids generalizing acc with
  | nil => exact h
  | cons i ids ih =>
    rw [List.foldl_cons]
    exact ih (mulP acc (d42slpElt i)) (size_mulP acc (d42slpElt i))

theorem size_slpP (ids : List Nat) : (d42slpP ids).1.size = 64 := size_foldl ids oneP size_oneP

theorem eq_of_beq {p q : Pr} (hp : p.1.size = 64) (hq : q.1.size = 64)
    (h : (encP p == encP q) = true) : p = q :=
  encP_inj hp hq (beq_iff_eq.1 h)

theorem d42Check_of (h : d42CheckK = true) (hs : ∀ k < 18, d42SlpK k = true) : D42Check := by
  unfold d42CheckK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  simp only [eK_eq, nK_eq, nInvK_eq, onePK, ← encP_mulP, ← encP_powP] at h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨?_, eq_of_beq (size_mulP _ _) (size_mulP _ _) h2,
    eq_of_beq (size_mulP _ _) (size_mulP _ _) h3, eq_of_beq (size_mulP _ _) (size_mulP _ _) h4,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact eq_of_beq (size_powP _ _) size_oneP (List.all_eq_true.1 h1 i hi)
  · intro a ha b hb c hc
    have := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h5 a ha) b hb) c hc
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
    rcases this with ⟨⟨ha0, hb0⟩, hc0⟩ | hne
    · exact Or.inl ⟨ha0, hb0, hc0⟩
    · exact Or.inr fun e => hne (congrArg encP e)
  · intro j hj
    exact eq_of_beq (size_mulP _ _) size_oneP (List.all_eq_true.1 h6 j hj)
  · intro j hj g hg
    have := List.all_eq_true.1 (List.all_eq_true.1 h7 j hj) g hg
    obtain ⟨s, hs', this⟩ := List.any_eq_true.1 this
    obtain ⟨t, ht, this⟩ := List.any_eq_true.1 this
    exact ⟨s, hs', t, ht, eq_of_beq (size_mulP _ _) (size_mulP _ _) this⟩
  · intro j hj g hg
    have := List.all_eq_true.1 (List.all_eq_true.1 h8 j hj) g hg
    obtain ⟨s, hs', this⟩ := List.any_eq_true.1 this
    obtain ⟨t, ht, this⟩ := List.any_eq_true.1 this
    exact ⟨s, hs', t, ht, eq_of_beq (size_mulP _ _) (size_mulP _ _) this⟩
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have hk18 : k < 18 := by
      have : d42Slp.length = 18 := rfl
      omega
    have hk' := hs k hk18
    unfold d42SlpK at hk'
    rw [List.getD_eq_getElem _ _ hk] at hk'
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hk'
    refine ⟨hk'.1, ?_⟩
    rw [← encP_slpP] at hk'
    exact eq_of_beq (size_slpP _) (size_ofMat _) hk'.2
  · intro k hk
    obtain ⟨x, hx, e⟩ := List.any_eq_true.1 (List.all_eq_true.1 h9 k hk)
    exact ⟨x, hx, beq_iff_eq.1 e⟩

end CFSG.KC.D42K

end
