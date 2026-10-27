module

public import CFSG.Certificates.Kernel.SortTreeArr

public section

namespace CFSG.KC.SortTree

open CFSG.KC.Bfs CFSG.Monster.B.TwoA.Census CFSG.KLie.CT CFSG.KC.U6Orb

@[expose] noncomputable def keyP (x : Array ℕ) : ℕ := packL 5 x.toList

@[expose] noncomputable def decP (c : ℕ) : Array ℕ :=
  ((List.range 24).map fun i => fget c i 5).toArray

@[expose] noncomputable def packF (f : ℕ → ℕ) : ℕ :=
  orN 24 fun i => Nat.shiftLeft (f i) (Nat.mul 5 i)

@[expose] noncomputable def amulP (G c : ℕ) : ℕ := packF fun i => fget G (fget c i 5) 5

@[expose] noncomputable def conjP (G GI c : ℕ) : ℕ :=
  packF fun i => fget G (fget c (fget GI i 5) 5) 5

theorem lt32_of_perm {x : Array ℕ} (hx : PermArr x = true) : ∀ v ∈ x.toList, v < 2 ^ 5 :=
  fun v hv => lt_trans (PermArr_toList_lt hx v hv) (by norm_num)

theorem fget_keyP {x : Array ℕ} (hx : PermArr x = true) {i : ℕ} (hi : i < 24) :
    fget (keyP x) i 5 = x[i]! :=
  fget_packA (lt32_of_perm hx) (by rw [PermArr_size hx]; exact hi)

theorem decP_keyP {x : Array ℕ} (hx : PermArr x = true) : decP (keyP x) = x := by
  apply Array.ext
  · simp [decP, PermArr_size hx]
  · intro i h1 h2
    simp only [decP, List.getElem_toArray, List.getElem_map, List.getElem_range]
    rw [fget_keyP hx (by simpa [decP] using h1), getElem!_pos x i h2]

theorem orN_succ' (m : ℕ) (f : ℕ → ℕ) : orN (m + 1) f = Nat.lor (f m) (orN m f) := rfl

theorem packL_append (w x : ℕ) : ∀ L : List ℕ,
    packL w (L ++ [x]) = packL w L ||| (x <<< (w * L.length))
  | [] => by
    change Nat.lor x (Nat.shiftLeft 0 w) = Nat.lor 0 (Nat.shiftLeft x (Nat.mul w 0))
    simp
  | y :: L => by
    change Nat.lor y (Nat.shiftLeft (packL w (L ++ [x])) w) =
      Nat.lor (Nat.lor y (Nat.shiftLeft (packL w L) w)) (x <<< (w * (L.length + 1)))
    rw [packL_append w x L]
    change y ||| (packL w L ||| x <<< (w * L.length)) <<< w =
      (y ||| packL w L <<< w) ||| x <<< (w * (L.length + 1))
    rw [Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add, Nat.or_assoc]
    congr 3

theorem packF_eq (f : ℕ → ℕ) : ∀ m, orN m (fun i => Nat.shiftLeft (f i) (Nat.mul 5 i)) =
    packL 5 ((List.range m).map f)
  | 0 => rfl
  | m + 1 => by
    rw [orN_succ', packF_eq f m, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      packL_append, List.length_map, List.length_range]
    change f m <<< (5 * m) ||| _ = _
    rw [Nat.or_comm]

theorem keyP_eq_packF {x : Array ℕ} (hx : PermArr x = true) : keyP x = packF fun i => x[i]! := by
  rw [packF, packF_eq, keyP]
  congr 1
  apply List.ext_getElem
  · simp [PermArr_size hx]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range, Array.getElem_toList,
      getElem!_pos x i (by simpa using h1)]

theorem amulP_eq {g x : Array ℕ} (hg : PermArr g = true) (hx : PermArr x = true) :
    amulP (keyP g) (keyP x) = keyP (amul g x) := by
  rw [keyP_eq_packF (PermArr_amul hg hx), amulP, packF, packF, packF_eq, packF_eq]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hi' : i < 24 := List.mem_range.1 hi
  rw [fget_keyP hx hi', fget_keyP hg (PermArr_lt hx ⟨i, hi'⟩), amul_getElem hx ⟨i, hi'⟩]

theorem conjP_eq {g x : Array ℕ} (hg : PermArr g = true) (hx : PermArr x = true) :
    conjP (keyP g) (keyP (ainv g)) (keyP x) = keyP (aconj g x) := by
  have hgi := PermArr_ainv hg
  rw [keyP_eq_packF (PermArr_aconj hg hx), conjP, packF, packF, packF_eq, packF_eq]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hi' : i < 24 := List.mem_range.1 hi
  have hj := PermArr_lt hgi ⟨i, hi'⟩
  have hk := PermArr_lt hx ⟨_, hj⟩
  rw [fget_keyP hgi hi', fget_keyP hx hj, fget_keyP hg hk, aconj,
    amul_getElem hgi ⟨i, hi'⟩, amul_getElem hx ⟨_, hj⟩]

theorem keyP_inj {x y : Array ℕ} (hx : PermArr x = true) (hy : PermArr y = true)
    (h : keyP x = keyP y) : x = y := by
  rw [← decP_keyP hx, ← decP_keyP hy, h]

theorem bfsCert_treeP_mem {act : Array ℕ → Array ℕ → Array ℕ} {gens : Array (Array ℕ)}
    {root : Array ℕ} {actN : ℕ → ℕ → ℕ} {rec : ℕ → ℕ} {E : ℕ → ℕ → ℕ}
    {n wv wl wp B C B' C' fuel : ℕ}
    (hact : ∀ k < gens.size, ∀ x, PermArr x = true → PermArr (act gens[k]! x) = true)
    (hcode : ∀ k < gens.size, ∀ x, PermArr x = true → actN k (keyP x) = keyP (act gens[k]! x))
    (hroot : PermArr root = true) (hn : 0 < n) (hfuel : n ≤ fuel)
    (hT : treeOK actN gens.size (fun _ => true) (keyP root) rec n wv wl wp B C = true)
    (hE : closeOK actN gens.size rec E n wv B' C' = true) :
    certOK act gens root (bfsCert act gens root fuel) = true ∧
      (bfsCert act gens root fuel).pts.size = n ∧
      (∀ x, x ∈ (bfsCert act gens root fuel).pts ↔
        PermArr x = true ∧ ∃ i < n, valF wv (rec i) = keyP x) ∧
      ((bfsCert act gens root fuel).pts.toList.map akey).Nodup ∧
      (∀ i < n, PermArr (decP (valF wv (rec i))) = true ∧
        keyP (decP (valF wv (rec i))) = valF wv (rec i)) ∧
      ∀ i j, i < j → j < n → valF wv (rec i) < valF wv (rec j) := by
  obtain ⟨S', hS', hcard, -, -, hmem⟩ := orbit_sound hn hT hE
  obtain ⟨hr, -, hlt, -⟩ := tree_sound hT
  obtain ⟨hS, hc, hv⟩ := orbit_code (act := fun k x => act gens[k]! x)
    (valid := fun x => PermArr x = true) (key := keyP) (dec := decP)
    (fun a ha => decP_keyP ha) hact hcode hroot hS'
  obtain ⟨h1, h2, h3, h4⟩ := bfsCert_spec (fuel := fuel) _ hS hv (by rw [hc, hcard]; exact hfuel)
  refine ⟨h1, h3.trans (hc.trans hcard), fun x => ?_, h4, fun i hi => ?_, hlt⟩
  · rw [h2]
    constructor
    · intro h
      obtain ⟨c, hcS, rfl⟩ := Finset.mem_image.1 h
      have hrc := reach_code (act := fun k x => act gens[k]! x)
        (valid := fun x => PermArr x = true) (fun a ha => decP_keyP ha) hact hcode hroot
        ((hS' c).2 hcS)
      obtain ⟨i, hi, e⟩ := (hmem c).1 hcS
      exact ⟨hrc.1, i, hi, e.trans hrc.2.2.symm⟩
    · rintro ⟨hx, i, hi, e⟩
      exact Finset.mem_image.2 ⟨keyP x, (hmem _).2 ⟨i, hi, e⟩, decP_keyP hx⟩
  · have hrc := reach_code (act := fun k x => act gens[k]! x) (valid := fun x => PermArr x = true)
      (fun a ha => decP_keyP ha) hact hcode hroot (hr i hi)
    exact ⟨hrc.1, hrc.2.2⟩

theorem filter_length_pts {pts : Array (Array ℕ)} {n : ℕ} {v : ℕ → ℕ} (P : Array ℕ → Bool)
    (hmem : ∀ x, x ∈ pts ↔ PermArr x = true ∧ ∃ i < n, v i = keyP x)
    (hnd : (pts.toList.map akey).Nodup)
    (hrec : ∀ i < n, PermArr (decP (v i)) = true ∧ keyP (decP (v i)) = v i)
    (hlt : ∀ i j, i < j → j < n → v i < v j) :
    (pts.toList.filter P).length =
      ((Finset.range n).filter fun i => P (decP (v i)) = true).card := by
  classical
  have hnd' : (pts.toList.filter P).Nodup := (hnd.of_map _).sublist List.filter_sublist
  rw [← List.toFinset_card_of_nodup hnd']
  have e : (pts.toList.filter P).toFinset =
      ((Finset.range n).filter fun i => P (decP (v i)) = true).image fun i => decP (v i) := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, Array.mem_toList_iff, Finset.mem_image,
      Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hx, hp⟩
      obtain ⟨hpx, i, hi, e⟩ := (hmem x).1 hx
      exact ⟨i, ⟨hi, by rw [e, decP_keyP hpx]; exact hp⟩, by rw [e, decP_keyP hpx]⟩
    · rintro ⟨i, ⟨hi, hp⟩, rfl⟩
      exact ⟨(hmem _).2 ⟨(hrec i hi).1, i, hi, (hrec i hi).2.symm⟩, hp⟩
  rw [e, Finset.card_image_of_injOn]
  intro i hi j hj h
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi hj
  have h' : v i = v j := by
    rw [← (hrec i hi.1).2, ← (hrec j hj.1).2]
    exact congrArg keyP h
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd h' (ne_of_lt (hlt i j hij hj.1))
  · rfl
  · exact absurd h' (ne_of_gt (hlt j i hij hi.1))

end CFSG.KC.SortTree

end
