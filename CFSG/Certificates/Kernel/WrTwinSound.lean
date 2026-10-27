module

public import Certificates.Data.Kernel.WrTwin

public section

namespace CFSG.KC.WrTwin

open CFSG.ClassicalInvolution.Q3.AE

variable {n : Nat}

theorem nib_packL : ∀ (l : List Nat) (p : Nat), (∀ x ∈ l, x < 16) → nib (packL l) p = l.getD p 0
  | [], p, _ => by simp [nib, packL]
  | x :: l, 0, h => by
    have hx := h x List.mem_cons_self
    simp only [nib, packL, pow_zero, Nat.div_one, List.getD_cons_zero]
    omega
  | x :: l, p + 1, h => by
    have hx := h x List.mem_cons_self
    have ih := nib_packL l p fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.getD_cons_succ, ← ih]
    have h16 : (x + 16 * packL l) / 16 = packL l := by omega
    simp only [nib, packL]
    rw [pow_succ', ← Nat.div_div_eq_div_mul, h16]

theorem nib_succ (y p : Nat) : nib y (p + 1) = nib (y / 16) p := by
  simp only [nib]
  rw [pow_succ', ← Nat.div_div_eq_div_mul]

theorem pmul_eq : ∀ (m x y : Nat), pmul m x y = packL ((List.range m).map fun p => nib x (nib y p))
  | 0, _, _ => rfl
  | m + 1, x, y => by
    have hx : (x >>> (4 * (y % 16))) % 16 = nib x (nib y 0) := by
      simp only [nib, pow_zero, Nat.div_one, Nat.shiftRight_eq_div_pow, pow_mul]
      rfl
    rw [pmul, pmul_eq m x (y / 16), List.range_succ_eq_map, List.map_cons, List.map_map, packL, hx]
    congr 2
    refine congrArg packL (List.map_congr_left fun p _ => ?_)
    simp only [Function.comp, nib_succ]

theorem img_pt (a : Wr n) (j : Fin n) (c : ZMod 2) :
    img a (2 * j.val + c.val) = 2 * (a.perm j).val + (c + a.vec (a.perm j)).val := by
  have hc : c.val < 2 := ZMod.val_lt c
  have h2 : (2 * j.val + c.val) / 2 < n := by omega
  have hj : (⟨(2 * j.val + c.val) / 2, h2⟩ : Fin n) = j := Fin.ext (by simp only; omega)
  have h4 : (2 * j.val + c.val) % 2 = c.val := by omega
  have h3 : (((2 * j.val + c.val) % 2 : Nat) : ZMod 2) = c := by
    rw [h4]
    exact ZMod.natCast_zmod_val c
  unfold img
  rw [dif_pos h2, hj, h3]

theorem exists_pt {p : Nat} (hp : p < 2 * n) : ∃ (j : Fin n) (c : ZMod 2), p = 2 * j.val + c.val :=
  ⟨⟨p / 2, by omega⟩, ((p % 2 : Nat) : ZMod 2), by simp only [ZMod.val_natCast, Nat.mod_mod]; omega⟩

theorem img_lt (a : Wr n) {p : Nat} (hp : p < 2 * n) : img a p < 2 * n := by
  obtain ⟨j, c, rfl⟩ := exists_pt hp
  rw [img_pt]
  have := (a.perm j).isLt
  have := ZMod.val_lt (c + a.vec (a.perm j))
  omega

theorem img_mul (a b : Wr n) {p : Nat} (hp : p < 2 * n) : img (a * b) p = img a (img b p) := by
  obtain ⟨j, c, rfl⟩ := exists_pt hp
  have hperm : (a * b).perm j = a.perm (b.perm j) := rfl
  have hvec : (a * b).vec (a.perm (b.perm j)) = a.vec (a.perm (b.perm j)) + b.vec (b.perm j) := by
    rw [Wr.mul_vec, Equiv.symm_apply_apply]
  have hz : c + (a.vec (a.perm (b.perm j)) + b.vec (b.perm j)) =
      c + b.vec (b.perm j) + a.vec (a.perm (b.perm j)) := by ring
  rw [img_pt, img_pt, img_pt, hperm, hvec, hz]

theorem nib_enc (hn : n ≤ 8) (a : Wr n) {p : Nat} (hp : p < 2 * n) : nib (enc a) p = img a p := by
  unfold enc
  rw [nib_packL]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_range, hp]
  · intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    have := img_lt a hq
    omega

theorem enc_mul (hn : n ≤ 8) (a b : Wr n) : enc (a * b) = pmul (2 * n) (enc a) (enc b) := by
  rw [pmul_eq]
  conv_lhs => unfold enc
  congr 1
  refine List.map_congr_left fun p hp => ?_
  have hp' : p < 2 * n := List.mem_range.mp hp
  rw [nib_enc hn b hp', nib_enc hn a (img_lt b hp'), img_mul a b hp']

theorem enc_injective (hn : n ≤ 8) {a b : Wr n} (h : enc a = enc b) : a = b := by
  have hi : ∀ j : Fin n, img a (2 * j.val + (0 : ZMod 2).val) = img b (2 * j.val + (0 : ZMod 2).val) := by
    intro j
    have hlt : 2 * j.val + (0 : ZMod 2).val < 2 * n := by
      have := ZMod.val_lt (0 : ZMod 2)
      omega
    rw [← nib_enc hn a hlt, ← nib_enc hn b hlt, h]
  have hperm : ∀ j, a.perm j = b.perm j := by
    intro j
    have h0 := hi j
    rw [img_pt, img_pt] at h0
    have := ZMod.val_lt (0 + a.vec (a.perm j))
    have := ZMod.val_lt (0 + b.vec (b.perm j))
    exact Fin.ext (by omega)
  have hvec : ∀ j, a.vec (a.perm j) = b.vec (a.perm j) := by
    intro j
    have h0 := hi j
    rw [img_pt, img_pt, ← hperm j] at h0
    have h1 : (0 + a.vec (a.perm j)).val = (0 + b.vec (a.perm j)).val := by omega
    simpa using ZMod.val_injective _ h1
  refine Wr.ext (funext fun x => ?_) (Equiv.ext hperm)
  have := hvec (a.perm.symm x)
  simpa using this

theorem tabOK_sound {N : Nat} {T Ti : List Nat} {g : Nat → Wr n} (h : tabOK N T Ti g = true) :
    (∀ i < N, T.getD i 0 = enc (g i)) ∧ ∀ i < N, Ti.getD i 0 = enc (g i)⁻¹ := by
  have h' := List.all_eq_true.mp h
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := h' i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true] at this
    exact Nat.eq_of_beq_eq_true this.1
  · have := h' i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true] at this
    exact Nat.eq_of_beq_eq_true this.2

theorem pword_eq (hn : n ≤ 8) {N e : Nat} {T : List Nat} {g : Nat → Wr n} (he : e = enc (1 : Wr n))
    (hT : ∀ i < N, T.getD i 0 = enc (g i)) (k : Nat) :
    ∀ W : List Nat, (∀ l ∈ W, 2 * k + l < N) →
      pword (2 * n) e T k W = enc ((W.map fun l => g (2 * k + l)).prod)
  | [], _ => by simp [pword, he]
  | l :: W, h => by
    have ih := pword_eq hn he hT k W fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have hc : pword (2 * n) e T k (l :: W) = pmul (2 * n) (T.getD (2 * k + l) 0) (pword (2 * n) e T k W) :=
      rfl
    rw [hc, ih, hT _ (h l List.mem_cons_self), List.map_cons, List.prod_cons, enc_mul hn]

theorem rowIdx_sound {N : Nat} {d : Nat × Nat × Nat × Nat × List Nat} (h : rowIdx N d = true) :
    d.1 < N ∧ 2 * d.2.1 + d.2.2.1 < N ∧ ∀ l ∈ d.2.2.2.2, 2 * d.2.2.2.1 + l < N := by
  simp only [rowIdx, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem rowL_eq (hn : n ≤ 8) {N : Nat} {T Ti : List Nat} {g : Nat → Wr n}
    (hT : ∀ i < N, T.getD i 0 = enc (g i)) (hTi : ∀ i < N, Ti.getD i 0 = enc (g i)⁻¹)
    {d : Nat × Nat × Nat × Nat × List Nat} (h1 : d.1 < N) (h2 : 2 * d.2.1 + d.2.2.1 < N) :
    rowL (2 * n) T Ti d = enc (g d.1 * g (2 * d.2.1 + d.2.2.1) * (g d.1)⁻¹) := by
  rw [rowL, hT _ h1, hT _ h2, hTi _ h1, enc_mul hn, enc_mul hn]

theorem rowOK_sound (hn : n ≤ 8) {N e : Nat} {T Ti : List Nat} {g : Nat → Wr n}
    (he : e = enc (1 : Wr n)) (hT : ∀ i < N, T.getD i 0 = enc (g i))
    (hTi : ∀ i < N, Ti.getD i 0 = enc (g i)⁻¹) {d : Nat × Nat × Nat × Nat × List Nat}
    (h : rowOK (2 * n) e N T Ti d = true) :
    g d.1 * g (2 * d.2.1 + d.2.2.1) * (g d.1)⁻¹ =
      (d.2.2.2.2.map fun l => g (2 * d.2.2.2.1 + l)).prod := by
  simp only [rowOK, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := rowIdx_sound h.1
  apply enc_injective hn
  rw [← rowL_eq hn hT hTi h1 h2, ← pword_eq hn he hT _ _ h3]
  exact Nat.eq_of_beq_eq_true h.2

theorem rowPiOK_sound (hn : n ≤ 8) {N e pe : Nat} {T Ti : List Nat} {g : Nat → Wr n} {π : Wr n}
    (he : e = enc (1 : Wr n)) (hpe : pe = enc π) (hT : ∀ i < N, T.getD i 0 = enc (g i))
    (hTi : ∀ i < N, Ti.getD i 0 = enc (g i)⁻¹) {d : Nat × Nat × Nat × Nat × List Nat}
    (h : rowPiOK (2 * n) e pe N T Ti d = true) :
    g d.1 * g (2 * d.2.1 + d.2.2.1) * (g d.1)⁻¹ =
        (d.2.2.2.2.map fun l => g (2 * d.2.2.2.1 + l)).prod ∨
      g d.1 * g (2 * d.2.1 + d.2.2.1) * (g d.1)⁻¹ =
        (d.2.2.2.2.map fun l => g (2 * d.2.2.2.1 + l)).prod * π := by
  simp only [rowPiOK, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := rowIdx_sound h.1
  rw [rowL_eq hn hT hTi h1 h2, pword_eq hn he hT _ _ h3] at h
  rcases h.2 with h4 | h4
  · exact Or.inl (enc_injective hn (Nat.eq_of_beq_eq_true h4))
  · rw [hpe, ← enc_mul hn] at h4
    exact Or.inr (enc_injective hn (Nat.eq_of_beq_eq_true h4))

variable {α : Type*}

theorem chainProds_length : ∀ L : List (List (Equiv.Perm α)),
    (chainProds L).length = (L.map List.length).prod
  | [] => rfl
  | E :: L => by
    simp [chainProds, List.length_flatMap, chainProds_length L]

theorem chainProds_fix {b : α} : ∀ L : List (List (Equiv.Perm α)),
    (∀ E ∈ L, ∀ e ∈ E, e b = b) → ∀ g ∈ chainProds L, g b = b
  | [], _, g, hg => by
    simp only [chainProds, List.mem_singleton] at hg
    simp [hg]
  | E :: L, h, g, hg => by
    simp only [chainProds, List.mem_flatMap, List.mem_map] at hg
    obtain ⟨e, he, g', hg', rfl⟩ := hg
    rw [Equiv.Perm.mul_apply, chainProds_fix L (fun E' hE' => h E' (List.mem_cons_of_mem _ hE')) g' hg',
      h E List.mem_cons_self e he]

theorem chainProds_mem (H : Subgroup (Equiv.Perm α)) : ∀ L : List (List (Equiv.Perm α)),
    (∀ E ∈ L, ∀ e ∈ E, e ∈ H) → ∀ g ∈ chainProds L, g ∈ H
  | [], _, g, hg => by
    simp only [chainProds, List.mem_singleton] at hg
    rw [hg]
    exact H.one_mem
  | E :: L, h, g, hg => by
    simp only [chainProds, List.mem_flatMap, List.mem_map] at hg
    obtain ⟨e, he, g', hg', rfl⟩ := hg
    exact H.mul_mem (h E List.mem_cons_self e he)
      (chainProds_mem H L (fun E' hE' => h E' (List.mem_cons_of_mem _ hE')) g' hg')

variable [DecidableEq α] {mem : Equiv.Perm α → Bool}

theorem chainOK_mem : ∀ (bs : List α) (L : List (List (Equiv.Perm α))),
    chainOK mem bs L = true → ∀ E ∈ L, ∀ e ∈ E, mem e = true
  | _, [], _ => by simp
  | [], _ :: _, h => by simp [chainOK] at h
  | b :: bs, E :: L, h => by
    simp only [chainOK, Bool.and_eq_true, List.all_eq_true] at h
    intro E' hE' e he
    rcases List.mem_cons.mp hE' with rfl | hE'
    · exact h.1.1.1 e he
    · exact chainOK_mem bs L h.2 E' hE' e he

theorem chainOK_nodup : ∀ (bs : List α) (L : List (List (Equiv.Perm α))),
    chainOK mem bs L = true → (chainProds L).Nodup
  | _, [], _ => by simp [chainProds]
  | [], _ :: _, h => by simp [chainOK] at h
  | b :: bs, E :: L, h => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨_, hE⟩, hfix⟩, hrest⟩ := h
    have ih := chainOK_nodup bs L hrest
    have hfix' : ∀ g ∈ chainProds L, g b = b :=
      chainProds_fix L fun E' hE' e he => hfix E' hE' e he
    rw [chainProds, List.nodup_flatMap]
    refine ⟨fun e _ => ih.map (mul_right_injective e), ?_⟩
    have hp : E.Pairwise fun e e' => e b ≠ e' b := List.pairwise_map.mp hE
    refine hp.imp fun {e e'} hne => ?_
    intro x hx hx'
    simp only [List.mem_map] at hx hx'
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨g', hg', hgg⟩ := hx'
    apply hne
    have h1 := congrArg (fun σ : Equiv.Perm α => σ b) hgg
    simp only [Equiv.Perm.mul_apply, hfix' g hg, hfix' g' hg'] at h1
    exact h1.symm

theorem le_card_of_chainOK [Fintype α] (H : Subgroup (Equiv.Perm α)) (S : Finset (Equiv.Perm α))
    (hS : ∀ g ∈ H, g ∈ S) (hmem : ∀ σ, mem σ = true → σ ∈ H) (bs : List α)
    (L : List (List (Equiv.Perm α))) (h : chainOK mem bs L = true) :
    (L.map List.length).prod ≤ S.card := by
  rw [← chainProds_length, ← List.toFinset_card_of_nodup (chainOK_nodup bs L h)]
  refine Finset.card_le_card fun g hg => hS g ?_
  rw [List.mem_toFinset] at hg
  exact chainProds_mem H L (fun E hE e he => hmem e (chainOK_mem bs L h E hE e he)) g hg

end CFSG.KC.WrTwin

end
