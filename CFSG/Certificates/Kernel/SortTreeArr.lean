module

public import CFSG.Certificates.Kernel.SortTreeSound
public import CFSG.Certificates.Kernel.MonsterB.PermBfsSound
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound

public section

namespace CFSG.KC.SortTree

open CFSG.KC.Bfs CFSG.Monster.B.TwoA.Census CFSG.KLie.CT

section Transfer

variable {β : Type} {act : ℕ → β → β} {actN : ℕ → ℕ → ℕ} {ng : ℕ} {valid : β → Prop}
  {key : β → ℕ} {dec : ℕ → β}

theorem reach_code (hdec : ∀ a, valid a → dec (key a) = a)
    (hact : ∀ k < ng, ∀ a, valid a → valid (act k a))
    (hcode : ∀ k < ng, ∀ a, valid a → actN k (key a) = key (act k a)) {root : β}
    (hroot : valid root) {c : ℕ} (h : Reach actN ng (key root) c) :
    valid (dec c) ∧ Reach act ng root (dec c) ∧ key (dec c) = c := by
  induction h with
  | root =>
    rw [hdec _ hroot]
    exact ⟨hroot, Reach.root, rfl⟩
  | step k hk _ ih =>
    obtain ⟨hv, hr, hk'⟩ := ih
    have hy := hact k hk _ hv
    rw [← hk', hcode k hk _ hv, hdec _ hy]
    exact ⟨hy, Reach.step k hk hr, rfl⟩

theorem code_reach (hact : ∀ k < ng, ∀ a, valid a → valid (act k a))
    (hcode : ∀ k < ng, ∀ a, valid a → actN k (key a) = key (act k a)) {root : β}
    (hroot : valid root) {a : β} (h : Reach act ng root a) :
    valid a ∧ Reach actN ng (key root) (key a) := by
  induction h with
  | root => exact ⟨hroot, Reach.root⟩
  | step k hk _ ih =>
    obtain ⟨hv, hr⟩ := ih
    refine ⟨hact k hk _ hv, ?_⟩
    rw [← hcode k hk _ hv]
    exact Reach.step k hk hr

theorem orbit_code [DecidableEq β] (hdec : ∀ a, valid a → dec (key a) = a)
    (hact : ∀ k < ng, ∀ a, valid a → valid (act k a))
    (hcode : ∀ k < ng, ∀ a, valid a → actN k (key a) = key (act k a)) {root : β}
    (hroot : valid root) {S' : Finset ℕ} (hS : ∀ c, Reach actN ng (key root) c ↔ c ∈ S') :
    (∀ a, Reach act ng root a ↔ a ∈ S'.image dec) ∧ (S'.image dec).card = S'.card ∧
      ∀ a ∈ S'.image dec, valid a := by
  have hrc := fun c (hc : c ∈ S') => reach_code hdec hact hcode hroot ((hS c).2 hc)
  refine ⟨fun a => ⟨fun h => ?_, fun h => ?_⟩, ?_, fun a h => ?_⟩
  · obtain ⟨hv, hr⟩ := code_reach hact hcode hroot h
    exact Finset.mem_image.2 ⟨_, (hS _).1 hr, hdec _ hv⟩
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
    exact (hrc c hc).2.1
  · refine Finset.card_image_of_injOn fun c1 h1 c2 h2 e => ?_
    rw [← (hrc c1 h1).2.2, ← (hrc c2 h2).2.2]
    exact congrArg key e
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
    exact (hrc c hc).1

end Transfer

@[expose] def decK (c : ℕ) : Array ℕ := ((List.range 24).map fun i => c / 24 ^ i % 24).toArray

theorem ofDigits_div_mod {b : ℕ} (hb : 0 < b) : ∀ (L : List ℕ), (∀ x ∈ L, x < b) →
    ∀ i (hi : i < L.length), Nat.ofDigits b L / b ^ i % b = L[i]
  | [], _, i, hi => absurd hi (Nat.not_lt_zero _)
  | x :: L, h, 0, _ => by
    rw [Nat.ofDigits_cons, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (h x (by simp))]
    rfl
  | x :: L, h, i + 1, hi => by
    rw [Nat.ofDigits_cons, pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hb,
      Nat.div_eq_of_lt (h x (by simp)), Nat.zero_add, List.getElem_cons_succ]
    exact ofDigits_div_mod hb L (fun y hy => h y (by simp [hy])) i (by simpa using hi)

theorem PermArr_toList_lt {a : Array ℕ} (h : PermArr a = true) : ∀ x ∈ a.toList, x < 24 := by
  have hs := PermArr_size h
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := PermArr_lt h ⟨i, by simpa [hs] using hi⟩
  rwa [getElem!_pos a i (by simpa using hi), ← Array.getElem_toList] at this

theorem akey_digit {a : Array ℕ} (h : PermArr a = true) {i : ℕ} (hi : i < 24) :
    akey a / 24 ^ i % 24 = a[i]! := by
  have hs := PermArr_size h
  rw [akey, ofDigits_div_mod (by norm_num) _ (PermArr_toList_lt h) i (by simpa [hs] using hi),
    Array.getElem_toList, getElem!_pos a i (by omega)]

theorem decK_akey {a : Array ℕ} (h : PermArr a = true) : decK (akey a) = a := by
  have hs := PermArr_size h
  apply Array.ext
  · simp [decK, hs]
  · intro i h1 h2
    simp only [decK, List.getElem_toArray, List.getElem_map, List.getElem_range]
    rw [akey_digit h (by simpa [decK] using h1), getElem!_pos a i h2]

@[expose] noncomputable def digK (c j : ℕ) : ℕ := Nat.mod (Nat.div c (Nat.pow 24 j)) 24

@[expose] noncomputable def ofDigK (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun x _ ih => Nat.add x (Nat.mul 24 ih)) L

@[expose] noncomputable def aconjK (G GI c : ℕ) : ℕ :=
  ofDigK ((List.range 24).map fun i => fget G (digK c (fget GI i 5)) 5)

theorem ofDigK_eq : ∀ L : List ℕ, ofDigK L = Nat.ofDigits 24 L
  | [] => rfl
  | x :: L => by
    change x + 24 * ofDigK L = _
    rw [ofDigK_eq L, Nat.ofDigits_cons]

theorem fget_perm {g : Array ℕ} (hg : PermArr g = true) {i : ℕ} (hi : i < 24) :
    fget (CFSG.KC.U6Orb.packL 5 g.toList) i 5 = g[i]! :=
  CFSG.KC.U6Orb.fget_packA (fun x hx => lt_trans (PermArr_toList_lt hg x hx) (by norm_num))
    (by rw [PermArr_size hg]; exact hi)

theorem aconjK_eq {g x : Array ℕ} (hg : PermArr g = true) (hx : PermArr x = true) :
    aconjK (CFSG.KC.U6Orb.packL 5 g.toList) (CFSG.KC.U6Orb.packL 5 (ainv g).toList) (akey x) =
      akey (aconj g x) := by
  have hgi := PermArr_ainv hg
  have hc := PermArr_aconj hg hx
  rw [aconjK, ofDigK_eq]
  conv_rhs => rw [akey]
  congr 1
  apply List.ext_getElem
  · simp [PermArr_size hc]
  · intro i h1 h2
    have hi : i < 24 := by simpa using h1
    rw [List.getElem_map, List.getElem_range, Array.getElem_toList,
      ← getElem!_pos (aconj g x) i (by simpa using h2)]
    have hj := PermArr_lt hgi ⟨i, hi⟩
    have hk := PermArr_lt hx ⟨_, hj⟩
    have e : digK (akey x) (ainv g)[i]! = akey x / 24 ^ (ainv g)[i]! % 24 := rfl
    rw [fget_perm hgi hi, e, akey_digit hx hj, fget_perm hg hk, aconj]
    rw [amul_getElem hgi ⟨i, hi⟩, amul_getElem hx ⟨_, hj⟩]

theorem bfsCert_tree {act : Array ℕ → Array ℕ → Array ℕ} {gens : Array (Array ℕ)}
    {root : Array ℕ} {actN : ℕ → ℕ → ℕ} {rec : ℕ → ℕ} {E : ℕ → ℕ → ℕ}
    {n wv wl wp B C B' C' fuel : ℕ}
    (hact : ∀ k < gens.size, ∀ x, PermArr x = true → PermArr (act gens[k]! x) = true)
    (hcode : ∀ k < gens.size, ∀ x, PermArr x = true → actN k (akey x) = akey (act gens[k]! x))
    (hroot : PermArr root = true) (hn : 0 < n) (hfuel : n ≤ fuel)
    (hT : treeOK actN gens.size (fun _ => true) (akey root) rec n wv wl wp B C = true)
    (hE : closeOK actN gens.size rec E n wv B' C' = true) :
    certOK act gens root (bfsCert act gens root fuel) = true ∧
      (bfsCert act gens root fuel).pts.size = n := by
  obtain ⟨S', hS', hcard, -, -, -⟩ := orbit_sound hn hT hE
  obtain ⟨hS, hc, hv⟩ := orbit_code (act := fun k x => act gens[k]! x)
    (valid := fun x => PermArr x = true) (key := akey) (dec := decK)
    (fun a ha => decK_akey ha) hact hcode hroot hS'
  obtain ⟨h1, -, h3, -⟩ := bfsCert_spec (fuel := fuel) _ hS hv (by rw [hc, hcard]; exact hfuel)
  exact ⟨h1, h3.trans (hc.trans hcard)⟩

end CFSG.KC.SortTree

end
