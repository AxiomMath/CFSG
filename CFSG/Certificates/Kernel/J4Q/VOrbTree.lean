module

public import Certificates.Data.Kernel.J4Q.VOrb
public import Mathlib.Data.Finset.Card

public section

namespace CFSG.KC.J4Q.VOrbTree

open CFSG.KC.Loop CFSG.KC.LQT.Syl
open CFSG.KC.LQT.T2 (spanLt mergeK passK)

private theorem andB_true (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

private theorem eqLK_sound : ∀ {xs ys : List Nat}, eqLK xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => (Bool.false_ne_true h).elim
  | _ :: _, [], h => (Bool.false_ne_true h).elim
  | x :: xs, y :: ys, h => by
    change andB (Nat.beq x y) (eqLK xs ys) = true at h
    obtain ⟨hxy, htail⟩ := (andB_true _ _).1 h
    rw [Nat.eq_of_beq_eq_true hxy, eqLK_sound htail]

private theorem spanLt_split (a : Nat) (ys : List Nat)
    (k : List Nat → List Nat → List Nat) (acc : List Nat) :
    ∃ p r, p ++ r = acc.reverse ++ ys ∧ spanLt a ys k acc = k p r := by
  induction ys generalizing acc with
  | nil => exact ⟨acc.reverse, [], by simp, rfl⟩
  | cons y ys ih =>
    cases hb : Nat.blt y a with
    | false =>
      refine ⟨acc.reverse, y :: ys, rfl, ?_⟩
      simp only [spanLt, hb]
    | true =>
      obtain ⟨p, r, hpr, he⟩ := ih (y :: acc)
      refine ⟨p, r, ?_, ?_⟩
      · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hpr
      · simpa only [spanLt, hb] using he

private theorem mem_mergeK (x : Nat) (xs ys : List Nat) :
    x ∈ mergeK xs ys ↔ x ∈ xs ∨ x ∈ ys := by
  induction xs generalizing ys with
  | nil => simp only [mergeK, List.not_mem_nil, false_or]
  | cons a xs ih =>
    change x ∈ spanLt a ys (fun p r => p ++ a :: mergeK xs r) [] ↔
      x ∈ a :: xs ∨ x ∈ ys
    obtain ⟨p, r, hpr, he⟩ := spanLt_split a ys (fun p r => p ++ a :: mergeK xs r) []
    have hys : p ++ r = ys := by simpa only [List.reverse_nil, List.nil_append] using hpr
    rw [he, ← hys]
    simp only [List.mem_append, List.mem_cons, ih]
    tauto

private theorem mem_flatten_passK (x : Nat) (rs : List (List Nat)) :
    x ∈ (passK rs).flatten ↔ x ∈ rs.flatten := by
  let go : List (List Nat) → Option (List Nat) → List (List Nat) := fun rs =>
    List.rec (motive := fun _ => Option (List Nat) → List (List Nat))
      (fun o => Option.rec [] (fun a => [a]) o)
      (fun r _ ih o => Option.rec (ih (some r))
        (fun a => mergeK a r :: ih none) o) rs
  have hgo : ∀ rs o, x ∈ (go rs o).flatten ↔ x ∈ rs.flatten ∨ x ∈ o.getD [] := by
    intro rs
    induction rs with
    | nil => intro o; cases o <;> simp [go]
    | cons r rs ih =>
      intro o
      cases o with
      | none =>
        change x ∈ (go rs (some r)).flatten ↔ x ∈ (r :: rs).flatten ∨
          x ∈ (none : Option (List Nat)).getD []
        rw [ih]
        simp only [Option.getD_some, Option.getD_none, List.not_mem_nil, or_false,
          List.flatten_cons, List.mem_append]
        tauto
      | some a =>
        change x ∈ (mergeK a r :: go rs none).flatten ↔ x ∈ (r :: rs).flatten ∨
          x ∈ (some a : Option (List Nat)).getD []
        rw [List.flatten_cons, List.mem_append, mem_mergeK, ih]
        simp only [Option.getD_some, Option.getD_none, List.not_mem_nil, or_false,
          List.flatten_cons, List.mem_append]
        tauto
  change x ∈ (go rs none).flatten ↔ x ∈ rs.flatten
  simpa only [Option.getD_none, List.not_mem_nil, or_false] using hgo rs none

private theorem mem_sortN (x : Nat) (xs : List Nat) : x ∈ sortN xs ↔ x ∈ xs := by
  let runs (n : Nat) := Nat.rec (motive := fun _ => List (List Nat))
    (xs.map fun x => [x]) (fun _ ih => passK ih) n
  have hbase : (xs.map fun x => [x]).flatten = xs := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      simpa only [List.map_cons, List.flatten_cons, List.singleton_append] using
        (congrArg (List.cons a) ih)
  have hrun : ∀ n, x ∈ (runs n).flatten ↔ x ∈ xs := by
    intro n
    induction n with
    | zero => change x ∈ (xs.map fun x => [x]).flatten ↔ x ∈ xs; rw [hbase]
    | succ n ih =>
      change x ∈ (passK (runs n)).flatten ↔ x ∈ xs
      rw [mem_flatten_passK, ih]
  exact hrun 17

private theorem mem_dropLt {a x : Nat} {ys : List Nat} : x ∈ dropLt a ys → x ∈ ys := by
  induction ys with
  | nil => simp only [dropLt, List.not_mem_nil, imp_self]
  | cons y ys ih =>
    intro hx
    cases hb : Nat.blt y a with
    | false => simpa only [dropLt, hb] using hx
    | true =>
      have ht : x ∈ dropLt a ys := by simpa only [dropLt, hb] using hx
      exact List.mem_cons_of_mem y (ih ht)

private theorem diffS_cover {xs ys : List Nat} {x : Nat} (hx : x ∈ xs) :
    x ∈ diffS xs ys ∨ x ∈ ys := by
  induction xs generalizing ys with
  | nil => exact (List.not_mem_nil hx).elim
  | cons a xs ih =>
    cases hd : dropLt a ys with
    | nil =>
      have he : diffS (a :: xs) ys = a :: diffS xs [] := by simp only [diffS, hd]
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inl (he.symm ▸ List.mem_cons_self)
      · rcases ih hx (ys := []) with hr | hr
        · exact Or.inl (he.symm ▸ List.mem_cons_of_mem a hr)
        · exact (List.not_mem_nil hr).elim
    | cons b bs =>
      have hsub : ∀ z ∈ b :: bs, z ∈ ys := by
        intro z hz
        exact mem_dropLt (hd.symm ▸ hz)
      cases hb : Nat.beq b a with
      | false =>
        have he : diffS (a :: xs) ys = a :: diffS xs (b :: bs) := by
          simp only [diffS, hd, hb]
        rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inl (he.symm ▸ List.mem_cons_self)
        · rcases ih hx (ys := b :: bs) with hr | hr
          · exact Or.inl (he.symm ▸ List.mem_cons_of_mem a hr)
          · exact Or.inr (hsub x hr)
      | true =>
        have hba : b = a := Nat.eq_of_beq_eq_true hb
        have he : diffS (a :: xs) ys = diffS xs (b :: bs) := by
          simp only [diffS, hd, hb]
        rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inr (hsub _ (by rw [hba]; exact List.mem_cons_self))
        · rcases ih hx (ys := b :: bs) with hr | hr
          · exact Or.inl (he.symm ▸ hr)
          · exact Or.inr (hsub x hr)

private theorem mem_dedupS {xs : List Nat} {x : Nat} : x ∈ dedupS xs ↔ x ∈ xs := by
  let go : List Nat → Option Nat → List Nat := fun l =>
    List.rec (motive := fun _ => Option Nat → List Nat) (fun _ => [])
      (fun y _ ih o => Option.rec (y :: ih (some y))
        (fun a => Bool.rec (y :: ih (some y)) (ih (some y)) (Nat.beq y a)) o) l
  have hgo : ∀ l o, (x ∈ go l o ∨ o = some x) ↔ (x ∈ l ∨ o = some x) := by
    intro l
    induction l with
    | nil => intro o; simp [go]
    | cons y ys ih =>
      intro o
      have ht := ih (some y)
      simp only [Option.some.injEq] at ht
      have hxy : x = y ↔ y = x := eq_comm
      cases o with
      | none =>
        change (x ∈ y :: go ys (some y) ∨ (none : Option Nat) = some x) ↔
          (x ∈ y :: ys ∨ (none : Option Nat) = some x)
        simp only [List.mem_cons, reduceCtorEq, or_false]
        tauto
      | some a =>
        change (x ∈ Bool.rec (motive := fun _ => List Nat) (y :: go ys (some y)) (go ys (some y)) (Nat.beq y a) ∨
          some a = some x) ↔ (x ∈ y :: ys ∨ some a = some x)
        cases hb : Nat.beq y a with
        | false =>
          simp only [List.mem_cons, Option.some.injEq]
          tauto
        | true =>
          have hya : y = a := Nat.eq_of_beq_eq_true hb
          simp only [List.mem_cons, Option.some.injEq]
          subst a
          tauto
  change x ∈ go xs none ↔ x ∈ xs
  simpa only [reduceCtorEq, or_false] using hgo xs none

theorem inSK_sound {pc SP : List Nat} (h : inSK pc SP = true) :
    ∀ x ∈ pc, x ∈ SP := by
  have he : diffS (sortN pc) SP = [] := eqLK_sound h
  intro x hx
  rcases diffS_cover (ys := SP) ((mem_sortN x pc).2 hx) with hd | hs
  · rw [he] at hd
    exact (List.not_mem_nil hd).elim
  · exact hs

private theorem diff_fold_cover {sc : List Nat} {Pch : List (List Nat)} {x : Nat}
    (hx : x ∈ sc) :
    x ∈ Pch.foldl (fun acc pc => diffS acc (sortN pc)) sc ∨ x ∈ Pch.flatten := by
  induction Pch generalizing sc with
  | nil => exact Or.inl hx
  | cons pc pcs ih =>
    rcases diffS_cover (ys := sortN pc) hx with hd | hp
    · rcases ih hd with hf | ht
      · exact Or.inl hf
      · exact Or.inr (List.mem_flatten.2 (by
          obtain ⟨p, hpcs, hx⟩ := List.mem_flatten.1 ht
          exact ⟨p, List.mem_cons_of_mem pc hpcs, hx⟩))
    · exact Or.inr (List.mem_flatten.2 ⟨pc, List.mem_cons_self, (mem_sortN x pc).1 hp⟩)

theorem spInK_sound {sc : List Nat} {Pch : List (List Nat)}
    (h : spInK sc Pch = true) : ∀ x ∈ sc, x ∈ Pch.flatten := by
  have he : Pch.foldl (fun acc pc => diffS acc (sortN pc)) sc = [] := eqLK_sound h
  intro x hx
  rcases diff_fold_cover hx with hd | hp
  · rw [he] at hd
    exact (List.not_mem_nil hd).elim
  · exact hp

theorem checked_membership {Pch SPch : List (List Nat)}
    (hin : ∀ pc ∈ Pch, inSK pc SPch.flatten = true)
    (hsp : ∀ sc ∈ SPch, spInK sc Pch = true) :
    ∀ x, x ∈ Pch.flatten ↔ x ∈ SPch.flatten := by
  intro x
  constructor
  · intro hx
    obtain ⟨pc, hpc, hx⟩ := List.mem_flatten.1 hx
    exact inSK_sound (hin pc hpc) x hx
  · intro hx
    obtain ⟨sc, hsc, hx⟩ := List.mem_flatten.1 hx
    exact spInK_sound (hsp sc hsc) x hx

theorem sincK_spec {l : List Nat} {b : Nat} (h : sincK l b = true) :
    l.Pairwise (fun x y => x < y) ∧ ∀ x ∈ l, b < x := by
  induction l generalizing b with
  | nil => exact ⟨List.Pairwise.nil, fun _ hx => (List.not_mem_nil hx).elim⟩
  | cons a l ih =>
    change andB (Nat.blt b a) (sincK l a) = true at h
    obtain ⟨hba, ht⟩ := (andB_true _ _).1 h
    have hlt : b < a := by simpa only [Nat.blt_eq] using hba
    obtain ⟨hp, hb⟩ := ih ht
    refine ⟨List.pairwise_cons.2 ⟨hb, hp⟩, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hlt
    · exact Nat.lt_trans hlt (hb x hx)

theorem checked_points_spec {Pch SPch : List (List Nat)} {cap : Nat}
    (hlen : Pch.flatten.length = cap) (hsl : SPch.flatten.length = cap)
    (hsinc : sincK SPch.flatten 0 = true)
    (hsp : ∀ sc ∈ SPch, spInK sc Pch = true) :
    (Pch.flatten).Perm SPch.flatten ∧ (Pch.flatten).Nodup ∧
      (Pch.flatten.toFinset).card = cap := by
  have hn : SPch.flatten.Nodup := (sincK_spec hsinc).1.imp Nat.ne_of_lt
  have hsub : SPch.flatten ⊆ Pch.flatten := by
    intro x hx
    obtain ⟨sc, hsc, hx⟩ := List.mem_flatten.1 hx
    exact spInK_sound (hsp sc hsc) x hx
  have hp : SPch.flatten.Perm Pch.flatten :=
    (List.subperm_of_subset hn hsub).perm_of_length_le (by rw [hlen, hsl])
  have hnP : Pch.flatten.Nodup := hp.nodup_iff.1 hn
  exact ⟨hp.symm, hnP, (List.toFinset_card_of_nodup hnP).trans hlen⟩

theorem clK_sound {Rs : List (List Nat)} {pc SP : List Nat}
    (h : clK Rs pc SP = true) :
    ∀ x ∈ pc, ∀ rs ∈ Rs, vecLJ x rs ∈ SP := by
  have he : diffS (dedupS (sortN (imgsK Rs pc))) SP = [] := eqLK_sound h
  intro x hx rs hrs
  have himg : vecLJ x rs ∈ imgsK Rs pc := by
    exact List.mem_flatten.2 ⟨Rs.map (fun rs => vecLJ x rs),
      List.mem_map.2 ⟨x, hx, rfl⟩, List.mem_map.2 ⟨rs, hrs, rfl⟩⟩
  have hd : vecLJ x rs ∈ dedupS (sortN (imgsK Rs pc)) :=
    mem_dedupS.2 ((mem_sortN _ _).2 himg)
  rcases diffS_cover (ys := SP) hd with hd | hp
  · rw [he] at hd
    exact (List.not_mem_nil hd).elim
  · exact hp

end CFSG.KC.J4Q.VOrbTree
