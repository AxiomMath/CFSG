module

public import Certificates.Data.Kernel.KeyTree
public import Mathlib.Logic.Relation

public section

namespace CFSG.KC.KeyTree

def KT.toList : KT → List (Nat × Nat)
  | .leaf => []
  | .node l k v r => l.toList ++ (k, v) :: r.toList

private theorem bAnd_eq_true {a b : Bool}
    (h : (Bool.rec (motive := fun _ => Bool) false b a : Bool) = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h (by simp)
  · exact ⟨rfl, h⟩

theorem KT.find_mem : ∀ (t : KT) {x v : Nat}, t.find x = v + 1 → (x, v) ∈ t.toList
  | .leaf, _, _, h => absurd h (by simp [KT.find])
  | .node l k w r, x, v, h => by
    have e : (KT.node l k w r).find x = nIf(Nat.blt x k, l.find x, nIf(Nat.beq x k,
        Nat.succ w, r.find x)) := rfl
    rw [e] at h
    simp only [KT.toList, List.mem_append, List.mem_cons, Prod.mk.injEq]
    cases hb : Nat.blt x k
    · rw [hb] at h
      cases hc : Nat.beq x k
      · rw [hc] at h
        exact Or.inr (Or.inr (KT.find_mem r h))
      · rw [hc] at h
        exact Or.inr (Or.inl ⟨Nat.eq_of_beq_eq_true hc, (Nat.succ.inj h).symm⟩)
    · rw [hb] at h
      exact Or.inl (KT.find_mem l h)

private theorem go_succ_succ (d m : Nat) (l : List (Nat × Nat)) : KT.go (d + 1) (m + 1) l =
    Prod.rec (motive := fun _ => KT × List (Nat × Nat))
      (fun lt r1 =>
        List.rec (motive := fun _ => KT × List (Nat × Nat)) (lt, r1)
          (fun kv r2 _ =>
            Prod.rec (motive := fun _ => KT × List (Nat × Nat))
              (fun rt r3 => (KT.node lt kv.1 kv.2 rt, r3))
              (KT.go d (Nat.sub (Nat.sub (m + 1) 1) (Nat.div (Nat.sub (m + 1) 1) 2)) r2))
          r1)
      (KT.go d (Nat.div (Nat.sub (m + 1) 1) 2) l) := rfl

theorem KT.go_append : ∀ (d n : Nat) (l : List (Nat × Nat)),
    (KT.go d n l).1.toList ++ (KT.go d n l).2 = l
  | 0, _, _ => rfl
  | _ + 1, 0, _ => rfl
  | d + 1, m + 1, l => by
    rw [go_succ_succ]
    have h1 := KT.go_append d (Nat.div (Nat.sub (m + 1) 1) 2) l
    rcases hA : KT.go d (Nat.div (Nat.sub (m + 1) 1) 2) l with ⟨lt, r1⟩
    rw [hA] at h1
    cases r1 with
    | nil => exact h1
    | cons kv r2 =>
      have h2 := KT.go_append d (Nat.sub (Nat.sub (m + 1) 1) (Nat.div (Nat.sub (m + 1) 1) 2)) r2
      rcases hB : KT.go d (Nat.sub (Nat.sub (m + 1) 1) (Nat.div (Nat.sub (m + 1) 1) 2)) r2 with
        ⟨rt, r3⟩
      rw [hB] at h2
      simp only [KT.toList, List.append_assoc, List.cons_append] at h1 h2 ⊢
      rw [hB]
      dsimp only
      rw [h2]
      exact h1

theorem KT.find_ofList {n x v : Nat} {l : List (Nat × Nat)} (h : (KT.ofList n l).find x = v + 1) :
    (x, v) ∈ l := by
  have e := KT.go_append 64 n l
  rw [← e]
  exact List.mem_append_left _ (KT.find_mem _ h)

theorem depths_eq (rs : List (Nat × Nat × Nat × Nat)) : depths rs = rs.map fun r => (r.1, r.2.1) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change (r.1, r.2.1) :: depths rs = _
    rw [ih, List.map_cons]

theorem reachK_all {isRoot : Nat → Bool} {edge : Nat → Nat → Nat → Bool} {M : KT}
    {rs : List (Nat × Nat × Nat × Nat)} (h : reachK isRoot edge M rs = true) :
    ∀ r ∈ rs, reachOK isRoot edge M r = true := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have h' := bAnd_eq_true (a := reachOK isRoot edge M r) (b := reachK isRoot edge M rs) h
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | hr'
    · exact h'.1
    · exact ih h'.2 r' hr'

theorem reach_sound {isRoot : Nat → Bool} {edge : Nat → Nat → Nat → Bool}
    {rs : List (Nat × Nat × Nat × Nat)} {n : Nat}
    (h : ∀ r ∈ rs, reachOK isRoot edge (KT.ofList n (depths rs)) r = true) :
    ∀ r ∈ rs, ∃ x, isRoot x = true ∧
      Relation.ReflTransGen (fun a b => ∃ g, edge g a b = true) x r.1 := by
  suffices H : ∀ d, ∀ r ∈ rs, r.2.1 ≤ d → ∃ x, isRoot x = true ∧
      Relation.ReflTransGen (fun a b => ∃ g, edge g a b = true) x r.1 from
    fun r hr => H r.2.1 r hr (Nat.le_refl _)
  intro d
  induction d with
  | zero =>
    rintro ⟨v, dd, g, p⟩ hr hd
    obtain rfl : dd = 0 := Nat.le_zero.mp hd
    exact ⟨v, h _ hr, Relation.ReflTransGen.refl⟩
  | succ d ih =>
    rintro ⟨v, dd, g, p⟩ hr hd
    have hc := h _ hr
    cases dd with
    | zero => exact ⟨v, hc, Relation.ReflTransGen.refl⟩
    | succ e =>
      have hc' := bAnd_eq_true hc
      have hc'' := bAnd_eq_true hc'.2
      obtain ⟨d', hd'⟩ : ∃ d', (KT.ofList n (depths rs)).find p = d' + 1 :=
        Nat.exists_eq_add_one.mpr (by simpa [Nat.blt_eq] using hc'.1)
      have hlt : d' < e + 1 := by
        have := hc''.1
        rw [hd'] at this
        simpa [Nat.blt_eq] using this
      have hm := KT.find_ofList hd'
      rw [depths_eq] at hm
      obtain ⟨r', hr', hr'e⟩ := List.mem_map.mp hm
      have hd2 : e + 1 ≤ d + 1 := hd
      obtain ⟨x, hx, hxp⟩ := ih r' hr' (by rw [(Prod.mk.inj hr'e).2]; omega)
      rw [(Prod.mk.inj hr'e).1] at hxp
      exact ⟨x, hx, Relation.ReflTransGen.tail hxp ⟨g, hc''.2⟩⟩

end CFSG.KC.KeyTree

end
