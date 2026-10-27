module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsSix

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

open Equiv CFSG.QuasithinUnique.Unc25K1.Six

structure RN (n : ℕ) where
  val : Vector (Fin n) n
  deriving DecidableEq

instance {n : ℕ} : Hashable (RN n) := ⟨fun x => hash x.val.toList⟩

namespace RN

variable {n : ℕ}

@[expose] def mul (x y : RN n) : RN n := ⟨Vector.ofFn fun i => x.val[(y.val[i] : Fin n)]⟩

@[expose] def one (n : ℕ) : RN n := ⟨Vector.ofFn fun i => i⟩

instance : Mul (RN n) := ⟨mul⟩

instance : One (RN n) := ⟨one n⟩

@[expose] def enc (σ : Perm (Fin n)) : RN n := ⟨Vector.ofFn fun i => σ i⟩

theorem ext {x y : RN n} (h : ∀ i : Fin n, x.val[i] = y.val[i]) : x = y := by
  cases x
  cases y
  congr 1
  exact Vector.ext fun i hi => h ⟨i, hi⟩

theorem enc_get (σ : Perm (Fin n)) (i : Fin n) : (enc σ).val[i] = σ i := by
  simp [enc]

theorem mul_get (x y : RN n) (i : Fin n) : (x * y).val[i] = x.val[(y.val[i] : Fin n)] := by
  show (Vector.ofFn fun i => x.val[(y.val[i] : Fin n)])[i] = _
  simp

theorem one_get (i : Fin n) : (1 : RN n).val[i] = i := by
  show (Vector.ofFn fun i => i)[i] = _
  simp

theorem enc_inj : Function.Injective (enc : Perm (Fin n) → RN n) := by
  intro σ τ h
  refine Equiv.ext fun i => ?_
  have := congrArg (fun r : RN n => r.val[i]) h
  simpa only [enc_get] using this

theorem enc_mul (σ τ : Perm (Fin n)) : enc (σ * τ) = enc σ * enc τ := by
  refine ext fun i => ?_
  rw [mul_get, enc_get, enc_get, enc_get, Perm.mul_apply]

theorem enc_one : enc (1 : Perm (Fin n)) = 1 := by
  refine ext fun i => ?_
  rw [one_get, enc_get]
  rfl

end RN

theorem rawIsEnc (n : ℕ) : IsEnc (RN.enc : Perm (Fin n) → RN n) :=
  ⟨RN.enc_inj, RN.enc_mul, RN.enc_one⟩

@[expose] def permOf (n : ℕ) (cs : List (List (Fin n))) : Perm (Fin n) := (cs.map List.formPerm).prod

section Closure

variable {R : Type} [Mul R] [One R] [DecidableEq R] [Hashable R]

def bfsStep (gens : List R) (S : Std.HashSet R) (F : List R) : Std.HashSet R × List R :=
  F.foldl (fun acc x => gens.foldl (fun (acc : Std.HashSet R × List R) g =>
    if acc.1.contains (x * g) then acc else (acc.1.insert (x * g), (x * g) :: acc.2)) acc) (S, [])

def bfsRun (gens : List R) : ℕ → Std.HashSet R × List R → Std.HashSet R × List R
  | 0, st => st
  | n + 1, st => bfsRun gens n (bfsStep gens st.1 st.2)

def bfsSet (gens : List R) (n : ℕ) : Std.HashSet R :=
  (bfsRun gens n ((∅ : Std.HashSet R).insert 1, [1])).1

omit [One R] in
theorem bfs_inner_sound (gens : List R) (P : R → Prop) (x : R) (hx : P x)
    (hP : ∀ y, P y → ∀ g ∈ gens, P (y * g)) :
    ∀ (l : List R) (acc : Std.HashSet R × List R),
      (∀ y ∈ acc.1, P y) → (∀ y ∈ acc.2, P y) → (∀ g ∈ l, g ∈ gens) →
      (∀ y ∈ (l.foldl (fun (acc : Std.HashSet R × List R) g =>
        if acc.1.contains (x * g) then acc else (acc.1.insert (x * g), (x * g) :: acc.2)) acc).1,
          P y) ∧
      (∀ y ∈ (l.foldl (fun (acc : Std.HashSet R × List R) g =>
        if acc.1.contains (x * g) then acc else (acc.1.insert (x * g), (x * g) :: acc.2)) acc).2,
          P y) := by
  intro l
  induction l with
  | nil => intro acc h1 h2 _; exact ⟨h1, h2⟩
  | cons g l ih =>
    intro acc h1 h2 hg
    simp only [List.foldl_cons]
    have hg' : g ∈ gens := hg g (List.mem_cons_self)
    have hl : ∀ g ∈ l, g ∈ gens := fun g' hg'' => hg g' (List.mem_cons_of_mem _ hg'')
    split_ifs with hc
    · exact ih acc h1 h2 hl
    · refine ih _ ?_ ?_ hl
      · intro y hy
        rw [Std.HashSet.mem_insert] at hy
        rcases hy with hy | hy
        · have : x * g = y := beq_iff_eq.mp hy
          rw [← this]
          exact hP x hx g hg'
        · exact h1 y hy
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hP x hx g hg'
        · exact h2 y hy

omit [One R] in
theorem bfsStep_sound (gens : List R) (P : R → Prop) (hP : ∀ y, P y → ∀ g ∈ gens, P (y * g))
    (S : Std.HashSet R) (F : List R) (hS : ∀ y ∈ S, P y) (hF : ∀ y ∈ F, P y) :
    (∀ y ∈ (bfsStep gens S F).1, P y) ∧ (∀ y ∈ (bfsStep gens S F).2, P y) := by
  unfold bfsStep
  have key : ∀ (l : List R) (acc : Std.HashSet R × List R), (∀ y ∈ acc.1, P y) →
      (∀ y ∈ acc.2, P y) → (∀ x ∈ l, P x) →
      (∀ y ∈ (l.foldl (fun acc x => gens.foldl (fun (acc : Std.HashSet R × List R) g =>
        if acc.1.contains (x * g) then acc else (acc.1.insert (x * g), (x * g) :: acc.2)) acc)
        acc).1, P y) ∧
      (∀ y ∈ (l.foldl (fun acc x => gens.foldl (fun (acc : Std.HashSet R × List R) g =>
        if acc.1.contains (x * g) then acc else (acc.1.insert (x * g), (x * g) :: acc.2)) acc)
        acc).2, P y) := by
    intro l
    induction l with
    | nil => intro acc h1 h2 _; exact ⟨h1, h2⟩
    | cons x l ih =>
      intro acc h1 h2 hl
      simp only [List.foldl_cons]
      have hx : P x := hl x (List.mem_cons_self)
      obtain ⟨h1', h2'⟩ := bfs_inner_sound gens P x hx hP gens acc h1 h2 (fun g hg => hg)
      exact ih _ h1' h2' (fun x' hx' => hl x' (List.mem_cons_of_mem _ hx'))
  exact key F (S, []) hS (fun y hy => absurd hy (List.not_mem_nil)) hF

omit [One R] in
theorem bfsRun_sound (gens : List R) (P : R → Prop) (hP : ∀ y, P y → ∀ g ∈ gens, P (y * g)) :
    ∀ (n : ℕ) (st : Std.HashSet R × List R), (∀ y ∈ st.1, P y) → (∀ y ∈ st.2, P y) →
      ∀ y ∈ (bfsRun gens n st).1, P y := by
  intro n
  induction n with
  | zero => intro st h1 _ y hy; exact h1 y hy
  | succ n ih =>
    intro st h1 h2 y hy
    obtain ⟨h1', h2'⟩ := bfsStep_sound gens P hP st.1 st.2 h1 h2
    exact ih _ h1' h2' y hy

theorem bfsSet_sound {G : Type*} [Group G] {enc : G → R} (h : IsEnc enc) (gens : List G) (n : ℕ) :
    ∀ r ∈ bfsSet (gens.map enc) n, ∃ x ∈ Subgroup.closure {g | g ∈ gens}, enc x = r := by
  have hP : ∀ y : R, (∃ x ∈ Subgroup.closure {g | g ∈ gens}, enc x = y) →
      ∀ g ∈ gens.map enc, ∃ x ∈ Subgroup.closure {g | g ∈ gens}, enc x = y * g := by
    rintro y ⟨x, hx, rfl⟩ g' hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    exact ⟨x * g, Subgroup.mul_mem _ hx (Subgroup.subset_closure hg), h.map_mul x g⟩
  have h1 : ∀ y ∈ ((∅ : Std.HashSet R).insert 1 : Std.HashSet R),
      ∃ x ∈ Subgroup.closure {g | g ∈ gens}, enc x = y := by
    intro y hy
    rw [Std.HashSet.mem_insert] at hy
    rcases hy with hy | hy
    · have : (1 : R) = y := beq_iff_eq.mp hy
      exact ⟨1, Subgroup.one_mem _, by rw [← this, h.map_one]⟩
    · have := Std.HashSet.contains_iff_mem.mpr hy
      simp [Std.HashSet.contains_empty] at this
  have h2 : ∀ y ∈ [(1 : R)], ∃ x ∈ Subgroup.closure {g | g ∈ gens}, enc x = y := by
    intro y hy
    rw [List.mem_singleton] at hy
    exact ⟨1, Subgroup.one_mem _, by rw [hy, h.map_one]⟩
  exact bfsRun_sound (gens.map enc) _ hP n _ h1 h2

def closedH (gens : List R) (S : Std.HashSet R) : Bool :=
  S.contains 1 && S.toList.all fun x => gens.all fun g => S.contains (x * g)

theorem closedH_spec {gens : List R} {S : Std.HashSet R} (h : closedH gens S = true) :
    (1 : R) ∈ S ∧ ∀ x ∈ S, ∀ g ∈ gens, x * g ∈ S := by
  simp only [closedH, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨Std.HashSet.contains_iff_mem.mp h.1, fun x hx g hg => ?_⟩
  exact Std.HashSet.contains_iff_mem.mp (by
    have := h.2 x (Std.HashSet.mem_toList.mpr hx)
    exact this g hg)

theorem mem_closure_iff_H {G : Type*} [Group G] [Finite G] {enc : G → R} (h : IsEnc enc)
    (gens : List G) (n : ℕ) (hc : closedH (gens.map enc) (bfsSet (gens.map enc) n) = true)
    (x : G) : x ∈ Subgroup.closure {g | g ∈ gens} ↔ enc x ∈ bfsSet (gens.map enc) n := by
  obtain ⟨h1, hcl⟩ := closedH_spec hc
  have := mem_closure_iff_of_closed h gens (bfsSet (gens.map enc) n).toList
    (Std.HashSet.mem_toList.mpr h1)
    (fun x hx g hg => Std.HashSet.mem_toList.mpr (hcl x (Std.HashSet.mem_toList.mp hx) g hg))
    (fun r hr => bfsSet_sound h gens n r (Std.HashSet.mem_toList.mp hr)) x
  rw [this, Std.HashSet.mem_toList]

theorem card_closure_of_closedH {G : Type*} [Group G] [Finite G] {enc : G → R} (h : IsEnc enc)
    (gens : List G) (n : ℕ) (hc : closedH (gens.map enc) (bfsSet (gens.map enc) n) = true) :
    Nat.card (Subgroup.closure {g | g ∈ gens}) = (bfsSet (gens.map enc) n).size := by
  have hnd : (bfsSet (gens.map enc) n).toList.Nodup :=
    Std.HashSet.distinct_toList.imp fun {a b} h hab => by simp [hab] at h
  have := card_of_list h.inj (Subgroup.closure {g | g ∈ gens}) (bfsSet (gens.map enc) n).toList
    hnd (fun x => by rw [mem_closure_iff_H h gens n hc x, Std.HashSet.mem_toList])
    (fun r hr => (bfsSet_sound h gens n r (Std.HashSet.mem_toList.mp hr)).imp fun x hx => hx.2)
  rw [this, Std.HashSet.length_toList]

end Closure

end CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
