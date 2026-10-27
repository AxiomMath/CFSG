module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsSix

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L.Seven

open Equiv CFSG.QuasithinUnique.Unc25K1.Six

abbrev P7 : Type := Equiv.Perm (Fin 7)

@[expose] def perm7 (cs : List (List (Fin 7))) : P7 := (cs.map List.formPerm).prod

structure R7 where
  a : Fin 7
  b : Fin 7
  c : Fin 7
  d : Fin 7
  e : Fin 7
  f : Fin 7
  g : Fin 7
  deriving DecidableEq, Hashable

namespace R7

@[expose] def get (x : R7) : Fin 7 → Fin 7
  | 0 => x.a
  | 1 => x.b
  | 2 => x.c
  | 3 => x.d
  | 4 => x.e
  | 5 => x.f
  | 6 => x.g

@[expose] def mul (x y : R7) : R7 :=
  ⟨x.get y.a, x.get y.b, x.get y.c, x.get y.d, x.get y.e, x.get y.f, x.get y.g⟩

@[expose] def one : R7 := ⟨0, 1, 2, 3, 4, 5, 6⟩

instance : Mul R7 := ⟨mul⟩

instance : One R7 := ⟨one⟩

@[expose] def enc (σ : P7) : R7 := ⟨σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6⟩

theorem enc_def (σ : P7) : enc σ = ⟨σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6⟩ := rfl

theorem get_enc (σ : P7) (i : Fin 7) : (enc σ).get i = σ i := by
  fin_cases i <;> rfl

theorem enc_mul (σ τ : P7) : enc (σ * τ) = enc σ * enc τ := by
  show enc (σ * τ) = ⟨(enc σ).get (τ 0), (enc σ).get (τ 1), (enc σ).get (τ 2),
    (enc σ).get (τ 3), (enc σ).get (τ 4), (enc σ).get (τ 5), (enc σ).get (τ 6)⟩
  simp only [get_enc]
  rfl

theorem enc_inj : Function.Injective enc := by
  intro σ τ h
  refine Equiv.ext fun i => ?_
  have := congrArg (fun r => r.get i) h
  simpa only [get_enc] using this

theorem enc_one : enc 1 = 1 := by decide

end R7

theorem rawIsEnc7 : IsEnc R7.enc := ⟨R7.enc_inj, R7.enc_mul, R7.enc_one⟩

def bfsStep (gens : List R7) (S : Std.HashSet R7) (F : List R7) : Std.HashSet R7 × List R7 :=
  F.foldl (fun acc x => gens.foldl (fun (acc : Std.HashSet R7 × List R7) g =>
    if acc.1.contains (x * g) then acc else (acc.1.insert (x * g), (x * g) :: acc.2)) acc) (S, [])

def bfsRun (gens : List R7) : ℕ → Std.HashSet R7 × List R7 → Std.HashSet R7 × List R7
  | 0, st => st
  | n + 1, st => bfsRun gens n (bfsStep gens st.1 st.2)

def bfsSet (gens : List R7) (n : ℕ) : Std.HashSet R7 :=
  (bfsRun gens n ((∅ : Std.HashSet R7).insert 1, [1])).1

theorem bfs_inner_sound (gens : List R7) (P : R7 → Prop) (x : R7) (hx : P x)
    (hP : ∀ y, P y → ∀ g ∈ gens, P (y * g)) :
    ∀ (l : List R7) (acc : Std.HashSet R7 × List R7),
      (∀ y ∈ acc.1, P y) → (∀ y ∈ acc.2, P y) → (∀ g ∈ l, g ∈ gens) →
      (∀ y ∈ (l.foldl (fun (acc : Std.HashSet R7 × List R7) g =>
        if acc.1.contains (x * g) then acc else (acc.1.insert (x * g), (x * g) :: acc.2)) acc).1,
          P y) ∧
      (∀ y ∈ (l.foldl (fun (acc : Std.HashSet R7 × List R7) g =>
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

theorem bfsStep_sound (gens : List R7) (P : R7 → Prop) (hP : ∀ y, P y → ∀ g ∈ gens, P (y * g))
    (S : Std.HashSet R7) (F : List R7) (hS : ∀ y ∈ S, P y) (hF : ∀ y ∈ F, P y) :
    (∀ y ∈ (bfsStep gens S F).1, P y) ∧ (∀ y ∈ (bfsStep gens S F).2, P y) := by
  unfold bfsStep
  have key : ∀ (l : List R7) (acc : Std.HashSet R7 × List R7), (∀ y ∈ acc.1, P y) →
      (∀ y ∈ acc.2, P y) → (∀ x ∈ l, P x) →
      (∀ y ∈ (l.foldl (fun acc x => gens.foldl (fun (acc : Std.HashSet R7 × List R7) g =>
        if acc.1.contains (x * g) then acc else (acc.1.insert (x * g), (x * g) :: acc.2)) acc)
        acc).1, P y) ∧
      (∀ y ∈ (l.foldl (fun acc x => gens.foldl (fun (acc : Std.HashSet R7 × List R7) g =>
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

theorem bfsRun_sound (gens : List R7) (P : R7 → Prop) (hP : ∀ y, P y → ∀ g ∈ gens, P (y * g)) :
    ∀ (n : ℕ) (st : Std.HashSet R7 × List R7), (∀ y ∈ st.1, P y) → (∀ y ∈ st.2, P y) →
      ∀ y ∈ (bfsRun gens n st).1, P y := by
  intro n
  induction n with
  | zero => intro st h1 _ y hy; exact h1 y hy
  | succ n ih =>
    intro st h1 h2 y hy
    obtain ⟨h1', h2'⟩ := bfsStep_sound gens P hP st.1 st.2 h1 h2
    exact ih _ h1' h2' y hy

theorem bfsSet_sound {G : Type*} [Group G] {enc : G → R7} (h : IsEnc enc) (gens : List G) (n : ℕ) :
    ∀ r ∈ bfsSet (gens.map enc) n, ∃ x ∈ Subgroup.closure {g | g ∈ gens}, enc x = r := by
  have hP : ∀ y : R7, (∃ x ∈ Subgroup.closure {g | g ∈ gens}, enc x = y) →
      ∀ g ∈ gens.map enc, ∃ x ∈ Subgroup.closure {g | g ∈ gens}, enc x = y * g := by
    rintro y ⟨x, hx, rfl⟩ g' hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    exact ⟨x * g, Subgroup.mul_mem _ hx (Subgroup.subset_closure hg), h.map_mul x g⟩
  have h1 : ∀ y ∈ ((∅ : Std.HashSet R7).insert 1 : Std.HashSet R7),
      ∃ x ∈ Subgroup.closure {g | g ∈ gens}, enc x = y := by
    intro y hy
    rw [Std.HashSet.mem_insert] at hy
    rcases hy with hy | hy
    · have : (1 : R7) = y := beq_iff_eq.mp hy
      exact ⟨1, Subgroup.one_mem _, by rw [← this, h.map_one]⟩
    · have := Std.HashSet.contains_iff_mem.mpr hy
      simp [Std.HashSet.contains_empty] at this
  have h2 : ∀ y ∈ [(1 : R7)], ∃ x ∈ Subgroup.closure {g | g ∈ gens}, enc x = y := by
    intro y hy
    rw [List.mem_singleton] at hy
    exact ⟨1, Subgroup.one_mem _, by rw [hy, h.map_one]⟩
  exact bfsRun_sound (gens.map enc) _ hP n _ h1 h2

def closedH (gens : List R7) (S : Std.HashSet R7) : Bool :=
  S.contains 1 && S.toList.all fun x => gens.all fun g => S.contains (x * g)

theorem closedH_spec {gens : List R7} {S : Std.HashSet R7} (h : closedH gens S = true) :
    (1 : R7) ∈ S ∧ ∀ x ∈ S, ∀ g ∈ gens, x * g ∈ S := by
  simp only [closedH, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨Std.HashSet.contains_iff_mem.mp h.1, fun x hx g hg => ?_⟩
  exact Std.HashSet.contains_iff_mem.mp (by
    have := h.2 x (Std.HashSet.mem_toList.mpr hx)
    exact this g hg)

theorem mem_closure_iff_H {G : Type*} [Group G] [Finite G] {enc : G → R7} (h : IsEnc enc)
    (gens : List G) (n : ℕ) (hc : closedH (gens.map enc) (bfsSet (gens.map enc) n) = true)
    (x : G) : x ∈ Subgroup.closure {g | g ∈ gens} ↔ enc x ∈ bfsSet (gens.map enc) n := by
  obtain ⟨h1, hcl⟩ := closedH_spec hc
  have := mem_closure_iff_of_closed h gens (bfsSet (gens.map enc) n).toList
    (Std.HashSet.mem_toList.mpr h1)
    (fun x hx g hg => Std.HashSet.mem_toList.mpr (hcl x (Std.HashSet.mem_toList.mp hx) g hg))
    (fun r hr => bfsSet_sound h gens n r (Std.HashSet.mem_toList.mp hr)) x
  rw [this, Std.HashSet.mem_toList]

theorem card_closure_of_closedH {G : Type*} [Group G] [Finite G] {enc : G → R7} (h : IsEnc enc)
    (gens : List G) (n : ℕ) (hc : closedH (gens.map enc) (bfsSet (gens.map enc) n) = true) :
    Nat.card (Subgroup.closure {g | g ∈ gens}) = (bfsSet (gens.map enc) n).size := by
  have hnd : (bfsSet (gens.map enc) n).toList.Nodup :=
    Std.HashSet.distinct_toList.imp fun {a b} h hab => by simp [hab] at h
  have := card_of_list h.inj (Subgroup.closure {g | g ∈ gens}) (bfsSet (gens.map enc) n).toList
    hnd (fun x => by rw [mem_closure_iff_H h gens n hc x, Std.HashSet.mem_toList])
    (fun r hr => (bfsSet_sound h gens n r (Std.HashSet.mem_toList.mp hr)).imp fun x hx => hx.2)
  rw [this, Std.HashSet.length_toList]

end CFSG.QuasithinUnique.Vol2Native.A312L.Seven
