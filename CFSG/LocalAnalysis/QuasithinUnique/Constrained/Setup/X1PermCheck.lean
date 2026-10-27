module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Sub
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier

section Eval

@[expose] def evalG {G : Type*} [Group G] (S : List G) : List ℤ → G
  | [] => 1
  | z :: w => (if 0 < z then S.getD (z.toNat - 1) 1 else (S.getD ((-z).toNat - 1) 1)⁻¹) * evalG S w

variable {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))

@[expose] def normH (x : ↥H) : ↥H := ⟨tab x.1, by rw [tab_eq]; exact x.2⟩

theorem normH_eq (x : ↥H) : normH H x = x := Subtype.ext (tab_eq x.1)

@[expose] def evalN (gens : List ↥H) (w : List ℤ) : ↥H := normH H (evalG gens w)

@[expose] def sylowGens (gA gB : ↥H) (rgw : List (List ℤ)) : List ↥H :=
  rgw.map (evalN H [gA, gB])

@[expose] def sylowList (gA gB : ↥H) (rgw rwords : List (List ℤ)) : List ↥H :=
  rwords.map (evalN H (sylowGens H gA gB rgw))

@[expose] def invList (Rl : List ↥H) : List ↥H :=
  Rl.filter fun x => decide (x ≠ 1 ∧ x * x = 1)

@[expose] def pairList (Rinv : List ↥H) : List (↥H × ↥H) :=
  Rinv.flatMap fun x => Rinv.filterMap fun y => if x ≠ y ∧ x * y = y * x then some (x, y) else none

end Eval

section Witness

variable {G : Type*} [Group G]

@[expose] def conjGens (ts cj : List G) : List G :=
  ts ++ cj.flatMap fun c => ts.map fun t => c * t * c⁻¹

theorem mem_conjSet_conjGens (ts cj : List G) :
    ∀ g ∈ conjGens ts cj, g ∈ conjSet (1 :: cj) {t | t ∈ ts} := by
  intro g hg
  rcases List.mem_append.1 hg with h | h
  · exact ⟨1, List.mem_cons_self, g, h, by simp⟩
  · obtain ⟨c, hc, h'⟩ := List.mem_flatMap.1 h
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h'
    exact ⟨c, List.mem_cons_of_mem _ hc, t, ht, rfl⟩

theorem exists_gen_of_witness (ts cj : List G) (w : List ℕ) {p : ℕ} [Fact p.Prime]
    (h : prodWord (conjGens ts cj) w ^ p = 1 ∧ prodWord (conjGens ts cj) w ≠ 1) :
    ∃ cs : List G, cs.length = cj.length + 1 ∧
      ∃ x ∈ Subgroup.closure (conjSet cs {t | t ∈ ts}), orderOf x = p :=
  ⟨1 :: cj, by simp, exists_mem_closure_conjSet (mem_conjSet_conjGens ts cj) w
    (orderOf_eq_prime h.1 h.2)⟩

variable [DecidableEq G]

@[expose] def witOK (ts cj : List G) (w : List ℕ) (p : ℕ) : Bool :=
  decide (prodWord (conjGens ts cj) w ^ p = 1 ∧ prodWord (conjGens ts cj) w ≠ 1)

theorem exists_gen_of_witOK (ts cj : List G) (w : List ℕ) {p : ℕ} [Fact p.Prime]
    (h : witOK ts cj w p = true) :
    ∃ cs : List G, cs.length = cj.length + 1 ∧
      ∃ x ∈ Subgroup.closure (conjSet cs {t | t ∈ ts}), orderOf x = p :=
  exists_gen_of_witness ts cj w (by simpa [witOK] using h)

end Witness

end CFSG.QuasithinUnique.Setup.X1
