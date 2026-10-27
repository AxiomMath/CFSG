module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.CGT.Timmesfeld75

open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F] {n : ℕ}

@[expose] def slAct (g : SL(n, F)) (u : (Fin n → F) × (Fin n → F)) : (Fin n → F) × (Fin n → F) :=
  ((g : Matrix (Fin n) (Fin n) F) *ᵥ u.1, (g : Matrix (Fin n) (Fin n) F) *ᵥ u.2)

@[expose] def IsSLInv (U : AddSubgroup ((Fin n → F) × (Fin n → F))) : Prop :=
  ∀ (g : SL(n, F)), ∀ u ∈ U, slAct g u ∈ U

def transvSL (i j : Fin n) (hij : i ≠ j) (c : F) : SL(n, F) :=
  ⟨transvection i j c, det_transvection_of_ne i j hij c⟩

theorem transvSL_mulVec (i j : Fin n) (hij : i ≠ j) (c : F) (v : Fin n → F) :
    (transvSL i j hij c : Matrix (Fin n) (Fin n) F) *ᵥ v =
      v + (c * v j) • (Pi.single i (1 : F) : Fin n → F) := by
  show transvection i j c *ᵥ v = _
  rw [transvection, add_mulVec, one_mulVec, single_mulVec_eq]

theorem IsSLInv.transv_mem {U : AddSubgroup ((Fin n → F) × (Fin n → F))} (hU : IsSLInv U)
    {i j : Fin n} (hij : i ≠ j) (c : F) {u : (Fin n → F) × (Fin n → F)} (hu : u ∈ U) :
    ((c * u.1 j) • (Pi.single i (1 : F) : Fin n → F),
      (c * u.2 j) • (Pi.single i (1 : F) : Fin n → F)) ∈ U := by
  have h := U.sub_mem (hU (transvSL i j hij c) u hu) hu
  have h2 : slAct (transvSL i j hij c) u - u =
      ((c * u.1 j) • (Pi.single i (1 : F) : Fin n → F),
        (c * u.2 j) • (Pi.single i (1 : F) : Fin n → F)) := by
    unfold slAct
    ext <;> simp [transvSL_mulVec]
  rwa [h2] at h

def coordSet (U : AddSubgroup ((Fin n → F) × (Fin n → F))) (i : Fin n) : Set (F × F) :=
  {p | (p.1 • (Pi.single i (1 : F) : Fin n → F), p.2 • (Pi.single i (1 : F) : Fin n → F)) ∈ U}

theorem mem_coordSet {U : AddSubgroup ((Fin n → F) × (Fin n → F))} {i : Fin n} {p : F × F} :
    p ∈ coordSet U i ↔
      (p.1 • (Pi.single i (1 : F) : Fin n → F), p.2 • (Pi.single i (1 : F) : Fin n → F)) ∈ U :=
  Iff.rfl

theorem coordSet_add {U : AddSubgroup ((Fin n → F) × (Fin n → F))} {i : Fin n} {p q : F × F}
    (hp : p ∈ coordSet U i) (hq : q ∈ coordSet U i) : p + q ∈ coordSet U i := by
  rw [mem_coordSet] at *
  have := U.add_mem hp hq
  convert this using 1
  ext <;> simp [add_mul]

theorem coordSet_neg {U : AddSubgroup ((Fin n → F) × (Fin n → F))} {i : Fin n} {p : F × F}
    (hp : p ∈ coordSet U i) : -p ∈ coordSet U i := by
  rw [mem_coordSet] at *
  have := U.neg_mem hp
  convert this using 1
  ext <;> simp [neg_mul]

theorem IsSLInv.coordSet_shift {U : AddSubgroup ((Fin n → F) × (Fin n → F))} (hU : IsSLInv U)
    {i j : Fin n} (hij : i ≠ j) {p : F × F} (hp : p ∈ coordSet U j) (c : F) :
    (c * p.1, c * p.2) ∈ coordSet U i := by
  have h := hU.transv_mem hij c hp
  rw [mem_coordSet]
  simpa using h

theorem exists_ne_fin (hn : 2 ≤ n) (i : Fin n) : ∃ j : Fin n, i ≠ j := by
  by_cases h : i.val = 0
  · exact ⟨⟨1, by omega⟩, fun h' => by
      have := congrArg Fin.val h'
      simp at this
      omega⟩
  · exact ⟨⟨0, by omega⟩, fun h' => by
      have := congrArg Fin.val h'
      simp at this
      omega⟩

theorem IsSLInv.coordSet_smul {U : AddSubgroup ((Fin n → F) × (Fin n → F))} (hU : IsSLInv U)
    (hn : 2 ≤ n) {i : Fin n} {p : F × F} (hp : p ∈ coordSet U i) (c : F) :
    (c * p.1, c * p.2) ∈ coordSet U i := by
  obtain ⟨j, hij⟩ := exists_ne_fin hn i
  have h1 : ((1 : F) * p.1, (1 : F) * p.2) ∈ coordSet U j := hU.coordSet_shift hij.symm hp 1
  simpa using hU.coordSet_shift hij h1 c

theorem IsSLInv.coordSet_transfer {U : AddSubgroup ((Fin n → F) × (Fin n → F))}
    (hU : IsSLInv U) {i j : Fin n} {p : F × F} (hp : p ∈ coordSet U i) : p ∈ coordSet U j := by
  by_cases hij : j = i
  · rwa [hij]
  · simpa using hU.coordSet_shift hij hp 1

theorem mem_of_forall_coordSet {U : AddSubgroup ((Fin n → F) × (Fin n → F))}
    {v w : Fin n → F} (h : ∀ j, (v j, w j) ∈ coordSet U j) : (v, w) ∈ U := by
  have hsum : (v, w) = ∑ j : Fin n, (v j • (Pi.single j (1 : F) : Fin n → F),
      w j • (Pi.single j (1 : F) : Fin n → F)) := by
    ext x
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [hsum]
  exact U.sum_mem fun j _ => h j

theorem IsSLInv.exists_ne_zero_coordSet {U : AddSubgroup ((Fin n → F) × (Fin n → F))}
    (hU : IsSLInv U) (hn : 2 ≤ n) (hne : U ≠ ⊥) (i : Fin n) :
    ∃ p ∈ coordSet U i, p ≠ 0 := by
  obtain ⟨⟨u, hu⟩, hu0'⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hne
  have hu0 : u ≠ 0 := fun h => hu0' (Subtype.ext h)
  have hcoord : ∃ j, u.1 j ≠ 0 ∨ u.2 j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hu0
    ext j
    · exact (hcon j).1
    · exact (hcon j).2
  obtain ⟨j, hj⟩ := hcoord
  obtain ⟨k, hjk⟩ := exists_ne_fin hn j
  have h1 := hU.transv_mem hjk.symm 1 hu
  have hp : (u.1 j, u.2 j) ∈ coordSet U k := by
    rw [mem_coordSet]
    simpa using h1
  refine ⟨(u.1 j, u.2 j), hU.coordSet_transfer hp, fun h0 => ?_⟩
  rcases hj with h | h
  · exact h (congrArg Prod.fst h0)
  · exact h (congrArg Prod.snd h0)

def graphSub (c : F) : AddSubgroup ((Fin n → F) × (Fin n → F)) where
  carrier := {u | u.2 = c • u.1}
  zero_mem' := by
    show (0 : (Fin n → F) × (Fin n → F)).2 = c • (0 : (Fin n → F) × (Fin n → F)).1
    simp
  add_mem' := fun {a b} ha hb => by
    have ha' : a.2 = c • a.1 := ha
    have hb' : b.2 = c • b.1 := hb
    show a.2 + b.2 = c • (a.1 + b.1)
    rw [ha', hb', smul_add]
  neg_mem' := fun {a} ha => by
    have ha' : a.2 = c • a.1 := ha
    show -a.2 = c • (-a.1)
    rw [ha', smul_neg]

theorem mem_graphSub {c : F} {u : (Fin n → F) × (Fin n → F)} :
    u ∈ graphSub c ↔ u.2 = c • u.1 := Iff.rfl

theorem isSLInv_classify (hn : 2 ≤ n) {U : AddSubgroup ((Fin n → F) × (Fin n → F))}
    (hU : IsSLInv U) :
    U = ⊥ ∨ U = ⊤ ∨ U = AddSubgroup.prod ⊥ ⊤ ∨ ∃ c : F, U = graphSub c := by
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨p, hp, hp0⟩ := hU.exists_ne_zero_coordSet hn hbot ⟨0, by omega⟩
  set S := coordSet U ⟨0, by omega⟩ with hSdef
  have hS : ∀ (j : Fin n) (q : F × F), q ∈ S → q ∈ coordSet U j :=
    fun j q hq => hU.coordSet_transfer hq
  have hsm : ∀ {q : F × F}, q ∈ S → ∀ c : F, (c * q.1, c * q.2) ∈ S :=
    fun hq c => hU.coordSet_smul hn hq c
  have htop : (∀ x y : F, (x, y) ∈ S) → U = ⊤ := by
    intro h
    rw [eq_top_iff]
    rintro ⟨v, w⟩ -
    exact mem_of_forall_coordSet fun j => hS j _ (h (v j) (w j))
  have hcoord : ∀ u ∈ U, ∀ j : Fin n, (u.1 j, u.2 j) ∈ S := by
    intro u hu j
    obtain ⟨k, hjk⟩ := exists_ne_fin hn j
    have h1 := hU.transv_mem hjk.symm 1 hu
    have hp' : (u.1 j, u.2 j) ∈ coordSet U k := by
      rw [mem_coordSet]
      simpa using h1
    exact hU.coordSet_transfer hp'
  by_cases ha : p.1 = 0
  ·
    have hb : p.2 ≠ 0 := fun h => hp0 (Prod.ext ha h)
    have h0z : ∀ z : F, ((0 : F), z) ∈ S := by
      intro z
      have := hsm hp (z / p.2)
      have e : ((z / p.2) * p.1, (z / p.2) * p.2) = ((0 : F), z) := by
        ext
        · simp [ha]
        · field_simp
      rwa [e] at this
    by_cases hq : ∃ q ∈ S, q.1 ≠ 0
    · obtain ⟨q, hq, hq1⟩ := hq
      have hx0 : (q.1, (0 : F)) ∈ S := by
        have := coordSet_add (U := U) hq (coordSet_neg (U := U) (h0z q.2))
        have e : q + -((0 : F), q.2) = (q.1, (0 : F)) := by
          ext <;> simp
        rwa [e] at this
      have hx : ∀ x : F, (x, (0 : F)) ∈ S := by
        intro x
        have := hsm hx0 (x / q.1)
        have e : ((x / q.1) * q.1, (x / q.1) * (0 : F)) = (x, (0 : F)) := by
          ext
          · field_simp
          · simp
        rwa [e] at this
      refine Or.inl (htop fun x y => ?_)
      have := coordSet_add (U := U) (hx x) (h0z y)
      simpa using this
    · push Not at hq
      refine Or.inr (Or.inl ?_)
      apply le_antisymm
      · intro u hu
        refine AddSubgroup.mem_prod.mpr ⟨?_, AddSubgroup.mem_top _⟩
        rw [AddSubgroup.mem_bot]
        funext j
        exact hq _ (hcoord u hu j)
      · rintro ⟨v, w⟩ huv
        have hv : v = 0 := by simpa [AddSubgroup.mem_prod] using huv
        subst hv
        exact mem_of_forall_coordSet fun j => hS j _ (h0z (w j))
  ·
    set c : F := p.2 / p.1 with hc
    have hline : ∀ x : F, (x, c * x) ∈ S := by
      intro x
      have := hsm hp (x / p.1)
      have e : ((x / p.1) * p.1, (x / p.1) * p.2) = (x, c * x) := by
        ext
        · field_simp
        · rw [hc]
          field_simp
      rwa [e] at this
    have hgraph : graphSub c ≤ U := by
      rintro ⟨v, w⟩ huv
      have hw : w = c • v := huv
      subst hw
      exact mem_of_forall_coordSet fun j => hS j _ (by simpa using hline (v j))
    by_cases hq : ∃ q ∈ S, q.2 ≠ c * q.1
    · obtain ⟨q, hq, hq2⟩ := hq
      have hy0 : ((0 : F), q.2 - c * q.1) ∈ S := by
        have := coordSet_add (U := U) hq (coordSet_neg (U := U) (hline q.1))
        have e : q + -(q.1, c * q.1) = ((0 : F), q.2 - c * q.1) := by
          ext <;> simp [sub_eq_add_neg]
        rwa [e] at this
      have hne : q.2 - c * q.1 ≠ 0 := sub_ne_zero.mpr hq2
      have h0z : ∀ z : F, ((0 : F), z) ∈ S := by
        intro z
        have := hsm hy0 (z / (q.2 - c * q.1))
        have e : ((z / (q.2 - c * q.1)) * (0 : F), (z / (q.2 - c * q.1)) * (q.2 - c * q.1)) =
            ((0 : F), z) := by
          ext
          · simp
          · field_simp
        rwa [e] at this
      refine Or.inl (htop fun x y => ?_)
      have := coordSet_add (U := U) (hline x) (h0z (y - c * x))
      have e : (x, c * x) + ((0 : F), y - c * x) = (x, y) := by
        ext <;> simp
      rwa [e] at this
    · push Not at hq
      refine Or.inr (Or.inr ⟨c, le_antisymm ?_ hgraph⟩)
      intro u hu
      by_contra hnot
      have hy : u.2 - c • u.1 ≠ 0 := fun h => hnot (sub_eq_zero.mp h)
      obtain ⟨j, hj⟩ : ∃ j, (u.2 - c • u.1) j ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hy (funext hcon)
      have hz : ((0 : Fin n → F), u.2 - c • u.1) ∈ U := by
        have := U.sub_mem hu (hgraph (show (u.1, c • u.1) ∈ graphSub c from rfl))
        have e : u - (u.1, c • u.1) = ((0 : Fin n → F), u.2 - c • u.1) := by
          ext <;> simp
        rwa [e] at this
      have h1 := hcoord _ hz j
      have := hq _ h1
      simp at this
      exact hj this

end CFSG.CGT.Timmesfeld75
