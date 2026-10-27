module

public import CFSG.Fischer.Classification.Uniqueness.Star

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

namespace Herm

variable {X : Type*} [Group X]

structure IsTranspositionSet (E : Set X) : Prop where
  mul_self : ∀ a ∈ E, a * a = 1
  mul_mul_mem : ∀ a ∈ E, ∀ b ∈ E, a * b * a ∈ E
  braid : ∀ a ∈ E, ∀ b ∈ E, a * b ≠ b * a → a * b * a = b * a * b

@[expose] def nonCommGraph (E : Set X) : SimpleGraph E where
  Adj a b := (a : X) * b ≠ b * a
  symm := ⟨fun _ _ h h' => h h'.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

theorem commute_of_not_adj {E : Set X} {a b : E} (h : ¬ (nonCommGraph E).Adj a b) :
    Commute (a : X) b :=
  not_not.1 h

theorem commute_left_of_commute {a b x : X} (hb : b * b = 1) (hab : a * b * a = b * a * b)
    (h1 : Commute x b) (h2 : Commute x (a * b * a)) : Commute x a := by
  have e : b * (a * b * a) * b = a := by
    rw [hab]
    calc b * (b * a * b) * b = (b * b) * a * (b * b) := by simp only [mul_assoc]
      _ = a := by rw [hb, one_mul, mul_one]
  rw [← e]
  exact (h1.mul_right h2).mul_right h1

theorem commute_mid_of_commute {a b x : X} (ha : a * a = 1) (h1 : Commute x a)
    (h2 : Commute x (a * b * a)) : Commute x b := by
  have e : a * (a * b * a) * a = b := by
    calc a * (a * b * a) * a = (a * a) * b * (a * a) := by simp only [mul_assoc]
      _ = b := by rw [ha, one_mul, mul_one]
  rw [← e]
  exact (h1.mul_right h2).mul_right h1

theorem commute_conj_iff {e a b : X} (he : e * e = 1) :
    Commute (e * a * e) (e * b * e) ↔ Commute a b := by
  have h1 : e * a * e * (e * b * e) = e * (a * b) * e := by
    calc e * a * e * (e * b * e) = e * a * (e * e) * b * e := by simp only [mul_assoc]
      _ = e * (a * b) * e := by rw [he, mul_one]; simp only [mul_assoc]
  have h2 : e * b * e * (e * a * e) = e * (b * a) * e := by
    calc e * b * e * (e * a * e) = e * b * (e * e) * a * e := by simp only [mul_assoc]
      _ = e * (b * a) * e := by rw [he, mul_one]; simp only [mul_assoc]
  change e * a * e * (e * b * e) = e * b * e * (e * a * e) ↔ a * b = b * a
  rw [h1, h2, mul_left_inj, mul_right_inj]

variable {E : Set X}

@[expose] def WithinTwo (E : Set X) (r v : E) : Prop :=
  v = r ∨ (nonCommGraph E).Adj r v ∨ ∃ x, (nonCommGraph E).Adj r x ∧ (nonCommGraph E).Adj x v

theorem withinTwo_of_adj (hE : IsTranspositionSet E) {r u w : E} (hu : WithinTwo E r u)
    (huw : (nonCommGraph E).Adj u w) : WithinTwo E r w := by
  rcases hu with rfl | hru | ⟨x, hrx, hxu⟩
  · exact Or.inr (Or.inl huw)
  · by_cases hwr : w = r
    · exact Or.inl hwr
    · exact Or.inr (Or.inr ⟨u, hru, huw⟩)
  · by_cases hwr : w = r
    · exact Or.inl hwr
    by_cases hrw : (nonCommGraph E).Adj r w
    · exact Or.inr (Or.inl hrw)
    by_cases hru : (nonCommGraph E).Adj r u
    · exact Or.inr (Or.inr ⟨u, hru, huw⟩)
    by_cases hxw : (nonCommGraph E).Adj x w
    · exact Or.inr (Or.inr ⟨x, hrx, hxw⟩)
    have hl := hE.braid x x.2 u u.2 hxu
    refine Or.inr (Or.inr ⟨⟨x * u * x, hE.mul_mul_mem x x.2 u u.2⟩, fun h => hrx ?_,
      fun h => huw ?_⟩)
    · exact commute_left_of_commute (hE.mul_self u u.2) hl (commute_of_not_adj hru) h
    · exact (commute_mid_of_commute (hE.mul_self x x.2) (commute_of_not_adj hxw).symm
        (Commute.symm h)).symm

theorem withinTwo_of_walk (hE : IsTranspositionSet E) {r u v : E}
    (p : (nonCommGraph E).Walk u v) : WithinTwo E r u → WithinTwo E r v := by
  induction p with
  | nil => exact id
  | cons h _ ih => exact fun hu => ih (withinTwo_of_adj hE hu h)

theorem withinTwo_of_reachable (hE : IsTranspositionSet E) {r v : E}
    (h : (nonCommGraph E).Reachable r v) : WithinTwo E r v :=
  h.elim fun p => withinTwo_of_walk hE p (Or.inl rfl)

theorem exists_adj_adj_of_connected (hE : IsTranspositionSet E)
    (hc : (nonCommGraph E).Connected) {r v : E} (hv : v ≠ r) (hrv : ¬ (nonCommGraph E).Adj r v) :
    ∃ x, (nonCommGraph E).Adj r x ∧ (nonCommGraph E).Adj x v := by
  rcases withinTwo_of_reachable hE (hc.preconnected r v) with h | h | h
  · exact absurd h hv
  · exact absurd h hrv
  · exact h

theorem connected_commonNeighbors (hE : IsTranspositionSet E) {r v y : E}
    (hrv : ¬ (nonCommGraph E).Adj r v) (hry : (nonCommGraph E).Adj r y)
    (hyv : (nonCommGraph E).Adj y v) :
    ((nonCommGraph E).induce
      {x | (nonCommGraph E).Adj r x ∧ (nonCommGraph E).Adj x v}).Connected := by
  set G := nonCommGraph E
  set C := {x | G.Adj r x ∧ G.Adj x v}
  have hrr := hE.mul_self r r.2
  have hl := hE.braid r r.2 y y.2 hry
  have hrrr : (r : X) * r * r = r := by rw [hrr, one_mul]
  have hrvr : (r : X) * v * r = v := by
    rw [(commute_of_not_adj hrv).eq, mul_assoc, hrr, mul_one]
  set y' : E := ⟨r * y * r, hE.mul_mul_mem r r.2 y y.2⟩ with hy'
  have hry' : G.Adj r y' := fun h => hry (by
    have h' : Commute ((r : X) * r * r) (r * y * r) := by rw [hrrr]; exact h
    exact (commute_conj_iff hrr).1 h')
  have hy'v : G.Adj y' v := fun h => hyv (by
    have h' : Commute ((r : X) * y * r) (r * v * r) := by rw [hrvr]; exact h
    exact (commute_conj_iff hrr).1 h')
  have hyy' : G.Adj y y' := fun h => hry (by
    have h' : Commute (y : X) (r * y * r) := h
    exact (commute_left_of_commute (hE.mul_self y y.2) hl (Commute.refl _) h').symm)
  have key : ∀ x ∈ C, G.Adj x y ∨ G.Adj x y' := by
    intro x hx
    by_contra hxy
    obtain ⟨h1, h2⟩ := not_or.1 hxy
    exact hx.1 (commute_left_of_commute (hE.mul_self y y.2) hl (commute_of_not_adj h1)
      (commute_of_not_adj h2)).symm
  let c₀ : C := ⟨y, hry, hyv⟩
  let c₁ : C := ⟨y', hry', hy'v⟩
  have h01 : (G.induce C).Adj c₀ c₁ := hyy'
  have hreach : ∀ c : C, (G.induce C).Reachable c c₀ := by
    intro c
    rcases key c c.2 with h | h
    · exact (show (G.induce C).Adj c c₀ from h).reachable
    · exact (show (G.induce C).Adj c c₁ from h).reachable.trans h01.symm.reachable
  exact (SimpleGraph.connected_iff _).2 ⟨fun a b => (hreach a).trans (hreach b).symm, ⟨c₀⟩⟩

theorem exists_adj_adj_adj_of_adj (hE : IsTranspositionSet E) {r v w x : E}
    (hrv : ¬ (nonCommGraph E).Adj r v) (hvw : (nonCommGraph E).Adj v w)
    (hrx : (nonCommGraph E).Adj r x) (hxv : (nonCommGraph E).Adj x v) :
    ∃ x, (nonCommGraph E).Adj r x ∧ (nonCommGraph E).Adj x v ∧ (nonCommGraph E).Adj x w := by
  by_cases hxw : (nonCommGraph E).Adj x w
  · exact ⟨x, hrx, hxv, hxw⟩
  have hvv := hE.mul_self v v.2
  have hvrv : (v : X) * r * v = r := by
    rw [(commute_of_not_adj hrv).symm.eq, mul_assoc, hvv, mul_one]
  have hvvv : (v : X) * v * v = v := by rw [hvv, one_mul]
  refine ⟨⟨v * x * v, hE.mul_mul_mem v v.2 x x.2⟩, fun h => hrx ?_, fun h => hxv ?_,
    fun h => hvw ?_⟩
  · have h' : Commute ((v : X) * r * v) (v * x * v) := by rw [hvrv]; exact h
    exact (commute_conj_iff hvv).1 h'
  · have h' : Commute ((v : X) * x * v) (v * v * v) := by rw [hvvv]; exact h
    exact (commute_conj_iff hvv).1 h'
  · have hl := hE.braid v v.2 x x.2 fun h' => hxv h'.symm
    exact (commute_left_of_commute (hE.mul_self x x.2) hl (commute_of_not_adj hxw).symm
      (Commute.symm h)).symm

theorem IsTranspositionSet.mono {S : Set X} (hE : IsTranspositionSet E) (hS : S ⊆ E)
    (hcl : ∀ a ∈ S, ∀ b ∈ S, a * b * a ∈ S) : IsTranspositionSet S :=
  ⟨fun a ha => hE.mul_self a (hS ha), hcl, fun a ha b hb => hE.braid a (hS ha) b (hS hb)⟩

theorem connected_nonCommGraph_of_surjective {S : Set X} (hc : (nonCommGraph E).Connected)
    (ρ : E → S) (hρ : Function.Surjective ρ)
    (hadj : ∀ a b : E, (a : X) * b ≠ b * a → (ρ a : X) * ρ b ≠ ρ b * ρ a) :
    (nonCommGraph S).Connected :=
  hc.map ⟨ρ, fun h => hadj _ _ h⟩ hρ

end Herm

open Herm

variable {X : Type*} [Group X] {E : Set X}

theorem coverRigid_nonCommGraph (hE : IsTranspositionSet E) (hc : (nonCommGraph E).Connected)
    (r : E) : CoverRigid (nonCommGraph E) r where
  exists_adj_adj _ hv hrv := exists_adj_adj_of_connected hE hc hv hrv
  connected _ hv hrv := by
    obtain ⟨_, hry, hyv⟩ := exists_adj_adj_of_connected hE hc hv hrv
    exact connected_commonNeighbors hE hrv hry hyv
  exists_adj_adj_adj _ _ hv hrv _ _ hvw := by
    obtain ⟨_, hrx, hxv⟩ := exists_adj_adj_of_connected hE hc hv hrv
    exact exists_adj_adj_adj_of_adj hE hrv hvw hrx hxv

section Pair

variable {X : Type} [Group X] {E : Set X}

theorem Pair.isTranspositionSet (hP : Pair X E) : IsTranspositionSet E :=
  ⟨fun _ ha => Pair.mul_self hP ha, fun _ ha _ hb => Pair.mul_mul_mem hP ha hb,
    fun _ ha _ hb h => Pair.mul_mul_eq hP ha hb h⟩

theorem Pair.connected_nonCommGraph (hP : Pair X E) : (nonCommGraph E).Connected := by
  obtain ⟨r, hr⟩ := Pair.nonempty hP
  set G := nonCommGraph E
  set R : X → Prop := fun y => ∃ hy : y ∈ E, G.Reachable ⟨r, hr⟩ ⟨y, hy⟩ with hR
  have step : ∀ e ∈ E, ∀ y, R y → R (e * y * e) := by
    rintro e he y ⟨hy, hry⟩
    refine ⟨Pair.mul_mul_mem hP he hy, ?_⟩
    by_cases hey : e * y = y * e
    · have h : (⟨e * y * e, Pair.mul_mul_mem hP he hy⟩ : E) = ⟨y, hy⟩ :=
        Subtype.ext (show e * y * e = y by rw [hey, mul_assoc, Pair.mul_self hP he, mul_one])
      rw [h]
      exact hry
    · have h1 : G.Adj ⟨y, hy⟩ ⟨e, he⟩ := fun h => hey h.symm
      have h2 : G.Adj ⟨e, he⟩ ⟨e * y * e, Pair.mul_mul_mem hP he hy⟩ := fun h => hey (by
        have h3 : e * (e * y * e) = y * e := by
          rw [← mul_assoc, ← mul_assoc, Pair.mul_self hP he, one_mul]
        have h4 : e * y * e * e = e * y := by rw [mul_assoc, Pair.mul_self hP he, mul_one]
        have h' : e * (e * y * e) = e * y * e * e := h
        rw [h3, h4] at h'
        exact h'.symm)
      exact (hry.trans h1.reachable).trans h2.reachable
  have key : ∀ g : X, ∀ y, R y ↔ R (g * y * g⁻¹) := by
    intro g
    have hg : g ∈ Subgroup.closure E := by rw [Pair.closure_eq hP]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem e he =>
      intro y
      rw [Pair.inv_eq hP he]
      refine ⟨step e he y, fun h => ?_⟩
      have h' := step e he _ h
      have hee := Pair.mul_self hP he
      rwa [show e * (e * y * e) * e = y by
        rw [← mul_assoc, ← mul_assoc, hee, one_mul, mul_assoc, hee, mul_one]] at h'
    | one => intro y; simp
    | mul g h _ _ ihg ihh =>
      intro y
      rw [ihh y, ihg (h * y * h⁻¹)]
      simp only [mul_inv_rev, mul_assoc]
    | inv g _ ih =>
      intro y
      rw [ih (g⁻¹ * y * g⁻¹⁻¹)]
      simp only [inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).2 ⟨⟨r, hr⟩, fun y => ?_⟩
  obtain ⟨g, hg⟩ := isConj_iff.1 (Pair.isConj hP hr y.2)
  obtain ⟨_, h⟩ := (key g r).1 ⟨hr, SimpleGraph.Reachable.refl _⟩
  have hy : (⟨g * r * g⁻¹, Pair.conj_mem hP hr g⟩ : E) = y := Subtype.ext hg
  rwa [hy] at h

end Pair

end CFSG.Fischer.Classification
