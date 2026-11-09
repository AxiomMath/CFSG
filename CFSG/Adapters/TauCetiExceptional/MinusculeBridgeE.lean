module

public import CFSG.Adapters.TauCetiExceptional.MinusculeBridge
public import CFSG.Adapters.TauCetiExceptional.MinusculeCellE
public import CFSG.Adapters.TauCetiExceptional.MinusculeSignsE
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted

public noncomputable section

namespace CFSG.TauCetiBridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  TauCeti BigCell Minuscule

theorem e6Data_excl : ∀ π' : Equiv.Perm (Fin (Tag.rank .E6)),
    (∀ ij : Fin (Tag.rank .E6) × Fin (Tag.rank .E6),
      Tag.cartan .E6 (π' ij.1) (π' ij.2) = Tag.cartan .E6 ij.1 ij.2) →
      (∀ a : Fin e6Data.d, ∃ b : Fin e6Data.d, ∀ j, e6Data.wt b (π' j) = e6Data.wt a j) →
        π' = 1 := by
  decide +kernel

@[expose] def e7Bimp (a b : Bool) : Bool := !a || b

theorem e7Bimp_eq_true (a b : Bool) : e7Bimp a b = true ↔ (a = true → b = true) := by
  cases a <;> simp [e7Bimp]

@[expose] def e7Ok (a b i j : Fin 7) : Bool := Tag.cartanE 7 a b == Tag.cartanE 7 i j

@[expose] def e7SearchB : Bool :=
  (List.finRange 7).all fun y3 => (List.finRange 7).all fun y2 => e7Bimp (e7Ok y3 y2 3 2) <|
  (List.finRange 7).all fun y4 => e7Bimp (e7Ok y3 y4 3 4 && e7Ok y2 y4 2 4) <|
  (List.finRange 7).all fun y1 => e7Bimp (e7Ok y3 y1 3 1 && e7Ok y2 y1 2 1 && e7Ok y4 y1 4 1) <|
  (List.finRange 7).all fun y0 =>
    e7Bimp (e7Ok y2 y0 2 0 && e7Ok y3 y0 3 0 && e7Ok y4 y0 4 0 && e7Ok y1 y0 1 0) <|
  (List.finRange 7).all fun y5 =>
    e7Bimp (e7Ok y4 y5 4 5 && e7Ok y3 y5 3 5 && e7Ok y2 y5 2 5 && e7Ok y1 y5 1 5 &&
      e7Ok y0 y5 0 5) <|
  (List.finRange 7).all fun y6 =>
    e7Bimp (e7Ok y5 y6 5 6 && e7Ok y4 y6 4 6 && e7Ok y3 y6 3 6 && e7Ok y2 y6 2 6 &&
      e7Ok y1 y6 1 6 && e7Ok y0 y6 0 6)
    (y0 == 0 && y1 == 1 && y2 == 2 && y3 == 3 && y4 == 4 && y5 == 5 && y6 == 6)

theorem e7SearchB_eq : e7SearchB = true := by decide +kernel

theorem e7_cartan_search : ∀ y3 y2 : Fin 7, Tag.cartanE 7 y3 y2 = Tag.cartanE 7 3 2 →
    ∀ y4 : Fin 7, Tag.cartanE 7 y3 y4 = Tag.cartanE 7 3 4 ∧
      Tag.cartanE 7 y2 y4 = Tag.cartanE 7 2 4 →
    ∀ y1 : Fin 7, Tag.cartanE 7 y3 y1 = Tag.cartanE 7 3 1 ∧
      Tag.cartanE 7 y2 y1 = Tag.cartanE 7 2 1 ∧ Tag.cartanE 7 y4 y1 = Tag.cartanE 7 4 1 →
    ∀ y0 : Fin 7, Tag.cartanE 7 y2 y0 = Tag.cartanE 7 2 0 ∧
      Tag.cartanE 7 y3 y0 = Tag.cartanE 7 3 0 ∧ Tag.cartanE 7 y4 y0 = Tag.cartanE 7 4 0 ∧
      Tag.cartanE 7 y1 y0 = Tag.cartanE 7 1 0 →
    ∀ y5 : Fin 7, Tag.cartanE 7 y4 y5 = Tag.cartanE 7 4 5 ∧
      Tag.cartanE 7 y3 y5 = Tag.cartanE 7 3 5 ∧ Tag.cartanE 7 y2 y5 = Tag.cartanE 7 2 5 ∧
      Tag.cartanE 7 y1 y5 = Tag.cartanE 7 1 5 ∧ Tag.cartanE 7 y0 y5 = Tag.cartanE 7 0 5 →
    ∀ y6 : Fin 7, Tag.cartanE 7 y5 y6 = Tag.cartanE 7 5 6 ∧
      Tag.cartanE 7 y4 y6 = Tag.cartanE 7 4 6 ∧ Tag.cartanE 7 y3 y6 = Tag.cartanE 7 3 6 ∧
      Tag.cartanE 7 y2 y6 = Tag.cartanE 7 2 6 ∧ Tag.cartanE 7 y1 y6 = Tag.cartanE 7 1 6 ∧
      Tag.cartanE 7 y0 y6 = Tag.cartanE 7 0 6 →
    y0 = 0 ∧ y1 = 1 ∧ y2 = 2 ∧ y3 = 3 ∧ y4 = 4 ∧ y5 = 5 ∧ y6 = 6 := by
  have h := e7SearchB_eq
  simp only [e7SearchB, List.all_eq_true, List.mem_finRange, forall_const, e7Bimp_eq_true,
    Bool.and_eq_true, beq_iff_eq, e7Ok, and_assoc] at h
  exact h

theorem e7_cartan_rigid (π' : Equiv.Perm (Fin (Tag.rank .E7)))
    (h : ∀ ij : Fin (Tag.rank .E7) × Fin (Tag.rank .E7),
      Tag.cartan .E7 (π' ij.1) (π' ij.2) = Tag.cartan .E7 ij.1 ij.2) : π' = 1 := by
  have h7 : ∀ i j : Fin 7, Tag.cartanE 7 (π' i) (π' j) = Tag.cartanE 7 i j :=
    fun i j => h (i, j)
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := e7_cartan_search _ _ (h7 3 2)
    _ ⟨h7 3 4, h7 2 4⟩ _ ⟨h7 3 1, h7 2 1, h7 4 1⟩
    _ ⟨h7 2 0, h7 3 0, h7 4 0, h7 1 0⟩
    _ ⟨h7 4 5, h7 3 5, h7 2 5, h7 1 5, h7 0 5⟩
    _ ⟨h7 5 6, h7 4 6, h7 3 6, h7 2 6, h7 1 6, h7 0 6⟩
  have hcases : ∀ i : Fin 7, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
    decide
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.one_apply]
  rcases hcases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem e7Data_excl : ∀ π' : Equiv.Perm (Fin (Tag.rank .E7)),
    (∀ ij : Fin (Tag.rank .E7) × Fin (Tag.rank .E7),
      Tag.cartan .E7 (π' ij.1) (π' ij.2) = Tag.cartan .E7 ij.1 ij.2) →
      (∀ a : Fin e7Data.d, ∃ b : Fin e7Data.d, ∀ j, e7Data.wt b (π' j) = e7Data.wt a j) →
        π' = 1 :=
  fun π' h _ => e7_cartan_rigid π' h

theorem untwistedBridge_E6
    : UntwistedBridge .E6 LieTypeIndex.E6 := by
  intro q hv hp2 K _ _ hK
  have hq : ValidLieTypeIndex.fieldOrder ⟨_, hv⟩ = q.card := LieTypeIndex.fieldOrder_E6 q
  have hfin : ∀ d : ValidLieTypeIndex, Finite d.fixedField := fun _ => inferInstance
  have := hfin ⟨_, hv⟩
  have : IsAlgClosure (ValidLieTypeIndex.fixedField ⟨_, hv⟩)
      (ValidLieTypeIndex.Closure ⟨_, hv⟩) := by
    rw [ValidLieTypeIndex.fixedField_def]
    exact isAlgClosure_frobeniusFixedSubfield _
  have hFr : ∀ c, (ValidLieTypeIndex.frobeniusEquiv ⟨_, hv⟩).toRingHom c =
      c ^ Nat.card (ValidLieTypeIndex.fixedField ⟨_, hv⟩) := fun c => by
    rw [ValidLieTypeIndex.card_fixedField]
    exact ValidLieTypeIndex.frobeniusEquiv_apply _ c
  have hodd : Odd (Nat.card (ValidLieTypeIndex.fixedField ⟨_, hv⟩)) := by
    rw [ValidLieTypeIndex.card_fixedField, hq, PrimePower.card_def]
    exact (q.prime_p.odd_of_ne_two hp2).pow
  have hp2' : ValidLieTypeIndex.characteristic ⟨_, hv⟩ ≠ 2 := by
    rw [show ValidLieTypeIndex.characteristic ⟨_, hv⟩ = q.p from LieTypeIndex.characteristic_E6 q]
    exact hp2
  obtain ⟨e⟩ := nonempty_fixedPointCandidate_equiv e6Match.lab
    (ValidLieTypeIndex.Closure ⟨_, hv⟩) e6Data_valid posDef_cartan_E6 e6Signs_check
    (E6Minuscule.points _) (fun z hz P hP => e6_evalMat_eq_zero P hP _ z hz)
    (fun _ c => e6_toMat_mem_points _ ⟨_, e6Data_valid.xu_mem _ _ c⟩)
    (fun _ c => e6_toMat_mem_points _ ⟨_, e6Data_valid.xu_mem _ _ c⟩)
    e6Data_dominant e6Data_degOrdered (by decide) e6Data_excl (by decide) hp2'
    (TypeE6LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩)
    (ValidLieTypeIndex.frobeniusEquiv ⟨_, hv⟩).toRingHom
    (fun z r s => (TypeE6LieIndex.coe_steinberg_apply ⟨⟨_, hv⟩, by simp⟩ z r s).trans
      (ValidLieTypeIndex.frobeniusEquiv_apply ⟨_, hv⟩ _).symm)
    (ValidLieTypeIndex.fixedField ⟨_, hv⟩) hodd hFr
    (commutator_adjointGroup_eq e6Data_valid posDef_cartan_E6 e6Signs_check _
      (CFSG.LieType.CurtisTits.isPerfect_e6 _))
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (ValidLieTypeIndex.fixedField ⟨_, hv⟩) := Fintype.ofFinite _
  have hcardK : Fintype.card K = Fintype.card (ValidLieTypeIndex.fixedField ⟨_, hv⟩) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      ValidLieTypeIndex.card_fixedField, hq]
  exact ⟨(adjointQuotientCongr (FiniteField.ringEquivOfCardEq hcardK)).trans e.symm⟩

theorem untwistedBridge_E7
    : UntwistedBridge .E7 LieTypeIndex.E7 := by
  intro q hv hp2 K _ _ hK
  have hq : ValidLieTypeIndex.fieldOrder ⟨_, hv⟩ = q.card := LieTypeIndex.fieldOrder_E7 q
  have hfin : ∀ d : ValidLieTypeIndex, Finite d.fixedField := fun _ => inferInstance
  have := hfin ⟨_, hv⟩
  have : IsAlgClosure (ValidLieTypeIndex.fixedField ⟨_, hv⟩)
      (ValidLieTypeIndex.Closure ⟨_, hv⟩) := by
    rw [ValidLieTypeIndex.fixedField_def]
    exact isAlgClosure_frobeniusFixedSubfield _
  have hFr : ∀ c, (ValidLieTypeIndex.frobeniusEquiv ⟨_, hv⟩).toRingHom c =
      c ^ Nat.card (ValidLieTypeIndex.fixedField ⟨_, hv⟩) := fun c => by
    rw [ValidLieTypeIndex.card_fixedField]
    exact ValidLieTypeIndex.frobeniusEquiv_apply _ c
  have hodd : Odd (Nat.card (ValidLieTypeIndex.fixedField ⟨_, hv⟩)) := by
    rw [ValidLieTypeIndex.card_fixedField, hq, PrimePower.card_def]
    exact (q.prime_p.odd_of_ne_two hp2).pow
  have hp2' : ValidLieTypeIndex.characteristic ⟨_, hv⟩ ≠ 2 := by
    rw [show ValidLieTypeIndex.characteristic ⟨_, hv⟩ = q.p from LieTypeIndex.characteristic_E7 q]
    exact hp2
  obtain ⟨e⟩ := nonempty_fixedPointCandidate_equiv e7Match.lab
    (ValidLieTypeIndex.Closure ⟨_, hv⟩) e7Data_valid posDef_cartan_E7 e7Signs_check
    (E7Minuscule.points _) (fun z hz P hP => e7_evalMat_eq_zero P hP _ z hz)
    (fun _ c => e7_toMat_mem_points _ ⟨_, e7Data_valid.xu_mem _ _ c⟩)
    (fun _ c => e7_toMat_mem_points _ ⟨_, e7Data_valid.xu_mem _ _ c⟩)
    e7Data_dominant e7Data_degOrdered (by decide) e7Data_excl (by decide) hp2'
    (TypeE7LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩)
    (ValidLieTypeIndex.frobeniusEquiv ⟨_, hv⟩).toRingHom
    (fun z r s => (TypeE7LieIndex.coe_steinberg_apply ⟨⟨_, hv⟩, by simp⟩ z r s).trans
      (ValidLieTypeIndex.frobeniusEquiv_apply ⟨_, hv⟩ _).symm)
    (ValidLieTypeIndex.fixedField ⟨_, hv⟩) hodd hFr
    (commutator_adjointGroup_eq e7Data_valid posDef_cartan_E7 e7Signs_check _
      (CFSG.LieType.CurtisTits.isPerfect_e7 _))
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (ValidLieTypeIndex.fixedField ⟨_, hv⟩) := Fintype.ofFinite _
  have hcardK : Fintype.card K = Fintype.card (ValidLieTypeIndex.fixedField ⟨_, hv⟩) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      ValidLieTypeIndex.card_fixedField, hq]
  exact ⟨(adjointQuotientCongr (FiniteField.ringEquivOfCardEq hcardK)).trans e.symm⟩

end CFSG.TauCetiBridge
