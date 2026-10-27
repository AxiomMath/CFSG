module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignSteiner3
public import CFSG.Monster.B.Classical.PlaneAut
public meta import CFSG.Monster.B.Classical.PlaneData
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignHyperovalsInputs
public import Certificates.Certificate2028

public section

namespace CFSG.ComponentClassification.WittDesign

open CFSG.Monster.B.Classical.Plane

@[expose] def phiTab : Array ℕ :=
  #[0, 0, 1, 5, 15, 16, 8, 17, 20, 3, 10, 11, 9, 13, 6, 12, 18, 2, 14, 4, 7, 19]

@[expose] def psiTab : Array ℕ :=
  #[1, 2, 17, 9, 19, 3, 14, 20, 6, 12, 10, 11, 15, 13, 18, 4, 5, 7, 16, 21, 8]

@[expose] def sigmaTab : Array ℕ :=
  #[0, 1, 2, 3, 8, 21, 20, 13, 4, 19, 10, 15, 12, 7, 14, 11, 18, 17, 16, 9, 6, 5]

@[expose] def IsSixArc (X : Finset (Fin 21)) : Prop :=
  X.card = 6 ∧ ∀ a, (X ∩ projLine a).card ≤ 2

theorem lineMasks_spec :
    ∀ a x : Fin 21, (lineMasks[a.val]!).testBit x = decide (x ∈ projLine a) :=
  Certificates.certificate2028.1

theorem arcs_listed : ∀ x₀ x₁ : Fin 21, x₀ < x₁ → ArcLevel2 x₀ x₁ :=
  Certificates.certificate2028.2.1

theorem class_facts : hyperClass0.length = 56 ∧ hyperClass1.length = 56 ∧
    hyperClass2.length = 56 ∧ allHyper.Nodup ∧
    hyperClass0.all (fun X => hyperClass1.all fun Y => (X ∩ Y).card % 2 == 1) = true ∧
    hyperClass0.all (fun X => hyperClass2.all fun Y => (X ∩ Y).card % 2 == 1) = true ∧
    hyperClass1.all (fun X => hyperClass2.all fun Y => (X ∩ Y).card % 2 == 1) = true :=
  Certificates.certificate2028.2.2.1

theorem delta_facts : (∀ x, ofTable21 deltaInvTab (ofTable21 deltaTab x) = x) ∧
    (∀ x, ofTable21 deltaTab (ofTable21 deltaInvTab x) = x) ∧
    (∀ a : Fin 21, ∃ b : Fin 21, (projLine a).image (ofTable21 deltaTab) = projLine b) ∧
    hyperClass0.all (fun X => hyperClass1.contains (X.image (ofTable21 deltaTab))) = true ∧
    hyperClass1.all (fun X => hyperClass2.contains (X.image (ofTable21 deltaTab))) = true ∧
    hyperClass2.all (fun X => hyperClass0.contains (X.image (ofTable21 deltaTab))) = true :=
  Certificates.certificate2028.2.2.2

theorem nc3_iff (x y z : Fin 21) :
    nc3 x y z = true ↔ ∀ a, ¬(x ∈ projLine a ∧ y ∈ projLine a ∧ z ∈ projLine a) := by
  rw [nc3, List.all_eq_true]
  simp only [List.mem_finRange, true_implies, Bool.not_eq_true', Bool.and_eq_false_iff,
    lineMasks_spec, decide_eq_false_iff_not]
  constructor
  · intro h a ⟨hx, hy, hz⟩
    rcases h a with (h | h) | h <;> contradiction
  · intro h a
    by_contra hc
    push Not at hc
    exact h a ⟨hc.1.1, hc.1.2, hc.2⟩

theorem nc3_of_sixArc {X : Finset (Fin 21)} (hX : IsSixArc X) {x y z : Fin 21} (hx : x ∈ X)
    (hy : y ∈ X) (hz : z ∈ X) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : nc3 x y z = true := by
  rw [nc3_iff]
  rintro a ⟨hxa, hya, hza⟩
  have hsub : ({x, y, z} : Finset (Fin 21)) ⊆ X ∩ projLine a := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact Finset.mem_inter.2 ⟨hx, hxa⟩
    · exact Finset.mem_inter.2 ⟨hy, hya⟩
    · exact Finset.mem_inter.2 ⟨hz, hza⟩
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]), Finset.card_pair hyz] at h3
  have := hX.2 a
  omega

theorem mem_allHyper {X : Finset (Fin 21)} (hX : IsSixArc X) : X ∈ allHyper := by
  set f := X.orderEmbOfFin hX.1
  have hmem : ∀ i, f i ∈ X := fun i => X.orderEmbOfFin_mem hX.1 i
  have hne : ∀ i j : Fin 6, i ≠ j → f i ≠ f j := fun i j h e => h (f.injective e)
  have hlt : ∀ i j : Fin 6, i < j → f i < f j := fun i j h => f.strictMono h
  have hnc : ∀ i j k : Fin 6, i ≠ j → i ≠ k → j ≠ k → nc3 (f i) (f j) (f k) = true :=
    fun i j k hij hik hjk => nc3_of_sixArc hX (hmem i) (hmem j) (hmem k) (hne i j hij)
      (hne i k hik) (hne j k hjk)
  have hX' : X = {f 0, f 1, f 2, f 3, f 4, f 5} := by
    rw [← Finset.image_orderEmbOfFin_univ X hX.1]
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [f]
    · rintro (h | h | h | h | h | h) <;> exact ⟨_, h.symm⟩
  rw [hX']
  exact arcs_listed _ _ (hlt 0 1 (by decide)) _ (hlt 1 2 (by decide))
    (hnc 0 1 2 (by decide) (by decide) (by decide)) _ (hlt 2 3 (by decide))
    (hnc 0 1 3 (by decide) (by decide) (by decide)) (hnc 0 2 3 (by decide) (by decide) (by decide))
    (hnc 1 2 3 (by decide) (by decide) (by decide)) _ (hlt 3 4 (by decide))
    (hnc 0 1 4 (by decide) (by decide) (by decide)) (hnc 0 2 4 (by decide) (by decide) (by decide))
    (hnc 0 3 4 (by decide) (by decide) (by decide)) (hnc 1 2 4 (by decide) (by decide) (by decide))
    (hnc 1 3 4 (by decide) (by decide) (by decide)) (hnc 2 3 4 (by decide) (by decide) (by decide))
    _ (hlt 4 5 (by decide)) (hnc 0 1 5 (by decide) (by decide) (by decide))
    (hnc 0 2 5 (by decide) (by decide) (by decide)) (hnc 0 3 5 (by decide) (by decide) (by decide))
    (hnc 0 4 5 (by decide) (by decide) (by decide)) (hnc 1 2 5 (by decide) (by decide) (by decide))
    (hnc 1 3 5 (by decide) (by decide) (by decide)) (hnc 1 4 5 (by decide) (by decide) (by decide))
    (hnc 2 3 5 (by decide) (by decide) (by decide)) (hnc 2 4 5 (by decide) (by decide) (by decide))
    (hnc 3 4 5 (by decide) (by decide) (by decide))

@[expose] def hyperClass : Fin 3 → List (Finset (Fin 21)) :=
  ![hyperClass0, hyperClass1, hyperClass2]

theorem mem_hyperClasses {X : Finset (Fin 21)} (hX : IsSixArc X) : ∃ i, X ∈ hyperClass i := by
  have h := mem_allHyper hX
  simp only [allHyper, List.mem_append] at h
  rcases h with (h | h) | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

theorem card_inter_odd {i j : Fin 3} (hij : i ≠ j) {X Y : Finset (Fin 21)} (hX : X ∈ hyperClass i)
    (hY : Y ∈ hyperClass j) : (X ∩ Y).card % 2 = 1 := by
  obtain ⟨-, -, -, -, h01, h02, h12⟩ := class_facts
  have key : ∀ {L L' : List (Finset (Fin 21))},
      L.all (fun X => L'.all fun Y => (X ∩ Y).card % 2 == 1) = true →
      ∀ X ∈ L, ∀ Y ∈ L', (X ∩ Y).card % 2 = 1 := by
    intro L L' h X hX Y hY
    have := List.all_eq_true.1 (List.all_eq_true.1 h X hX) Y hY
    simpa using this
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact key h01 X hX Y hY
  · exact key h02 X hX Y hY
  · rw [Finset.inter_comm]; exact key h01 Y hY X hX
  · exact absurd rfl hij
  · exact key h12 X hX Y hY
  · rw [Finset.inter_comm]; exact key h02 Y hY X hX
  · rw [Finset.inter_comm]; exact key h12 Y hY X hX
  · exact absurd rfl hij

theorem length_hyperClass (i : Fin 3) : (hyperClass i).length = 56 := by
  obtain ⟨h0, h1, h2, -⟩ := class_facts
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem nodup_hyperClass (i : Fin 3) : (hyperClass i).Nodup := by
  have h := class_facts.2.2.2.1
  simp only [allHyper, List.nodup_append] at h
  fin_cases i
  · exact h.1.1
  · exact h.1.2.1
  · exact h.2.1

@[expose] def deltaPerm : Equiv.Perm (Fin 21) where
  toFun := ofTable21 deltaTab
  invFun := ofTable21 deltaInvTab
  left_inv := delta_facts.1
  right_inv := delta_facts.2.1

theorem deltaPerm_mem_lineAut : deltaPerm ∈ lineAut := by
  rw [mem_lineAut]
  intro a
  obtain ⟨b, hb⟩ := delta_facts.2.2.1 a
  refine ⟨b, ?_⟩
  rw [Finset.map_eq_image]
  exact hb

theorem map_delta_class (i : Fin 3) {X : Finset (Fin 21)} (hX : X ∈ hyperClass i) :
    X.map deltaPerm.toEmbedding ∈ hyperClass (i + 1) := by
  obtain ⟨-, -, -, h0, h1, h2⟩ := delta_facts
  rw [Finset.map_eq_image]
  have key : ∀ {L L' : List (Finset (Fin 21))},
      L.all (fun X => L'.contains (X.image (ofTable21 deltaTab))) = true →
      ∀ X ∈ L, X.image (ofTable21 deltaTab) ∈ L' := by
    intro L L' h X hX
    have := List.all_eq_true.1 h X hX
    simpa using this
  fin_cases i
  · exact key h0 X hX
  · exact key h1 X hX
  · exact key h2 X hX

end CFSG.ComponentClassification.WittDesign
