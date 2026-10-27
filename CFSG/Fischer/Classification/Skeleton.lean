module

public import CFSG.Fischer.Classification.Defs

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer

structure Hyp (G : Type) [Group G] (D : Set G) : Prop where
  pair : Pair G D
  center : Subgroup.center G = ⊥
  simple : IsSimpleGroup (commutator G)

@[expose] def Statement : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → Conclusion G D

@[expose] def NonabelianCommutator (G : Type) [Group G] : Prop :=
  ∃ a b : commutator G, a * b ≠ b * a

@[expose] def HasNormalPSubgroup (p : ℕ) (H : Type) [Group H] : Prop :=
  ∃ N : Subgroup H, N.Normal ∧ N ≠ ⊥ ∧ IsPGroup p N

@[expose] def S3Input : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → ¬ NonabelianCommutator G →
    ClassicalConclusion G D

@[expose] def SymplecticInput : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → NonabelianCommutator G → IsSymplecticType D →
    ClassicalConclusion G D

@[expose] def TrichotomyInput : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → NonabelianCommutator G →
    ∃ d ∈ D, (LocalClass D d).Nonempty ∧
      (HasNormalPSubgroup 3 (LocalQuotient D d) ∨ HasNormalPSubgroup 2 (LocalQuotient D d) ∨
        (Hyp (LocalQuotient D d) (LocalImages D d) ∧
          Nat.card (LocalQuotient D d) < Nat.card G))

@[expose] def O3Input : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → NonabelianCommutator G → ¬ IsSymplecticType D →
    ∀ d ∈ D, (LocalClass D d).Nonempty → HasNormalPSubgroup 3 (LocalQuotient D d) →
      ClassicalConclusion G D

@[expose] def O2Input : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → NonabelianCommutator G → ¬ IsSymplecticType D →
    ∀ d ∈ D, (LocalClass D d).Nonempty → HasNormalPSubgroup 2 (LocalQuotient D d) →
      ClassicalConclusion G D

@[expose] def PartIIIInput : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → NonabelianCommutator G → ¬ IsSymplecticType D →
    ∀ d ∈ D, (LocalClass D d).Nonempty → Hyp (LocalQuotient D d) (LocalImages D d) →
      Conclusion (LocalQuotient D d) (LocalImages D d) → Conclusion G D

theorem statement_of_inputs (h0 : S3Input) (h1 : SymplecticInput) (ht : TrichotomyInput)
    (h3 : O3Input) (h2 : O2Input) (hIII : PartIIIInput) : Statement := by
  suffices h : ∀ n, ∀ (G : Type) [Group G] (D : Set G), Nat.card G = n → Hyp G D →
      Conclusion G D from fun G _ D hH => h _ G D rfl hH
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ D hn hH
    by_cases hnab : NonabelianCommutator G
    · by_cases hsymp : IsSymplecticType D
      · exact Or.inl (h1 G D hH hnab hsymp)
      · obtain ⟨d, hd, hne, h3' | h2' | ⟨hHl, hlt⟩⟩ := ht G D hH hnab
        · exact Or.inl (h3 G D hH hnab hsymp d hd hne h3')
        · exact Or.inl (h2 G D hH hnab hsymp d hd hne h2')
        · exact hIII G D hH hnab hsymp d hd hne hHl
            (ih _ (hn ▸ hlt) _ (LocalImages D d) rfl hHl)
    · exact Or.inl (h0 G D hH hnab)

@[expose] def StatementBelow (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Nat.card G < n → Hyp G D → Conclusion G D

@[expose] def O3InputI : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), StatementBelow (Nat.card G) → Hyp G D →
    NonabelianCommutator G → ¬ IsSymplecticType D →
    ∀ d ∈ D, (LocalClass D d).Nonempty → HasNormalPSubgroup 3 (LocalQuotient D d) →
      ClassicalConclusion G D

@[expose] def O2InputI : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), StatementBelow (Nat.card G) → Hyp G D →
    NonabelianCommutator G → ¬ IsSymplecticType D →
    ∀ d ∈ D, (LocalClass D d).Nonempty → HasNormalPSubgroup 2 (LocalQuotient D d) →
      ClassicalConclusion G D

@[expose] def PartIIIInputI : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), StatementBelow (Nat.card G) → Hyp G D →
    NonabelianCommutator G → ¬ IsSymplecticType D →
    ∀ d ∈ D, (LocalClass D d).Nonempty → Hyp (LocalQuotient D d) (LocalImages D d) →
      Nat.card (LocalQuotient D d) < Nat.card G →
      Conclusion (LocalQuotient D d) (LocalImages D d) → Conclusion G D

theorem o3InputI_of (h : O3Input) : O3InputI :=
  fun G _ D _ => h G D

theorem o2InputI_of (h : O2Input) : O2InputI :=
  fun G _ D _ => h G D

theorem partIIIInputI_of (h : PartIIIInput) : PartIIIInputI :=
  fun G _ D _ hH hnab hsymp d hd hne hHl _ => h G D hH hnab hsymp d hd hne hHl

theorem statement_of_inputsI (h0 : S3Input) (h1 : SymplecticInput) (ht : TrichotomyInput)
    (h3 : O3InputI) (h2 : O2InputI) (hIII : PartIIIInputI) : Statement := by
  suffices h : ∀ n, ∀ (G : Type) [Group G] (D : Set G), Nat.card G = n → Hyp G D →
      Conclusion G D from fun G _ D hH => h _ G D rfl hH
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ D hn hH
    have hb : StatementBelow (Nat.card G) := fun G' _ D' hlt hH' =>
      ih _ (hn ▸ hlt) G' D' rfl hH'
    by_cases hnab : NonabelianCommutator G
    · by_cases hsymp : IsSymplecticType D
      · exact Or.inl (h1 G D hH hnab hsymp)
      · obtain ⟨d, hd, hne, h3' | h2' | ⟨hHl, hlt⟩⟩ := ht G D hH hnab
        · exact Or.inl (h3 G D hb hH hnab hsymp d hd hne h3')
        · exact Or.inl (h2 G D hb hH hnab hsymp d hd hne h2')
        · exact hIII G D hb hH hnab hsymp d hd hne hHl hlt (hb _ _ hlt hHl)
    · exact Or.inl (h0 G D hH hnab)

@[expose] def IsLocalPSU6 (H : Type) [Group H] (F : Set H) : Prop :=
  CFSG.Open.fischerCentralQuotientModel F
    (CFSG.Open.fischerMatrixGroup fun A : Matrix (Fin 6) (Fin 6) (GaloisField 2 2) =>
      A.det = 1 ∧ ∀ x y, CFSG.Open.fischerHermitianF4 6 (A.mulVec x) (A.mulVec y) =
        CFSG.Open.fischerHermitianF4 6 x y)
    (CFSG.Open.fischerTransvections (CFSG.Open.fischerHermitianF4 6)
      fun v => v ≠ 0 ∧ CFSG.Open.fischerHermitianF4 6 v v = 0)

@[expose] def NoF25Input : Prop :=
  ∀ (X : Type) [Group X] (E : Set X), Pair X E → ∀ e ∈ E,
    F24 (LocalQuotient E e) (LocalImages E e) →
    Subgroup.center (LocalQuotient E e) = ⊥ →
    IsSimpleGroup (commutator (LocalQuotient E e)) → False

@[expose] def PSU6Input : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Pair G D → ∀ d ∈ D,
    IsLocalPSU6 (LocalQuotient D d) (LocalImages D d) → F22 G D

@[expose] def ClassicalPartIIIInput : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → NonabelianCommutator G → ¬ IsSymplecticType D →
    ∀ d ∈ D, (LocalClass D d).Nonempty → Hyp (LocalQuotient D d) (LocalImages D d) →
      ClassicalConclusion (LocalQuotient D d) (LocalImages D d) →
      ¬ IsLocalPSU6 (LocalQuotient D d) (LocalImages D d) → ClassicalConclusion G D

@[expose] def ClassicalPartIIIInputI : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), StatementBelow (Nat.card G) → Hyp G D →
    NonabelianCommutator G → ¬ IsSymplecticType D →
    ∀ d ∈ D, (LocalClass D d).Nonempty → Hyp (LocalQuotient D d) (LocalImages D d) →
      Nat.card (LocalQuotient D d) < Nat.card G →
      ClassicalConclusion (LocalQuotient D d) (LocalImages D d) →
      ¬ IsLocalPSU6 (LocalQuotient D d) (LocalImages D d) → ClassicalConclusion G D

theorem partIIIInputI_of_classical (hC : ClassicalPartIIIInputI) (h25 : NoF25Input)
    (hU : PSU6Input) : PartIIIInputI := by
  intro G _ D hb hH hnab hsymp d hd hne hHl hlt hloc
  rcases hloc with hcl | ⟨k, hk⟩
  · by_cases hU6 : IsLocalPSU6 (LocalQuotient D d) (LocalImages D d)
    · exact Or.inr ⟨0, hU G D hH.pair d hd hU6⟩
    · exact Or.inl (hC G D hb hH hnab hsymp d hd hne hHl hlt hcl hU6)
  · refine Or.inr ?_
    match k, hk with
    | ⟨0, _⟩, hk => exact ⟨1, hH.pair, d, hd, hk⟩
    | ⟨1, _⟩, hk => exact ⟨2, hH.pair, d, hd, hk⟩
    | ⟨2, _⟩, hk => exact (h25 G D hH.pair d hd hk hHl.center hHl.simple).elim

theorem partIIIInput_of (hC : ClassicalPartIIIInput) (h25 : NoF25Input) (hU : PSU6Input) :
    PartIIIInput := by
  intro G _ D hH hnab hsymp d hd hne hHl hloc
  rcases hloc with hcl | ⟨k, hk⟩
  · by_cases hU6 : IsLocalPSU6 (LocalQuotient D d) (LocalImages D d)
    · exact Or.inr ⟨0, hU G D hH.pair d hd hU6⟩
    · exact Or.inl (hC G D hH hnab hsymp d hd hne hHl hcl hU6)
  · refine Or.inr ?_
    match k, hk with
    | ⟨0, _⟩, hk => exact ⟨1, hH.pair, d, hd, hk⟩
    | ⟨1, _⟩, hk => exact ⟨2, hH.pair, d, hd, hk⟩
    | ⟨2, _⟩, hk => exact (h25 G D hH.pair d hd hk hHl.center hHl.simple).elim

end CFSG.Fischer.Classification
