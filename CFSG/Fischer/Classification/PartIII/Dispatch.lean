module

public import CFSG.Fischer.Classification.PartIII.Symp.MinusSix
public import CFSG.Fischer.Classification.PartIII.R3.Main
public import CFSG.Fischer.Classification.PartIII.U.Large

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Open CFSG.Fischer.Classification.Unitary

@[expose] def PartIIISetting (G : Type) [Group G] (D : Set G) (d : G) : Prop :=
  StatementBelow (Nat.card G) ∧ Hyp G D ∧ NonabelianCommutator G ∧ ¬ IsSymplecticType D ∧
    d ∈ D ∧ (LocalClass D d).Nonempty ∧ Hyp (LocalQuotient D d) (LocalImages D d) ∧
    Nat.card (LocalQuotient D d) < Nat.card G

theorem classicalPartIIIInputI_of_rows
    (h6 : ∀ (G : Type) [Group G] (D : Set G), StatementBelow (Nat.card G) → Hyp G D →
      NonabelianCommutator G → ¬ IsSymplecticType D →
      ∀ d ∈ D, (LocalClass D d).Nonempty → Hyp (LocalQuotient D d) (LocalImages D d) →
        Nat.card (LocalQuotient D d) < Nat.card G →
        MinusSixLocal (LocalQuotient D d) (LocalImages D d) → D.ncard = 117 →
        (∀ c ∈ D, c * d ≠ d * c → ThreeCommutingLines (muSet D d c)) →
        ClassicalConclusion G D)
    (hU4 : ∀ (G : Type) [Group G] (D : Set G) (d : G), PartIIISetting G D d →
      fischerCentralQuotientModel (LocalImages D d) (SUm 4) (TU 4) → ClassicalConclusion G D)
    (hU5 : ∀ (G : Type) [Group G] (D : Set G) (d : G), PartIIISetting G D d →
      fischerCentralQuotientModel (LocalImages D d) (SUm 5) (TU 5) → False)
    (hR56 : ∀ (G : Type) [Group G] (D : Set G) (d : G), PartIIISetting G D d →
      ∀ m : ℕ, (m = 5 ∨ m = 6) → ∀ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3),
        IsF3Form f → ∀ φ : LocalQuotient D d ≃* R3 f, φ '' LocalImages D d = D3 f →
        ClassicalConclusion G D) :
    ClassicalPartIIIInputI := by
  intro G _ D hb hH hnab hsymp d hd hne hHl hlt hcl hU6
  have hS : PartIIISetting G D d := ⟨hb, hH, hnab, hsymp, hd, hne, hHl, hlt⟩
  rcases hcl with h1 | h2 | h3 | ⟨m, hm, hmod⟩ | h5
  · exact classicalPartIII_symp_of_minusSix h6 G D hb hH hnab hsymp d hd hne hHl hlt (Or.inl h1)
  · exact classicalPartIII_symp_of_minusSix h6 G D hb hH hnab hsymp d hd hne hHl hlt
      (Or.inr (Or.inl h2))
  · exact classicalPartIII_symp_of_minusSix h6 G D hb hH hnab hsymp d hd hne hHl hlt
      (Or.inr (Or.inr h3))
  · rcases (show m = 4 ∨ m = 5 ∨ m = 6 ∨ 7 ≤ m by omega) with rfl | rfl | rfl | hm7
    · exact hU4 G D d hS hmod
    · exact (hU5 G D d hS hmod).elim
    · exact (hU6 hmod).elim
    · exact (false_of_local_case4_large hH hnab hd hm7 hmod).elim
  · obtain ⟨m, hm, f, hsymm, hnd, hmod⟩ := h5
    rcases (show m = 5 ∨ m = 6 ∨ 7 ≤ m by omega) with hm' | hm' | hm7
    · obtain ⟨m', hm'', f', hf', φ, hφ⟩ :=
        exists_mulEquiv_R3_of_case5 (k := 5) ⟨m, hm, f, hsymm, hnd, hmod⟩
      have : m' = 5 ∨ m' = 6 ∨ 7 ≤ m' := by omega
      rcases this with h | h | h
      · exact hR56 G D d hS m' (Or.inl h) f' hf' φ hφ
      · exact hR56 G D d hS m' (Or.inr h) f' hf' φ hφ
      · exact classicalConclusion_of_localR3 hH hnab hd h hf' φ hφ
    · obtain ⟨m', hm'', f', hf', φ, hφ⟩ :=
        exists_mulEquiv_R3_of_case5 (k := 5) ⟨m, hm, f, hsymm, hnd, hmod⟩
      have : m' = 5 ∨ m' = 6 ∨ 7 ≤ m' := by omega
      rcases this with h | h | h
      · exact hR56 G D d hS m' (Or.inl h) f' hf' φ hφ
      · exact hR56 G D d hS m' (Or.inr h) f' hf' φ hφ
      · exact classicalConclusion_of_localR3 hH hnab hd h hf' φ hφ
    · exact classicalConclusion_of_local_case5 hH hnab hd ⟨m, hm7, f, hsymm, hnd, hmod⟩

end CFSG.Fischer.Classification
