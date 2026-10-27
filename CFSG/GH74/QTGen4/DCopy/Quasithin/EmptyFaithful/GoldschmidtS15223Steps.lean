module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Steps
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223P1Main

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def Reduction15223P2_F4 : Prop :=
  Reduction15223P1_F4 → ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G),
    Setting152 T Mc M → ∀ H : Subgroup G, IsHStar T M H →
      ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
        ∀ I : Subgroup G, Hyp15215.Min T Mc M B₀ I → CharTwo I →
          (∀ X : Subgroup G, ¬ IsChiBlock2 I X) ∧ L3NotInMc15223 T Mc M H B₀ I

@[expose] def Reduction15223P3_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∀ I : Subgroup G, Hyp15215.Min T Mc M B₀ I → CharTwo I → Concl15218i Mc M I →
        ∃ (r : ℕ) (L : Fin r → Subgroup G), (∀ i, IsChiBlock2 I (L i)) ∧
          ∀ h ∈ I, ∃ m ∈ Mc ⊓ I, ∃ x : Fin r → G, (∀ i, x i ∈ L i) ∧
            h = m * (List.ofFn x).prod

@[expose] def Reduction15223P4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
      ∀ I : Subgroup G, Hyp15215.Min T Mc M B₀ I → CharTwo I →
        (∀ X : Subgroup G, ¬ IsChiBlock2 I X) → L3NotInMc15223 T Mc M H B₀ I →
          Concl15218ii T Mc M H B₀ I → False

namespace S15223

theorem stageLemma15223_of_steps_F4 (h5 : StageLemma15205_F4) (h159 : StageLemma1519)
    (h8 : StageLemma15208_F4) (h11 : StageLemma15211_F4) (h12 : He12.StageLemma15212W_F4)
    (h13 : StageLemma15213_F4) (h14 : StageLemma15214_F4) (hN : StageNotation15209_F4)
    (h16 : StageLemma15216_F4) (h17 : StageLemma15217_F4) (h18 : StageLemma15218_F4)
    (hP2 : Reduction15223P2_F4) (hP3 : Reduction15223P3_F4) (hP4 : Reduction15223P4_F4) :
    StageLemma15223_F4 := by
  intro G _ _ T Mc M hs H hH B₀ hB₀ I hI hchar
  have hP1 : Reduction15223P1_F4 :=
    reduction15223P1_of_F4 (fun _ _ _ _ hX => S152O4.om4_facts hX) h5 h159 h8 h11 h12 h13 h14 hN h16
      h17
  obtain ⟨hno, hnot⟩ := hP2 hP1 G T Mc M hs H hH B₀ hB₀ I hI hchar
  rcases (h18 G T Mc M hs H hH B₀ hB₀ I hI.1).cases with hi | hii
  · obtain ⟨r, L, hL, hall⟩ := hP3 G T Mc M hs H hH B₀ hB₀ I hI hchar hi
    refine hI.1.not_le fun h hh => ?_
    obtain ⟨m, hm, x, hx, rfl⟩ := hall h hh
    cases r with
    | zero => simpa using (Subgroup.mem_inf.mp hm).1
    | succ r => exact absurd (hL 0) (hno _)
  · exact hP4 G T Mc M hs H hH B₀ hB₀ I hI hchar hno hnot hii

end S15223

end CFSG.Quasithin
