module

public import CFSG.GH74.GLS.C3.Layer1.Th2L82

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

@[expose] def B_thm2_l74_A7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G) (ρ : Th2Row),
    (ρ = .r3a ∨ ρ = .r3b ∨ ρ = .r3c) → Th2Std x y K T S → ρ.holds x y K T S →
      ρ.BT x K T S = {B' : Subgroup G | IsSn ρ.level.n (ρ.Tstar x K T S) B'}

namespace Th2

variable {G : Type} [Group G]

theorem le_omega1_of_isElementaryAbelian {B H : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (hBH : B ≤ H) : B ≤ omega1 H := by
  obtain ⟨-, hs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  intro b hb
  exact Subgroup.subset_closure ⟨hBH hb, by simpa [pow_two] using hs b hb⟩

theorem omega1_mono {H H' : Subgroup G} (h : H ≤ H') : omega1 H ≤ omega1 H' :=
  Subgroup.closure_mono fun _ hu => ⟨h hu.1, hu.2⟩

theorem isSn_tstar_eq [Finite G] (X : Subgroup G) (n : ℕ) :
    {B : Subgroup G | IsSn n X B} =
      {B' : Subgroup G | IsSn n (⨆ B ∈ {B : Subgroup G | IsSn n X B}, B) B'} := by
  set Ts : Subgroup G := ⨆ B ∈ {B : Subgroup G | IsSn n X B}, B with hTs
  have hle : ∀ B, IsSn n X B → B ≤ Ts := fun B hB =>
    le_iSup₂ (f := fun (B : Subgroup G) (_ : B ∈ {B : Subgroup G | IsSn n X B}) => B) B hB
  have hTsX : Ts ≤ X := iSup₂_le fun B hB => hB.1.1
  ext B'
  constructor
  · intro hB
    obtain ⟨⟨hBX, hBel, hBeq⟩, hBn⟩ := hB
    have hBTs : B' ≤ Ts := hle B' ⟨⟨hBX, hBel, hBeq⟩, hBn⟩
    refine ⟨⟨hBTs, hBel, le_antisymm ?_ ?_⟩, hBn⟩
    · refine le_omega1_of_isElementaryAbelian hBel (le_inf hBTs ?_)
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (C3.Layer1.Back.forall_of_isElementaryAbelian hBel).1 c hc b hb
    · exact (omega1_mono (inf_le_inf_right _ hTsX)).trans hBeq.ge
  · rintro ⟨⟨hB'T, hB'el, hB'eq⟩, hB'n⟩
    obtain ⟨B'', hB'B'', hB''S⟩ := exists_maximal_elemAbelian (hB'T.trans hTsX) hB'el
    have hB''n : IsSn n X B'' :=
      ⟨hB''S, hB'n.trans (C3.Layer1.Back.pRank_mono' hB'B'')⟩
    have hB''T : B'' ≤ Ts := hle B'' hB''n
    have hB''C : B'' ≤ Ts ⊓ centralizer (B' : Set G) := by
      refine le_inf hB''T fun c hc => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (C3.Layer1.Back.forall_of_isElementaryAbelian hB''S.2.1).1 b (hB'B'' hb) c hc
    have hB''le : B'' ≤ B' := by
      rw [hB'eq]
      exact le_omega1_of_isElementaryAbelian hB''S.2.1 hB''C
    have : B' = B'' := le_antisymm hB'B'' hB''le
    rw [this]
    exact hB''n

end Th2

open Th2 in
theorem b_thm2_l74_of (h : B_thm2_l74_A7) : B_thm2_l74 := by
  intro G _ _ hG x y K T S ρ hstd hρ
  cases ρ
  · exact isSn_tstar_eq _ 5
  · exact isSn_tstar_eq _ 4
  · exact isSn_tstar_eq _ 4
  · exact h G hG x y K T S _ (Or.inl rfl) hstd hρ
  · exact h G hG x y K T S _ (Or.inr (Or.inl rfl)) hstd hρ
  · exact h G hG x y K T S _ (Or.inr (Or.inr rfl)) hstd hρ
  · exact isSn_tstar_eq _ 4
  · exact isSn_tstar_eq _ 4
  · exact isSn_tstar_eq _ 4
  · exact isSn_tstar_eq _ 4

end CFSG.GH74.GLS
