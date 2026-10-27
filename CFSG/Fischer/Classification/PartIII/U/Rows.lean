module

public import CFSG.Fischer.Classification.PartIII.Dispatch
public import CFSG.Fischer.Classification.PartIII.Arf.Convert
public import CFSG.Fischer.Classification.PartIII.U.Five
public import CFSG.Fischer.Classification.PartIII.U.SixMinus
public import CFSG.Fischer.Classification.PartIII.U.SixPlus

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Open CFSG.Fischer.Classification.Unitary F3 LocalU

theorem formMinusFive_eq_diagF3 : formMinusFive = diagF3 5 2 := by
  refine LinearMap.ext₂ fun x y => ?_
  rw [formMinusFive_apply, diagF3_apply, Fin.sum_univ_five]
  simp only [Arf.f5, diagF3Entry]
  norm_num
  linear_combination (-(x 4 * y 4)) * three_eq_zero

theorem normOneCompl_formMinusFive : NormOneCompl formMinusFive := by
  rw [formMinusFive_eq_diagF3]
  exact normOneCompl_diagF3_five_two

theorem partIII_minusSix : ∀ (G : Type) [Group G] (D : Set G), StatementBelow (Nat.card G) →
    Hyp G D → NonabelianCommutator G → ¬ IsSymplecticType D →
    ∀ d ∈ D, (LocalClass D d).Nonempty → Hyp (LocalQuotient D d) (LocalImages D d) →
      Nat.card (LocalQuotient D d) < Nat.card G →
      MinusSixLocal (LocalQuotient D d) (LocalImages D d) → D.ncard = 117 →
      (∀ c ∈ D, c * d ≠ d * c → ThreeCommutingLines (muSet D d c)) →
      ClassicalConclusion G D := by
  intro G _ D _ hH hnab _ d hd _ hHl _ h6 _ _
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_formMinusFive_of_minusSix hHl.pair hHl.center h6
  exact classicalConclusion_of_localR3_five_of_normOneCompl hH hnab hd isF3Form_formMinusFive
    normOneCompl_formMinusFive φ hφ

theorem partIII_unitary_five : ∀ (G : Type) [Group G] (D : Set G) (d : G),
    PartIIISetting G D d →
    fischerCentralQuotientModel (LocalImages D d) (SUm 5) (TU 5) → False :=
  fun _ _ _ _ hS h => false_of_local_case4_five hS.2.1 hS.2.2.1 hS.2.2.2.2.1 h

theorem partIII_F3_five_six_of
    (h45 : ∀ {G : Type} [Group G] {D : Set G}, Hyp G D → NonabelianCommutator G → ∀ {d : G},
      d ∈ D → ∀ {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)}, IsF3Form f →
        (D3 f).ncard = 45 → ∀ φ : LocalQuotient D d ≃* R3 f, φ '' LocalImages D d = D3 f →
          ClassicalConclusion G D)
    (hIC : Comparison fun f' : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3) =>
      (D3 f').ncard = 45) :
    ∀ (G : Type) [Group G] (D : Set G) (d : G), PartIIISetting G D d →
      ∀ m : ℕ, (m = 5 ∨ m = 6) → ∀ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3),
        IsF3Form f → ∀ φ : LocalQuotient D d ≃* R3 f, φ '' LocalImages D d = D3 f →
          ClassicalConclusion G D := by
  intro G _ D d hS m hm f hf φ hφ
  obtain ⟨-, hH, hnab, -, hd, -⟩ := hS
  rcases hm with rfl | rfl
  · rcases R3_five_cases hf with ⟨h, -⟩ | ⟨h, -⟩
    · exact h45 hH hnab hd hf h φ hφ
    · exact classicalConclusion_of_localR3_five_of_ncard_36 hH hnab hd hf h φ hφ
  · obtain ⟨δ, e, hδ, he⟩ := exists_linearEquiv_diagF3 (by norm_num) hf
    obtain ⟨ψ, hψ⟩ := exists_mulEquiv_R3_of_isometry e he
    have hφψ : (φ.trans ψ) '' LocalImages D d = D3 (diagF3 6 δ) := by
      rw [MulEquiv.coe_trans, Set.image_comp, hφ, hψ]
    rcases hδ with rfl | rfl
    · exact classicalConclusion_of_localR3_diagF3_six_one hIC hH hnab hd (φ.trans ψ) hφψ
    · exact classicalConclusion_of_localR3_diagF3_six_two hH hnab hd (φ.trans ψ) hφψ

theorem partIII_unitary_four_of
    (hU : ∀ {G : Type} [Group G] {D : Set G}, Hyp G D → NonabelianCommutator G → ∀ {d : G},
      d ∈ D → ∀ φ : LocalQuotient D d ≃* U2 4, φ '' LocalImages D d = DU 4 →
        ClassicalConclusion G D) :
    ∀ (G : Type) [Group G] (D : Set G) (d : G), PartIIISetting G D d →
      fischerCentralQuotientModel (LocalImages D d) (SUm 4) (TU 4) → ClassicalConclusion G D := by
  intro G _ D d hS h
  obtain ⟨φ, hφ⟩ := fischerCentralQuotientModel_iff_U2.1 h
  exact hU hS.2.1 hS.2.2.1 hS.2.2.2.2.1 φ hφ

theorem classicalPartIIIInputI_of_U4
    (hU : ∀ {G : Type} [Group G] {D : Set G}, Hyp G D → NonabelianCommutator G → ∀ {d : G},
      d ∈ D → ∀ φ : LocalQuotient D d ≃* U2 4, φ '' LocalImages D d = DU 4 →
        ClassicalConclusion G D)
    (h45 : ∀ {G : Type} [Group G] {D : Set G}, Hyp G D → NonabelianCommutator G → ∀ {d : G},
      d ∈ D → ∀ {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)}, IsF3Form f →
        (D3 f).ncard = 45 → ∀ φ : LocalQuotient D d ≃* R3 f, φ '' LocalImages D d = D3 f →
          ClassicalConclusion G D)
    (hIC : Comparison fun f' : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3) =>
      (D3 f').ncard = 45) :
    ClassicalPartIIIInputI :=
  classicalPartIIIInputI_of_rows partIII_minusSix (partIII_unitary_four_of hU)
    partIII_unitary_five (partIII_F3_five_six_of h45 hIC)

end CFSG.Fischer.Classification
