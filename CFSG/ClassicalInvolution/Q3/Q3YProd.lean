module

public import CFSG.ClassicalInvolution.Q3.Q3YThird
public import CFSG.ClassicalInvolution.Q3.Q3YModelAll
public import CFSG.ClassicalInvolution.Q3.Q3CAlpha

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Y

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

@[expose] def TypeC3NoThin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K →
      ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂ →
        z₁ ∈ nbrSpan3 (conjClass3 K) K₁

theorem typeC3Third_of_noThin (hNT : TypeC3NoThin) : Q3C.TypeC3Third := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  exact exists_third_of_nbhd hz (inClass3_conjugates hz) hBelow hB hA2 he
    (hNT G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he) modelPairOrCenterless3

theorem typeC3Prod_of_noThin (hNT : TypeC3NoThin) : Q3C.TypeC3Prod := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  obtain ⟨K₃, z₃, hK₃, hz₃, h13, h23, h1, h2⟩ :=
    typeC3Third_of_noThin hNT G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  have hmul : z₃ = z₁ * z₂ := Q3C.eq_mul_of_third hB he hK₃ hz₃ h13 h23 h1 h2
  obtain ⟨g, -, hg⟩ := conjClass3_involution hz hK₃ hz₃
  exact ⟨g, hg.symm.trans hmul⟩

theorem typeC3Triangle_of_noThin (hNT : TypeC3NoThin) : TypeC3Triangle :=
  Q3C.typeC3Triangle_of_third (typeC3Third_of_noThin hNT)

theorem typeC3NoThin_of_third (h : Q3C.TypeC3Third) : TypeC3NoThin := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  obtain ⟨K₃, z₃, hK₃, hz₃, h13, h23, h1, h2⟩ :=
    h G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  have hmul : z₃ = z₁ * z₂ := Q3C.eq_mul_of_third hB he hK₃ hz₃ h13 h23 h1 h2
  have hK₂nbr : K₂ ∈ nbrs3 (conjClass3 K) K₁ := by
    refine ⟨he.mem₂, fun h' => he.ne ?_, he.comm⟩
    have h2' : IsClassicalMember3 K₁ z₂ := h' ▸ he.cls₂
    exact involution_unique3 he.cls₁ h2'
  have hK₃nbr : K₃ ∈ nbrs3 (conjClass3 K) K₁ := by
    refine ⟨hK₃, fun h' => h1 ?_, h13⟩
    rw [h'] at hz₃
    exact involution_unique3 hz₃ he.cls₁
  have hz2sq : z₂ * z₂ = 1 := he.cls₂.isCentralInvolution.sq
  have hz : z₁ = z₃ * z₂ := by rw [hmul, mul_assoc, hz2sq, mul_one]
  rw [hz]
  exact Subgroup.mul_mem _ (le_nbrSpan3 hK₃nbr hz₃.mem) (le_nbrSpan3 hK₂nbr he.cls₂.mem)

end CFSG.ClassicalInvolution.Q3.Q3Y
