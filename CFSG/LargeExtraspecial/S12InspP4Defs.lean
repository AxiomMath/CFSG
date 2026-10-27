module

public import CFSG.LargeExtraspecial.S12InspSplit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CFSG.Open

theorem dvd_card_or_dvd_index_of_surjective {M A : Type*} [Group M] [Finite M] [Group A]
    [IsSimpleGroup A] {H : Subgroup M} (f : H →* A) (hf : Function.Surjective f)
    (N : Subgroup M) [hN : N.Normal] : Nat.card A ∣ Nat.card N ∨ Nat.card A ∣ N.index := by
  have hKA : ((N.subgroupOf H).map f).Normal := (hN.subgroupOf H).map f hf
  rcases hKA.eq_bot_or_eq_top with h | h
  · right
    have hle : N.subgroupOf H ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp h
    have h1 : Nat.card A = f.ker.index := by
      rw [index_ker, f.range_eq_top_of_surjective hf, card_top]
    rw [h1]
    exact (index_dvd_of_le hle).trans (relIndex_dvd_index_of_normal N H)
  · left
    have h1 : Nat.card A = Nat.card ((N.subgroupOf H).map f) := by rw [h, card_top]
    rw [h1]
    refine (card_map_dvd (N.subgroupOf H) f).trans ?_
    rw [← card_map_of_injective (f := H.subtype) (subtype_injective H)]
    refine card_dvd_of_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact mem_subgroupOf.mp hx

@[expose] def Insp4PlusInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ≠ S.z → S.width = 4 →
    (∀ P : Subgroup S.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7) →
    (∀ P : Subgroup S.Mbar, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) → (∀ x ∈ P, x ^ 2 = 1) →
      Nat.card P ≤ 2 ^ 4) →
    (∀ N : Subgroup S.Mbar, N.Normal → 20160 ∣ Nat.card N ∨ 20160 ∣ N.index) →
    t ∈ S.Lbar g → IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 → S.S12Standing g t →
    ¬ S.IsReducible12 →
    ((S.IsNondeg12 g ∧ CFSG.Timmesfeld.Outcome (S.Xbar12 g)) ∨
      (¬ S.IsNondeg12 g ∧
        S12FischerConclusion (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g))) →
    S.S12Case1 g t ∨ (S.IsNondeg12 g ∧ S.S12Case2 g t) ∨ S.S12IndexCert g ∨
      (¬ S.IsNondeg12 g ∧ S.S12FuseCert g t) ∨ S.S12GenCert g ∨ Nat.card (S.Lbar g) ≤ 4 ∨
      S.S12SpSixSpin g

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G} [IsSimpleGroup G]

theorem timmesfeld_12_16_of_insp4Plus (hRI : RootInvolutionComponentsInput.{0})
    (hARS : CFSG.Timmesfeld.ARSInput) (hTri : FischerTrialityInput)
    (hFischer : S12FischerStatement) (hInsp : Insp4PlusInput)
    (h36 : Timmesfeld36Input) (hSL : S12SL4ModuleInput) (hw : S.width = 4)
    (hP : ∀ P : Subgroup S.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7)
    (hE : ∀ P : Subgroup S.Mbar, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) → (∀ x ∈ P, x ^ 2 = 1) →
      Nat.card P ≤ 2 ^ 4)
    (hsec : ∀ N : Subgroup S.Mbar, N.Normal → 20160 ∣ Nat.card N ∨ 20160 ∣ N.index)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    {t : S.O} (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    S.IsReducible12 ∨ S.S12OmegaPlusEight ∨ S.S12GammaLResidual g t ∨ S.S12SpSixSpin g :=
  timmesfeld_12_16_of_inspAt hRI hARS hTri hFischer h36 hSL haQ hne (by omega) ht htA
    (hInsp G S g t haQ hne hw hP hE hsec ht htA)

end Setting

end CFSG.LargeExtraspecial
