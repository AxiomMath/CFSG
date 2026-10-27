module

public import CFSG.LargeExtraspecial.S12InspXFis
public import CFSG.LargeExtraspecial.S12InspXSym
public import CFSG.LargeExtraspecial.S12InspXSix
public import CFSG.LargeExtraspecial.S12InspXR3
public import CFSG.LargeExtraspecial.S12InspSplit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Matrix CFSG.RankThree.OrthogonalInvolutions CFSG.Open

@[expose] def S12FischerResidual4 (G : Type) [Group G] (D : Set G) : Prop :=
    (∃ m : ℕ, 2 ≤ m ∧ m ≤ 3 ∧ ∃ Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) ∧
      (m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
        Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) ∧
      fischerLinearModel D
        (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
        (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) ∨
    (∃ m : ℕ, 4 ≤ m ∧
      fischerCentralQuotientModel D
        (fischerMatrixGroup fun A => A.det = 1 ∧
          ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
        (fischerTransvections (fischerHermitianF4 m)
          fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) ∨
    (∃ m : ℕ, 5 ≤ m ∧ m ≤ 7 ∧ ∃ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3),
      (∀ x y, f x y = f y x) ∧ (∀ x, (∀ y, f x y = 0) → x = 0) ∧
      fischerCentralQuotientModel D
        (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
        (fischerTransvections (fun x y => f x y) fun v => f v v = 1))

@[expose] def Insp4FischerResidual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ≠ S.z → S.width = 4 →
    (∀ P : Subgroup S.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7) → 25920 ∣ Nat.card S.Mbar →
    t ∈ S.Lbar g → IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 → S.S12Standing g t →
    ¬ S.IsReducible12 → ¬ S.IsNondeg12 g →
    S12FischerResidual4 (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g) →
    S.S12Case1 g t ∨ (S.IsNondeg12 g ∧ S.S12Case2 g t) ∨ S.S12IndexCert g ∨
      (¬ S.IsNondeg12 g ∧ S.S12FuseCert g t) ∨ S.S12GenCert g ∨ Nat.card (S.Lbar g) ≤ 4 ∨
      S.S12SpSixSpin g

theorem insp4Input_of_fischerResidual (h : Insp4FischerResidual) : Insp4Input := by
  intro G _ _ _ S g t haQ hne hw hP hM ht htA hS hred hcls
  have h2 : ∀ k, 2 ^ k ∣ Nat.card (S.Xbar12 g) → k ≤ 7 := fun _ hk =>
    Setting.le_seven_of_two_pow_dvd_card_Xbar12 hP hk
  have h3 := Setting.three_pow_four_dvd_of_insp4 hS hM
  rcases hcls with ⟨-, hout⟩ | ⟨hdeg, hfis⟩
  · exact (S12Insp4.false_of_outcome hout h2 h3).elim
  refine h G S g t haQ hne hw hP hM ht htA hS hred hdeg ?_
  rcases hfis with ⟨m, hm, φ, hφ⟩ | ⟨m, hm, b, halt, hnd, hmod⟩ | hO | hU | hF3 | hFi | hFi | hFi
  · rcases hm with rfl | hm
    · exact (S12Insp4.false_of_perm_three φ h3).elim
    by_cases h5 : m = 5
    · subst h5
      exact (S12Insp4.false_of_perm_five φ h3).elim
    by_cases h7 : 7 ≤ m
    · exact (Setting.false_of_perm_ge_seven haQ hne (by omega) ht htA h7 φ hφ).elim
    obtain rfl : m = 6 := by omega
    exact (Setting.false_of_mulEquiv_perm_six hS hM φ).elim
  · by_cases hm3 : 3 ≤ m
    · exact (S12Insp4.false_of_sp hm3 halt hnd hmod h2).elim
    obtain rfl : m = 2 := by omega
    obtain ⟨ψ⟩ := S12Insp4.nonempty_mulEquiv_perm_six_of_sp halt hnd hmod
    exact (Setting.false_of_mulEquiv_perm_six hS hM ψ).elim
  · obtain ⟨m, hm, Q, hnd, hm2, hmod⟩ := hO
    by_cases hm4 : 4 ≤ m
    · exact (S12Insp4.false_of_orth hm4 hnd hmod h2).elim
    exact Or.inl ⟨m, hm, by omega, Q, hnd, hm2, hmod⟩
  · exact Or.inr (Or.inl hU)
  · obtain ⟨m, hm, f, hsymm, hnd, hmod⟩ := hF3
    by_cases hm8 : 8 ≤ m
    · exact (Setting.false_of_reflGroup_ge_eight hw hm8 hsymm hnd hmod).elim
    exact Or.inr (Or.inr ⟨m, hm, by omega, f, hsymm, hnd, hmod⟩)
  · exact (S12Insp4.false_of_fi h2 (Or.inl hFi.1)).elim
  · exact (S12Insp4.false_of_fi h2 (Or.inr (Or.inl hFi.1))).elim
  · exact (S12Insp4.false_of_fi h2 (Or.inr (Or.inr hFi.1))).elim

end CFSG.LargeExtraspecial
