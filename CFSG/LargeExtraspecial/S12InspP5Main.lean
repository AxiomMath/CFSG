module

public import CFSG.LargeExtraspecial.S12InspP5O
public import CFSG.LargeExtraspecial.S12InspP5R
public import CFSG.LargeExtraspecial.S12InspP5U
public import CFSG.LargeExtraspecial.S12InspP4Res
public import CFSG.LargeExtraspecial.S12InspFamDO
public import CFSG.LargeExtraspecial.S12InspP4U
public import CFSG.LargeExtraspecial.S12InspXMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Matrix CFSG.RankThree.OrthogonalInvolutions CFSG.Open CFSG.Blueprint

@[expose] def S12FischerResidual4Two (G : Type) [Group G] (D : Set G) : Prop :=
    fischerCentralQuotientModel D
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4)
        fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0) ∨
    (commutator G = ⊤ ∧ ∃ f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3),
      (∀ x y, f x y = f y x) ∧ (∀ x, (∀ y, f x y = 0) → x = 0) ∧
      fischerCentralQuotientModel D
        (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
        (fischerTransvections (fun x y => f x y) fun v => f v v = 1))

@[expose] def Insp4FischerResidual2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ≠ S.z → S.width = 4 →
    (∀ P : Subgroup S.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7) → 25920 ∣ Nat.card S.Mbar →
    t ∈ S.Lbar g → IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 → S.S12Standing g t →
    ¬ S.IsReducible12 → ¬ S.IsNondeg12 g →
    S12FischerResidual4Two (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g) →
    S.S12Case1 g t ∨ (S.IsNondeg12 g ∧ S.S12Case2 g t) ∨ S.S12IndexCert g ∨
      (¬ S.IsNondeg12 g ∧ S.S12FuseCert g t) ∨ S.S12GenCert g ∨ Nat.card (S.Lbar g) ≤ 4 ∨
      S.S12SpSixSpin g

@[expose] def Insp4PlusResidual2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ≠ S.z → S.width = 4 →
    (∀ P : Subgroup S.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7) →
    (∀ P : Subgroup S.Mbar, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) → (∀ x ∈ P, x ^ 2 = 1) →
      Nat.card P ≤ 2 ^ 4) →
    (∀ N : Subgroup S.Mbar, N.Normal → 20160 ∣ Nat.card N ∨ 20160 ∣ N.index) →
    t ∈ S.Lbar g → IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 → S.S12Standing g t →
    ¬ S.IsReducible12 → S.IsNondeg12 g → LieModel (S.Xbar12 g) .PSL 4 2 1 →
    S.S12Case1 g t ∨ (S.IsNondeg12 g ∧ S.S12Case2 g t) ∨ S.S12IndexCert g ∨
      (¬ S.IsNondeg12 g ∧ S.S12FuseCert g t) ∨ S.S12GenCert g ∨ Nat.card (S.Lbar g) ≤ 4 ∨
      S.S12SpSixSpin g

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem commutator_eq_top_of_mem {g : G} {t : S.O} (hS : S.S12Standing g t)
    (htX : t ∈ S.Xbar12 g) (hc : (⟨t, htX⟩ : S.Xbar12 g) ∈ commutator (S.Xbar12 g)) :
    commutator (S.Xbar12 g) = ⊤ := by
  rw [eq_top_iff, ← s12_closure_preimage_eq_top (rfl : S.Xbar12 g = closure (S.Ebar12 g)),
    closure_le]
  intro τ hτ
  obtain ⟨x, hx, hxτ⟩ := hS.cls τ hτ
  have e : τ = ⟨x, hx⟩ * ⟨t, htX⟩ * (⟨x, hx⟩ : S.Xbar12 g)⁻¹ := Subtype.ext hxτ
  rw [SetLike.mem_coe, e]
  exact (inferInstance : (commutator (S.Xbar12 g)).Normal).conj_mem _ hc _

end Setting

theorem insp4FischerResidual_of_2 (h : Insp4FischerResidual2) : Insp4FischerResidual := by
  intro G _ _ _ S g t haQ hne hw hP hM ht htA hS hred hdeg hres
  have hn : 3 ≤ S.width := by omega
  refine h G S g t haQ hne hw hP hM ht htA hS hred hdeg ?_
  rcases hres with ⟨m, hm, hm3, Q, hnd, hm2, hmod⟩ | ⟨m, hm, hmod⟩ |
    ⟨m, hm5, hm7, f, hsymm, hnd, hmod⟩
  · exfalso
    rcases (show m = 2 ∨ m = 3 by omega) with rfl | rfl
    · exact Setting.false_of_orth_minus_four_insp4 haQ hne hn ht htA hS hdeg hM hnd (hm2 rfl)
        hmod
    · exact Setting.false_of_orth_six haQ hne hn ht htA hnd hmod
  · by_cases h4 : m = 4
    · subst h4
      exact Or.inl hmod
    exfalso
    by_cases h5 : m = 5
    · subst h5
      exact Setting.false_of_psu_five hP hmod
    have := Setting.le_five_of_psu hP ht htA hm hmod
    omega
  · rcases (show m = 5 ∨ m = 6 ∨ m = 7 by omega) with rfl | rfl | rfl
    · have htX := Setting.subset_Xbar12 (Setting.mem_Ebar12_of_mem_Lbar ht htA)
      by_cases hc : (⟨t, htX⟩ : S.Xbar12 g) ∈ commutator (S.Xbar12 g)
      · exact Or.inr ⟨Setting.commutator_eq_top_of_mem hS htX hc, f, hsymm, hnd, hmod⟩
      · exact (Setting.false_of_reflGroup_of_not_mem_commutator haQ hne hn ht htA hS hdeg le_rfl
          hsymm hnd hmod hc).elim
    · exact (Setting.false_of_reflGroup_six haQ hne hn ht htA hS hdeg hsymm hnd hmod).elim
    · exact (Setting.false_of_reflGroup_seven hw hsymm hnd hmod).elim

theorem insp4PlusResidual_of_2 (h : Insp4PlusResidual2) : Insp4PlusResidual := by
  intro G _ _ _ S g t haQ hne hw hP hE hsec ht htA hS hred hcls
  rcases hcls with ⟨hnd, hL⟩ | ⟨-, hres⟩
  · exact h G S g t haQ hne hw hP hE hsec ht htA hS hred hnd hL
  exfalso
  rcases hres with ⟨Q, hnd, -, hmod⟩ | ⟨m, hm4, hm5, hmod⟩
  · exact Setting.false_of_orth_six haQ hne (by omega) ht htA hnd hmod
  · rcases (show m = 4 ∨ m = 5 by omega) with rfl | rfl
    · exact Setting.false_of_psu_four_of_section hP hsec hmod
    · exact Setting.false_of_psu_five hP hmod

end CFSG.LargeExtraspecial
