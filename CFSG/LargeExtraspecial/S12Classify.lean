module

public import CFSG.LargeExtraspecial.S12Fischer
public import CFSG.LargeExtraspecial.S12TriExcl
public import CFSG.LargeExtraspecial.S12SevenMain
public import CFSG.LargeExtraspecial.S12Square
public import CFSG.Timmesfeld.Skeleton

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

@[expose] def IsNondeg12 (g : G) : Prop :=
  ∃ d ∈ S.Ebar12 g, ∃ e ∈ S.Ebar12 g, orderOf (d * e) = 4

structure S12Standing (g : G) (t : S.O) : Prop where
  cls : ∀ τ ∈ S.Ebar12 g, ∃ x ∈ S.Xbar12 g, τ = x * t * x⁻¹
  cent : S.CXbar12 g = ⊥
  core3 : S.O3Xbar12 g = ⊥

variable {S}

theorem s12Standing_or (hRI : RootInvolutionComponentsInput.{u}) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 4 ≤ S.width) {t : S.O}
    (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    S.IsReducible12 ∨ S.S12Standing g t := by
  by_cases hred : S.IsReducible12
  · exact Or.inl hred
  exact Or.inr ⟨(S.timmesfeld_12_5 hRI haQ hne hn ht htA).resolve_left hred,
    (S.timmesfeld_12_8 haQ hne hn ht htA).resolve_right hred,
    (S.timmesfeld_12_7 hRI haQ hne hn ht htA).resolve_right hred⟩

theorem transpositionData_Xbar12 (hRI : RootInvolutionComponentsInput.{u}) {g : G} {t : S.O}
    (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hS : S.S12Standing g t) : S12TranspositionData (S.Xbar12 g) (S.Ebar12 g) t where
  subset := subset_Xbar12
  gen := rfl
  mem := mem_Ebar12_of_mem_Lbar ht htA
  cls := hS.cls
  conj := fun x hx τ hτ => conj_mem_Ebar12 (Xbar12_le_Mbar hx) hτ
  invol := fun τ hτ => Subtype.ext (isTypeA_of_mem_Ebar12 hτ).2.2.1
  ne_one := fun τ hτ h => (isTypeA_of_mem_Ebar12 hτ).2.1 (by rw [h]; rfl)
  ord := fun d hd e he =>
    Dbar12_rootInvolution.1 d (Ebar12_subset_Dbar12 hd) e (Ebar12_subset_Dbar12 he)
  sq := fun _ hd _ he h4 => sq_mem_Ebar12 hRI hd he h4

theorem S12Standing.center_trivial {g : G} {t : S.O} (hS : S.S12Standing g t) :
    ∀ y ∈ S.Xbar12 g, (∀ x ∈ S.Xbar12 g, x * y = y * x) → y = 1 := by
  intro y hy h
  have hmem : y ∈ S.CXbar12 g := ⟨Xbar12_le_Mbar hy, mem_centralizer_iff.mpr h⟩
  rw [hS.cent, mem_bot] at hmem
  exact hmem

theorem noNormalTwo_Xbar12 {g : G} : S12NoNormalTwo (S.Xbar12 g) :=
  S.s12_noNormalTwo_Mbar.of_normal Xbar12_le_Mbar Mbar_le_normalizer_Xbar12

theorem S12Standing.core3_trivial {g : G} {t : S.O} (hS : S.S12Standing g t) :
    ∀ P : Subgroup S.O, P ≤ S.Xbar12 g → IsPGroup 3 P →
      S.Xbar12 g ≤ normalizer (P : Set S.O) → P = ⊥ := by
  intro P h1 h2 h3
  have := (O3Xbar12_spec (S := S) g).2.2.2 P h1 h3 h2
  rw [hS.core3] at this
  exact eq_bot_iff.mpr this

end Setting

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem timmesfeld_12_3_classification (hRI : RootInvolutionComponentsInput.{0})
    (hARS : CFSG.Timmesfeld.ARSInput) (hTri : FischerTrialityInput)
    (hFischer : S12FischerStatement) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 4 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    S.IsReducible12 ∨
      (S.IsNondeg12 g ∧ CFSG.Timmesfeld.Outcome (S.Xbar12 g)) ∨
      (¬ S.IsNondeg12 g ∧
        S12FischerConclusion (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g)) := by
  rcases s12Standing_or hRI haQ hne hn ht htA with hred | hS
  · exact Or.inl hred
  right
  have hD := transpositionData_Xbar12 hRI ht htA hS
  by_cases hnd : S.IsNondeg12 g
  · exact Or.inl ⟨hnd, hARS _ _ (hD.arsHyp hS.center_trivial noNormalTwo_Xbar12 hnd)⟩
  · exact Or.inr ⟨hnd, hD.fischer hTri hFischer hS.center_trivial noNormalTwo_Xbar12
      hS.core3_trivial hnd (isSolvable_fischerQ_inf_centralizer haQ hne (by omega) ht htA)⟩

end Setting

end CFSG.LargeExtraspecial
