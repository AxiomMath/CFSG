module

public import CFSG.ClassicalInvolution.Asc77.AscT8ZC4
public import CFSG.ClassicalInvolution.Q3.Q3T8P26P02
public import CFSG.ClassicalInvolution.Q3.Q3MTShapeB
import CFSG.ClassicalInvolution.Asc77.AscT8ZC4Eng

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab
namespace T8ZZ
open CFSG.ClassicalInvolution.Asc77.T8ZZ
section Link
variable {X : Type} [Group X] {Ψ : Set (Subgroup X)} {k : Subgroup X}
variable [Finite X]

theorem hypOmegaModU_linkFam (hΨ : Uniform.HypOmegaModU (.sl2 3 1) Ψ)
    (hk : ∀ g : X, conjSub g k = k) :
    Uniform.HypOmegaModU (.sl2 3 1) (linkFam Ψ k) where
  conjInvariant := conjInvariant_linkFam hΨ.conjInvariant hk
  classical := fun L hL => hΨ.classical L hL.1
  omega4 := fun K hK J hJ hne => hΨ.omega4 K hK.1 J hJ.1 hne
  omega5 := fun K hK J hJ hne z hz v hv hnc hv2 hvz =>
    hΨ.omega5 K hK.1 J hJ.1 hne z hz v hv hnc hv2 hvz

theorem rSet_linkFam_subset : RSet (linkFam Ψ k) ⊆ RSet Ψ := by
  rintro _ ⟨M, hM, P, rfl⟩
  exact ⟨M, hM.1, P, rfl⟩

theorem uSet_linkFam_subset : USet (linkFam Ψ k) ⊆ USet Ψ := by
  rintro U ⟨R, hR, hUR, hc, hi⟩
  exact ⟨R, rSet_linkFam_subset hR, hUR, hc, hi⟩

theorem omegaNbr_linkFam_iff (hΨ : HypOmegaMod Ψ) {J K : Subgroup X}
    (hJ : J ∈ linkFam Ψ k) : J ∈ omegaNbr (linkFam Ψ k) K ↔ J ∈ omegaNbr Ψ K := by
  constructor
  · rintro ⟨-, hne, R, ⟨M, hM, P, rfl⟩, hRJ, hRN⟩
    exact ⟨hJ.1, hne, _, ⟨M, hM.1, P, rfl⟩, hRJ, hRN⟩
  · rintro ⟨-, hne, R, hR, hRJ, hRN⟩
    have hsyl : IsSylow2In R J := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΨ
        hJ.1 hR hRJ
    exact ⟨hJ, hne, R, mem_RSet_of_isSylow2In hJ hsyl, hRJ, hRN⟩

theorem link_path (hΨ : HypOmegaMod Ψ) (hk : ∀ g : X, conjSub g k = k)
    (hconn : DConnected (restrictFamily (linkFam Ψ k) (linkGen Ψ k))) {B₀ B : Subgroup X}
    (hB₀ : B₀ ∈ linkFam Ψ k) (hB : B ∈ linkFam Ψ k) :
    Relation.ReflTransGen
      (fun A C => C ∈ linkFam Ψ k ∧ (C ∈ omegaNbr Ψ A ∨ A ∈ omegaNbr Ψ C)) B₀ B := by
  exact CFSG.ClassicalInvolution.Asc77.T8ZZ.link_pathE
    (fun hJ => omegaNbr_linkFam_iff (k := k) hΨ hJ) hconn hB₀ hB

theorem aEmpty_linkFam (hΨ : HypOmegaMod Ψ) (hA : ∀ B ∈ Ψ, AEmpty Ψ B) :
    ∀ B ∈ linkFam Ψ k, AEmpty (linkFam Ψ k) B := by
  intro B hB J hJstar hJnbr zB zJ hzB hzJ
  obtain ⟨hJΨ', hne, U, hU, hUJ, hUN⟩ := hJstar
  have h1 : J ∈ omegaStarNbr Ψ B := ⟨hJΨ'.1, hne, U, uSet_linkFam_subset hU, hUJ, hUN⟩
  have h2 : J ∉ omegaNbr Ψ B := fun h => hJnbr ((omegaNbr_linkFam_iff hΨ hJΨ').mpr h)
  exact hA B hB.1 J h1 h2 zB zJ hzB hzJ

theorem link_dichotomy {n : ℕ} (hih : Uniform.IH8T 3 1 n) (hn : Uniform.CITBelowT (.sl2 3 1) n)
    (hlt : Nat.card X < n) (hΨ : Uniform.HypOmegaModU (.sl2 3 1) Ψ) (hA : ∀ B ∈ Ψ, AEmpty Ψ B)
    (hOX : classicalInvolutionOddCore X = ⊥) (hk : ∀ g : X, conjSub g k = k)
    (B : Fin 3 → Subgroup X) (hB : ∀ i, B i ∈ linkFam Ψ k) (hinj : Function.Injective B)
    (hadj : ∀ i j, i ≠ j → B j ∈ omegaNbr Ψ (B i)) :
    DConnected (restrictFamily (linkFam Ψ k) (linkGen Ψ k)) ∨
      ∃ C : Fin 3 → Subgroup X, (∀ i, C i ∈ linkFam Ψ k) ∧ Function.Injective C ∧
        ∀ i, C i ∈ omegaNbr Ψ (B 0) := by
  classical
  by_cases hconn : DConnected (restrictFamily (linkFam Ψ k) (linkGen Ψ k))
  · exact Or.inl hconn
  right
  set H := linkGen Ψ k with hH
  have hΨg : HypOmegaMod Ψ := Uniform.hypOmegaGenU_of_modU (Uniform.MemberType.cert_sl2 3 1) hΨ
  have hΨ' : Uniform.HypOmegaModU (.sl2 3 1) (linkFam Ψ k) := hypOmegaModU_linkFam hΨ hk
  have hΨ'g : HypOmegaMod (linkFam Ψ k) :=
    Uniform.hypOmegaGenU_of_modU (Uniform.MemberType.cert_sl2 3 1) hΨ'
  have hNorm : H.Normal := linkGen_normal hΨ.conjInvariant hk
  have hΛ := Q3T6.hypOmegaModU_restrict hΨ' H
  have hO : classicalInvolutionOddCore ↥H = ⊥ := oddCore_normal_eq_bot H hOX
  have hgen := omegaGen_restrictFamily_omegaGen (linkFam Ψ k)
  have hAH : ∀ L ∈ restrictFamily (linkFam Ψ k) H, AEmpty (restrictFamily (linkFam Ψ k) H) L := by
    rintro _ ⟨B', hB', hB'H, rfl⟩
    exact C25J.aEmpty_restrict_gen hΨ'g hB'H (aEmpty_linkFam hΨg hA B' hB')
  have hBH : ∀ i, B i ≤ H := fun i => le_omegaGen (hB i)
  have hcardH : Nat.card H < n := (Subgroup.card_le_card_group H).trans_lt hlt
  have hinj' : Function.Injective (fun i => (B i).subgroupOf H) := by
    intro i j hij
    apply hinj
    have := Subgroup.subgroupOf_inj.mp hij
    rwa [inf_eq_left.mpr (hBH i), inf_eq_left.mpr (hBH j)] at this
  obtain ⟨e, ⟨M⟩⟩ := T8X.exists_spin8_datum_of_triangle hih hn hcardH hΛ hO hgen hAH
    (fun i => (B i).subgroupOf H) (fun i => subgroupOf_mem_restrictFamily (hB i) (hBH i)) hinj'
    (fun i j hij => C25J.omegaNbr_subgroupOf_gen hΨ'g (hBH i) (hBH j) (hB j)
      ((omegaNbr_linkFam_iff hΨg (hB j)).mpr (hadj i j hij))) hconn
  have hD4 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .trialityD4 := by decide
  have hG2 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .G2 := by decide
  have he : e = 1 := M.exp_eq_f hD4
  subst he
  have hne : (restrictFamily (linkFam Ψ k) H).Nonempty :=
    ⟨_, subgroupOf_mem_restrictFamily (hB 0) (hBH 0)⟩
  obtain ⟨R₁, hR₁, hB0⟩ := (M.mem_iff _).mp (subgroupOf_mem_restrictFamily (hB 0) (hBH 0))
  obtain ⟨R₂, h₂, R₃, h₃, R₄, h₄, n12, n13, n14, n23, n24, n34, c12, c13, c14, -, -, -, -⟩ :=
    Q3MT.clique_plus3 (M.cls_sub hR₁)
  have m₂ := M.fund_subset_cls hne hG2 hD4 h₂
  have m₃ := M.fund_subset_cls hne hG2 hD4 h₃
  have m₄ := M.fund_subset_cls hne hG2 hD4 h₄
  let Rr : Fin 3 → Subgroup (modelUniv CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus 4 3 1
    Fact.out).K := ![R₂, R₃, R₄]
  have hRr : ∀ i, Rr i ∈ M.cls := by
    intro i
    fin_cases i <;> assumption
  have hRrne : ∀ i, R₁ ≠ Rr i := by
    intro i
    fin_cases i <;> assumption
  have hRrc : ∀ i, Commutes R₁ (Rr i) := by
    intro i
    fin_cases i <;> assumption
  have hRrd : ∀ i j : Fin 3, i ≠ j → Rr i ≠ Rr j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [Rr] at hij ⊢ <;> first | assumption | exact Ne.symm ‹_›
  have hCmem : ∀ i, ((Rr i).map M.ψ).map H.subtype ∈ linkFam Ψ k := fun i =>
    mem_restrictFamily_iff.mp (M.map_mem (hRr i))
  refine ⟨fun i => ((Rr i).map M.ψ).map H.subtype, hCmem, ?_, fun i => ?_⟩
  · intro i j h
    by_contra hij
    have h1 := Subgroup.map_injective H.subtype_injective h
    exact hRrd i j hij (Q3MT.map_inj3 M hG2 hD4 (hRr i) (hRr j) h1)
  · have h1 : (Rr i).map M.ψ ∈ omegaNbr (restrictFamily (linkFam Ψ k) H) (R₁.map M.ψ) :=
      (Q3MT.omegaNbr_iff3 M hΛ hG2 hD4 hR₁ (hRr i)).mpr ⟨hRrne i, hRrc i⟩
    have h2 := omegaNbr_map h1
    rw [← hB0, Subgroup.map_subgroupOf_eq_of_le (hBH 0)] at h2
    exact (omegaNbr_linkFam_iff hΨg (hCmem i)).mp h2
end Link
end T8ZZ
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
