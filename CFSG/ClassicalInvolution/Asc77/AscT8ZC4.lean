module

import CFSG.ClassicalInvolution.Asc77.AscT8ZC4Eng
public import CFSG.ClassicalInvolution.Asc77.AscIHSectL
public import CFSG.ClassicalInvolution.Asc77.AscMuTabD4
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab

namespace T8ZZ

section Link

variable {X : Type} [Group X] {Ψ : Set (Subgroup X)} {k : Subgroup X}

@[expose] def linkFam (Ψ : Set (Subgroup X)) (k : Subgroup X) : Set (Subgroup X) :=
  {B | B ∈ Ψ ∧ B ≠ k}

@[expose] def linkGen (Ψ : Set (Subgroup X)) (k : Subgroup X) : Subgroup X :=
  omegaGen (linkFam Ψ k)

theorem conjInvariant_linkFam (hΨ : ConjInvariant Ψ) (hk : ∀ g : X, conjSub g k = k) :
    ConjInvariant (linkFam Ψ k) := by
  intro g B hB
  refine ⟨hΨ g B hB.1, fun h => hB.2 ?_⟩
  have := congrArg (conjSub g⁻¹) h
  rwa [conjSub_inv_conjSub, hk] at this

theorem linkGen_normal (hΨ : ConjInvariant Ψ) (hk : ∀ g : X, conjSub g k = k) :
    (linkGen Ψ k).Normal :=
  omegaGen_normal (conjInvariant_linkFam hΨ hk)

variable [Finite X] {p f : ℕ} [Fact p.Prime]

theorem hypOmegaMod_linkFam (hΨ : HypOmegaMod p f Ψ) (hk : ∀ g : X, conjSub g k = k) :
    HypOmegaMod p f (linkFam Ψ k) where
  conjInvariant := conjInvariant_linkFam hΨ.conjInvariant hk
  classical := fun L hL => hΨ.classical L hL.1
  omega4 := fun K hK J hJ hne => hΨ.omega4 K hK.1 J hJ.1 hne
  omega5 := fun K hK J hJ hne z hz v hv hnc hv2 hvz =>
    hΨ.omega5 K hK.1 J hJ.1 hne z hz v hv hnc hv2 hvz

theorem noTwins_link (hnt : ∀ B ∈ Ψ, ∀ B' ∈ twinSet Ψ B, B' = B) :
    ∀ L ∈ restrictFamily (linkFam Ψ k) (linkGen Ψ k),
      ∀ L' ∈ twinSet (restrictFamily (linkFam Ψ k) (linkGen Ψ k)) L, L' = L := by
  rintro _ ⟨A, hA, hAH, rfl⟩ L' hL'
  have h1 := twinSet_map hAH hL'
  obtain ⟨hJ, w, hwA, hwJ⟩ := h1
  have h2 : L'.map (linkGen Ψ k).subtype = A :=
    hnt A hA.1 _ ⟨hJ.1, w, hwA, hwJ⟩
  calc L' = (L'.map (linkGen Ψ k).subtype).subgroupOf (linkGen Ψ k) :=
        (subgroupOf_map_subtype' L').symm
    _ = A.subgroupOf (linkGen Ψ k) := by rw [h2]

theorem omegaNbr_linkFam_iff (hp : p ≠ 2) (hΨ : HypOmegaMod p f Ψ) {J K : Subgroup X}
    (hJ : J ∈ linkFam Ψ k) : J ∈ omegaNbr (linkFam Ψ k) K ↔ J ∈ omegaNbr Ψ K := by
  constructor
  · rintro ⟨-, hne, R, ⟨M, hM, P, rfl⟩, hRJ, hRN⟩
    exact ⟨hJ.1, hne, _, ⟨M, hM.1, P, rfl⟩, hRJ, hRN⟩
  · rintro ⟨-, hne, R, hR, hRJ, hRN⟩
    have hsyl : IsSylow2In R J := T3.isSylow2In_of_mem_RSet_of_le hp hΨ hJ.1 hR hRJ
    exact ⟨hJ, hne, R, mem_RSet_of_isSylow2In hJ hsyl, hRJ, hRN⟩

theorem link_path (hp : p ≠ 2) (hΨ : HypOmegaMod p f Ψ) (hk : ∀ g : X, conjSub g k = k)
    (hconn : DConnected (restrictFamily (linkFam Ψ k) (linkGen Ψ k))) {B₀ B : Subgroup X}
    (hB₀ : B₀ ∈ linkFam Ψ k) (hB : B ∈ linkFam Ψ k) :
    Relation.ReflTransGen
      (fun A C => C ∈ linkFam Ψ k ∧ (C ∈ omegaNbr Ψ A ∨ A ∈ omegaNbr Ψ C)) B₀ B := by
  exact link_pathE (fun hJ => omegaNbr_linkFam_iff (k := k) hp hΨ hJ) hconn hB₀ hB

theorem link_dichotomy {n : ℕ} (hn : CITBelowU p f n) (hlt : Nat.card X < n) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΨ : HypOmegaMod p f Ψ) (hnt : ∀ B ∈ Ψ, ∀ B' ∈ twinSet Ψ B, B' = B)
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
  have hΨ' : HypOmegaMod p f (linkFam Ψ k) := hypOmegaMod_linkFam hΨ hk
  have hNorm : H.Normal := linkGen_normal hΨ.conjInvariant hk
  have hΛ := hΨ'.restrict H
  have hO : classicalInvolutionOddCore ↥H = ⊥ := oddCore_normal_eq_bot H hOX
  have hgen := omegaGen_restrictFamily_omegaGen (linkFam Ψ k)
  have hntH := noTwins_link (k := k) hnt
  have hBH : ∀ i, B i ≤ H := fun i => le_omegaGen (hB i)
  have hcardH : Nat.card H < n := (Subgroup.card_le_card_group H).trans_lt hlt
  have hinj' : Function.Injective (fun i => (B i).subgroupOf H) := by
    intro i j hij
    apply hinj
    have := Subgroup.subgroupOf_inj.mp hij
    rwa [inf_eq_left.mpr (hBH i), inf_eq_left.mpr (hBH j)] at this
  obtain ⟨e, ⟨M⟩⟩ := T8X.exists_spin8_datum_of_triangle hn hcardH hp hq hΛ hO hgen hntH
    (fun i => (B i).subgroupOf H) (fun i => subgroupOf_mem_restrictFamily (hB i) (hBH i)) hinj'
    (fun i j hij => omegaNbr_subgroupOf hp hΨ' (hBH i) (hBH j) (hB j)
      ((omegaNbr_linkFam_iff hp hΨ (hB j)).mpr (hadj i j hij))) hconn
  have hD4 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .trialityD4 := by decide
  have hG2 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .G2 := by decide
  have he : e = f := M.exp_eq_f hD4
  have hq' : 5 ≤ p ^ e := he ▸ hq
  have hne : (restrictFamily (linkFam Ψ k) H).Nonempty :=
    ⟨_, subgroupOf_mem_restrictFamily (hB 0) (hBH 0)⟩
  obtain ⟨R₁, hR₁, hB0⟩ := (M.mem_iff _).mp (subgroupOf_mem_restrictFamily (hB 0) (hBH 0))
  obtain ⟨R₂, h₂, R₃, h₃, R₄, h₄, n12, n13, n14, n23, n24, n34, c12, c13, c14, -, -, -, -⟩ :=
    MuTab.clique_plus hp hq' M.admissible (M.cls_sub hR₁)
  have m₂ := M.fund_subset_cls hne hG2 hD4 h₂
  have m₃ := M.fund_subset_cls hne hG2 hD4 h₃
  have m₄ := M.fund_subset_cls hne hG2 hD4 h₄
  let Rr : Fin 3 → Subgroup (modelUniv CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus 4 p e
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
    exact hRrd i j hij (M.muTab_map_inj hp hq hD4 (hRr i) (hRr j) h1)
  · have h1 : (Rr i).map M.ψ ∈ omegaNbr (restrictFamily (linkFam Ψ k) H) (R₁.map M.ψ) :=
      (M.muTab_omegaNbr_iff hΛ hp hq hG2 hD4 hR₁ (hRr i)).mpr ⟨hRrne i, hRrc i⟩
    have h2 := omegaNbr_map h1
    rw [← hB0, Subgroup.map_subgroupOf_eq_of_le (hBH 0)] at h2
    exact (omegaNbr_linkFam_iff hp hΨ (hCmem i)).mp h2

end Link

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
