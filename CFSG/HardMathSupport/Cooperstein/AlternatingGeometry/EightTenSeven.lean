module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.KerThetaTwoCore
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.SwapTypeCases
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaShapes
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLGroup

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

theorem swapType_of_odd {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hodd : Odd (Fintype.card Ω)) {E : Subgroup (Perm Ω)} (h : OffenderShapeConcl E) :
    SwapType E := by
  by_cases hf : ∃ p, ∀ g ∈ E, g p = p
  · exact h.1 hf
  · exfalso
    have heven : ∀ i : Ω, Even (Nat.card (orbit E i)) := by
      rcases h.2 hf with ⟨hall, -⟩ | ⟨-, h24, -⟩
      · intro i; rw [hall i]; exact even_two
      · intro i
        rcases h24 i with h2 | h4
        · rw [h2]; exact even_two
        · rw [h4]; exact ⟨2, rfl⟩
    have hsum := card_eq_sum_orbits E
    have hev : Even (Nat.card Ω) := by
      rw [hsum]
      exact Finset.sum_induction _ Even (fun a b ha hb => ha.add hb) (by decide : Even 0)
        (fun ω _ => heven _)
    rw [Nat.card_eq_fintype_card] at hev
    exact (Nat.not_even_iff_odd.2 hodd) hev

open scoped Classical in
theorem eightTen_cases_of_natural_seven {G : Type} [Group G] [Finite G]
    {X S L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hZ : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥)
    (hN : NaturalSectionLSL S L 7) :
    ∃ θ : ↥(L ⊔ S) →* Perm (Fin 7), ∃ r s : ℕ, 1 ≤ r ∧ 1 ≤ s ∧ 2 * r + s = 7 ∧
      EightBlockData (L ⊔ S) S L r s ∧ EightBlockDataX S L r s ∧ HasSym3Lift S L (L ⊔ S) ∧
      ((r = 1 ∨ r = 3 ∨ 5 ≤ r) → (s = 1 ∨ s = 3 ∨ 5 ≤ s) → HasSym3LiftS S L (L ⊔ S)) := by
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  have hLs : IsTwoPrimeComponent (L ⊔ S) L :=
    CFSG.HardMathSupport.Cooperstein.Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent
      hA.twoRadical.1 hA.twoRadical.isPGroup hSL
  have hA' : Asc81bHyp (L ⊔ S) S := Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hVS : blockV S L ≤ S := Coordinator.blockV_le hA hL hSL
  have hVN : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) := Coordinator.sup_le_normalizer_blockV S L
  have hV : CFSG.Open.IsElemAbelian 2 (blockV S L) := CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _
  obtain ⟨θ, hAlt, hkerC, hsh⟩ := hN.exists_theta_shapes (Or.inl rfl) hVS hVN hV
  have hpS : pCoreOf 2 (L ⊔ S) ≤ S := Coordinator.twoCore_sup_le hA hL hSL
  have hkerP : ∀ m' : ↥(L ⊔ S), θ m' = 1 ↔ (m' : G) ∈ pCoreOf 2 (L ⊔ S) := by
    intro m'
    rw [hkerC]
    constructor
    · intro h
      exact inf_centralizer_blockV_le_pCoreOf hA' hLs hSL
        (Coordinator.not_le_centralizer_blockV hA hL hSL) hZ ⟨m'.2, h⟩
    · intro h
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (CFSG.HardMathSupport.Cooperstein.StructureLie.commute_of_mem_pCoreOf_blockV h hv).symm
  have hodd : Odd (Fintype.card (Fin 7)) := ⟨3, by simp⟩
  have hne : ((thompsonJ S).subgroupOf (L ⊔ S)).map θ ≠ ⊥ := by
    obtain ⟨A, hAmax, hAQ⟩ := Coordinator.exists_isMaxElemAbelian_not_le hA hL hSL
    obtain ⟨a, haA, haQ⟩ := Set.not_subset.1 hAQ
    have haJ : a ∈ thompsonJ S :=
      (le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S A) => A) A hAmax) haA
    have haM : a ∈ L ⊔ S := (le_sup_right : S ≤ L ⊔ S) (hAmax.1 haA)
    intro hbot
    have h1 : θ ⟨a, haM⟩ ∈ (⊥ : Subgroup (Perm (Fin 7))) := hbot ▸
      Subgroup.mem_map_of_mem θ (Subgroup.mem_subgroupOf.2 haJ)
    exact haQ ((hkerP ⟨a, haM⟩).1 (Subgroup.mem_bot.1 h1))
  have hres := eightTen_swapType_cases hA' hLs hSL hpS (Or.inr ⟨by simp, hodd⟩) θ hkerP hAlt
    (fun A hA'' => swapType_of_odd hodd (hsh A hA'')) hne
  rcases hres with ⟨r, s, h1, h2, h3, h4, h5, h6, h7, -⟩ | ⟨n, -, h2n, -⟩
  · exact ⟨θ, r, s, h1, h2, by simpa using h3, h4, h5, h6, h7⟩
  · exfalso
    rcases hodd with ⟨k, hk⟩
    simp at h2n
    omega

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
