module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenPermCases
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaShapes
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.KerThetaTwoCore
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLGroup

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

open scoped Classical in
theorem eightTen_cases_of_natural (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) {m : ℕ} (hm : 8 < m)
    (e : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m))
    (hN : NaturalSectionLSL S L m) :
    ∃ θ : ↥(L ⊔ S) →* Perm (Fin m), NaturalSectionTheta S L m θ ∧
      (∀ m' : ↥(L ⊔ S), θ m' = 1 → (m' : G) ∈ S) ∧
      (((∃ r s : ℕ, 1 ≤ r ∧ 1 ≤ s ∧ 2 * r + s = m ∧ EightBlockData (L ⊔ S) S L r s ∧ EightBlockDataX S L r s ∧
        HasSym3Lift S L (L ⊔ S) ∧
        ((r = 1 ∨ r = 3 ∨ 5 ≤ r) → (s = 1 ∨ s = 3 ∨ 5 ≤ s) → HasSym3LiftS S L (L ⊔ S)) ∧
        ThetaTypeI S L r s ∧
        ∃ e : Fin m ≃ OmegaE r s,
          ((thompsonJ S).subgroupOf (L ⊔ S)).map (e.permCongrHom.toMonoidHom.comp θ) = Wr r s) ∨
        (∃ n : ℕ, 5 ≤ n ∧ 2 * n = m ∧ PairActionData (L ⊔ S) S L n)) ∨
      (∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ∃ x : Fin m,
        Nat.card (orbit ((A.subgroupOf (L ⊔ S)).map θ) x) = 4) ∨
      (∃ (A : Subgroup G) (σ : Perm (Fin m)) (c : Fin m → Bool), IsMaxElemAbelian S A ∧
        BlockData ((A.subgroupOf (L ⊔ S)).map θ) σ c ∧ ∃ x, (cls c x).card = 4) ∨
      ∃ σ : Perm (Fin m), ∃ (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x),
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m))) ≤
          pairPres σ hσ1 hσ2 ∧
        (∀ x y, y ≠ x → y ≠ σ x →
          swap x (σ x) ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m))) →
          swap y (σ y) ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m))) →
          swap x (σ x) * swap y (σ y) ∈
            (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))) ∧
        (Finset.univ.filter fun x : Fin m => swap x (σ x) ∉
          (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))).card ≠ 2 * 1 ∧
        (Finset.univ.filter fun x : Fin m => swap x (σ x) ∉
          (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))).card ≠ 2 * 2 ∧
        (Finset.univ.filter fun x : Fin m => swap x (σ x) ∈
          (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))).card ≠ 2 * 2 ∧
      (∀ n : ℕ, 5 ≤ n → 2 * n = m →
        (Finset.univ.filter fun x : Fin m => swap x (σ x) ∉
          (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))).card ≠ 2 * 4 →
        (Finset.univ.filter fun x : Fin m => swap x (σ x) ∈
          (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))).card ≠ 2 * 4 → PairActionData (L ⊔ S) S L n)) := by
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  have hLs : IsTwoPrimeComponent (L ⊔ S) L :=
    CFSG.HardMathSupport.Cooperstein.Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent
      hA.twoRadical.1 hA.twoRadical.isPGroup hSL
  have hA' : Asc81bHyp (L ⊔ S) S := Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hZ : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (card_center_barM_sup_eq_one hA' hLs hSL hm e)
  have hVS : blockV S L ≤ S := Coordinator.blockV_le hA hL hSL
  have hVN : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) := Coordinator.sup_le_normalizer_blockV S L
  have hV : CFSG.Open.IsElemAbelian 2 (blockV S L) := CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _
  obtain ⟨θ, hNS, hAlt, hkerC, hsh⟩ := hN.exists_theta_section_shapes (Or.inr (by omega)) hVS hVN hV
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
  refine ⟨θ, hNS, fun m' h => hpS ((hkerP m').1 h), ?_⟩
  have hcard : 9 ≤ Fintype.card (Fin m) := by simp; omega
  have hne : ((thompsonJ S).subgroupOf (L ⊔ S)).map θ ≠ ⊥ := by
    obtain ⟨A, hAmax, hAQ⟩ := Coordinator.exists_isMaxElemAbelian_not_le hA hL hSL
    obtain ⟨a, haA, haQ⟩ := Set.not_subset.1 hAQ
    have haJ : a ∈ thompsonJ S :=
      (le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S A) => A) A hAmax) haA
    have haM : a ∈ L ⊔ S := (le_sup_right : S ≤ L ⊔ S) (hAmax.1 haA)
    intro hbot
    have h1 : θ ⟨a, haM⟩ ∈ (⊥ : Subgroup (Perm (Fin m))) := hbot ▸
      Subgroup.mem_map_of_mem θ (Subgroup.mem_subgroupOf.2 haJ)
    exact haQ ((hkerP ⟨a, haM⟩).1 (Subgroup.mem_bot.1 h1))
  simpa using eightTen_perm_cases hA' hLs hSL hpS hcard θ hkerP hAlt hsh hne

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
