module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffendersDichotomy
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.SwapTypeCases

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

variable {G : Type} [Group G] [Finite G] {S L : Subgroup G}

theorem iSup_offenders_eq_map_thompsonJ {M : Subgroup G} (hSM : S ≤ M) {Ω : Type*}
    (θ : ↥M →* Perm Ω) :
    (⨆ A : {A : Subgroup G // IsMaxElemAbelian S A}, (A.1.subgroupOf M).map θ) =
      ((thompsonJ S).subgroupOf M).map θ := by
  rw [map_thompsonJ_eq_iSup hSM θ]
  apply le_antisymm
  · exact iSup_le fun A =>
      le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S A) =>
        (A.subgroupOf M).map θ) A.1 A.2
  · exact iSup_le fun A => iSup_le fun hA =>
      le_iSup (fun A : {A : Subgroup G // IsMaxElemAbelian S A} => (A.1.subgroupOf M).map θ) ⟨A, hA⟩

open scoped Classical in
theorem eightTen_perm_cases (hA : Asc81bHyp (L ⊔ S) S)
    (hLM : IsTwoPrimeComponent (L ⊔ S) L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hpS : pCoreOf 2 (L ⊔ S) ≤ S)
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (hΩ : 9 ≤ Fintype.card Ω)
    (θ : ↥(L ⊔ S) →* Perm Ω)
    (hker : ∀ m : ↥(L ⊔ S), θ m = 1 ↔ (m : G) ∈ pCoreOf 2 (L ⊔ S))
    (hAltL : ∀ x ∈ alternatingGroup Ω,
      ∃ l : ↥L, θ ⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩ = x)
    (hsh : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      OffenderShapeConcl ((A.subgroupOf (L ⊔ S)).map θ))
    (hne : ((thompsonJ S).subgroupOf (L ⊔ S)).map θ ≠ ⊥) :
    ((∃ r s : ℕ, 1 ≤ r ∧ 1 ≤ s ∧ 2 * r + s = Fintype.card Ω ∧ EightBlockData (L ⊔ S) S L r s ∧ EightBlockDataX S L r s ∧
        HasSym3Lift S L (L ⊔ S) ∧
        ((r = 1 ∨ r = 3 ∨ 5 ≤ r) → (s = 1 ∨ s = 3 ∨ 5 ≤ s) → HasSym3LiftS S L (L ⊔ S)) ∧
        ThetaTypeI S L r s ∧
        ∃ e : Ω ≃ OmegaE r s,
          ((thompsonJ S).subgroupOf (L ⊔ S)).map (e.permCongrHom.toMonoidHom.comp θ) = Wr r s) ∨
      (∃ n : ℕ, 5 ≤ n ∧ 2 * n = Fintype.card Ω ∧ PairActionData (L ⊔ S) S L n)) ∨
    (∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ∃ x : Ω,
      Nat.card (orbit ((A.subgroupOf (L ⊔ S)).map θ) x) = 4) ∨
    (∃ (A : Subgroup G) (σ : Perm Ω) (c : Ω → Bool), IsMaxElemAbelian S A ∧
      BlockData ((A.subgroupOf (L ⊔ S)).map θ) σ c ∧ ∃ x, (cls c x).card = 4) ∨
    ∃ σ : Perm Ω, ∃ (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x),
      (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω)) ≤ pairPres σ hσ1 hσ2 ∧
      (∀ x y, y ≠ x → y ≠ σ x →
        swap x (σ x) ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω)) →
        swap y (σ y) ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω)) →
        swap x (σ x) * swap y (σ y) ∈
          (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω))) ∧
      (Finset.univ.filter fun x : Ω => swap x (σ x) ∉
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω))).card ≠ 2 * 1 ∧
      (Finset.univ.filter fun x : Ω => swap x (σ x) ∉
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω))).card ≠ 2 * 2 ∧
      (Finset.univ.filter fun x : Ω => swap x (σ x) ∈
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω))).card ≠ 2 * 2 ∧
      (∀ n : ℕ, 5 ≤ n → 2 * n = Fintype.card Ω →
        (Finset.univ.filter fun x : Ω => swap x (σ x) ∉
          (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω))).card ≠ 2 * 4 →
        (Finset.univ.filter fun x : Ω => swap x (σ x) ∈
          (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω))).card ≠ 2 * 4 → PairActionData (L ⊔ S) S L n) := by
  classical
  have hP : IsPGroup 2 ((S.subgroupOf (L ⊔ S)).map θ) :=
    (hA.twoRadical.isPGroup.comap_subtype (K := L ⊔ S)).map θ
  let E : {A : Subgroup G // IsMaxElemAbelian S A} → Subgroup (Perm Ω) :=
    fun A => (A.1.subgroupOf (L ⊔ S)).map θ
  have hEP : ∀ A, E A ≤ (S.subgroupOf (L ⊔ S)).map θ := fun A =>
    Subgroup.map_mono (Subgroup.comap_mono A.2.1)
  rcases offenders_dichotomy hΩ hP E hEP (fun A => hsh A.1 A.2) with h | ⟨A, x, hx⟩ |
    ⟨A, σ, c, hbd, hc⟩ | ⟨σ, hσ1, hσ2, hle, hD, hN1, hN2, hC2⟩
  · exact Or.inl (eightTen_swapType_cases hA hLM hSL hpS (Or.inl hΩ) θ hker hAltL
      (fun A hA' => h ⟨A, hA'⟩) hne)
  · exact Or.inr (Or.inl ⟨A.1, A.2, x, hx⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨A.1, σ, c, A.2, hbd, hc⟩))
  · rw [iSup_offenders_eq_map_thompsonJ (le_sup_right : S ≤ L ⊔ S) θ] at hle hD hN1 hN2 hC2
    refine Or.inr (Or.inr (Or.inr ⟨σ, hσ1, hσ2, hle, hD, hN1, hN2, hC2, ?_⟩))
    intro n hn5 hn h8 hc8
    exact pairActionData_of_theta_perm hA hLM hSL hpS θ hker hAltL σ hσ1 hσ2 n hn.symm hn5 hle hD
      hN1 hN2 h8 hC2 hc8

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
