module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigiditySL
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigidityFieldRigid
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionB
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect
  perfectCore_perfect map_perfectCore)

section Dedekind

variable {G : Type*} [Group G]

theorem sup_inf_eq_of_le_normalizer {Q M C : Subgroup G} (hMN : M ≤ normalizer (Q : Set G))
    (hQC : Q ≤ C) : (Q ⊔ M) ⊓ C = Q ⊔ (M ⊓ C) := by
  apply le_antisymm
  · rintro x ⟨hx, hxC⟩
    have hx' : x ∈ ((Q ⊔ M : Subgroup G) : Set G) := hx
    rw [coe_mul_of_right_le_normalizer_left Q M hMN] at hx'
    obtain ⟨q, hq, m, hm, rfl⟩ := hx'
    have hmC : m ∈ C := by
      have : m = q⁻¹ * (q * m) := by group
      rw [this]
      exact C.mul_mem (C.inv_mem (hQC hq)) hxC
    exact mul_mem_sup hq ⟨hm, hmC⟩
  · exact sup_le (le_inf le_sup_left hQC) (inf_le_inf_right C le_sup_right)

theorem map_centralizer_mulAut (β : MulAut G) (H : Subgroup G) :
    (centralizer (H : Set G)).map β.toMonoidHom =
      centralizer ((H.map β.toMonoidHom : Subgroup G) : Set G) := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨h, hh, rfl⟩
    change β h * β y = β y * β h
    rw [← map_mul, ← map_mul, hy h hh]
  · refine ⟨β.symm x, fun h hh => β.injective ?_, β.apply_symm_apply x⟩
    rw [map_mul, map_mul, β.apply_symm_apply]
    exact hx (β h) ⟨h, hh, rfl⟩

variable [Finite G]

theorem sup_perfectCore_inf_eq {Q M C : Subgroup G} (hMN : M ≤ normalizer (Q : Set G))
    (hQC : Q ≤ C) : Q ⊔ perfectCore (M ⊓ C) = Q ⊔ perfectCore ((Q ⊔ M) ⊓ C) := by
  apply le_antisymm
  · exact sup_le_sup_left (perfectCore_mono (inf_le_inf_right C le_sup_right)) Q
  · rw [sup_inf_eq_of_le_normalizer hMN hQC]
    exact sup_le le_sup_left (E6Pilot.perfectCore_sup_le (inf_le_left.trans hMN))

end Dedekind

section Placement

variable {n k : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem InvPlacement.radicalP_sup_blockSL_eq (hq : 4 ≤ Nat.card K) (P : InvPlacement n k)
    (hJ : 2 ≤ P.free.card) :
    P.radicalP K ⊔ blockSL (K := K) P.free =
      P.radicalP K ⊔ perfectCore (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) ⊓
        centralizer ((⁅P.radicalP K, P.radicalP K⁆ : Subgroup (projectiveSL n K)) :
          Set (projectiveSL n K))) := by
  obtain ⟨-, hΛeq, -, hMN, hSeq⟩ := P.centralizer_inv_perfectCore hq (P.card_free ▸ hJ)
  conv_lhs => rw [hSeq]
  rw [hΛeq]
  exact sup_perfectCore_inf_eq hMN P.radicalP_le_centralizer_commutator

theorem InvPlacement.map_radicalP_eq_of_map_eq (hq : 4 ≤ Nat.card K) (P : InvPlacement n k)
    (hJ : 2 ≤ P.free.card) (β : MulAut (projectiveSL n K))
    (hβ : (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map β.toMonoidHom =
      perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))) :
    (P.radicalP K).map β.toMonoidHom = P.radicalP K := by
  obtain ⟨hQp, hΛeq, -, hMN, -⟩ := P.centralizer_inv_perfectCore hq (P.card_free ▸ hJ)
  have hQΛ : P.radicalP K ≤ perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) := by
    rw [hΛeq]
    exact le_sup_left
  have hΛN : perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) ≤
      normalizer (P.radicalP K : Set (projectiveSL n K)) := by
    rw [hΛeq]
    exact sup_le le_normalizer hMN
  have hle : (P.radicalP K).map β.toMonoidHom ≤ P.radicalP K := by
    refine P.le_radicalP_of_isPGroup_perfectCore hq hJ (hQp.map _) ?_ ?_
    · rw [← hβ]
      exact map_mono hQΛ
    · rw [← hβ]
      exact (map_mono hΛN).trans (le_normalizer_map _)
  exact eq_of_le_of_card_ge hle (card_map_of_injective β.injective).ge

theorem InvPlacement.map_radicalP_sup_blockSL_eq_of_map_eq (hq : 4 ≤ Nat.card K)
    (P : InvPlacement n k) (hJ : 2 ≤ P.free.card) (β : MulAut (projectiveSL n K))
    (hβ : (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map β.toMonoidHom =
      perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))) :
    (P.radicalP K ⊔ blockSL (K := K) P.free).map β.toMonoidHom =
      P.radicalP K ⊔ blockSL (K := K) P.free := by
  have hQ := P.map_radicalP_eq_of_map_eq hq hJ β hβ
  rw [P.radicalP_sup_blockSL_eq hq hJ, Subgroup.map_sup, hQ, map_perfectCore,
    Subgroup.map_inf_eq _ _ _ β.injective, hβ, map_centralizer_mulAut, Subgroup.map_commutator, hQ]

end Placement

section Complements

variable {G : Type*} [Group G]

theorem exists_mulAut_complement {Q S : Subgroup G} (hSN : S ≤ normalizer (Q : Set G))
    (hQS : Disjoint Q S) (γ : G) (hγQ : Q.map (MulAut.conj γ).toMonoidHom = Q)
    (hγM : (Q ⊔ S).map (MulAut.conj γ).toMonoidHom = Q ⊔ S) :
    ∃ γbar : MulAut S, ∀ s : S, ((γbar s : S) : G)⁻¹ * (γ * s * γ⁻¹) ∈ Q := by
  set S' := S.map (MulAut.conj γ).toMonoidHom with hS'
  set e₁ : S ≃* S' := S.equivMapOfInjective _ (MulAut.conj γ).injective with he₁
  have hS'N : S' ≤ normalizer (Q : Set G) := by
    rw [hS', ← hγQ]
    exact (map_mono hSN).trans (le_normalizer_map _)
  have hQS' : Disjoint Q S' := by
    rw [hS', ← hγQ]
    exact disjoint_map_of_injective (MulAut.conj γ).injective hQS
  have hM' : Q ⊔ S' = Q ⊔ S := by
    conv_lhs => rw [← hγQ]
    rw [hS', ← Subgroup.map_sup, hγM]
  set ι := EPilot.mulEquivOfComplements hS'N hQS' hQS hM' with hι
  refine ⟨e₁.trans ι, fun s => ?_⟩
  have h := EPilot.mulEquivOfComplements_inv_mul_mem hS'N hQS' hQS hM' (e₁ s)
  have he : ((e₁ s : S') : G) = γ * s * γ⁻¹ := rfl
  rw [he] at h
  exact h

theorem complement_intertwine {Q S₁ S₂ : Subgroup G} (hSN : S₁ ≤ normalizer (Q : Set G))
    (hQS₁ : Disjoint Q S₁) (hQS₂ : Disjoint Q S₂) (hM : Q ⊔ S₁ = Q ⊔ S₂) {γ : G}
    (hγQ : Q.map (MulAut.conj γ).toMonoidHom = Q) (γ₁ : MulAut S₁) (γ₂ : MulAut S₂)
    (hγ₁ : ∀ s : S₁, ((γ₁ s : S₁) : G)⁻¹ * (γ * s * γ⁻¹) ∈ Q)
    (hγ₂ : ∀ s : S₂, ((γ₂ s : S₂) : G)⁻¹ * (γ * s * γ⁻¹) ∈ Q) (s : S₁) :
    γ₂ (EPilot.mulEquivOfComplements hSN hQS₁ hQS₂ hM s) =
      EPilot.mulEquivOfComplements hSN hQS₁ hQS₂ hM (γ₁ s) := by
  set ι := EPilot.mulEquivOfComplements hSN hQS₁ hQS₂ hM with hι
  have hγQ' : ∀ x ∈ Q, γ * x * γ⁻¹ ∈ Q := fun x hx => by
    rw [← hγQ]
    exact ⟨x, hx, rfl⟩
  symm
  rw [EPilot.mulEquivOfComplements_eq_iff]
  have ha := hγ₂ (ι s)
  have hb : γ * (((ι s : S₂) : G)⁻¹ * s) * γ⁻¹ ∈ Q :=
    hγQ' _ (EPilot.mulEquivOfComplements_inv_mul_mem hSN hQS₁ hQS₂ hM s)
  have hc := Q.inv_mem (hγ₁ s)
  have e : ((γ₂ (ι s) : S₂) : G)⁻¹ * (γ₁ s : S₁) =
      (((γ₂ (ι s) : S₂) : G)⁻¹ * (γ * (ι s : S₂) * γ⁻¹)) *
        (γ * (((ι s : S₂) : G)⁻¹ * s) * γ⁻¹) *
          (((γ₁ s : S₁) : G)⁻¹ * (γ * s * γ⁻¹))⁻¹ := by group
  rw [e]
  exact Q.mul_mem (Q.mul_mem ha hb) hc

end Complements

section Rigid

variable {n k k' : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]

variable (K) in
@[expose] def InvPlacement.RestrictionField (hn : 3 ≤ n) (P : InvPlacement n k) : Prop :=
  ∀ β : MulAut (projectiveSL n K),
    (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map β.toMonoidHom =
      perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) →
    ∀ βbar : MulAut (blockSL (K := K) P.free),
      (∀ s : blockSL (K := K) P.free,
        ((βbar s : blockSL (K := K) P.free) : projectiveSL n K)⁻¹ * β s ∈ P.radicalP K) →
      ∀ (m : ℕ) (hm : 3 ≤ m) (κ : blockSL (K := K) P.free ≃* Matrix.SpecialLinearGroup (Fin m) K),
        slFieldPart hm (MulAut.congr κ βbar) = linearFieldPart K hn β

theorem fieldRigidIn_inner (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) (P : InvPlacement n k)
    (P' : InvPlacement n k') (hP : P.elt K ≠ 1) (hP' : P'.elt K ≠ 1) (hJ : 3 ≤ P.free.card)
    (hJ' : 3 ≤ P'.free.card) (hRC : P.RestrictionField K hn) (hRC' : P'.RestrictionField K hn) :
    FieldRigidIn hn (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
      (perfectCore (centralizer ({P'.elt K} : Set (projectiveSL n K)))) := by
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβX h₁ h₂
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => hP (P.elt_eq_one_of_eq_zero h)
  have hk' : 0 < k' := Nat.pos_of_ne_zero fun h => hP' (P'.elt_eq_one_of_eq_zero h)
  have hJ2 : 2 ≤ P.free.card := by omega
  have hJ'2 : 2 ≤ P'.free.card := by omega
  have hc₁ : ∀ X : Subgroup (projectiveSL n K),
      (X.map φ₁).map (MulAut.conj γ).toMonoidHom = (X.map β₁.toMonoidHom).map φ₁ := by
    intro X
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact (h₁ x).symm
  have hc₂ : ∀ X : Subgroup (projectiveSL n K),
      (X.map φ₂).map (MulAut.conj γ).toMonoidHom = (X.map β₂.toMonoidHom).map φ₂ := by
    intro X
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact (h₂ x).symm
  have hβ₁Λ : (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))).map
      β₁.toMonoidHom = perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) := by
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective β₁.injective).ge
    rintro _ ⟨x, hx, rfl⟩
    exact hβX x hx
  have hβ₂Λ : (perfectCore (centralizer ({P'.elt K} : Set (projectiveSL n K)))).map
      β₂.toMonoidHom = perfectCore (centralizer ({P'.elt K} : Set (projectiveSL n K))) := by
    apply Subgroup.map_injective hφ₂
    rw [← hc₂, ← hX, hc₁, hβ₁Λ]
  have hQ := map_radicalP_eq hq hφ₁ hφ₂ P P' hJ2 hJ'2 hX
  obtain ⟨-, hSN, hQS, hQS', hSS'⟩ := complements_map_blockSL hq hφ₁ hφ₂ P P' hJ2 hJ'2 hX
  have hcard := card_free_eq_of_map_perfectCore_eq hq hφ₁ hφ₂ P P' hk hk' hJ2 hJ'2 hX
  obtain ⟨-, hS'N, -, -, -⟩ := complements_map_blockSL hq hφ₂ hφ₁ P' P hJ'2 hJ2 hX.symm
  rw [hQ] at hS'N
  have hγQ : ((P.radicalP K).map φ₁).map (MulAut.conj γ).toMonoidHom =
      (P.radicalP K).map φ₁ := by
    rw [hc₁, P.map_radicalP_eq_of_map_eq hq hJ2 β₁ hβ₁Λ]
  have hγM : ((P.radicalP K).map φ₁ ⊔ (blockSL (K := K) P.free).map φ₁).map
      (MulAut.conj γ).toMonoidHom = (P.radicalP K).map φ₁ ⊔ (blockSL (K := K) P.free).map φ₁ := by
    rw [← Subgroup.map_sup, hc₁, P.map_radicalP_sup_blockSL_eq_of_map_eq hq hJ2 β₁ hβ₁Λ]
  have hγM' : ((P.radicalP K).map φ₁ ⊔ (blockSL (K := K) P'.free).map φ₂).map
      (MulAut.conj γ).toMonoidHom = (P.radicalP K).map φ₁ ⊔ (blockSL (K := K) P'.free).map φ₂ := by
    rw [← hSS']
    exact hγM
  obtain ⟨γ₁, hγ₁⟩ := exists_mulAut_complement hSN hQS γ hγQ hγM
  obtain ⟨γ₂, hγ₂⟩ := exists_mulAut_complement hS'N hQS' γ hγQ hγM'
  have hint := complement_intertwine hSN hQS hQS' hSS' hγQ γ₁ γ₂ hγ₁ hγ₂
  have hlt : P.free.card < n := by have := P.card_free; omega
  have hlt' : P'.free.card < n := by have := P'.card_free; omega
  obtain ⟨κ₁⟩ := blockSL_mulEquiv (K := K) hlt
  obtain ⟨κ₂⟩ := blockSL_mulEquiv (K := K) hlt'
  set κ₂' := κ₂.trans (reindexSpecialLinear (K := K) (finCongr hcard.symm)) with hκ₂'
  set e₁ := (blockSL (K := K) P.free).equivMapOfInjective φ₁ hφ₁ with he₁
  set e₂ := (blockSL (K := K) P'.free).equivMapOfInjective φ₂ hφ₂ with he₂
  set βbar₁ : MulAut (blockSL (K := K) P.free) := e₁.trans (γ₁.trans e₁.symm) with hβbar₁
  set βbar₂ : MulAut (blockSL (K := K) P'.free) := e₂.trans (γ₂.trans e₂.symm) with hβbar₂
  have hcond₁ : ∀ s : blockSL (K := K) P.free,
      ((βbar₁ s : blockSL (K := K) P.free) : projectiveSL n K)⁻¹ * β₁ s ∈ P.radicalP K := by
    intro s
    have he : φ₁ ((βbar₁ s : blockSL (K := K) P.free) : projectiveSL n K) =
        ((γ₁ (e₁ s) : (blockSL (K := K) P.free).map φ₁) : Γ) := by
      have : e₁ (βbar₁ s) = γ₁ (e₁ s) := by
        rw [hβbar₁, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rw [← this]
      rfl
    have hmem : φ₁ (((βbar₁ s : blockSL (K := K) P.free) : projectiveSL n K)⁻¹ * β₁ s) ∈
        (P.radicalP K).map φ₁ := by
      rw [map_mul, map_inv, he, h₁]
      exact hγ₁ (e₁ s)
    obtain ⟨q, hq', hqe⟩ := hmem
    rw [← hφ₁ hqe]
    exact hq'
  have hcond₂ : ∀ s : blockSL (K := K) P'.free,
      ((βbar₂ s : blockSL (K := K) P'.free) : projectiveSL n K)⁻¹ * β₂ s ∈ P'.radicalP K := by
    intro s
    have he : φ₂ ((βbar₂ s : blockSL (K := K) P'.free) : projectiveSL n K) =
        ((γ₂ (e₂ s) : (blockSL (K := K) P'.free).map φ₂) : Γ) := by
      have : e₂ (βbar₂ s) = γ₂ (e₂ s) := by
        rw [hβbar₂, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rw [← this]
      rfl
    have hmem : φ₂ (((βbar₂ s : blockSL (K := K) P'.free) : projectiveSL n K)⁻¹ * β₂ s) ∈
        (P'.radicalP K).map φ₂ := by
      rw [map_mul, map_inv, he, h₂, hQ]
      exact hγ₂ (e₂ s)
    obtain ⟨q, hq', hqe⟩ := hmem
    rw [← hφ₂ hqe]
    exact hq'
  have hF₁ := hRC β₁ hβ₁Λ βbar₁ hcond₁ P.free.card hJ κ₁
  have hF₂ := hRC' β₂ hβ₂Λ βbar₂ hcond₂ P.free.card hJ κ₂'
  have hT := slFieldPart_eq_of_intertwine hJ (e₁.symm.trans κ₁) (e₂.symm.trans κ₂')
    (EPilot.mulEquivOfComplements hSN hQS hQS' hSS') γ₁ γ₂ hint
  have hA : MulAut.congr κ₁ βbar₁ = MulAut.congr (e₁.symm.trans κ₁) γ₁ := by
    ext A
    rfl
  have hB : MulAut.congr κ₂' βbar₂ = MulAut.congr (e₂.symm.trans κ₂') γ₂ := by
    ext A
    rfl
  rw [← hF₁, ← hF₂, hA, hB, hT]

end Rigid

end CFSG.SeitzReduction.LinearPilot
