module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRSmallOdd

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart)
open CFSG.Quasithin (perfectCore)

variable {n k k' : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem fieldRigidIn_inner_of_card_free_eq_one (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (P : InvPlacement n k) (P' : InvPlacement n k') (hJ : P.free.card = 1)
    (hJ' : P'.free.card = 1) :
    FieldRigidIn (Nat.le_of_succ_le hn)
      (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
      (perfectCore (centralizer ({P'.elt K} : Set (projectiveSL n K)))) := by
  have hcard := P.card_free
  have hcard' := P'.card_free
  have hk : 2 ≤ k := by omega
  have hkk' : k = k' := by omega
  subst hkk'
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβX h₁ h₂
  have hJne : P.free.Nonempty := Finset.card_pos.1 (by omega)
  have hJne' : P'.free.Nonempty := Finset.card_pos.1 (by omega)
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
  have hQ := map_radicalP_eq_of_card_free_eq_one hq hφ₁ hφ₂ P P' hk hk hJ hJ' hX
  have hΛ₁ := P.perfectCore_centralizer_elt_of_card_free_eq_one hq hk hJ
  have hΛ₂ := P'.perfectCore_centralizer_elt_of_card_free_eq_one hq hk hJ'
  have hMN₁ : P.leviOneP K ≤ normalizer (P.radicalP K : Set (projectiveSL n K)) := by
    have h := P.levi_le_normalizer_radicalP (K := K)
    rw [blockSL_eq_bot_of_card_le_one (by omega), sup_bot_eq] at h
    exact h
  have hMN₂ : P'.leviOneP K ≤ normalizer (P'.radicalP K : Set (projectiveSL n K)) := by
    have h := P'.levi_le_normalizer_radicalP (K := K)
    rw [blockSL_eq_bot_of_card_le_one (by omega), sup_bot_eq] at h
    exact h
  have hSN : (P.leviOneP K).map φ₁ ≤
      normalizer (((P.radicalP K).map φ₁ : Subgroup Γ) : Set Γ) :=
    (map_mono hMN₁).trans (le_normalizer_map φ₁)
  have hS'N : (P'.leviOneP K).map φ₂ ≤
      normalizer (((P.radicalP K).map φ₁ : Subgroup Γ) : Set Γ) := by
    rw [← hQ]
    exact (map_mono hMN₂).trans (le_normalizer_map φ₂)
  have hQS : Disjoint ((P.radicalP K).map φ₁) ((P.leviOneP K).map φ₁) :=
    disjoint_map_of_injective hφ₁ (P.disjoint_radicalP.mono_right le_sup_left)
  have hQS' : Disjoint ((P.radicalP K).map φ₁) ((P'.leviOneP K).map φ₂) := by
    rw [← hQ]
    exact disjoint_map_of_injective hφ₂ (P'.disjoint_radicalP.mono_right le_sup_left)
  have hSS' : (P.radicalP K).map φ₁ ⊔ (P.leviOneP K).map φ₁ =
      (P.radicalP K).map φ₁ ⊔ (P'.leviOneP K).map φ₂ := by
    rw [← Subgroup.map_sup, ← hΛ₁, hX, hΛ₂, Subgroup.map_sup, hQ]
  have hγQ : ((P.radicalP K).map φ₁).map (MulAut.conj γ).toMonoidHom =
      (P.radicalP K).map φ₁ := by
    rw [hc₁, P.map_radicalP_eq_of_map_eq_of_card_free_eq_one hq hk hJ β₁ hβ₁Λ]
  have hγM : ((P.radicalP K).map φ₁ ⊔ (P.leviOneP K).map φ₁).map
      (MulAut.conj γ).toMonoidHom = (P.radicalP K).map φ₁ ⊔ (P.leviOneP K).map φ₁ := by
    rw [← Subgroup.map_sup, ← hΛ₁, hc₁, hβ₁Λ]
  have hγM' : ((P.radicalP K).map φ₁ ⊔ (P'.leviOneP K).map φ₂).map
      (MulAut.conj γ).toMonoidHom = (P.radicalP K).map φ₁ ⊔ (P'.leviOneP K).map φ₂ := by
    rw [← hSS']
    exact hγM
  obtain ⟨γ₁, hγ₁⟩ := exists_mulAut_complement hSN hQS γ hγQ hγM
  obtain ⟨γ₂, hγ₂⟩ := exists_mulAut_complement hS'N hQS' γ hγQ hγM'
  have hint := complement_intertwine hSN hQS hQS' hSS' hγQ γ₁ γ₂ hγ₁ hγ₂
  set κ₁ := (P.leviOnePEquiv K hJne).symm with hκ₁
  set κ₂ := (P'.leviOnePEquiv K hJne').symm with hκ₂
  set e₁ := (P.leviOneP K).equivMapOfInjective φ₁ hφ₁ with he₁
  set e₂ := (P'.leviOneP K).equivMapOfInjective φ₂ hφ₂ with he₂
  set βbar₁ : MulAut (P.leviOneP K) := e₁.trans (γ₁.trans e₁.symm) with hβbar₁
  set βbar₂ : MulAut (P'.leviOneP K) := e₂.trans (γ₂.trans e₂.symm) with hβbar₂
  have hcond₁ : ∀ s : P.leviOneP K,
      ((βbar₁ s : P.leviOneP K) : projectiveSL n K)⁻¹ * β₁ s ∈ P.radicalP K := by
    intro s
    have he : φ₁ ((βbar₁ s : P.leviOneP K) : projectiveSL n K) =
        ((γ₁ (e₁ s) : (P.leviOneP K).map φ₁) : Γ) := by
      have : e₁ (βbar₁ s) = γ₁ (e₁ s) := by
        rw [hβbar₁, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rw [← this]
      rfl
    have hmem : φ₁ (((βbar₁ s : P.leviOneP K) : projectiveSL n K)⁻¹ * β₁ s) ∈
        (P.radicalP K).map φ₁ := by
      rw [map_mul, map_inv, he, h₁]
      exact hγ₁ (e₁ s)
    obtain ⟨q, hq', hqe⟩ := hmem
    rw [← hφ₁ hqe]
    exact hq'
  have hcond₂ : ∀ s : P'.leviOneP K,
      ((βbar₂ s : P'.leviOneP K) : projectiveSL n K)⁻¹ * β₂ s ∈ P'.radicalP K := by
    intro s
    have he : φ₂ ((βbar₂ s : P'.leviOneP K) : projectiveSL n K) =
        ((γ₂ (e₂ s) : (P'.leviOneP K).map φ₂) : Γ) := by
      have : e₂ (βbar₂ s) = γ₂ (e₂ s) := by
        rw [hβbar₂, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rw [← this]
      rfl
    have hmem : φ₂ (((βbar₂ s : P'.leviOneP K) : projectiveSL n K)⁻¹ * β₂ s) ∈
        (P'.radicalP K).map φ₂ := by
      rw [map_mul, map_inv, he, h₂, hQ]
      exact hγ₂ (e₂ s)
    obtain ⟨q, hq', hqe⟩ := hmem
    rw [← hφ₂ hqe]
    exact hq'
  obtain ⟨F, hF, hFσ, hFδ⟩ := exists_mulAutHom_fieldPart (K := K) hk
  have hF₁ := P.mulAutHom_congr_eq_linearFieldPart_levi hq (Nat.le_of_succ_le hn) hk hJ F hF hFσ
    hFδ β₁ hβ₁Λ βbar₁ hcond₁ κ₁
  have hF₂ := P'.mulAutHom_congr_eq_linearFieldPart_levi hq (Nat.le_of_succ_le hn) hk hJ' F hF hFσ
    hFδ β₂ hβ₂Λ βbar₂ hcond₂ κ₂
  have hT := mulAutHom_congr_eq_of_intertwine F (fun a b => ringEquiv_mul_comm _ _)
    (e₁.symm.trans κ₁) (e₂.symm.trans κ₂) (EPilot.mulEquivOfComplements hSN hQS hQS' hSS')
    γ₁ γ₂ hint
  have hA : MulAut.congr κ₁ βbar₁ = MulAut.congr (e₁.symm.trans κ₁) γ₁ := by
    ext A
    rfl
  have hB : MulAut.congr κ₂ βbar₂ = MulAut.congr (e₂.symm.trans κ₂) γ₂ := by
    ext A
    rfl
  rw [← hF₁, ← hF₂, hA, hB, hT]

end CFSG.SeitzReduction.LinearPilot
