module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRNonaltCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRNonaltRC

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart)
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Complements

variable {G Γ : Type*} [Group G] [Group Γ]

theorem exists_intertwined_complements {φ₁ φ₂ : G →* Γ} (hφ₁ : Function.Injective φ₁)
    (hφ₂ : Function.Injective φ₂) {Λ₁ Λ₂ Q₁ Q₂ L₁ L₂ : Subgroup G} (hΛ₁ : Λ₁ = Q₁ ⊔ L₁)
    (hΛ₂ : Λ₂ = Q₂ ⊔ L₂) (hL₁N : L₁ ≤ normalizer (Q₁ : Set G))
    (hL₂N : L₂ ≤ normalizer (Q₂ : Set G)) (hd₁ : Disjoint Q₁ L₁) (hd₂ : Disjoint Q₂ L₂)
    (hX : Λ₁.map φ₁ = Λ₂.map φ₂) (hQ : Q₂.map φ₂ = Q₁.map φ₁) {γ : Γ} {β₁ β₂ : MulAut G}
    (h₁ : ∀ x, φ₁ (β₁ x) = γ * φ₁ x * γ⁻¹) (h₂ : ∀ x, φ₂ (β₂ x) = γ * φ₂ x * γ⁻¹)
    (hβ₁Λ : Λ₁.map β₁.toMonoidHom = Λ₁) (hβ₁Q : Q₁.map β₁.toMonoidHom = Q₁) :
    ∃ (βbar₁ : MulAut L₁) (βbar₂ : MulAut L₂) (ψ : L₁ ≃* L₂),
      (∀ s : L₁, ((βbar₁ s : L₁) : G)⁻¹ * β₁ s ∈ Q₁) ∧
      (∀ s : L₂, ((βbar₂ s : L₂) : G)⁻¹ * β₂ s ∈ Q₂) ∧
      ∀ s : L₁, βbar₂ (ψ s) = ψ (βbar₁ s) := by
  have hc₁ : ∀ X : Subgroup G,
      (X.map φ₁).map (MulAut.conj γ).toMonoidHom = (X.map β₁.toMonoidHom).map φ₁ := by
    intro X
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact (h₁ x).symm
  have hSN : L₁.map φ₁ ≤ normalizer ((Q₁.map φ₁ : Subgroup Γ) : Set Γ) :=
    (map_mono hL₁N).trans (le_normalizer_map φ₁)
  have hS'N : L₂.map φ₂ ≤ normalizer ((Q₁.map φ₁ : Subgroup Γ) : Set Γ) := by
    rw [← hQ]
    exact (map_mono hL₂N).trans (le_normalizer_map φ₂)
  have hQS : Disjoint (Q₁.map φ₁) (L₁.map φ₁) := disjoint_map_of_injective hφ₁ hd₁
  have hQS' : Disjoint (Q₁.map φ₁) (L₂.map φ₂) := by
    rw [← hQ]
    exact disjoint_map_of_injective hφ₂ hd₂
  have hSS' : Q₁.map φ₁ ⊔ L₁.map φ₁ = Q₁.map φ₁ ⊔ L₂.map φ₂ := by
    rw [← Subgroup.map_sup, ← hΛ₁, hX, hΛ₂, Subgroup.map_sup, hQ]
  have hγQ : (Q₁.map φ₁).map (MulAut.conj γ).toMonoidHom = Q₁.map φ₁ := by
    rw [hc₁, hβ₁Q]
  have hγM : (Q₁.map φ₁ ⊔ L₁.map φ₁).map (MulAut.conj γ).toMonoidHom =
      Q₁.map φ₁ ⊔ L₁.map φ₁ := by
    rw [← Subgroup.map_sup, ← hΛ₁, hc₁, hβ₁Λ]
  have hγM' : (Q₁.map φ₁ ⊔ L₂.map φ₂).map (MulAut.conj γ).toMonoidHom =
      Q₁.map φ₁ ⊔ L₂.map φ₂ := by
    rw [← hSS']
    exact hγM
  obtain ⟨γ₁, hγ₁⟩ := exists_mulAut_complement hSN hQS γ hγQ hγM
  obtain ⟨γ₂, hγ₂⟩ := exists_mulAut_complement hS'N hQS' γ hγQ hγM'
  have hint := complement_intertwine hSN hQS hQS' hSS' hγQ γ₁ γ₂ hγ₁ hγ₂
  set ι := EPilot.mulEquivOfComplements hSN hQS hQS' hSS' with hι
  set e₁ := L₁.equivMapOfInjective φ₁ hφ₁ with he₁
  set e₂ := L₂.equivMapOfInjective φ₂ hφ₂ with he₂
  refine ⟨e₁.trans (γ₁.trans e₁.symm), e₂.trans (γ₂.trans e₂.symm),
    e₁.trans (ι.trans e₂.symm), fun s => ?_, fun s => ?_, fun s => ?_⟩
  · have he : φ₁ (((e₁.trans (γ₁.trans e₁.symm)) s : L₁) : G) = ((γ₁ (e₁ s) : L₁.map φ₁) : Γ) := by
      have : e₁ ((e₁.trans (γ₁.trans e₁.symm)) s) = γ₁ (e₁ s) := by
        rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rw [← this]
      rfl
    have hmem : φ₁ ((((e₁.trans (γ₁.trans e₁.symm)) s : L₁) : G)⁻¹ * β₁ s) ∈ Q₁.map φ₁ := by
      rw [map_mul, map_inv, he, h₁]
      exact hγ₁ (e₁ s)
    obtain ⟨q, hq', hqe⟩ := hmem
    rw [← hφ₁ hqe]
    exact hq'
  · have he : φ₂ (((e₂.trans (γ₂.trans e₂.symm)) s : L₂) : G) = ((γ₂ (e₂ s) : L₂.map φ₂) : Γ) := by
      have : e₂ ((e₂.trans (γ₂.trans e₂.symm)) s) = γ₂ (e₂ s) := by
        rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rw [← this]
      rfl
    have hmem : φ₂ ((((e₂.trans (γ₂.trans e₂.symm)) s : L₂) : G)⁻¹ * β₂ s) ∈ Q₂.map φ₂ := by
      rw [map_mul, map_inv, he, h₂, hQ]
      exact hγ₂ (e₂ s)
    obtain ⟨q, hq', hqe⟩ := hmem
    rw [← hφ₂ hqe]
    exact hq'
  · simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [hint]

end Complements

section Self

variable {n : ℕ} {K : Type} [Field K] [Finite K]

open Nonalt in
theorem fieldRigidIn_graph_nonalt_self_of_even {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) {r : ℕ} (hr : n = 2 * r + 2) (hr1 : 1 ≤ r) :
    FieldRigidIn hn (perfectCore (autFixSubgroup (dualAut n K)))
      (perfectCore (autFixSubgroup (dualAut n K))) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [hK, pow_zero] at hq
      omega
    · exact h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hev : Even n := ⟨r + 1, by omega⟩
  set i : Fin n := ⟨0, by omega⟩ with hi
  set a : Fin n := ⟨1, by omega⟩ with ha
  set b : Fin n := ⟨2, by omega⟩ with hb
  have hab : a ≠ b := by simp [ha, hb, Fin.ext_iff]
  have hia : i ≠ a := by simp [hi, ha, Fin.ext_iff]
  have hib : i ≠ b := by simp [hi, hb, Fin.ext_iff]
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβX h₁ h₂
  set Θ := perfectCore (autFixSubgroup (dualAut n K)) with hΘ
  obtain ⟨-, -, -, -, hΘeq, hLN, hdisj⟩ := coreRadical_spec hK hq hr hr1 i
  have hβ₁Θ : Θ.map β₁.toMonoidHom = Θ := by
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective β₁.injective).ge
    rintro _ ⟨x, hx, rfl⟩
    exact hβX x hx
  have hβ₁Q := map_coreRadical_eq_of_map_eq hK hq hr hr1 i β₁ hβ₁Θ
  have hQ := map_coreRadical_eq hK hq hr hr1 i hφ₁ hφ₂ hX
  obtain ⟨βbar₁, βbar₂, ψ, hcond₁, hcond₂, hint⟩ := exists_intertwined_complements hφ₁ hφ₂
    hΘeq hΘeq hLN hLN hdisj hdisj hX hQ h₁ h₂ hβ₁Θ hβ₁Q
  obtain ⟨-, -, hOut⟩ := levi_spec hK hq hr hr1 i
  obtain ⟨ℓ, hℓ⟩ := hOut (ψ : MulAut (levi (K := K) i)) βbar₁
  have hβbar₂ : ∀ s, βbar₂ s = ℓ * βbar₁ s * ℓ⁻¹ := by
    intro s
    have e1 : βbar₂ s = ψ (βbar₁ (ψ.symm s)) := by rw [← hint, MulEquiv.apply_symm_apply]
    have e2 : (MulAut.conj ℓ) (βbar₁ s) = ψ (βbar₁ (ψ.symm s)) := by
      rw [hℓ]
      simp only [MulAut.mul_apply, MulAut.inv_def, MulEquiv.symm_apply_apply]
    rw [e1, ← e2, MulAut.conj_apply]
  have hβ₁inv : ∀ x ∈ coreRadical K i, β₁⁻¹ x ∈ coreRadical K i := fun x hx => by
    rw [← hβ₁Q] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  set u : Fin n → K := Pi.single a 1 + Pi.single b 1 with hu
  have hui : u i = 0 := by
    rw [hu, Pi.add_apply, Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib, add_zero]
  have hαt : ∀ c : K, (transElt u (onesVec_dotProduct_pairVec a b) c)⁻¹ *
      ((MulAut.conj (ℓ : projectiveSL n K) * β₁)⁻¹ * β₂)
        (transElt u (onesVec_dotProduct_pairVec a b) c) ∈ radical (K := K) i := by
    intro c
    set t := transElt u (onesVec_dotProduct_pairVec a b) c with ht
    have htL : t ∈ levi (K := K) i := transElt_mem_levi _ hui c
    set s : levi (K := K) i := ⟨t, htL⟩
    set q₁ := ((βbar₁ s : levi (K := K) i) : projectiveSL n K)⁻¹ * β₁ t with hq₁
    set q₂ := ((βbar₂ s : levi (K := K) i) : projectiveSL n K)⁻¹ * β₂ t with hq₂
    have hq₁Q : q₁ ∈ coreRadical K i := hcond₁ s
    have hq₂Q : q₂ ∈ coreRadical K i := hcond₂ s
    set w := q₁⁻¹ * ((ℓ : projectiveSL n K)⁻¹ * q₂ * ℓ) with hw
    have hwQ : w ∈ coreRadical K i := by
      refine mul_mem (inv_mem hq₁Q) ?_
      have hℓN := hLN (ℓ⁻¹).2
      rw [mem_normalizer_iff] at hℓN
      have := (hℓN q₂).1 hq₂Q
      simpa using this
    have hβ₂t : β₂ t = (ℓ : projectiveSL n K) * β₁ t * (ℓ : projectiveSL n K)⁻¹ *
        (ℓ * w * (ℓ : projectiveSL n K)⁻¹) := by
      have e1 : β₂ t = ((βbar₂ s : levi (K := K) i) : projectiveSL n K) * q₂ := by
        rw [hq₂, mul_inv_cancel_left]
      have e2 : ((βbar₂ s : levi (K := K) i) : projectiveSL n K) =
          (ℓ : projectiveSL n K) * ((βbar₁ s : levi (K := K) i) : projectiveSL n K) *
            (ℓ : projectiveSL n K)⁻¹ := by
        rw [hβbar₂ s, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      have e3 : ((βbar₁ s : levi (K := K) i) : projectiveSL n K) = β₁ t * q₁⁻¹ := by
        rw [hq₁, _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
      rw [e1, e2, e3, hw]
      group
    have hαt' : ((MulAut.conj (ℓ : projectiveSL n K) * β₁)⁻¹ * β₂) t = t * β₁⁻¹ w := by
      rw [MulAut.mul_apply, _root_.mul_inv_rev, MulAut.mul_apply, hβ₂t, MulAut.conj_inv_apply]
      have e : (ℓ : projectiveSL n K)⁻¹ * ((ℓ : projectiveSL n K) * β₁ t *
          (ℓ : projectiveSL n K)⁻¹ * (ℓ * w * (ℓ : projectiveSL n K)⁻¹)) * ℓ = β₁ t * w := by
        group
      rw [e, map_mul, MulAut.inv_apply_self]
    rw [hαt', inv_mul_cancel_left]
    exact (hβ₁inv w hwQ).2
  have hfc := linearFieldPart_eq_one_of_mem_radical hev hn hab hia hib _ hαt
  rw [map_mul, map_inv, map_mul, linearFieldPart_mulAut_conj, one_mul, inv_mul_eq_one] at hfc
  exact hfc

end Self

end CFSG.SeitzReduction.LinearPilot
