module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36J
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped Pointwise

variable {X : Type} [Group X]

theorem DgF.eq_one_of_mem_coreActionKernel {N : Subgroup X} {r : ℕ}
    {ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin r)}
    {ρ : ↥(normalizer (N : Set X)) →* Perm (Fin r)} (hρ : IsPermActionZ ψ ρ) (hr : 4 ≤ r)
    {g : X} (hg : g ∈ UnbalancedLayer.coreActionKernel N) : ρ ⟨g, hg.1⟩ = 1 := by
  apply GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup r hr
  rw [map_one]
  refine MulEquiv.ext fun b => Subtype.ext ?_
  obtain ⟨q, rfl⟩ := ψ.surjective b
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  change ρ _ * _ * (ρ _)⁻¹ = (ψ (x : ↥N ⧸ Open.fusionZStar ↥N) : Perm (Fin r))
  rw [← hρ]
  have hgi : g⁻¹ ∈ UnbalancedLayer.coreActionKernel N := inv_mem hg
  have h1 := hgi.2 x x.2
  rw [inv_inv] at h1
  obtain ⟨o, ho, hoeq⟩ := h1
  have h2 : ((N.normalizerMonoidHom ⟨g, hg.1⟩ x : ↥N) : ↥N ⧸ Open.fusionZStar ↥N) =
      (x : ↥N ⧸ Open.fusionZStar ↥N) := by
    apply QuotientGroup.eq.mpr
    have h4 : (N.normalizerMonoidHom ⟨g, hg.1⟩ x)⁻¹ * x = o⁻¹ := Subtype.ext (by
      change (g * (x : X) * g⁻¹)⁻¹ * x = ((o : X))⁻¹
      rw [show (o : X) = (x : X)⁻¹ * g * x * g⁻¹ from hoeq]
      group)
    rw [h4]
    exact Sol78.pPrimeCore_le_fusionZStar _ (inv_mem ho)
  rw [h2]

theorem DgF.exists_lift_sqrt [Finite X] {c a : X} {M' : Subgroup X}
    {ψ : ↥M' ⧸ Open.fusionZStar ↥M' ≃* alternatingGroup (Fin 7)}
    {ρ' : ↥(normalizer (M' : Set X)) →* Perm (Fin 7)} (hρ' : IsPermActionZ ψ ρ')
    (hcak : M'.map (MulAut.conj c).toMonoidHom ≤ UnbalancedLayer.coreActionKernel M')
    (haMM : a ∈ M' ⊔ M'.map (MulAut.conj c).toMonoidHom) (haN : a ∈ normalizer (M' : Set X))
    (ha2 : a * a = 1) {w : Perm (Fin 7)} (hwA : Perm.sign w = 1)
    (hw2 : w * w = ρ' ⟨a, haN⟩) :
    ∃ (g : X) (hgM : g ∈ M'), g * a = a * g ∧ ρ' ⟨g, le_normalizer hgM⟩ = w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hρcak : ∀ (g : X) (hg : g ∈ UnbalancedLayer.coreActionKernel M'), ρ' ⟨g, hg.1⟩ = 1 :=
    fun g hg => DgF.eq_one_of_mem_coreActionKernel hρ' (by norm_num) hg
  obtain ⟨q, hq⟩ := ψ.surjective ⟨w, Perm.mem_alternatingGroup.mpr hwA⟩
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hρg₀ : ρ' ⟨g₀, le_normalizer g₀.2⟩ = w := by
    rw [hρ'.apply_of_mem (by norm_num) g₀, hq]
  have hle : M'.map (MulAut.conj c).toMonoidHom ≤ normalizer (M' : Set X) :=
    fun y hy => (hcak hy).1
  have haMM' : a ∈ ((M' : Set X) * (M'.map (MulAut.conj c).toMonoidHom : Set X)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left M' _ hle]
    exact haMM
  obtain ⟨a₁, ha₁, a₂, ha₂, ha12⟩ := haMM'
  have hρa₁ : ρ' ⟨a₁, le_normalizer ha₁⟩ =
      (ψ ((⟨a₁, ha₁⟩ : ↥M') : ↥M' ⧸ Open.fusionZStar ↥M') : Perm (Fin 7)) :=
    hρ'.apply_of_mem (by norm_num) ⟨a₁, ha₁⟩
  have hρa : ρ' ⟨a, haN⟩ =
      (ψ ((⟨a₁, ha₁⟩ : ↥M') : ↥M' ⧸ Open.fusionZStar ↥M') : Perm (Fin 7)) := by
    have h1 : (⟨a, haN⟩ : ↥(normalizer (M' : Set X))) =
        ⟨a₁, le_normalizer ha₁⟩ * ⟨a₂, (hcak ha₂).1⟩ := Subtype.ext ha12.symm
    rw [h1, map_mul, hρcak a₂ (hcak ha₂), mul_one, hρa₁]
  have hsq : ((g₀ * g₀ : ↥M') : ↥M' ⧸ Open.fusionZStar ↥M') =
      ((⟨a₁, ha₁⟩ : ↥M') : ↥M' ⧸ Open.fusionZStar ↥M') := by
    apply ψ.injective
    apply Subtype.ext
    rw [QuotientGroup.mk_mul, map_mul, hq, ← hρa]
    exact hw2
  have hz := QuotientGroup.eq.mp hsq
  have hO : Open.fusionOddCore ↥M' = pPrimeCore 2 ↥M' := GSLit.oddCore_eq_pPrimeCore_two _
  have hzc : ∀ z ∈ Open.fusionZStar ↥M', ∀ y : ↥M', (z * y)⁻¹ * (y * z) ∈ pPrimeCore 2 ↥M' := by
    intro z hz' y
    have h1 : QuotientGroup.mk' (Open.fusionOddCore ↥M') z ∈
        center (↥M' ⧸ Open.fusionOddCore ↥M') := hz'
    have h2 := (mem_center_iff.mp h1) (QuotientGroup.mk' (Open.fusionOddCore ↥M') y)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h2
    have h3 := QuotientGroup.eq.mp h2.symm
    rw [hO] at h3
    exact h3
  set z : ↥M' := (g₀ * g₀)⁻¹ * ⟨a₁, ha₁⟩ with hzdef
  have ha₁z : a₁ = (g₀ : X) * g₀ * z := by
    rw [hzdef]
    simp only [coe_mul, coe_inv]
    group
  have hzi : z⁻¹ ∈ Open.fusionZStar ↥M' := inv_mem hz
  obtain ⟨o₂, ho₂, ho₂eq⟩ : (g₀ : X)⁻¹ * z * g₀ * (z : X)⁻¹ ∈
      (pPrimeCore 2 ↥M').map M'.subtype := by
    refine ⟨_, hzc z⁻¹ hzi g₀, ?_⟩
    simp only [map_mul, map_inv, Subgroup.coe_subtype]
    group
  have ha₂i : a₂⁻¹ ∈ UnbalancedLayer.coreActionKernel M' := inv_mem (hcak ha₂)
  have ho₁ := ha₂i.2 g₀ g₀.2
  rw [inv_inv] at ho₁
  have hON : ∀ m ∈ M', ∀ o ∈ (pPrimeCore 2 ↥M').map M'.subtype,
      m * o * m⁻¹ ∈ (pPrimeCore 2 ↥M').map M'.subtype := fun m hm o ho =>
    (mem_normalizer_iff.mp (le_normalizer_pPrimeCore (le_normalizer hm)) o).mp ho
  have hcoset : (g₀ : X)⁻¹ * (a * g₀ * a⁻¹) ∈ (pPrimeCore 2 ↥M').map M'.subtype := by
    have h1 : (g₀ : X)⁻¹ * (a * g₀ * a⁻¹) =
        ((g₀ : X) * g₀ * ((g₀ : X)⁻¹ * z * g₀ * (z : X)⁻¹) * ((g₀ : X) * g₀)⁻¹) *
          (a₁ * ((g₀ : X)⁻¹ * a₂ * g₀ * a₂⁻¹) * a₁⁻¹) := by
      rw [← ha12, ha₁z]
      group
    rw [h1]
    refine mul_mem (hON _ (mul_mem g₀.2 g₀.2) _ ?_) (hON _ ha₁ _ ho₁)
    rw [← ho₂eq]
    exact ⟨o₂, ho₂, rfl⟩
  obtain ⟨k, hkO, hkc⟩ := exists_commute_of_mem_coset (odd_coreNOf M') ha2
    (fun o ho => (mem_normalizer_iff.mp (le_normalizer_pPrimeCore haN) o).mp ho) hcoset
  obtain ⟨k', hk', hk'eq⟩ := hkO
  have hkM : k ∈ M' := by
    rw [← hk'eq]
    exact k'.2
  refine ⟨(g₀ : X) * k, mul_mem g₀.2 hkM, hkc.symm, ?_⟩
  have hρk : ρ' ⟨k, le_normalizer hkM⟩ = 1 := by
    have h1 : ρ' ⟨k, le_normalizer hkM⟩ =
        (ψ ((⟨k, hkM⟩ : ↥M') : ↥M' ⧸ Open.fusionZStar ↥M') : Perm (Fin 7)) :=
      hρ'.apply_of_mem (by norm_num) ⟨k, hkM⟩
    have h2 : ((⟨k, hkM⟩ : ↥M') : ↥M' ⧸ Open.fusionZStar ↥M') = 1 := by
      rw [QuotientGroup.eq_one_iff]
      apply Sol78.pPrimeCore_le_fusionZStar
      have h3 : (⟨k, hkM⟩ : ↥M') = k' := Subtype.ext hk'eq.symm
      rw [h3]
      exact hk'
    rw [h1, h2, map_one]
    rfl
  have h1 : (⟨(g₀ : X) * k, le_normalizer (mul_mem g₀.2 hkM)⟩ :
      ↥(normalizer (M' : Set X))) = ⟨g₀, le_normalizer g₀.2⟩ * ⟨k, le_normalizer hkM⟩ := rfl
  rw [h1, map_mul, hρg₀, hρk, mul_one]
end CFSG.ComponentClassification.SolMax
