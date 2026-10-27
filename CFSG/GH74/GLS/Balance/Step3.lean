module

public import CFSG.GH74.GLS.Balance.Step3Basic
public import CFSG.GH74.GLS.Balance.Step4
public import CFSG.GH74.GLS.Balance.CompLayer
public import CFSG.GH74.GLS.Balance.CompFitting
public import CFSG.GH74.GLS.Balance.CompDiag
public import CFSG.GH74.GLS.Balance.CompInner
public import CFSG.GH74.GLS.Balance.OResidual
public import CFSG.GH74.GLS.Balance.Step2

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

section Step3

variable {x : X} {V : Subgroup X}

theorem step3_V_normalizes (hB : BenderBalance) (hx : orderOf x = 2) (A : SolvAPI x V)
    (hRE : ¬ oPrimeResidualOf 2 V ≤ layer X) {K : Subgroup X} (hK : IsComponent K) :
    V ≤ normalizer (K : Set X) := by
  have hEn : (layer X).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := X)
    infer_instance
  have hnormE : ∀ g : X, g ∈ normalizer (layer X : Set X) := normalizer_of_normal hEn
  obtain ⟨Q, hQE, hQ2, hQs⟩ := exists_sylow_pack (layer X)
  have hdec := step2_decomp hB hx A (N := layer X) (fun v _ => hnormE v) (hnormE x) (isPStar_layer X) hRE
    hQE hQ2 hQs
  apply A.gen
  intro v hv hv2
  obtain ⟨n, hn, c, hc, rfl⟩ := hdec v hv hv2
  exact mul_mem (CFSG.LocalCores.layer_le_normalizer hK hn)
    (mem_normalizer_of_centralizes_sylow hK Q hQE hQ2 hQs hc)

theorem step3_R_normalizes (hB : BenderBalance) (hx : orderOf x = 2) (A : SolvAPI x V)
    {K : Subgroup X} (hK : IsComponent K) : oPrimeResidualOf 2 V ≤ normalizer (K : Set X) := by
  by_cases hRE : oPrimeResidualOf 2 V ≤ layer X
  · exact hRE.trans (CFSG.LocalCores.layer_le_normalizer hK)
  · exact (oPrimeResidualOf_le_self V).trans (step3_V_normalizes hB hx A hRE hK)

theorem step3_R_centralizes_swapped (hB : BenderBalance) (hx : orderOf x = 2) (A : SolvAPI x V)
    {K : Subgroup X} (hK : IsComponent K) (hKx : x ∉ normalizer (K : Set X))
    {r : X} (hr : r ∈ oPrimeResidualOf 2 V) : ∀ y ∈ K, r * y = y * r := by
  have hVC : V ≤ centralizer ({x} : Set X) := A.hVC
  have hxC : ∀ g ∈ centralizer ({x} : Set X), x * g = g * x := fun g hg =>
    (mem_centralizer_singleton_iff.mp hg).symm
  obtain ⟨J, hJC, hJcomp, hJK⟩ := isComponent_diagonal hx hK hKx
  have hrC : r ∈ centralizer ({x} : Set X) := hVC (oPrimeResidualOf_le_self V hr)
  refine commute_of_swap hx (hxC r hrC) hK hKx (step3_R_normalizes hB hx A hK hr)
    (pPrimeCoreOf 2 (centralizer ({x} : Set X))) (odd_card_pPrimeCoreOf _)
    (le_normalizer_pPrimeCoreOf _) ?_
  intro k hk
  have hjJ : k * (x * k * x⁻¹) ∈ J := hJK k hk
  have hjC : k * (x * k * x⁻¹) ∈ centralizer ({x} : Set X) := hJC hjJ
  obtain ⟨m, hm, hmr⟩ := A.R_le_pPrimePCore hr
  have h1 := commutator_mem_pPrimeCore_of_component hJcomp hm ⟨k * (x * k * x⁻¹), hjC⟩
    (show _ ∈ J.subgroupOf (centralizer ({x} : Set X)) from hjJ)
  refine ⟨_, h1, ?_⟩
  have hmr' : (m : X) = r := hmr
  show (((⁅(⟨k * (x * k * x⁻¹), hjC⟩ : ↥(centralizer ({x} : Set X))), m⁆ :
    ↥(centralizer ({x} : Set X)))) : X) = _
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, hmr']

theorem step3_R_inner (hB : BenderBalance) (hO : pPrimeCore 2 X = ⊥) (hx : orderOf x = 2)
    (A : SolvAPI x V) {K : Subgroup X} (hK : IsComponent K) (hKx : x ∈ normalizer (K : Set X)) :
    oPrimeResidualOf 2 V ≤ innerNormalizer K := by
  by_cases hRK : oPrimeResidualOf 2 V ≤ K
  · exact hRK.trans (le_innerNormalizer_self K)
  by_cases hRE : oPrimeResidualOf 2 V ≤ layer X
  · exact hRE.trans (layer_le_innerNormalizer hK)
  have hVK : V ≤ normalizer (K : Set X) := step3_V_normalizes hB hx A hRE hK
  obtain ⟨Q, hQK, hQ2, hQs⟩ := exists_sylow_pack K
  have hdec := step2_decomp hB hx A (N := K) hVK hKx (isPStar_component hK) hRK hQK hQ2 hQs
  apply oPrimeResidualOf_le_of_two_elements
  intro r hr hr2
  obtain ⟨k, hk, hkk⟩ := exists_inner_of_two_element hO hK Q hQK hQ2 hQs V hVK A.gen hdec hr hr2
  exact ⟨hVK hr, k, hk, hkk⟩


theorem step3_R_decomp (hB : BenderBalance) (hO : pPrimeCore 2 X = ⊥) (hx : orderOf x = 2)
    (A : SolvAPI x V) (hVF : V ≤ centralizer (pCore 2 X : Set X)) {r : X}
    (hr : r ∈ oPrimeResidualOf 2 V) :
    ∃ ℓ ∈ invLayer x, ∃ g ∈ pCore 2 X, r = ℓ * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ℓ, hℓ, hconj⟩ := exists_layer_element r (invComps x) (fun K hK => hK.1)
    (fun K hK => (step3_R_inner hB hO hx A hK.1 hK.2 hr).2)
    (fun K hK hKS y hy =>
      step3_R_centralizes_swapped hB hx A hK (fun hx' => hKS ⟨hK, hx'⟩) hr y hy)
  refine ⟨ℓ, hℓ, ℓ⁻¹ * r, ?_, by group⟩
  have hFn : (pCore 2 X).Normal := CFSG.pCore_normal
  have hF2 : IsPGroup 2 (pCore 2 X) := pCore_isPGroup
  have hnil := CFSG.LocalCores.fitting_nilpotent (G := X)
  have hFfit : pCore 2 X ≤ fittingSubgroup X := hnil.2.2.1 _ hFn hF2.isNilpotent
  have hfitF : fittingSubgroup X ≤ pCore 2 X :=
    le_sSup ⟨hnil.2.1, isPGroup_of_nilpotent_normal _ hnil.2.1 hnil.1 hO⟩
  have hL₁E : invLayer x ≤ layer X :=
    iSup₂_le fun K hK => CFSG.LocalCores.component_le_layer hK.1
  have hEF : ∀ ℓ' ∈ layer X, ∀ f ∈ pCore 2 X, ℓ' * f = f * ℓ' := by
    intro ℓ' hℓ' f hf
    have h0 : ⁅fittingSubgroup X, layer X⁆ = ⊥ := CFSG.LocalCores.fitting_layer_commute
    have h1 : ⁅f, ℓ'⁆ ∈ (⁅fittingSubgroup X, layer X⁆ : Subgroup X) :=
      Subgroup.commutator_mem_commutator (hFfit hf) hℓ'
    rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  set g : X := ℓ⁻¹ * r with hg
  have hgK : ∀ K : Subgroup X, IsComponent K → ∀ y ∈ K, g * y = y * g := by
    intro K hK y hy
    have h1 := hconj K hK y hy
    have e : g * y * g⁻¹ = y := by
      calc g * y * g⁻¹ = ℓ⁻¹ * (r * y * r⁻¹) * ℓ := by rw [hg]; group
        _ = ℓ⁻¹ * (ℓ * y * ℓ⁻¹) * ℓ := by rw [h1]
        _ = y := by group
    calc g * y = g * y * g⁻¹ * g := by group
      _ = y * g := by rw [e]
  have hgF : ∀ f ∈ pCore 2 X, g * f = f * g := by
    intro f hf
    have h1 : r * f = f * r := (mem_centralizer_iff.mp (hVF (oPrimeResidualOf_le_self V hr)) f hf).symm
    have h2 : ℓ * f = f * ℓ := hEF ℓ (hL₁E hℓ) f hf
    have h3 : ℓ⁻¹ * f = f * ℓ⁻¹ := by
      calc ℓ⁻¹ * f = ℓ⁻¹ * (f * ℓ) * ℓ⁻¹ := by group
        _ = ℓ⁻¹ * (ℓ * f) * ℓ⁻¹ := by rw [h2]
        _ = f * ℓ⁻¹ := by group
    calc g * f = (ℓ⁻¹ * f) * r := by
          calc g * f = ℓ⁻¹ * (r * f) := by rw [hg]; group
            _ = ℓ⁻¹ * (f * r) := by rw [h1]
            _ = (ℓ⁻¹ * f) * r := by group
      _ = (f * ℓ⁻¹) * r := by rw [h3]
      _ = f * g := by rw [hg]; group
  have hgle : generalizedFitting X ≤ centralizer ({g} : Set X) := by
    refine sup_le (fun z hz => ?_) (sSup_le fun K hK => fun y hy => ?_)
    · rw [mem_centralizer_singleton_iff]
      exact (hgF z (hfitF hz)).symm
    · rw [mem_centralizer_singleton_iff]
      exact (hgK K hK y hy).symm
  have hgC : g ∈ centralizer (generalizedFitting X : Set X) := by
    rw [mem_centralizer_iff]
    intro z hz
    exact (mem_centralizer_singleton_iff.mp (hgle hz))
  have hgG : g ∈ generalizedFitting X := CFSG.centralizer_generalizedFitting_le X hgC
  have hGn : (generalizedFitting X).Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  have hNn : (generalizedFitting X ⊓ centralizer (generalizedFitting X : Set X)).Normal :=
    inferInstance
  have hNab : ∀ a ∈ generalizedFitting X ⊓ centralizer (generalizedFitting X : Set X),
      ∀ b ∈ generalizedFitting X ⊓ centralizer (generalizedFitting X : Set X), a * b = b * a :=
    fun a ha b hb => (mem_centralizer_iff.mp ha.2 b hb.1).symm
  have hNnil : Group.IsNilpotent ↥(generalizedFitting X ⊓ centralizer (generalizedFitting X : Set X)) := by
    let _ : CommGroup ↥(generalizedFitting X ⊓ centralizer (generalizedFitting X : Set X)) :=
      { (inferInstance : Group _) with mul_comm := fun a b => Subtype.ext (hNab a a.2 b b.2) }
    exact CommGroup.isNilpotent
  exact hfitF (hnil.2.2.1 _ hNn hNnil ⟨hgG, hgC⟩)

theorem step3_P_le (hB : BenderBalance) (hO : pPrimeCore 2 X = ⊥) (hx : orderOf x = 2)
    (A : SolvAPI x V) (hVF : V ≤ centralizer (pCore 2 X : Set X)) : A.P ≤ invLayer x := by
  have hP := A.P_comm
  rw [← hP]
  refine Subgroup.commutator_le.mpr fun p hp a ha => ?_
  obtain ⟨ℓ, hℓ, g, hg, rfl⟩ := step3_R_decomp hB hO hx A hVF (A.P_le_R hp)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hwC : A.w ∈ centralizer ({x} : Set X) := A.hVC A.w_mem
  have hwk : A.w ^ k ∈ centralizer ({x} : Set X) := zpow_mem hwC k
  have hwg : A.w ^ k * g = g * A.w ^ k := by
    have := mem_centralizer_iff.mp (hVF (zpow_mem A.w_mem k)) g hg
    exact this.symm
  have e : ⁅ℓ * g, A.w ^ k⁆ = ℓ * (A.w ^ k * ℓ⁻¹ * (A.w ^ k)⁻¹) := by
    have hg' : g * (A.w ^ k)⁻¹ = (A.w ^ k)⁻¹ * g := by
      calc g * (A.w ^ k)⁻¹ = (A.w ^ k)⁻¹ * (A.w ^ k * g) * (A.w ^ k)⁻¹ := by group
        _ = (A.w ^ k)⁻¹ * (g * A.w ^ k) * (A.w ^ k)⁻¹ := by rw [hwg]
        _ = (A.w ^ k)⁻¹ * g := by group
    simp only [commutatorElement_def]
    calc ℓ * g * A.w ^ k * (ℓ * g)⁻¹ * (A.w ^ k)⁻¹
        = ℓ * (g * A.w ^ k) * g⁻¹ * ℓ⁻¹ * (A.w ^ k)⁻¹ := by group
      _ = ℓ * (A.w ^ k * g) * g⁻¹ * ℓ⁻¹ * (A.w ^ k)⁻¹ := by rw [hwg]
      _ = ℓ * (A.w ^ k * ℓ⁻¹ * (A.w ^ k)⁻¹) := by group
  rw [e]
  exact (invLayer x).mul_mem hℓ (invLayer_conj_mem hwk ℓ⁻¹ ((invLayer x).inv_mem hℓ))

end Step3

theorem core_balance (hB : BenderBalance) (hO : pPrimeCore 2 X = ⊥) {x : X} (hx : orderOf x = 2)
    {V : Subgroup X} (A : SolvAPI x V) :
    oPrimeResidualOf 2 V ≤ pCore 2 X ∨
      ∃ K : Subgroup X, IsComponent K ∧ x ∈ normalizer (K : Set X) ∧ oPrimeResidualOf 2 V ≤ K := by
  by_cases hF : oPrimeResidualOf 2 V ≤ pCore 2 X
  · exact Or.inl hF
  right
  have hVF := step3_centralizes_pCore hx A hF
  exact step4 hx hO A (fun K hK => step3_R_normalizes hB hx A hK) (step3_P_le hB hO hx A hVF)


end CFSG.GH74.GLS.Balance
