module

public import CFSG.GH74.E2.Isolation
public import CFSG.GH74.E2.DirectProd
public import CFSG.GH74.E2.DirectSylow
public import CFSG.GH74.E2.SD16Cert
public meta import Mathlib
public meta import CFSG.GH74.E2.SD16Cert
public meta import CFSG.CharacterTheory.Semidihedral.Model
public import Certificates.Certificate5010
public import Certificates.Certificate5018
public import CFSG.GH74.SectionalRank
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

namespace CFSG.GH74.E2

open Subgroup

section Aux

private theorem sd16_center :
    ∃ z : SD16M, z ≠ 1 ∧ z * z = 1 ∧ ∀ y : SD16M, y * z = z * y :=
  Certificates.certificate5010

private theorem quat_data {m : ℕ} [NeZero m] (hm : m = 2 ∨ m = 4) :
    QuaternionGroup.a (m : ZMod (2 * m)) ≠ 1 ∧
    (∀ x : QuaternionGroup m, x * x = 1 → x = 1 ∨ x = QuaternionGroup.a (m : ZMod (2 * m))) ∧
    (∀ ψ : MulAut (SD16M × QuaternionGroup m),
      ψ (1, QuaternionGroup.a (m : ZMod (2 * m))) ∈ Subgroup.center _ →
        ψ (1, QuaternionGroup.a (m : ZMod (2 * m))) =
          (1, QuaternionGroup.a (m : ZMod (2 * m)))) := by
  rcases hm with rfl | rfl
  · refine ⟨by decide, by decide, ?_⟩
    have h : gc 2 ^ 2 = (1, QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2))) :=
      Prod.ext (by simp [gc]) (by simp only [gc, Prod.pow_snd]; decide)
    rw [← h]
    exact fix_SD16_Q8
  · refine ⟨by decide, by decide, ?_⟩
    have h : gc 4 ^ 4 = (1, QuaternionGroup.a ((4 : ℕ) : ZMod (2 * 4))) :=
      Prod.ext (by simp [gc]) (by simp only [gc, Prod.pow_snd]; decide)
    rw [← h]
    exact fix_SD16_Q16

end Aux

theorem isolation_direct_product
    {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2) (K D : Subgroup G)
    (hKC : K ≤ Cen t) (hDC : D ≤ Cen t) (hcomm : ∀ k ∈ K, ∀ d ∈ D, k * d = d * k)
    (hdisj : K ⊓ D = ⊥) (hCKD : Cen t = K ⊔ D)
    (hone : ∀ u ∈ K, ∀ v ∈ K, orderOf u = 2 → orderOf v = 2 → ∃ g ∈ K, g * u * g⁻¹ = v)
    (SK : Subgroup G) (hSKK : SK ≤ K) (hSKp : IsPGroup 2 SK)
    (hSKmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ K → SK ≤ P → P = SK)
    (SD : Subgroup G) (hSDD : SD ≤ D) (hSDp : IsPGroup 2 SD)
    (hSDmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ D → SD ≤ P → P = SD) (htSD : t ∈ SD)
    (eK : ↥SK ≃* SD16M) (m : ℕ) [NeZero m] (hm : m = 2 ∨ m = 4)
    (eD : ↥SD ≃* QuaternionGroup m) : False := by
  have hcommS : ∀ a ∈ SK, ∀ b ∈ SD, a * b = b * a := fun a ha b hb =>
    hcomm a (hSKK ha) b (hSDD hb)
  have hdisjS : SK ⊓ SD = ⊥ := le_bot_iff.1 ((inf_le_inf hSKK hSDD).trans hdisj.le)
  have hS1C : SK ⊔ SD ≤ Cen t := sup_le (hSKK.trans hKC) (hSDD.trans hDC)
  have htS : t ∈ SK ⊔ SD := Subgroup.mem_sup_right htSD
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  obtain ⟨-, -, hS12, hmax⟩ := directProduct_sylow hKC hDC hcomm hdisj hCKD hSKK hSKp hSKmax hSDD
    hSDp hSDmax
  obtain ⟨hq1, hq2, hq3⟩ := quat_data (m := m) hm
  have heD : eD ⟨t, htSD⟩ = QuaternionGroup.a (m : ZMod (2 * m)) := eD_t_eq_a htSD ht hm eD
  have hSD2 : ∀ d ∈ SD, d * d = 1 → d = 1 ∨ d = t := by
    intro d hd hdd
    have h1 : eD ⟨d, hd⟩ * eD ⟨d, hd⟩ = 1 := by
      rw [← map_mul]
      have : (⟨d, hd⟩ : ↥SD) * ⟨d, hd⟩ = 1 := Subtype.ext hdd
      rw [this, map_one]
    rcases hq2 _ h1 with h | h
    · left
      have : (⟨d, hd⟩ : ↥SD) = 1 := by
        apply eD.injective
        rw [h, map_one]
      exact congrArg Subtype.val this
    · right
      have : (⟨d, hd⟩ : ↥SD) = ⟨t, htSD⟩ := by
        apply eD.injective
        rw [h, heD]
      exact congrArg Subtype.val this
  obtain ⟨z0, hz01, hz02, hz0c⟩ := sd16_center
  have hsK : ((eK.symm z0 : ↥SK) : G) ∈ SK := (eK.symm z0).2
  have hsK1 : ((eK.symm z0 : ↥SK) : G) ≠ 1 := by
    intro h
    apply hz01
    have : eK.symm z0 = 1 := Subtype.ext h
    rwa [MulEquiv.symm_apply_eq, map_one] at this
  have hsK2 : ((eK.symm z0 : ↥SK) : G) * ((eK.symm z0 : ↥SK) : G) = 1 := by
    have : eK.symm z0 * eK.symm z0 = 1 := by
      rw [← map_mul, hz02, map_one]
    exact congrArg Subtype.val this
  have hsKc : ∀ k ∈ SK, k * ((eK.symm z0 : ↥SK) : G) = ((eK.symm z0 : ↥SK) : G) * k := by
    intro k hk
    have : (⟨k, hk⟩ : ↥SK) * eK.symm z0 = eK.symm z0 * ⟨k, hk⟩ := by
      apply eK.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz0c _
    exact congrArg Subtype.val this
  have hcl : ∀ u ∈ SK ⊔ SD, orderOf u = 2 → ∃ c : G, c * t = t * c ∧ c⁻¹ * u * c ∈ SK ⊔ SD ∧
      ∀ s ∈ SK ⊔ SD, s * (c⁻¹ * u * c) = (c⁻¹ * u * c) * s := by
    intro u hu hu2
    obtain ⟨k, hk, d, hd, hkd⟩ := (mem_sup_iff_of_commute hcommS).1 hu
    subst hkd
    have hsq : (k * d) * (k * d) = 1 := by
      have := pow_orderOf_eq_one (k * d)
      rwa [hu2, pow_two] at this
    have hkd1 : k * k * (d * d) = 1 := by
      calc k * k * (d * d) = k * (k * d) * d := by simp only [mul_assoc]
        _ = k * (d * k) * d := by rw [hcommS k hk d hd]
        _ = (k * d) * (k * d) := by simp only [mul_assoc]
        _ = 1 := hsq
    have hkk : k * k = 1 := by
      have h1 : k * k ∈ K := K.mul_mem (hSKK hk) (hSKK hk)
      have h2 : k * k ∈ D := by
        have : k * k = (d * d)⁻¹ := eq_inv_of_mul_eq_one_left hkd1
        rw [this]
        exact D.inv_mem (D.mul_mem (hSDD hd) (hSDD hd))
      have h3 : k * k ∈ K ⊓ D := ⟨h1, h2⟩
      rw [hdisj, Subgroup.mem_bot] at h3
      exact h3
    have hdd : d * d = 1 := by
      rw [hkk, one_mul] at hkd1
      exact hkd1
    have hdt := hSD2 d hd hdd
    have hdcomm : ∀ d' ∈ SD, d' * d = d * d' := by
      intro d' hd'
      rcases hdt with h | h
      · rw [h, mul_one, one_mul]
      · rw [h]
        exact mem_Cen'.1 (hS1C (Subgroup.mem_sup_right hd'))
    by_cases hk1 : k = 1
    · subst hk1
      have hdt' : d = t := by
        rcases hdt with h | h
        · exfalso
          rw [h, one_mul, orderOf_one] at hu2
          exact absurd hu2 (by norm_num)
        · exact h
      refine ⟨1, by simp, ?_, ?_⟩
      · simpa using hu
      · intro s hs
        simp only [inv_one, one_mul, mul_one]
        rw [hdt']
        exact mem_Cen'.1 (hS1C hs)
    · have hkord : orderOf k = 2 := orderOf_eq_prime (by rw [pow_two]; exact hkk) hk1
      have hsKord : orderOf ((eK.symm z0 : ↥SK) : G) = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact hsK2) hsK1
      obtain ⟨g, hgK, hg⟩ := hone k (hSKK hk) _ (hSKK hsK) hkord hsKord
      have hgiD : ∀ x ∈ D, g⁻¹ * x = x * g⁻¹ := fun x hx => hcomm g⁻¹ (K.inv_mem hgK) x hx
      have e : g⁻¹⁻¹ * (k * d) * g⁻¹ = ((eK.symm z0 : ↥SK) : G) * d := by
        rw [inv_inv]
        calc g * (k * d) * g⁻¹ = (g * k) * (d * g⁻¹) := by group
          _ = (g * k) * (g⁻¹ * d) := by rw [← hgiD d (hSDD hd)]
          _ = (g * k * g⁻¹) * d := by group
          _ = ((eK.symm z0 : ↥SK) : G) * d := by rw [hg]
      refine ⟨g⁻¹, mem_Cen'.1 (Subgroup.inv_mem _ (hKC hgK)), ?_, ?_⟩
      · rw [e]
        exact mul_mem_sup_of_commute hsK hd
      · intro s hs
        obtain ⟨k', hk', d', hd', hs'⟩ := (mem_sup_iff_of_commute hcommS).1 hs
        subst hs'
        rw [e]
        have h1 : Commute k' ((eK.symm z0 : ↥SK) : G) := hsKc k' hk'
        have h2 : Commute k' d := hcomm k' (hSKK hk') d (hSDD hd)
        have h3 : Commute d' ((eK.symm z0 : ↥SK) : G) :=
          (hcomm _ (hSKK hsK) d' (hSDD hd')).symm
        have h4 : Commute d' d := hdcomm d' hd'
        exact ((h1.mul_right h2).mul_left (h3.mul_right h4)).eq
  have haut : ∀ ψ : MulAut ↥(SK ⊔ SD), ψ ⟨t, htS⟩ ∈ Subgroup.center ↥(SK ⊔ SD) →
      ψ ⟨t, htS⟩ = ⟨t, htS⟩ :=
    haut_of_prod hcommS hdisjS htSD htS eK eD (by rw [heD]; exact hq3)
  exact isolation_of_aut hs hnab ht hS1C hS12 htS hmax hcl haut

end CFSG.GH74.E2
