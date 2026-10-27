module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Act

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup

namespace Sec2

section Rho

variable {G : Type} [Group G] {Q : Subgroup G} {z : G} {ψ : G → (Fin 6 → ZMod 2)}
  (hadd : ∀ a ∈ Q, ∀ b ∈ Q, ψ (a * b) = ψ a + ψ b)
  (hsurj : ∀ v : Fin 6 → ZMod 2, ∃ a ∈ Q, ψ a = v)
  (hker : ∀ a ∈ Q, ψ a = 0 ↔ a ∈ zpowers z)
  {K : Subgroup G} (hK : K ≤ normalizer (Q : Set G) ⊓ centralizer ({z} : Set G))

noncomputable def rhoEquiv (c : K) : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun := act hsurj (c : G)
  invFun := act hsurj (c : G)⁻¹
  map_add' u w := by
    obtain ⟨a, ha, rfl⟩ := hsurj u
    obtain ⟨b, hb, rfl⟩ := hsurj w
    have hN := (hK c.2).1
    have hz := (hK c.2).2
    have hca := (mem_normalizer_iff.mp hN a).mp ha
    have hcb := (mem_normalizer_iff.mp hN b).mp hb
    rw [← hadd a ha b hb, act_psi hadd hsurj hker hN hz (Q.mul_mem ha hb),
      act_psi hadd hsurj hker hN hz ha, act_psi hadd hsurj hker hN hz hb,
      show (c : G) * (a * b) * (c : G)⁻¹ = ((c : G) * a * (c : G)⁻¹) * ((c : G) * b * (c : G)⁻¹)
        by group]
    exact hadd _ hca _ hcb
  map_smul' r u := by
    rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one r with rfl | rfl
    · rw [zero_smul, RingHom.id_apply, zero_smul, ← psi_one hadd,
        act_psi hadd hsurj hker (hK c.2).1 (hK c.2).2 Q.one_mem, mul_one, mul_inv_cancel]
    · rw [one_smul, RingHom.id_apply, one_smul]
  left_inv u := by
    rw [← act_mul hadd hsurj hker (inv_mem (hK c.2).1) (inv_mem (hK c.2).2) (hK c.2).1 (hK c.2).2,
      inv_mul_cancel, act_one hadd hsurj hker]
  right_inv u := by
    rw [← act_mul hadd hsurj hker (hK c.2).1 (hK c.2).2 (inv_mem (hK c.2).1) (inv_mem (hK c.2).2),
      mul_inv_cancel, act_one hadd hsurj hker]

noncomputable def rho : ↥K →* ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) where
  toFun := rhoEquiv hadd hsurj hker hK
  map_one' := LinearEquiv.ext fun u => act_one hadd hsurj hker u
  map_mul' c d := LinearEquiv.ext fun u =>
    act_mul hadd hsurj hker (hK c.2).1 (hK c.2).2 (hK d.2).1 (hK d.2).2 u

theorem rho_psi (c : K) {a : G} (ha : a ∈ Q) :
    rho hadd hsurj hker hK c (ψ a) = ψ ((c : G) * a * (c : G)⁻¹) :=
  act_psi hadd hsurj hker (hK c.2).1 (hK c.2).2 ha

theorem rho_mem_orthogonalGroup (hsq : ∀ a ∈ Q, qMinus (ψ a) = 0 ↔ a * a = 1) (c : K) :
    rho hadd hsurj hker hK c ∈ TauCeti.QuadraticMap.orthogonalGroup Sec2Omega.qMinusForm := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro u
  obtain ⟨a, ha, rfl⟩ := hsurj u
  rw [rho_psi hadd hsurj hker hK c ha, Sec2Omega.qMinusForm_apply, Sec2Omega.qMinusForm_apply]
  have hca := (mem_normalizer_iff.mp (hK c.2).1 a).mp ha
  have h3 : ((c : G) * a * (c : G)⁻¹) * ((c : G) * a * (c : G)⁻¹) = 1 ↔ a * a = 1 := by
    rw [show ((c : G) * a * (c : G)⁻¹) * ((c : G) * a * (c : G)⁻¹) =
      (c : G) * (a * a) * (c : G)⁻¹ by group]
    constructor
    · intro h
      rw [show a * a = (c : G)⁻¹ * ((c : G) * (a * a) * (c : G)⁻¹) * (c : G) by group, h]
      group
    · intro h
      rw [h]
      group
  have key := (hsq _ hca).trans (h3.trans (hsq a ha).symm)
  rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one (qMinus (ψ a)) with h | h <;>
    rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one
      (qMinus (ψ ((c : G) * a * (c : G)⁻¹))) with h' | h'
  · rw [h, h']
  · exact absurd (key.mpr h) (by rw [h']; exact one_ne_zero)
  · exact absurd (key.mp h') (by rw [h]; exact one_ne_zero)
  · rw [h, h']

theorem rho_eq_one_iff (c : K) :
    rho hadd hsurj hker hK c = 1 ↔ ∀ a ∈ Q, (c : G) * a * (c : G)⁻¹ * a⁻¹ ∈ zpowers z := by
  constructor
  · intro h a ha
    have h1 := rho_psi hadd hsurj hker hK c ha
    rw [h, LinearEquiv.coe_one, id] at h1
    exact (psi_eq_iff hadd hker ((mem_normalizer_iff.mp (hK c.2).1 a).mp ha) ha).mp h1.symm
  · intro h
    refine LinearEquiv.ext fun u => ?_
    obtain ⟨a, ha, rfl⟩ := hsurj u
    rw [rho_psi hadd hsurj hker hK c ha, LinearEquiv.coe_one, id]
    exact (psi_eq_iff hadd hker ((mem_normalizer_iff.mp (hK c.2).1 a).mp ha) ha).mpr (h a ha)

end Rho

end Sec2

end CFSG.ComponentClassification.AS81
