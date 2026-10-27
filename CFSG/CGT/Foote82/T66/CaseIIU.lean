module

public import CFSG.CGT.Foote82.T66.CaseIIRefl
import CFSG.CGT.Foote82.T66.Overgroup
import CFSG.GroupTheory.PGroup.RankTwoCommute

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel

namespace CaseII

theorem commutator_le_of_relIndex_two {Γ : Type*} [Group Γ] {X C : Subgroup Γ} (hXC : X ≤ C)
    (h : X.relIndex C = 2) : ⁅C, C⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hi : (X.subgroupOf C).index = 2 := h
  have key : (⟨a, ha⟩ : ↥C) * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥C)⁻¹ * (⟨b, hb⟩ : ↥C)⁻¹ ∈
      X.subgroupOf C := by
    have hm := fun (x y : ↥C) => Subgroup.mul_mem_iff_of_index_two hi (a := x) (b := y)
    rw [hm, hm, inv_mem_iff, hm, inv_mem_iff]
    tauto
  rw [commutatorElement_def]
  exact key

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {G L : Subgroup (GLV V)} {z : GLV V} {v : V} {H₁ : Subgroup (GLV V)}
  {ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)}

theorem card_alternatingGroup_six : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  have h := two_mul_card_alternatingGroup (α := Fin 6)
  rw [Fintype.card_perm, Fintype.card_fin] at h
  rw [Nat.card_eq_fintype_card]
  have : Nat.factorial 6 = 720 := by decide
  omega

@[expose] noncomputable def psiGL (ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)) :
    ↥H₁ →* GL I6 (ZMod 2) :=
  (orthogonalMinus 2 (ZMod 2) 1 1).subtype.comp ψ.toMonoidHom

theorem psiGL_injective : Function.Injective (psiGL ψ) :=
  (orthogonalMinus 2 (ZMod 2) 1 1).subtype_injective.comp ψ.injective

@[expose] noncomputable def XL (L : Subgroup (GLV V))
    (ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : Subgroup (GL I6 (ZMod 2)) :=
  (L.subgroupOf H₁).map (psiGL ψ)

namespace Ctx

variable (c : Ctx G L z v H₁ ψ)
include c

theorem L_le_H₁ : L ≤ H₁ := c.data.L_le

theorem isQuasisimple_L : CFSG.Open.IsQuasisimple ↥L := c.std.extremal.setup.component.2.2

theorem L_perfect : ⁅L, L⁆ = L := commutator_eq_self_of_isQuasisimple c.isQuasisimple_L

theorem card_L : Nat.card ↥L = 360 := by
  obtain ⟨e⟩ := c.data.L_iso
  rw [Nat.card_congr e.toEquiv, card_alternatingGroup_six]

theorem mem_XL_iff {x : GL I6 (ZMod 2)} :
    x ∈ XL L ψ ↔ ∃ (ℓ : GLV V) (hℓ : ℓ ∈ L), psiGL ψ ⟨ℓ, c.L_le_H₁ hℓ⟩ = x := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨ℓ, hℓ, rfl⟩
    exact ⟨⟨ℓ, c.L_le_H₁ hℓ⟩, hℓ, rfl⟩

theorem card_XL : Nat.card ↥(XL L ψ) = 360 := by
  rw [XL, Subgroup.card_map_of_injective psiGL_injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.L_le_H₁).toEquiv, c.card_L]

theorem XL_perfect : ⁅(XL L ψ), (XL L ψ)⁆ = XL L ψ := by
  have h1 : ⁅L.subgroupOf H₁, L.subgroupOf H₁⁆ = L.subgroupOf H₁ := by
    apply Subgroup.map_injective H₁.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le c.L_le_H₁]
    exact c.L_perfect
  rw [XL, ← Subgroup.map_commutator, h1]

theorem XL_le : XL L ψ ≤ omegaMinusTwo 2 ⊓ Subgroup.centralizer
    {((ψ ⟨z, c.z_mem⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : GL I6 (ZMod 2))} := by
  rintro _ ⟨⟨ℓ, hℓ₁⟩, hℓ, rfl⟩
  have hℓL : ℓ ∈ L := hℓ
  have e : (⟨ℓ, hℓ₁⟩ : ↥H₁) * ⟨z, c.z_mem⟩ = ⟨z, c.z_mem⟩ * ⟨ℓ, hℓ₁⟩ :=
    Subtype.ext (c.comm_z hℓL)
  have he := congrArg (psiGL ψ) e
  rw [map_mul, map_mul] at he
  exact ⟨(c.mem_H_iff hℓ₁).1 (c.L_le_H hℓL), Subgroup.mem_centralizer_singleton_iff.2 he⟩

theorem XL_eq (hG1 : CaseIIG1) :
    ⁅omegaMinusTwo 2 ⊓ Subgroup.centralizer
        {((ψ ⟨z, c.z_mem⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : GL I6 (ZMod 2))},
      omegaMinusTwo 2 ⊓ Subgroup.centralizer
        {((ψ ⟨z, c.z_mem⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : GL I6 (ZMod 2))}⁆ = XL L ψ := by
  set C := omegaMinusTwo 2 ⊓ Subgroup.centralizer
    {((ψ ⟨z, c.z_mem⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : GL I6 (ZMod 2))} with hC
  have hcard : Nat.card ↥C = 720 := (hG1 _ (ψ ⟨z, c.z_mem⟩).2 c.orderOf_psi_z c.data.ψ_z).2.1
  have hle := c.XL_le
  have hidx : (XL L ψ).relIndex C = 2 := by
    have h := ((XL L ψ).subgroupOf C).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, c.card_XL, hcard] at h
    rw [Subgroup.relIndex]
    omega
  apply le_antisymm (commutator_le_of_relIndex_two hle hidx)
  calc XL L ψ = ⁅(XL L ψ), (XL L ψ)⁆ := c.XL_perfect.symm
    _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hle hle

theorem eq_one_or_eq_z (hG1 : CaseIIG1) {k : GLV V} (hk : k ∈ H₁)
    (hkL : ∀ ℓ ∈ L, k * ℓ = ℓ * k) : k = 1 ∨ k = z := by
  have h3 := (hG1 _ (ψ ⟨z, c.z_mem⟩).2 c.orderOf_psi_z c.data.ψ_z).2.2 (psiGL ψ ⟨k, hk⟩)
    (ψ ⟨k, hk⟩).2 (by
      intro x hx
      rw [c.XL_eq hG1, c.mem_XL_iff] at hx
      obtain ⟨ℓ, hℓ, rfl⟩ := hx
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hkL ℓ hℓ))
  rcases h3 with h | h
  · left
    have : (⟨k, hk⟩ : ↥H₁) = 1 := psiGL_injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  · right
    have : (⟨k, hk⟩ : ↥H₁) = ⟨z, c.z_mem⟩ := psiGL_injective h
    exact congrArg Subtype.val this

theorem two_le_pRank_L : 2 ≤ CFSG.Open.pRank 2 L := by
  obtain ⟨e⟩ := c.data.L_iso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a₀ : ↥(alternatingGroup (Fin 6)) := ⟨Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.Perm.mem_alternatingGroup.2 (by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
      decide)⟩
  set b₀ : ↥(alternatingGroup (Fin 6)) := ⟨Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.Perm.mem_alternatingGroup.2 (by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
      decide)⟩
  have ha₀ : orderOf a₀ = 2 := orderOf_eq_prime (by decide) (by decide)
  have hb₀ : orderOf b₀ = 2 := orderOf_eq_prime (by decide) (by decide)
  have hab : a₀ * b₀ = b₀ * a₀ := by decide
  have hnot : b₀ ∉ Subgroup.zpowers a₀ := by
    intro h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h
    have h2 : a₀ ^ (2 : ℕ) = 1 := by decide
    have : a₀ ^ n = a₀ ^ (n % 2) := by
      have := zpow_eq_zpow_emod' n h2
      simpa using this
    rw [this] at hn
    rcases Int.emod_two_eq_zero_or_one n with h0 | h0 <;> rw [h0] at hn <;> revert hn <;> decide
  refine CFSG.GroupTheory.two_le_pRank_of_commute (x := ((e.symm a₀ : ↥L) : GLV V))
    (y := ((e.symm b₀ : ↥L) : GLV V)) (e.symm a₀).2 (e.symm b₀).2 ?_ ?_ ?_ ?_
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ha₀]
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hb₀]
  · show _ * _ = _ * _
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hab]
  · intro h
    apply hnot
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    apply e.symm.injective
    apply Subtype.ext
    rw [map_zpow, Subgroup.coe_zpow, hn]

end Ctx

end CaseII

end CFSG.CGT.Foote82
