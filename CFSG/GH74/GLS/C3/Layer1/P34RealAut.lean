module

public import CFSG.GH74.GLS.C3.Layer1.P34Stmt

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34Real

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK

structure AutP34G {M : Type} [Group M] (I B : Subgroup M) (α z : M) : Prop where
  dihedral : ∃ n : ℕ, 3 ≤ n ∧ IsDihedralTwoGroup ↥(B ⊓ I) n
  z_mem : z ∈ B ⊓ I
  z_order : orderOf z = 2
  z_cent : ∀ q ∈ B ⊓ I, z * q = q * z
  z_unique : ∀ w ∈ B ⊓ I, (∀ q ∈ B ⊓ I, w * q = q * w) → w = 1 ∨ w = z
  abelian : ∀ a ∈ B, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ B ⊓ I
  invol_coset : ∀ u ∈ B, u * u = 1 → u ∉ (B ⊓ I) ⊔ zpowers α →
    ∀ u' ∈ B, u' * u' = 1 → u' ∉ (B ⊓ I) ⊔ zpowers α → u' * u⁻¹ ∈ B ⊓ I
  invol_dih : ∀ u ∈ B, u * u = 1 → u ∉ (B ⊓ I) ⊔ zpowers α →
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥((B ⊓ I) ⊔ zpowers u) ≃* DihedralGroup (2 ^ n))
  cent_B : ∀ w ∈ B, (∀ q ∈ B ⊓ I, w * q = q * w) → w ∈ zpowers α ⊔ zpowers z
  conj_z : ∀ p ∈ B ⊓ I, orderOf p = 2 → ∃ g ∈ I, g * z * g⁻¹ = p
  fus_alpha : ∀ v ∈ B ⊓ I, orderOf v = 2 →
    ∃ g ∈ I, g * (α * v) * g⁻¹ = α ∨ g * (α * v) * g⁻¹ = α * z
  shear : ∀ σ' ∈ B, orderOf σ' = 2 → σ' ∉ I → (∀ q ∈ B ⊓ I, σ' * q = q * σ') →
    ∃ p ∈ B ⊓ I, orderOf p = 2 ∧ ∃ g ∈ I, g * σ' * g⁻¹ = σ' * p

abbrev AutP34 {Kb : Type} [Group Kb] (B : Subgroup (MulAut Kb)) (α z : MulAut Kb) : Prop :=
  AutP34G (innAut Kb) B α z

@[expose] def AutLevelP (Kb : Type) [Group Kb] : Prop :=
  (∀ α : MulAut Kb, orderOf α = 2 → P34.IsFAutL2A7 Kb α →
      (Nat.card ↥(fixedSubgroup Kb α)).factorization 2 = (Nat.card Kb).factorization 2) ∧
  ∀ B : Subgroup (MulAut Kb), IsPGroup 2 ↥B → IsSylowOf 2 (B ⊓ innAut Kb) (innAut Kb) →
    ∀ α ∈ B, orderOf α = 2 → P34.IsFAutL2A7 Kb α → (∀ q ∈ B ⊓ innAut Kb, α * q = q * α) →
      ∃ z : MulAut Kb, AutP34 B α z

@[expose] def B_prop34_autlevel : Prop :=
  ∀ (Kb : Type) [Group Kb] [Finite Kb],
    (HasL2Model Kb Odd ∨ Nonempty (Kb ≃* alternatingGroup (Fin 7))) → AutLevelP Kb

theorem isDihedralGE8_of_equiv {G : Type} [Group G] {D : Subgroup G} {Y : Type} [Group Y]
    (e : ↥D ≃* Y) {n : ℕ} (hn : 3 ≤ n) (hY : IsDihedralOrder Y (2 ^ n)) :
    P34.IsDihedralGE8 D := by
  obtain ⟨k, hk, hk2, ⟨φ⟩⟩ := hY
  refine ⟨n - 1, by omega, ⟨e.trans (φ.trans ?_)⟩⟩
  have : k = 2 ^ (n - 1) := by
    have h1 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  rw [this]

end CFSG.GH74.GLS.C3.Layer1.P34Real
