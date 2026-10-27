module

public import CFSG.LargeExtraspecial.GLRLinPair
public import CFSG.LargeExtraspecial.S12Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

@[expose] noncomputable def kerB (A : Submodule (ZMod 2) S.Qt) (β : S.Qt) :
    Submodule (ZMod 2) S.Qt :=
  A ⊓ LinearMap.ker (S.q.polarBilin.flip β)

structure Mixed (S : Setting G) (X : Subgroup S.O) (A B : Submodule (ZMod 2) S.Qt) (k : G)
    (α β : S.Qt) : Prop where
  pair : Pair S X A B
  five_le : 5 ≤ S.width
  le_Mbar : X ≤ S.Mbar
  conj_mem : k * S.z * k⁻¹ ∈ S.QG
  conj_ne : k * S.z * k⁻¹ ≠ S.z
  mem_A : α ∈ A
  mem_B : β ∈ B
  ne_zero_A : α ≠ 0
  ne_zero_B : β ≠ 0
  cl_eq : S.cl (k * S.z * k⁻¹) = α + β

namespace Pair

variable {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt}

theorem fix_of_fix_add (h : Pair S X A B) {e : S.O} (he : e ∈ X) {α β : S.Qt} (hα : α ∈ A)
    (hβ : β ∈ B) (hfix : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) (α + β) = α + β) :
    (e : S.Qt ≃ₗ[ZMod 2] S.Qt) α = α ∧ (e : S.Qt ≃ₗ[ZMod 2] S.Qt) β = β := by
  rw [map_add] at hfix
  have hd : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) α - α ∈ A ⊓ B := by
    refine ⟨A.sub_mem (h.apply_A e he α hα) hα, ?_⟩
    have : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) α - α = β - (e : S.Qt ≃ₗ[ZMod 2] S.Qt) β := by
      rw [sub_eq_sub_iff_add_eq_add, hfix, add_comm]
    rw [this]
    exact B.sub_mem hβ (h.apply_B e he β hβ)
  rw [h.inf_eq, Submodule.mem_bot, sub_eq_zero] at hd
  refine ⟨hd, ?_⟩
  rw [hd] at hfix
  exact add_left_cancel hfix

end Pair

namespace Mixed

variable {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt} {k : G} {α β : S.Qt}

theorem polar_eq (hM : Mixed S X A B k α β) : polar S.q α β = 0 := by
  have hq : S.q (α + β) = 0 := by
    rw [← hM.cl_eq]
    exact (S.q_cl_eq_zero_iff hM.conj_mem).mpr (S.s12_conj_z_sq k)
  have h1 : polar S.q α β = S.q (α + β) - S.q α - S.q β := rfl
  rw [h1, hq, hM.pair.q_A α hM.mem_A, hM.pair.q_B β hM.mem_B, sub_zero, sub_zero]

theorem Lbar_fix (hM : Mixed S X A B k α β) {e : S.O} (he : e ∈ S.Lbar k) :
    (e : S.Qt ≃ₗ[ZMod 2] S.Qt) (α + β) = α + β := by
  rw [← hM.cl_eq]
  exact S.s12_Lbar_apply_cl_a hM.conj_mem he

theorem fix_of_mem (hM : Mixed S X A B k α β) {e : S.O} (he : e ∈ S.Lbar k ⊓ X) :
    (e : S.Qt ≃ₗ[ZMod 2] S.Qt) α = α ∧ (e : S.Qt ≃ₗ[ZMod 2] S.Qt) β = β :=
  hM.pair.fix_of_fix_add he.2 hM.mem_A hM.mem_B (hM.Lbar_fix he.1)

theorem mem_normalizer (hM : Mixed S X A B k α β) {p : S.O} (hp : p ∈ S.Mbar)
    (hpx : (p : S.Qt ≃ₗ[ZMod 2] S.Qt) (α + β) = α + β) :
    p ∈ normalizer (S.Lbar k : Set S.O) := by
  obtain ⟨m, rfl⟩ := hp
  refine (S.timmesfeld_12_4_1 hM.conj_mem hM.conj_ne (by have := hM.five_le; omega) m).mpr ?_
  rw [hM.cl_eq]
  exact hpx

theorem conj_mem_E (hM : Mixed S X A B k α β) {p e : S.O} (hp : p ∈ X)
    (hpα : (p : S.Qt ≃ₗ[ZMod 2] S.Qt) α = α) (hpβ : (p : S.Qt ≃ₗ[ZMod 2] S.Qt) β = β)
    (he : e ∈ S.Lbar k ⊓ X) : p * e * p⁻¹ ∈ S.Lbar k ⊓ X := by
  have hN := hM.mem_normalizer (hM.le_Mbar hp) (by rw [map_add, hpα, hpβ])
  exact ⟨(mem_normalizer_iff.mp hN e).mp he.1, X.mul_mem (X.mul_mem hp he.2) (X.inv_mem hp)⟩

theorem conj_mem_E' (hM : Mixed S X A B k α β) {p e : S.O} (hp : p ∈ X)
    (hpα : (p : S.Qt ≃ₗ[ZMod 2] S.Qt) α = α) (hpβ : (p : S.Qt ≃ₗ[ZMod 2] S.Qt) β = β)
    (he : e ∈ S.Lbar k ⊓ X) : p⁻¹ * e * p ∈ S.Lbar k ⊓ X := by
  have hinv : ∀ v, ((p⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((p : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v :=
    fun v => by rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have h1 := hM.conj_mem_E (p := p⁻¹) (X.inv_mem hp)
    (by conv_lhs => rw [← hpα]
        exact hinv α)
    (by conv_lhs => rw [← hpβ]
        exact hinv β) he
  rwa [inv_inv] at h1

theorem exists_a₀ (hM : Mixed S X A B k α β) : ∃ a₀ ∈ A, polar S.q a₀ β = 1 :=
  hM.pair.exists_polar_eq_one hM.mem_B hM.ne_zero_B

theorem α_mem_kerB (hM : Mixed S X A B k α β) : α ∈ kerB A β :=
  ⟨hM.mem_A, hM.polar_eq⟩

theorem sub_mem_kerB {a₀ : S.Qt} (ha₀ : a₀ ∈ A)
    (ha₀β : polar S.q a₀ β = 1) {a : S.Qt} (ha : a ∈ A) :
    a - polar S.q a β • a₀ ∈ kerB A β := by
  refine ⟨A.sub_mem ha (A.smul_mem _ ha₀), ?_⟩
  change polar S.q (a - polar S.q a β • a₀) β = 0
  rw [polar_sub_left, polar_smul_left, ha₀β, smul_eq_mul, mul_one, sub_self]

theorem finrank_kerB (hM : Mixed S X A B k α β) : S.width - 1 ≤ finrank (ZMod 2) (kerB A β) := by
  obtain ⟨a₀, ha₀, ha₀β⟩ := hM.exists_a₀
  have hle : A ≤ kerB A β ⊔ Submodule.span (ZMod 2) ({a₀} : Set S.Qt) := by
    intro a ha
    have e : a = (a - polar S.q a β • a₀) + polar S.q a β • a₀ := by abel
    rw [e]
    exact Submodule.add_mem_sup (sub_mem_kerB ha₀ ha₀β ha)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (kerB A β)
    (Submodule.span (ZMod 2) ({a₀} : Set S.Qt))
  have h3 : finrank (ZMod 2) (Submodule.span (ZMod 2) ({a₀} : Set S.Qt)) ≤ 1 := by
    have := finrank_span_le_card (R := ZMod 2) ({a₀} : Set S.Qt)
    simpa using this
  rw [hM.pair.finrank_A] at h1
  omega

theorem apply_kerB_mem (hM : Mixed S X A B k α β) {e : S.O} (he : e ∈ S.Lbar k ⊓ X) {u : S.Qt}
    (hu : u ∈ kerB A β) : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ kerB A β := by
  refine ⟨hM.pair.apply_A e he.2 u hu.1, ?_⟩
  change polar S.q ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) u) β = 0
  conv_lhs => rw [← (hM.fix_of_mem he).2]
  rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup e.2]
  exact hu.2

end Mixed

end CFSG.LargeExtraspecial.GLR
