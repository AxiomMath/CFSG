module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitInputs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup
open CFSG.Assembly.LowTwoRank (StatedSL StatedProj)

@[expose] def IsFieldAutPSL2Any {Y : Type} [Group Y] (φ : Y ≃* Y) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (e : Y ≃* StatedProj (StatedSL 2 F)) (σ : F ≃+* F),
    σ ≠ 1 ∧ ∀ M N : StatedSL 2 F,
      (N : GL (Fin 2) F) = Matrix.GeneralLinearGroup.map σ.toRingHom (M : GL (Fin 2) F) →
        e (φ (e.symm (QuotientGroup.mk M))) = QuotientGroup.mk N

abbrev innAut (Y : Type) [Group Y] : Subgroup (MulAut Y) :=
  (MulAut.conj : Y →* MulAut Y).range

structure SylowAutData {Y : Type} [Group Y] (T : Subgroup (MulAut Y)) (v : MulAut Y) : Prop where
  dihedral : ∃ m : ℕ, 3 ≤ m ∧ Nonempty (↥(T ⊓ innAut Y) ≃* DihedralGroup (2 ^ m))
  mem : v ∈ T
  not_mem_inn : v ∉ T ⊓ innAut Y
  field : IsFieldAutPSL2Any v
  field₀ : IsFieldAutPSL2 (v ^ (orderOf v / 2))
  disj : zpowers v ⊓ (T ⊓ innAut Y) = ⊥
  relIndex_le : ((T ⊓ innAut Y) ⊔ zpowers v).relIndex T ≤ 2
  derived : ⁅(T ⊓ innAut Y) ⊔ zpowers v, (T ⊓ innAut Y) ⊔ zpowers v⁆ =
    ⁅T ⊓ innAut Y, T ⊓ innAut Y⁆
  comm_v₀ : ∀ ρ ∈ T ⊓ innAut Y, ρ * v ^ (orderOf v / 2) = v ^ (orderOf v / 2) * ρ
  centralizer_v₀ : T ⊓ centralizer {v ^ (orderOf v / 2)} = (T ⊓ innAut Y) ⊔ zpowers v
  centralizer_R : T ⊓ centralizer ((T ⊓ innAut Y : Subgroup (MulAut Y)) : Set (MulAut Y)) =
    ((T ⊓ innAut Y) ⊓ centralizer ((T ⊓ innAut Y : Subgroup (MulAut Y)) : Set (MulAut Y))) ⊔
      zpowers (v ^ (orderOf v / 2))
  fieldInv : ∀ k ∈ T, IsFieldAutPSL2 k → ∃ ρ ∈ T ⊓ innAut Y, k = ρ * v ^ (orderOf v / 2)
  center_of_ne : T ≠ (T ⊓ innAut Y) ⊔ zpowers v →
    T ⊓ centralizer (T : Set (MulAut Y)) =
      (T ⊓ innAut Y) ⊓ centralizer ((T ⊓ innAut Y : Subgroup (MulAut Y)) : Set (MulAut Y))
  derived_of_ne : T ≠ (T ⊓ innAut Y) ⊔ zpowers v → ∀ α ∈ T, α ∉ (T ⊓ innAut Y) ⊔ zpowers v →
    (⁅T, T⁆ : Subgroup (MulAut Y)) = ⁅T ⊓ innAut Y, zpowers α⁆
  derived_cyclic_of_ne : T ≠ (T ⊓ innAut Y) ⊔ zpowers v →
    IsCyclic (⁅T, T⁆ : Subgroup (MulAut Y)) ∧ (⁅T, T⁆ : Subgroup (MulAut Y)) ≤ T ⊓ innAut Y ∧
      (⁅T, T⁆ : Subgroup (MulAut Y)).relIndex (T ⊓ innAut Y) = 2
  swap_of_ne : T ≠ (T ⊓ innAut Y) ⊔ zpowers v → ∀ α ∈ T, α ∉ (T ⊓ innAut Y) ⊔ zpowers v →
    ∀ y ∈ T ⊓ innAut Y, y ^ 2 = 1 →
      y ∉ centralizer ((T ⊓ innAut Y : Subgroup (MulAut Y)) : Set (MulAut Y)) →
      ∀ ρ ∈ T ⊓ innAut Y, α⁻¹ * y * α ≠ ρ⁻¹ * y * ρ
  small_of_ne : T ≠ (T ⊓ innAut Y) ⊔ zpowers v → ∀ α ∈ T, α ∉ (T ⊓ innAut Y) ⊔ zpowers v →
    α ^ 2 = 1 → Nat.card ↥((T ⊓ innAut Y) ⊓ centralizer {α}) ≤ 4

@[expose] def AutPSL2SylowInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → Even f → 16 ∣ p ^ f - 1 →
    Blueprint.LieModel Y .PSL 2 p f →
    ∀ K : Subgroup (MulAut Y), innAut Y ≤ K → (∃ k ∈ K, IsFieldAutPSL2 k) →
    ∀ T : Subgroup (MulAut Y), T ≤ K → (∃ P : Sylow 2 ↥K, (P : Subgroup ↥K) = T.subgroupOf K) →
      (∃ v, SylowAutData T v) ∧
      ∀ Q : Subgroup (MulAut Y), Q ≤ T →
        ∃ s : Finset (MulAut Y), s.card ≤ 3 ∧ Subgroup.closure (s : Set (MulAut Y)) = Q

theorem IsFieldAutPSL2Any.inv {Y : Type} [Group Y] {φ : Y ≃* Y} (h : IsFieldAutPSL2Any φ) :
    IsFieldAutPSL2Any φ⁻¹ := by
  obtain ⟨F, _, _, e, σ, hσ, hφ⟩ := h
  refine ⟨F, inferInstance, inferInstance, e, σ⁻¹, inv_ne_one.mpr hσ, fun M N hMN => ?_⟩
  have hNM : (M : GL (Fin 2) F) = Matrix.GeneralLinearGroup.map σ.toRingHom (N : GL (Fin 2) F) := by
    rw [hMN]
    ext i j
    simp [Matrix.GeneralLinearGroup.map, RingHom.mapMatrix]
  have h1 := hφ N M hNM
  apply e.symm.injective
  rw [MulEquiv.symm_apply_apply, ← h1, MulEquiv.symm_apply_apply]
  exact φ.symm_apply_apply _

theorem IsFieldAutPSL2.conj {Y : Type} [Group Y] {k : Y ≃* Y} (h : IsFieldAutPSL2 k)
    (a : Y ≃* Y) : IsFieldAutPSL2 (a⁻¹ * k * a) := by
  obtain ⟨F, _, _, e, σ, hσ, hk⟩ := h
  refine ⟨F, inferInstance, inferInstance, a.trans e, σ, hσ, fun M N hMN => ?_⟩
  have h1 := hk M N hMN
  simpa [MulEquiv.trans_apply, MulEquiv.symm_trans_apply] using h1

end CFSG.ComponentClassification.HarrisLit
