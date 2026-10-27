module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieU5Swap
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Irr

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.LocalAnalysis.RankThreeTheoremC

section Aut

variable {X : Type*} [Group X]

@[expose] def autOfStab (ψ : X ≃* X) (J : Subgroup X) (h1 : ∀ g ∈ J, ψ g ∈ J)
    (h2 : ∀ g ∈ J, ψ.symm g ∈ J) : J ≃* J where
  toFun g := ⟨ψ g, h1 g g.2⟩
  invFun g := ⟨ψ.symm g, h2 g g.2⟩
  left_inv g := Subtype.ext (ψ.symm_apply_apply _)
  right_inv g := Subtype.ext (ψ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul ψ _ _)

theorem autOfStab_apply (ψ : X ≃* X) (J : Subgroup X) (h1 : ∀ g ∈ J, ψ g ∈ J)
    (h2 : ∀ g ∈ J, ψ.symm g ∈ J) (g : J) : ((autOfStab ψ J h1 h2 g : J) : X) = ψ g := rfl

end Aut

section Main

variable {Q : Type*} [Group Q]

theorem not_transitive_of_separated {Lb P E N : Subgroup Q} (hPL : P ≤ Lb) (hEP : E ≤ P)
    (hNLb : N ≤ Subgroup.normalizer (Lb : Set Q)) (hNP : N ≤ Subgroup.normalizer (P : Set Q))
    (hsep : ∃ e₁ e₂ : ↥((P.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb))),
      (e₁ : ↥Lb ⧸ Subgroup.center ↥Lb) ∈
        (E.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb)) ∧
      (e₂ : ↥Lb ⧸ Subgroup.center ↥Lb) ∈
        (E.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb)) ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧
      ∀ φ : ↥((P.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb))) ≃*
        ↥((P.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb))), φ e₁ ≠ e₂) :
    ¬ TransitiveOnNonidentity N E := by
  intro htr
  set ρ := QuotientGroup.mk' (Subgroup.center ↥Lb) with hρ
  set Jim : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb) := (P.subgroupOf Lb).map ρ with hJim
  obtain ⟨e₁, e₂, h₁, h₂, hn₁, hn₂, hφ⟩ := hsep
  obtain ⟨a₁, ha₁, ha₁e⟩ := h₁
  obtain ⟨a₂, ha₂, ha₂e⟩ := h₂
  have hu₁ : (a₁ : Q) ∈ E := Subgroup.mem_subgroupOf.mp ha₁
  have hu₂ : (a₂ : Q) ∈ E := Subgroup.mem_subgroupOf.mp ha₂
  have hu₁1 : (a₁ : Q) ≠ 1 := fun h => hn₁ (by
    apply Subtype.ext
    rw [← ha₁e]
    have : a₁ = 1 := Subtype.ext h
    rw [this, map_one]; rfl)
  have hu₂1 : (a₂ : Q) ≠ 1 := fun h => hn₂ (by
    apply Subtype.ext
    rw [← ha₂e]
    have : a₂ = 1 := Subtype.ext h
    rw [this, map_one]; rfl)
  obtain ⟨n, hn, hn12⟩ := htr _ hu₁ _ hu₂ hu₁1 hu₂1
  have hnLb : n ∈ Subgroup.normalizer (Lb : Set Q) := hNLb hn
  have hnLb' : n⁻¹ ∈ Subgroup.normalizer (Lb : Set Q) := hNLb (N.inv_mem hn)
  obtain ⟨ψ, hψ⟩ := exists_inducedAut hnLb
  obtain ⟨ψ', hψ'⟩ := exists_inducedAut hnLb'
  have hψρ : ∀ y : ↥Lb, ψ (ρ y) = ρ (conjOnNormalizer Lb n hnLb y) := hψ
  have hψρ' : ∀ y : ↥Lb, ψ' (ρ y) = ρ (conjOnNormalizer Lb n⁻¹ hnLb' y) := hψ'
  have hPn : ∀ y : ↥Lb, y ∈ P.subgroupOf Lb → conjOnNormalizer Lb n hnLb y ∈ P.subgroupOf Lb :=
    fun y hy => Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp (hNP hn) y).mp (Subgroup.mem_subgroupOf.mp hy))
  have hPn' : ∀ y : ↥Lb, y ∈ P.subgroupOf Lb → conjOnNormalizer Lb n⁻¹ hnLb' y ∈ P.subgroupOf Lb :=
    fun y hy => Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp (hNP (N.inv_mem hn)) y).mp (Subgroup.mem_subgroupOf.mp hy))
  have h1 : ∀ g ∈ Jim, ψ g ∈ Jim := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hψρ]
    exact ⟨_, hPn y hy, rfl⟩
  have hψψ' : ∀ g, ψ (ψ' g) = g := by
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    change ψ (ψ' (ρ y)) = ρ y
    rw [hψρ', hψρ]
    congr 1
    apply Subtype.ext
    show n * (n⁻¹ * (y : Q) * n⁻¹⁻¹) * n⁻¹ = y
    group
  have hψ'symm : ∀ g, ψ.symm g = ψ' g := fun g =>
    (ψ.symm_apply_eq.mpr (hψψ' g).symm)
  have h2 : ∀ g ∈ Jim, ψ.symm g ∈ Jim := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hψ'symm]
    change ψ' (ρ y) ∈ Jim
    rw [hψρ']
    exact ⟨_, hPn' y hy, rfl⟩
  refine hφ (autOfStab ψ Jim h1 h2) (Subtype.ext ?_)
  rw [autOfStab_apply, ← ha₁e, hψρ, ← ha₂e]
  congr 1
  exact Subtype.ext hn12

end Main

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
