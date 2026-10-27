module

public import CFSG.LargeExtraspecial.AS35YFSymAut
public import CFSG.LargeExtraspecial.AS35YFHub
public import CFSG.LargeExtraspecial.AS35YFOut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.OuterAutomorphisms

namespace AS35YF

theorem mem_inner_of_perm_six {X : Type*} [Group X] (φ : X ≃* Perm (Fin 6)) {E : Set X}
    (hφ : ∀ x, x ∈ E ↔ (φ x).IsSwap) (α : MulAut X) (hαE : ∀ e ∈ E, α e ∈ E) :
    α ∈ inner X := by
  have hsw : ∀ σ : Perm (Fin 6), σ.IsSwap → (MulAut.congr φ α σ).IsSwap := by
    intro σ hσ
    have h1 : φ.symm σ ∈ E := (hφ _).mpr (by rwa [MulEquiv.apply_symm_apply])
    have h2 := (hφ _).mp (hαE _ h1)
    simpa [MulAut.congr_apply] using h2
  obtain ⟨π, hπ⟩ := perm_aut_eq_conj_of_isSwap _ hsw (by norm_num)
  refine ⟨φ.symm π, MulEquiv.ext fun x => ?_⟩
  have h3 := hπ (φ x)
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h3
  rw [MulAut.conj_apply]
  apply φ.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact h3.symm

theorem comm_of_perm_six {X : Type*} [Group X] (φ : X ≃* Perm (Fin 6)) {τ : X}
    (hτ : (φ τ).IsSwap) {N : Subgroup X} (hA : Setting.AscImage N τ) {a b : X} (ha : a ∈ N)
    (hb : b ∈ N) : a * b = b * a := by
  obtain ⟨u, v, huv, huvt⟩ := hτ
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_swap huv (by decide : (0 : Fin 6) ≠ 1))
  set ψ : X ≃* Perm (Fin 6) := φ.trans (MulAut.conj c) with hψ
  have hψt : ψ τ = swap 0 1 := by
    rw [hψ, MulEquiv.trans_apply, huvt, MulAut.conj_apply, hc]
  have hA' := hA.map ψ
  rw [hψt] at hA'
  have hTa := mem_T6_of_normal hA'.isPGroup hA'.commute hA'.normal ⟨a, ha, rfl⟩
  have hTb := mem_T6_of_normal hA'.isPGroup hA'.commute hA'.normal ⟨b, hb, rfl⟩
  have hcomm := t6_comm _ hTa _ hTb
  exact ψ.injective ((map_mul ψ a b).trans (hcomm.trans (map_mul ψ b a).symm))

theorem mem_image_iff_isConj {Y : Type*} [Group Y] {L : Subgroup Y} {D : Set Y}
    (hcls : ∀ a ∈ D, ∀ b ∈ D, ∃ g ∈ L, g * a * g⁻¹ = b)
    (hconj : ∀ g ∈ L, ∀ d ∈ D, g * d * g⁻¹ ∈ D) {t : Y} (ht : t ∈ D) (htL : t ∈ L)
    (x : L ⧸ center L) :
    x ∈ (QuotientGroup.mk' (center L)) '' (Subtype.val ⁻¹' D) ↔
      IsConj (QuotientGroup.mk ⟨t, htL⟩ : L ⧸ center L) x := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨y, hy, hyd⟩ := hcls _ ht _ hd
    refine isConj_iff.mpr ⟨QuotientGroup.mk ⟨y, hy⟩, ?_⟩
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext hyd)
  · intro hx
    obtain ⟨y, rfl⟩ := isConj_iff.mp hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨y * ⟨t, htL⟩ * y⁻¹, ?_, by simp⟩
    exact hconj y y.2 t ht

end AS35YF

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

variable (hst : S.Asc512Standing)
include hst

theorem asc_mem_Ehat_iff {g : G} (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M)
    (x : S.LbarAsc ⧸ center S.LbarAsc) :
    x ∈ S.EhatAsc ↔ IsConj (QuotientGroup.mk (ascTL htD htM)) x :=
  AS35YF.mem_image_iff_isConj hst.conj
    (fun _g hg _d hd => S.conj_mem_DbarAsc_L (asc_Lbar_le_Mbar hg) hd)
    (S.ρ_mem_DbarAsc htD htM) _ x

theorem asc_false_of_perm_six (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M)
    (φ : S.LbarAsc ⧸ center S.LbarAsc ≃* Perm (Fin 6))
    (hφ : ∀ x : S.LbarAsc ⧸ center S.LbarAsc, x ∈ S.EhatAsc ↔ (φ x).IsSwap) : False := by
  have hle := asc_Pbar_le_Lbar_of_inner hst hP hS htD htM fun p hp =>
    AS35YF.mem_inner_of_perm_six φ hφ _ fun e he => asc_hub_E hst (g := g) _ ⟨p, hp, rfl⟩ e he
  obtain ⟨a, ha, b, hb, hab⟩ := ascPhat_not_comm_of_le hst hP hS htD htM hle
  exact hab (AS35YF.comm_of_perm_six φ ((hφ _).mp ⟨ascTL htD htM, S.ρ_mem_DbarAsc htD htM, rfl⟩)
    (ascImage_ascPhat hst hP hS htD htM) ha hb)

end Setting

end CFSG.LargeExtraspecial
