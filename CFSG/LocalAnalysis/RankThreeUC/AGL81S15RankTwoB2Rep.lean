module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerNat
public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank


public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.RankThree.FFModules

section Faithful

theorem injective_of_isQuasisimple_of_center_eq_bot {G : Type*} [Group G] {Y : Type*}
    [AddCommGroup Y] [Module (ZMod 2) Y] (hq : CFSG.Open.IsQuasisimple G)
    (hZ : Subgroup.center G = ⊥)
    (π : G →* (Y ≃ₗ[ZMod 2] Y)) (hnt : ∃ g, π g ≠ 1) : Function.Injective π := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq π.ker with h | h
  · rw [hZ] at h
    exact le_bot_iff.mp h
  · exfalso
    obtain ⟨g, hg⟩ := hnt
    have hg' : g ∈ π.ker := by
      rw [h]
      exact Subgroup.mem_top g
    exact hg (MonoidHom.mem_ker.mp hg')

theorem pow_three_eq_one_of_central_sp4 {K : Type*} [Group K] {L : Subgroup K} {F : Type}
    [Field F] [CharP F 2] (e : ↥L ≃* StatedSp 2 F) :
    ∀ z ∈ L, (∀ k ∈ L, k * z = z * k) → z ^ 3 = 1 := by
  intro z hz hzc
  have hmem : (⟨z, hz⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzc g g.2)
  have hcen : e ⟨z, hz⟩ ∈ Subgroup.center (StatedSp 2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hmem g']
  rw [CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (by norm_num),
    Subgroup.mem_bot] at hcen
  have hz1 : (⟨z, hz⟩ : ↥L) = 1 := e.injective (by rw [hcen, map_one])
  have hz1' : z = 1 := congrArg Subtype.val hz1
  rw [hz1', one_pow]

end Faithful

section Rho

variable {K : Type*} [Group K] {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z] {L B : Subgroup K}
  {F : Type} [Field F]

@[expose] noncomputable def rhoYSp (e : ↥L ≃* StatedSp 2 F) (κ : Representation (ZMod 2) K Z)
    (Y : Submodule (ZMod 2) Z) (hY : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y) :
    StatedSp 2 F →* (↥Y ≃ₗ[ZMod 2] ↥Y) :=
  (repGL ((⟨Y, fun g _ hv => hY g g.2 _ hv⟩ :
    Subrepresentation (κ.comp L.subtype)).toRepresentation)).comp e.symm.toMonoidHom

theorem rhoYSp_coe (e : ↥L ≃* StatedSp 2 F) (κ : Representation (ZMod 2) K Z)
    (Y : Submodule (ZMod 2) Z) (hY : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y) (g : StatedSp 2 F) (y : ↥Y) :
    ((rhoYSp e κ Y hY g y : ↥Y) : Z) = κ ((e.symm g : ↥L) : K) y := rfl

theorem rhoYSp_irr (e : ↥L ≃* StatedSp 2 F) {κ : Representation (ZMod 2) K Z}
    {Y : Submodule (ZMod 2) Z} (hY : LMin L κ Y) :
    ∀ U : Submodule (ZMod 2) ↥Y, (∀ g, ∀ u ∈ U, rhoYSp e κ Y hY.inv g u ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
  intro W hW
  have hinv : ∀ l ∈ L, ∀ w ∈ W.map Y.subtype, κ l w ∈ W.map Y.subtype := by
    rintro l hl _ ⟨w, hw, rfl⟩
    refine ⟨rhoYSp e κ Y hY.inv (e ⟨l, hl⟩) w, hW _ w hw, ?_⟩
    rw [Submodule.subtype_apply, rhoYSp_coe, MulEquiv.symm_apply_apply]
    rfl
  rcases hY.min _ (Submodule.map_subtype_le Y W) hinv with hbot | htop
  · left
    have h1 : W.map Y.subtype = (⊥ : Submodule (ZMod 2) ↥Y).map Y.subtype := by
      rw [hbot, Submodule.map_bot]
    exact Submodule.map_injective_of_injective Y.injective_subtype h1
  · right
    have h1 : W.map Y.subtype = (⊤ : Submodule (ZMod 2) ↥Y).map Y.subtype := by
      rw [htop, Submodule.map_subtype_top]
    exact Submodule.map_injective_of_injective Y.injective_subtype h1

theorem rhoYSp_nontrivial (e : ↥L ≃* StatedSp 2 F) {κ : Representation (ZMod 2) K Z}
    {Y : Submodule (ZMod 2) Z} (hY : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y)
    (hnt : ∃ l ∈ L, ∃ y ∈ Y, κ l y ≠ y) : ∃ g, rhoYSp e κ Y hY g ≠ 1 := by
  obtain ⟨l, hl, y, hy, hne⟩ := hnt
  refine ⟨e ⟨l, hl⟩, fun hg => hne ?_⟩
  have h1 : rhoYSp e κ Y hY (e ⟨l, hl⟩) ⟨y, hy⟩ = ⟨y, hy⟩ := by
    rw [hg]
    rfl
  have h2 := congrArg Subtype.val h1
  rw [rhoYSp_coe, MulEquiv.symm_apply_apply] at h2
  exact h2

theorem rhoYSp_injective [CharP F 2] (h : InnerCtx L B) (e : ↥L ≃* StatedSp 2 F)
    {κ : Representation (ZMod 2) K Z} {Y : Submodule (ZMod 2) Z}
    (hY : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y) (hnt : ∃ l ∈ L, ∃ y ∈ Y, κ l y ≠ y) :
    Function.Injective (rhoYSp e κ Y hY) :=
  injective_of_isQuasisimple_of_center_eq_bot (h.quasi.of_mulEquiv e.symm)
    (CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (by norm_num)) _
    (rhoYSp_nontrivial e hY hnt)

theorem stabImage_normalizes_rhoYSp (h : InnerCtx L B) (e : ↥L ≃* StatedSp 2 F)
    (κ : Representation (ZMod 2) K Z) (Y : Submodule (ZMod 2) Z)
    (hY : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y) :
    ∀ a ∈ stabImage h κ Y, ∀ x, ∃ y, a * rhoYSp e κ Y hY x * a⁻¹ = rhoYSp e κ Y hY y := by
  intro a ha x
  obtain ⟨b, hb, hab⟩ := (mem_stabImage h κ Y).mp ha
  set l : ↥L := e.symm x with hl
  have hconj : b * (l : K) * b⁻¹ ∈ L := h.normalizes b hb.1 l l.2
  refine ⟨e ⟨b * (l : K) * b⁻¹, hconj⟩, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  refine LinearEquiv.ext fun u => Subtype.ext ?_
  show ((a (rhoYSp e κ Y hY x u) : ↥Y) : Z) =
    ((rhoYSp e κ Y hY (e ⟨b * (l : K) * b⁻¹, hconj⟩) (a u) : ↥Y) : Z)
  rw [hab, rhoYSp_coe, rhoYSp_coe, MulEquiv.symm_apply_apply, hab]
  show κ b (κ (l : K) u) = κ (b * (l : K) * b⁻¹) (κ b u)
  rw [← repMulApply, ← repMulApply, show b * (l : K) * b⁻¹ * b = b * (l : K) by group]

end Rho

end CFSG.LocalAnalysis.RankThreeUC.S15

end
