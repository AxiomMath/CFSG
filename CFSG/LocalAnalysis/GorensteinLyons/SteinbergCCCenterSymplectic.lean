module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCSymplecticCore

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)
open scoped IsMulCommutative commutatorElement

theorem cyclic_center_two_core_faithful_symplectic_action {H : Type*} [Group H] [Finite H]
    (hH : IsCharacteristicP 2 H) (hQnab : ∃ x y : pCore 2 H, x * y ≠ y * x)
    [IsCyclic (center (pCore 2 H))]
    [IsElementaryAbelian 2 (pCore 2 H ⧸ center (pCore 2 H))]
    {z : pCore 2 H} (hzZ : z ∈ center (pCore 2 H)) (hz : orderOf z = 2) :
    commutator (pCore 2 H) = zpowers z ∧
    (∃! w : ℕ, 1 ≤ w ∧
      Module.finrank (ZMod 2) (Additive (pCore 2 H ⧸ center (pCore 2 H))) = 2 * w) ∧
    ∃ b : LinearMap.BilinForm (ZMod 2) (Additive (pCore 2 H ⧸ center (pCore 2 H))),
      (∀ x y : pCore 2 H, ⁅x, y⁆ = z ^ (b (Additive.ofMul (x : pCore 2 H ⧸ center (pCore 2 H)))
        (Additive.ofMul (y : pCore 2 H ⧸ center (pCore 2 H)))).val) ∧
      (∀ b' : LinearMap.BilinForm (ZMod 2) (Additive (pCore 2 H ⧸ center (pCore 2 H))),
        (∀ x y : pCore 2 H, ⁅x, y⁆ = z ^ (b' (Additive.ofMul (x : pCore 2 H ⧸ center (pCore 2 H)))
          (Additive.ofMul (y : pCore 2 H ⧸ center (pCore 2 H)))).val) → b' = b) ∧
      b.IsAlt ∧ b.Nondegenerate ∧
      ∃ ρ : H →* LinearMap.GeneralLinearGroup (ZMod 2)
          (Additive (pCore 2 H ⧸ center (pCore 2 H))),
        (∀ (h : H) (x y : pCore 2 H), (y : H) = h * x * h⁻¹ →
          ((ρ h : LinearMap.GeneralLinearGroup (ZMod 2)
              (Additive (pCore 2 H ⧸ center (pCore 2 H)))) :
            Module.End (ZMod 2) (Additive (pCore 2 H ⧸ center (pCore 2 H))))
              (Additive.ofMul (x : pCore 2 H ⧸ center (pCore 2 H))) =
            Additive.ofMul (y : pCore 2 H ⧸ center (pCore 2 H))) ∧
        ρ.ker = pCore 2 H ∧ (∀ h, ρ h ∈ bilinIsometryGroup b) ∧
        (∃ ι : H ⧸ pCore 2 H →* bilinIsometryGroup b, Function.Injective ι ∧
          ∀ h : H, ((ι (h : H ⧸ pCore 2 H) : bilinIsometryGroup b) :
            LinearMap.GeneralLinearGroup (ZMod 2) (Additive (pCore 2 H ⧸ center (pCore 2 H)))) =
              ρ h) ∧
        ∀ K : Subgroup H, Odd (Nat.card K) → Function.Injective (ρ.comp K.subtype) := by
  have hQD : ∀ q ∈ pCore 2 H, ∀ d d' : pCore 2 H, ⁅q, (d : H)⁆ * d' = d' * ⁅q, (d : H)⁆ := by
    intro q hq d d'
    have h := commutatorElement_mem_center_of_isElementaryAbelian (⟨q, hq⟩ : pCore 2 H) d
    have h' := congrArg Subtype.val (mem_center_iff.mp h d')
    have hc : ((⁅(⟨q, hq⟩ : pCore 2 H), d⁆ : pCore 2 H) : H) = ⁅q, (d : H)⁆ :=
      map_commutatorElement (pCore 2 H).subtype _ _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc] at h'
    exact h'.symm
  have hCQ : ∀ q ∈ pCore 2 H, (∀ d : pCore 2 H, q * d = d * q) → q ∈ pCore 2 H :=
    fun q hq _ => hq
  obtain ⟨hzz, b, hrule, hba, hbn, hker, hiso, hι, hodd⟩ :=
    symplectic_core hH le_rfl hQD hCQ hzZ hz
  obtain ⟨x, y, hxy⟩ := hQnab
  have hxy' : ⁅x, y⁆ ≠ 1 := fun h => hxy (commutatorElement_eq_one_iff_mul_comm.mp h)
  refine ⟨commutator_eq_zpowers_of_exists hzz hxy', ?_, b, hrule,
    fun b' hb' => bilinForm_eq_of_commutator_rule hz hrule hb', hba, hbn,
    centerQuotientConjGL (pCore 2 H), ?_, hker, hiso, hι, hodd⟩
  · obtain ⟨w, hw, hwu⟩ := existsUnique_finrank_eq_two_mul hba hbn
    have hne : Module.finrank (ZMod 2) (Additive (pCore 2 H ⧸ center (pCore 2 H))) ≠ 0 := by
      rw [Ne, finrank_eq_zero_iff_forall_mem_center]
      intro hall
      exact hxy (mem_center_iff.mp (hall y) x)
    refine ⟨w, ⟨by omega, hw⟩, fun w' hw' => hwu w' hw'.2⟩
  · intro h x y hy
    rw [centerQuotientConjGL_apply]
    congr 2
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, hy]

end CFSG.LocalAnalysis.GorensteinLyons
