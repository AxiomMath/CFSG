module

public import CFSG.CGT.PushingUpLit.CGT6.TwoFiveMain
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.RegularLocalRing.Defs

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.ComponentClassification.OutcomeLocal Module Equiv

class ElemAbelianTwo (W : Type*) [CommGroup W] : Prop where
  sq : ∀ w : W, w ^ 2 = 1

def fixSub {W : Type*} [Group W] (g : MulAut W) : Subgroup W :=
  MonoidHom.eqLocus g.toMonoidHom (MonoidHom.id W)

theorem mem_fixSub {W : Type*} [Group W] {g : MulAut W} {w : W} : w ∈ fixSub g ↔ g w = w :=
  Iff.rfl

section Bridge

variable {W : Type*} [CommGroup W] [ElemAbelianTwo W]

theorem elemAbelianTwo_mul_self (w : W) : w * w = 1 := by
  rw [← pow_two]
  exact ElemAbelianTwo.sq w

instance instModuleZMod2Additive : Module (ZMod 2) (Additive W) :=
  AddCommGroup.zmodModule (n := 2) fun x =>
    Additive.toMul.injective (by simpa [toMul_nsmul] using ElemAbelianTwo.sq (Additive.toMul x))

noncomputable def autLin (g : MulAut W) : Additive W ≃ₗ[ZMod 2] Additive W :=
  LinearEquiv.ofLinearMap
    ((MulEquiv.toAdditive g).toAddMonoidHom.toZModLinearMap 2)
    ((MulEquiv.toAdditive g.symm).toAddMonoidHom.toZModLinearMap 2)
    (LinearMap.ext fun x => by simp [AddMonoidHom.coe_toZModLinearMap])
    (LinearMap.ext fun x => by simp [AddMonoidHom.coe_toZModLinearMap])

noncomputable def autGL : MulAut W →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive W) where
  toFun g := LinearMap.GeneralLinearGroup.ofLinearEquiv (autLin g)
  map_one' := Units.ext (LinearMap.ext fun _ => rfl)
  map_mul' _ _ := Units.ext (LinearMap.ext fun _ => rfl)

theorem autGL_injective : Function.Injective (autGL (W := W)) := by
  intro g h hgh
  refine MulEquiv.ext fun w => ?_
  have := congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 2) (Additive W) =>
    (u : Additive W →ₗ[ZMod 2] Additive W) (Additive.ofMul w)) hgh
  exact Additive.ofMul.injective this

theorem isF2Transvection_autGL [Finite W] (g : MulAut W)
    (h : Nat.card W = 2 * Nat.card (fixSub g)) : IsF2Transvection (autGL g) := by
  have hpos : 0 < Nat.card (fixSub g) := Nat.card_pos
  refine ⟨?_, ?_⟩
  · intro h1
    have hg : g = 1 := autGL_injective (h1.trans (map_one autGL).symm)
    have htop : fixSub g = ⊤ := by
      refine eq_top_iff.2 fun w _ => ?_
      rw [mem_fixSub, hg]
      rfl
    rw [htop, Subgroup.card_top] at h
    have := Nat.card_pos (α := W)
    omega
  · let f : Additive W →ₗ[ZMod 2] Additive W :=
      LinearMap.id + ((autGL g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive W)) :
        Additive W →ₗ[ZMod 2] Additive W)
    change finrank (ZMod 2) (LinearMap.range f) = 1
    have hker : Nat.card (LinearMap.ker f) = Nat.card (fixSub g) := by
      refine Nat.card_congr (Equiv.subtypeEquiv (Additive.toMul : Additive W ≃ W) fun x => ?_)
      change (x + (autLin g) x = 0) ↔ g (Additive.toMul x) = Additive.toMul x
      have e : (autLin g) x = Additive.ofMul (g (Additive.toMul x)) := rfl
      rw [e]
      constructor
      · intro hx
        have := congrArg Additive.toMul hx
        simp only [toMul_add, toMul_ofMul, toMul_zero] at this
        have h2 := elemAbelianTwo_mul_self (Additive.toMul x)
        exact (eq_inv_of_mul_eq_one_right this).trans (inv_eq_of_mul_eq_one_right h2)
      · intro hx
        rw [hx]
        exact Additive.toMul.injective (by simp [elemAbelianTwo_mul_self])
    have hrk := LinearMap.finrank_range_add_finrank_ker f
    have hV : Nat.card (Additive W) = 2 ^ finrank (ZMod 2) (Additive W) := by
      have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
      rwa [Nat.card_zmod] at this
    have hK : Nat.card (LinearMap.ker f) = 2 ^ finrank (ZMod 2) (LinearMap.ker f) := by
      have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker f)
      rwa [Nat.card_zmod] at this
    have hVW : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
    have hfk_pos : 0 < 2 ^ finrank (ZMod 2) (LinearMap.ker f) := by positivity
    have h2 : 2 ^ finrank (ZMod 2) (LinearMap.range f) * 2 ^ finrank (ZMod 2) (LinearMap.ker f) =
        2 * 2 ^ finrank (ZMod 2) (LinearMap.ker f) := by
      rw [← pow_add, hrk, ← hV, hVW, h, ← hK, hker]
    have h3 : 2 ^ finrank (ZMod 2) (LinearMap.range f) = 2 :=
      Nat.eq_of_mul_eq_mul_right hfk_pos h2
    exact Nat.pow_right_injective (le_refl 2) (h3.trans (pow_one 2).symm)

end Bridge

section Main

variable {W : Type*} [CommGroup W] [ElemAbelianTwo W]

theorem twoFive_aut [Finite W] {Gb : Subgroup (MulAut W)} {m : ℕ} (σ : Perm (Fin (2 * m + 1)) →* MulAut W)
    (hσ : Function.Injective σ) (hσG : ∀ s, σ s ∈ Gb) {a b : Fin (2 * m + 1)} (hab : a ≠ b)
    (htv : IsF2Transvection (autGL (σ (swap a b)))) (T : Sylow 2 ↥Gb)
    (hD : ∀ g ∈ Gb, g * σ (swap a b) * g⁻¹ ∈ (T : Subgroup ↥Gb).map Gb.subtype →
      ∃ i j, i ≠ j ∧ g * σ (swap a b) * g⁻¹ = σ (swap i j)) :
    ∀ g ∈ Gb, ∀ s ∈ σ.range, g * s * g⁻¹ ∈ σ.range := by
  classical
  have : Finite (MulAut W) := Finite.of_injective (fun (g : MulAut W) (w : W) => g w)
    (fun g h hgh => MulEquiv.ext (congrFun hgh))
  set tb : MulAut W := σ (swap a b) with htb
  let D : Set (MulAut W) := {x | ∃ g ∈ Gb, x = g * tb * g⁻¹}
  have hDG : ∀ x ∈ D, x ∈ Gb := by
    rintro x ⟨g, hg, rfl⟩
    exact mul_mem (mul_mem hg (hσG _)) (inv_mem hg)
  have hDconj : ∀ g ∈ Gb, ∀ x ∈ D, g * x * g⁻¹ ∈ D := by
    rintro g hg x ⟨g₀, hg₀, rfl⟩
    exact ⟨g * g₀, mul_mem hg hg₀, by group⟩
  have hswapD : ∀ i j, i ≠ j → σ (swap i j) ∈ D := by
    intro i j hij
    obtain ⟨π, hπ⟩ := exists_perm_swap_conj hab hij
    exact ⟨σ π, hσG π, by rw [← hπ, map_mul, map_mul, map_inv]⟩
  set G0 : Subgroup (MulAut W) := Subgroup.closure D with hG0
  have hG0Gb : G0 ≤ Gb := (Subgroup.closure_le Gb).2 hDG
  have hG0norm : ∀ g ∈ Gb, ∀ x ∈ G0, g * x * g⁻¹ ∈ G0 := by
    intro g hg x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hDconj g hg x hx)
    | one => simp
    | mul x y _ _ hx hy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact G0.mul_mem hx hy
    | inv x _ hx =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact G0.inv_mem hx
  have hσG0 : ∀ s, σ s ∈ G0 := by
    intro s
    have hs : s ∈ Subgroup.closure {f : Perm (Fin (2 * m + 1)) | f.IsSwap} := by
      rw [Equiv.Perm.closure_isSwap]
      exact Subgroup.mem_top s
    induction hs using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, j, hij, rfl⟩ := hx
      exact Subgroup.subset_closure (hswapD i j hij)
    | one => simp
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact G0.mul_mem hx hy
    | inv x _ hx =>
      rw [map_inv]
      exact G0.inv_mem hx
  let σ' : Perm (Fin (2 * m + 1)) →* ↥G0 := σ.codRestrict G0 hσG0
  let D' : Set ↥G0 := ((↑) : ↥G0 → MulAut W) ⁻¹' D
  let ρ : ↥G0 →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive W) := autGL.comp G0.subtype
  have hsurj : Function.Surjective σ' := by
    refine twoFive_surjective' (ρ := ρ) (D := D') ?_ ?_ ?_ σ' ?_ ?_ ?_
    · exact autGL_injective.comp Subtype.val_injective
    · rintro ⟨x, hxG⟩ ⟨g₀, hg₀, hx⟩
      change IsF2Transvection (autGL x)
      have hx' : x = g₀ * tb * g₀⁻¹ := hx
      rw [hx', map_mul, map_mul, map_inv]
      exact isF2Transvection_conj htv _
    · exact Subgroup.closure_closure_coe_preimage
    · intro s t hst
      exact hσ (congrArg Subtype.val hst)
    · intro i j hij
      exact hswapD i j hij
    · intro P hP
      let ι : ↥G0 →* ↥Gb := Subgroup.inclusion hG0Gb
      have hP' : IsPGroup 2 (P.map ι) := hP.map ι
      obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
      obtain ⟨gh, hgh⟩ := MulAction.exists_smul_eq ↥Gb Q T
      let c : ↥G0 ≃* ↥G0 :=
        { toFun := fun x => ⟨gh.1 * x.1 * gh.1⁻¹, hG0norm _ gh.2 _ x.2⟩
          invFun := fun x => ⟨gh.1⁻¹ * x.1 * gh.1, by
            simpa using hG0norm _ (inv_mem gh.2) _ x.2⟩
          left_inv := fun x => Subtype.ext (by
            change gh.1⁻¹ * (gh.1 * x.1 * gh.1⁻¹) * gh.1 = x.1
            group)
          right_inv := fun x => Subtype.ext (by
            change gh.1 * (gh.1⁻¹ * x.1 * gh.1) * gh.1⁻¹ = x.1
            group)
          map_mul' := fun x y => Subtype.ext (by
            change gh.1 * (x.1 * y.1) * gh.1⁻¹ = gh.1 * x.1 * gh.1⁻¹ * (gh.1 * y.1 * gh.1⁻¹)
            group) }
      refine ⟨c, fun d hd hdP => ?_⟩
      obtain ⟨g₀, hg₀, hx⟩ := hd
      have hmem : gh.1 * d.1 * gh.1⁻¹ ∈ (T : Subgroup ↥Gb).map Gb.subtype := by
        refine ⟨gh * ι d * gh⁻¹, ?_, rfl⟩
        have h1 : ι d ∈ (Q : Subgroup ↥Gb) := hQ (Subgroup.mem_map_of_mem ι hdP)
        have h2 : gh * ι d * gh⁻¹ ∈ ((gh • Q : Sylow 2 ↥Gb) : Subgroup ↥Gb) := by
          rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
          simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using h1
        rw [hgh] at h2
        exact h2
      have hx' : d.1 = g₀ * tb * g₀⁻¹ := hx
      obtain ⟨i, j, hij, hij'⟩ := hD (gh.1 * g₀) (mul_mem gh.2 hg₀) (by
        have : (gh.1 * g₀) * tb * (gh.1 * g₀)⁻¹ = gh.1 * d.1 * gh.1⁻¹ := by rw [hx']; group
        rw [this]
        exact hmem)
      refine ⟨i, j, hij, Subtype.ext ?_⟩
      have : (gh.1 * g₀) * tb * (gh.1 * g₀)⁻¹ = gh.1 * d.1 * gh.1⁻¹ := by rw [hx']; group
      rw [this] at hij'
      exact hij'
  intro g hg s hs
  obtain ⟨π, rfl⟩ := hs
  obtain ⟨π', hπ'⟩ := hsurj ⟨g * σ π * g⁻¹, hG0norm g hg _ (hσG0 π)⟩
  exact ⟨π', congrArg Subtype.val hπ'⟩

end Main

end CFSG.CGT.PushingUpLit.CGT6
