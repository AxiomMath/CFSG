module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EPlane
public import CFSG.HardMathSupport.Solomon.LocalBalance.Extremal
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.HardMathSupport.Solomon.LocalBalance

def mulAutToLin {H : Type*} [CommGroup H] [Module (ZMod 3) (Additive H)] (g : MulAut H) :
    Additive H ≃ₗ[ZMod 3] Additive H where
  toFun x := Additive.ofMul (g x.toMul)
  map_add' x y := by simp
  map_smul' c x := ZMod.map_smul
    (AddMonoidHom.mk' (fun x : Additive H => Additive.ofMul (g x.toMul)) (fun x y => by simp)) c x
  invFun x := Additive.ofMul (g.symm x.toMul)
  left_inv x := by simp
  right_inv x := by simp

def mulAutToLinHom (H : Type*) [CommGroup H] [Module (ZMod 3) (Additive H)] :
    MulAut H →* (Additive H ≃ₗ[ZMod 3] Additive H) where
  toFun := mulAutToLin
  map_one' := by ext x; rfl
  map_mul' g h := by ext x; rfl

theorem mulAutToLinHom_injective (H : Type*) [CommGroup H] [Module (ZMod 3) (Additive H)] :
    Function.Injective (mulAutToLinHom H) := by
  intro g h hgh
  ext x
  have := congrArg (fun e : Additive H ≃ₗ[ZMod 3] Additive H => e (Additive.ofMul x)) hgh
  exact Additive.ofMul.injective this

theorem fuse_of_q8 {G : Type*} [Group G] (J F : Subgroup G)
    (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hexp : ∀ x ∈ F, x ^ 3 = 1)
    (hcard : Nat.card F = 9) (f : QuaternionGroup 2 →* autizer J F)
    (hf : Function.Injective f) :
    ∀ x ∈ F, x ≠ 1 → ∀ y ∈ F, y ≠ 1 →
      ∃ n ∈ J ⊓ Subgroup.normalizer (F : Set G), n * x * n⁻¹ = y := by
  classical
  let _ : CommGroup F :=
    { (inferInstance : Group F) with
      mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Finite (Additive F) := inferInstanceAs (Finite F)
  let _ : Module (ZMod 3) (Additive F) :=
    AddCommGroup.zmodModule (n := 3) fun x => by
      apply Additive.toMul.injective
      simpa [toMul_nsmul] using Subtype.ext (hexp x.toMul x.toMul.2)
  have hM : Nat.card (Additive F) = 9 := by
    rw [← hcard]; exact Nat.card_congr Additive.toMul
  let ρ : ↥(J ⊓ Subgroup.normalizer (F : Set G)) →* MulAut ↥F :=
    F.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right)
  have hker : ρ.ker ≤ (J ⊓ Subgroup.centralizer (F : Set G)).subgroupOf
      (J ⊓ Subgroup.normalizer (F : Set G)) := by
    intro n hn
    have h1 : (⟨n.1, n.2.2⟩ : Subgroup.normalizer (F : Set G)) ∈ F.normalizerMonoidHom.ker := hn
    rw [Subgroup.normalizerMonoidHom_ker] at h1
    exact ⟨n.2.1, h1⟩
  have hsub : (J ⊓ Subgroup.centralizer (F : Set G)).subgroupOf
      (J ⊓ Subgroup.normalizer (F : Set G)) ≤ ρ.ker := by
    intro n hn
    have h1 : (⟨n.1, n.2.2⟩ : Subgroup.normalizer (F : Set G)) ∈
        (Subgroup.centralizer (F : Set G)).subgroupOf (Subgroup.normalizer (F : Set G) :
          Subgroup G) := hn.2
    rw [← Subgroup.normalizerMonoidHom_ker] at h1
    exact h1
  let ρ' : autizer J F →* MulAut ↥F := QuotientGroup.lift _ ρ hsub
  have hρ' : Function.Injective ρ' := by
    rw [injective_iff_map_eq_one]
    intro z hz
    induction z using QuotientGroup.induction_on with
    | H n =>
      rw [QuotientGroup.eq_one_iff]
      exact hker (by simpa [ρ'] using hz)
  let Φ : QuaternionGroup 2 →* (Additive F ≃ₗ[ZMod 3] Additive F) :=
    (mulAutToLinHom F).comp (ρ'.comp f)
  have hΦ : Function.Injective Φ :=
    (mulAutToLinHom_injective F).comp (hρ'.comp hf)
  intro x hx hx1 y hy hy1
  obtain ⟨q, ⟨c, rfl⟩, hq⟩ := Sec6E.plane_q8_trans hM Φ hΦ
    (Additive.ofMul ⟨x, hx⟩) (Additive.ofMul ⟨y, hy⟩)
    (fun h => hx1 (congrArg Subtype.val (Additive.ofMul.injective h)))
    (fun h => hy1 (congrArg Subtype.val (Additive.ofMul.injective h)))
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (f c)
  refine ⟨n.1, n.2, ?_⟩
  have h1 : ρ n ⟨x, hx⟩ = ⟨y, hy⟩ := by
    have h2 : Φ c = mulAutToLin (ρ n) := by
      simp only [Φ, MonoidHom.comp_apply]
      rw [← hn]
      rfl
    rw [h2] at hq
    exact Additive.ofMul.injective hq
  exact congrArg Subtype.val h1

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
