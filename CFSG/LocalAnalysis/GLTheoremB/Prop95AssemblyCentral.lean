module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly

open CFSG.Open
open scoped commutatorElement

section Central

variable {X Y : Type*} [Group X] [Group Y]

theorem mem_center_of_image_mem_center {f : X →* Y} (hperf : commutator X = ⊤)
    (hker : ∀ x ∈ f.ker, x ∈ Subgroup.center X) {x : X} (hx : f x ∈ Subgroup.center Y) :
    x ∈ Subgroup.center X := by
  have hc : ∀ y : X, ⁅x, y⁆ ∈ Subgroup.center X := by
    intro y
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hx (f y)).symm
  have key : ∀ a b : X, ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅x, b⁆ := by
    intro a b
    have h := Subgroup.mem_center_iff.1 (hc b) a
    simp only [commutatorElement_def] at h ⊢
    have h2 : a⁻¹ * (x * b * x⁻¹ * b⁻¹) = (x * b * x⁻¹ * b⁻¹) * a⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h, mul_inv_cancel_right]
    calc x * (a * b) * x⁻¹ * (a * b)⁻¹
        = x * a * x⁻¹ * ((x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
      _ = x * a * x⁻¹ * (a⁻¹ * (x * b * x⁻¹ * b⁻¹)) := by rw [h2]
      _ = x * a * x⁻¹ * a⁻¹ * (x * b * x⁻¹ * b⁻¹) := by group
  let φ : X →* ↥(Subgroup.center X) :=
    MonoidHom.mk' (fun y => (⟨⁅x, y⁆, hc y⟩ : ↥(Subgroup.center X)))
      (by
        intro a b
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        exact key a b)
  have hφc : ∀ a b : X, φ (⁅a, b⁆) = 1 := by
    intro a b
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, φ, MonoidHom.mk'_apply]
    exact Subgroup.mem_center_iff.1 (hc b) ⁅x, a⁆
  have hle : ⁅(⊤ : Subgroup X), ⊤⁆ ≤ φ.ker :=
    Subgroup.commutator_le.2 fun a _ b _ => MonoidHom.mem_ker.2 (hφc a b)
  have htop : (⊤ : Subgroup X) ≤ φ.ker := by
    rw [← hperf]
    exact hle
  have hy : ∀ y : X, ⁅x, y⁆ = 1 := by
    intro y
    have h1 : φ y = 1 := MonoidHom.mem_ker.1 (htop (Subgroup.mem_top y))
    exact congrArg Subtype.val h1
  exact Subgroup.mem_center_iff.2 fun g => (commutatorElement_eq_one_iff_mul_comm.1 (hy g)).symm

theorem isQuasisimple_of_central_quotient {f : X →* Y} (hsurj : Function.Surjective f)
    (hperf : commutator X = ⊤) (hker : ∀ x ∈ f.ker, x ∈ Subgroup.center X)
    (hY : CFSG.Open.IsQuasisimple Y) : CFSG.Open.IsQuasisimple X := by
  let φ : X →* Y ⧸ Subgroup.center Y := (QuotientGroup.mk' (Subgroup.center Y)).comp f
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hsurj
  have hφk : φ.ker = Subgroup.center X := by
    ext x
    simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact mem_center_of_image_mem_center hperf hker hx
    · intro hx
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := hsurj g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
  let e : X ⧸ φ.ker ≃* Y ⧸ Subgroup.center Y := QuotientGroup.quotientKerEquivOfSurjective φ hφs
  let e1 : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y :=
    (QuotientGroup.quotientMulEquivOfEq hφk).symm.trans e
  exact ⟨hperf, e1.isSimpleGroup_congr.2 hY.2⟩

end Central

end CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly
