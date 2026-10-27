module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutHS29Lift

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup

variable {T : Type} [Group T] [Finite T] {ρ x : MulAut T}

private noncomputable def fixSubQuotHom (x : MulAut T) :
    ↥(fixSub x) →* T ⧸ center T :=
  (QuotientGroup.mk' (center T)).comp (fixSub x).subtype

private theorem fixSubQuotHom_apply (x : MulAut T) (g : ↥(fixSub x)) :
    fixSubQuotHom x g = QuotientGroup.mk g.1 := rfl

theorem card_fixSub (hS : FpfSpecial T) (hρ : ρ ^ 3 = 1) (hfpf : ∀ g : T, ρ g = g → g = 1)
    (hx : x * x = 1) (hxρ : x * ρ * x⁻¹ = ρ⁻¹) : Nat.card ↥(fixSub x) = 8 := by
  have hker : Nat.card ↥((fixSubQuotHom x).ker) = 2 := by
    have hEq : (fixSubQuotHom x).ker = (center T ⊓ fixSub x).subgroupOf (fixSub x) := by
      ext g
      rw [MonoidHom.mem_ker, fixSubQuotHom_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨h, g.2⟩, fun h => h.1⟩
    rw [hEq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := center T ⊓ fixSub x)
        (K := fixSub x) inf_le_right).toEquiv]
    exact card_center_inf_fix hS hρ hfpf hx hxρ
  have hrange : (fixSubQuotHom x).range = fixSub (centerAut x) := by
    ext v
    rw [MonoidHom.mem_range, mem_fixSub]
    constructor
    · rintro ⟨g, rfl⟩
      rw [fixSubQuotHom_apply, centerAut_mk, g.2]
    · intro hv
      obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective v
      have hgx : centerAut x (QuotientGroup.mk g) = QuotientGroup.mk g := by
        rw [hg]; exact hv
      obtain ⟨g', hg'x, hg'⟩ := exists_lift_fix hS hρ hfpf hx hxρ hgx
      refine ⟨⟨g', hg'x⟩, ?_⟩
      rw [fixSubQuotHom_apply, hg', hg]
  have hcard := card_ker_mul_card_range (fixSubQuotHom x)
  rw [hker, hrange, card_fix_quot hS hρ hfpf hx hxρ] at hcard
  norm_num at hcard
  exact hcard.symm

theorem exists_decomp_fixSub (hS : FpfSpecial T) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : T, ρ g = g → g = 1) (hx : x * x = 1) (hxρ : x * ρ * x⁻¹ = ρ⁻¹) (a : T) :
    ∃ f₁ ∈ fixSub x, ∃ f₂ ∈ fixSub x, ∃ z ∈ center T, a = f₁ * ρ f₂ * z := by
  have hρ' : centerAut ρ ^ 3 = 1 := by rw [← centerAut_pow, hρ, centerAut_one]
  have hfpf' : ∀ v : T ⧸ center T, centerAut ρ v = v → v = 1 :=
    centerAut_fpf ρ hρ hfpf
  have hx' : centerAut x * centerAut x = 1 := by rw [← centerAut_mul, hx, centerAut_one]
  have hxρ' : centerAut x * centerAut ρ * (centerAut x)⁻¹ = (centerAut ρ)⁻¹ := by
    rw [← centerAut_mul, ← centerAut_inv, ← centerAut_mul, hxρ, centerAut_inv]
  have hN2 : ∀ n ∈ (⊤ : Subgroup (T ⧸ center T)), n * n = 1 := by
    intro n _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective n
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hS.sq_mem g
  have hNρ : ∀ n ∈ (⊤ : Subgroup (T ⧸ center T)), centerAut ρ n ∈ ⊤ :=
    fun _ _ => Subgroup.mem_top _
  have hNx : ∀ n ∈ (⊤ : Subgroup (T ⧸ center T)), centerAut x n ∈ ⊤ :=
    fun _ _ => Subgroup.mem_top _
  obtain ⟨c₁, c₂, -, -, hx₁, hx₂, heq⟩ :=
    exists_decomp_fix (T := T ⧸ center T) (ρ := centerAut ρ) (x := centerAut x)
      (N := ⊤) hN2 hNρ hNx hρ' hfpf' hx' hxρ' (n := QuotientGroup.mk a) (Subgroup.mem_top _)
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective c₁
  obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective c₂
  obtain ⟨f₁, hf₁x, hf₁⟩ := exists_lift_fix hS hρ hfpf hx hxρ hx₁
  obtain ⟨f₂, hf₂x, hf₂⟩ := exists_lift_fix hS hρ hfpf hx hxρ hx₂
  refine ⟨f₁, hf₁x, f₂, hf₂x, (f₁ * ρ f₂)⁻¹ * a, ?_, ?_⟩
  · rw [← QuotientGroup.eq_one_iff ((f₁ * ρ f₂)⁻¹ * a), QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
    have hmk : (QuotientGroup.mk a : T ⧸ center T) = QuotientGroup.mk (f₁ * ρ f₂) := by
      rw [heq, ← hf₁, ← hf₂, centerAut_mk, ← QuotientGroup.mk_mul]
    rw [hmk, inv_mul_cancel]
  · group

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
