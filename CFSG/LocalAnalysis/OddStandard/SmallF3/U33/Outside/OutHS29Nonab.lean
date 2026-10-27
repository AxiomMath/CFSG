module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutHS29Cent

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup
open scoped commutatorElement

variable {T : Type} [Group T] [Finite T] {ρ x : MulAut T}

private lemma comm_mem_center (hS : FpfSpecial T) (a b : T) : ⁅a, b⁆ ∈ center T := by
  simpa only [commutatorElement_def] using hS.comm_mem a b

private lemma commutator_eq_one_of_mem_center (hS : FpfSpecial T) {z : T} (hz : z ∈ center T)
    (b : T) : ⁅z, b⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz b).symm

private lemma commutator_eq_one_of_mem_center' (hS : FpfSpecial T) {z : T} (hz : z ∈ center T)
    (b : T) : ⁅b, z⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz b)

private lemma commutator_mul_right (hS : FpfSpecial T) (a b c : T) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have hcomm : ⁅a, c⁆ ∈ center T := comm_mem_center hS a c
  have h : b * ⁅a, c⁆ * b⁻¹ = ⁅a, c⁆ := by
    rw [Subgroup.mem_center_iff.mp hcomm b, mul_assoc, mul_inv_cancel, mul_one]
  rw [commutatorElement_mul_right_eq_mul_conj]
  calc ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by group
    _ = ⁅a, b⁆ * ⁅a, c⁆ := by rw [h]

private lemma commutator_mul_left (hS : FpfSpecial T) (a b c : T) :
    ⁅a * b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
  have hcomm : ⁅b, c⁆ ∈ center T := comm_mem_center hS b c
  have h : a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ := by
    rw [Subgroup.mem_center_iff.mp hcomm a, mul_assoc, mul_inv_cancel, mul_one]
  rw [commutatorElement_mul_left_eq_conj_mul]
  calc a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by rw [h]

private lemma commutator_inv_right (hS : FpfSpecial T) (a b : T) :
    ⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹ := by
  have hcomm : ⁅a, b⁻¹⁆ ∈ center T := comm_mem_center hS a b⁻¹
  have h : b * ⁅a, b⁻¹⁆ * b⁻¹ = ⁅a, b⁻¹⁆ := by
    rw [Subgroup.mem_center_iff.mp hcomm b, mul_assoc, mul_inv_cancel, mul_one]
  have h1 := commutatorElement_mul_right_eq_mul_conj a b b⁻¹
  rw [mul_inv_cancel, commutatorElement_one_right] at h1
  have h2 : (1 : T) = ⁅a, b⁆ * ⁅a, b⁻¹⁆ := by
    calc (1 : T) = ⁅a, b⁆ * b * ⁅a, b⁻¹⁆ * b⁻¹ := h1
      _ = ⁅a, b⁆ * (b * ⁅a, b⁻¹⁆ * b⁻¹) := by group
      _ = ⁅a, b⁆ * ⁅a, b⁻¹⁆ := by rw [h]
  exact eq_inv_of_mul_eq_one_right h2.symm

private lemma inv_eq_self_of_comm (hS : FpfSpecial T) (a b : T) : ⁅a, b⁆⁻¹ = ⁅a, b⁆ := by
  have hc : ⁅a, b⁆ ∈ center T := comm_mem_center hS a b
  have h2 : ⁅a, b⁆ * ⁅a, b⁆ = 1 := hS.sq_center ⁅a, b⁆ hc
  exact inv_eq_of_mul_eq_one_right h2

private lemma commutator_mul_center_left (hS : FpfSpecial T) {z : T} (hz : z ∈ center T)
    (w b : T) : ⁅w * z, b⁆ = ⁅w, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, commutator_eq_one_of_mem_center hS hz b,
    mul_one, mul_inv_cancel, one_mul]

private lemma commutator_center_mul_right (hS : FpfSpecial T) {z : T} (hz : z ∈ center T)
    (w b : T) : ⁅w, b * z⁆ = ⁅w, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, commutator_eq_one_of_mem_center' hS hz w, mul_one]
  group

private lemma fix_comm_rho (hS : FpfSpecial T) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : T, ρ g = g → g = 1) (hx : x * x = 1) (hxρ : x * ρ * x⁻¹ = ρ⁻¹)
    (hF : ∀ a ∈ fixSub x, ∀ b ∈ fixSub x, a * b = b * a) {f g : T}
    (hf : f ∈ fixSub x) (hg : g ∈ fixSub x) : x ⁅f, ρ g⁆ = ⁅f, ρ g⁆ := by
  have hxf : x f = f := hf
  have hxg : x g = g := hg
  have hxρ' : x * ρ = ρ⁻¹ * x := by
    calc x * ρ = (x * ρ * x⁻¹) * x := by group
      _ = ρ⁻¹ * x := by rw [hxρ]
  have hρ2 : ρ ^ 2 = ρ⁻¹ := by
    have h : ρ ^ 2 * ρ = 1 := by rw [← pow_succ, hρ]
    exact eq_inv_of_mul_eq_one_left h
  have hxρg : x (ρ g) = ρ (ρ g) := by
    calc x (ρ g) = (x * ρ) g := rfl
      _ = (ρ⁻¹ * x) g := by rw [hxρ']
      _ = ρ⁻¹ (x g) := rfl
      _ = ρ⁻¹ g := by rw [hxg]
      _ = ρ (ρ g) := by rw [← hρ2]; rfl
  have hburn : ρ (ρ g) = (g * ρ g)⁻¹ :=
    eq_inv_of_mul_eq_one_right (forall_mul_rho_rho_sq ρ hρ hfpf g)
  have hfg : ⁅f, g⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hF f hf g hg)
  calc x ⁅f, ρ g⁆ = ⁅x f, x (ρ g)⁆ := map_commutatorElement x f (ρ g)
    _ = ⁅f, ρ (ρ g)⁆ := by rw [hxf, hxρg]
    _ = ⁅f, (g * ρ g)⁻¹⁆ := by rw [hburn]
    _ = ⁅f, g * ρ g⁆⁻¹ := commutator_inv_right hS f (g * ρ g)
    _ = (⁅f, g⁆ * ⁅f, ρ g⁆)⁻¹ := by rw [commutator_mul_right hS f g (ρ g)]
    _ = (1 * ⁅f, ρ g⁆)⁻¹ := by rw [hfg]
    _ = ⁅f, ρ g⁆ := by rw [one_mul, inv_eq_self_of_comm hS f (ρ g)]

private lemma fix_comm_rho' (hS : FpfSpecial T) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : T, ρ g = g → g = 1) (hx : x * x = 1) (hxρ : x * ρ * x⁻¹ = ρ⁻¹)
    (hF : ∀ a ∈ fixSub x, ∀ b ∈ fixSub x, a * b = b * a) {f g : T}
    (hf : f ∈ fixSub x) (hg : g ∈ fixSub x) : x ⁅ρ f, g⁆ = ⁅ρ f, g⁆ := by
  have h1 : x ⁅g, ρ f⁆ = ⁅g, ρ f⁆ := fix_comm_rho hS hρ hfpf hx hxρ hF hg hf
  have hinv : ⁅ρ f, g⁆ = ⁅g, ρ f⁆ := by
    rw [← commutatorElement_inv (ρ f) g, inv_eq_self_of_comm hS (ρ f) g]
  rw [hinv]
  exact h1

private lemma expand_comm (hS : FpfSpecial T)
    (hF : ∀ a ∈ fixSub x, ∀ b ∈ fixSub x, a * b = b * a)
    {f₁ f₂ g₁ g₂ : T} (hf₁ : f₁ ∈ fixSub x) (hg₁ : g₁ ∈ fixSub x)
    (hf₂ : f₂ ∈ fixSub x) (hg₂ : g₂ ∈ fixSub x) :
    ⁅f₁ * ρ f₂, g₁ * ρ g₂⁆ = ⁅ρ f₂, g₁⁆ * ⁅f₁, ρ g₂⁆ := by
  have h11 : ⁅f₁, g₁⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hF f₁ hf₁ g₁ hg₁)
  have h22 : ⁅ρ f₂, ρ g₂⁆ = 1 := by
    have h : ⁅f₂, g₂⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hF f₂ hf₂ g₂ hg₂)
    rw [← map_commutatorElement (f := ρ), h, map_one]
  rw [commutator_mul_right hS (f₁ * ρ f₂) g₁ (ρ g₂),
    commutator_mul_left hS f₁ (ρ f₂) g₁,
    commutator_mul_left hS f₁ (ρ f₂) (ρ g₂), h11, h22]
  group

private lemma fix_comm (hS : FpfSpecial T) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : T, ρ g = g → g = 1) (hx : x * x = 1) (hxρ : x * ρ * x⁻¹ = ρ⁻¹)
    (hF : ∀ a ∈ fixSub x, ∀ b ∈ fixSub x, a * b = b * a) (a b : T) :
    x ⁅a, b⁆ = ⁅a, b⁆ := by
  obtain ⟨f₁, hf₁, f₂, hf₂, z, hz, ha⟩ := exists_decomp_fixSub hS hρ hfpf hx hxρ a
  obtain ⟨g₁, hg₁, g₂, hg₂, z', hz', hb⟩ := exists_decomp_fixSub hS hρ hfpf hx hxρ b
  rw [ha, hb,
    commutator_mul_center_left hS hz (f₁ * ρ f₂) (g₁ * ρ g₂ * z'),
    commutator_center_mul_right hS hz' (f₁ * ρ f₂) (g₁ * ρ g₂),
    expand_comm hS hF hf₁ hg₁ hf₂ hg₂,
    map_mul, fix_comm_rho' hS hρ hfpf hx hxρ hF hf₂ hg₁,
    fix_comm_rho hS hρ hfpf hx hxρ hF hf₁ hg₂]

theorem fixSub_nonabelian (hS : FpfSpecial T) (hρ : ρ ^ 3 = 1)
    (hfpf : ∀ g : T, ρ g = g → g = 1) (hx : x * x = 1) (hxρ : x * ρ * x⁻¹ = ρ⁻¹) :
    ∃ a ∈ fixSub x, ∃ b ∈ fixSub x, a * b ≠ b * a := by
  by_contra hcon
  push_neg at hcon
  have hZleF : center T ≤ fixSub x := by
    rw [← hS.commutator_eq, _root_.commutator_def]
    exact (Subgroup.commutator_le).mpr fun a _ b _ => fix_comm hS hρ hfpf hx hxρ hcon a b
  have hZeq : center T ⊓ fixSub x = center T := inf_eq_left.mpr hZleF
  have hcard : Nat.card ↥(center T ⊓ fixSub x) = 4 := by
    rw [hZeq]
    exact hS.card_center
  have h2 := card_center_inf_fix hS hρ hfpf hx hxρ
  omega

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
