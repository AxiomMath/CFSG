module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M3

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.Q8P

section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7F2
open CFSG.ClassicalInvolution.Asc77.T7F2
section Aux
variable {G : Type} [Group G] [Finite G]

open CFSG.ClassicalInvolution.Asc77.T7F2 in
theorem false_of_fusion_gen (U : Set G) (hG : ∀ f : G →* Multiplicative (ZMod 2),
      (∀ u ∈ U, f u = 1) → f = 1)
    (S : Sylow 2 G) (B : Subgroup G) (hB : B.relIndex (S : Subgroup G) = 2) (a : G)
    (haS : a ∈ (S : Subgroup G))
    (h1 : ∀ x : G, x⁻¹ * a * x ∈ (S : Subgroup G) → x⁻¹ * a * x ∉ B)
    (h2 : ∀ (i : ℕ) (x : G), x⁻¹ * a ^ (2 ^ (i + 1)) * x ∈ (S : Subgroup G) →
      x⁻¹ * a ^ (2 ^ (i + 1)) * x ∈ B)
    (hU : ∀ u ∈ U, u ∈ (S : Subgroup G) ∧
      (∀ x : G, x⁻¹ * u * x ∈ (S : Subgroup G) → x⁻¹ * u * x ∈ B) ∧
      (∀ (i : ℕ) (x : G), x⁻¹ * u ^ (2 ^ (i + 1)) * x ∈ (S : Subgroup G) →
        x⁻¹ * u ^ (2 ^ (i + 1)) * x ∈ B)) : False :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7F2.false_of_fusion_gen U hG S B hB a haS h1 h2 hU
end Aux
variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
namespace Hyp25T
open CFSG.ClassicalInvolution.Asc77.T7F2.Hyp25T
variable (h : Asc77.T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
include h
variable (h11 : Asc77.C25_11)
include h11
include h11
theorem conj_not_mem_B {a : G}
    (d : BData (S : Subgroup G) (Nsub S R) (Psub S R) (Psub S R') t' a)
    (ha : a ∈ Csub S R) (ha2 : a * a ≠ 1) {x : G} (hy : x⁻¹ * a * x ∈ (S : Subgroup G)) :
    x⁻¹ * a * x ∉ d.B :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7F2.Hyp25T.conj_not_mem_B h.toF
    (h11 G Ω K K' W S R R' z t u₁ u₂ h.hyp) d ha ha2 hy
theorem pow_conj_mem_B {a : G}
    (d : BData (S : Subgroup G) (Nsub S R) (Psub S R) (Psub S R') t' a)
    (ha : a ∈ Csub S R) (i : ℕ) {x : G}
    (hx : x⁻¹ * a ^ (2 ^ (i + 1)) * x ∈ (S : Subgroup G)) :
    x⁻¹ * a ^ (2 ^ (i + 1)) * x ∈ d.B :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7F2.Hyp25T.pow_conj_mem_B h.toF
    (h11 G Ω K K' W S R R' z t u₁ u₂ h.hyp) d ha i hx
theorem conj_mem_B_of_mem_R' {a : G}
    (d : BData (S : Subgroup G) (Nsub S R) (Psub S R) (Psub S R') t' a)
    {c : G} (hcpow : c ∈ R') {x : G} (hx : x⁻¹ * c * x ∈ (S : Subgroup G)) :
    x⁻¹ * c * x ∈ d.B :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7F2.Hyp25T.conj_mem_B_of_mem_R' h.toF
    (h11 G Ω K K' W S R R' z t u₁ u₂ h.hyp) d hcpow hx

theorem false_of_d8 (h16 : C25_16)
    (hlt : 2 * Nat.card ↥(R ⊔ R') < Nat.card ↥(Nsub S R)) : False := by
  obtain ⟨a, haC, haR', ha2⟩ := h.exists_a h11 h16 hlt
  have d := h.bdata h11 h16 hlt haC haR'
  refine false_of_fusion_gen (R' : Set G) (fun f hf => ?_) S d.B d.relIndex_B a
    (mem_Csub.mp haC).1 (fun x hx => h.conj_not_mem_B h11 d haC ha2 hx)
    (fun i x hx => h.pow_conj_mem_B h11 d haC i hx) (fun u hu => ⟨h.hR'S hu, fun x hx =>
      h.conj_mem_B_of_mem_R' h11 d hu hx, fun i x hx => h.conj_mem_B_of_mem_R' h11 d
        (R'.pow_mem hu _) hx⟩)
  exact T7C.hom_eq_one_of_sylow h.hs.stand h.hK' h.hR'syl f hf
end Hyp25T
end T7F2
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7G2
open CFSG.ClassicalInvolution.Asc77.T7G2
variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
section Swap
variable (hyp : Asc77.Hyp25 Ω K K' W S R R' z t u₁ u₂)
include hyp
theorem exists_swap_nonfused :
    ∃ t' ∈ (S : Subgroup G), t' * t' = 1 ∧ (∃ g : G, g * z * g⁻¹ = t') ∧ conjSub t' R = R' ∧
      ¬ ∃ y : G, y * z * y⁻¹ = t' * z :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7G2.exists_swap_nonfused hyp.toF
end Swap
end T7G2
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
theorem c25_17_norm_of_11_16 (h11 : C25_11) (h16 : C25_16) : C25_17_norm := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  obtain ⟨t', ht'S, ⟨g, hg⟩, hconj⟩ := c25_2_t_proved G Ω K K' W S R R' z t u₁ u₂ hyp
  have hzz : z * z = 1 := hyp.std.setting.hz.sq
  have ht'2 : t' * t' = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have h : T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t' := ⟨hyp, ht'S, ht'2, hconj⟩
  by_contra hlt
  push Not at hlt
  exact h.false_of_d8 h11 h16 hlt
theorem c25_17_idx_of_11_16 (h11 : C25_11) (h16 : C25_16) : C25_17_idx :=
  c25_17_idx_of_norm (c25_17_norm_of_11_16 h11 h16)
end Asc77
end
end CFSG.ClassicalInvolution.Q8P
