module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF07
public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF06x
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngB

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77
namespace S24B
namespace Ctx8Frame

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

include C in
theorem exists_centralizes_r {y : G} (hyS : y ∈ (S : Subgroup G)) (hT : S24B.TrivMu Ω W y)
    (hinv : ∀ w ∈ W, y * w * y⁻¹ = w⁻¹) :
    ∃ k : ℤ, (y * C.D.x₃ ^ k) * C.D.F.ρ.r = C.D.F.ρ.r * (y * C.D.x₃ ^ k) := by
  have hyN := C.le_normalizer_W hyS
  have hK : conjSub y K = K := by
    have h := C.fix_of_trivMu hyN hT C.D.F.ρ
    rwa [C.hK] at h
  have hyr : y * C.D.F.ρ.r * y⁻¹ ∈ R := by
    refine (le_of_eq C.inf_S_eq_R) ⟨?_, S.mul_mem (S.mul_mem hyS (C.hd.hR.2.2 C.r_mem_R))
      (S.inv_mem hyS)⟩
    have h := conj_mem_conjSub (n := y) C.r_mem_K
    rwa [hK] at h
  have hU : Subgroup.zpowers C.D.x₁ ≤ R := Subgroup.zpowers_le.mpr C.x₁_mem_R
  have hinv' := inv_conj_of_inv hinv
  have hyrU : y * C.D.F.ρ.r * y⁻¹ ∉ Subgroup.zpowers C.D.x₁ := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply C.r_not_mem_zpowers
    have e : C.D.F.ρ.r = y⁻¹ * (y * C.D.F.ρ.r * y⁻¹) * y := by group
    rw [e, ← hk, hinv' _ (W.zpow_mem C.D.x₁_mem k)]
    exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers _ _)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (Thompson.inv_mul_mem_of_card_eq_two_mul hU C.card_R C.r_mem_R hyr C.r_not_mem_zpowers hyrU)
  refine ⟨k, ?_⟩
  have hyrk : y * C.D.F.ρ.r * y⁻¹ = C.D.F.ρ.r * C.D.x₁ ^ k := by rw [hk]; group
  have h1 := C.conj_x₃_zpow_r k
  have h2 : y * C.D.x₁ ^ (-k) * y⁻¹ = C.D.x₁ ^ k := by
    rw [hinv _ (W.zpow_mem C.D.x₁_mem _), zpow_neg, inv_inv]
  have h4 : C.D.x₁ ^ k * C.D.F.ρ.r = C.D.F.ρ.r * C.D.x₁ ^ (-k) := by
    have h3 := C.r_mul_x₁_zpow (-k)
    rw [neg_neg] at h3
    exact h3.symm
  have e : (y * C.D.x₃ ^ k) * C.D.F.ρ.r * (y * C.D.x₃ ^ k)⁻¹ = C.D.F.ρ.r := by
    calc (y * C.D.x₃ ^ k) * C.D.F.ρ.r * (y * C.D.x₃ ^ k)⁻¹
        = y * (C.D.x₃ ^ k * C.D.F.ρ.r * (C.D.x₃ ^ k)⁻¹) * y⁻¹ := by group
      _ = y * (C.D.x₁ ^ (-k) * C.D.F.ρ.r) * y⁻¹ := by rw [h1]
      _ = (y * C.D.x₁ ^ (-k) * y⁻¹) * (y * C.D.F.ρ.r * y⁻¹) := by group
      _ = C.D.x₁ ^ k * C.D.F.ρ.r * C.D.x₁ ^ k := by rw [h2, hyrk]; group
      _ = C.D.F.ρ.r * C.D.x₁ ^ (-k) * C.D.x₁ ^ k := by rw [h4]
      _ = C.D.F.ρ.r := by rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  calc (y * C.D.x₃ ^ k) * C.D.F.ρ.r
      = (y * C.D.x₃ ^ k) * C.D.F.ρ.r * (y * C.D.x₃ ^ k)⁻¹ * (y * C.D.x₃ ^ k) := by group
    _ = C.D.F.ρ.r * (y * C.D.x₃ ^ k) := by rw [e]

include C in
theorem conj_mem_sZero {s x : G} (hs : s ∈ (S : Subgroup G)) (hx : x ∈ sZero Ω W S) :
    s * x * s⁻¹ ∈ sZero Ω W S := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24.conj_mem_sZero_of (fun hs' => C.le_normalizer_W hs')
    (fun hsN => Ctx8Frame.le_normalizer_MGrp C.D.c.hΩ hsN) hs hx

include C in
theorem mem_or_inv_mul_mem_sZero {c y : G} (hcS : c ∈ (S : Subgroup G))
    (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) (hyS : y ∈ (S : Subgroup G)) :
    y ∈ sZero Ω W S ∨ c⁻¹ * y ∈ sZero Ω W S := by
  obtain ⟨x, hxP, t, htS, hT, rfl⟩ := C.exists_decomp hyS
  rcases acts_pm C htS hT with ht | ht
  · left
    refine ⟨S.mul_mem hxP.1 htS, x, hxP.2, fun w hw => ?_⟩
    calc x * t * w * (x * t)⁻¹ = x * (t * w * t⁻¹) * x⁻¹ := by group
      _ = x * w * x⁻¹ := by rw [ht w hw]
  · right
    have hcinv := inv_conj_of_inv hinv
    refine ⟨S.mul_mem (S.inv_mem hcS) (S.mul_mem hxP.1 htS), x, hxP.2, fun w hw => ?_⟩
    have hxN := C.le_normalizer_W hxP.1
    have hxw : x * w * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hxN w).mp hw
    calc c⁻¹ * (x * t) * w * (c⁻¹ * (x * t))⁻¹ = c⁻¹ * (x * (t * w * t⁻¹) * x⁻¹) * c := by group
      _ = c⁻¹ * (x * w⁻¹ * x⁻¹) * c := by rw [ht w hw]
      _ = c⁻¹ * (x * w * x⁻¹)⁻¹ * c := by group
      _ = (x * w * x⁻¹)⁻¹⁻¹ := hcinv _ (W.inv_mem hxw)
      _ = x * w * x⁻¹ := inv_inv _

include C in
theorem commutator_mem_sZero {c : G} (hcS : c ∈ (S : Subgroup G))
    (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) :
    ∀ y₁ ∈ (S : Subgroup G), ∀ y₂ ∈ (S : Subgroup G), y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ sZero Ω W S := by
  intro y₁ hy₁ y₂ hy₂
  have hnorm : ∀ s ∈ (S : Subgroup G), ∀ x ∈ sZero Ω W S, s * x * s⁻¹ ∈ sZero Ω W S :=
    fun s hs x hx => conj_mem_sZero C hs hx
  rcases mem_or_inv_mul_mem_sZero C hcS hinv hy₁ with h₁ | h₁ <;>
    rcases mem_or_inv_mul_mem_sZero C hcS hinv hy₂ with h₂ | h₂
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
      (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)
  · have h := hnorm y₂ hy₂ _ (Subgroup.inv_mem _ h₁)
    have e : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ = y₁ * (y₂ * y₁⁻¹ * y₂⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ h₁ h
  · exact Subgroup.mul_mem _ (hnorm y₁ hy₁ y₂ h₂) (Subgroup.inv_mem _ h₂)
  · have hb : y₁⁻¹ * y₂ ∈ sZero Ω W S := by
      have e : y₁⁻¹ * y₂ = (c⁻¹ * y₁)⁻¹ * (c⁻¹ * y₂) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h₁) h₂
    have h3 := hnorm y₁ hy₁ _
      (Subgroup.mul_mem _ (hnorm y₁ hy₁ _ hb) (Subgroup.inv_mem _ hb))
    have e : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ =
        y₁ * (y₁ * (y₁⁻¹ * y₂) * y₁⁻¹ * (y₁⁻¹ * y₂)⁻¹) * y₁⁻¹ := by group
    rw [e]
    exact h3

end

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

theorem mem_Dg_of_lam {a : G} (ha : a ∈ C.A)
    (h : (C.lam ⟨a, ha⟩ : G) = 1 ∨ (C.lam ⟨a, ha⟩ : G) = z) :
    a ∈ C.Dg ∨ a * C.D.x₂⁻¹ ∈ C.Dg := by
  rcases h with h | h
  · exact Or.inl ((C.lam_eq_one_iff ⟨a, ha⟩).mp (Subtype.ext h))
  · right
    have hmem : a * C.D.x₂⁻¹ ∈ C.A := C.A.mul_mem ha (C.A.inv_mem C.x₂_mem_A)
    refine (C.lam_eq_one_iff ⟨_, hmem⟩).mp (Subtype.ext ?_)
    have e : (⟨a * C.D.x₂⁻¹, hmem⟩ : ↥C.A) = ⟨a, ha⟩ * (⟨C.D.x₂, C.x₂_mem_A⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
    rw [h, C.lam_x₂, mul_inv_cancel]

end
end Ctx8Frame
end S24B
end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8
