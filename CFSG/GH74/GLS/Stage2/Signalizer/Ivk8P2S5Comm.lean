module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Gen
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.Bender.Thm2
open scoped commutatorElement

section Comm

variable {G : Type} [Group G]

theorem commutator_conj_mem {H K : Subgroup G} {c : G} (hc : c ∈ H) :
    ∀ y ∈ ⁅H, K⁆, c * y * c⁻¹ ∈ ⁅H, K⁆ := by
  intro y hy
  rw [Subgroup.commutator_def] at hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hx
    have e : c * ⁅g₁, g₂⁆ * c⁻¹ = ⁅c * g₁, g₂⁆ * ⁅c, g₂⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (H.mul_mem hc hg₁) hg₂)
      (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hc hg₂))
  | one => simp
  | mul x y _ _ hx hy =>
    have e : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem commutator_zpowers_le {H : Subgroup G} {z : G} (hz : z ∈ H) : ⁅H, zpowers z⁆ ≤ H := by
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  have hyH : y ∈ H := (Subgroup.zpowers_le.2 hz) hy
  have : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
  rw [this]
  exact H.mul_mem hx (H.mul_mem (H.mul_mem hyH (H.inv_mem hx)) (H.inv_mem hyH))

theorem le_normalizer_commutator [Finite G] {H K : Subgroup G} :
    H ≤ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := fun _ hc =>
  mem_normalizer_of_forall_conj (commutator_conj_mem hc)

theorem zpow_one_or_self_of_mul_self {z : G} (hz2 : z * z = 1) (n : ℤ) : z ^ n = 1 ∨ z ^ n = z := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  induction n using Int.induction_on with
  | zero => exact Or.inl (zpow_zero z)
  | succ n ih =>
    rw [zpow_add_one]
    rcases ih with h | h
    · rw [h, one_mul]
      exact Or.inr rfl
    · rw [h, hz2]
      exact Or.inl rfl
  | pred n ih =>
    rw [zpow_sub_one, hzi]
    rcases ih with h | h
    · rw [h, one_mul]
      exact Or.inr rfl
    · rw [h, hz2]
      exact Or.inl rfl

theorem commutator_zpowers_self_mem {H : Subgroup G} {z : G} (hz2 : z * z = 1)
    (hzN : z ∈ normalizer (H : Set G)) {x : G} (hx : x ∈ H) (n : ℤ) : ⁅x, z ^ n⁆ ∈ H := by
  rcases zpow_one_or_self_of_mul_self hz2 n with h | h
  · rw [h]
    simp
  · rw [h]
    have : ⁅x, z⁆ = x * (z * x⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact H.mul_mem hx ((Subgroup.mem_normalizer_iff.1 hzN x⁻¹).1 (H.inv_mem hx))

end Comm

section Layer

variable {G : Type} [Group G]

theorem le_Em_of_isCompIn {H J : Subgroup G} (hJ : IsCompIn H J) : J ≤ Em H := by
  rw [Em_def]
  obtain ⟨hJH, hJc⟩ := hJ
  have hsub : (J.subgroupOf H).map H.subtype = J := Subgroup.map_subgroupOf_eq_of_le hJH
  rw [← hsub]
  exact Subgroup.map_mono (le_sSup hJc)

theorem Em_le_of_forall_comp {H T : Subgroup G} (h : ∀ J, IsCompIn H J → J ≤ T) : Em H ≤ T := by
  rw [Em_def, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hsub : (K.map H.subtype).subgroupOf H = K :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective K
  exact h (K.map H.subtype) ⟨Subgroup.map_subtype_le K, by rw [hsub]; exact hK⟩

end Layer

section Fpf

variable {G : Type} [Group G] [Finite G]

theorem odd_orderOf_of_fpf {F : Subgroup G} {z : G} (hinv : ∀ f ∈ F, z * f * z⁻¹ = f⁻¹)
    (hfpf : ∀ f ∈ F, z * f = f * z → f = 1) {f : G} (hf : f ∈ F) : Odd (orderOf f) := by
  by_contra hne
  obtain ⟨m, hm⟩ := Nat.not_odd_iff_even.1 hne
  have hpos : 0 < orderOf f := orderOf_pos f
  have h2 : 2 ∣ orderOf f := ⟨m, by omega⟩
  have hu : orderOf (f ^ (orderOf f / 2)) = 2 := orderOf_pow_orderOf_div hpos.ne' h2
  have huF : f ^ (orderOf f / 2) ∈ F := Subgroup.pow_mem _ hf _
  have hu2 : f ^ (orderOf f / 2) * f ^ (orderOf f / 2) = 1 := by
    have : (f ^ (orderOf f / 2)) ^ orderOf (f ^ (orderOf f / 2)) = 1 := pow_orderOf_eq_one _
    rw [hu] at this
    simpa [pow_two] using this
  have hcomm : z * f ^ (orderOf f / 2) = f ^ (orderOf f / 2) * z := by
    have h1 := hinv _ huF
    rw [inv_eq_of_mul_eq_one_right hu2] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  have := hfpf _ huF hcomm
  rw [this, orderOf_one] at hu
  omega

end Fpf

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
