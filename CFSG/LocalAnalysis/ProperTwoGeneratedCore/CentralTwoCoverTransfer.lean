module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.ProperTwoGeneratedCore.CentralTwoCover

open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

theorem mem_commutator_of_mem_center_of_perfect (hperf : commutator G = ⊤) (P : Sylow p G)
    {z : G} (hz : z ∈ Subgroup.center G) (hzP : z ∈ (P : Subgroup G)) :
    (⟨z, hzP⟩ : (P : Subgroup G)) ∈ commutator (P : Subgroup G) := by
  classical
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup G) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ Subgroup.center G := Subgroup.pow_mem _ hz k
    rw [Subgroup.mem_center_iff.mp hzk g₀⁻¹, inv_mul_cancel_right]
  let φ : (P : Subgroup G) →* Abelianization (P : Subgroup G) := Abelianization.of
  have htr := MonoidHom.transfer_eq_pow φ z key
  have htriv : φ.transfer z = 1 := by
    have hker := Abelianization.commutator_subset_ker (φ.transfer (H := (P : Subgroup G)))
    rw [hperf] at hker
    exact MonoidHom.mem_ker.mp (hker (Subgroup.mem_top z))
  rw [htriv] at htr
  have hpow : (⟨z, hzP⟩ : (P : Subgroup G)) ^ (P : Subgroup G).index ∈
      commutator (P : Subgroup G) := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    have heq : (⟨z, hzP⟩ : (P : Subgroup G)) ^ (P : Subgroup G).index =
        ⟨z ^ (P : Subgroup G).index, MonoidHom.transfer_eq_pow_aux z key⟩ :=
      Subtype.ext (by simp)
    rw [heq]
    exact htr.symm
  have hcop : Nat.Coprime p (P : Subgroup G).index :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).mpr P.not_dvd_index
  have hgcd : ((P : Subgroup G).index).gcd (orderOf (⟨z, hzP⟩ : (P : Subgroup G))) = 1 :=
    (P.isPGroup'.orderOf_coprime hcop _).symm
  exact (Subgroup.zpowers_le.mpr hpow) (mem_zpowers_pow_iff.mpr hgcd)

theorem mem_commutator_sylow_of_mem_center_of_perfect (hperf : commutator G = ⊤)
    (P : Sylow p G) {z : G} (hz : z ∈ Subgroup.center G) (hzP : z ∈ (P : Subgroup G)) :
    z ∈ ⁅(P : Subgroup G), (P : Subgroup G)⁆ := by
  have h := mem_commutator_of_mem_center_of_perfect hperf P hz hzP
  have hmap := Subgroup.mem_map_of_mem (P : Subgroup G).subtype h
  rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at hmap

theorem eq_bot_of_inf_commutator_eq_bot_of_perfect (hperf : commutator G = ⊤)
    (P : Sylow p G) {Z : Subgroup G} (hZ : Z ≤ Subgroup.center G) (hZP : Z ≤ P)
    (hinf : Z ⊓ ⁅(P : Subgroup G), (P : Subgroup G)⁆ = ⊥) : Z = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [← hinf]
  exact ⟨hz, mem_commutator_sylow_of_mem_center_of_perfect hperf P (hZ hz) (hZP hz)⟩

omit [Finite G] in
theorem commutatorElement_central_mul_left {z : G} (hz : ∀ g : G, g * z = z * g) (a b : G) :
    ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have h : z * a * b * (z * a)⁻¹ = a * b * a⁻¹ := by
    calc z * a * b * (z * a)⁻¹ = z * (a * b * a⁻¹) * z⁻¹ := by group
      _ = a * b * a⁻¹ := by rw [← hz, mul_inv_cancel_right]
  simp only [commutatorElement_def, h]

omit [Finite G] in
theorem commutatorElement_central_mul_right {z : G} (hz : ∀ g : G, g * z = z * g) (a b : G) :
    ⁅a, z * b⁆ = ⁅a, b⁆ := by
  have h1 : a * (z * b) = z * (a * b) := by rw [← mul_assoc, hz a, mul_assoc]
  rw [commutatorElement_def, h1, mul_inv_rev]
  calc z * (a * b) * a⁻¹ * (b⁻¹ * z⁻¹) = z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [← hz, mul_inv_cancel_right]
    _ = ⁅a, b⁆ := (commutatorElement_def a b).symm

theorem eq_bot_of_complement_of_perfect (hperf : commutator G = ⊤) (P : Sylow p G)
    {Z P₁ : Subgroup G} (hZ : Z ≤ Subgroup.center G) (hZP : Z ≤ P)
    (hdec : ∀ x ∈ (P : Subgroup G), ∃ z ∈ Z, ∃ y ∈ P₁, x = z * y) (hinf : Z ⊓ P₁ = ⊥) :
    Z = ⊥ := by
  refine eq_bot_of_inf_commutator_eq_bot_of_perfect hperf P hZ hZP ?_
  have hle : ⁅(P : Subgroup G), (P : Subgroup G)⁆ ≤ P₁ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨z₁, hz₁, y₁, hy₁, rfl⟩ := hdec a ha
    obtain ⟨z₂, hz₂, y₂, hy₂, rfl⟩ := hdec b hb
    rw [commutatorElement_central_mul_left (Subgroup.mem_center_iff.mp (hZ hz₁)),
      commutatorElement_central_mul_right (Subgroup.mem_center_iff.mp (hZ hz₂)),
      commutatorElement_def]
    exact P₁.mul_mem (P₁.mul_mem (P₁.mul_mem hy₁ hy₂) (P₁.inv_mem hy₁)) (P₁.inv_mem hy₂)
  exact eq_bot_iff.mpr fun x hx => hinf ▸ ⟨hx.1, hle hx.2⟩

theorem central_pSubgroup_eq_bot_of_perfect (hperf : commutator G = ⊤) (P : Sylow p G)
    {Z : Subgroup G} (hZ : Z ≤ Subgroup.center G) (hZP : Z ≤ P)
    (hP : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a) : Z = ⊥ := by
  refine eq_bot_of_inf_commutator_eq_bot_of_perfect hperf P hZ hZP ?_
  have hbot : ⁅(P : Subgroup G), (P : Subgroup G)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hP a ha b hb
  rw [hbot, inf_bot_eq]

end CFSG.ProperTwoGeneratedCore.CentralTwoCover
