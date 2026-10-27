module

public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87AltOrb

public section

open Subgroup CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoVacFix

theorem exists_stable_sylow {Y : Type} [Group Y] [Finite Y] (α : MulAut Y) (hα : α * α = 1) :
    ∃ Q : Sylow 2 Y, ∀ x ∈ (Q : Subgroup Y), α x ∈ (Q : Subgroup Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Set.univ : Set (Sylow 2 Y)).ncard := by
    rw [Set.ncard_univ]
    have h : Nat.card (Sylow 2 Y) % 2 = 1 % 2 := card_sylow_modEq_one 2 Y
    exact Nat.odd_iff.mpr (by omega)
  obtain ⟨Q, -, hQ⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltOrb.exists_fixed_of_odd
    (S := (Set.univ : Set (Sylow 2 Y))) (Set.toFinite _) (σ := fun Q => α • Q)
    (fun Q => show α • α • Q = Q by rw [← mul_smul, hα, one_smul]) (fun b _ => Set.mem_univ _) hodd
  refine ⟨Q, fun x hx => ?_⟩
  have hQ' : α • Q = Q := hQ
  have h1 : ((α • Q : Sylow 2 Y) : Subgroup Y) = (Q : Subgroup Y) := by
    rw [hQ']
  rw [Sylow.pointwise_smul_def] at h1
  rw [← h1]
  exact Subgroup.smul_mem_pointwise_smul x α _ hx

theorem exists_fixed_subgroup_card_sq {Y : Type} [Group Y] [Finite Y] (α : MulAut Y)
    (hα : ∀ y, α (α y) = y) {Z : Subgroup Y} (hsq : ∀ z ∈ Z, z * z = 1)
    (hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZ : ∀ z ∈ Z, α z ∈ Z) :
    ∃ T : Subgroup Y, T ≤ Z ∧ (∀ t ∈ T, α t = t) ∧ Nat.card Z ≤ Nat.card T ^ 2 := by
  let N : ↥Z →* ↥Z := MonoidHom.mk' (fun z => ⟨(z : Y) * α z, Z.mul_mem z.2 (hZ z z.2)⟩) (by
    intro a b
    apply Subtype.ext
    have hba : (b : Y) * α a = α a * b := hcomm b b.2 (α a) (hZ a a.2)
    show (a : Y) * b * α (a * b) = (a * α a) * (b * α b)
    rw [map_mul]
    calc (a : Y) * b * (α a * α b) = a * (b * α a) * α b := by group
      _ = a * (α a * b) * α b := by rw [hba]
      _ = (a * α a) * (b * α b) := by group)
  have hN : ∀ z : ↥Z, ((N z : ↥Z) : Y) = (z : Y) * α z := fun z => rfl
  refine ⟨N.ker.map Z.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro t ht
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ht
    have h1 : N z = 1 := hz
    have h2 : (z : Y) * α z = 1 := by
      have := congrArg Subtype.val h1
      rw [hN] at this
      exact this
    show α (z : Y) = z
    calc α (z : Y) = (z : Y)⁻¹ * ((z : Y) * α z) := by group
      _ = (z : Y)⁻¹ := by rw [h2, mul_one]
      _ = z := inv_eq_of_mul_eq_one_right (hsq z z.2)
  · have hk : Nat.card ↥(N.ker.map Z.subtype) = Nat.card N.ker :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective Z)
    rw [hk]
    have h1 := Subgroup.card_ker_mul_card_range N
    have hrk : N.range ≤ N.ker := by
      rintro w ⟨z, rfl⟩
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show ((z : Y) * α z) * α ((z : Y) * α z) = 1
      rw [map_mul, hα]
      have hzz := hsq (α z) (hZ z z.2)
      calc (z : Y) * α z * (α z * z) = z * (α z * α z) * z := by group
        _ = 1 := by rw [hzz, mul_one]; exact hsq z z.2
    have h2 : Nat.card N.range ≤ Nat.card N.ker := Subgroup.card_le_of_le hrk
    calc Nat.card ↥Z = Nat.card N.ker * Nat.card N.range := h1.symm
      _ ≤ Nat.card N.ker * Nat.card N.ker := Nat.mul_le_mul_left _ h2
      _ = Nat.card N.ker ^ 2 := (sq _).symm

theorem exists_fixed_four_group {Y : Type} [Group Y] [Finite Y] {n i : ℕ}
    (hn : 3 ≤ n) (hB : CFSG.GH74.Uniqueness.Bender.BenderType Y n i 1) (α : MulAut Y) (hα : α * α = 1) :
    ∃ T : Subgroup Y, 4 ≤ Nat.card ↥T ∧ (∀ t ∈ T, t * t = 1) ∧ (∀ t ∈ T, α t = t) := by
  have hα' : ∀ y, α (α y) = y := fun y => by
    have := congrArg (fun f : MulAut Y => f y) hα
    simpa using this
  obtain ⟨Q, hQ⟩ := exists_stable_sylow α hα
  obtain ⟨t, hc⟩ := hB.exists_benderCore Q
  have hsq : ∀ z ∈ rootCenter (Q : Subgroup Y), z * z = 1 := hc.center_sq
  have hcard : Nat.card (rootCenter (Q : Subgroup Y)) = 2 ^ n := hc.card_center
  have hcomm : ∀ a ∈ rootCenter (Q : Subgroup Y), ∀ b ∈ rootCenter (Q : Subgroup Y),
      a * b = b * a := fun a ha b hb =>
    (mem_rootCenter_iff.mp hb).2 a (mem_rootCenter_iff.mp ha).1
  have hZ : ∀ z ∈ rootCenter (Q : Subgroup Y), α z ∈ rootCenter (Q : Subgroup Y) := by
    intro z hz
    obtain ⟨hzQ, hzc⟩ := mem_rootCenter_iff.mp hz
    refine mem_rootCenter_iff.mpr ⟨hQ z hzQ, fun u hu => ?_⟩
    have h2 := congrArg α (hzc (α u) (hQ u hu))
    rw [map_mul, map_mul, hα'] at h2
    exact h2
  obtain ⟨T, hTZ, hTfix, hTcard⟩ := exists_fixed_subgroup_card_sq α hα' hsq hcomm hZ
  refine ⟨T, ?_, fun t ht => hsq t (hTZ ht), hTfix⟩
  have hdvd : Nat.card T ∣ 2 ^ n := hcard ▸ Subgroup.card_dvd_of_le hTZ
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hcard] at hTcard
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [hjeq] at hTcard ⊢
  by_contra hlt
  have hj1 : j ≤ 1 := by
    by_contra h
    have : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases j <;> simp at hTcard <;> omega

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoVacFix
