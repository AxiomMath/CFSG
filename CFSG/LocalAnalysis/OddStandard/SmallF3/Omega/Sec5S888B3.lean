module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888B1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E4

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H} {α : H →* X}

private lemma b3_mem_conjugate_iff {Y : Type*} [Group Y] {A : Subgroup Y} {g x : Y} :
    x ∈ CFSG.conjugate A g ↔ g * x * g⁻¹ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    simpa [h] using ha
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

private lemma b3_zpowers_two {t : H} (hzsq : z * z = 1) (ht : t ∈ zpowers z) :
    t = 1 ∨ t = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  have h2 : z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two]
    exact hzsq
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

private lemma b3_eq_or_eq_mul (hS : PlaneSetup z K α) {u q : H} (h : α u = α q) :
    u = q ∨ u = q * z := by
  have hk : q⁻¹ * u ∈ zpowers z := by
    rw [← hS.ker, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rcases b3_zpowers_two hS.quad.z_sq hk with h1 | h1
  · left
    exact (inv_mul_eq_one.mp h1).symm
  · right
    rw [← h1]
    group

private lemma b3_conj_iff (hS : PlaneSetup z K α)
    (hperm : ∀ x ∈ normalizer (Sec5B517Q8 hS.quad : Set H), ∀ i : Fin 4,
      ∃ j, CFSG.conjugate (K i) x = K j)
    (hSys : PlaneSys (planeV hS.quad α) (planeW hS.quad α)) {s : H}
    (hsN : s ∈ normalizer (Sec5B517Q8 hS.quad : Set H))
    (hyW : ∀ i, ∀ w ∈ planeW hS.quad α i, α s * w * (α s)⁻¹ ∈ planeW hS.quad α i) (i : Fin 4) :
    (∀ x, s⁻¹ * x * s ∈ K i ↔ x ∈ K i) ∧ (∀ x, s * x * s⁻¹ ∈ K i ↔ x ∈ K i) := by
  obtain ⟨j, hj⟩ := hperm s⁻¹ ((normalizer (Sec5B517Q8 hS.quad : Set H)).inv_mem hsN) i
  have hji : j = i := by
    by_contra hne
    have hall : ∀ u ∈ Sec5B517Q8 hS.quad ⊓ K i, α u = 1 := by
      intro u hu
      obtain ⟨huQ, huK⟩ := Subgroup.mem_inf.mp hu
      have hmemj : s * u * s⁻¹ ∈ K j := by
        rw [← hj, b3_mem_conjugate_iff]
        have e : s⁻¹ * (s * u * s⁻¹) * (s⁻¹)⁻¹ = u := by group
        rw [e]
        exact huK
      have hmemQ : s * u * s⁻¹ ∈ Sec5B517Q8 hS.quad :=
        (Subgroup.mem_set_normalizer_iff.mp hsN u).mp huQ
      have hWj : α (s * u * s⁻¹) ∈ planeW hS.quad α j :=
        Subgroup.mem_map.mpr ⟨_, Subgroup.mem_inf.mpr ⟨hmemQ, hmemj⟩, rfl⟩
      have hWi : α (s * u * s⁻¹) ∈ planeW hS.quad α i := by
        have h := hyW i (α u) (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
        simpa only [map_mul, map_inv] using h
      have hbot : α (s * u * s⁻¹) ∈ planeW hS.quad α i ⊓ planeW hS.quad α j := ⟨hWi, hWj⟩
      rw [hSys.inf_eq_bot (Ne.symm hne)] at hbot
      have h1 : α (s * u * s⁻¹) = 1 := Subgroup.mem_bot.mp hbot
      rw [map_mul, map_mul, map_inv] at h1
      have h2 : α u = (α s)⁻¹ * (α s * α u * (α s)⁻¹) * α s := by group
      rw [h2, h1]
      group
    have hbot : planeW hS.quad α i = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro w hw
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
      exact hall u hu
    have h4 := hSys.card i
    rw [hbot, Subgroup.card_bot] at h4
    omega
  subst hji
  have hK1 : ∀ x, s⁻¹ * x * s ∈ K j ↔ x ∈ K j := by
    intro x
    have h := SetLike.ext_iff.mp hj x
    rw [b3_mem_conjugate_iff, inv_inv] at h
    exact h
  refine ⟨hK1, fun x => ?_⟩
  have h := hK1 (s * x * s⁻¹)
  have e : s⁻¹ * (s * x * s⁻¹) * s = x := by group
  rw [e] at h
  exact h.symm

theorem planeParity_of_setup [Finite H] (hS : PlaneSetup z K α)
    (hperm : ∀ x ∈ normalizer (Sec5B517Q8 hS.quad : Set H), ∀ i : Fin 4,
      ∃ j, CFSG.conjugate (K i) x = K j)
    (hpar : ∀ w ∈ normalizer (Sec5B517Q8 hS.quad : Set H),
      (∀ i, CFSG.conjugate (K i) w = K i) →
      (∀ q ∈ Sec5B517Q8 hS.quad, w * w * q * (w * w)⁻¹ * q⁻¹ ∈ zpowers z) →
        Even (Nat.card {i : Fin 4 // ∃ q ∈ Sec5B517Q8 hS.quad ⊓ K i,
          w⁻¹ * q * w ≠ q ∧ w⁻¹ * q * w ≠ q * z})) :
    PlaneParity (planeV hS.quad α) (planeW hS.quad α) := by
  classical
  have hSys : PlaneSys (planeV hS.quad α) (planeW hS.quad α) := planeSys_of_setup hS hperm
  intro y hyN hyW hy2
  obtain ⟨s, rfl⟩ := hS.surj y
  have hsN : s ∈ normalizer (Sec5B517Q8 hS.quad : Set H) :=
    (mem_normalizer_planeV_iff hS).mp hyN
  have hK : ∀ i, (∀ x, s⁻¹ * x * s ∈ K i ↔ x ∈ K i) ∧ (∀ x, s * x * s⁻¹ ∈ K i ↔ x ∈ K i) :=
    fun i => b3_conj_iff hS hperm hSys hsN hyW i
  have hKfix : ∀ i, CFSG.conjugate (K i) s = K i := by
    intro i
    ext x
    rw [b3_mem_conjugate_iff]
    exact (hK i).2 x
  have hsq : ∀ q ∈ Sec5B517Q8 hS.quad, s * s * q * (s * s)⁻¹ * q⁻¹ ∈ zpowers z := by
    intro q hq
    rw [← hS.ker, MonoidHom.mem_ker]
    have h := hy2 (α q) (Subgroup.mem_map.mpr ⟨q, hq, rfl⟩)
    simp only [map_mul, map_inv]
    rw [h, mul_inv_cancel]
  have hP := hpar s hsN hKfix hsq
  have hz : α z = 1 := MonoidHom.mem_ker.mp (by rw [hS.ker]; exact Subgroup.mem_zpowers z)
  have hiff : ∀ i : Fin 4, (∃ q ∈ Sec5B517Q8 hS.quad ⊓ K i,
      s⁻¹ * q * s ≠ q ∧ s⁻¹ * q * s ≠ q * z) ↔ ActsNontriv (planeW hS.quad α i) (α s) := by
    intro i
    constructor
    · rintro ⟨q, hq, hne1, hne2⟩
      obtain ⟨hqQ, hqK⟩ := Subgroup.mem_inf.mp hq
      have huQ : s⁻¹ * q * s ∈ Sec5B517Q8 hS.quad := by
        have h := (Subgroup.mem_set_normalizer_iff.mp
          ((normalizer (Sec5B517Q8 hS.quad : Set H)).inv_mem hsN) q).mp hqQ
        simpa using h
      have huK : s⁻¹ * q * s ∈ K i := ((hK i).1 q).mpr hqK
      refine ⟨α (s⁻¹ * q * s), Subgroup.mem_map.mpr ⟨_, Subgroup.mem_inf.mpr ⟨huQ, huK⟩, rfl⟩, ?_⟩
      intro heq
      have h1 : α s * α (s⁻¹ * q * s) * (α s)⁻¹ = α q := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        group
      rw [h1] at heq
      rcases b3_eq_or_eq_mul hS heq.symm with h | h
      · exact hne1 h
      · exact hne2 h
    · rintro ⟨a, ha, hne⟩
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨huQ, huK⟩ := Subgroup.mem_inf.mp hu
      have hqQ : s * u * s⁻¹ ∈ Sec5B517Q8 hS.quad :=
        (Subgroup.mem_set_normalizer_iff.mp hsN u).mp huQ
      have hqK : s * u * s⁻¹ ∈ K i := ((hK i).2 u).mpr huK
      have e : s⁻¹ * (s * u * s⁻¹) * s = u := by group
      refine ⟨s * u * s⁻¹, Subgroup.mem_inf.mpr ⟨hqQ, hqK⟩, ?_, ?_⟩
      · rw [e]
        intro h
        apply hne
        have h' : α u = α (s * u * s⁻¹) := congrArg α h
        rw [map_mul, map_mul, map_inv] at h'
        exact h'.symm
      · rw [e]
        intro h
        apply hne
        have h' : α u = α ((s * u * s⁻¹) * z) := congrArg α h
        rw [map_mul, hz, mul_one, map_mul, map_mul, map_inv] at h'
        exact h'.symm
  have hcard : Nat.card {i : Fin 4 // ∃ q ∈ Sec5B517Q8 hS.quad ⊓ K i,
      s⁻¹ * q * s ≠ q ∧ s⁻¹ * q * s ≠ q * z} =
      Nat.card {i : Fin 4 // ActsNontriv (planeW hS.quad α i) (α s)} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  rw [← hcard]
  exact hP

end CFSG.OddStandard.SmallF3.Omega
