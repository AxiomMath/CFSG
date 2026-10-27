module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutLift

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec4I_exists_twisted_lift (Y : Subgroup G) {P : Type} [Group P] (ρ : ↥Y →* P)
    (hρ : OddCentralCover ρ) {s : G} (hs : s * s = 1) (hsN : s ∈ normalizer (Y : Set G))
    (α : MulAut P) (hα : ∀ y : ↥Y, ρ (conjAut Y hs hsN y) = α (ρ y)) {a₀ u₀ : P}
    (hu₀ : u₀ ∈ fixSub α) (huu : u₀ * u₀ = 1) (hau : a₀⁻¹ * α a₀ = u₀) :
    ∃ (u : G) (hu : u ∈ Y), u * u = 1 ∧ ρ ⟨u, hu⟩ = u₀ ∧ s * u = u * s ∧
      ∃ a ∈ Y, a⁻¹ * s * a = u * s := by
  set σ : MulAut ↥Y := conjAut Y hs hsN with hσdef
  have hσ2 : σ * σ = 1 := conjAut_mul_self Y hs hsN
  have hcov := hρ.oddCentralCover_fixHom hσ2 hα
  have huFF : (⟨u₀, hu₀⟩ : ↥(fixSub α)) * ⟨u₀, hu₀⟩ = 1 := Subtype.ext huu
  obtain ⟨û, hûû, hûF⟩ := hcov.exists_mul_self_eq_one_lift huFF
  have hρû : ρ ((û : ↥Y)) = u₀ := congrArg Subtype.val hûF
  have hûσ : σ (û : ↥Y) = û := û.2
  have hûû' : (û : ↥Y) * û = 1 := congrArg Subtype.val hûû
  obtain ⟨b, hb⟩ := hρ.surjective a₀
  obtain ⟨t, htdef⟩ : ∃ t : ↥Y, t = b⁻¹ * σ b := ⟨_, rfl⟩
  have hρt : ρ t = u₀ := by
    rw [htdef, map_mul, map_inv, hα, hb]
    exact hau
  obtain ⟨n, hndef⟩ : ∃ n : ↥Y, n = (û : ↥Y)⁻¹ * t := ⟨_, rfl⟩
  have hn : n ∈ ρ.ker := by
    rw [hndef, MonoidHom.mem_ker, map_mul, map_inv, hρû, hρt, inv_mul_cancel]
  have hnc : n ∈ center ↥Y := hρ.ker_le_center hn
  have hσt : σ t = t⁻¹ := by
    rw [htdef, map_mul, map_inv, aut_apply_apply hσ2, mul_inv_rev, inv_inv]
  have hûi : (û : ↥Y)⁻¹ = û := inv_eq_of_mul_eq_one_right hûû'
  have htn : t = (û : ↥Y) * n := by rw [hndef, hûi, ← mul_assoc, hûû', one_mul]
  have hût : (û : ↥Y) * t = t * û := by
    have hc := Subgroup.mem_center_iff.mp hnc (û : ↥Y)
    calc (û : ↥Y) * t = û * (û * n) := by rw [← htn]
      _ = û * (n * û) := by rw [hc]
      _ = (û * n) * û := by rw [mul_assoc]
      _ = t * û := by rw [← htn]
  have hσn : σ n = n⁻¹ := by
    have h1 : σ n = (û : ↥Y) * t⁻¹ := by
      rw [hndef, map_mul, map_inv, hûσ, hσt, hûi]
    have h2 : n⁻¹ = t⁻¹ * û := by
      rw [hndef, mul_inv_rev, inv_inv]
    rw [h1, h2]
    calc (û : ↥Y) * t⁻¹ = t⁻¹ * (t * û) * t⁻¹ := by group
      _ = t⁻¹ * (û * t) * t⁻¹ := by rw [hût]
      _ = t⁻¹ * û := by group
  obtain ⟨k, hk⟩ := hρ.exists_sqrt hn
  obtain ⟨m, hmdef⟩ : ∃ m : ↥Y, m = n ^ k := ⟨_, rfl⟩
  have hmk : m ∈ ρ.ker := by rw [hmdef]; exact Subgroup.pow_mem _ hn k
  have hmc : m ∈ center ↥Y := hρ.ker_le_center hmk
  have hσm : σ m = m⁻¹ := by rw [hmdef, map_pow, hσn, inv_pow]
  have hmm : m * m = n := by rw [hmdef]; exact hk
  have hkey : (b * m)⁻¹ * σ (b * m) = (û : ↥Y) := by
    have hcomm : ∀ z : ↥Y, m * z = z * m := fun z => (Subgroup.mem_center_iff.mp hmc z).symm
    have hmi : m⁻¹ * t = t * m⁻¹ := by
      calc m⁻¹ * t = m⁻¹ * (t * m) * m⁻¹ := by group
        _ = m⁻¹ * (m * t) * m⁻¹ := by rw [hcomm t]
        _ = t * m⁻¹ := by group
    calc (b * m)⁻¹ * σ (b * m) = m⁻¹ * (b⁻¹ * σ b) * σ m := by rw [map_mul]; group
      _ = m⁻¹ * t * m⁻¹ := by rw [← htdef, hσm]
      _ = t * (m * m)⁻¹ := by rw [hmi]; group
      _ = t * n⁻¹ := by rw [hmm]
      _ = (û : ↥Y) := by rw [hndef, mul_inv_rev, inv_inv]; group
  refine ⟨((û : ↥Y) : G), (û : ↥Y).2, congrArg Subtype.val hûû', hρû,
    ((mem_fixSub_conjAut_iff Y hs hsN (û : ↥Y)).mp û.2), ((b * m : ↥Y) : G), (b * m).2, ?_⟩
  have h1 := congrArg Subtype.val hkey
  have h2 : ((((b * m)⁻¹ * σ (b * m) : ↥Y)) : G) =
      ((b * m : ↥Y) : G)⁻¹ * (s * ((b * m : ↥Y) : G) * s⁻¹) := rfl
  rw [h2] at h1
  calc ((b * m : ↥Y) : G)⁻¹ * s * ((b * m : ↥Y) : G) =
      (((b * m : ↥Y) : G)⁻¹ * (s * ((b * m : ↥Y) : G) * s⁻¹)) * s := by group
    _ = ((û : ↥Y) : G) * s := by rw [h1]

end CFSG.OddStandard.SmallF3.Omega
