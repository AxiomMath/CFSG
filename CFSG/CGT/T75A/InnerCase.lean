module

public import CFSG.CGT.T75A.FixRoot
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.FinalTheorem

public section

namespace CFSG.CGT.T75A

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki
open CFSG.ComponentClassification.AschbacherToolkit.Bender

theorem isBenderGroup_of_model {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (hD : StatedClassicalModel D .PSU 3 2 f) : IsBenderGroup D := by
  obtain ⟨e⟩ := exists_psu3_of_statedClassicalModel hf hD
  exact .isPSU3 f hf
    (e.trans (MulEquiv.subgroupCongr (show CFSG.Open.PSU3 2 f = PSU3Model f from rfl)))

theorem mem_sylowCenter_of_involution {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (hD : StatedClassicalModel D .PSU 3 2 f) (S : Sylow 2 D) {u : D} (huS : u ∈ (S : Subgroup D))
    (hu : u * u = 1) : u ∈ sylowCenter (S : Subgroup D) :=
  mem_sylowCenter.2 ⟨huS, fun t ht =>
    ((CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one
      (isBenderGroup_of_model hf hD) S huS hu t ht).eq).symm⟩

theorem mem_root_of_involution {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (hD : StatedClassicalModel D .PSU 3 2 f) {S : Sylow 2 D} {u : D} (hu : u * u = 1)
    (hT : ∀ x ∈ sylowCenter (S : Subgroup D), u * x * u⁻¹ ∈ sylowCenter (S : Subgroup D)) :
    u ∈ sylowCenter (S : Subgroup D) := by
  have hS := map_sylow_of_center hf hD (MulAut.conj u) (fun x hx => by
    rw [MulAut.conj_apply]
    exact hT x hx)
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hN : u ∈ Subgroup.normalizer ((S : Subgroup D) : Set D) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => ?_, fun hh => ?_⟩
    · have := hS h hh
      rwa [MulAut.conj_apply] at this
    · have h1 := hS (u * h * u⁻¹) hh
      rw [MulAut.conj_apply, huinv] at h1
      have h2 : u * (u * h * u) * u = h := by
        calc u * (u * h * u) * u = (u * u) * h * (u * u) := by group
          _ = h := by rw [hu]; group
      rwa [h2] at h1
  by_cases hu1 : u = 1
  · rw [hu1]
    exact (sylowCenter (S : Subgroup D)).one_mem
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu) hu1
  have hzp : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have huS : u ∈ (S : Subgroup D) :=
    le_of_isPGroup_of_le_normalizer hzp S (Subgroup.zpowers_le.2 hN) (Subgroup.mem_zpowers u)
  exact mem_sylowCenter_of_involution hf hD S huS hu

theorem center_eq_bot_of_model {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (hD : StatedClassicalModel D .PSU 3 2 f) : Subgroup.center D = ⊥ := by
  obtain ⟨e⟩ := exists_psu3_of_statedClassicalModel hf hD
  have : IsSimpleGroup (CFSG.Open.PSU3 2 f) :=
    CFSG.ShultStronglyClosedTI.unitaryCover_native_simple f hf
  have : IsSimpleGroup D := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center D) with h | h
  · exact h
  · exfalso
    have hB := benderBorel_of_model hf hD
    obtain ⟨S⟩ : Nonempty (Sylow 2 D) := inferInstance
    obtain ⟨-, -, -, hZcard, hScard⟩ := hB S
    have hq : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hcomm : (Subgroup.center (S : Subgroup D)) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      have hxc : (x : D) ∈ Subgroup.center D := h ▸ Subgroup.mem_top (x : D)
      exact Subtype.ext (Subgroup.mem_center_iff.1 hxc y)
    rw [hcomm, Subgroup.card_top, hScard] at hZcard
    have h3 : (2 ^ f) ^ 3 = (2 ^ f) ^ 1 := by rw [pow_one]; exact hZcard
    have := Nat.pow_right_injective hq h3
    omega

theorem inner_involution_eq_conj_root {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (hD : StatedClassicalModel D .PSU 3 2 f) {S : Sylow 2 D} (α : MulAut D) (hαα : α * α = 1)
    (hin : α ∈ (MulAut.conj : D →* MulAut D).range)
    (hαT : ∀ x ∈ sylowCenter (S : Subgroup D), α x ∈ sylowCenter (S : Subgroup D)) :
    ∃ t ∈ sylowCenter (S : Subgroup D), α = MulAut.conj t := by
  obtain ⟨u, rfl⟩ := hin
  have hcen : u * u ∈ Subgroup.center D := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun a : MulAut D => a g) hαα
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h
    have h2 : u * (u * g * u⁻¹) * u⁻¹ = g := h
    calc g * (u * u) = (u * (u * g * u⁻¹) * u⁻¹) * (u * u) := by rw [h2]
      _ = (u * u) * g := by group
  rw [center_eq_bot_of_model hf hD, Subgroup.mem_bot] at hcen
  exact ⟨u, mem_root_of_involution hf hD hcen (fun x hx => hαT x hx), rfl⟩

theorem inner_involution_eq_conj_root_map {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (hD : StatedClassicalModel D .PSU 3 2 f) {S : Sylow 2 D} (α : MulAut D) (hαα : α * α = 1)
    (hin : α ∈ (MulAut.conj : D →* MulAut D).range)
    (hαT : ∀ x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype,
      α x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype) :
    ∃ t ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype,
      α = MulAut.conj t := by
  rw [map_center_eq_sylowCenter] at hαT ⊢
  exact inner_involution_eq_conj_root hf hD α hαα hin hαT

end CFSG.CGT.T75A
