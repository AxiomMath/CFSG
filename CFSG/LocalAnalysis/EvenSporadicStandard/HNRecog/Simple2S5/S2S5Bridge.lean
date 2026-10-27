module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5BridgeSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5I50
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Restrict
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixPrimes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

noncomputable def u0 : Subgroup ↥P1408 := MulAction.stabilizer ↥P1408 (0 : Fin 1408)

theorem mem_u0 {g : ↥P1408} : g ∈ u0 ↔ g • (0 : Fin 1408) = 0 :=
  MulAction.mem_stabilizer_iff

section Orbit

theorem isPretransitive_P1408 : MulAction.IsPretransitive ↥P1408 (Fin 1408) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨gx, hgx, hx⟩ := trans_P x
  obtain ⟨gy, hgy, hy⟩ := trans_P y
  refine ⟨⟨gy⁻¹ * gx, P1408.mul_mem (P1408.inv_mem hgy) hgx⟩, ?_⟩
  rw [Subgroup.smul_def, Equiv.Perm.smul_def, Equiv.Perm.mul_apply, hx]
  exact (Equiv.symm_apply_eq gy).2 hy.symm

theorem card_u0 (hP : Nat.card ↥P1408 = 177408000) : Nat.card ↥u0 = 126000 := by
  haveI := isPretransitive_P1408
  have hOS : Nat.card (MulAction.orbit ↥P1408 (0 : Fin 1408)) *
      Nat.card (MulAction.stabilizer ↥P1408 (0 : Fin 1408)) = Nat.card ↥P1408 := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥P1408 (0 : Fin 1408))
  have horbit : Nat.card (MulAction.orbit ↥P1408 (0 : Fin 1408)) = 1408 := by
    rw [MulAction.orbit_eq_univ]
    simp [Nat.card_coe_set_eq]
  change Nat.card (MulAction.stabilizer ↥P1408 (0 : Fin 1408)) = 126000
  rw [horbit, hP] at hOS
  omega

end Orbit

section Bridge

private theorem bridge_core (hP : Nat.card ↥P1408 = 177408000) :
    u0 = Subgroup.closure (Set.range bridgeGen) ∧ Nonempty (↥u0 ≃* ↥i50) := by
  let I' : Subgroup ↥P1408 := Subgroup.closure (Set.range bridgeGen)
  have hI'le : I' ≤ u0 := by
    rw [Subgroup.closure_le]
    rintro g ⟨k, rfl⟩
    exact mem_u0.2 (bridgeGen_smul_zero k)
  obtain ⟨σ, hσ, hgen⟩ := exists_gens_i50
  obtain ⟨ρ, hρ⟩ := exists_restrictHom (G := ↥P1408) bridgePt bridgePt_injective
  have hgenMem : ∀ k : Fin 6, bridgeGen k ∈ stabEmb (G := ↥P1408) bridgePt := by
    intro k
    rw [mem_stabEmb]
    exact ⟨σ k, fun l => bridgeGen_smul_pt k l (σ k l) (hσ k l)⟩
  have hI'le' : I' ≤ stabEmb (G := ↥P1408) bridgePt := by
    rw [Subgroup.closure_le]
    rintro g ⟨k, rfl⟩
    exact hgenMem k
  let ρ' : ↥I' →* Equiv.Perm (Fin 50) := ρ.comp (Subgroup.inclusion hI'le')
  have hρ'gen : ∀ k : Fin 6,
      ρ' ⟨bridgeGen k, Subgroup.subset_closure ⟨k, rfl⟩⟩ = σ k := by
    intro k
    apply Equiv.ext
    intro l
    apply bridgePt_injective
    have h1 : bridgeGen k • bridgePt l =
        bridgePt (ρ' ⟨bridgeGen k, Subgroup.subset_closure ⟨k, rfl⟩⟩ l) := by
      have hh := hρ (Subgroup.inclusion hI'le'
        ⟨bridgeGen k, Subgroup.subset_closure ⟨k, rfl⟩⟩) l
      simpa [ρ', MonoidHom.comp_apply] using hh
    have h2 : bridgeGen k • bridgePt l = bridgePt (σ k l) :=
      bridgeGen_smul_pt k l (σ k l) (hσ k l)
    exact h1.symm.trans h2
  have hle5 : i50 ≤ ρ'.range := by
    rw [← hgen, Subgroup.closure_le]
    rintro x ⟨k, rfl⟩
    exact ⟨⟨bridgeGen k, Subgroup.subset_closure ⟨k, rfl⟩⟩, hρ'gen k⟩
  have hU : Nat.card ↥I' = 126000 := by
    have h1 : Nat.card i50 ≤ Nat.card ↥ρ'.range := Subgroup.card_le_of_le hle5
    rw [card_i50] at h1
    have h2 : Nat.card ↥ρ'.range ≤ Nat.card ↥I' :=
      Nat.card_le_card_of_surjective ρ'.rangeRestrict ρ'.rangeRestrict_surjective
    have h3 : Nat.card ↥I' ≤ Nat.card ↥u0 := Subgroup.card_le_of_le hI'le
    rw [card_u0 hP] at h3
    omega
  have hEq : I' = u0 := by
    exact Subgroup.eq_of_le_of_card_ge hI'le (by rw [hU, card_u0 hP])
  obtain ⟨e₁⟩ := nonempty_mulEquiv_i50_of_le_range ρ' hU hle5
  exact ⟨hEq.symm, ⟨(MulEquiv.subgroupCongr hEq.symm).trans e₁⟩⟩

theorem isShapeU35_u0 (hP : Nat.card ↥P1408 = 177408000) : Section3.IsShapeU35 ↥u0 := by
  obtain ⟨-, ⟨e₁⟩⟩ := bridge_core hP
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e₂⟩ := nonempty_psu3_mulEquiv_i50
  exact ⟨e₁.trans e₂.symm⟩

end Bridge

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
