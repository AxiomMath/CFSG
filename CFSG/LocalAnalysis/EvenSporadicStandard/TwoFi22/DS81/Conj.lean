module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Transfer

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Quasithin

variable {G : Type*} [Group G]

theorem exists_conj_le_of_odd_index [Finite G] {L N B : Subgroup G} (hBL : B ≤ L)
    (hodd : Odd (N.relIndex L)) (hB : IsPGroup 2 B) :
    ∃ g ∈ L, ∀ b ∈ B, g * b * g⁻¹ ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup L := N.subgroupOf L with hK
  obtain ⟨Q⟩ : Nonempty (Sylow 2 K) := inferInstance
  have hP : IsPGroup 2 ((Q : Subgroup K).map K.subtype) := Q.isPGroup'.map K.subtype
  have hidx : ¬ 2 ∣ ((Q : Subgroup K).map K.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro h
    rcases (Nat.prime_two.dvd_mul).mp h with h1 | h1
    · exact Q.not_dvd_index h1
    · exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd) h1
  set P : Sylow 2 L := hP.toSylow hidx with hPdef
  have hPK : ∀ x ∈ (P : Subgroup L), x ∈ K := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := (show x ∈ (Q : Subgroup K).map K.subtype from hx)
    exact k.2
  have hB' : IsPGroup 2 (B.subgroupOf L) :=
    hB.of_equiv (Subgroup.subgroupOfEquivOfLe hBL).symm
  obtain ⟨P', hP'⟩ := hB'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L P P'
  refine ⟨(g : G)⁻¹, inv_mem g.2, fun b hb => ?_⟩
  have hbL : (⟨b, hBL hb⟩ : L) ∈ (P' : Subgroup L) := hP' (mem_subgroupOf.2 hb)
  have hmem : (g⁻¹ * ⟨b, hBL hb⟩ * g : L) ∈ (P : Subgroup L) := by
    rw [← hg] at hbL
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hbL
    obtain ⟨s, hs, hsb⟩ := hbL
    have : s = g⁻¹ * ⟨b, hBL hb⟩ * g := by
      rw [MulAut.smul_def, MulAut.conj_apply] at hsb
      rw [← hsb]
      group
    rwa [this] at hs
  have hK' := hPK _ hmem
  rw [hK, mem_subgroupOf] at hK'
  simpa using hK'

theorem exists_conj_of_unique [Finite G] {L E : Subgroup G} {n : ℕ}
    (hodd : Odd ((normalizer (E : Set G)).relIndex L))
    (huniq : ∀ B : Subgroup G, B ≤ normalizer (E : Set G) ⊓ L → (∀ b ∈ B, b ^ 2 = 1) →
      Nat.card B = 2 ^ n → B = E)
    {B : Subgroup G} (hBL : B ≤ L) (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hBn : Nat.card B = 2 ^ n) :
    ∃ l ∈ L, B = conjSubgroup E l := by
  have hodd' : Odd ((normalizer (E : Set G) ⊓ L).relIndex L) := by
    rwa [inf_relIndex_right]
  have hB : IsPGroup 2 B := IsPGroup.of_card hBn
  obtain ⟨g, hgL, hg⟩ := exists_conj_le_of_odd_index hBL hodd' hB
  have hle : conjSubgroup B g⁻¹ ≤ normalizer (E : Set G) ⊓ L := by
    intro x hx
    rw [mem_conjSubgroup_iff, inv_inv] at hx
    have := hg _ hx
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
  have hsq : ∀ b ∈ conjSubgroup B g⁻¹, b ^ 2 = 1 := by
    intro b hb
    rw [mem_conjSubgroup_iff, inv_inv] at hb
    have h2 := hB2 _ hb
    rw [sq] at h2 ⊢
    calc b * b = g * ((g⁻¹ * b * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = 1 := by rw [h2]; group
  have hcard : Nat.card (conjSubgroup B g⁻¹) = 2 ^ n := by
    rw [CFSG.EvenSmallLie.UnitarySix.SolomonWong.card_conjSubgroup, hBn]
  have heq := huniq _ hle hsq hcard
  refine ⟨g, hgL, ?_⟩
  have := congrArg (fun A => conjSubgroup A g) heq
  simp only [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at this
  exact this

end CFSG.EvenSporadicStandard.TwoFi22.DS81
