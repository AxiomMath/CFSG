module

public import CFSG.CGT.T75A.InnerCase

public section

namespace CFSG.CGT.T75A

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki
open CFSG.ComponentClassification.AschbacherToolkit.Bender

theorem exists_normalizer_conj_root {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (hD : StatedClassicalModel D .PSU 3 2 f) {S S' S'' : Sylow 2 D}
    (h' : (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype ≠
      (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype)
    (h'' : (Subgroup.center (S'' : Subgroup D)).map (S'' : Subgroup D).subtype ≠
      (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype) :
    ∃ g ∈ (S : Subgroup D), g ∈ Subgroup.normalizer
        (((Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype : Subgroup D) : Set D) ∧
      conjSubgroup g ((Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype) =
        (Subgroup.center (S'' : Subgroup D)).map (S'' : Subgroup D).subtype := by
  have hB := benderBorel_of_model hf hD
  have hK := isBenderGroup_of_model hf hD
  have hcard : Nat.card (Sylow 2 D) = Nat.card (S : Subgroup D) + 1 := by
    rw [card_sylow_psu3 hD, (hB S).2.2.2.2, ← pow_mul, mul_comm]
  have hS' : S' ≠ S := fun h => h' (by rw [h])
  have hS'' : S'' ≠ S := fun h => h'' (by rw [h])
  obtain ⟨u, huS, hu⟩ := exists_smul_eq_of_card_sylow hK S hcard hS' hS''
  refine ⟨u, huS, ?_, ?_⟩
  ·
    rw [map_center_eq_sylowCenter]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hc : ∀ x ∈ sylowCenter (S : Subgroup D), u * x * u⁻¹ = x := fun x hx => by
      have := (mem_sylowCenter.1 hx).2 u huS
      rw [this, mul_inv_cancel_right]
    have hc' : ∀ x ∈ sylowCenter (S : Subgroup D), u⁻¹ * x * u = x := fun x hx => by
      have := (mem_sylowCenter.1 hx).2 u⁻¹ (inv_mem huS)
      rw [this, mul_assoc, inv_mul_cancel, mul_one]
    refine ⟨fun hh => ?_, fun hh => ?_⟩
    · rwa [hc h hh]
    · have h2 : h = u⁻¹ * (u * h * u⁻¹) * u := by group
      rw [h2, hc' _ hh]
      exact hh
  · have hS''eq : (S'' : Subgroup D) = (S' : Subgroup D).map (MulAut.conj u).toMonoidHom := by
      rw [← hu]
      rfl
    rw [map_center_eq_sylowCenter, map_center_eq_sylowCenter, hS''eq, sylowCenter_map_equiv]
    rfl

end CFSG.CGT.T75A
