module

public import CFSG.ClassicalInvolution.Q3.Q3T7Stmt
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen611
public import CFSG.ClassicalInvolution.Asc77.AscP1Nine3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Disc3

section Wz

theorem sq_eq_of_orderOf_four {G : Type} [Group G] {K : Subgroup G} {z u : G}
    (hz : IsUniqueInvolution K z) (hu : u ∈ K) (hu4 : orderOf u = 4) : u * u = z := by
  have h1 : (u * u) * (u * u) = 1 := by
    have : u ^ 4 = 1 := by rw [← hu4]; exact pow_orderOf_eq_one u
    calc u * u * (u * u) = u ^ 4 := by simp [pow_succ, mul_assoc]
      _ = 1 := this
  rcases hz.unique (u * u) (K.mul_mem hu hu) h1 with h | h
  · exfalso
    have : u ^ 2 = 1 := by rw [pow_two]; exact h
    have h2 := orderOf_dvd_of_pow_eq_one this
    rw [hu4] at h2
    omega
  · exact h


theorem wz3 : WzThree := by
  intro G _ _ _ Ω K hs z hz
  have hΩ : HypOmegaGen Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hs.hyp
  have hK : K ∈ Ω := hs.mem
  obtain ⟨R, hR, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    (bot_le : ⊥ ≤ K)
  obtain ⟨S, hRS⟩ := hR.2.1.exists_le_sylow
  obtain ⟨η, hη, hinv⟩ := exists_invariant_mem_etaSet hΩ S
  have hηG : η ∈ etaG Ω := ⟨S, hη, hinv⟩
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hη.1 hV).2
  have hR8 : 8 ≤ Nat.card R := eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR)
  have hcard : 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) :=
    lt_of_lt_of_le (by omega) ((Subgroup.card_le_of_le (le_inf hR.1 hRS)).trans' hR8)
  have h611 := l6_11Gen G Ω hΩ S η hηG hηS K hK hcard
  have hU : K ⊓ (⨆ V ∈ η, V) ∈ USet Ω := (hη.1 h611).1
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := exists_data_of_mem_USet hΩ hU
  have h2 : IsPGroup 2 ↥(K ⊓ (⨆ V ∈ η, V)) := isPGroup_of_mem_USet hΩ hU
  obtain ⟨x, hx, hx4⟩ := AscP1Nine3.exists_orderOf_four_of_four_le hz inf_le_left h2 h4
  refine ⟨_, ⟨η, hηG, rfl⟩, ?_⟩
  rw [← sq_eq_of_orderOf_four hz hx.1 hx4]
  exact Subgroup.mul_mem _ hx.2 hx.2

end Wz

end CFSG.ClassicalInvolution.Q3.Q3T7
