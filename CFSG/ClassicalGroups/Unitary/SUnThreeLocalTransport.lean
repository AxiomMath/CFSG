module

public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.LieType.Universal.Unitary.Comparison

public section

namespace CFSG.ClassicalGroups.SUnThreeLocal

open Matrix CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem map_conj_statedScalars {ι : Type} [Fintype ι] [DecidableEq ι] {L : Type} [Field L]
    (P : GL ι L) : (StatedScalars ι L).map (MulAut.conj P).toMonoidHom = StatedScalars ι L := by
  have hcent : ∀ c : Lˣ, P * GeneralLinearGroup.scalar ι c * P⁻¹ =
      GeneralLinearGroup.scalar ι c := by
    intro c
    have hc : GeneralLinearGroup.scalar ι c ∈ Subgroup.center (GL ι L) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    rw [Subgroup.mem_center_iff.mp hc P, mul_inv_cancel_right]
  ext B
  simp only [Subgroup.mem_map, StatedScalars, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨A, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, (hcent c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, hcent c⟩

@[expose] noncomputable def statedProjConjEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    {L : Type} [Field L] (P : GL ι L) {H H' : Subgroup (GL ι L)}
    (hH : H.map (MulAut.conj P).toMonoidHom = H') : StatedProj H ≃* StatedProj H' :=
  statedProjCongr (MulAut.conj P) hH (map_conj_statedScalars P)

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem exists_map_conj_statedSU_eq_SU_of_card (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) :
    ∃ P : GL (Fin n) F, (StatedSU n (p ^ f) F).map (MulAut.conj P).toMonoidHom =
      SU (unitaryInvolution F p f) n := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hF n
  refine ⟨P⁻¹, ?_⟩
  rw [← SUid_eq_statedSU hF n]
  ext B
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨A, hA, rfl⟩
    have h := ((conjEquiv P hP).symm ⟨A, hA⟩).2
    rw [inv_inv]
    exact h
  · intro hB
    exact ⟨P * B * P⁻¹, (conjEquiv P hP ⟨B, hB⟩).2, by group⟩

theorem statedProj_statedSU_mulEquiv_SU_of_card (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) :
    Nonempty (StatedProj (StatedSU n (p ^ f) F) ≃*
      StatedProj (SU (unitaryInvolution F p f) n)) := by
  obtain ⟨P, hP⟩ := exists_map_conj_statedSU_eq_SU_of_card hF n
  exact ⟨statedProjConjEquiv P hP⟩

end CFSG.ClassicalGroups.SUnThreeLocal
