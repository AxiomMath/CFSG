module

public import CFSG.LieType.BorelExponent.Defs
public import CFSG.LocalAnalysis.UniquenessCase.Lie.BorelSU

public section

namespace CFSG.LieType.BorelExponent

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem pow_card_sub_one_mem_hypProjUnitriangular {p f r ε : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {b : hypPSU h r ε} (hb : b ∈ hypProjBorel h r ε) :
    b ^ (Nat.card K - 1) ∈ hypProjUnitriangular h r ε := by
  obtain ⟨g, hg, rfl⟩ := hb
  exact ⟨_, pow_mem_of_ker_eq (hypDiagHom h r ε hε) (ker_hypDiagHom hε)
    (fun _ => units_pi_pow_card_sub_one _) hg, map_pow _ _ _⟩

theorem borelExponentAt_PSU : BorelExponentAt .PSU := by
  intro X _ _ m f hadm hLie
  set r := m / 2
  set ε := m % 2
  have hε : ε ≤ 1 := by
    have := Nat.mod_lt m (by norm_num : 0 < 2)
    omega
  have hm_eq : 2 * r + ε = m := Nat.div_add_mod m 2
  have hm3 : 3 ≤ m := by
    have h := hadm
    simp [CFSG.Open.StatedLieAdmissible] at h
    omega
  have hf1 : 1 ≤ f := hadm.2.1
  have hr : 1 ≤ r := by omega
  obtain ⟨K, hK, hfin, h, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_exists_hypPSU (Y := X) (n := f) (r := r)
      (ε := ε) hf1 (by omega) (by rwa [hm_eq])
  obtain ⟨P, hP⟩ := (unitary_order_and_Sylow h hr hε).2.2.2.2.1
  refine HasBorelExponent.of_mulEquiv e.symm (hasBorelExponent_of_sylow P ?_)
  intro x hx
  rw [hP, UnitaryHigher.normalizer_hypProjUnitriangular h hr hε] at hx
  rw [hP]
  have hpow := pow_card_sub_one_mem_hypProjUnitriangular h hε hx
  rwa [h.card] at hpow

end CFSG.LieType.BorelExponent

end
