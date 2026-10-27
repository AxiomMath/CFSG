module

public import CFSG.Sporadic.Schreier.RuInvClasses
public import Certificates.Certificate24360

public section

namespace CFSG.EvenSporadicStandard.TwoRu

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native

theorem ruS_sq_fixed :
    ∀ g ∈ ruS, g ^ 4 = 1 → g ^ 2 ≠ 1 → 0 < (fixSet (g ^ 2)).ncard := by
  refine ruS_forall (p := ruSquareTest)
    (P := fun g => g ^ 4 = 1 → g ^ 2 ≠ 1 → 0 < (fixSet (g ^ 2)).ncard) ?_
    Certificates.certificate24360
  intro t g ht hp h4 h2
  have h4' : eqA 4060 (powA 4060 t 4) (idA 4060) = true :=
    (eqA_iff (rep_powA ht 4) rep_idA).2 h4
  have h2' : eqA 4060 (compA 4060 t t) (idA 4060) = false := by
    cases h : eqA 4060 (compA 4060 t t) (idA 4060)
    · rfl
    · exact absurd (by rw [pow_two]; exact (eqA_iff (rep_compA ht ht) rep_idA).1 h) h2
  simp only [ruSquareTest, h4', h2', Bool.not_true, Bool.false_or, decide_eq_true_eq] at hp
  rw [pow_two, ← ruFixCount_eq (rep_compA ht ht)]
  exact hp

theorem exists_conj_mem_ruS_of_pow_four
    {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruP) (h4 : t ^ 4 = 1) :
    ∃ g ∈ ruP, g * t * g⁻¹ ∈ ruS := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let t' : ruP := ⟨t, ht⟩
  have ht' : t' ^ 4 = 1 := Subtype.ext (by simpa using h4)
  have hp : IsPGroup 2 (Subgroup.zpowers t') := by
    have hd : orderOf t' ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one ht'
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ruP Q ruSylow
  have hmem : MulAut.conj g • t' ∈ (ruSylow : Subgroup ruP) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ (Subgroup.mem_zpowers t'))
  rw [ruSylow_coe, Subgroup.mem_subgroupOf, MulAut.smul_def, MulAut.conj_apply] at hmem
  exact ⟨g, g.2, by simpa [t'] using hmem⟩

theorem ru_sq_not_mem_ruAP
    {w : Equiv.Perm (Fin 4060)} (hw : w ∈ ruP) (h4 : w ^ 4 = 1)
    (h2 : w ^ 2 ≠ 1) : w ^ 2 ∉ ruAP := by
  rintro ⟨h, -, hh⟩
  obtain ⟨g, -, hg⟩ := exists_conj_mem_ruS_of_pow_four hw h4
  have h4g : (g * w * g⁻¹) ^ 4 = 1 := by rw [conj_pow, h4]; group
  have h2g : (g * w * g⁻¹) ^ 2 ≠ 1 := fun h1 => h2 (by
    rw [conj_pow] at h1
    calc w ^ 2 = g⁻¹ * (g * w ^ 2 * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)
  have hpos := ruS_sq_fixed _ hg h4g h2g
  rw [conj_pow, ncard_fixSet_conj, ← hh, conj_ruA0_ncard] at hpos
  exact lt_irrefl _ hpos

end CFSG.EvenSporadicStandard.TwoRu
