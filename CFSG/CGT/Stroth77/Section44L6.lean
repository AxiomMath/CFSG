module

public import CFSG.CGT.Foote81L6.Bridge.Sylow
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YOutside

public section

namespace CFSG.CGT.Stroth77

open CFSG.Open CFSG.CGT.Foote81L6.Bridge
open CFSG.OddStandard.HigherRank.YamadaG23 (HasPSL6Sylow)

theorem exists_prime_mod_four_factorization_sq_sub_one {m : ℕ} (hm : 1 ≤ m) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ (p ^ 2 - 1).factorization 2 = m + 2 := by
  obtain ⟨B, hB⟩ : ∃ B, 2 ^ m = B + 1 :=
    ⟨2 ^ m - 1, by have := Nat.one_le_two_pow (n := m); omega⟩
  have hBodd : B % 2 = 1 := by
    have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    omega
  have hq : 2 ^ (m + 2) = 4 * (B + 1) := by rw [pow_add, hB]; ring
  have hcop : (2 * B + 1).Coprime (2 ^ (m + 2)) := by
    refine Nat.Coprime.pow_right _ ?_
    rw [Nat.coprime_two_right]
    exact odd_two_mul_add_one B
  obtain ⟨p, -, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq 0 (q := 2 ^ (m + 2)) (a := 2 * B + 1) (by positivity) hcop
  have hpmod : p % (4 * (B + 1)) = 2 * B + 1 := by
    rw [← hq, hmod, hq]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨k, hk⟩ : ∃ k, p = 4 * (B + 1) * k + (2 * B + 1) :=
    ⟨p / (4 * (B + 1)), by rw [← hpmod]; exact (Nat.div_add_mod p _).symm⟩
  have h4 : 4 ∣ 4 * (B + 1) * k := ⟨(B + 1) * k, by ring⟩
  refine ⟨p, hp, by omega, ?_⟩
  have hsq : p ^ 2 - 1 = 2 ^ (m + 2) * ((2 * k + 1) * (2 * (B + 1) * k + B)) := by
    have e : p ^ 2 = 2 ^ (m + 2) * ((2 * k + 1) * (2 * (B + 1) * k + B)) + 1 := by
      rw [hk, hq]
      ring
    omega
  have hodd : ¬ 2 ∣ (2 * k + 1) * (2 * (B + 1) * k + B) := by
    have h2 : 2 ∣ 2 * (B + 1) * k := ⟨(B + 1) * k, by ring⟩
    rw [Nat.Prime.dvd_mul Nat.prime_two]
    omega
  rw [hsq, Nat.factorization_mul (by positivity) (by omega), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]

theorem exists_lieModel_forall_sylow_mulEquiv_sModel {p f : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hq : p ^ f % 4 = 3) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H), CFSG.Blueprint.LieModel H .PSL 6 p f ∧
      ∀ Q : Sylow 2 H,
        Nonempty (↥(Q : Subgroup H) ≃* SModel (((p ^ f) ^ 2 - 1).factorization 2)) := by
  haveI := Fact.mk hp
  have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf.ne'
  refine ⟨StatedProj (StatedSL 6 (GaloisField p f)), inferInstance, inferInstance,
    Or.inl ⟨by decide, ⟨hp, hf, by norm_num, by simp, by simp⟩, GaloisField p f, inferInstance,
      inferInstance, hK, ⟨MulEquiv.refl _⟩⟩, fun Q => ?_⟩
  rw [← hK]
  exact nonempty_mulEquiv_sModel (by rw [hK]; exact hq) Q

theorem hasPSL6Sylow_of_mulEquiv_sModel {G : Type} [Group G] (P : Sylow 2 G) {m : ℕ}
    (hm : 1 ≤ m) (eP : ↥(P : Subgroup G) ≃* SModel (m + 2)) : HasPSL6Sylow G := by
  obtain ⟨p, hp, hp4, hv⟩ := exists_prime_mod_four_factorization_sq_sub_one hm
  obtain ⟨H, _, _, hH, hQ⟩ :=
    exists_lieModel_forall_sylow_mulEquiv_sModel (f := 1) hp one_pos (by simpa using hp4)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 H) := inferInstance
  obtain ⟨eQ⟩ := hQ Q
  rw [pow_one, hv] at eQ
  exact ⟨p, 1, H, inferInstance, hp, one_pos, by simpa using hp4, hH, P, Q, ⟨eP.trans eQ.symm⟩⟩

end CFSG.CGT.Stroth77
