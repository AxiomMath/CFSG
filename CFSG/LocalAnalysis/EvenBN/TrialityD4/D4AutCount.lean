module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Native
public import CFSG.LieType.Simplicity.TrialityD4
import CFSG.LocalAnalysis.EvenBN.TrialityD4.Thompson
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bZsig

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

private theorem dvd_pow_eight_add_pow_four_add_one {ℓ x : ℕ} (hℓ : ℓ.Prime) (hx : 1 ≤ x)
    (hord : orderOf (2 : ZMod ℓ) = 12 * x) : ℓ ∣ (2 ^ x) ^ 8 + (2 ^ x) ^ 4 + 1 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  have h12 : ((2 : ZMod ℓ) ^ x) ^ 12 = 1 := by
    have h := pow_orderOf_eq_one (2 : ZMod ℓ)
    rwa [hord, mul_comm, pow_mul] at h
  have h4 : ((2 : ZMod ℓ) ^ x) ^ 4 ≠ 1 := by
    intro h
    rw [← pow_mul, mul_comm] at h
    have h' := Nat.le_of_dvd (by omega) (hord ▸ orderOf_dvd_of_pow_eq_one h)
    omega
  have hf : (((2 : ZMod ℓ) ^ x) ^ 4 - 1) * (((2 : ZMod ℓ) ^ x) ^ 8 + ((2 : ZMod ℓ) ^ x) ^ 4 + 1)
      = 0 := by
    linear_combination h12
  rcases mul_eq_zero.1 hf with h | h
  · exact absurd (sub_eq_zero.1 h) h4
  · exact h

theorem card_le_of_sq_eq_one_of_lieModel_trialityD4
    {X : Type} [Group X] {m x : ℕ} (hX : CFSG.Blueprint.LieModel X .trialityD4 m 2 x)
    {E : Subgroup (MulAut X)} (hE : ∀ e ∈ E, e ^ 2 = 1) : Nat.card E ≤ 2 ^ (5 * x) := by
  obtain ⟨-, hx, rfl⟩ := hX.admissible
  obtain ⟨d⟩ := nonempty_trialityD4Data_of_lieModel hx hX
  have hsq : ∀ e : E, orderOf e ∣ 2 := fun e =>
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [Subgroup.coe_pow, hE e e.2, Subgroup.coe_one]))
  have hcomm : IsMulCommutative E := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two hsq a b).eq⟩⟩
  calc Nat.card E ≤ (2 ^ x) ^ 5 := (d.card_le_of_isElemAbelian_aut rfl ⟨hcomm, hE⟩).1
    _ = 2 ^ (5 * x) := (pow_mul' 2 5 x).symm

theorem isSimpleGroup_of_lieModel_trialityD4
    {X : Type} [Group X] {m x : ℕ} (hX : CFSG.Blueprint.LieModel X .trialityD4 m 2 x) :
    IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_3d4_simplicity X 2 x
    (hX.chevalleyExceptionalModel (by decide))).2

theorem exists_prime_dvd_card_of_lieModel_trialityD4
    {X : Type} [Group X] {m x : ℕ} (hX : CFSG.Blueprint.LieModel X .trialityD4 m 2 x) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ Nat.card X ∧ orderOf (2 : ZMod ℓ) = 12 * x := by
  obtain ⟨-, hx, rfl⟩ := hX.admissible
  obtain ⟨d⟩ := nonempty_trialityD4Data_of_lieModel hx hX
  obtain ⟨ℓ, hℓ, -, hord⟩ :=
    CFSG.QuasithinUnique.Setup.X5.exists_prime_orderOf_two_eq_six_mul (f := 2 * x) (by omega)
  rw [show 6 * (2 * x) = 12 * x by ring] at hord
  refine ⟨ℓ, hℓ, ?_, hord⟩
  rw [d.card_eq]
  exact Dvd.dvd.mul_left (dvd_pow_eight_add_pow_four_add_one hℓ hx hord) _

end CFSG.LocalAnalysis.EvenBN.TrialityD4
