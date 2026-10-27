module

public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge

public section

namespace CFSG.CGT.T75M

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

theorem sz_outer_odd {a : ℕ} (ha : 1 ≤ a) {K : Type} [Group K]
    (e : K ≃* Sz a) : Odd (Nat.card (Outer K)) := by
  obtain ⟨e'⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a
  have hmodel : CFSG.Blueprint.SuzukiModel K 2 (2 * a + 1) :=
    ⟨rfl, a, ha, GaloisField 2 (2 * a + 1), inferInstance, inferInstance, rfl,
      GaloisField.card 2 (2 * a + 1) (by omega), ⟨e.trans e'⟩⟩
  exact (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} K 2 (2 * a + 1)
    hmodel).1.2.2

theorem exists_conj_of_mul_self_eq_one {K : Type*} [Group K] (hodd : Odd (Nat.card (Outer K)))
    {σ : MulAut K} (hσ : σ * σ = 1) : ∃ g : K, σ = MulAut.conj g := by
  have h1 : (QuotientGroup.mk σ : Outer K) ^ 2 = 1 := by
    rw [pow_two, ← QuotientGroup.mk_mul, hσ, QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk σ : Outer K) ∣ 2 := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk σ : Outer K) ∣ Nat.card (Outer K) := orderOf_dvd_natCard _
  have h4 : orderOf (QuotientGroup.mk σ : Outer K) = 1 := by
    have hc : Nat.Coprime 2 (Nat.card (Outer K)) := Nat.coprime_two_left.2 hodd
    exact Nat.eq_one_of_dvd_coprimes hc h2 h3
  have h5 : (QuotientGroup.mk σ : Outer K) = 1 := orderOf_eq_one_iff.1 h4
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff σ).1 h5
  exact ⟨g, hg.symm⟩

end CFSG.CGT.T75M
