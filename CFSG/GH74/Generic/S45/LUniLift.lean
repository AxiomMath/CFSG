module

public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
public import CFSG.LieType.Steinberg.CentralExt.UnitaryHigher
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.GH74.Generic.S45

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

variable {p f : ℕ} {K : Type} [Field K]

theorem isPerfect_and_center_unitarySU' (h : UnitaryFieldData p f K) (hp : p ≠ 2) {d : ℕ}
    (hd : 3 ≤ d) :
    Group.IsPerfect (unitarySU p f K d) ∧
      Subgroup.center (unitarySU p f K d) = unitaryScalars h d := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have hF : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hnq : (d, p ^ f) ≠ (3, 2) := fun he => by
    have h2 : p ^ f = 2 := congrArg Prod.snd he
    apply hp
    have : p ∣ 2 := h2 ▸ dvd_pow_self p (by have := h.one_le; omega)
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this
  obtain ⟨hqs, hcen⟩ := isQuasisimple_statedSU_of_card (F := K) (p := p) (f := f) hF hd hnq
  exact ⟨hqs.1, hcen.trans (unitaryScalars_eq h (by omega)).symm⟩

theorem exists_lift_unitarySU' (h : UnitaryFieldData p f K) (hp : p ≠ 2) {d : ℕ} (hd : 3 ≤ d)
    {X : Type} [Group X] (θ : unitarySU p f K d →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (unitarySU p f K d)) (σ : X ≃* X) :
    ∃ (A : GL (Fin d) K) (φ : K ≃+* K)
      (hA : ∀ g : unitarySU p f K d,
        A * glAut φ (g : GL (Fin d) K) * A⁻¹ ∈ unitarySU p f K d),
      ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (A : Matrix (Fin d) (Fin d) K) = 1 ∧
        (∀ g : unitarySU p f K d, θ (unitaryConjHom A φ hA g) = σ (θ g)) ∧
        ((∀ x, σ (σ x) = x) →
          (φ = RingEquiv.refl K ∨ ∀ c, φ c = h.bar c) ∧
            (unitaryConjHom A φ hA).comp (unitaryConjHom A φ hA) = MonoidHom.id _) := by
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ d = 2 * r + ε := ⟨d / 2, d % 2, by omega, by omega⟩
  obtain ⟨hperf, hcen⟩ := isPerfect_and_center_unitarySU' h hp hd
  have := hperf
  obtain ⟨β, hβ, hβinv⟩ := exists_mulEquiv_of_central_cover
    (unitaryProj_surjective h (2 * r + ε)) (by rw [ker_unitaryProj, hcen]) hθ hker σ
  obtain ⟨φ, A, hAu, hAg, hφ⟩ := exists_unitary_semilinear_psu h hp (by omega) hε hd β
  have hlift := hβ (unitaryConjHom A φ fun g => (hAg g).1) fun x => ((hAg x).2).symm
  exact ⟨A, φ, fun g => (hAg g).1, hAu, hlift, fun hσ =>
    ⟨hφ (hβinv hσ), lift_comp_self_eq_id hker hσ hlift⟩⟩

end CFSG.GH74.Generic.S45
