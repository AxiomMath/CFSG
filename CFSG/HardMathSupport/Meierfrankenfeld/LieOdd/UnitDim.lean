module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitRoot
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitOrbit
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.LiftOrbitRel

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.LinearGroups

variable {W : Type} [CommGroup W] [Finite W]

theorem two_pow_le_card_of_psun (hW : ∀ w : W, w * w = 1)
    {K : Type} [Field K] [Finite K] {p e n : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ e) ^ 2) (hn : 3 ≤ n) {L : Subgroup (MulAut W)}
    (π : ↥L →* StatedProj (StatedSU n (p ^ e) K)) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥L) (hZ : ¬ p ∣ Nat.card π.ker) :
    2 ^ (orderOf (2 : ZMod p) * ((p ^ e - 1) * (p ^ e) ^ (n - 2) / (2 * (p - 1)))) ≤
      Nat.card W := by
  have he : 1 ≤ e := by
    by_contra hlt
    have he0 : e = 0 := by omega
    have h1 : Nat.card K = 1 := by rw [hK, he0]; simp
    have h2 := Finite.one_lt_card (α := K)
    omega
  have hU : UnitaryFieldData p e K := ⟨Fact.out, he, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨ε, rfl⟩ : ∃ ε, n = 2 * 1 + ε := ⟨n - 2, by omega⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport hU (r := 1) (ε := ε)
  have hn1 : 1 ≤ 2 * 1 + ε := by omega
  let ι := hypPSUEquivStatedProj hU hR hn1
  let π' : ↥L →* hypPSU hU 1 ε := (ι.symm : _ →* _).comp π
  have hπ' : Function.Surjective π' := ι.symm.surjective.comp hπ
  have hker_eq : π'.ker = π.ker := by
    ext x
    simp [π', MonoidHom.mem_ker]
  obtain ⟨τ₀, hτE, hτ0⟩ := hU.exists_mem_traceZero_ne_zero
  have hbar : hU.bar τ₀ = -τ₀ := by
    have := hU.mem_traceZero.1 hτE
    rw [UnitaryFieldData.trace] at this
    linear_combination this
  have two_ne : (2 : K) ≠ 0 := by
    intro h2
    have h3 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
    rw [CharP.cast_eq_zero_iff K p] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h3)
  have hc : UCtx hU τ₀ := ⟨hbar, hτ0, two_ne⟩
  let _ : Fintype hU.fixedField := Fintype.ofFinite _
  let ψ : Multiplicative (UP hU.fixedField ε) →* hypPSU hU 1 ε :=
    (hypProj hU 1 ε).comp (uPar hc)
  have hψ : Function.Injective ψ := uPar_inj hc
  have hFcard : Nat.card hU.fixedField = p ^ e := hU.card_fixedField
  have hpF : ∀ y : UP hU.fixedField ε, p • y = 0 := by
    intro y
    refine Prod.ext (funext fun l => ?_) ?_
    · apply Subtype.ext
      simp
    · apply Subtype.ext
      simp
  have hZne : (ψ.comp (AddMonoidHom.inr (Fin ε → hU.fixedField) hU.fixedField).toMultiplicative).range
      ≠ ⊥ := by
    intro h0
    have hmem : ψ (Multiplicative.ofAdd ((0 : Fin ε → hU.fixedField), (1 : hU.fixedField))) ∈
        (ψ.comp (AddMonoidHom.inr (Fin ε → hU.fixedField) hU.fixedField).toMultiplicative).range :=
      ⟨Multiplicative.ofAdd 1, rfl⟩
    rw [h0, Subgroup.mem_bot] at hmem
    have h1 := hψ (hmem.trans (map_one ψ).symm)
    exact one_ne_zero (congrArg (fun z : Multiplicative (UP hU.fixedField ε) =>
      (Multiplicative.toAdd z).2) h1)
  have hUc : ∀ a ∈ ψ.range, ∀ b ∈ ψ.range, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (mul_comm x y)
  have hUp : ∀ a ∈ ψ.range, a ^ p = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ p = 1 := by
      rw [← ofAdd_toAdd x, ← ofAdd_nsmul, hpF]
      rfl
    rw [this, map_one]
  have ht : ∀ (d : Fin ε → hU.fixedField) (μ : (hU.fixedField)ˣ)
      (x : Multiplicative (UP hU.fixedField ε)),
      hypProj hU 1 ε (tPar hc d μ) * ψ x * (hypProj hU 1 ε (tPar hc d μ))⁻¹ =
        ψ (Multiplicative.ofAdd (utau d (μ : hU.fixedField) (Multiplicative.toAdd x))) := by
    intro d μ x
    simp only [ψ, MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, tPar_conj hc]
  have hfin : Finite (hypPSU hU 1 ε) := inferInstance
  have key := FFToolkit.two_pow_le_card_of_lift_orbit_rel hW hp2 π' hπ'
    (by rw [hker_eq]; exact hker) (by rw [hker_eq]; exact hZ)
    (Z := (ψ.comp (AddMonoidHom.inr (Fin ε → hU.fixedField) hU.fixedField).toMultiplicative).range)
    (U₀ := ψ.range) (T₀ := Subgroup.normalizer (ψ.range : Set (hypPSU hU 1 ε)))
    (m := (p ^ e - 1) * (p ^ e) ^ ε / (2 * (p - 1)))
    (fun z ⟨y, hy⟩ => ⟨_, hy⟩) hZne hUc hUp le_rfl (fun D₀ _ hrel hZD => by
      have := horb_of_param ψ (fun d μ => hypProj hU 1 ε (tPar hc d μ)) ht hrel hZD
      rw [hFcard] at this
      exact Nat.div_le_of_le_mul (by rw [mul_comm (p ^ e - 1)]; exact this))
  have e2 : 2 * 1 + ε - 2 = ε := by omega
  rw [e2, mul_comm]
  exact key

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
