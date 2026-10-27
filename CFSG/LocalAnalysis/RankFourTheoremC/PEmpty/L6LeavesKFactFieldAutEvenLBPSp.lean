module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenDefs
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSp

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSp)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.CASymplecticSubfield
open CFSG.RankThree.Classical.SteinbergBY (symplectic_prime_semilinear_field_descent)
open CFSG.HardMathSupport.Lang.Coordinator CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)

theorem card_statedProj_statedSp_mul_gcd {k : Type} [Field k] [Finite k] {ℓ f₀ : ℕ}
    (hℓ : ℓ.Prime) (hf₀ : 1 ≤ f₀) (hk : Nat.card k = ℓ ^ f₀) {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (StatedProj (StatedSp n k)) * Nat.gcd 2 (ℓ ^ f₀ - 1) =
      lieOrderNumerator .PSp n (ℓ ^ f₀) := by
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fintype k := Fintype.ofFinite k
    have : CharP k 2 :=
      charP_of_card_eq_prime_pow (f := f₀) (by rw [← Nat.card_eq_fintype_card, hk])
    have h2 : 2 ∣ 2 ^ f₀ := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ f₀ := Nat.one_le_two_pow
    have hg : Nat.gcd 2 (2 ^ f₀ - 1) = 1 :=
      Nat.coprime_two_left.mpr (by rw [Nat.odd_iff]; omega)
    rw [hg, mul_one, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hk]
    rfl
  · have h := CFSG.ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero
      (CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hℓ hℓ2 hk) hn
    rw [hk] at h
    rw [CFSG.ClassicalInvolution.gcd_two_sub_one_of_odd
      (CFSG.ClassicalInvolution.odd_of_card_eq_prime_pow hℓ hℓ2 rfl), h]
    rfl

theorem card_fixed_PSp {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hcl : StatedClassicalModel K .PSp n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut K) (hαp : α ^ p = 1)
    (hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K) :
    ∃ f₀ : ℕ, f = p * f₀ ∧
      lieOrderNumerator .PSp n (ℓ ^ f₀) =
        Nat.gcd 2 (ℓ ^ f₀ - 1) * Nat.card (fixedSubgroup α) := by
  classical
  obtain ⟨⟨hℓ, hf, hn, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, -, -, -, -, hidx, hDH, hdesc⟩ :=
    symplectic_prime_semilinear_field_descent hℓ hf hn hFcard
  set β := MulAut.congr e α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp n F)) :=
    fun hin => hαin ((congr_mem_inner_iff e α).mp hin)
  rw [← card_fixedSubgroup_congr e α]
  have hβ1 : β ≠ 1 := fun h1 =>
    hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hβE : β ∈ spSemilinearAutGroup n F := mem_of_pow_eq_one_of_index_dvd_two hidx hp hp2 hβp
  by_cases hD : β ∈ spLinearAutGroup n F
  · exfalso
    haveI := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal
      (StatedProj (StatedSp n F))
    exact hβout (mem_of_pow_eq_one_of_relIndex_dvd_two
      (H := CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp n F)))
      (D := spLinearAutGroup n F) (hDH.trans (Nat.gcd_dvd_left 2 _)) hp hp2 hD hβp)
  obtain ⟨hpf, σ, hσord, hcardk, h, hh, hβh⟩ := hdesc p hp β hβE hD hβord
  have hcard1 : Nat.card (fixedSubgroup β) = Nat.card (fixedSubgroup (fieldAut n F σ)) := by
    refine (card_fixedSubgroup_eq_of_intertwine (h : MulAut _) (fieldAut n F σ) β
      fun x => ?_).symm
    rw [hβh]
    simp [MulAut.mul_apply]
  have hfix : fixedSubgroup (fieldAut n F σ) = (subfieldSpProj n (descentField σ)).range :=
    Subgroup.ext fun x => fieldAut_apply_eq_self_iff (by omega)
      (by rw [hσord]; exact hp.odd_of_ne_two hp2) x
  have hinj := subfieldSpProj_injective (K := F) (r := n) (by omega) (descentField σ)
  have : Finite (descentField σ) := Subtype.finite
  have hcard2 : Nat.card (fixedSubgroup (fieldAut n F σ)) =
      Nat.card (StatedProj (StatedSp n (descentField σ))) := by
    rw [hfix]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hk : Nat.card (descentField σ) = ℓ ^ (f / p) := hcardk
  have hf0 : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  refine ⟨f / p, (Nat.mul_div_cancel' hpf).symm, ?_⟩
  rw [hcard1, hcard2, mul_comm]
  exact (card_statedProj_statedSp_mul_gcd hℓ hf0 hk (by omega)).symm

theorem fixedLowerBoundAt_PSp : FixedLowerBoundAt .PSp := by
  intro K _ _ n ℓ f f₀ p hadm hmodel ht hp hp5 hpK hdiv hf α hαp hαin
  have hcl : StatedClassicalModel K .PSp n ℓ f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hp2 : p ≠ 2 := by omega
  have hpos : 0 < p := hp.pos
  obtain ⟨f₁, hf₁, heq⟩ := card_fixed_PSp hcl hp hp2 α hαp hαin
  have : f₁ = f₀ := by
    have := hf.symm.trans hf₁
    exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
  subst this
  exact dvd_of_eq heq

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
