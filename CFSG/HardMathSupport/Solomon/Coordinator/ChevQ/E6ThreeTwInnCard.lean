module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Diag

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Dickson.Sec6.I923

section Inn

set_option linter.unusedSectionVars false


theorem card_inf_twistedE6Inn {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q) {E : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    (hEc : Nat.card E = 3 ^ 3) (hED : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hEi : ¬ E ≤ twistedE6Inn K σ) : Nat.card ↥(E ⊓ twistedE6Inn K σ) = 3 ^ 2 := by
  classical
  set N := twistedE6Inn K σ with hN
  set π := QuotientGroup.mk' N with hπ
  set ψ : TwM σ →* MulAut ↥(twistedE6RootGroup K σ) ⧸ N :=
    π.comp (compatDiagAutHom TwistTag.E6 K σ.toRingHom) with hψ
  have hψker : twIm σ ≤ ψ.ker := fun u hu =>
    (QuotientGroup.eq_one_iff _).2 (compatDiagAutHom_mem_inner_of_mem_twIm σ hu)
  have hψcard : Nat.card ψ.range ∣ 3 := by
    rw [← Subgroup.index_ker]
    refine (Subgroup.index_dvd_of_le hψker).trans ?_
    rw [twIm_index σ hK hσ]
    exact Nat.gcd_dvd_left _ _
  set φ : ↥E →* MulAut ↥(twistedE6RootGroup K σ) ⧸ N := π.comp E.subtype with hφ
  have hrange : φ.range ≤ ψ.range := by
    rintro _ ⟨⟨d, hd⟩, rfl⟩
    have hdd : d ∈ ((N ⊔ twistedE6Diag K σ : Subgroup _) : Set _) := hED hd
    rw [Subgroup.normal_mul] at hdd
    obtain ⟨i, hi, r, ⟨a, rfl⟩, rfl⟩ := hdd
    refine ⟨a, ?_⟩
    change π (compatDiagAutHom TwistTag.E6 K σ.toRingHom a) =
      π (i * compatDiagAutHom TwistTag.E6 K σ.toRingHom a)
    have hpi : π i = 1 := (QuotientGroup.eq_one_iff i).2 hi
    rw [map_mul, hpi, one_mul]
  have h3 : Nat.card φ.range ∣ 3 := (Subgroup.card_dvd_of_le hrange).trans hψcard
  have hkerφ : φ.ker = N.subgroupOf E := by
    rw [hφ, ← MonoidHom.comap_ker, hπ, QuotientGroup.ker_mk']
    rfl
  have hcardker : Nat.card φ.ker = Nat.card ↥(E ⊓ N) := by
    rw [hkerφ, ← Subgroup.card_map_of_injective E.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have hmul : Nat.card φ.ker * Nat.card φ.range = 3 ^ 3 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, hEc]
  rw [hcardker] at hmul
  rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h1 | h1
  · rw [h1, mul_one] at hmul
    have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; norm_num)
    have heq : E ⊓ N = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hmul, hEc])
    exact absurd (inf_eq_left.1 heq) hEi
  · rw [h1] at hmul
    omega

end Inn

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
