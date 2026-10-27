module

public import CFSG.LieType.Steinberg.CentralExt.SUOddPrime
public import CFSG.LieType.Steinberg.CentralExt.SUOddCover
public import CFSG.LieType.Steinberg.CentralExt.PrimeCover
public import CFSG.LieType.Steinberg.CentralExt.SUThreeThree
public import CFSG.LieType.Steinberg.CentralExt.SUThreeCharThree
public import CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo
public import CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverOddChar
public import CFSG.RankThree.CentralLiftU.UnitaryThreeSplit
public import CFSG.RankThree.CentralLiftU.EvenSplit

public section

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg

namespace CFSG.LieType.Steinberg.CentralExt.SUOdd

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime] [CharP F p]

local notation "σ₀" => unitaryInvolution F p f

theorem su_odd_exists_section_of_ne
    (hF : Nat.card F = (p ^ f) ^ 2) (hf : 1 ≤ f) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) {n : ℕ}
    (hn : 3 ≤ n) (ho : ¬ Even n) {E : Type} [Group E] [Finite E] {π : E →* SU σ₀ n}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hk : IsPGroup ℓ π.ker) :
    ∃ s : SU σ₀ n →* E, ∀ x, π (s x) = x := by
  have hℓ2 := hℓ.two_le
  rcases hp.out.eq_two_or_odd' with rfl | hpo
  · rcases (show ℓ = 3 ∨ 3 < ℓ by omega) with rfl | hℓ3
    · refine su_odd_exists_section_of_prime hF hℓ hℓp ?_ hn ho hπ hcen hk
      intro R _ _ ρ hρ hc hk'
      rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
      · exact SUThreeFieldTwo.su_three_two_exists_section_of_three hF hρ hc hk'
      · exact su_three_even_exists_section_of_odd hF hf2 hρ hc
          (odd_card_of_isPGroup Nat.prime_three (by norm_num) hk')
    · obtain ⟨s, hs, -⟩ :=
        CFSG.RankThree.CentralLiftU.su_odd_central_large_prime_extension_splitting_two
          ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩ hℓ hℓ3 hn ho hπ hcen hk
      exact ⟨s, hs⟩
  · have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_odd_iff_even.2 even_two) hpo
    rcases (show ℓ = 2 ∨ ℓ = 3 ∨ 3 < ℓ by omega) with rfl | rfl | hℓ3
    · obtain ⟨s, hs, -⟩ := su_central_two_extension_splitting hF hp2 (by omega) hπ hcen hk
      exact ⟨s, hs⟩
    · refine su_odd_exists_section_of_prime hF hℓ hℓp ?_ hn ho hπ hcen hk
      intro R _ _ ρ hρ hc hk'
      exact SUThreeThree.su_three_exists_section_of_three hF hp2 (Ne.symm hℓp) hρ hc hk'
    · refine su_odd_exists_section_of_prime hF hℓ hℓp ?_ hn ho hπ hcen hk
      intro R _ _ ρ hρ hc hk'
      exact CFSG.RankThree.CentralLiftU.exists_section_SU_three_large hF hp2 hℓ hℓ3 hρ hc hk'

theorem su_odd_cover_trivial_char
    (hF : Nat.card F = (p ^ f) ^ 2) (hf : 1 ≤ f) {n : ℕ} (hn : 3 ≤ n) (ho : ¬ Even n)
    (hq : (n, p ^ f) ≠ (3, 2))
    (P : Type) [Group P] [Finite P] [Group.IsPerfect P] (η : P →* SU σ₀ n)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center P) (hk : IsPGroup p η.ker) :
    η.ker = ⊥ := by
  rcases hp.out.eq_two_or_odd' with rfl | hpo
  · refine su_cover_trivial_of_psu hF (psu_odd_two_cover_trivial hF hf hn ho ?_) P η hη hC hk
    rintro rfl
    by_contra h
    obtain rfl : f = 1 := by omega
    exact hq rfl
  · have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_odd_iff_even.2 even_two) hpo
    have hp3 : 3 ≤ p := by
      have := hp.out.two_le
      omega
    rcases (show n = 3 ∨ 5 ≤ n by
      obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.1 ho
      omega) with rfl | hn5
    · rcases (show p = 3 ∨ 3 < p by omega) with rfl | hp5
      · exact SUThreeCharThree.su_three_char_three_cover_trivial' hF η hη hC hk
      · obtain ⟨s, hs⟩ :=
          CFSG.RankThree.CentralLiftU.exists_section_SU_three_large hF hp2 hp.out hp5 hη hC hk
        exact ker_eq_bot_of_section hC hs
    · by_cases hq5 : 5 ≤ p ^ f
      · obtain ⟨r, rfl⟩ : ∃ r, n = 2 * r + 1 := ⟨n / 2, by
          obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.1 ho
          omega⟩
        exact su_cover_trivial_of_psu hF (fun P _ _ _ η hη hC hk =>
          (CFSG.LocalAnalysis.ComponentInitial.odd_odd_dimensional_unitary_catalog_perfect_central_p_cover_trivial
            η hη hC hp2 hk (by omega) hq5 (lieModel_statedProj_SU hF hf hn hq)).1) P η hη hC hk
      · have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
        obtain rfl : p = 3 := by
          obtain ⟨k, hk⟩ := hpo
          omega
        obtain rfl : f = 1 := by
          by_contra h
          have : 3 ^ 2 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        exact SUOddFieldThree.su_odd_field_three_cover_trivial hF (Nat.not_even_iff_odd.1 ho) η hη
          hC hk

theorem su_odd_cover_trivial
    (hF : Nat.card F = (p ^ f) ^ 2) (hf : 1 ≤ f) {n : ℕ} (hn : 3 ≤ n) (ho : ¬ Even n)
    (hq : (n, p ^ f) ≠ (3, 2))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (P : Type) [Group P] [Finite P] [Group.IsPerfect P]
    (η : P →* SU σ₀ n) (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center P)
    (hk : IsPGroup ℓ η.ker) : η.ker = ⊥ := by
  by_cases hℓp : ℓ = p
  · rw [hℓp] at hk
    exact su_odd_cover_trivial_char hF hf hn ho hq P η hη hC hk
  · obtain ⟨s, hs⟩ := su_odd_exists_section_of_ne hF hf hℓ hℓp hn ho hη hC hk
    exact ker_eq_bot_of_section hC hs

theorem isPerfect_statedSU_odd (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n)
    (hq : (n, p ^ f) ≠ (3, 2)) : Group.IsPerfect (StatedSU n (p ^ f) F) := by
  have h := CFSG.ClassicalGroups.Unitary.isPerfect_SUid
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF) (n := n) hn
    fun h3 => CFSG.ClassicalGroups.Unitary.exists_norm_ne_one hF fun h2 => hq (by rw [h3, h2])
  rw [SUid_eq_statedSU hF n] at h
  exact h

theorem statedSU_odd_exists_section_of_central
    (hF : Nat.card F = (p ^ f) ^ 2) (hf : 1 ≤ f) {n : ℕ} (hn : 3 ≤ n) (ho : ¬ Even n)
    (hq : (n, p ^ f) ≠ (3, 2))
    {E : Type} [Group E] [Finite E] {π : E →* StatedSU n (p ^ f) F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ s : StatedSU n (p ^ f) F →* E, ∀ g, π (s g) = g := by
  have := isPerfect_statedSU_odd hF hn hq
  refine PrimeCover.exists_section_of_forall_prime (fun ℓ hℓ P _ _ _ η hη hC hk => ?_) E π hπ hcen
  set ψ := equivStatedSU hF n
  have hker : (ψ.symm.toMonoidHom.comp η).ker = η.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ ψ.symm.injective]
  rw [← hker]
  exact su_odd_cover_trivial hF hf hn ho hq ℓ hℓ P _ (ψ.symm.surjective.comp hη)
    (hker ▸ hC) (hker ▸ hk)

theorem psu_odd_hopfMultiplier
    (hF : Nat.card F = (p ^ f) ^ 2) (hf : 1 ≤ f) {n : ℕ} (hn : 3 ≤ n) (ho : ¬ Even n)
    (hq : (n, p ^ f) ≠ (3, 2)) :
    commutator (StatedProj (StatedSU n (p ^ f) F)) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSU n (p ^ f) F)) ≃*
        Multiplicative (ZMod (Nat.gcd n (p ^ f + 1)))) := by
  set H := StatedSU n (p ^ f) F
  set Z := (StatedScalars (Fin n) F).subgroupOf H
  set q : H →* StatedProj H := QuotientGroup.mk' Z
  have hq' : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = Z := QuotientGroup.ker_mk' _
  have hZc : Z ≤ Subgroup.center H := fun z hz => by
    have hz' : (z : GL (Fin n) F) ∈ Subgroup.center (GL (Fin n) F) := by
      have h1 := Subgroup.mem_subgroupOf.1 hz
      rwa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    exact Subgroup.mem_center_iff.2 fun h => Subtype.ext (Subgroup.mem_center_iff.1 hz' h)
  have : Group.IsPerfect H := isPerfect_statedSU_odd hF hn hq
  have hperf : Group.IsPerfect (StatedProj H) := Group.IsPerfect.ofSurjective hq'
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have : Finite (CFSG.RankThree.PerfectCover.HopfCover (StatedProj H)) :=
    CFSG.RankThree.PerfectCover.finite_hopfCover hperf
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier (StatedProj H) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq' (hker ▸ hZc)
      fun π hπ hcen => statedSU_odd_exists_section_of_central hF hf hn ho hq hπ hcen)
  have hcard : Nat.card Z = Nat.gcd n (p ^ f + 1) :=
    (CFSG.LinearGroups.unitary_scalar_kernel hp.out hF (by omega)).2.2
  have hcyc : IsCyclic Z := (isCyclic_scalars_statedSU hF (by omega)).1
  rw [← hcard]
  exact ⟨(CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans ((MulEquiv.subgroupCongr hker).trans (zmodCyclicMulEquiv hcyc).symm))⟩

end CFSG.LieType.Steinberg.CentralExt.SUOdd
