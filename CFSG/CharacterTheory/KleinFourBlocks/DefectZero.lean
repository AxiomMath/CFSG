module

public import CFSG.CharacterTheory.BrauerCharacters.InertialQuotient
public import CFSG.CharacterTheory.BrauerCharacters.MajorFixedPoints
public import CFSG.CharacterTheory.BlockSectionOrthogonality.LocalCoefficients
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.ProductCharacterFormula
public import CFSG.CharacterTheory.BrauerCharacters.Residue
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

open CFSG CFSG.BrauerThirdMainTheorem.Helpers CFSG.BrauerCharacters CFSG.LyonsUnitaryFour
  CFSG.BlockSectionOrthogonality.Helpers CFSG.TwoRankLowerBound.Helpers

namespace CFSG.KleinFourBlocks

section DefectZero

variable {L : Type} [Group L] [Fintype L] (m : Ideal BlocksAlgInt) [hm : m.IsMaximal]
  [h2 : CharP (BlocksAlgInt ⧸ m) 2]

omit [Fintype L] in
theorem idempotentCoeff_singleton (θ : L → ℂ) (g : L) :
    BlocksIdempotentCoeff L {θ} g = θ 1 / (Nat.card L : ℂ) * θ g⁻¹ := by
  unfold BlocksIdempotentCoeff
  rw [finsum_mem_singleton]

include h2 in
theorem degree_div_card_mem_localRing {d : ℕ} (hd : 2 ^ (Nat.card L).factorization 2 ∣ d) :
    (d : ℂ) / (Nat.card L : ℂ) ∈ BlocksLocalRing m := by
  have hp : Nat.Prime 2 := Nat.prime_two
  obtain ⟨d', hd'⟩ := hd
  obtain ⟨n, hn, hcop⟩ : ∃ n : ℕ, Nat.card L = 2 ^ (Nat.card L).factorization 2 * n ∧
      Nat.Coprime 2 n :=
    ⟨Nat.card L / 2 ^ (Nat.card L).factorization 2,
      (Nat.ordProj_mul_ordCompl_eq_self _ 2).symm, Nat.coprime_ordCompl hp Nat.card_pos.ne'⟩
  have hnodd : ¬ 2 ∣ n := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  generalize (Nat.card L).factorization 2 = a at hd' hn
  have hn_not : ((n : ℕ) : BlocksAlgInt) ∉ m := by
    intro hmem
    refine natCast_not_mem_localMaxIdeal (ideal := m) 2 hnodd ?_
    exact ⟨(n : BlocksAlgInt), 1, hmem, hm.isPrime.one_notMem, by simp⟩
  refine ⟨(d' : BlocksAlgInt), (n : BlocksAlgInt), hn_not, ?_⟩
  rw [hd', hn]
  push_cast
  have h2a : (2 : ℂ) ^ a ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [mul_div_mul_left _ _ h2a]

include h2 in
theorem admissible_singleton_of_defect_zero {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L)
    (hdeg : ∃ d : ℕ, θ 1 = d ∧ 2 ^ (Nat.card L).factorization 2 ∣ d) :
    BlocksAdmissible m L {θ} := by
  refine ⟨Set.singleton_subset_iff.mpr hθ, fun g => ?_⟩
  rw [idempotentCoeff_singleton]
  obtain ⟨d, hd, hdvd⟩ := hdeg
  rw [hd]
  exact localRing_mul_mem m hm (degree_div_card_mem_localRing m hdvd)
    (localRing_of_algInt m hm ⟨θ g⁻¹, (mem_integralClosure_iff ℤ ℂ).mpr (irr_integral hθ _)⟩)

include h2 in
theorem blockOf_eq_singleton_of_defect_zero {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L)
    (hdeg : ∃ d : ℕ, θ 1 = d ∧ 2 ^ (Nat.card L).factorization 2 ∣ d) :
    BlocksBlockOf m L θ = {θ} := by
  ext ψ
  constructor
  · rintro ⟨-, hA⟩
    exact (hA {θ} (admissible_singleton_of_defect_zero m hθ hdeg)).mp rfl
  · rintro rfl
    exact mem_blockOf_self m hθ

theorem centralChar_classCoefficients_mul_degree {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) (z : L) :
    BlocksCentralChar θ (classCoefficients (ConjClasses.mk z)) * θ 1 =
      (Nat.card L : ℂ) / (Nat.card (Subgroup.centralizer ({z} : Set L)) : ℂ) * θ z := by
  classical
  have h1 : θ 1 ≠ 0 := irr_degree_ne_zero hθ
  obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hθ
  have hc0 : (Nat.card (Subgroup.centralizer ({z} : Set L)) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  unfold BlocksCentralChar
  rw [div_mul_cancel₀ _ h1, finsum_eq_sum_of_fintype]
  have hsum : ∑ g : L, classCoefficients (ConjClasses.mk z) g * ρ.character g =
      ∑ g ∈ conjClassFinset z, ρ.character g := by
    rw [conjClassFinset, Finset.sum_filter]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold classCoefficients
    by_cases hg : IsConj z g
    · have hg' : ConjClasses.mk g = ConjClasses.mk z :=
        ConjClasses.mk_eq_mk_iff_isConj.mpr hg.symm
      simp only [hg', hg, ↓reduceIte, one_mul]
    · have hg' : ¬ ConjClasses.mk g = ConjClasses.mk z := fun h =>
        hg (ConjClasses.mk_eq_mk_iff_isConj.mp h).symm
      simp only [hg', hg, ↓reduceIte, zero_mul]
  rw [hsum]
  have hdata := character_conjClassFinset_sum (⟨V, ρ⟩ : FiniteComplexRepresentation L) z
  have hcard := card_conjClassFinset_mul z
  change ∑ g ∈ conjClassFinset z, ρ.character g = _ at hdata
  rw [hdata, ← hcard]
  field_simp

include h2 in
theorem blockDefect_bot_of_defect_zero {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L)
    (hdeg : ∃ d : ℕ, θ 1 = d ∧ 2 ^ (Nat.card L).factorization 2 ∣ d) :
    blockDefect 2 m θ ⊥ := by
  classical
  have hp2 : (2 : BlocksAlgInt) ∈ m := by
    have h0 : ((2 : ℕ) : BlocksAlgInt ⧸ m) = 0 := CharP.cast_eq_zero _ 2
    have h0' : (Ideal.Quotient.mk m) ((2 : ℕ) : BlocksAlgInt) = 0 := by
      rw [map_natCast]; exact h0
    exact_mod_cast Ideal.Quotient.eq_zero_iff_mem.mp h0'
  have hadm := admissible_singleton_of_defect_zero m hθ hdeg
  have hcen := admissible_central m hadm
  have hω : BlocksCentralChar θ (BlocksIdempotentCoeff L {θ}) ∉ BlocksLocalMaxIdeal m := by
    rw [centralChar_idempotentCoeff (Set.singleton_subset_iff.mpr hθ) hθ]
    simp only [Set.mem_singleton_iff, ite_true]
    exact localMaxIdeal_one_not m
  obtain ⟨y, hy, -⟩ := exists_coeff_not_mem_of_centralChar_not_mem (ideal := m) hθ hcen hω
  rw [idempotentCoeff_singleton] at hy
  obtain ⟨d, hd, hdvd⟩ := hdeg
  have hu1 : θ 1 / (Nat.card L : ℂ) ∈ BlocksLocalRing m := by
    rw [hd]; exact degree_div_card_mem_localRing m hdvd
  have ht : θ y⁻¹ ∈ BlocksLocalRing m :=
    localRing_of_algInt m hm ⟨θ y⁻¹, (mem_integralClosure_iff ℤ ℂ).mpr (irr_integral hθ _)⟩
  have hu1_not : θ 1 / (Nat.card L : ℂ) ∉ BlocksLocalMaxIdeal m :=
    fun h => hy (localMaxIdeal_mul_localRing m hm h ht)
  have ht_not : θ y⁻¹ ∉ BlocksLocalMaxIdeal m := fun h => hy (by
    rw [mul_comm]; exact localMaxIdeal_mul_localRing m hm h hu1)
  have hu1inv : (θ 1 / (Nat.card L : ℂ))⁻¹ ∈ BlocksLocalRing m := localRing_inv_of_not_mem m hu1 hu1_not
  have hu1inv_not : (θ 1 / (Nat.card L : ℂ))⁻¹ ∉ BlocksLocalMaxIdeal m := by
    intro h
    apply localMaxIdeal_one_not m
    have hne : θ 1 / (Nat.card L : ℂ) ≠ 0 := by
      intro h0; exact hu1_not (h0 ▸ localMaxIdeal_zero m hm)
    have := localMaxIdeal_mul_localRing m hm h hu1
    rwa [inv_mul_cancel₀ hne] at this
  set z : L := y⁻¹ with hz
  set C : ℕ := Nat.card (Subgroup.centralizer ({z} : Set L)) with hC
  have hC0 : (C : ℂ) ≠ 0 := by rw [hC]; exact_mod_cast Nat.card_pos.ne'
  have hωR : BlocksCentralChar θ (classCoefficients (ConjClasses.mk z)) ∈ BlocksLocalRing m :=
    centralChar_localRing m hm hθ (classCoefficients_central m hm _)
  have hθ1 : θ 1 ≠ 0 := irr_degree_ne_zero hθ
  have hmain : (C : ℂ) * BlocksCentralChar θ (classCoefficients (ConjClasses.mk z)) =
      (θ 1 / (Nat.card L : ℂ))⁻¹ * θ z := by
    have h := centralChar_classCoefficients_mul_degree hθ z
    rw [← hC] at h
    have h' : (C : ℂ) * (BlocksCentralChar θ (classCoefficients (ConjClasses.mk z)) * θ 1) =
        (Nat.card L : ℂ) * θ z := by
      rw [h]; field_simp
    rw [inv_div, div_mul_eq_mul_div, eq_div_iff hθ1]
    linear_combination h'
  have hmain_not : (C : ℂ) * BlocksCentralChar θ (classCoefficients (ConjClasses.mk z)) ∉
      BlocksLocalMaxIdeal m := by
    rw [hmain]
    exact localMaxIdeal_mul_not_mem m hm hu1inv ht hu1inv_not ht_not
  have hCodd : ¬ 2 ∣ C := by
    intro hdv
    apply hmain_not
    exact localMaxIdeal_mul_localRing m hm (localMaxIdeal_natCast_of_dvd m hm 2 hp2 hdv) hωR
  have hωnot : BlocksCentralChar θ (classCoefficients (ConjClasses.mk z)) ∉
      BlocksLocalMaxIdeal m := by
    intro h
    apply hmain_not
    rw [mul_comm]
    exact localMaxIdeal_mul_localRing m hm h (localRing_natCast m hm C)
  have hfac : C.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hCodd
  obtain ⟨S⟩ : Nonempty (Sylow 2 (Subgroup.centralizer ({z} : Set L))) := inferInstance
  have hfac' : (Nat.card (Subgroup.centralizer ({z} : Set L))).factorization 2 = 0 := hfac
  have hS : Nat.card (S : Subgroup (Subgroup.centralizer ({z} : Set L))) = 1 := by
    rw [Sylow.card_eq_multiplicity, hfac', pow_zero]
  have hbot : (S : Subgroup (Subgroup.centralizer ({z} : Set L))) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ hS
  refine ⟨⟨ConjClasses.mk z, ⟨z, rfl, S, ?_⟩, hωnot⟩, ?_⟩
  · rw [hbot]; exact Subgroup.map_bot _
  · intro K _ other _
    exact ⟨1, fun x hx => by
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_bot] at ha
      subst ha
      simp⟩

end DefectZero

end CFSG.KleinFourBlocks
