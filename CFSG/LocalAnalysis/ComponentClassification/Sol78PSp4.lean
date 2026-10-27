module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitTypeClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34Out
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldBasic
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LieType.Classical.SteinbergBLSymplectic

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup CFSG.Assembly.LowTwoRank

theorem pow_four_dvd_two_mul_card_statedProj (F : Type) [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) :
    Nat.card F ^ 4 ∣ 2 * Nat.card (StatedProj (StatedSp 2 F)) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F))
  have h2 : Nat.card ↥((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)) = 2 := by
    rw [← Subgroup.card_map_of_injective (StatedSp 2 F).subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm,
      CFSG.LieType.Classical.card_statedSp_inf_statedScalars (by norm_num),
      CFSG.LieType.Classical.card_sq_eq_one_units]
    obtain ⟨m, hm⟩ := hodd
    rw [hm, show 2 * m + 1 - 1 = 2 * m by omega, Nat.gcd_mul_right_right]
  have h3 := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := F) 2
  rw [h2] at h1
  refine ⟨∏ j ∈ Finset.Icc 1 2, (Nat.card F ^ (2 * j) - 1), ?_⟩
  rw [mul_comm 2, ← h1, h3, show (2 : ℕ) ^ 2 = 4 by norm_num]

theorem not_exists_statedProjSp_of_card {X : Type*} [Group X]
    (h : ∀ q : ℕ, Odd q → 3 ≤ q → ¬ q ^ 4 ∣ 2 * Nat.card X) :
    ¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
      Nonempty (X ≃* StatedProj (StatedSp 2 K)) := by
  rintro ⟨K, _, _, hodd, ⟨e⟩⟩
  have hq : 3 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    obtain ⟨m, hm⟩ := hodd
    omega
  apply h _ hodd hq
  rw [Nat.card_congr e.toEquiv]
  exact pow_four_dvd_two_mul_card_statedProj K hodd

theorem not_psp4_of_l34 {G : Type} [Group G]
    {L : Subgroup G} (h : GrSLit.IsL34Type (↥L ⧸ Open.fusionZStar ↥L)) :
    ¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
      Nonempty (↥L ⧸ Open.fusionZStar ↥L ≃* StatedProj (StatedSp 2 K)) := by
  obtain ⟨ψ⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel h
  have hcard : Nat.card (↥L ⧸ Open.fusionZStar ↥L) = 20160 := by
    rw [Nat.card_congr ψ.toEquiv, PSL3Four.card_S]
  refine not_exists_statedProjSp_of_card fun q hq h3 hdvd => ?_
  rw [hcard] at hdvd
  have hle : q ≤ 14 := by
    by_contra hq'
    have h1 : 15 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have h2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  obtain ⟨m, hm⟩ := hq
  interval_cases q <;> omega

theorem not_psp4_of_held {J : Type*} [Group J]
    (e : J ⧸ pPrimeCore 2 J ≃* Blueprint.NativeSporadic.He) :
    ¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
      Nonempty (J ⧸ Open.fusionZStar J ≃* StatedProj (StatedSp 2 K)) := by
  have : IsSimpleGroup Blueprint.NativeSporadic.He := Sporadic.He.isSimpleGroup_He
  have hZHe : center Blueprint.NativeSporadic.He = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Blueprint.NativeSporadic.He) with
      h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := GrSLit.exists_mul_ne_held
      have hb : b ∈ center Blueprint.NativeSporadic.He := by rw [h]; exact mem_top b
      exact hab (mem_center_iff.mp hb a)
  have hZ : center (J ⧸ pPrimeCore 2 J) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hez : e z ∈ center Blueprint.NativeSporadic.He := by
      rw [mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz) g']
    rw [hZHe, mem_bot] at hez
    rw [mem_bot]
    exact e.injective (by rw [hez, map_one])
  have hZstar : Open.fusionZStar J = pPrimeCore 2 J := (fusionZStar_eq_iff J).mpr hZ
  have hcard : Nat.card (J ⧸ Open.fusionZStar J) = 4030387200 := by
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZstar).toEquiv,
      Nat.card_congr e.toEquiv, Sporadic.He.card_He]
  refine not_exists_statedProjSp_of_card fun q hq h3 hdvd => ?_
  rw [hcard] at hdvd
  have hodd4 : Odd (q ^ 4) := hq.pow
  have hdvd' : q ^ 4 ∣ 3935925 := by
    have hcop : Nat.Coprime (q ^ 4) (2 ^ 11) :=
      Nat.Coprime.pow_right 11 (Nat.coprime_two_right.mpr hodd4)
    have h2 : q ^ 4 ∣ 2 ^ 11 * 3935925 := by
      rw [show (2 : ℕ) ^ 11 * 3935925 = 2 * 4030387200 by norm_num]
      exact hdvd
    exact hcop.dvd_of_dvd_mul_left h2
  have hle : q ≤ 44 := by
    by_contra hq'
    have h1 : 45 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have h2 := Nat.le_of_dvd (by norm_num) hdvd'
    omega
  obtain ⟨m, hm⟩ := hq
  interval_cases q <;> omega

end CFSG.ComponentClassification.Sol78
