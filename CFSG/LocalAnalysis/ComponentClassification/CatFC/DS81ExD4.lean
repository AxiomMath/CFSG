module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTransport
public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Classes
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.CatFC.DS81.Ex

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.RankTwoExceptional.D4
  CFSG.ComponentClassification.RankTwoExceptional.Exc

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

theorem forall_d4Tuple {P : Kˣ → Prop} {x₀ x₁ x₂ x₃ : Kˣ} (h₀ : P x₀) (h₁ : P x₁) (h₂ : P x₂)
    (h₃ : P x₃) : ∀ i, P (d4Tuple x₀ x₁ x₂ x₃ i) := by
  intro i
  obtain ⟨n, hn⟩ := i
  have hn' : n < 4 := hn
  interval_cases n
  exacts [h₀, h₁, h₂, h₃]

theorem d4_exists_order_eightynine_commute [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ (σ (σ c)) = c) {ε : Kˣ} (hε : orderOf ε = 89) (hεσ : σ (ε : K) = ε)
    (hz : d4z K ∈ d4C K σ) (ht : d4t K σ ∈ d4C K σ) :
    ∀ y ∈ ([⟨d4z K, hz⟩, ⟨d4t K σ, ht⟩] : List ↥(d4C K σ)),
      ∃ w : ↥(d4C K σ), orderOf w = 89 ∧ Commute w y := by
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  have hεp : ε ^ 89 = 1 := hε ▸ pow_orderOf_eq_one ε
  have hz89 : ∀ x ∈ Subgroup.zpowers ε, x ^ 89 = 1 := fun x hx => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hεp, one_zpow]
  have hεz : ε ∈ Subgroup.zpowers ε := Subgroup.mem_zpowers ε
  have hε2 : ε ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hε] at this
    omega
  have hσu : Units.map σ.toRingHom.toMonoidHom ε = ε := Units.ext hεσ
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  ·
    refine ⟨⟨trialityOuterTorus K σ ε, trialityOuterTorus_mem_d4C σ hσ3 ε⟩, ?_, ?_⟩
    · rw [Subgroup.orderOf_mk, trialityOuterTorus_eq_rootDiagUnit]
      simp only [hσu]
      refine orderOf_rootDiagUnit_eq_prime_of_pow _ ?_ ⟨0, by decide⟩ ?_
      · exact forall_d4Tuple (P := fun x => x ^ 89 = 1)
          (hz89 _ (Subgroup.pow_mem _ hεz 2)) (hz89 _ (Subgroup.pow_mem _ hεz 2))
          (hz89 _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hεz hεz) hεz)))
          (hz89 _ (Subgroup.pow_mem _ hεz 2))
      · exact hε2
    · exact Subtype.ext (mul_inv_eq_iff_eq_mul.1 (ho_conj_d4x₆ (σ := σ) ε 1))
  ·
    have hmem : (ε : K) ∈ trialityFixedField K σ.toRingHom := (mem_trialityFixedField).2 hεσ
    have hne : (⟨(ε : K), hmem⟩ : ↥(trialityFixedField K σ.toRingHom)) ≠ 0 := fun h =>
      ε.ne_zero (congrArg Subtype.val h)
    let β : (trialityFixedField K σ.toRingHom)ˣ := Units.mk0 _ hne
    have hβ : trialityFixedUnit K σ β = ε := Units.ext rfl
    refine ⟨⟨trialityMiddleTorus K σ β, trialityMiddleTorus_mem_d4C σ hσ3 β⟩, ?_, ?_⟩
    · rw [Subgroup.orderOf_mk, trialityMiddleTorus_eq_rootDiagUnit, hβ]
      refine orderOf_rootDiagUnit_eq_prime_of_pow _ ?_ ⟨2, by decide⟩ ?_
      · exact forall_d4Tuple (P := fun x => x ^ 89 = 1)
          (hz89 _ (Subgroup.inv_mem _ hεz)) (hz89 _ (Subgroup.inv_mem _ hεz))
          (hz89 _ (Subgroup.pow_mem _ hεz 2)) (hz89 _ (Subgroup.inv_mem _ hεz))
      · exact hε2
    · exact Subtype.ext (mul_inv_eq_iff_eq_mul.1 (hm_conj_d4x₄ (σ := σ) β 1))

theorem lie23To89At_trialityD4 : Lie23To89At .trialityD4 := by
  intro X _ _ n f hadm hM τ hτ h23
  have hn : n = 0 := hadm.2.2
  subst hn
  have h11 : 11 ∣ f := eleven_dvd_of_twentythree_dvd_card (by simp) hadm hM
    (dvd_trans h23 (Subgroup.card_subgroup_dvd_card _))
  obtain ⟨-, K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hM.chevalleyExceptionalModel (by decide)
  have hcard1 : Nat.card K = (2 ^ f) ^ 3 := hcard
  haveI : CharP K 2 := charP_two_of_card_d4 hcard1
  obtain ⟨σE, rfl⟩ : ∃ σE : K ≃+* K, σE.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩,
      RingHom.ext fun _ => rfl⟩
  obtain ⟨E⟩ := nonempty_derivedCentralQuotient_equiv .D4 Nat.prime_two hadm.2.1 K hcard
    σE.toRingHom hσ
  have hσ3 : ∀ c, σE (σE (σE c)) = c := sigma_cube_of_card_d4 σE hcard1 hσ
  have hσ3' : σE.toRingHom ^ 3 = 1 := toRingHom_pow_three_d4 σE hσ3
  have hz : d4z K ∈ d4C K σE := (d4x_long_mem σE (map_one σE)).2.2
  have ht : d4t K σE ∈ d4C K σE := (d4x_short_mem σE hσ3' 1).2.2
  have h89 : 89 ∣ 2 ^ f - 1 := (eightynine_dvd_two_pow_sub_one_iff f).2 h11
  obtain ⟨ε, hε⟩ := exists_unit_orderOf_eightynine (K := K) (by
    rw [hcard1]
    have := Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 3
    rw [one_pow] at this
    exact h89.trans this)
  have hεσ : σE (ε : K) = ε := by
    have hεq : ε ^ (2 ^ f - 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hε ▸ h89)
    have h1 : (ε : K) ^ (2 ^ f - 1) = 1 := by
      have := congrArg Units.val hεq
      simpa using this
    have h2 : 2 ^ f - 1 + 1 = 2 ^ f := Nat.sub_add_cancel Nat.one_le_two_pow
    calc σE (ε : K) = (ε : K) ^ 2 ^ f := hσ _
      _ = (ε : K) ^ (2 ^ f - 1) * ε := by rw [← pow_succ, h2]
      _ = ε := by rw [h1, one_mul]
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  exact prime_dvd_card_centralizer_of_classesCover (e.trans E)
    (d4_classesCover σE hσ3 (z := ⟨d4z K, hz⟩) (t := ⟨d4t K σE, ht⟩) rfl rfl)
    (d4_exists_order_eightynine_commute σE hσ3 hε hεσ hz ht) hτ

end CFSG.ComponentClassification.CatFC.DS81.Ex
