module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossOmega
import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossPSL
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Cycle
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieDispatch

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.CrossOmega

theorem dichLieCross_PSp : DichLieCrossAt .PSp := by
  intro K _ _ _ _ n ℓ f hadm hmodel hℓ3 _
  obtain ⟨_, F, _, _, hF, ⟨e⟩⟩ := hmodel.statedClassicalModel (by simp [classicalTags])
  have hℓ : ℓ.Prime := hadm.1
  have hn : 1 ≤ n := by have := hadm.2.2.1; omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := Fintype.ofFinite F
  have hF3 : ¬ 3 ∣ Fintype.card F :=
    not_dvd_card_of_card_eq_pow Nat.prime_three hℓ (Ne.symm hℓ3) hF
  have hSp : ThreeLocal (CFSG.Open.StatedSp n F) :=
    threeLocal_of_sigma (PSLCross.one_le_padicValNat_card Nat.prime_three hF3)
      (fun P => CFSG.GroupTheory.WeirSylow.sylow_Sp (by decide) F hF3 n P)
  refine DichThreeLieAt.of_mulEquiv e (dichThreeLieAt_of_threeLocal ?_)
  refine ThreeLocal.of_surjective_coprime_ker (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) ?_ hSp
  refine not_dvd_card_ker_of_sq Nat.prime_three (by norm_num) _ fun x hx => ?_
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hx)
  have hc2 : c ^ 2 = 1 :=
    (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff hn c).1 (by rw [hc]; exact x.2)
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hc, ← map_pow, hc2, map_one, Subgroup.coe_one]

section Transfer

open CFSG.Open CFSG.ClassicalGroups.Orthogonal Module QuadraticMap

theorem threeLocal_projOmega {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Q : QuadraticForm F (ι → F)} {Q₀ : (ι → F) → F} (hQ0 : ⇑Q = Q₀)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F (ι → F), finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hO : ThreeLocal ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) :
    ThreeLocal (StatedProj (StatedOmega Q₀)) := by
  classical
  obtain ⟨-, -, -, -, -, hsq', -, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hsq : ∀ g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q),
      g ^ 2 ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := fun g =>
    mem_commutator_of_coe_mem (by simpa using hsq' (g : (ι → F) ≃ₗ[F] (ι → F)) g.2)
  haveI : Nontrivial (ι → F) := by
    obtain ⟨T, hT3, -⟩ := hT
    refine Module.nontrivial_of_finrank_pos (R := F) ?_
    have := Submodule.finrank_le T
    omega
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO'
  let Θ₁ : ↥O →* GL ι F := (toLinEquiv ι F).symm.toMonoidHom.comp O.subtype
  have hΘ₁ : ∀ x : ↥O, toLinEquiv ι F (Θ₁ x) = (x : (ι → F) ≃ₗ[F] (ι → F)) := fun x =>
    MulEquiv.apply_symm_apply _ _
  have hmemΩ : ∀ A : GL ι F, A ∈ StatedOmega Q₀ ↔ toLinEquiv ι F A ∈ ⁅O, O⁆ := fun A => by
    rw [statedOmega_eq_comap hQ0, Subgroup.mem_comap]
    rfl
  have hΘ₁Ω : ∀ x ∈ commutator ↥O, Θ₁ x ∈ StatedOmega Q₀ := by
    intro x hx
    rw [hmemΩ, hΘ₁]
    have : (x : (ι → F) ≃ₗ[F] (ι → F)) ∈ (commutator ↥O).map O.subtype := ⟨x, hx, rfl⟩
    rwa [Subgroup.map_subtype_commutator] at this
  let Θ₂ : ↥(commutator ↥O) →* ↥(StatedOmega Q₀) :=
    (Θ₁.comp (commutator ↥O).subtype).codRestrict (StatedOmega Q₀) (fun x => hΘ₁Ω x x.2)
  let pj : ↥(commutator ↥O) →* StatedProj (StatedOmega Q₀) :=
    (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf (StatedOmega Q₀))).comp Θ₂
  have hker : ∀ x : ↥(commutator ↥O), pj x = 1 → x ^ 2 = 1 := by
    intro x hx
    have h1 : Θ₂ x ∈ (StatedScalars ι F).subgroupOf (StatedOmega Q₀) :=
      (QuotientGroup.eq_one_iff _).1 hx
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : ((x : ↥O) : (ι → F) ≃ₗ[F] (ι → F)) ∈ scalars F (ι → F) := by
      have := (mem_statedScalars_iff _).1 h1
      rwa [show ((Θ₂ x : ↥(StatedOmega Q₀)) : GL ι F) = Θ₁ (x : ↥O) from rfl, hΘ₁] at this
    obtain ⟨a₀, ha₀⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hQ
    obtain ⟨c, hc, hcv⟩ :=
      CFSG.RankThree.Classical.exists_sq_eq_one_of_mem_scalars h2 (x : ↥O).2 ha₀
    apply Subtype.ext
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one]
    refine LinearEquiv.ext fun v => ?_
    rw [pow_two, LinearEquiv.mul_apply, hcv v, map_smul, hcv v, smul_smul, ← _root_.sq, hc,
      one_smul]
    rfl
  have hsurj : Function.Surjective pj := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    have hz : toLinEquiv ι F (z : GL ι F) ∈ ⁅O, O⁆ := (hmemΩ _).1 z.2
    rw [← Subgroup.map_subtype_commutator] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    refine ⟨⟨x, hx⟩, ?_⟩
    have h1 : Θ₂ ⟨x, hx⟩ = z := Subtype.ext (by
      show Θ₁ x = (z : GL ι F)
      apply (toLinEquiv ι F).injective
      rw [hΘ₁]
      exact hxz)
    show QuotientGroup.mk' _ (Θ₂ ⟨x, hx⟩) = _
    rw [h1]
    rfl
  have hN : ThreeLocal ↥(commutator ↥O) :=
    ThreeLocal.of_normal_coprime_index (commutator ↥O)
      (not_dvd_index_commutator_of_sq Nat.prime_three (by norm_num) hsq) hO
  exact ThreeLocal.of_surjective_coprime_ker pj hsurj
    (not_dvd_card_ker_of_sq Nat.prime_three (by norm_num) pj hker) hN

end Transfer

open CFSG.GroupTheory.WeirSylow Module

theorem dichLieCross_POmegaOdd : DichLieCrossAt .POmegaOdd := by
  intro K _ _ _ _ n ℓ f hadm hmodel hℓ3 _
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmodel.statedClassicalModel (by decide)
  have hn : 3 ≤ n := hadm.2.2.1
  have hℓ : ℓ.Prime := hadm.1
  have hℓ2 : ℓ ≠ 2 := hadm.2.2.2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP F ℓ := charP_of_card_eq_prime_pow (p := ℓ) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have h2 : ringChar F ≠ 2 := by rw [ringChar.eq F ℓ]; exact hℓ2
  have hpq : ¬ 3 ∣ Fintype.card F := not_dvd_card_of_card_eq_pow Nat.prime_three hℓ (Ne.symm hℓ3) hF
  obtain ⟨hQnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadOdd (K := F) (n := n)
    (Ring.two_ne_zero h2) hn
  have hdim : finrank F (Fin n ⊕ Fin n ⊕ Unit → F) = 2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  obtain ⟨N, hN⟩ := exists_sigmaModel_sylow_orthogonal_odd (p := 3) (by norm_num)
    (Nat.odd_iff.2 (FiniteField.odd_card_of_char_ne_two h2)) hpq hdim hQnd
  exact DichThreeLieAt.of_mulEquiv e (dichThreeLieAt_of_threeLocal (threeLocal_projOmega
    (CFSG.LieType.Universal.Spin.coe_quadOdd n F) hQnd hT
    (threeLocal_of_sigma (one_le_weirA hpq) hN)))

theorem dichLieCross_POmegaPlus : DichLieCrossAt .POmegaPlus := by
  intro K _ _ _ _ n ℓ f hadm hmodel hℓ3 _
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmodel.statedClassicalModel (by decide)
  have hn : 4 ≤ n := hadm.2.2
  have hℓ : ℓ.Prime := hadm.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hpq : ¬ 3 ∣ Fintype.card F := not_dvd_card_of_card_eq_pow Nat.prime_three hℓ (Ne.symm hℓ3) hF
  obtain ⟨hQnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := F) (n := n)
    (by omega)
  have hdim : finrank F (Fin n ⊕ Fin n → F) = 2 * n := finrank_quadPlus_space n
  obtain ⟨N, hN⟩ := exists_sigmaModel_sylow_orthogonal_even (p := 3) (by norm_num) hpq
    (by omega) hdim hQnd (ε := 1) (Or.inl ⟨rfl, isPlusType_quadPlus F n⟩)
  exact DichThreeLieAt.of_mulEquiv e (dichThreeLieAt_of_threeLocal (threeLocal_projOmega
    (CFSG.LieType.Universal.Spin.coe_quadPlus n F) hQnd hT
    (threeLocal_of_sigma (one_le_weirA hpq) hN)))

theorem dichLieCross_POmegaMinus : DichLieCrossAt .POmegaMinus := by
  intro K _ _ _ _ n ℓ f hadm hmodel hℓ3 _
  obtain ⟨-, F, _, _, hF, b, c, hirr, ⟨e⟩⟩ := hmodel.statedClassicalModel (by decide)
  have hn : 4 ≤ n := hadm.2.2
  have hℓ : ℓ.Prime := hadm.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hpq : ¬ 3 ∣ Fintype.card F := not_dvd_card_of_card_eq_pow Nat.prime_three hℓ (Ne.symm hℓ3) hF
  obtain ⟨hQnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := F) (n := n) hn
    hirr
  have hdim : finrank F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) = 2 * n :=
    finrank_quadMinus_space (by omega)
  obtain ⟨N, hN⟩ := exists_sigmaModel_sylow_orthogonal_even (p := 3) (by norm_num) hpq
    (by omega) hdim hQnd (ε := -1) (Or.inr ⟨rfl, isMinusType_quadMinus (by omega) hirr⟩)
  exact DichThreeLieAt.of_mulEquiv e (dichThreeLieAt_of_threeLocal (threeLocal_projOmega
    (CFSG.LieType.Universal.Spin.coe_quadMinus n F b c) hQnd hT
    (threeLocal_of_sigma (one_le_weirA hpq) hN)))

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
