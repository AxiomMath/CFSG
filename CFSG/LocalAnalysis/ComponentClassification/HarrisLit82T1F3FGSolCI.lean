module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1NoSLTwoSolv
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup
open scoped MatrixGroups

theorem oddLieType_or_m11_of_slTwoThree_fstar (hCI : GSLit.ClassicalInvolutionInput)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup ↥(Open.genFittingFStar X)]
    (hFnonab : ∃ a b : Open.genFittingFStar X, a * b ≠ b * a) {u : X} (hu : orderOf u = 2)
    {J : Subgroup X} (hJC : J ≤ centralizer {u})
    (hJs : (J.subgroupOf (centralizer {u})).IsSubnormal) (huJ : u ∈ J)
    (e₃ : ↥J ⧸ pPrimeCore 2 ↥J ≃* SL(2, ZMod 3)) :
    Blueprint.OddLieType ↥(Open.genFittingFStar X) ∨
      Blueprint.NativeSporadic.IsSporadic ↥(Open.genFittingFStar X) .M11 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := centralizer ({u} : Set X)
  have hsub : Open.IsSubnormal J C := by
    have h := Components.chain_of_mathlib_subnormal hJs
    have hmap : ∀ {H K : Subgroup ↥C}, Open.IsSubnormal H K →
        Open.IsSubnormal (H.map C.subtype) (K.map C.subtype) := by
      intro H K hHK
      induction hHK with
      | refl H => exact .refl _
      | @step H M K hHM hn _ ih =>
        refine .step (map_mono hHM) ?_ ih
        rw [normal_subgroupOf_iff (map_mono hHM)]
        rintro _ _ ⟨h, hh, rfl⟩ ⟨m, hm, rfl⟩
        exact ⟨m * h * m⁻¹, (normal_subgroupOf_iff hHM).mp hn h m hh hm, by simp⟩
    have h' := hmap h
    rwa [subgroupOf_map_subtype, inf_eq_left.mpr hJC, ← MonoidHom.range_eq_map,
      range_subtype] at h'
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥J) := inferInstance
  let π : ↥J →* SL(2, ZMod 3) := e₃.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥J))
  have hinj : ∀ s ∈ (S : Subgroup ↥J), π s = 1 → s = 1 := by
    intro s hs h1
    have hO : s ∈ pPrimeCore 2 ↥J := by
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ e₃.injective,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    have h2 : orderOf s ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk
      simpa using this
    have hodd : orderOf s ∣ Nat.card ↥(pPrimeCore 2 ↥J) := by
      rw [← Subgroup.orderOf_mk s hO]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(pPrimeCore 2 ↥J)) :=
      Nat.Coprime.pow_left _ pPrimeCore_coprime_card
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h2) hodd)
  set P := (S : Subgroup ↥J).map π
  let ρ : ↥(S : Subgroup ↥J) →* ↥P := π.subgroupMap (S : Subgroup ↥J)
  have hρi : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have := hinj s s.2 (congrArg Subtype.val hs)
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  let eSP : ↥(S : Subgroup ↥J) ≃* ↥P :=
    MulEquiv.ofBijective ρ ⟨hρi, π.subgroupMap_surjective _⟩
  have hcardJ : Nat.card ↥J = Nat.card ↥(pPrimeCore 2 ↥J) * 24 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥J), Nat.card_congr e₃.toEquiv,
      card_specialLinearGroup_two_zmod_three, mul_comm]
  have hS8 : Nat.card ↥(S : Subgroup ↥J) = 8 := by
    rw [Sylow.card_eq_multiplicity, hcardJ]
    have hodd : ¬ 2 ∣ Nat.card ↥(pPrimeCore 2 ↥J) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
    have hpos : Nat.card ↥(pPrimeCore 2 ↥J) ≠ 0 := Nat.card_pos.ne'
    rw [Nat.factorization_mul hpos (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hodd, zero_add,
      show (24 : ℕ) = 2 ^ 3 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
    simp
  have hP8 : Nat.card ↥P = 8 := by rw [← Nat.card_congr eSP.toEquiv, hS8]
  obtain ⟨eQ⟩ := nonempty_quaternion_of_card_eq_eight hP8
  have hwit : Open.classicalInvolutionWitness J := by
    left
    refine ⟨3, 1, inferInstance, by norm_num, by norm_num, ⟨?_⟩⟩
    exact ((QuotientGroup.quotientMulEquivOfEq (TBLit.classicalInvolutionOddCore_eq ↥J)).trans
      e₃).trans (ClassicalModels.specialLinearFieldEquiv (GaloisField.equivZmodP 3).symm.toRingEquiv
        (Fin 2))
  exact (hCI X hFnonab u hu J huJ hsub S ⟨3, le_rfl, ⟨eSP.trans eQ⟩⟩).1 hwit

theorem nonempty_quot_of_odd_index {J : Type} [Group J] [Finite J]
    (e : J ⧸ pPrimeCore 2 J ≃* SL(2, ZMod 3)) (R : Subgroup J) [R.Normal] (hR : Odd R.index) :
    Nonempty (↥R ⧸ pPrimeCore 2 ↥R ≃* QuaternionGroup 2) ∨
      Nonempty (↥R ⧸ pPrimeCore 2 ↥R ≃* SL(2, ZMod 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : J →* SL(2, ZMod 3) := e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 J)) with hπ
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : π.ker = pPrimeCore 2 J := by
    rw [hπ, MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  set φ := π.comp R.subtype with hφ
  have hφk : φ.ker = pPrimeCore 2 ↥R := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 R
      (Subgroup.Normal.isSubnormal inferInstance), hφ, ← MonoidHom.comap_ker, hπk]
    rfl
  have hr : φ.range = R.map π := by rw [hφ, MonoidHom.range_comp, range_subtype]
  let eR : ↥R ⧸ pPrimeCore 2 ↥R ≃* ↥(R.map π) :=
    (QuotientGroup.quotientMulEquivOfEq hφk.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hr))
  have hidx : Odd (R.map π).index := Odd.of_dvd_nat hR (Subgroup.index_map_dvd _ hπs)
  have hcard : Nat.card ↥(R.map π) * (R.map π).index = 24 := by
    rw [Subgroup.card_mul_index, card_specialLinearGroup_two_zmod_three]
  have hcases : Nat.card ↥(R.map π) = 8 ∨ Nat.card ↥(R.map π) = 24 := by
    have hdvd : (R.map π).index ∣ 24 := Dvd.intro_left _ hcard
    have hle : (R.map π).index ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨k, hk⟩ := hidx
    set i := (R.map π).index with hi
    set c := Nat.card ↥(R.map π)
    interval_cases i <;> omega
  rcases hcases with h8 | h24
  · obtain ⟨eQ⟩ := nonempty_quaternion_of_card_eq_eight h8
    exact .inl ⟨eR.trans eQ⟩
  · have htop : R.map π = ⊤ := Subgroup.eq_top_of_card_eq _ (by
      rw [h24, card_specialLinearGroup_two_zmod_three])
    exact .inr ⟨eR.trans ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)⟩

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
