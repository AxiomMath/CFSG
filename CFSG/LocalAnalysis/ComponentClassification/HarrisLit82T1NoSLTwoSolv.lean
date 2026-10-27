module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.LieType.HighestRoot.CentLinearBasic
public import CFSG.ClassicalInvolution.OrderForm
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTheorem1
public import CFSG.LocalAnalysis.ComponentClassification.TBLitIntrinsic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open scoped MatrixGroups

theorem pow_twelve_SL23 : ∀ x : SL(2, ZMod 3), x ^ 12 = 1 := by
  decide

theorem nonempty_quaternion_of_card_eq_eight {P : Subgroup SL(2, ZMod 3)} (hP : Nat.card P = 8) :
    Nonempty (↥P ≃* QuaternionGroup 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ↥P := IsPGroup.of_card (n := 3) (by rw [hP]; norm_num)
  have hrank : DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions ↥P := by
    intro a b _
    have hneg : ∀ c : DisconnectedInvolutionGraph.Helpers.Involution ↥P,
        ((c : ↥P) : SL(2, ZMod 3)) = -1 := by
      intro c
      have hc := c.2
      rw [← Subgroup.orderOf_coe] at hc
      have hsq : ((c : ↥P) : SL(2, ZMod 3)) * ((c : ↥P) : SL(2, ZMod 3)) = 1 := by
        have h1 := pow_orderOf_eq_one ((c : ↥P) : SL(2, ZMod 3))
        rw [hc] at h1
        rw [← sq]
        exact h1
      rcases LieType.HighestRoot.eq_one_or_neg_one_of_mul_self_SL23 _ hsq with h | h
      · rw [h, orderOf_one] at hc
        exact absurd hc (by norm_num)
      · exact h
    exact Subtype.ext (Subtype.ext ((hneg a).trans (hneg b).symm))
  rcases DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion hP2 hrank with
    hcyc | ⟨e, -, ⟨φ⟩⟩
  · exfalso
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥P)
    rw [hP] at hg
    have h12 : orderOf ((g : ↥P) : SL(2, ZMod 3)) ∣ 12 :=
      orderOf_dvd_of_pow_eq_one (pow_twelve_SL23 _)
    rw [Subgroup.orderOf_coe, hg] at h12
    exact absurd h12 (by norm_num)
  · have hcard := Nat.card_congr φ.toEquiv
    rw [hP, Nat.card_eq_fintype_card, QuaternionGroup.card] at hcard
    have he : e = 1 := by
      have h2 : 2 ^ e = 2 ^ 1 := by omega
      exact Nat.pow_right_injective le_rfl h2
    subst he
    exact ⟨φ.symm⟩

theorem oddLieType_or_m11_of_intrinsic_slTwoThree
    (hCI : GSLit.ClassicalInvolutionInput) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {u : G} (hu : orderOf u = 2) {J : Subgroup G}
    (hJC : J ≤ centralizer {u}) (hJs : (J.subgroupOf (centralizer {u})).IsSubnormal)
    (huJ : u ∈ J) (e₃ : ↥J ⧸ pPrimeCore 2 ↥J ≃* SL(2, ZMod 3)) :
    Blueprint.OddLieType G ∨ Blueprint.NativeSporadic.IsSporadic G .M11 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := centralizer ({u} : Set G)
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
  let eF : Open.genFittingFStar G ≃* G :=
    (MulEquiv.subgroupCongr (StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup
      hnonab)).trans Subgroup.topEquiv
  have : IsSimpleGroup (Open.genFittingFStar G) := eF.isSimpleGroup
  have hFnonab : ∃ a b : Open.genFittingFStar G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨eF.symm a, eF.symm b, fun h => hab (eF.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  rcases (hCI G hFnonab u hu J huJ hsub S ⟨3, le_rfl, ⟨eSP.trans eQ⟩⟩).1 hwit with h | h
  · exact .inl ((ClassicalInvolution.oddLieType_congr eF).1 h)
  · exact .inr ((ClassicalInvolution.isSporadic_congr eF).1 h)

end CFSG.ComponentClassification.HarrisLit.T1
