module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Q8Target
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStarBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TightFamily

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3T.MFS
open scoped commutatorElement

section Subnormal

variable {G : Type} [Group G]

theorem commutator_le_of_isSubnormal {K H : Subgroup G} (hK : IsSubnormal K H) {A U : Subgroup G}
    (hidem : ⁅⁅U, A⁆, A⁆ = ⁅U, A⁆) : A ≤ K → U ≤ H → ⁅U, A⁆ ≤ K := by
  induction hK with
  | refl B =>
    intro hAB hUB
    rw [Subgroup.commutator_le]
    intro u hu a ha
    rw [commutatorElement_def]
    exact B.mul_mem (B.mul_mem (B.mul_mem (hUB hu) (hAB ha)) (B.inv_mem (hUB hu)))
      (B.inv_mem (hAB ha))
  | @step S M B hSM hSn _ ih =>
    intro hAS hUB
    have hV : ⁅U, A⁆ ≤ M := ih (hAS.trans hSM) hUB
    rw [← hidem, Subgroup.commutator_le]
    intro v hv a ha
    rw [commutatorElement_def]
    have h1 : v * a * v⁻¹ ∈ S := by
      have := hSn.conj_mem ⟨a, hSM (hAS ha)⟩ (by rw [Subgroup.mem_subgroupOf]; exact hAS ha)
        ⟨v, hV hv⟩
      rwa [Subgroup.mem_subgroupOf] at this
    exact S.mul_mem h1 (S.inv_mem (hAS ha))

variable [Finite G]

theorem card_dvd_eight_of_le {K W : Subgroup G} {z : G} (hz : IsClassicalMember3 K z)
    (hW : IsPGroup 2 W) (hWK : W ≤ K) : Nat.card W ∣ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW' : IsPGroup 2 (W.subgroupOf K) :=
    hW.of_equiv (Subgroup.subgroupOfEquivOfLe hWK).symm
  obtain ⟨P, hP⟩ := hW'.exists_le_sylow
  obtain ⟨e⟩ := Q3T6.quaternion_sylow_of_isClassicalMember3 hz P
  have hP8 : Nat.card (P : Subgroup K) = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv, ← hP8]
  exact Subgroup.card_dvd_of_le hP

theorem card_commutator_dvd_eight {K U : Subgroup G} {z x : G}
    (hz : IsClassicalMemberU (.sl2 3 1) K z) (hxK : x ∈ K) (hx3 : ∃ k : ℕ, x ^ 3 ^ k = 1)
    (hU : IsPGroup 2 U) (hUC : U ≤ Subgroup.centralizer ({z} : Set G))
    (hxU : x ∈ Subgroup.normalizer (U : Set G)) :
    Nat.card ↥⁅U, Subgroup.zpowers x⁆ ∣ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 (Subgroup.zpowers x) := by
    obtain ⟨k, hk⟩ := hx3
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have h3U : ¬ 3 ∣ Nat.card U := by
    obtain ⟨m, hm⟩ := hU.exists_card_eq
    rw [hm]
    intro hd
    have := Nat.prime_three.dvd_of_dvd_pow hd
    norm_num at this
  have hAU : Subgroup.zpowers x ≤ Subgroup.normalizer (U : Set G) := Subgroup.zpowers_le.mpr hxU
  have hidem :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three
      (Subgroup.zpowers x) U hA3 h3U hAU
  have hleK : ⁅U, Subgroup.zpowers x⁆ ≤ K :=
    commutator_le_of_isSubnormal hz.subnormal hidem (Subgroup.zpowers_le.mpr hxK) hUC
  have hleU : ⁅U, Subgroup.zpowers x⁆ ≤ U :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hAU
  exact card_dvd_eight_of_le (hz.toQ3 (by norm_num)) (hU.to_le hleU) hleK

end Subnormal

section Outer

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_three_elt_not_mem {K T : Subgroup Y} (h3 : memberIndex K T = 3) :
    ∃ x ∈ K, x ∉ T ∧ ∃ k : ℕ, x ^ 3 ^ k = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup K := T.subgroupOf K ⊔ classicalInvolutionOddCore K with hN
  have hNi : N.index = 3 := h3
  obtain ⟨P⟩ : Nonempty (Sylow 3 K) := inferInstance
  have hPN : ¬ (P : Subgroup K) ≤ N := by
    intro hle
    have hdvd : N.index ∣ (P : Subgroup K).index := Subgroup.index_dvd_of_le hle
    rw [hNi] at hdvd
    exact P.not_dvd_index hdvd
  obtain ⟨y, hyP, hyN⟩ := IsConcreteLE.not_le_iff_exists.mp hPN
  refine ⟨(y : Y), y.2, fun hyT => hyN ?_, ?_⟩
  · exact le_sup_left (a := T.subgroupOf K) (Subgroup.mem_subgroupOf.mpr hyT)
  · obtain ⟨k, hk⟩ := P.isPGroup' ⟨y, hyP⟩
    refine ⟨k, ?_⟩
    have h1 : (y : K) ^ 3 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have := congrArg Subtype.val h1
    simpa using this

end Outer

section Exit


@[expose] def D42OuterCommutator : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (T : Subgroup Y), T.Normal →
    Subgroup.centralizer (T : Set Y) = ⊥ → Odd T.index → Models.LieModel ↥T .POmegaPlus 4 2 1 →
    ∀ z ∈ T, orderOf z = 2 → ∀ x : Y, x ∉ T → (∃ k : ℕ, x ^ 3 ^ k = 1) → x * z = z * x →
      ∃ U : Subgroup Y, IsPGroup 2 U ∧ U ≤ Subgroup.centralizer ({z} : Set Y) ∧
        x ∈ Subgroup.normalizer (U : Set Y) ∧ ¬ Nat.card ↥⁅U, Subgroup.zpowers x⁆ ∣ 8

theorem frameExitD42_of_outerCommutator (h : D42OuterCommutator) : FrameExitD42 := by
  intro Y _ _ _ hnab _ Ω K hΩ hK _ _ _ hsup _ h3 hd4
  set T : Subgroup Y := genFittingFStar Y with hTdef
  have hTn : T.Normal := fstar_normal
  obtain ⟨hodd, -⟩ := odd_index_of_memberIndex_eq_three hsup h3
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  have hzT : z ∈ T := tightCore_le_of_odd_index hodd K (mem_tightCore_of_member hz)
  obtain ⟨x, hxK, hxT, hx3⟩ := exists_three_elt_not_mem h3
  have hxz : x * z = z * x := (hz.comm_of_mem hxK).symm
  obtain ⟨U, hU2, hUC, hxU, hnd⟩ :=
    h Y T hTn (centralizer_fstar_eq_bot hnab) hodd hd4 z hzT hz.orderOf_eq_two x hxT hx3 hxz
  exact hnd (card_commutator_dvd_eight hz hxK hx3 hU2 hUC hxU)

end Exit

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
