module

public import CFSG.ClassicalInvolution.PerfectCase.Basic
public import CFSG.ClassicalInvolution.SubnormalCommutator
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open
open scoped commutatorElement

theorem normal_pGroup_le_center_of_isQuasisimple {K : Type*} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple (K ⧸ classicalInvolutionOddCore K))
    (M : Subgroup K) [M.Normal] (hM : IsPGroup 2 M) : M ≤ Subgroup.center K := by
  let π : K →* K ⧸ classicalInvolutionOddCore K := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hMn : (M.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq (M.map π) with
    h | h
  · intro m hm
    rw [Subgroup.mem_center_iff]
    intro k
    have hc : ⁅m, k⁆ ∈ M := by
      rw [commutatorElement_def]
      have := Subgroup.Normal.conj_mem inferInstance m⁻¹ (M.inv_mem hm) k
      simpa [mul_assoc] using M.mul_mem hm this
    have hπc : π ⁅m, k⁆ = 1 := by
      have hcentral := Subgroup.mem_center_iff.mp (h (Subgroup.mem_map_of_mem π hm)) (π k)
      rw [map_commutatorElement, commutatorElement_def, ← hcentral]
      group
    have hker : Odd (Nat.card π.ker) := by
      rw [QuotientGroup.ker_mk']
      exact QuaternionStructure.odd_natCard_oddCore K
    have hinj := QuaternionStructure.injective_domRestrict_of_odd_ker π hker M hM
    have hc1 : ⁅m, k⁆ = 1 :=
      congrArg Subtype.val (hinj (a₁ := ⟨⁅m, k⁆, hc⟩) (a₂ := 1) (by simpa using hπc))
    rw [commutatorElement_eq_one_iff_mul_comm] at hc1
    exact hc1.symm
  · exfalso
    apply not_isSolvable_of_open_isQuasisimple hq
    have hp : IsPGroup 2 (K ⧸ classicalInvolutionOddCore K) := by
      intro x
      have hx : x ∈ M.map π := by rw [h]; exact Subgroup.mem_top x
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨j, hj⟩ := hM ⟨m, hm⟩
      refine ⟨j, ?_⟩
      have := congrArg (fun y : M => π y.1) hj
      simpa [← map_pow] using this
    have := hp.isNilpotent
    infer_instance

theorem eq_top_of_forall_odd_orderOf_mem {K : Type*} [Group K] [Finite K]
    (hperf : commutator (K ⧸ classicalInvolutionOddCore K) = ⊤)
    (A : Subgroup K) [A.Normal] (hA : ∀ x : K, Odd (orderOf x) → x ∈ A) : A = ⊤ := by
  have hOA : classicalInvolutionOddCore K ≤ A := by
    intro o ho
    refine hA o ?_
    have hodd : Odd (Nat.card (classicalInvolutionOddCore K)) :=
      QuaternionStructure.odd_natCard_oddCore K
    exact Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ ho)
  have hp : IsPGroup 2 (K ⧸ A) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨a, ?_⟩
    have hodd : Odd (orderOf (x ^ 2 ^ a)) := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hord⟩, hord,
        Nat.mul_div_cancel_left _ (by positivity)]
      exact hm
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hA _ hodd)
  have hsolv : Group.IsSolvable (K ⧸ A) := by
    have := hp.isNilpotent
    infer_instance
  let f : K ⧸ classicalInvolutionOddCore K →* K ⧸ A :=
    QuotientGroup.lift _ (QuotientGroup.mk' A) fun x hx =>
      (QuotientGroup.eq_one_iff x).mpr (hOA hx)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hcomm : commutator (K ⧸ A) = ⊤ := by
    have h1 : (commutator (K ⧸ classicalInvolutionOddCore K)).map f = ⊤ := by
      rw [hperf, ← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr hf
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf] at h1
    rw [commutator_def]
    exact h1
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x : K, x ∉ A := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.mpr fun x _ => h x)
  have hnt : Nontrivial (K ⧸ A) :=
    ⟨⟨QuotientGroup.mk x, 1, fun h => hx ((QuotientGroup.eq_one_iff x).mp h)⟩⟩
  have := Group.IsSolvable.commutator_lt_top_of_nontrivial (K ⧸ A)
  rw [hcomm] at this
  exact lt_irrefl _ this

theorem commute_of_odd_orderOf_of_isSubnormal {G : Type*} [Group G] [Finite G]
    {K C U : Subgroup G} (hK : IsSubnormal K C) (hUC : U ≤ C)
    (hCU : C ≤ Subgroup.normalizer (U : Set G)) (hU : IsPGroup 2 U)
    (hq : CFSG.Open.IsQuasisimple (K ⧸ classicalInvolutionOddCore K))
    {g : G} (hgK : g ∈ K) (hg : Odd (orderOf g)) : ∀ u ∈ U, u * g = g * u := by
  have hKC : K ≤ C := isSubnormal_le hK
  have hMc : ∀ m ∈ K ⊓ U, ∀ k ∈ K, m * k = k * m := by
    let M : Subgroup K := (K ⊓ U).subgroupOf K
    have hMn : M.Normal := by
      refine ⟨fun n hn k => ?_⟩
      have hn' : (n : G) ∈ K ⊓ U := hn
      have hU' : (k : G) * n * (k : G)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hCU (hKC k.2)) (n : G)).mp hn'.2
      exact ⟨K.mul_mem (K.mul_mem k.2 hn'.1) (K.inv_mem k.2), hU'⟩
    have hM : IsPGroup 2 M :=
      (hU.to_le inf_le_right).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
    intro m hm k hk
    have hmM : (⟨m, hm.1⟩ : K) ∈ M := hm
    have := normal_pGroup_le_center_of_isQuasisimple hq M hM hmM
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp this ⟨k, hk⟩).symm)
  intro u hu
  have hzK : Subgroup.zpowers g ≤ K := Subgroup.zpowers_le.mpr hgK
  have h1 : ⁅U, Subgroup.zpowers g⁆ ≤ K ⊓ U :=
    commutator_zpowers_le_of_isSubnormal hK hUC hCU hU hgK hg
  have h2 : ⁅K ⊓ U, Subgroup.zpowers g⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro m hm h hh
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hMc m hm h (hzK hh)
  have hRW : Subgroup.zpowers g ≤ Subgroup.normalizer (U : Set G) := hzK.trans (hKC.trans hCU)
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers g)) (Nat.card U) := by
    obtain ⟨k, hk⟩ := hU.exists_card_eq
    rw [Nat.card_zpowers, hk]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hg)
  have h3 : ⁅U, Subgroup.zpowers g⁆ ≤ ⁅⁅U, Subgroup.zpowers g⁆, Subgroup.zpowers g⁆ :=
    commutator_le_commutator_commutator_of_coprime U (Subgroup.zpowers g) hRW hcop
  have h4 : ⁅U, Subgroup.zpowers g⁆ = ⊥ :=
    le_bot_iff.mp (h3.trans ((Subgroup.commutator_mono h1 le_rfl).trans h2.le))
  have h5 : ⁅u, g⁆ ∈ ⁅U, Subgroup.zpowers g⁆ :=
    Subgroup.commutator_mem_commutator hu (Subgroup.mem_zpowers g)
  rw [h4, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h5
  exact h5

end CFSG.ClassicalInvolution
