module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15SecComp
import CFSG.ClassicalInvolution.Asc77.WP3FrameChain
import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
public import CFSG.ClassicalInvolution.Asc77.WP3FrameData

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected

namespace TwinVertex

section Images

variable {G : Type} [Group G] [Finite G]

theorem isUniqueInvolution_modOdd {c w : G} {M : Subgroup G}
    (hw : IsUniqueInvolution M w) (hwC : w ∈ Subgroup.centralizer ({c} : Set G)) :
    IsUniqueInvolution (modOdd c M) (oddQuotMk c ⟨w, hwC⟩) := by
  have hz : IsUniqueInvolution (M.subgroupOf (Subgroup.centralizer ({c} : Set G))) ⟨w, hwC⟩ := by
    refine ⟨hw.mem, fun h => hw.ne_one (congrArg Subtype.val h), Subtype.ext hw.sq, ?_⟩
    intro y hy hy2
    rcases hw.unique (y : G) hy (congrArg Subtype.val hy2) with h | h
    · left
      exact Subtype.ext h
    · right
      exact Subtype.ext h
  exact isUniqueInvolution_map_mk_of_odd
    (odd_natCard_inf (OddCore.odd_card ↥(Subgroup.centralizer ({c} : Set G))) _) hz

omit [Finite G] in
theorem oddQuotMk_mem_sup {c : G} {A A' : Subgroup G}
    (hA : A ≤ Subgroup.centralizer ({c} : Set G)) (hA' : A' ≤ Subgroup.centralizer ({c} : Set G))
    {x : G} (hx : x ∈ A ⊔ A') (hxC : x ∈ Subgroup.centralizer ({c} : Set G)) :
    oddQuotMk c ⟨x, hxC⟩ ∈ modOdd c A ⊔ modOdd c A' := by
  have h1 : (⟨x, hxC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
      A.subgroupOf (Subgroup.centralizer ({c} : Set G)) ⊔
        A'.subgroupOf (Subgroup.centralizer ({c} : Set G)) := by
    rw [← Subgroup.subgroupOf_sup hA hA']
    exact hx
  have h2 := Subgroup.mem_map_of_mem (oddQuotMk c) h1
  rwa [Subgroup.map_sup] at h2

end Images

section ExactCore

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem isUniqueInvolution_exactCore (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {M : Subgroup G} {w c : G}
    (hM : IsClassicalMember p f M w) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hcM : c ∈ trivialOnQuot M) : IsUniqueInvolution (exactCore c M) w := by
  have hw2 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hM.orderOf_eq_two, pow_two] at this
  have hw1 : w ≠ 1 := by
    intro h
    have := hM.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  exact ⟨mem_exactCore hM hc2 hcM, hw1, hw2, fun y hy hy2 =>
    eq_one_or_eq_of_mem_exactCore hM hp2 hq hy hy2⟩

end ExactCore

end TwinVertex

section Vertex

variable (p f : ℕ) [Fact p.Prime]

theorem twinFrameHyp51zCore : TwinFrameHyp51zCore p f := by
  intro G _ _ _ Ω K K' J z u t hs
  have hp : p ≠ 2 := hs.odd
  have hq : 5 ≤ p ^ f := hs.five
  have hΩ := hs.hyp
  have hd := hs.frame
  have hzK : IsUniqueInvolution K z := hd.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hd.hz hd.hK'
  have hKΩ : K ∈ Ω := hd.mem
  have hK'Ω : K' ∈ Ω := hd.hK'.1
  have hJΩ : J ∈ Ω := hd.hJ.1
  have hcK : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hKΩ hzK
  have hcK' : IsClassicalMember p f K' z := isClassicalMember_of_twin hΩ hK'Ω hzK'
  have hcJ : IsClassicalMember p f J t := isClassicalMember_of_twin hΩ hJΩ hd.ht
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) := isPGroup_zpowers_of_sq_eq_one hzK.sq
  have hnonab : ∃ x y : G, x * y ≠ y * x := exists_noncomm_of_isClassicalMember hcK
  have hnc : ¬ ({z} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one hnonab hzK.ne_one
  have hKtq : K ∈ tqMembers Ω z :=
    ⟨hKΩ, trivialOnQuot_of_isUniqueInvolution hp hq hΩ hKΩ hzK⟩
  have hK'tq : K' ∈ tqMembers Ω z :=
    ⟨hK'Ω, trivialOnQuot_of_isUniqueInvolution hp hq hΩ hK'Ω hzK'⟩
  have hJK : J ∈ omegaNbr Ω K := hd.hJ.2 K (mem_twinSet_self hKΩ hzK)
  obtain ⟨a, ha, hJa⟩ := tq_of_mem_omegaNbr hp hq hΩ.classical hKΩ hJK
  have haz : a = z := (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq ha).eq hzK
  have hJtq : J ∈ tqMembers Ω z :=
    ⟨hJΩ, (mem_trivialOnQuot_iff_actsTrivOnQuot).mpr (haz ▸ hJa)⟩
  have hzt : z * t = t * z := hd.comm_zt hp hΩ
  have hzu : z * u = u * z := hd.comm_zu
  have hBab : IsElemAbelian 2 (Subgroup.closure ({z, u, t} : Set G)) :=
    twinFrame_isElemAbelian hp hΩ hd
  have hcB : z ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hno : ∀ L : Subgroup (OddQuot z), CFSG.IsComponent L →
      MovedByAll (Subgroup.closure ({z, u, t} : Set G)) z L → False := by
    intro L hL hmov
    obtain ⟨Dsys⟩ := lieSystemAt_exactFamily hΩ.conjInvariant hΩ.classical hz2 hs.below hnc
      ⟨K, hKtq⟩
    obtain ⟨j, hLj, hJj⟩ := SecComp.exists_index_of_moved hp hq hΩ.conjInvariant hΩ.classical
      hz2 hBab hcB hzK.ne_one htB hd.ht.ne_one hd.t_ne_z hJtq hcJ Dsys hL hmov
    have hs' : SecData p f z (exactFamily Ω z) :=
      secData_exactFamily hΩ.conjInvariant hΩ.classical hz2 ⟨K, hKtq⟩
    have hmem : ∀ M ∈ tqMembers Ω z,
        exactCore z M ∈ centMembers (exactFamily Ω z) z := fun M hM =>
      ⟨exactCore_mem_exactFamily hM, exactCore_le_centralizer z M⟩
    have hJj' : modOdd z (exactCore z J) ≤
        (secComponentHom hs'.normalizes Dsys j).range := hLj ▸ hJj
    have hbad : ∀ M : Subgroup G, M ∈ tqMembers Ω z → IsClassicalMember p f M z →
        modOdd z (exactCore z M) ≤ (secComponentHom hs'.normalizes Dsys j).range → False := by
      intro M hMtq hcM hMj
      have hzmem : z ∈ exactCore z M := mem_exactCore hcM hz2 hMtq.2
      have hwM : Lemma52Proof.oddQuotSelf z ∈ modOdd z (exactCore z M) :=
        oddQuotMk_mem_modOdd hzmem ((Subgroup.mem_centralizer_singleton_iff.mpr rfl))
      have hw1 := Lemma52Proof.oddQuotSelf_ne_one hBab hcB hzK.ne_one
      have hwc : ∀ y ∈ (secComponentHom hs'.normalizes Dsys j).range,
          Lemma52Proof.oddQuotSelf z * y = y * Lemma52Proof.oddQuotSelf z := fun y _ =>
        (Lemma52Proof.oddQuotSelf_central z y).symm
      have hA1 := SecComp.tag_of_central hs' Dsys j (hmem M hMtq) hMj hwM hw1 hwc
      have h1 := SecComp.modOdd_eq_range_of_A1 hs' Dsys j (hmem M hMtq) hMj hA1
      have h2 := SecComp.modOdd_eq_range_of_A1 hs' Dsys j (hmem J hJtq) hJj' hA1
      have htJ : t ∈ exactCore z J := mem_exactCore hcJ hz2 hJtq.2
      have htC : t ∈ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
      have htbar : oddQuotMk z ⟨t, htC⟩ ∈ modOdd z (exactCore z M) := by
        rw [h1, ← h2]
        exact oddQuotMk_mem_modOdd htJ htC
      have huniq := TwinVertex.isUniqueInvolution_modOdd (c := z)
        (TwinVertex.isUniqueInvolution_exactCore hp hq hcM hz2 hMtq.2)
        ((Subgroup.mem_centralizer_singleton_iff.mpr rfl))
      have htsq : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨t, htC⟩ = 1 :=
        Subtype.ext hd.ht.sq
      have htt : oddQuotMk z ⟨t, htC⟩ * oddQuotMk z ⟨t, htC⟩ = 1 := by
        rw [← map_mul, htsq, map_one]
      rcases huniq.unique _ htbar htt with h | h
      · exact hd.ht.ne_one (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one htsq h))
      ·
        have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.mpr rfl
        have htz2 : (⟨t, htC⟩ * ⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) *
            (⟨t, htC⟩ * ⟨z, hzC⟩) = 1 :=
          Subtype.ext (by
            show t * z * (t * z) = 1
            exact mul_involution_of_commute hd.ht.sq hzK.sq hzt.symm)
        have hone : oddQuotMk z (⟨t, htC⟩ * ⟨z, hzC⟩) = 1 := by
          have hzz : (⟨z, hzC⟩ * ⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 :=
            Subtype.ext hzK.sq
          have h4 : oddQuotMk z ⟨z, hzC⟩ * oddQuotMk z ⟨z, hzC⟩ = 1 := by
            rw [← map_mul, hzz, map_one]
          calc oddQuotMk z (⟨t, htC⟩ * ⟨z, hzC⟩)
              = oddQuotMk z ⟨t, htC⟩ * oddQuotMk z ⟨z, hzC⟩ := map_mul _ _ _
            _ = oddQuotMk z ⟨z, hzC⟩ * oddQuotMk z ⟨z, hzC⟩ := by rw [h]
            _ = 1 := h4
        have h3 : t * z = 1 := congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one htz2 hone)
        exact hd.t_ne_z ((eq_inv_of_mul_eq_one_left h3).trans (inv_eq_of_mul_eq_one_right hzK.sq))
    have huC : u ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hzu.symm
    obtain ⟨y, hyL, hy⟩ := hmov (oddQuotMk z ⟨u, huC⟩) (oddQuotMk_mem_modOdd huB huC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hBab hcB hzK.ne_one huB hd.hu1 hd.huz huC)
    rcases SecComp.le_range_or_commute hs' Dsys j (hmem K hKtq) with hKj | hKc
    · exact hbad K hKtq hcK hKj
    rcases SecComp.le_range_or_commute hs' Dsys j (hmem K' hK'tq) with hK'j | hK'c
    · exact hbad K' hK'tq hcK' hK'j
    have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hcK.subnormal
    have hK'z : K' ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hcK'.subnormal
    have hKeq : exactCore z K = K := exactCore_eq_self hcK.perfect hKz
    have hK'eq : exactCore z K' = K' := exactCore_eq_self hcK'.perfect hK'z
    have hubar : oddQuotMk z ⟨u, huC⟩ ∈ modOdd z (exactCore z K) ⊔ modOdd z (exactCore z K') := by
      rw [hKeq, hK'eq]
      exact TwinVertex.oddQuotMk_mem_sup hKz hK'z hd.hu huC
    have hcent : modOdd z (exactCore z K) ⊔ modOdd z (exactCore z K') ≤
        Subgroup.centralizer ((secComponentHom hs'.normalizes Dsys j).range :
          Set (OddQuot z)) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_centralizer_iff.mpr fun w hw => (hKc x hx w hw).symm
      · exact Subgroup.mem_centralizer_iff.mpr fun w hw => (hK'c x hx w hw).symm
    have hyc := Subgroup.mem_centralizer_iff.mp (hcent hubar) y (hLj ▸ hyL)
    exact hy hyc.symm
  exact ⟨fun L₁ L₂ h1 h2 m1 m2 => (hno L₁ h1 m1).elim, fun L hL hm => (hno L hL hm).elim⟩

theorem twinFrameHyp51z : TwinFrameHyp51z p f :=
  fun G _ _ _ Ω K K' J z u t hs => twinFrameHyp51zCore p f G Ω K K' J z u t hs.toCore

end Vertex

end CFSG.ClassicalInvolution.Asc77
