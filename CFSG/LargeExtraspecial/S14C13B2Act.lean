module

public import CFSG.LargeExtraspecial.S14C13B2Data
public import CFSG.LargeExtraspecial.S14C13B2Gen
public import CFSG.LargeExtraspecial.S14NQSixPre

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S2

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

@[expose] noncomputable def B2Data.ofStd {H : Hyp4 S g} {C : Cons311 S g} {t : S.O}
    {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g} (D : S8.Std H C ht ht1 hVQ)
    (hdim : finrank (ZMod 2) (Vt S g t) = 8) : B2Data S g ht where
  hVQ := hVQ
  Q := D.Q
  hQ := D.hQ
  hX := D.hX
  hE := D.hE
  horb := D.hsing
  h := D.h
  hh := D.hh
  hb := D.hb
  hth := mem_Lbar_of_pair H ht D.hh
  hab := D.polar_aV_bV
  hdim := hdim

section Act

variable {t : S.O} [NQHyp S g t] {ht : t ∈ S.Lbar g} (D : B2Data S g ht)

noncomputable def omegaOf (haQ : g * S.z * g⁻¹ ∈ S.QG) {r : S.O} (hr : r ∈ Rbar S g t) :
    omegaGroup D.Q D.hQ :=
  ⟨resV haQ t ⟨r, hr⟩, by rw [← D.hX]; exact ⟨r, hr, fun v => rfl⟩⟩

theorem nqRep_omegaOf_sub (haQ : g * S.z * g⁻¹ ∈ S.QG) {r : S.O} (hr : r ∈ Rbar S g t)
    (n x : Nbar S g t) (hx : (x : S.O) = r * n * r⁻¹ * (n : S.O)⁻¹) :
    nqRep S g t D.hX (omegaOf D haQ hr) (nqMk n) - nqMk n = nqMk x := by
  have e : nConj ⟨r, hr⟩ n = x * n := Subtype.ext (by
    change r * n * r⁻¹ = (x : S.O) * n
    rw [hx]
    group)
  exact sub_eq_iff_eq_add.mpr ((nqRep_apply D.hX (x := ⟨r, hr⟩) rfl n).trans
    ((congrArg nqMk e).trans (nqMk_mul x n)))

theorem nqRep_omegaOf_eq_iff (haQ : g * S.z * g⁻¹ ∈ S.QG) {r : S.O} (hr : r ∈ Rbar S g t)
    (n : Nbar S g t) :
    nqRep S g t D.hX (omegaOf D haQ hr) (nqMk n) = nqMk n ↔
      r * n * r⁻¹ * (n : S.O)⁻¹ ∈ zpowers t := by
  have hx : r * n * r⁻¹ * (n : S.O)⁻¹ ∈ Nbar S g t :=
    mul_mem (conj_mem_Nbar_of_mem_Rbar haQ hr n.2) (inv_mem n.2)
  have h := nqRep_omegaOf_sub D haQ hr n ⟨_, hx⟩ rfl
  rw [← sub_eq_zero, h, nqMk_eq_zero_iff]

variable {ψ : Module.End (ZMod 2) (NQ S g t)}

theorem comm_mem_zpowers_of_rank_le_one (H : Hyp4 S g) [IsSimpleGroup (omegaGroup D.Q D.hQ)]
    (hcN : IsCompl (fixOf (nqRep S g t D.hX) (pointRadical D.Q (aV ht) : Set _))
      (fixOf (nqRep S g t D.hX) (pointRadical D.Q (bV D.hth) : Set _)))
    (hψ : ∀ e v, ψ (nqRep S g t D.hX e v) = nqRep S g t D.hX e (ψ v))
    (hr : finrank (ZMod 2) (LinearMap.range ψ) = 8) {r : S.O} (hrR : r ∈ Rbar S g t)
    {c : S.O} (hcNb : c ∈ Nbar S g t)
    (h : ∀ a ∈ nqPre S g t (LinearMap.range ψ), r * a * r⁻¹ * a⁻¹ = 1 ∨
      r * a * r⁻¹ * a⁻¹ = t ∨ r * a * r⁻¹ * a⁻¹ = c ∨ r * a * r⁻¹ * a⁻¹ = c * t) :
    ∀ a ∈ nqPre S g t (LinearMap.range ψ), r * a * r⁻¹ * a⁻¹ ∈ zpowers t := by
  have haQ := H.conj_mem
  have htN : t ∈ Nbar S g t := S6.self_mem_Nbar H ht
  have hrn : ∀ n : Nbar S g t, r * n * r⁻¹ * (n : S.O)⁻¹ ∈ Nbar S g t := fun n =>
    mul_mem (conj_mem_Nbar_of_mem_Rbar haQ hrR n.2) (inv_mem n.2)
  have ht0 : nqMk (⟨t, htN⟩ : Nbar S g t) = 0 := (nqMk_eq_zero_iff _).mpr (mem_zpowers t)
  have hcomm : ∀ w ∈ LinearMap.range ψ, nqRep S g t D.hX (omegaOf D haQ hrR) w - w ∈
      (ZMod 2) ∙ nqMk (⟨c, hcNb⟩ : Nbar S g t) := by
    intro w hw
    have hsw := nqMk_surjective w
    obtain ⟨n, rfl⟩ := hsw
    have hsub := nqRep_omegaOf_sub D haQ hrR n ⟨_, hrn n⟩ rfl
    rw [hsub, Submodule.mem_span_singleton]
    rcases h n ⟨n.2, hw⟩ with h1 | h1 | h1 | h1
    · exact ⟨0, (zero_smul _ _).trans ((nqMk_eq_zero_iff _).mpr
        (show r * (n : S.O) * r⁻¹ * (n : S.O)⁻¹ ∈ zpowers t by rw [h1]; exact one_mem _)).symm⟩
    · exact ⟨0, (zero_smul _ _).trans ((nqMk_eq_zero_iff _).mpr
        (show r * (n : S.O) * r⁻¹ * (n : S.O)⁻¹ ∈ zpowers t by rw [h1]; exact mem_zpowers t)).symm⟩
    · exact ⟨1, (one_smul _ _).trans (congrArg nqMk (Subtype.ext h1.symm))⟩
    · refine ⟨1, (one_smul _ _).trans ?_⟩
      have e : (⟨_, hrn n⟩ : Nbar S g t) = ⟨c, hcNb⟩ * ⟨t, htN⟩ := Subtype.ext h1
      exact ((add_zero _).symm.trans (congrArg (nqMk (⟨c, hcNb⟩ : Nbar S g t) + ·) ht0.symm)).trans
        ((nqMk_mul _ _).symm.trans (congrArg nqMk e.symm))
  have htriv := rangeRep_trivial_of_rank_le_one (nqRep S g t D.hX) D.hdim (aV_ne_zero H ht)
    (D.Q_aV H) (D.Q_bV H) D.hab hcN hψ (by rw [hr]; norm_num) (omegaOf D haQ hrR) _ hcomm
  intro a ha
  exact (nqRep_omegaOf_eq_iff D haQ hrR ⟨a, ha.1⟩).mp (htriv _ ha.2)

theorem mem_Nbar_of_comm_A (H : Hyp4 S g) [IsSimpleGroup (omegaGroup D.Q D.hQ)]
    (hcN : IsCompl (fixOf (nqRep S g t D.hX) (pointRadical D.Q (aV ht) : Set _))
      (fixOf (nqRep S g t D.hX) (pointRadical D.Q (bV D.hth) : Set _)))
    (hψ : ∀ e v, ψ (nqRep S g t D.hX e v) = nqRep S g t D.hX e (ψ v))
    (hr : finrank (ZMod 2) (LinearMap.range ψ) = 8) {r : S.O} (hrR : r ∈ Rbar S g t)
    (h : ∀ a ∈ nqPre S g t (LinearMap.range ψ), r * a * r⁻¹ * a⁻¹ ∈ zpowers t) :
    r ∈ Nbar S g t := by
  have haQ := H.conj_mem
  have he : rangeRep (nqRep S g t D.hX) hψ (omegaOf D haQ hrR) = 1 := by
    refine LinearEquiv.ext fun u => Subtype.ext ?_
    show nqRep S g t D.hX (omegaOf D haQ hrR) (u : NQ S g t) = (u : NQ S g t)
    have hsu := nqMk_surjective (u : NQ S g t)
    obtain ⟨n, hn⟩ := hsu
    have hnU : nqMk n ∈ LinearMap.range ψ := by rw [hn]; exact u.2
    have h1 := (nqRep_omegaOf_eq_iff D haQ hrR n).mpr (h n ⟨n.2, hnU⟩)
    rw [← hn]
    exact h1
  have h1 := rangeRep_faithful (nqRep S g t D.hX) (m := 4) (by norm_num) (by rw [D.hdim])
    (aV_ne_zero H ht) (D.Q_aV H) (D.Q_bV H) D.hab hcN hψ (by rw [hr]; norm_num) _ he
  have h2 : resV haQ t ⟨r, hrR⟩ = 1 := congrArg Subtype.val h1
  exact (resV_eq_one_iff haQ ⟨r, hrR⟩).mp h2

theorem exists_mem_A_inf_Lbar (H : Hyp4 S g)
    (hcN : IsCompl (fixOf (nqRep S g t D.hX) (pointRadical D.Q (aV ht) : Set _))
      (fixOf (nqRep S g t D.hX) (pointRadical D.Q (bV D.hth) : Set _)))
    (hψ : ∀ e v, ψ (nqRep S g t D.hX e v) = nqRep S g t D.hX e (ψ v))
    (hr : finrank (ZMod 2) (LinearMap.range ψ) = 8)
    (hfixL : fixOf (nqRep S g t D.hX) (pointRadical D.Q (aV ht) : Set _) ≤
      nqSub S g t (S.Lbar g)) :
    ∃ a ∈ nqPre S g t (LinearMap.range ψ), a ∈ S.Lbar g ∧ a ≠ 1 ∧ a ≠ t := by
  have hw := exists_mem_range_fixOf (nqRep S g t D.hX) (m := 4) (by norm_num) (by rw [D.hdim])
    (aV_ne_zero H ht) (D.Q_aV H) (D.Q_bV H) D.hab hcN hψ (by rw [hr]; norm_num)
  obtain ⟨w, hwR, hw0, hwF⟩ := hw
  have hx := hfixL hwF
  obtain ⟨x, hxL, hxw⟩ := hx
  refine ⟨x, ⟨x.2, hxw ▸ hwR⟩, hxL, fun h => hw0 ?_, fun h => hw0 ?_⟩
  · exact hxw.symm.trans ((nqMk_eq_zero_iff x).mpr (by rw [h]; exact one_mem _))
  · exact hxw.symm.trans ((nqMk_eq_zero_iff x).mpr (by rw [h]; exact mem_zpowers t))

end Act

end CFSG.LargeExtraspecial.S14
