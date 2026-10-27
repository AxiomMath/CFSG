module

public import CFSG.CGT.T75O.Class
public import CFSG.Timmesfeld.RootSubgroupBasic

public section

namespace CFSG.CGT.T75O

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

namespace Cfg56

variable (c : Cfg56 T T₁)
include c

omit c in
theorem mem_classD_of_isConj {a e : G} (ha : a ∈ secA T T₁) (ha1 : a ≠ 1) (he : IsConj a e) :
    e ∈ classD T := by
  obtain ⟨x, hx⟩ := isConj_iff.1 he
  exact ⟨x⁻¹, a, secA_le_left ha, ha1, by rw [inv_inv]; exact hx.symm⟩

theorem comm_secA_of_comm {a e b : G} (ha : a ∈ secA T T₁) (ha1 : a ≠ 1) (he : IsConj a e)
    (hb : b ∈ secA T T₁) (hb1 : b ≠ 1) (hcomm : e * b = b * e) :
    ∀ z ∈ secA T T₁, e * z = z * e := by
  have := c.hy.finite
  have hN : e ∈ Subgroup.normalizer (T : Set G) :=
    c.hy.pair.wc.centralizer_le_normalizer (secA_le_left hb) hb1
      (Subgroup.mem_centralizer_singleton_iff.2 hcomm)
  have h53 := secA_le_centralizer_normD c.hy.pair c.hS
  intro z hz
  exact Subgroup.mem_centralizer_iff.1 (h53 hz) e ⟨mem_classD_of_isConj ha ha1 he, hN⟩

theorem rootSet_eq {a : G} (ha : a ∈ secA T T₁) (ha1 : a ≠ 1) :
    rootSet (CorB.cls a) a = {e | e ∈ secA T T₁ ∧ e ≠ 1} := by
  have := c.hy.finite
  ext e
  constructor
  · rintro ⟨hE, hrs⟩
    have hE' : IsConj a e := hE
    obtain ⟨x, hx⟩ := isConj_iff.1 hE'
    have he1 : e ≠ 1 := conj_ne_one' hx ha1
    have hea : e * a = a * e := ((hrs a (IsConj.refl a)).2 (Commute.refl a)).eq
    refine ⟨?_, he1⟩
    rcases c.conj_comm_cases ha ha1 hx hea with hA | ⟨hu, hex⟩
    · exact hA
    · exfalso
      have hall : ∀ h : G, IsUIdx T T₁ h → ∀ y ∈ conjSubgroup h (secA T T₁),
          ∀ z ∈ conjSubgroup x (secA T T₁), y * z = z * y := by
        intro h hh y hy z hz
        by_cases hy1 : y = 1
        · rw [hy1]
          simp
        have hyE : y ∈ CorB.cls a := (c.isConj_invol_of_mem_secA_conj ha ha1 hy hy1).1
        have hay : a * y = y * a :=
          secA_comm_conjSubgroup_secA c.hy.pair c.hS hh.1 (hh.normIn_conj_ne_bot c.hy.pair) a ha
            y hy
        have hey : e * y = y * e := ((hrs y hyE).2 (show Commute a y from hay)).eq
        have hyD : y ∈ classD T :=
          mem_classD_of_mem_conjSubgroup (conjSubgroup_mono secA_le_left hy) hy1
        exact c.comm_all_of_comm_one hyD x hex he1 hey.symm z hz
      apply c.hnc x hu
      intro z hz r hr
      have hle : secR₁ T T₁ ≤ Subgroup.centralizer ({z} : Set G) := by
        refine iSup₂_le fun h hh y hy => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hall h hh y hy z hz
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hr)).symm
  · rintro ⟨he, he1⟩
    have hE' : IsConj a e := c.isConj_of_mem_secA ha ha1 he he1
    refine ⟨hE', fun f hf => ?_⟩
    have hf' : IsConj a f := hf
    constructor
    · intro hef
      exact (c.comm_secA_of_comm ha ha1 hf' he he1 hef.symm.eq a ha).symm
    · intro haf
      exact (c.comm_secA_of_comm ha ha1 hf' ha ha1 haf.symm.eq e he).symm

theorem rootGroup_eq {a : G} (ha : a ∈ secA T T₁) (ha1 : a ≠ 1) :
    rootGroup (CorB.cls a) a = secA T T₁ := by
  unfold rootGroup
  rw [c.rootSet_eq ha ha1]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact fun e he => he.1
  · intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨hx, hx1⟩

theorem hyp {a : G} (ha : a ∈ secA T T₁) (ha1 : a ≠ 1) : Hyp G (CorB.cls a) := by
  have := c.hy.finite
  have : IsSimpleGroup G := c.hy.simple
  have hs := c.setup ha ha1
  have hnonab := c.hy.nonab
  have hNtop : Subgroup.normalClosure ({a} : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({a} : Set G)) with
      h | h
    · exfalso
      apply ha1
      have : a ∈ Subgroup.normalClosure ({a} : Set G) := Subgroup.subset_normalClosure rfl
      rw [h] at this
      exact Subgroup.mem_bot.1 this
    · exact h
  refine ⟨c.hy.finite, ⟨a, rfl⟩, hs.isRootInvolutionSet, ?_, ?_, ?_, ?_⟩
  · rw [← CorB.normalClosure_eq]
    exact hNtop
  · intro N hN hodd
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top] at hodd
      have heven : 2 ∣ Nat.card G := hs.orderOf_eq ▸ orderOf_dvd_natCard a
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 heven)
  · intro N hN h2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      have hG2 : IsPGroup 2 G := fun g => by
        obtain ⟨k, hk⟩ := h2 ⟨g, h ▸ Subgroup.mem_top g⟩
        exact ⟨k, congrArg Subtype.val hk⟩
      have hcen := center_eq_bot_of_simple_nonabelian G hnonab
      have : Nontrivial (Subgroup.center G) := hG2.center_nontrivial
      rw [hcen] at this
      exact absurd this (not_nontrivial (⊥ : Subgroup G))
  · obtain ⟨d, e, hd, he, h4⟩ := c.exists_orderOf_eq_four ha ha1
    exact ⟨d, hd, e, he, h4⟩

end Cfg56

end CFSG.CGT.T75O
