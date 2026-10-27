module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.LargeExtraspecial.OrthoF2Fixed
public import CFSG.LargeExtraspecial.S4Basic
public import CFSG.LargeExtraspecial.S4Weak

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem two_mul_width_le_card_Lbar (H : Hyp4 S g) : 2 * S.width ≤ Nat.card (S.Lbar g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := S.isElementaryAbelian_Lbar H.conj_mem
  set A : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) := (S.Lbar g).map S.O.subtype with hAdef
  have : CFSG.IsElementaryAbelian 2 A := CFSG.IsElementaryAbelian.map_subtype
  have hA : Nat.card A = Nat.card (S.Lbar g) := card_map_of_injective S.O.subtype_injective
  obtain ⟨r, hr⟩ := (isPGroup_Lbar S H.conj_mem).exists_card_eq
  have h1 := (timmesfeld_3_1_one A (hA.trans hr)).2
  have hfix : fixSpaceOf A = fixSub S (S.Lbar g) := by
    ext v
    constructor
    · intro hv x hx
      exact hv _ ⟨x, hx, rfl⟩
    · rintro hv _ ⟨x, hx, rfl⟩
      exact hv x hx
  rw [hfix, H.fixSub_eq, finrank_span_singleton (cl_conj_z_ne_zero S H.conj_mem H.conj_ne),
    S.finrank_Qt_eq_two_mul_width, mul_one] at h1
  rw [hr]
  exact h1

theorem four_le_width (H : Hyp4 S g) (C : Cons311 S g) : 4 ≤ S.width := by
  have h1 := two_mul_width_le_card_Lbar H
  rw [C.card_Lbar] at h1
  have h2 := H.two_lt_width
  by_contra h
  interval_cases hw : S.width
  simp_all

theorem isWC_Lbar (H : Hyp4 S g) (C : Cons311 S g)
    (hTI : ∀ h : S.M, S.Lbar ((h : G) * g) ⊓ S.Lbar g = ⊥ ∨
      S.Lbar ((h : G) * g) = S.Lbar g) :
    CFSG.CGT.Timmesfeld75.IsWC ((S.Lbar g).subgroupOf S.Mbar) := by
  have hLM := S.Lbar_le_Mbar g
  have hconj : ∀ x : S.Mbar, ((CFSG.CGT.Timmesfeld75.conjSubgroup x
      ((S.Lbar g).subgroupOf S.Mbar)).map S.Mbar.subtype : Subgroup S.O) =
        (S.Lbar g).map (MulAut.conj (x : S.O)).toMonoidHom := by
    intro x
    ext y
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      exact ⟨l, mem_subgroupOf.mp hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨_, ⟨⟨l, hLM hl⟩, mem_subgroupOf.mpr hl, rfl⟩, rfl⟩
  have hLbar : ∀ x : S.Mbar, ∃ h : S.M,
      (S.Lbar g).map (MulAut.conj (x : S.O)).toMonoidHom = S.Lbar ((h : G) * g) := by
    intro x
    obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp x.2
    exact ⟨h, by rw [Lbar_mul S h, hh]⟩
  refine ⟨⟨?_, fun x _ => ?_⟩, fun t ht ht1 => ⟨?_, fun x hx => ?_⟩⟩
  ·
    refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩
    exact Lbar_comm S H.conj_mem (mem_subgroupOf.mp a.2) (mem_subgroupOf.mp b.2)
  · exact Subtype.ext (by
      rw [SubgroupClass.coe_pow, pow_two]
      exact mul_self_of_mem_Lbar S H.conj_mem (mem_subgroupOf.mp ‹_›))
  · intro y hy
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (Lbar_comm S H.conj_mem (mem_subgroupOf.mp hy) (mem_subgroupOf.mp ht))
  ·
    obtain ⟨h, hh⟩ := hLbar x
    have hnorm : S.Lbar ((h : G) * g) ≤ normalizer (S.Lbar g : Set S.O) := by
      intro y hy
      rw [← hh, ← hconj x] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      have hc := mem_centralizer_singleton_iff.mp (hx hy')
      obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp y'.2
      rcases hTI k with hbot | heq
      · exfalso
        apply ht1
        have htk : (t : S.O) ∈ S.Lbar ((k : G) * g) := by
          rw [Lbar_mul S k, hk]
          refine ⟨t, mem_subgroupOf.mp ht, ?_⟩
          have := congrArg Subtype.val hc
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul] at this ⊢
          rw [this, mul_inv_cancel_right]
        have : (t : S.O) ∈ S.Lbar ((k : G) * g) ⊓ S.Lbar g :=
          mem_inf.mpr ⟨htk, mem_subgroupOf.mp ht⟩
        rw [hbot, mem_bot] at this
        exact Subtype.ext this
      · rw [Lbar_mul S k, hk] at heq
        exact mem_normalizer_of_map_conj_eq heq
    have := C.weaklyClosed (h : G) h.2 hnorm
    apply Subgroup.map_injective S.Mbar.subtype_injective
    rw [hconj x, hh, this]
    ext y
    constructor
    · intro hy
      exact ⟨⟨y, hLM hy⟩, mem_subgroupOf.mpr hy, rfl⟩
    · rintro ⟨y', hy', rfl⟩
      exact mem_subgroupOf.mp hy'

end CFSG.LargeExtraspecial.S4
