module

public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasBActionKernel
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverExclusion
import CFSG.Sporadic.Schreier.MathieuOddCoreM12
import CFSG.Sporadic.J2
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Schreier.Outer

public section

namespace CFSG.ComponentClassification.CentralCover

open Subgroup

theorem index_inner_le_two {Q : Type*} [Group Q] [Finite Q] (hZQ : center Q = ⊥)
    (hAut : Nat.card (MulAut Q) ≤ 2 * Nat.card Q) : (OuterAutomorphisms.inner Q).index ≤ 2 := by
  have hcard := (OuterAutomorphisms.inner Q).card_mul_index
  rw [CFSG.Sporadic.Schreier.card_inner_of_center_eq_bot hZQ] at hcard
  have hpos : 0 < Nat.card Q := Nat.card_pos
  by_contra h
  have h3 : 3 ≤ (OuterAutomorphisms.inner Q).index := by omega
  have h4 : Nat.card Q * 3 ≤ Nat.card (MulAut Q) := hcard ▸ Nat.mul_le_mul_left _ h3
  omega

theorem exists_injective_quotient_outer {H : Type*} [Group H] {L : Subgroup H} [L.Normal]
    [Group.IsPerfect L] {Q : Type*} [Group Q] (π : L →* Q) (hπ : Function.Surjective π)
    (hker : π.ker = center L) (hCL : centralizer (L : Set H) ≤ L) :
    ∃ φ : H ⧸ L →* OuterAutomorphisms.Outer Q, Function.Injective φ := by
  let f : H →* OuterAutomorphisms.Outer Q :=
    (QuotientGroup.mk' (OuterAutomorphisms.inner Q)).comp (fullAction π hπ hker)
  have hf : f.ker = L := by
    rw [← comap_inner_fullAction π hπ hker hCL]
    ext h
    simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_comap]
  exact ⟨(QuotientGroup.kerLift f).comp (QuotientGroup.quotientMulEquivOfEq hf.symm).toMonoidHom,
    (QuotientGroup.kerLift_injective f).comp (QuotientGroup.quotientMulEquivOfEq hf.symm).injective⟩

theorem index_le_two_of_card_mulAut_le {H : Type*} [Group H] [Finite H] {L : Subgroup H}
    [L.Normal] [Group.IsPerfect L] {Q : Type*} [Group Q] [Finite Q] (π : L →* Q)
    (hπ : Function.Surjective π) (hker : π.ker = center L)
    (hCL : centralizer (L : Set H) ≤ L) (hZQ : center Q = ⊥)
    (hAut : Nat.card (MulAut Q) ≤ 2 * Nat.card Q) : L.index ≤ 2 := by
  rw [← comap_inner_fullAction π hπ hker hCL, index_comap]
  calc (OuterAutomorphisms.inner Q).relIndex (fullAction π hπ hker).range
      ≤ (OuterAutomorphisms.inner Q).relIndex ⊤ :=
        relIndex_le_of_le_right le_top (by
          rw [relIndex_top_right]
          exact Subgroup.index_ne_zero_of_finite)
    _ = (OuterAutomorphisms.inner Q).index := relIndex_top_right _
    _ ≤ 2 := index_inner_le_two hZQ hAut

theorem quasisimple_faithful_overgroup_index_le_two
    (hJ2 : Nat.card (MulAut Blueprint.NativeSporadic.J2) ≤
      2 * Nat.card Blueprint.NativeSporadic.J2)
    {H : Type} [Group H] [Finite H] {L : Subgroup H} [L.Normal]
    (hLq : Assembly.IsQuasisimple L) (hQ : StandardRecognition.IsM12OrJ2Quotient L)
    (hCL : centralizer (L : Set H) = (center L).map L.subtype) :
    (∃ φ : H ⧸ L →* OuterAutomorphisms.Outer (L ⧸ center L), Function.Injective φ) ∧
      L.index ≤ 2 := by
  have : Group.IsPerfect L := (Group.isPerfect_def).2 hLq.1
  have hCL' : centralizer (L : Set H) ≤ L := by
    rw [hCL]
    exact map_subtype_le _
  have key : ∀ s : TauCeti.SporadicName,
      Nat.card (MulAut (Blueprint.NativeSporadic.Carrier s)) ≤
        2 * Nat.card (Blueprint.NativeSporadic.Carrier s) →
      IsSimpleGroup (Blueprint.NativeSporadic.Carrier s) →
      ¬ (Nat.card (Blueprint.NativeSporadic.Carrier s)).Prime →
      Finite (Blueprint.NativeSporadic.Carrier s) →
      Blueprint.NativeSporadic.IsSporadic (L ⧸ center L) s → L.index ≤ 2 := by
    rintro s hAut hsimp hprime hfin ⟨e⟩
    have hZQ : center (Blueprint.NativeSporadic.Carrier s) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (center (Blueprint.NativeSporadic.Carrier s)) with h | h
      · exact h
      · exfalso
        have : IsMulCommutative (Blueprint.NativeSporadic.Carrier s) :=
          ⟨⟨fun a b => (mem_center_iff.mp (h ▸ mem_top b : b ∈ center _) a)⟩⟩
        exact hprime (Group.is_simple_iff_prime_card.mp hsimp)
    let π : L →* Blueprint.NativeSporadic.Carrier s :=
      e.toMonoidHom.comp (QuotientGroup.mk' (center L))
    have hπ : Function.Surjective π :=
      e.surjective.comp (QuotientGroup.mk'_surjective (center L))
    have hker : π.ker = center L := by
      ext l
      simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact index_le_two_of_card_mulAut_le π hπ hker hCL' hZQ hAut
  refine ⟨exists_injective_quotient_outer (QuotientGroup.mk' (center L))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hCL', ?_⟩
  rcases hQ with h | h
  · obtain ⟨hfin, -, hsimp⟩ := CFSG.Sporadic.Mathieu.fam_m12_simplicity
    refine key .M12 CFSG.Sporadic.Schreier.m12_mulAut_card hsimp ?_ hfin h
    change ¬ (Nat.card Blueprint.NativeSporadic.M12).Prime
    rw [CFSG.Sporadic.Mathieu.card_M12]
    norm_num
  · obtain ⟨hfin, -, hsimp⟩ := CFSG.Sporadic.J2.fam_j2_simplicity
    refine key .J2 hJ2 hsimp ?_ hfin h
    change ¬ (Nat.card Blueprint.NativeSporadic.J2).Prime
    rw [CFSG.Sporadic.J2.card_J2]
    norm_num

end CFSG.ComponentClassification.CentralCover
