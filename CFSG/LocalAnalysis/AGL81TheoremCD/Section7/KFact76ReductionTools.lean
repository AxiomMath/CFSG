module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76Rows
import CFSG.RankThree.PartTwo.Sec4.RonanK432Main

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7

open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts (centerDescend)

theorem isSimpleGroup_of_listRow76 {L : Type} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (hZ3 : IsPGroup 3 (Subgroup.center L)) (hlist : ListRow76 (L ⧸ Subgroup.center L)) {b : L}
    (hb3 : b ^ 3 = 1) (hb1 : MulAut.conj b ≠ 1)
    (hwc : RonanK432.AutWeaklyClosed (MulAut.conj b)) :
    IsSimpleGroup L ∧
      (CFSG.Open.pRank 3 (⊤ : Subgroup L) = 1 ∨
        (∃ q : TauCeti.PrimePower, ∃ hv : (TauCeti.LieTypeIndex.G2 q).Valid, q.p ≠ 3 ∧
          Nonempty (L ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group)) ∨
        (∃ q : TauCeti.PrimePower, ∃ hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid,
          q.card = 3 ∧ Nonempty (L ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group)) ∨
        Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic .J2).Group)) := by
  have : Group.IsPerfect L := hq.1
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2.1
  have hZS := RonanK432.center_eq_bot_of_isQuasisimple_quot hq
  have hwcb : RonanK432.WeaklyClosed (Subgroup.zpowers (b : L ⧸ Subgroup.center L)) := by
    refine RonanK432.weaklyClosed_zpowers_of_autWeaklyClosed_conj hZS ?_
    rw [← Res423Five.centerDescend_conj']
    exact RonanK432.autWeaklyClosed_descend hwc
  have hb3' : (b : L ⧸ Subgroup.center L) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hb3, QuotientGroup.mk_one]
  have hb1' : (b : L ⧸ Subgroup.center L) ≠ 1 := by
    intro h
    apply hb1
    have hbc : b ∈ Subgroup.center L := (QuotientGroup.eq_one_iff b).mp h
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.mp hbc x,
      mul_inv_cancel_right]
  have hcase := hlist _ (orderOf_eq_prime hb3' hb1') hwcb
  have hbot : Subgroup.center L = ⊥ := by
    rcases hcase with h1 | ⟨-, -, hno⟩
    · exact RonanK432.center_eq_bot_of_pRank_quot_le_one hq.1 hZ3 h1.le
    · exact hno L hq hZ3 ⟨MulEquiv.refl _⟩
  set e := RonanK432.mulEquivQuotCenterOfEqBot hbot
  refine ⟨e.isSimpleGroup, ?_⟩
  rcases hcase with h1 | ⟨hiso, -, -⟩
  · left
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    exact h1
  · right
    rcases hiso with ⟨q, hv, hq3, ⟨e'⟩⟩ | ⟨q, hv, hq3, ⟨e'⟩⟩ | he'
    · exact Or.inl ⟨q, hv, hq3, ⟨e.trans e'⟩⟩
    · exact Or.inr (Or.inl ⟨q, hv, hq3, ⟨e.trans e'⟩⟩)
    · obtain ⟨e'⟩ := he'
      exact Or.inr (Or.inr ⟨e.trans e'⟩)

theorem exists_inv_of_row76 {L : Type} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (hZ3 : IsPGroup 3 (Subgroup.center L)) (h3 : 3 ∣ Nat.card L)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 3) (hrow : Row76 (L ⧸ Subgroup.center L))
    {σ : MulAut L} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hwc : RonanK432.AutWeaklyClosed σ)
    (hfix : CFSG.Open.pRank 3 (σ.toMonoidHom.eqLocus (MonoidHom.id L)) ≤ 2) :
    ∃ b t : L, σ = MulAut.conj b ∧ t * b * t⁻¹ * b ∈ Subgroup.center L := by
  have : Group.IsPerfect L := hq.1
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2.1
  have hZS := RonanK432.center_eq_bot_of_isQuasisimple_quot hq
  obtain ⟨hlist, houter⟩ := hrow
  have hinj : Function.Injective (centerDescend L) := Res423Five.centerDescend_injective
  have hρσ3 : centerDescend L σ ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
  have hρσ1 : centerDescend L σ ≠ 1 := fun h => hσ1 (hinj (by rw [h, map_one]))
  have hwc' : RonanK432.AutWeaklyClosed (centerDescend L σ) :=
    RonanK432.autWeaklyClosed_descend hwc
  by_cases hin : centerDescend L σ ∈
      (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range
  ·
    obtain ⟨bb, hbb⟩ := hin
    have hcinj := RonanK432.conj_injective_of_center_eq_bot hZS
    have hbb3 : bb ^ 3 = 1 := by
      apply hcinj
      rw [map_pow, hbb, hρσ3, map_one]
    have hbb1 : bb ≠ 1 := by
      intro h
      apply hρσ1
      rw [← hbb, h, map_one]
    have horder : orderOf bb = 3 := orderOf_eq_prime hbb3 hbb1
    have hwcb : RonanK432.WeaklyClosed (Subgroup.zpowers bb) :=
      RonanK432.weaklyClosed_zpowers_of_autWeaklyClosed_conj hZS (by rw [hbb]; exact hwc')
    have hreal : ∃ t : L ⧸ Subgroup.center L, t * bb * t⁻¹ = bb⁻¹ := by
      rcases hlist bb horder hwcb with h1 | ⟨-, hr, -⟩
      · exact RonanK432.exists_inv_of_pRank_one hq.2.2 h1 horder
      · exact hr bb hbb3
    obtain ⟨tt, htt⟩ := hreal
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective bb
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective tt
    refine ⟨b, t, hinj (hbb.symm.trans (Res423Five.centerDescend_conj' b).symm), ?_⟩
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [htt]
    group
  ·
    exact absurd hwc' (houter (RonanK432.three_dvd_card_quot_center hq.1 h3) _ hρσ3 hin
      ⟨L, inferInstance, inferInstance, σ, MulEquiv.refl _, hq, hZ3, hσ3, fun _ => rfl, hrk,
        hfix⟩)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7
