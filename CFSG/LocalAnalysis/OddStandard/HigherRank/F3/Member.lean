module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Transfer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Raw
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit

structure BlockData (X : Type) [Group X] : Prop where
  quasisimple : IsQuasisimple X
  card_center : ∃ k : ℕ, 1 ≤ k ∧ Nat.card ↥(center X) = 2 ^ k
  shape : ∃ (τ : StatedLieTag) (n : ℕ), CFSG.Blueprint.LieModel (X ⧸ center X) τ n 3 1 ∧
    ((τ = .PSL ∧ (n = 4 ∨ n = 6)) ∨ (τ = .PSU ∧ (n = 4 ∨ n = 6)) ∨ (τ = .PSp ∧ 2 ≤ n) ∨
      (τ = .POmegaPlus ∧ (n = 4 ∨ n = 6)) ∨ τ = .E7)
  fullCover : ordProj[2] (Nat.card (Open.griessHopfMultiplier (X ⧸ center X))) ≤
    ordProj[2] (Nat.card ↥(center X))

namespace BlockData

variable {X : Type} [Group X] [Finite X]

theorem isPGroup_center (h : BlockData X) : IsPGroup 2 ↥(center X) := by
  obtain ⟨k, -, hk⟩ := h.card_center
  exact IsPGroup.of_card hk

theorem pPrimeCore_eq_bot (h : BlockData X) : pPrimeCore 2 X = ⊥ :=
  pPrimeCore_eq_bot_of_surjective_of_isQuasisimple h.quasisimple h.isPGroup_center
    (MonoidHom.id X) Function.surjective_id

theorem fusionZStar_eq (h : BlockData X) : Open.fusionZStar X = center X :=
  fusionZStar_eq_center_of_pPrimeCore_eq_bot h.pPrimeCore_eq_bot

theorem even_card_center (h : BlockData X) : Even (Nat.card ↥(center X)) := by
  obtain ⟨k, hk1, hk⟩ := h.card_center
  rw [hk]
  exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))

theorem classBShape (h : BlockData X) : ClassBShape X := by
  obtain ⟨τ, n, hm, hs⟩ := h.shape
  exact ⟨τ, n, ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv
    (QuotientGroup.quotientMulEquivOfEq h.fusionZStar_eq).symm hm, hs⟩

theorem ordProj_eq (h : BlockData X) :
    ordProj[2] (Nat.card ↥(center X)) =
      ordProj[2] (Nat.card (Open.griessHopfMultiplier (X ⧸ center X))) := by
  haveI hfin : Finite (Open.griessHopfMultiplier (X ⧸ center X)) := by
    haveI : Group.IsPerfect X := h.quasisimple.1
    haveI hfr : Finite (X ⧸ center X) :=
      Finite.of_surjective (QuotientGroup.mk' (center X)) (QuotientGroup.mk'_surjective _)
    haveI hpq : Group.IsPerfect (X ⧸ center X) := inferInstance
    haveI : Finite (RankThree.PerfectCover.hopfMultiplier (X ⧸ center X)) :=
      RankThree.PerfectCover.finite_hopfMultiplier hpq
    exact Finite.of_equiv _
      (RankThree.PerfectCover.hopfMultiplierEquivGriess (X ⧸ center X)).symm.toEquiv
  have hdvd : Nat.card ↥(center X) ∣
      Nat.card (Open.griessHopfMultiplier (X ⧸ center X)) :=
    Center47.card_center_dvd_card_griessHopfMultiplier h.quasisimple
  have hfac : (Nat.card ↥(center X)).factorization 2 =
      (Nat.card (Open.griessHopfMultiplier (X ⧸ center X))).factorization 2 := by
    refine le_antisymm ?_ ?_
    · exact (Nat.factorization_le_iff_dvd (Nat.card_pos.ne') (Nat.card_pos.ne')).mpr hdvd 2
    · exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h.fullCover
  rw [hfac]

private theorem ordProj_fusionZStar_eq (h : BlockData X) :
    ordProj[2] (Nat.card ↥(Open.fusionZStar X)) =
      ordProj[2] (Nat.card (Open.griessHopfMultiplier (X ⧸ Open.fusionZStar X))) := by
  have hZ : Nat.card ↥(Open.fusionZStar X) = Nat.card ↥(center X) := by
    rw [h.fusionZStar_eq]
  have hM : Nat.card (Open.griessHopfMultiplier (X ⧸ Open.fusionZStar X)) =
      Nat.card (Open.griessHopfMultiplier (X ⧸ center X)) :=
    Nat.card_congr (LieType.Steinberg.CentralExt.griessHopfMultiplierCongr
      (QuotientGroup.quotientMulEquivOfEq h.fusionZStar_eq)).toEquiv
  rw [hZ, hM, h.ordProj_eq]

theorem not_partialCentre (h : BlockData X) : ¬ PartialCentre X := by
  unfold PartialCentre
  intro hlt
  rw [ordProj_fusionZStar_eq h] at hlt
  exact lt_irrefl _ hlt

theorem isMTypeSchur (h : BlockData X) : IsMTypeSchur 3 X := by
  have hq : IsQuasisimple (X ⧸ pPrimeCore 2 X) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq h.pPrimeCore_eq_bot.symm)) h.quasisimple
  obtain ⟨τ, n, hm, -⟩ := h.classBShape
  refine Or.inl ⟨⟨h.quasisimple.1, hq⟩, ⟨τ, n, 1, hm⟩, ?_, ?_⟩
  · rw [h.fusionZStar_eq]
    exact h.even_card_center
  · intro n r hn hr hm'
    exact ordProj_fusionZStar_eq h

end BlockData

theorem hasCleanFullClassBMember_of_block {H Q X : Type} [Group H] [Group Q] [Group X]
    [Finite Q] [Finite X] [IsSimpleGroup Q] (α : H →* Q) (hα : Function.Surjective α)
    (hαk : α.ker ≤ center H) (θ : X →* H) (hθ : Function.Injective (α.comp θ)) {c : X}
    (hc2 : orderOf c = 2) (hcc : c ∈ center X)
    (hnorm : (θ.range.subgroupOf (centralizer ({θ c} : Set H))).Normal) (hX : BlockData X) :
    HasCleanFullClassBMember Q := by
  have hle : θ.range ≤ centralizer ({θ c} : Set H) := by
    rintro x ⟨y, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc θ y * θ c = θ (y * c) := (map_mul θ y c).symm
      _ = θ (c * y) := by rw [Subgroup.mem_center_iff.mp hcc y]
      _ = θ c * θ y := map_mul θ c y
  obtain ⟨hmap_le, hsn⟩ :=
    T1.P54.F3.map_isSubnormal_of_central hα hαk hle hnorm.isSubnormal
  have hle' : (α.comp θ).range ≤ centralizer ({(α.comp θ) c} : Set Q) := by
    have h := hmap_le
    rw [← MonoidHom.range_comp α θ] at h
    exact h
  have hsub :
      (((α.comp θ).range).subgroupOf (centralizer ({(α.comp θ) c} : Set Q))).IsSubnormal := by
    have h := hsn
    rw [← MonoidHom.range_comp α θ] at h
    exact h
  have eJ : X ≃* ↥(α.comp θ).range := MonoidHom.ofInjective hθ
  refine ⟨(α.comp θ).range, (α.comp θ) c, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact (orderOf_injective (α.comp θ) hθ c).trans hc2
  · exact MonoidHom.mem_range.mpr ⟨c, rfl⟩
  · intro hc
    have hord2 : orderOf ((α.comp θ) c) = 2 := (orderOf_injective (α.comp θ) hθ c).trans hc2
    have hcne : (α.comp θ) c ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord2
      exact absurd hord2 (by norm_num)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with hbot | htop
    · rw [hbot, Subgroup.mem_bot] at hc
      exact hcne hc
    · have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
        Subgroup.mem_center_iff.mp (by rw [htop]; exact Subgroup.mem_top b) a
      obtain ⟨a, b, hab⟩ := hX.quasisimple.2.2
      apply hab
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      have hxy : x * y = y * x :=
        hθ (by rw [map_mul, map_mul]; exact hcomm ((α.comp θ) x) ((α.comp θ) y))
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]
  · haveI : Group.IsPerfect X := hX.quasisimple.1
    exact Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  · exact (CFSG.Open.IsSubnormal.iff_subgroupOf hle').mpr hsub
  · exact T23.isMTypeSchur_of_mulEquiv eJ hX.isMTypeSchur
  · exact ClassBShape.of_mulEquiv eJ hX.classBShape
  · exact fun h' => hX.not_partialCentre ((partialCentre_iff_of_mulEquiv eJ).mpr h')
  · exact LocalCores.isQuasisimple_of_mulEquiv eJ hX.quasisimple
  · have h1 := pPrimeCore_map_iso 2 eJ
    rw [hX.pPrimeCore_eq_bot, Subgroup.map_bot] at h1
    exact h1.symm

end CFSG.OddStandard.HigherRank.F3
