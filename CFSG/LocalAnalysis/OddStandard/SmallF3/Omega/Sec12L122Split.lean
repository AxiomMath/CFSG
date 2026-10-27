module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12InputsSplitM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameB0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Aux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L44
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

namespace PspFrame

variable {G : Type} [Group G] {L : Subgroup G} (F : PspFrame L)

theorem le_normalizer_pre_B0
    {S : Subgroup G} (hF : F.img (S ⊓ L) = QT0.originalSubgroup)
    (hSN : S ≤ normalizer (L : Set G)) : S ≤ normalizer (F.pre B0 : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  haveI : IsMulCommutative (F.pre B0) := F.isElemAbelian_pre_B0.1
  refine F.eq_pre_B0_of_abelian hF inf_le_right ?_ inferInstance ?_
  · rintro _ ⟨b, hb, rfl⟩
    have hbP : b ∈ S ⊓ L := F.pre_B0_le hF inf_le_right hb
    show s * b * s⁻¹ ∈ S ⊓ L
    exact Subgroup.mem_inf.2 ⟨S.mul_mem (S.mul_mem hs hbP.1) (S.inv_mem hs),
      (Subgroup.mem_normalizer_iff.1 (hSN hs) b).1 hbP.2⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj s).injective, F.card_pre_B0]

end PspFrame

theorem asc82FactSplit5_of_model
    (hm : Asc82FactSplitModel) : Asc82FactSplit5 := by
  obtain ⟨X, -, hXB, hXprod⟩ := hm
  intro G _ _ t L S _ _ _ hctx hPSp hSN hCS hSyl htL
  obtain ⟨F0⟩ := exists_pspFrame hPSp
  obtain ⟨F, hF⟩ := F0.exists_frame_syl hSyl
  have hB : secB S L = F.pre B0 := F.jElem_eq hF inf_le_right
  have hLt : L ≤ centralizer ({t} : Set G) := hctx.component.le
  have ht2 : orderOf t = 2 := hctx.involution
  have htC : t ∈ centralizer (L : Set G) := by
    have h : t ∈ centralizer (L : Set G) ⊓ S := by rw [hCS]; exact Subgroup.mem_zpowers t
    exact h.1
  have hAL : secA t S L ⊓ L = secB S L := sec4_sup_zpowers_inf (secB_le_L S L) htC htL ht2
  have hML : secM t S L ⊓ L = L ⊓ normalizer (secB S L : Set G) := by
    rw [secM, inf_comm]
    exact sec4_inf_normalizer_eq hLt rfl hAL
  have hSB : S ≤ normalizer (secB S L : Set G) := by
    rw [hB]
    exact F.le_normalizer_pre_B0 hF hSN
  have hYL : (secM t S L ⊓ L) ⊔ S ≤ normalizer (L : Set G) :=
    sup_le (inf_le_right.trans Subgroup.le_normalizer) hSN
  have hYB : (secM t S L ⊓ L) ⊔ S ≤ normalizer (secB S L : Set G) :=
    sup_le (by rw [hML]; exact inf_le_right) hSB
  have hBY : secB S L ≤ (secM t S L ⊓ L) ⊔ S := (secB_le_S S L).trans le_sup_right
  let Xg : Subgroup G := (X.comap F.φ).map (normalizer (L : Set G)).subtype
  have hXg : ∀ g : G, g ∈ Xg ↔ ∃ h : g ∈ normalizer (L : Set G), F.φ ⟨g, h⟩ ∈ X := by
    intro g
    simp only [Xg, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨h, hg⟩
      exact ⟨⟨g, h⟩, hg, rfl⟩
  refine ⟨Xg ⊓ ((secM t S L ⊓ L) ⊔ S), ?_, ?_⟩
  ·
    refine eq_bot_iff.2 fun g hg => ?_
    obtain ⟨hgXY, hgB⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨hgN, hgφ⟩ := (hXg g).1 (Subgroup.mem_inf.1 hgXY).1
    rw [hB] at hgB
    obtain ⟨hgL, hgψ⟩ := F.mem_pre.1 hgB
    have h1 : F.ψ ⟨g, hgL⟩ ∈ X ⊓ B0 := Subgroup.mem_inf.2 ⟨hgφ, hgψ⟩
    rw [hXB, Subgroup.mem_bot] at h1
    have h2 : (⟨g, hgL⟩ : ↥L) = 1 := F.ψ_injective (by rw [h1, map_one])
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)
  ·
    refine le_antisymm (sup_le inf_le_right hBY) fun y hy => ?_
    have hyN : y ∈ normalizer (L : Set G) := hYL hy
    have hyB : y ∈ normalizer (F.pre B0 : Set G) := hB ▸ hYB hy
    let yN : ↥(normalizer (L : Set G)) := ⟨y, hyN⟩
    have hφn : F.φ yN ∈ QA45.originalSubgroup ⊓ normalizer (B0 : Set P45) :=
      Subgroup.mem_inf.2 ⟨F.mem_A yN, mem_normalizer_B0 (fun b hb => F.phi_conj_mem_B0 yN hyB hb)
        (fun b hb => F.phi_conj_inv_mem_B0 yN hyB hb)⟩
    obtain ⟨x, hx, b, hb, hxb⟩ := hXprod _ hφn
    obtain ⟨l, hl⟩ := F.ψ_surj (B0_le_P hb)
    have hlB : (l : G) ∈ secB S L := hB ▸ F.mem_pre.2 ⟨l.2, by rw [hl]; exact hb⟩
    have hx0 : y * (l : G)⁻¹ ∈ Xg ⊓ ((secM t S L ⊓ L) ⊔ S) := by
      refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mul_mem _ hy (Subgroup.inv_mem _ (hBY hlB))⟩
      refine (hXg _).2 ⟨Subgroup.mul_mem _ hyN (Subgroup.inv_mem _ (Subgroup.le_normalizer l.2)),
        ?_⟩
      have hmul : (⟨y * (l : G)⁻¹, Subgroup.mul_mem _ hyN (Subgroup.inv_mem _
          (Subgroup.le_normalizer l.2))⟩ : ↥(normalizer (L : Set G))) =
          yN * (⟨(l : G), Subgroup.le_normalizer l.2⟩ : ↥(normalizer (L : Set G)))⁻¹ := rfl
      rw [hmul, map_mul, map_inv, ← F.ψ_apply l, hl, hxb, mul_inv_cancel_right]
      exact hx
    have hy' : y = (y * (l : G)⁻¹) * (l : G) := by group
    rw [hy']
    exact Subgroup.mul_mem_sup hx0 hlB

end CFSG.OddStandard.SmallF3.Omega
