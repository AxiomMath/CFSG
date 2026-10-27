module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenTen
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ExcPlaneG2Three
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K4143NoExtraLie
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K1410aOut
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28Generic

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.S15.K4143K2

private def quotientCenterMulEquiv {X : Type} [Group X] (L : Subgroup X)
    (hZ : Subgroup.center ↥L = ⊥) : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
  (QuotientGroup.quotientMulEquivOfEq (G := ↥L) hZ).trans
    (QuotientGroup.quotientBot (G := ↥L))

private theorem false_of_small {X : Type} [Group X] [Finite X] {L : Subgroup X} [L.Normal]
    (hZ : Subgroup.center ↥L = ⊥) (h3L : CFSG.Open.pRank 3 L = 3)
    (h3X : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    (hS : (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧
        Nonempty (↥L ≃* alternatingGroup (Fin n))) ∨
      ∃ d : TauCeti.ValidLieTypeIndex,
        ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
          (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
        Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group))
    {R : Subgroup X}
    (hR : CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥R) : False := by
  obtain ⟨hcard, hpow, -, -⟩ := hR
  let c : X →* MulAut ↥L := MulAut.conjNormal (H := L)
  have hexpR : ∀ x ∈ R, x ^ 3 = 1 := by
    intro x hx
    simpa using congrArg Subtype.val (hpow ⟨x, hx⟩)
  have hinj : ∀ x ∈ R, c x = 1 → x = 1 := by
    intro x hx hx1
    have hcen : x ∈ Subgroup.centralizer (L : Set X) :=
      (conjNormal_eq_one_iff_mem_centralizer L).1 hx1
    obtain ⟨k, hk⟩ := (IsPGroup.of_card (p := 3) (n := 5) hcard) ⟨x, hx⟩
    exact eq_one_of_mem_centralizer_of_pow_three_pow hZ h3L.ge h3X.le hcen
      (congrArg Subtype.val hk)
  have hcardT : Nat.card (R.map c) = 3 ^ 5 := by
    have hinj' : Function.Injective (c.subgroupMap R) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      exact Subgroup.mem_bot.2 (Subtype.ext (hinj x x.2 (congrArg Subtype.val hx)))
    rw [← hcard]
    exact (Nat.card_congr (MulEquiv.ofBijective (c.subgroupMap R)
      ⟨hinj', MonoidHom.subgroupMap_surjective c R⟩).toEquiv).symm
  have hexpT : ∀ t ∈ R.map c, t ^ 3 = 1 := by
    rintro t ⟨x, hx, rfl⟩
    rw [← map_pow, hexpR x hx, map_one]
  exact false_of_le_mulAut_small hS hcardT hexpT


private theorem false_of_g2 {X : Type} [Group X] [Finite X] {L : Subgroup X} [L.Normal]
    (hZ : Subgroup.center ↥L = ⊥) (h3L : CFSG.Open.pRank 3 L = 3)
    {q : TauCeti.PrimePower} {hv : (TauCeti.LieTypeIndex.G2 q).Valid} (hp2 : q.p = 2)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃*
      (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : False := by
  have hRankCat :
      CFSG.LieType.SeitzGeneration.RankLE2 3
        (CFSG.LieType.SeitzGeneration.Cat ⟨.G2 q, hv⟩) :=
    CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_cat_G2 q hv
      (by omega : 3 ≠ q.p)
  have hRankQuot : CFSG.LieType.SeitzGeneration.RankLE2 3
      (↥L ⧸ Subgroup.center ↥L) :=
    CFSG.LieType.SeitzGeneration.RankLE2.of_mulEquiv e.symm hRankCat
  obtain ⟨E, hEL, hE, hE27⟩ :=
    CFSG.AGLEmbedding.KFactProofs.G28.exists_elemAbelian_27 h3L.ge
  let qce : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L := quotientCenterMulEquiv L hZ
  let F : Subgroup (↥L ⧸ Subgroup.center ↥L) :=
    (E.subgroupOf L).map qce.symm.toMonoidHom
  have hF : IsElemAbelian 3 F := (hE.subgroupOf L).map qce.symm.toMonoidHom
  have hFcard : Nat.card F = 27 := by
    have h1 : Nat.card (E.subgroupOf L) = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
    have h2 : Nat.card F = Nat.card (E.subgroupOf L) :=
      Subgroup.card_map_of_injective qce.symm.injective
    rw [h2, h1, hE27]
  have hle := hRankQuot F hF
  rw [hFcard] at hle
  norm_num at hle

theorem k4143NoExtraspecial_holds : K4143NoExtraspecial := by
  intro X _ _ L hLn hq hZ hcl h3L h3X R hR
  haveI : L.Normal := hLn
  rcases hcl with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · by_cases hG2 : ∃ q, d.1 = .G2 q
    · obtain ⟨x, hv⟩ := d
      obtain ⟨q, hq⟩ := hG2
      obtain rfl : x = .G2 q := hq
      have hp2 : q.p = 2 := by
        simpa [CFSG.AGLEmbedding.IsClassicalOrG2Index] using hd
      exact false_of_g2 hZ h3L hp2 e
    · exact not_isThreeOnePlusFour_of_classical L hq hZ h3L h3X d hd
        (fun q hq => hG2 ⟨q, hq⟩) e R hR
  · exact false_of_small hZ h3L h3X
      (Or.inl ⟨n, hn, ⟨(quotientCenterMulEquiv L hZ).symm.trans e⟩⟩) hR
  · exact false_of_small hZ h3L h3X
      (Or.inr ⟨d, hd, ⟨(quotientCenterMulEquiv L hZ).symm.trans e⟩⟩) hR

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
