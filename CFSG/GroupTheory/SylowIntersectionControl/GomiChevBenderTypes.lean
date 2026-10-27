module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiBender
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev

import CFSG.GroupTheory.SylowIntersectionControl.GomiL2StatedSL
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCentralQuotient
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedBender
import CFSG.CGT.PushingUp.BenderBridge
import CFSG.RankThree.PartTwo.Census.Classical.Bridges

public section

namespace CFSG.GroupTheory

open Subgroup

private theorem isGomiU3_of_mulEquiv_psu3 {Y : Type} [Group Y] {f : ℕ} (hf : 2 ≤ f)
    (e : Y ≃* CFSG.Open.PSU3 2 f) : IsGomiU3 Y := by
  have hf1 : 1 ≤ f := by omega
  have hmodel : CFSG.Theory.Comparator.PSU3Model f = CFSG.Open.PSU3 2 f :=
    CFSG.Models.benderPSU3Model_eq_psu3 f
  obtain ⟨eSU⟩ := CFSG.CGT.PushingUp.benderBridge_psu (n := f) hf
    (e.trans (MulEquiv.subgroupCongr hmodel.symm))
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf1⟩
  have hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    dsimp only
    have hcard : q.card = 2 ^ f := by
      rw [TauCeti.PrimePower.card_def]
    have hpow : 3 ≤ 2 ^ f := by
      calc 3 ≤ 4 := by norm_num
        _ = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    rw [hcard]
    refine ⟨⟨by norm_num, fun _ => hpow⟩, by simp⟩
  have : Fact (Nat.Prime q.p) := ⟨Nat.prime_two⟩
  exact ⟨⟨.twistedA 2 q, hv⟩, ⟨q, rfl, rfl⟩,
    ⟨eSU.trans (CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU 2 q hv).symm⟩⟩

private theorem isGomiSz_of_mulEquiv_sz {Y : Type} [Group Y] {a : ℕ} (ha : 1 ≤ a)
    (e : Y ≃* CFSG.Open.Sz a) : IsGomiSz Y := by
  obtain ⟨m, hm, ⟨eL⟩⟩ := CFSG.CGT.PushingUp.benderBridge_suzuki ha
    (e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz a).symm))
  exact ⟨⟨.suzuki m, hm⟩, ⟨m, rfl⟩, ⟨eL⟩⟩

theorem isGomiL2_or_isGomiU3_or_isGomiSz_of_fusionIsBenderGroup {Y : Type} [Group Y]
    (h : CFSG.Open.fusionIsBenderGroup Y) : IsGomiL2 Y ∨ IsGomiU3 Y ∨ IsGomiSz Y := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · left
    let F := GaloisField 2 f
    have hcard : Nat.card F = 2 ^ f := GaloisField.card 2 f (by omega)
    have hL2 := isGomiL2_of_mulEquiv_statedSL (K := Matrix.SpecialLinearGroup (Fin 2) F)
      (F := F) hf hcard (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)
    exact hL2.of_mulEquiv e.symm
  · exact Or.inr (Or.inl (isGomiU3_of_mulEquiv_psu3 hf e))
  · exact Or.inr (Or.inr (isGomiSz_of_mulEquiv_sz ha e))

theorem isGomiL2_or_isGomiU3_or_isGomiSz_of_isPIsolatedOver_top (hB : GomiBender) {X : Type}
    [Group X] [Finite X] (hX : IsGomiChevTwo X) (hiso : IsPIsolatedOver 2 (⊤ : Subgroup X) ⊥) :
    IsGomiL2 (X ⧸ center X) ∨ IsGomiU3 (X ⧸ center X) ∨ IsGomiSz (X ⧸ center X) := by
  have htop : IsGomiChevTwo ↥(⊤ : Subgroup X) :=
    IsGomiChevTwo.of_mulEquiv Subgroup.topEquiv.symm hX
  have hq' : CFSG.IsQuasisimple ↥(⊤ : Subgroup X) :=
    CFSG.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hX.1
  have hZ : Odd (Nat.card (Subgroup.center (⊤ : Subgroup X))) :=
    (IsGomiChevTwo.coprime_card_center htop).odd_of_right
  have hcomm : ∀ g : X, (⊤ : Subgroup X).map (MulAut.conj g).toMonoidHom ≠ ⊤ →
      ⁅(⊤ : Subgroup X), (⊤ : Subgroup X).map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
    intro g hg
    exact absurd (Subgroup.map_top_of_surjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).surjective) hg
  have hq : IsPGroup 2 (X ⧸ Subgroup.normalClosure (⊤ : Set X)) := by
    have hsub : Subsingleton (X ⧸ Subgroup.normalClosure (⊤ : Set X)) :=
      QuotientGroup.subsingleton_iff.mpr (Subgroup.normalClosure_eq_self (⊤ : Subgroup X))
    exact @IsPGroup.of_subsingleton 2 (X ⧸ Subgroup.normalClosure (⊤ : Set X)) _ hsub
  have hO : ∀ K : Subgroup X, K.Normal → IsPGroup 2 K → K = ⊥ := by
    intro K hKn hKp
    exact le_bot_iff.mp
      ((CFSG.LieType.BorelTits.le_pCore 2 hKn hKp).trans (le_of_eq hX.2.1))
  obtain ⟨-, hBender⟩ :=
    eq_top_of_isPIsolatedOver hB (L := ⊤) hiso hcomm hq hO (Or.inr ⟨hq', hZ⟩)
  exact isGomiL2_or_isGomiU3_or_isGomiSz_of_fusionIsBenderGroup (hBender hq')

theorem isGomiL2_or_isGomiU3_or_isGomiSz_of_isPIsolatedOver (hB : GomiBender) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (hL : IsGomiChevTwo ↥L)
    (hiso : IsPIsolatedOver 2 L ⊥) :
    IsGomiL2 (↥L ⧸ center ↥L) ∨ IsGomiU3 (↥L ⧸ center ↥L) ∨ IsGomiSz (↥L ⧸ center ↥L) := by
  have hiso' : IsPIsolatedOver 2 (L.subgroupOf L) ((⊥ : Subgroup G).subgroupOf L) :=
    (isPIsolatedOver_subgroupOf_iff (H := (⊥ : Subgroup G)) (K := L) (K' := L) bot_le
      le_rfl).mpr hiso
  rw [Subgroup.subgroupOf_self, Subgroup.bot_subgroupOf] at hiso'
  exact isGomiL2_or_isGomiU3_or_isGomiSz_of_isPIsolatedOver_top hB hL hiso'

end CFSG.GroupTheory
