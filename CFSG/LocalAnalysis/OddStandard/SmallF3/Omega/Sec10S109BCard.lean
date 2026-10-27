module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10JWb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TwoCore
public import CFSG.Walter.W67.W1Basic
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Walter.JRAssembly

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10B_card_twoCoreIn (X : Subgroup G) (e : ↥X ≃* SL23) :
    Nat.card (twoCoreIn X) = 8 := by
  unfold twoCoreIn CFSG.inSubgroup
  rw [Subgroup.card_map_of_injective X.subtype_injective]
  calc Nat.card (CFSG.pCore 2 ↥X)
      = Nat.card ((CFSG.pCore 2 ↥X).map e.toMonoidHom) :=
        (Subgroup.card_map_of_injective e.injective).symm
    _ = Nat.card (CFSG.pCore 2 SL23) := by rw [CFSG.pCore_map_iso 2 e]
    _ = 8 := sl23_card_pCore

variable [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}

theorem sec10B_card_Q (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) : 32 ≤ Nat.card ↥(secQ K1 K2) := by
  obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := sec10KS_equiv hP5 hC5 hpsp hctx
  have hcomm : ∀ a ∈ twoCoreIn K1, ∀ b ∈ twoCoreIn K2, a * b = b * a := fun a ha b hb =>
    sec10Z_comm hP5 hpsp hctx a (twoCoreIn_le_self K1 ha) b (twoCoreIn_le_self K2 hb)
  have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute (twoCoreIn K1) (twoCoreIn K2)
    hcomm).1
  rw [sec10B_card_twoCoreIn K1 e1, sec10B_card_twoCoreIn K2 e2] at h
  have hle : twoCoreIn K1 ⊓ twoCoreIn K2 ≤ zpowers z := by
    rw [← (sec10KS_main hP5 hC5 hpsp hctx).2.2]
    exact inf_le_inf (twoCoreIn_le_self K1) (twoCoreIn_le_self K2)
  have hinf : Nat.card ↥(twoCoreIn K1 ⊓ twoCoreIn K2) ≤ 2 :=
    calc Nat.card ↥(twoCoreIn K1 ⊓ twoCoreIn K2) ≤ Nat.card ↥(zpowers z) :=
          Subgroup.card_le_of_le hle
      _ = 2 := by rw [Nat.card_zpowers, hctx.toSec10Z.pocket.1]
  have hpos : 0 < Nat.card ↥(twoCoreIn K1 ⊓ twoCoreIn K2) := Nat.card_pos
  rw [sec10KS_twoCore_sup hP5 hC5 hpsp hctx]
  have hb : Nat.card ↥(twoCoreIn K1 ⊓ twoCoreIn K2) = 1 ∨
      Nat.card ↥(twoCoreIn K1 ⊓ twoCoreIn K2) = 2 := by omega
  rcases hb with hb | hb <;> rw [hb] at h <;> omega

theorem sec10B_card_W (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) (hb : Asc82Basic10)
    (hctx : Sec10Ctx G t L S z K1 K2) : 64 ≤ Nat.card ↥(secW t K1 K2) := by
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  have hQ := sec10B_card_Q hP5 hC5 hpsp hctx
  have hle : secQ K1 K2 ≤ secW t K1 K2 := le_sup_left
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
  have hne : Nat.card ↥(secW t K1 K2) ≠ Nat.card ↥(secQ K1 K2) := by
    intro heq
    have hEq := Subgroup.eq_of_le_of_card_ge hle heq.le
    exact sec10J_t_notin_Q hP5 hb hctx (hEq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hpos : 0 < Nat.card ↥(secW t K1 K2) := Nat.card_pos
  rcases m with _ | _ | m
  · omega
  · exact absurd (by simpa using hm) hne
  · have := Nat.mul_le_mul_left (Nat.card ↥(secQ K1 K2)) (show 2 ≤ m + 1 + 1 by omega)
    omega

end CFSG.OddStandard.SmallF3.Omega
