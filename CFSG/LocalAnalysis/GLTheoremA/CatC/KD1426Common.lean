module

public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Common

theorem isQuasisimple_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (hG : CFSG.Open.IsQuasisimple G) : CFSG.Open.IsQuasisimple G' := by
  refine ⟨?_, ?_⟩
  · have h1 := Subgroup.map_commutator (⊤ : Subgroup G) (⊤ : Subgroup G) (e : G →* G')
    have hc : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := hG.1
    rw [hc, Subgroup.map_top_of_surjective _ e.surjective] at h1
    exact h1.symm
  · let eq : G ⧸ Subgroup.center G ≃* G' ⧸ Subgroup.center G' :=
      QuotientGroup.congr (Subgroup.center G) (Subgroup.center G') e
        (Subgroup.map_center_eq e)
    haveI : IsSimpleGroup (G ⧸ Subgroup.center G) := hG.2
    exact eq.symm.isSimpleGroup

theorem glaPPrimeCoreOf_eq_bot_of {Y : Type} [Group Y] {K : Subgroup Y}
    (hcore : GLAPPrimeCore 3 ↥K = ⊥) : GLAPPrimeCoreOf 3 K = ⊥ := by
  unfold GLAPPrimeCoreOf
  rw [hcore, Subgroup.map_bot]

theorem glaPLayer_eq_self {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hcore : GLAPPrimeCore 3 ↥K = ⊥) :
    GLAPLayer 3 K = K := by
  have eK : ↥K ⧸ GLAPPrimeCore 3 ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  have hY : CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore 3 ↥K) :=
    isQuasisimple_of_mulEquiv eK.symm hq
  obtain ⟨hcomp, -, hbarX⟩ := glaPLayer_of_isQuasisimple hY
  have hle : GLAPLayer 3 K ≤ K := hcomp.1
  have h2 := sup_glaPPrimeCoreOf_eq_of_barX_eq_top hle hbarX
  rw [glaPPrimeCoreOf_eq_bot_of hcore, sup_bot_eq] at h2
  exact h2

theorem pSimple_mulEquiv {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} {n : ℕ}
    (hcore : GLAPPrimeCore 3 ↥K = ⊥)
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin n)) :
    Nonempty (PSimple 3 K ≃* alternatingGroup (Fin n)) := by
  let e1 : PQuot 3 K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  let e2 : PSimple 3 K ≃* ↥K ⧸ Subgroup.center ↥K :=
    QuotientGroup.congr (Subgroup.center (PQuot 3 K)) (Subgroup.center ↥K) e1
      (Subgroup.map_center_eq e1)
  exact ⟨e2.trans eK⟩

theorem glaPComponent_self {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hcore : GLAPPrimeCore 3 ↥K = ⊥) :
    GLAPComponent 3 K K := by
  have eK : ↥K ⧸ GLAPPrimeCore 3 ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  have hY : CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore 3 ↥K) :=
    isQuasisimple_of_mulEquiv eK.symm hq
  have h := (glaPLayer_of_isQuasisimple hY).1
  rwa [glaPLayer_eq_self hq hcore] at h

theorem isElemAbelian_of_le {Y : Type} [Group Y] {p : ℕ} {E B : Subgroup Y} (hEB : E ≤ B)
    (hB : IsElemAbelian p B) : IsElemAbelian p E := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => hB.2 x (hEB hx)⟩
  have h := hB.1.is_comm.comm (⟨x, hEB x.2⟩ : ↥B) ⟨y, hEB y.2⟩
  apply Subtype.ext
  simpa using congrArg Subtype.val h

theorem isElemAbelian_range {G G' : Type} [Group G] [Group G'] {p : ℕ} {B : Subgroup G}
    (hB : IsElemAbelian p B) (f : ↥B →* G') : IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 x.2
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 y.2
    have hbc : b * c = c * b := hB.1.is_comm.comm b c
    apply Subtype.ext
    show (x : G') * (y : G') = (y : G') * (x : G')
    rw [← hb, ← hc, ← map_mul, ← map_mul, hbc]
  · intro x hx
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 hx
    have hpow : b ^ p = 1 := Subtype.ext (by simpa using hB.2 b.1 b.2)
    rw [← hb, ← map_pow, hpow, map_one]

end CFSG.LocalAnalysis.GLTheoremA.KD1426Common

end
