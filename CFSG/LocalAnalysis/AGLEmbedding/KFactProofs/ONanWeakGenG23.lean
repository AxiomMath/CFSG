module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenCommon
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaThreeWeakRes
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.LieType.Multipliers.G23Bridge
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Prime
public import CFSG.Adapters.TauCetiExceptional.BridgeG2
public import CFSG.Blueprint.MatrixSeedIdentification
public import Certificates.Certificate9436
import all CFSG.LieType.Multipliers.G23Bridge

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

open TauCeti CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Multipliers.G23
  CFSG.Sporadic.He.Native CFSG.SectionRank CFSG.SectionRank.Native
  CFSG.RankThree.PartTwo.Census.Carrier

section Model

variable {K : Type} [Field K] (σ : K ≃+* ZMod 3)

theorem val_matHom_aElt :
    ((matHom σ (aElt σ) : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
      toMat 3 14 aArr :=
  val_matHom_prod σ aWord

theorem val_matHom_bElt :
    ((matHom σ (bElt σ) : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
      toMat 3 14 bArr :=
  val_matHom_prod σ bWord

theorem seedMonoid_eq_G23 :
    NativeSporadic.seedMonoid 3 14 1 R3.G23Three.seedA R3.G23Three.seedB =
      Submonoid.closure {((matHom σ (aElt σ) : GL (Fin 14) (ZMod 3)) :
        Matrix (Fin 14) (Fin 14) (ZMod 3)),
        ((matHom σ (bElt σ) : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3))} := by
  unfold NativeSporadic.seedMonoid
  rw [Certificates.certificate9436.2.2.1, Certificates.certificate9436.2.2.2,
    val_matHom_aElt, val_matHom_bElt]

theorem closure_matHom_gens :
    Subgroup.closure {matHom σ (aElt σ), matHom σ (bElt σ)} = (matHom σ).range := by
  have h := closure_range_gens (K := K) σ
  have hr : Set.range (gens σ) = {aElt σ, bElt σ} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [hr] at h
  rw [MonoidHom.range_eq_map, ← h, MonoidHom.map_closure, Set.image_pair]

noncomputable def seedEquivG2 :
    (NativeSporadic.seedMonoid 3 14 1 R3.G23Three.seedA R3.G23Three.seedB)ˣ ≃*
      ↥(adjointGroup .G2 K) := by
  rw [seedMonoid_eq_G23 σ]
  exact (NativeSporadic.unitSeedEquiv (matHom σ (aElt σ)) (matHom σ (bElt σ))).trans
    ((MulEquiv.subgroupCongr (closure_matHom_gens σ)).trans
      (MonoidHom.ofInjective (matHom_injective σ)).symm)

end Model

theorem weakGenG23 :
    WeakGenG23 := by
  intro q hv hq
  have hdvd : q.p ∣ 3 := by
    rw [← hq, PrimePower.card_def]
    exact dvd_pow_self _ q.exponent_pos.ne'
  have hp3 : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hdvd
  obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv (by rw [hp3]; norm_num) (ZMod 3)
    (by rw [Nat.card_zmod, hq])
  let e := (seedEquivG2 (RingEquiv.refl (ZMod 3))).trans
    ((adjointQuotientG2Equiv (ZMod 3)).symm.trans b)
  have : Fact (Nat.Prime R3.G23Three.cpSpec.p) := ⟨by show Nat.Prime 3; norm_num⟩
  exact coverWeakGen_of_check (spec3 14) (D := R3.G23Three.cpSpec) (by show (3 : ℕ) ≠ 2; norm_num)
    Certificates.certificate9436.1 Certificates.certificate9436.2.1 e

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
