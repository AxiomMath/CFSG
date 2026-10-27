module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Data
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3He
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3M24
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Mathieu
public import CFSG.Sporadic.Schreier.PairHSFaithful
public import CFSG.Sporadic.Schreier.PairJ2Faithful
public import Certificates.Certificate13513
public import Certificates.Certificate13514

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3

theorem noL3Eq_of_ord {D : Data} {N : ℕ} (h : D.ord = N) (hB : 12 * N < 44 ^ 8)
    (hc : L3Check N 40 = true) : NoL3Eq D.ord := by
  rw [h]
  exact noL3Eq_of_check (B := 40) (by simpa using hB) hc

theorem sporL3DownInner_M11 (hbr : SporadicBridges) :
    SporL3DownInner .M11 :=
  sporL3DownInner_of_check m11S3Data Certificates.certificate13511.1 rep_m11A rep_m11B
    NativeSporadic.M11 rfl (hbr .M11)
    (noL3Eq_of_ord (N := 7920) rfl (by norm_num) (by decide +kernel)) (by decide +kernel)

theorem sporL3DownInner_M12 (hbr : SporadicBridges) :
    SporL3DownInner .M12 :=
  sporL3DownInner_of_check m12S3Data Certificates.certificate13511.2.1 rep_m12A rep_m12B
    NativeSporadic.M12 rfl (hbr .M12)
    (noL3Eq_of_ord (N := 95040) rfl (by norm_num) (by decide +kernel)) (by decide +kernel)

theorem sporL3DownInner_M22 (hbr : SporadicBridges) :
    SporL3DownInner .M22 :=
  sporL3DownInner_of_check m22S3Data Certificates.certificate13511.2.2.1 rep_m22A rep_m22B
    NativeSporadic.M22 rfl (hbr .M22)
    (noL3Eq_of_ord (N := 443520) rfl (by norm_num) (by decide +kernel)) (by decide +kernel)

theorem sporL3DownInner_M23 (hbr : SporadicBridges) :
    SporL3DownInner .M23 :=
  sporL3DownInner_of_check m23S3Data Certificates.certificate13511.2.2.2 rep_m23A rep_m23B
    NativeSporadic.M23 rfl (hbr .M23)
    (noL3Eq_of_ord (N := 10200960) rfl (by norm_num) (by decide +kernel)) (by decide +kernel)

theorem sporL3DownInner_M24 (hbr : SporadicBridges) :
    SporL3DownInner .M24 :=
  sporL3DownInner_of_check m24S3Data Certificates.certificate13512 rep_m24A rep_m24B
    NativeSporadic.M24 rfl (hbr .M24)
    (noL3Eq_of_ord (N := 244823040) rfl (by norm_num) (by decide +kernel)) (by decide +kernel)

theorem sporL3DownInner_J2
    (hbr : SporadicBridges) :
    SporL3DownInner .J2 := by
  have h := Certificates.certificate13513
  obtain ⟨hvA, hvB⟩ := check_valid h
  exact sporL3DownInner_of_check j2S3Data h (CFSG.RankThree.Native.rep_of_validA hvA)
    (CFSG.RankThree.Native.rep_of_validA hvB) CFSG.Sporadic.Schreier.j2P rfl
    ⟨CFSG.Sporadic.Schreier.j2PermEquiv.symm.trans (hbr .J2).some⟩
    (noL3Eq_of_ord (N := 604800) rfl (by norm_num) (by decide +kernel)) (by decide +kernel)

theorem sporL3DownInner_HS
    (hbr : SporadicBridges) :
    SporL3DownInner .HS := by
  have h := Certificates.certificate13514
  obtain ⟨hvA, hvB⟩ := check_valid h
  exact sporL3DownInner_of_check hsS3Data h (CFSG.RankThree.Native.rep_of_validA hvA)
    (CFSG.RankThree.Native.rep_of_validA hvB) CFSG.Sporadic.Schreier.hsP rfl
    ⟨CFSG.Sporadic.Schreier.hsPermEquiv.symm.trans (hbr .HS).some⟩
    (noL3Eq_of_ord (N := 44352000) rfl (by norm_num) (by decide +kernel)) (by decide +kernel)

theorem sporL3DownInner_J1 (hbr : SporadicBridges) :
    SporL3DownInner .J1 := by
  haveI : Finite NativeSporadic.J1 := Nat.finite_of_card_ne_zero (by
    rw [CFSG.Sporadic.J1.card_J1]; norm_num)
  exact sporL3DownInner_of_ninth NativeSporadic.J1 (hbr .J1) (by
    rw [CFSG.Sporadic.J1.card_J1]; norm_num)

theorem sporL3DownInner_He
    (hbr : SporadicBridges) :
    SporL3DownInner .He := by
  refine sporL3DownInner_of_model _ ⟨CFSG.Sporadic.HeldB.heEquivP.symm.trans (hbr .He).some⟩
    (by
      rw [CFSG.Sporadic.HeldB.card_heP]
      exact noL3Eq_of_ord (D := heS3Data) (N := 4030387200) rfl (by norm_num) (by decide +kernel))
    fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin 8330)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have hcc : Nat.card (Subgroup.centralizer ({x} : Set ↥CFSG.Sporadic.HeldB.heP)) =
      Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin 8330))} : Set (Equiv.Perm (Fin 8330))) ⊓
        CFSG.Sporadic.HeldB.heP) := by
    rw [← map_centralizer_subtype CFSG.Sporadic.HeldB.heP x,
      Subgroup.card_map_of_injective CFSG.Sporadic.HeldB.heP.subtype_injective]
  rw [hcc]
  rcases he3_card x.2 hx3 with h | h <;> rw [h] <;> norm_num

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
