module

public import CFSG.GH74.Filter.Sporadic.Spec
public import CFSG.GH74.Generic.Certificates
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public meta import Certificates.Data.CFSGNative.Filter.Sec2
public meta import Certificates.Data.CFSGNative.SectionRank.F3
public meta import Certificates.Data.CFSGNative.SectionRank.Fp
import all CFSG.Blueprint.NativeSporadic
public import CFSG.GH74.Generic.NativeCertsInputs
public meta import CFSG.GH74.Generic.NativeCertsInputs
public import Certificates.Certificate5106

public section

namespace CFSG.GH74.Generic

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem rankCertified_of_secCheck {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
    [NeZero p] [Inhabited M] (D : SecData) (h : O.secCheck D = true) {s : ℕ}
    (hs : s < D.outs.length) :
    RankCertified (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ s := by
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB
  have hA : Sp.WF (O.decode D.seedA) ∧ Sp.toMat (O.decode D.seedA) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert _ _)⟩
  have hB : Sp.WF (O.decode D.seedB) ∧ Sp.toMat (O.decode D.seedB) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  obtain ⟨r, hrr, t, x, ht, hc, hsq, hcomm, hker⟩ := Sp.exists_of_secCheck S D hA hB h
  subst hrr
  exact rankCertified_of_central_section t ht x hc hsq hcomm hker hs

theorem mclSec_check :
    (ops3 21).secCheck mclSec = true :=
  Certificates.certificate5106.1

theorem rankCertified_McL :
    RankCertified CFSG.Blueprint.NativeSporadic.McL 3 :=
  rankCertified_of_secCheck (spec3 21) mclSec mclSec_check (by decide)

theorem rankCertified_of_isSporadic_McL {S : Type} [Group S]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic S .McL) : RankCertified S 3 := by
  obtain ⟨e⟩ := h
  exact rankCertified_McL.of_mulEquiv e.symm

theorem lySec_check :
    (opsP 5 111).secCheck lySec = true :=
  Certificates.certificate5106.2

theorem rankCertified_Ly :
    RankCertified CFSG.Blueprint.NativeSporadic.Ly 3 :=
  rankCertified_of_secCheck (specP 5 111) lySec lySec_check (by decide)

theorem rankCertified_of_isSporadic_Ly {S : Type} [Group S]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic S .Ly) : RankCertified S 3 := by
  obtain ⟨e⟩ := h
  exact rankCertified_Ly.of_mulEquiv e.symm

end CFSG.GH74.Generic
