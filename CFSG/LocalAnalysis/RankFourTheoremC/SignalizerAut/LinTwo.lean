module

public import CFSG.LocalAnalysis.RankFourTheoremC.SignalizerAut.Basic
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieNonUnitaryLin

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.AGLEmbedding Subgroup

theorem signalizerAutAt_linTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} {n : ℕ} (hn : 2 ≤ n) (hd : IsLinTwoIndex p n d) :
    SignalizerAutAt p (.lie d) := by
  haveI hpf : Fact p.Prime := ⟨hp⟩
  have hout : ¬ GL83OuterType24 p (.lie d) := by
    rintro ⟨d', hd', ⟨-, hq'⟩ | ⟨-, hs⟩⟩
    · obtain rfl := TauCeti.CFSGIndex.lie.inj hd'
      obtain ⟨q, hq, hqp, -⟩ := hd
      obtain ⟨q', hq'', hqp', -⟩ := hq'
      rw [hq] at hq''
      cases hq''
      omega
    · obtain rfl := TauCeti.CFSGIndex.lie.inj hd'
      obtain ⟨q, hq, -, -⟩ := hd
      rw [hq] at hs
      cases hs
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  obtain ⟨U⟩ : Nonempty (Sylow p (PSL2GF p n)) := inferInstance
  have hcard : Nat.card (U : Subgroup (PSL2GF p n)) = p ^ n :=
    (psl2GF_sylow p n (by omega) U).2
  have hfac : (Nat.card (PSL2GF p n)).factorization p = n :=
    CFSG.SectionRank.OddCover.factorization_card_psl_two hp hp2 (GaloisField.card p n (by omega))
  have hTI : WeakTI (U : Subgroup (PSL2GF p n)) := by
    intro g x hx hx1 hgx
    have h := psl2GF_ti hp2 (by omega) U x hx hx1 g⁻¹ (by rw [inv_inv]; exact hgx)
    have h' := (Subgroup.normalizer ((U : Subgroup (PSL2GF p n)) : Set (PSL2GF p n))).inv_mem h
    rwa [inv_inv] at h'
  exact signalizerAutAt_of_model_weakTI hp hout e.symm
    (CFSG.AGLEmbedding.KFactProofs.NonUnitary.center_psl2GF' (p := p) hn)
    (R := (U : Subgroup (PSL2GF p n))) (by rw [hfac, hcard]) hTI

end CFSG.LocalAnalysis.RankFourTheoremC
