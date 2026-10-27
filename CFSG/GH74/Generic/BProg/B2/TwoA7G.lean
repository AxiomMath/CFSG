module

public import CFSG.GH74.Generic.BProg.B2.TwoA7
public import CFSG.GH74.Generic.BProg.B2.TwoA7TermG
public import CFSG.GH74.Generic.BProg.B2.TwoA7Comp
public import CFSG.GH74.Generic.BProg.B2.TwoA7Syl

public section

namespace CFSG.GH74.Generic.BProg.B2.SD.TwoA7G

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.GH74.Generic.BProg.B2.SD.TwoA7 CFSG.GH74.Generic.BProg.B2.SD.TwoA7Term
open CFSG.GH74.Generic.BProg.B2

variable {G : Type} [Group G] [Finite G]

theorem twoA7_centralized {x : G} {K A M P Q H B : Subgroup G} {h : G}
    (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1Core x K M Q H)
    (hQS : QbarSylow M K Q) (hK : TwoA7TermG.PumpupTwoA7GH)
    (S : Sym8A M B h) (J : Subgroup (Mbar M)) (hJ : IsComponent J)
    (hA7 : Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7))) (hZ : center ↥J ≠ ⊥) :
    barIn M (sigX M h) ≤ centralizer (J : Set (Mbar M)) := by
  have _hS := S
  exfalso
  have hdc : IsDoubleCoverOfAlt ↥J 7 := J_doubleCover J hJ hA7 hZ
  have hJK := J_commute_barK h1 J hJ hdc
  obtain ⟨u, huQ, hu2, huM, huJ, huJc⟩ := exists_u hs h1 hQS J hJ hdc hJK
  obtain ⟨I, hILo, huI, hcov⟩ := exists_twoA7_pair hs h1 hJ hdc hJK huQ hu2 huM huJ huJc
  have hG : IsKProperSimple G :=
    GLS.isKProperSimple_of_kgh hs.hyp.simple hs.hyp.nonab hs.hyp.kgh
  have hterm : IsTwoTerminal u I :=
    TwoA7TermG.isTwoTerminal_of_twoA7 hK hs.hyp.kgh hG hILo huI hcov
  refine hs.hyp.noThin ⟨u, I, hterm, ⟨⟨hcov.1, Or.inr (Or.inr (Or.inr (Or.inl
    ⟨7, le_rfl, by norm_num, hcov⟩)))⟩, ?_⟩⟩
  intro hbot
  have h2 := hcov.2.1
  rw [hbot] at h2
  simp at h2

end CFSG.GH74.Generic.BProg.B2.SD.TwoA7G
