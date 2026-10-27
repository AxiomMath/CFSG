module

public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremC
public import CFSG.RankThree.PartTwo.Sec19.F194Item316X

public section

namespace CFSG.CGT.Hall82

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19

structure Setting (G : Type) [Group G] [Finite G] (M L : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G
  charTwo : CFSG.Assembly.IsCharTwoType G
  maxLocal : CFSG.IsMaximalTwoLocal M
  block : IsBlock M L
  perfect : ⁅L, L⁆ = L
  type : IsA6Z3Type L
  elemU : CFSG.Open.IsElemAbelian 2 (blockU L)
  uniq : CFSG.maximalTwoLocalsContaining (L : Set G) = {M}
  cent : ∀ t ∈ CFSG.Open.pCoreOf 2 M, t ≠ 1 →
    CFSG.generalizedFitting ↥(Subgroup.centralizer ({t} : Set G)) =
      CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set G))
  normalizer_eq : Subgroup.normalizer (L : Set G) = M

theorem lit316Hall_of_setting (hC : CFSG.CGT.PushingUpLit.FooteNonsolvableSimple)
    (h : ∀ (G : Type) [Group G] [Finite G] (M L : Subgroup G), Setting G M L →
      CFSG.Assembly.InCatalog G) :
    Lit316Hall := by
  intro G _ _ hs hn hK hc M L hM hB hperf htype hab huniq hcent
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    SimsTheoremC.isQuasisimple_of_isFType hB.1 (Or.inr (Or.inr (Or.inr (Or.inr htype))))
  have hnorm : (L.subgroupOf M).Normal :=
    hC G hs hK hc M L hM hB.2.1 hB.2.2 (isShortGroup_of_isShort hB.1) hq huniq
  exact h G M L ⟨hs, hn, hK, hc, hM, hB, hperf, htype, hab, huniq, hcent,
    SimsTheoremC.normalizer_eq_of_normal hM hB.2.1 hnorm hB.1⟩

namespace Setting

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G} (S : Setting G M L)
include S

theorem le : L ≤ M := S.block.2.1

theorem short : IsShort L := S.block.1

theorem normal {m : G} (hm : m ∈ M) {x : G} (hx : x ∈ L) : m * x * m⁻¹ ∈ L := by
  rw [← S.normalizer_eq] at hm
  exact (Subgroup.mem_normalizer_iff.mp hm x).mp hx

theorem centralizer_le : Subgroup.centralizer (L : Set G) ≤ M := by
  rw [← S.normalizer_eq]
  exact Subgroup.centralizer_le_normalizer (L : Set G)

theorem quasisimple : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
  SimsTheoremC.isQuasisimple_of_isFType S.short (Or.inr (Or.inr (Or.inr (Or.inr S.type))))

theorem card_quot : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080 :=
  SimsTheoremC.card_quot_of_isA6Z3Type S.type

end Setting

end CFSG.CGT.Hall82
