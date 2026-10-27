module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeAlpha
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner_le_innAutDerived)

private theorem card_pSimple_dvd_lt {G : Type} [Group G] [Finite G] {α : MulAut G} (hα : α ≠ 1)
    {J : Subgroup G} (hJ : GLAPComponent 3 (fixSubgroup α) J) :
    Nat.card (PSimple 3 J) ∣ Nat.card G ∧ Nat.card (PSimple 3 J) < Nat.card G := by
  have hdvd : Nat.card (PSimple 3 J) ∣ Nat.card J :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)
  have hne : J ≠ ⊤ := by
    intro htop
    apply hα
    ext g
    exact mem_fixSubgroup.1 (hJ.1 (by rw [htop]; exact Subgroup.mem_top g))
  have hlt : Nat.card J < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group J)
      fun h => hne ((Subgroup.card_eq_iff_eq_top J).1 h)
  exact ⟨hdvd.trans (Subgroup.card_subgroup_dvd_card J),
    (Nat.le_of_dvd Nat.card_pos hdvd).trans_lt hlt⟩


theorem QSNL.exists_alphaD {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (hN : QSNL 3 S B T x D K) (h3K : 3 ∣ Nat.card ↥K) :
    ∃ d₀ ∈ D, d₀ ∉ Subgroup.zpowers x ∧ d₀ ^ 3 = 1 ∧
      S ⊓ Subgroup.centralizer (D : Set Ω) = S ⊓ Subgroup.centralizer ({d₀} : Set Ω) ∧
      GLAPComponent 3 (S ⊓ Subgroup.centralizer ({d₀} : Set Ω)) K ∧
      ∃ hdN : d₀ ∈ Subgroup.normalizer (S : Set Ω),
        chevAut 3 S ⟨d₀, hdN⟩ ^ 3 = 1 ∧ chevAut 3 S ⟨d₀, hdN⟩ ≠ 1 ∧
        chevAut 3 S ⟨d₀, hdN⟩ ∈ innAutDerived (PSimple 3 S) ∧
        GLAPComponent 3 (fixSubgroup (chevAut 3 S ⟨d₀, hdN⟩)) (chevTransfer 3 S K) ∧
        Nonempty (PSimple 3 K ≃* PSimple 3 (chevTransfer 3 S K)) ∧
        Nat.card (PSimple 3 K) ∣ Nat.card (PSimple 3 S) ∧
        Nat.card (PSimple 3 K) < Nat.card (PSimple 3 S) := by
  have hc := hN.cfg
  have hpre := hc.std
  obtain ⟨d₀, hdD, hdx⟩ := S171.exists_y Nat.prime_three hc.x1 hpre
  have hd3 : d₀ ^ 3 = 1 := hpre.2.1.2 d₀ hdD
  have hSx : S ≤ Subgroup.centralizer ({x} : Set Ω) := fun s _ =>
    Subgroup.mem_centralizer_singleton_iff.2 (hc.xcen s)
  have hcs := S171.L_cs_eq Nat.prime_three hc.x1 hpre hdD hdx hSx
  have hK : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({d₀} : Set Ω)) K := by
    rw [← hcs]
    exact (hN.nlAct h3K).comp
  have hdN : d₀ ∈ Subgroup.normalizer (S : Set Ω) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hc.normal]
    exact Subgroup.mem_top d₀
  have hdp := isPGroup_zpowers_of_pow_eq_one hd3
  have hqS := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hc.comp
  obtain ⟨lab, hLabQ, hinDiag⟩ := I141F.innDiagKind_chevAut hdN hqS
    (innDiagOn_mono hc.inn (Subgroup.zpowers_le.2 (hpre.1 hdD)))
  have hcen := Y10F.center_centerQuot_eq_bot hqS
  obtain ⟨hsimp, hnc⟩ := chev_pSimple_simple_nonabelian Nat.prime_three hc.comp
  haveI := hsimp
  have hLab := Y10F.hasLabel_of_equiv_centerQuot
    (CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_isQuasisimple_of_simple hnc).1
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm hLabQ
  have hα3 := chevAut_pow_eq_one 3 S hdN hd3
  have hder : chevAut 3 S ⟨d₀, hdN⟩ ∈ innAutDerived (PSimple 3 S) := by
    by_cases hB2 : lab.tag = .B2der
    · exact inner_le_innAutDerived _ (T171S.inner_of_hasLabel_B2der hLab hcen hB2 hα3)
    by_cases hG2 : lab.tag = .G2der
    · exact inner_le_innAutDerived _ (T171S.inner_of_hasLabel_G2der hLab hcen hG2 hα3)
    by_cases hTw : lab.tag = .twF4der
    · exact inner_le_innAutDerived _ (T171S.inner_of_hasLabel_twF4der hLab hcen hTw hα3)
    exact I141F.Tri.mem_innAutDerived_of_innDiagKind_of_not_derived hcen ⟨hB2, hG2, hTw⟩
      hinDiag
  have hα1 : chevAut 3 S ⟨d₀, hdN⟩ ≠ 1 := fun h1 =>
    hdx ((hc.centB d₀ (hpre.1 hdD)).1 ((chevAut_eq_one_iff Nat.prime_three hc.comp hdN).1 h1))
  have hJ := glaPComponent_chevTransfer Nat.prime_three hdN hdp hK
  obtain ⟨e⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three hdN hdp hK
  obtain ⟨h1, h2⟩ := card_pSimple_dvd_lt hα1 hJ
  have hce : Nat.card (PSimple 3 K) = Nat.card (PSimple 3 (chevTransfer 3 S K)) :=
    Nat.card_congr e.toEquiv
  exact ⟨d₀, hdD, hdx, hd3, hcs, hK, hdN, hα3, hα1, hder, hJ, ⟨e⟩, hce ▸ h1, hce ▸ h2⟩

end CFSG.LocalAnalysis.GLTheoremA.S265

end
