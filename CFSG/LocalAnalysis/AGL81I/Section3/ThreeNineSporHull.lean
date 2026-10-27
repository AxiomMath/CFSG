module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.OPPrimeHullStar
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFive
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineStatements
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporCent

open CFSG.LocalAnalysis.RankThreeUC.AGL81C (oPPrimeHull)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12
  (oPrimeModPrimeComplement oPPrimeHull_top_eq_of_isSimpleGroup)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section14 (map_oPPrimeHull_top_of_surjective)

theorem oPPrimeHull_top_le_of_not_dvd_index {Y : Type*} [Group Y] [Finite Y] {d : ℕ}
    (hd : d.Prime) (M : Subgroup Y) [M.Normal] (hidx : ¬ d ∣ M.index) :
    oPPrimeHull d (⊤ : Subgroup Y) ≤ M := by
  rw [oPPrimeHull, Subgroup.closure_le]
  rintro x ⟨-, k, hk⟩
  have h1 : orderOf (QuotientGroup.mk' M x) ∣ d ^ k := hk ▸ orderOf_map_dvd _ x
  have h2 : orderOf (QuotientGroup.mk' M x) ∣ M.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (d ^ k) M.index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hd).2 hidx)
  have h3 : orderOf (QuotientGroup.mk' M x) = 1 :=
    Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h3)

theorem nonempty_oPrimeModPrimeComplement_mulEquiv {G : Type} [Group G] [Finite G] {d : ℕ}
    (hd : d.Prime) {Y : Subgroup G} (M : Subgroup ↥Y) [M.Normal] [IsSimpleGroup ↥M]
    (hdM : d ∣ Nat.card M) (hidx : ¬ d ∣ M.index) :
    Nonempty (oPrimeModPrimeComplement d Y ≃* ↥M) := by
  classical
  set N := CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (G := ↥Y) d with hN
  obtain ⟨hNn, hNd⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.primeComplementCore_properties ↥Y d hd
  have hhull : oPPrimeHull d (⊤ : Subgroup ↥Y) = M := by
    refine le_antisymm (oPPrimeHull_top_le_of_not_dvd_index hd M hidx) fun x hx => ?_
    have htop := oPPrimeHull_top_eq_of_isSimpleGroup (X := ↥M) hd hdM
    have hx' : (⟨x, hx⟩ : ↥M) ∈ oPPrimeHull d (⊤ : Subgroup ↥M) := by
      rw [htop]
      exact Subgroup.mem_top _
    have hle : (oPPrimeHull d (⊤ : Subgroup ↥M)).map M.subtype ≤
        oPPrimeHull d (⊤ : Subgroup ↥Y) := by
      rw [oPPrimeHull, MonoidHom.map_closure, oPPrimeHull]
      apply Subgroup.closure_mono
      rintro _ ⟨y, ⟨-, k, hk⟩, rfl⟩
      exact ⟨Subgroup.mem_top _, k, by rw [Subgroup.coe_subtype, Subgroup.orderOf_coe, hk]⟩
    exact hle (Subgroup.mem_map_of_mem M.subtype hx')
  have hNM : N.subgroupOf M = ⊥ := by
    have : (N.subgroupOf M).Normal := hNn.subgroupOf M
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf M) with h1 | h1
    · exact h1
    · exact absurd (hdM.trans (Subgroup.card_dvd_of_le (Subgroup.subgroupOf_eq_top.mp h1))) hNd
  set φ : ↥Y →* ↥Y ⧸ N := QuotientGroup.mk' N with hφ
  have hmap := map_oPPrimeHull_top_of_surjective hd φ (QuotientGroup.mk'_surjective N)
  rw [hhull] at hmap
  have hinj : Function.Injective (φ.comp M.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro m hm
    have hmN : (m : ↥Y) ∈ N := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hφ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hm
      exact hm
    have : m ∈ N.subgroupOf M := Subgroup.mem_subgroupOf.mpr hmN
    rwa [hNM] at this
  have hrange : (φ.comp M.subtype).range = M.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(MulEquiv.subgroupCongr (hmap.symm.trans hrange.symm)).trans
    (MonoidHom.ofInjective hinj).symm⟩

end CFSG.LocalAnalysis.AGL81I.Section3.SporCent
