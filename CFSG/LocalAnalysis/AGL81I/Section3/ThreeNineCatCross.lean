module

public import CFSG.LieType.OutStructureSeitzComponent
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineStatements

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open TauCeti
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaOver)

private theorem one_le_pRank_zpowers {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {x : X} (hxp : x ^ p = 1) (hx1 : x ≠ 1) : 1 ≤ CFSG.Open.pRank p (Subgroup.zpowers x) := by
  have : Fact p.Prime := ⟨hp⟩
  have hEA : CFSG.Open.IsElemAbelian p (Subgroup.zpowers x) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨m, hm⟩ := a.2
      obtain ⟨n, hn⟩ := b.2
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hm, ← hn, ← zpow_add,
        ← zpow_add, add_comm])
    · obtain ⟨n, rfl⟩ := ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hcard : Nat.card (Subgroup.zpowers x) = p ^ 1 := by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hxp hx1
  exact CFSG.SectionRank.le_pRank hp.one_lt le_rfl hEA hcard

theorem mem_gammaOver_of_commute {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {R T : Subgroup X} {x c : X} (hxR : x ∈ R) (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hcT : c ∈ T)
    (hxc : x * c = c * x) : c ∈ gammaOver 1 p R T := by
  have hcC : c ∈ Subgroup.centralizer (Subgroup.zpowers x : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    exact (Commute.zpow_left (show Commute x c from hxc) n).eq
  have hcN : c ∈ Subgroup.normalizer (Subgroup.zpowers x : Set X) :=
    Subgroup.centralizer_le_normalizer _ hcC
  exact (le_iSup₂_of_le (Subgroup.zpowers x) ((Subgroup.zpowers_le).mpr hxR)
    (le_iSup_of_le (one_le_pRank_zpowers hp hxp hx1) le_rfl) :
      Subgroup.normalizer (Subgroup.zpowers x : Set X) ⊓ T ≤ gammaOver 1 p R T) ⟨hcN, hcT⟩

theorem le_gammaOver_of_seitz (hS : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) {X : Type}
    [Group X] [Finite X] {K E : Subgroup X} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hKn : K.Normal) {d : ValidLieTypeIndex} (hpd : p ≠ d.1.characteristic)
    (hexc : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1)
    (φ : ↥K ≃* (CFSGIndex.lie d).Group) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) :
    K ≤ gammaOver 1 p E K := by
  by_cases hc : ∃ x ∈ E, x ≠ 1 ∧ ∀ c ∈ K, x * c = c * x
  · obtain ⟨x, hxE, hx1, hxc⟩ := hc
    exact fun c hcK => mem_gammaOver_of_commute hp hxE hx1 (hE.2 x hxE) hcK (hxc c hcK)
  · push Not at hc
    have hEN : E ≤ Subgroup.normalizer (K : Set X) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hKn]
      exact le_top
    refine (CFSG.LieType.OutStructure.le_closure_fixed_of_seitz hS hp hp2 hpd hexc φ hE hEc hEN
      hc).trans ((Subgroup.closure_le _).mpr ?_)
    rintro c ⟨hcK, x, hxE, hx1, hxc⟩
    exact mem_gammaOver_of_commute hp hxE hx1 (hE.2 x hxE) hcK hxc

end CFSG.LocalAnalysis.AGL81I.Section3
