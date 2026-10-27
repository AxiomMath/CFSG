module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalSymplecticAut
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour

theorem centralizes_of_symplectic {G : Type} [Group G] [Finite G] {H S U L : Subgroup G}
    (h : StrongClosureComponent H S U L) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSp 2 K)) {w : G}
    (hwU : w ∈ U) (hwS : w ∈ Subgroup.centralizer (S : Set G)) :
    L ≤ Subgroup.centralizer ({w} : Set G) := by
  let ψ : StatedProj (StatedSp 2 K) ≃* StatedSp 2 K :=
    (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_eq_bot 2)).trans
      QuotientGroup.quotientBot
  exact centralizes_of_family h
    (NoStronglyClosedElemAbelian.of_mulEquiv (e.trans ψ) (noStronglyClosed_statedSp hK))
    (SylowCentralizingAutInner.of_mulEquiv e sylowCentralizingAutInner_statedProj) hwU hwS

theorem centralizes_of_statedClassicalModel_psp {G : Type} [Group G] [Finite G]
    {H S U L : Subgroup G} (h : StrongClosureComponent H S U L) {f : ℕ} (hf : 2 ≤ f)
    (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 2 2 f) {w : G} (hwU : w ∈ U)
    (hwS : w ∈ Subgroup.centralizer (S : Set G)) : L ≤ Subgroup.centralizer ({w} : Set G) := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := hmodel
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  have hK : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact centralizes_of_symplectic h hK e hwU hwS

end CFSG.QuasithinUnique.K1
