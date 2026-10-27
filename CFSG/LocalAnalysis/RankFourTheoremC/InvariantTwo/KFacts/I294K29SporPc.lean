module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular
public import Certificates.Data.CFSGNative.Timmesfeld.PcFus
public import Certificates.Data.CFSGNative.Timmesfeld.PcE3
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29Spor

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup
open _root_.Timmesfeld.PcReg _root_.Timmesfeld.PcFus _root_.Timmesfeld.PcE3 CFSG.HardMathSupport.Foote.E27 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow

section Power

variable {G : Type*} [Group G]

theorem pow_pow_eq_self_of_mod {p : ℕ} {x : G} (hx : x ^ p = 1) {k k' : ℕ}
    (h : k * k' % p = 1) : (x ^ k) ^ k' = x := by
  rw [← pow_mul, ← Nat.div_add_mod (k * k') p, h, pow_add, pow_mul, hx, one_pow, one_mul,
    pow_one]

theorem RankThreeWitness.pow {p : ℕ} (hp : p.Prime) {x : G} (hx : x ^ p = 1) {k : ℕ}
    (hk : Nat.Coprime k p) (h : RankThreeWitness p x) : RankThreeWitness p (x ^ k) := by
  obtain ⟨k', -, hk'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk hp.one_lt
  rcases h with ⟨P, hP⟩ | ⟨Q, Z, hexp, hZQ, hZc, hZ, hcomm, hcard, hxQ, hxZ⟩ |
    ⟨E, hE, hcard, hxE⟩
  · refine Or.inl ⟨P, fun g hg => ?_⟩
    have hz : Commute g x := Subgroup.mem_centralizer_singleton_iff.1 (hP hg)
    exact Subgroup.mem_centralizer_singleton_iff.2 (hz.pow_right k).eq
  · refine Or.inr (Or.inl ⟨Q, Z, hexp, hZQ, hZc, hZ, hcomm, hcard, Q.pow_mem hxQ k, ?_⟩)
    intro hZk
    exact hxZ (pow_pow_eq_self_of_mod hx hk' ▸ Z.pow_mem hZk k')
  · exact Or.inr (Or.inr ⟨E, hE, hcard, E.pow_mem hxE k⟩)

end Power

end CFSG.LocalAnalysis.RankFourTheoremC
