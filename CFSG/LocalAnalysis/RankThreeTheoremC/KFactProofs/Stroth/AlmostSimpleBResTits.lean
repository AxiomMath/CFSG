module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResLeaves
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem mem_inner_of_isPGroup_two_outer {L : Type*} [Group L] (h : IsPGroup 2 (Outer L)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {α : MulAut L} (hαp : α ^ p = 1) : α ∈ inner L := by
  obtain ⟨n, hn⟩ := h (QuotientGroup.mk α)
  have h1 : (QuotientGroup.mk α : Outer L) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hαp, QuotientGroup.mk_one]
  have hcop : Nat.Coprime (2 ^ n) p :=
    Nat.Coprime.pow_left n ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hord : orderOf (QuotientGroup.mk α : Outer L) = 1 :=
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hn) hcop).eq_one_of_dvd
      (orderOf_dvd_of_pow_eq_one h1)
  exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 hord)

theorem chevTwoOuterFixesPair_tits :
    ChevTwoOuterFixesPair LieIndexTits := by
  intro p hp hp2 L _ _ hrk ⟨d, hchar, hF, ⟨e⟩⟩ hne α hα hαp
  exfalso
  obtain ⟨d, hv⟩ := d
  cases d with
  | tits =>
    have hR : CFSG.Blueprint.ReeTitsModel L .Tits 2 1 :=
      CFSG.HardMathSupport.Cooperstein.Coordinator.reeTitsModel_tits_of_lie hv e
    have h2 : IsPGroup 2 (Outer L) :=
      (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier L 2 1 hR).1
    exact hα (mem_inner_of_isPGroup_two_outer h2 hp hp2 hαp)
  | A _ _ => exact absurd hF (by simp [LieIndexTits])
  | twistedA _ _ => exact absurd hF (by simp [LieIndexTits])
  | B _ _ => exact absurd hF (by simp [LieIndexTits])
  | C _ _ => exact absurd hF (by simp [LieIndexTits])
  | D _ _ => exact absurd hF (by simp [LieIndexTits])
  | twistedD _ _ => exact absurd hF (by simp [LieIndexTits])
  | E6 _ => exact absurd hF (by simp [LieIndexTits])
  | E7 _ => exact absurd hF (by simp [LieIndexTits])
  | E8 _ => exact absurd hF (by simp [LieIndexTits])
  | F4 _ => exact absurd hF (by simp [LieIndexTits])
  | G2 _ => exact absurd hF (by simp [LieIndexTits])
  | twistedE6 _ => exact absurd hF (by simp [LieIndexTits])
  | trialityD4 _ => exact absurd hF (by simp [LieIndexTits])
  | suzuki _ => exact absurd hF (by simp [LieIndexTits])
  | reeG2 _ => exact absurd hF (by simp [LieIndexTits])
  | reeF4 _ => exact absurd hF (by simp [LieIndexTits])

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
