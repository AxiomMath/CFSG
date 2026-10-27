module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29CrossRankOnly

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace ExcRank

open CFSG.Open Subgroup

theorem crossRankAtPrime_of_model {d : TauCeti.ValidLieTypeIndex} {p : ℕ}
    (h : p.Prime → 5 ≤ p → d.1.characteristic ≠ p →
      ∃ (G : Type) (_ : Group G) (_ : Finite G),
        Nonempty ((TauCeti.CFSGIndex.lie d).Group ≃* G) ∧
          ∀ y : G, y ^ p = 1 → 3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set G))) :
    CrossRankAtPrime d p := by
  intro hp hp5 hdp L _ _ _ ⟨e⟩ _ _ y hy
  obtain ⟨G, _, _, ⟨φ⟩, hr⟩ := h hp hp5 hdp
  set ψ := e.trans φ with hψ
  have hyp : ψ y ^ p = 1 := by rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
  have h1 := hr (ψ y) hyp
  have h2 := CFSG.SectionRank.pRank_le_map hp.one_lt ψ.symm.toMonoidHom ψ.symm.injective
    (centralizer ({ψ y} : Set G))
  have h3 : (centralizer ({ψ y} : Set G)).map ψ.symm.toMonoidHom ≤
      centralizer ({y} : Set L) := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' := Subgroup.mem_centralizer_singleton_iff.1 hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg ψ.symm hc'
    simp only [map_mul, MulEquiv.symm_apply_apply] at this
    simpa only [MulEquiv.coe_toMonoidHom] using this
  have h4 := CFSG.SectionRank.pRank_mono hp.one_lt h3
  omega

end ExcRank

end CFSG.LocalAnalysis.RankFourTheoremC
