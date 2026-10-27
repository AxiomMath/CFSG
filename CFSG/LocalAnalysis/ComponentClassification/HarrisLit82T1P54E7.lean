module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54E7Iso

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54

open CFSG Subgroup Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts

theorem rowE7 : RowE7 := by
  intro Y _ _ hY hZ p hp hp2 τ n f hτ hL hq _ _ t ht2 htZ
  obtain rfl : τ = .E7 := hτ
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := E7Row.nonempty_mulEquiv_E7sc hY hZ hp2 hL hq ht2 htZ
  have : Finite (E7sc p f) := Finite.of_equiv Y e.symm.toEquiv
  have hc : e.symm t ∈ center (E7sc p f) := Subgroup.mem_center_iff.2 fun g => e.injective (by
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.1 htZ (e g))
  have h2 : orderOf (e.symm t) = 2 := by rw [MulEquiv.orderOf_eq, ht2]
  have hk : ¬ 2 ∣ Nat.card e.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective, Subgroup.card_bot]
    norm_num
  simpa using Concl.map (φ := e.toMonoidHom) e.surjective hk (E7Row.concl_E7sc hp2 hq hc h2)

end CFSG.ComponentClassification.HarrisLit.T1.P54
