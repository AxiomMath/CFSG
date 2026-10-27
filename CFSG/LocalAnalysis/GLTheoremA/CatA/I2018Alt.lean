module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2018

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem i2018_alt_absurd {X K J : Subgroup G} {x : G}
    (hK : GLAPComponent 3 X K) (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hx3 : x ^ 3 = 1)
    (hJ : GLAPComponent 3 (K ⊓ cx x) J) (hU : catalogIs (PSimple 3 J) CFSG.LocalAnalysis.GLTheoremA.S9.isU3eight)
    (hNA : I2018U38NotAlt) {n : ℕ} (hn : 5 ≤ n) (eS : PSimple 3 K ≃* alternatingGroup (Fin n)) : False := by
  obtain ⟨hsimple, hna⟩ := chev_pSimple_simple_nonabelian Nat.prime_three hK
  haveI := hsimple
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hx3
  have hα3 : (chevAut 3 K ⟨x, hxN⟩) ^ 3 = 1 := chevAut_pow_eq_one 3 K hxN hx3
  have hJ' := glaPComponent_chevTransfer Nat.prime_three hxN hxp hJ
  obtain ⟨eJ⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three hxN hxp hJ
  by_cases hα1 : chevAut 3 K ⟨x, hxN⟩ = 1
  · rw [hα1, fixSubgroup_one_eq_top] at hJ'
    obtain ⟨eT⟩ := chevQ_pSimple_top_equiv Nat.prime_three hna hJ'
    exact hNA (PSimple 3 J) hU n hn ⟨eJ.trans (eT.trans eS)⟩
  · have hβ : (MulAut.congr eS) (chevAut 3 K ⟨x, hxN⟩) ^ 3 = 1 := by
      rw [← map_pow, hα3, map_one]
    have hβ1 : (MulAut.congr eS) (chevAut 3 K ⟨x, hxN⟩) ≠ 1 := fun h =>
      hα1 ((MulAut.congr eS).injective (h.trans (map_one _).symm))
    obtain ⟨hLe, ⟨eLe⟩⟩ := chevQ_transport Nat.prime_three eS hJ'
    obtain ⟨m, hm, -, ⟨f⟩⟩ := kdAltDown_holds n 3 hn Nat.prime_three (by norm_num) _ hβ hβ1 _ hLe
    have hm5 : 5 ≤ m := (le_max_left 5 3).trans hm
    exact hNA (PSimple 3 J) hU m hm5 ⟨eJ.trans (eLe.trans f)⟩

end CFSG.LocalAnalysis.GLTheoremA.I2018

end
