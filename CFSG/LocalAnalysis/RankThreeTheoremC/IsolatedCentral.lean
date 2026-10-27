module

public import CFSG.LocalAnalysis.RankThreeTheoremC.FullCoreReduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.IsolatedPlanes
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionCentre

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.RankThree.PartOne.Planes Subgroup

variable {G : Type*} [Group G]

theorem exists_mem_inf_centralizer_of_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] {P E : Subgroup G}
    (hP : IsPGroup p P) (hPE : P ≤ normalizer (E : Set G)) (hSE : P ⊓ E ≠ ⊥) :
    ∃ y ∈ P ⊓ E, y ∈ centralizer (P : Set G) ∧ orderOf y = p := by
  classical
  have hPS : P ≤ normalizer ((P ⊓ E : Subgroup G) : Set G) :=
    le_trans (le_inf le_normalizer hPE) inf_normalizer_le_normalizer_inf
  have hn : ((P ⊓ E).subgroupOf P).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).2 hPS
  have hne : (P ⊓ E).subgroupOf P ≠ ⊥ := by
    intro h
    apply hSE
    have := congrArg (Subgroup.map P.subtype) h
    rwa [subgroupOf_map_subtype, inf_of_le_left inf_le_left, Subgroup.map_bot] at this
  have : Group.IsNilpotent P := hP.isNilpotent
  have hT : (P ⊓ E).subgroupOf P ⊓ center P ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hTp : IsPGroup p ((P ⊓ E).subgroupOf P ⊓ center P : Subgroup P) := hP.to_subgroup _
  have hTnt : Nontrivial ((P ⊓ E).subgroupOf P ⊓ center P : Subgroup P) :=
    (nontrivial_iff_ne_bot _).2 hT
  obtain ⟨n, hn0, hcard⟩ := hTp.nontrivial_iff_card.1 hTnt
  have hdvd : p ∣ Nat.card ((P ⊓ E).subgroupOf P ⊓ center P : Subgroup P) := by
    rw [hcard]
    exact dvd_pow_self p hn0.ne'
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := ((P ⊓ E).subgroupOf P ⊓ center P : Subgroup P)) p hdvd
  refine ⟨(((w : P)) : G), (mem_subgroupOf.1 w.2.1), ?_, ?_⟩
  · refine mem_centralizer_iff.2 fun g hg => ?_
    exact congrArg Subtype.val (mem_center_iff.1 w.2.2 ⟨g, hg⟩)
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hw

theorem central_mem_of_isolated_plane [Finite G] {p : ℕ} [Fact p.Prime] {P E D : Subgroup G}
    {z : G} (hP : IsPGroup p P) (hPE : P ≤ normalizer (E : Set G)) (hSE : P ⊓ E ≠ ⊥)
    (hiso : IsIsolatedPlane p P D) (hDn : ¬ P ≤ normalizer (D : Set G)) (hzD : z ∈ D)
    (hz1 : z ≠ 1) (hzc : z ∈ centralizer (P : Set G)) : z ∈ E := by
  have hp : p.Prime := Fact.out
  obtain ⟨y, hyS, hyc, hyord⟩ := exists_mem_inf_centralizer_of_ne_bot hP hPE hSE
  have hyp : y ^ p = 1 := by rw [← hyord]; exact pow_orderOf_eq_one y
  have hyD : y ∈ D := mem_of_isIsolatedPlane hp hiso hyS.1 hyc hyp
  have hzp : z ^ p = 1 := by
    have hexp := Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hiso.2.1.exponent_dvd_p ⟨z, hzD⟩
    simpa using congrArg Subtype.val hexp
  have hzord : orderOf z = p := orderOf_eq_prime hzp hz1
  by_cases hyz : y ∈ zpowers z
  ·
    have heq : zpowers y = zpowers z := by
      refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hyz) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hyord, hzord]
    exact (zpowers_le.2 hyS.2) (heq ▸ mem_zpowers z)
  ·
    exfalso
    apply hDn
    have hzP : z ∈ P := hiso.1 hzD
    have hcommzy : ∀ e ∈ zpowers z, e * y = y * e := fun e he =>
      mem_centralizer_iff.1 hyc e ((zpowers_le.2 hzP) he)
    have hcard2 := card_sup_zpowers hp (zpowers z) hyp hyz hcommzy
    have hcardz : Nat.card (zpowers z) = p := by rw [Nat.card_zpowers, hzord]
    have hle : zpowers z ⊔ zpowers y ≤ D := sup_le (zpowers_le.2 hzD) (zpowers_le.2 hyD)
    have heq : zpowers z ⊔ zpowers y = D := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [hcard2, hcardz, hiso.2.2.1, pow_two]
    have hDc : D ≤ centralizer (P : Set G) := by
      rw [← heq]
      exact sup_le (zpowers_le.2 hzc) (zpowers_le.2 hyc)
    exact (le_centralizer_iff.2 hDc).trans (centralizer_le_normalizer _)

section Extremal

variable {G : Type} [Group G] [Finite G]

theorem ExtremalObstruction.mem_of_inf_ne_bot_of_not_isMulCommutative {p : ℕ} {P : Sylow p G}
    {M D : Subgroup G} (hext : ExtremalObstruction p P M D) (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : ¬ IsMulCommutative D) {E : Subgroup G}
    (hPE : (P : Subgroup G) ≤ normalizer (E : Set G)) (hSE : (P : Subgroup G) ⊓ E ≠ ⊥) {z : G}
    (hzD : z ∈ D) (hzc : z ∈ centralizer ((P : Subgroup G) : Set G)) (hzp : z ^ p = 1) :
    z ∈ E := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hyS, hyc, hyord⟩ := exists_mem_inf_centralizer_of_ne_bot P.isPGroup' hPE hSE
  have hyp : y ^ p = 1 := by rw [← hyord]; exact pow_orderOf_eq_one y
  have hyZ := hext.mem_center_of_mem_centralizer_sylow hp hp2 hD hyS.1 hyc hyp
  have hzZ := hext.mem_center_of_mem_centralizer_sylow hp hp2 hD (hext.obstruction.2.1 hzD) hzc hzp
  have heq : zpowers y = (center D).map D.subtype := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hyZ) ?_
    rw [hext.card_center_eq hp hp2 hD, Nat.card_zpowers, hyord]
  have hzy : z ∈ zpowers y := by
    rw [heq]
    exact hzZ
  exact (zpowers_le.2 hyS.2) hzy

theorem ExtremalObstruction.mem_of_inf_ne_bot {p : ℕ} {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hp : p.Prime) (hp2 : p ≠ 2)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) {E : Subgroup G}
    (hPE : (P : Subgroup G) ≤ normalizer (E : Set G)) (hSE : (P : Subgroup G) ⊓ E ≠ ⊥) {z : G}
    (hzD : z ∈ D) (hz1 : z ≠ 1) (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hzp : z ^ p = 1) : z ∈ E := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hD : IsMulCommutative D
  · exact central_mem_of_isolated_plane P.isPGroup' hPE hSE
      (hext.isIsolatedPlane_of_isMulCommutative hp hD) hPD hzD hz1 hzc
  · exact hext.mem_of_inf_ne_bot_of_not_isMulCommutative hp hp2 hD hPE hSE hzD hzc hzp

end Extremal

end CFSG.LocalAnalysis.RankThreeTheoremC
