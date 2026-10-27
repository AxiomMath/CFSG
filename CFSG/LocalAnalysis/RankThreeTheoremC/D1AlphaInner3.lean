module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaThree3
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ComponentSL3
import CFSG.LocalAnalysis.RankThreeTheoremC.OuterAlpha
import CFSG.LocalAnalysis.RankThreeTheoremC.OuterAlphaInner
import CFSG.LocalAnalysis.RankThreeTheoremC.OutTwoExponentThree
import CFSG.LocalAnalysis.RankThreeTheoremC.OuterExtraspecial

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.Assembly.LowTwoRank
open CFSG.AGLEmbedding (isPGroup_center_of_isComponentOf
  prime_dvd_card_center_quotient_of_isComponentOf centerQuotientAction)

variable {G : Type} [Group G] [Finite G]

theorem D1ComponentAlphaData3.isCyclic_inf_centralizer {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {K : Subgroup (ReducedCentralizer p z)}
    (h : D1ComponentAlphaData3 p P M H R z Pbar zbar K) :
    IsCyclic ((Pbar : Subgroup (ReducedCentralizer p z)) ⊓
      Subgroup.centralizer (K : Set (ReducedCentralizer p z)) : Subgroup _) := by
  have hp : p.Prime := Fact.out
  by_contra hnc
  obtain ⟨F, hF, hFel, hFcard⟩ := CFSG.AGLEmbedding.exists_isElemAbelian_card_sq_of_two_le_pRank hp
    (CFSG.AGLEmbedding.two_le_pRank_of_isPGroup_not_isCyclic hp h.data.red.ne_two
      (Pbar.isPGroup'.to_le inf_le_left) hnc)
  have hFz : F ≤ Subgroup.zpowers zbar := by
    intro f hf
    by_cases hf1 : f = 1
    · rw [hf1]
      exact Subgroup.one_mem _
    · exact h.omega f (hF hf) (orderOf_eq_prime (hFel.2 f hf) hf1)
  have hcard := Subgroup.card_le_of_le hFz
  rw [Nat.card_zpowers, h.data.zbar_order, hFcard] at hcard
  have h1 := hp.one_lt
  nlinarith

theorem D1ComponentAlphaData3.commute_inf_centralizer {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {K : Subgroup (ReducedCentralizer p z)}
    (h : D1ComponentAlphaData3 p P M H R z Pbar zbar K) :
    ∀ c₁ ∈ (Pbar : Subgroup (ReducedCentralizer p z)) ⊓
        Subgroup.centralizer (K : Set (ReducedCentralizer p z)),
      ∀ c₂ ∈ (Pbar : Subgroup (ReducedCentralizer p z)) ⊓
        Subgroup.centralizer (K : Set (ReducedCentralizer p z)), c₁ * c₂ = c₂ * c₁ := by
  intro c₁ hc₁ c₂ hc₂
  have := h.isCyclic_inf_centralizer
  let _ : CommGroup ((Pbar : Subgroup (ReducedCentralizer p z)) ⊓
    Subgroup.centralizer (K : Set (ReducedCentralizer p z)) : Subgroup _) := IsCyclic.commGroup
  exact congrArg Subtype.val (mul_comm (⟨c₁, hc₁⟩ : ↥((Pbar : Subgroup (ReducedCentralizer p z)) ⊓
    Subgroup.centralizer (K : Set (ReducedCentralizer p z)))) ⟨c₂, hc₂⟩)

theorem D1ComponentAlphaData3.inf_sup_le_or_le_sup {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {K : Subgroup (ReducedCentralizer p z)}
    (h : D1ComponentAlphaData3 p P M H R z Pbar zbar K)
    {E L : Subgroup (ReducedCentralizer p z)}
    (hEZ : (Subgroup.center E).map E.subtype = Subgroup.zpowers zbar)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p))
    (hSL : StatedSL 2 (ZMod p) ≤
      (L.subgroupOf (Subgroup.normalizer (E : Set (ReducedCentralizer p z)))).map
        (centerQuotientAction E e)) :
    E ⊓ (K ⊔ Subgroup.centralizer (K : Set (ReducedCentralizer p z))) ≤
        (Subgroup.center E).map E.subtype ∨
      E ≤ K ⊔ Subgroup.centralizer (K : Set (ReducedCentralizer p z)) := by
  have : K.Normal := h.data.normal
  rcases inf_le_map_center_or_le_sup_of_normal
    (Y := K ⊔ Subgroup.centralizer (K : Set (ReducedCentralizer p z))) e hSL with h1 | h1
  · exact Or.inl h1
  · refine Or.inr (h1.trans (sup_le le_rfl ?_))
    rw [hEZ]
    exact (Subgroup.zpowers_le.mpr h.mem).trans le_sup_left

theorem D1ComponentAlphaData3.three_le_pRank_of_inf_sup_le {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {M H R : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {K : Subgroup (ReducedCentralizer p z)}
    (h : D1ComponentAlphaData3 p P M H R z Pbar zbar K)
    {E : Subgroup (ReducedCentralizer p z)}
    (hER : E ≤ (Pbar : Subgroup (ReducedCentralizer p z))) (hEcard : Nat.card E = p ^ 3)
    (hEexp : ∀ x ∈ E, x ^ p = 1)
    (hEZ : (Subgroup.center E).map E.subtype = Subgroup.zpowers zbar)
    (hEY : E ⊓ (K ⊔ Subgroup.centralizer (K : Set (ReducedCentralizer p z))) ≤
      (Subgroup.center E).map E.subtype)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)) :
    3 ≤ Open.pRank p (⊤ : Subgroup (MulAut K)) := by
  have : K.Normal := h.data.normal
  have hp : p.Prime := Fact.out
  exact three_le_pRank_mulAut_of_inf_sup_le Pbar
    (isPGroup_center_of_isComponentOf hp h.data.red.core_eq_bot h.data.comp)
    (prime_dvd_card_center_quotient_of_isComponentOf hp h.data.red.core_eq_bot h.data.comp)
    h.data.zbar_mem_center h.omega hER hEcard hEexp hEZ hEY e

theorem exists_pElement_transvection_three {Y : Type*} [Group Y] [Finite Y] {E L : Subgroup Y}
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod 3))
    (hSL : StatedSL 2 (ZMod 3) ≤
      (L.subgroupOf (Subgroup.normalizer (E : Set Y))).map (centerQuotientAction E e)) :
    ∃ (u : Y) (hu : u ∈ Subgroup.normalizer (E : Set Y)), (∃ n : ℕ, u ^ (3 ^ n) = 1) ∧
      centerQuotientAction E e ⟨u, hu⟩ ≠ 1 := by
  obtain ⟨A, hA, hA1, hA3⟩ := exists_statedSL_orderOf_three
  obtain ⟨g, -, hgA⟩ := Subgroup.mem_map.mp (hSL hA)
  obtain ⟨m, a, hm, hu⟩ := exists_pow_not_dvd_isPElement 3 g
  refine ⟨((g ^ m : Subgroup.normalizer (E : Set Y)) : Y), (g ^ m).2, ⟨a, ?_⟩, ?_⟩
  · simpa using congrArg Subtype.val hu
  · show centerQuotientAction E e (g ^ m) ≠ 1
    rw [map_pow, hgA]
    exact pow_ne_one_of_not_dvd hA3 hA1 hm

@[expose] def D1ComponentAlphaSmallInner3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G) (z : G)
    (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z)
    (K : Subgroup (ReducedCentralizer p z)), p = 3 →
    D1ComponentAlphaData3 p P M H R z Pbar zbar K →
    zbar ∈ ⁅(Pbar : Subgroup (ReducedCentralizer p z)) ⊓ K,
      (Pbar : Subgroup (ReducedCentralizer p z)) ⊓ K⁆ →
    (∃ B : Subgroup (MulAut K), IsPGroup p B ∧ ¬ IsMulCommutative B) →
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → False

theorem d1ComponentAlphaSmallCaseThree3_of_inner (h : D1ComponentAlphaSmallInner3 G) :
    D1ComponentAlphaSmallCaseThree3 G := by
  intro p _ P M H R z Pbar zbar K hp3 hd hAut
  have : K.Normal := hd.data.normal
  obtain ⟨E, L, hER, hEcard, hEexp, hEZ, e, hSL⟩ := hd.data.exists_extraspecial
  rcases hd.inf_sup_le_or_le_sup hEZ e hSL with hE0 | hEY
  · have := hd.three_le_pRank_of_inf_sup_le hER hEcard hEexp hEZ hE0 e
    omega
  · refine h p P M H R z Pbar zbar K hp3 hd (mem_commutator_inf_of_le_sup Pbar
      hd.commute_inf_centralizer hd.data.zbar_order hER hEZ hEY e) ?_ hAut
    subst hp3
    obtain ⟨u, hu, ⟨n, hun⟩, hψ⟩ := exists_pElement_transvection_three e hSL
    exact exists_nonabelian_isPGroup_mulAut hEexp (inf_centralizer_eq_center_map_of_omega hER
      hEexp hEZ hd.data.zbar_mem_center hd.omega) e hu hun hψ

end CFSG.LocalAnalysis.RankThreeTheoremC
