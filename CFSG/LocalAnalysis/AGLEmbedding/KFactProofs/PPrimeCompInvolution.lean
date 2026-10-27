module

public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePPrime
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.PPrimeCompEven
public import CFSG.RankThree.PartOne.S11.PlaneData
import CFSG.RankThree.PartOne.KF.F128Act
public import CFSG.RankThree.PerfectCover.CentralQuotientPrimeSupport

public section

namespace CFSG.AGLEmbedding.KFactProofs.PPrimeComp

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.CatalogBridge (mem_zpowers_of_orderOf_eq_prime)
open CFSG.RankThree.PartOne (centerQuotientConj)

@[expose] def KFactPPrimeCompInvolutionU : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ Λ : Subgroup Y, CFSG.IsComponent Λ → IsCatalogGroup (↥Λ ⧸ Subgroup.center ↥Λ) →
    ¬ p ∣ (Subgroup.center Λ).index →
    ∀ u ∈ Subgroup.normalizer (Λ : Set Y), u ^ p = 1 → u ∉ Subgroup.centralizer (Λ : Set Y) →
      ∃ j ∈ Λ, j ≠ 1 ∧ j ^ 2 = 1 ∧ j * u = u * j

theorem mem_centralizer_of_conj_eq_one {Y : Type} [Group Y] {Λ : Subgroup Y}
    [Group.IsPerfect Λ] {g : Y} (hg : g ∈ Subgroup.normalizer (Λ : Set Y))
    (h : centerQuotientConj Λ ⟨g, hg⟩ = 1) : g ∈ Subgroup.centralizer (Λ : Set Y) := by
  have hAL : Subgroup.zpowers g ≤ Subgroup.normalizer (Λ : Set Y) := Subgroup.zpowers_le.mpr hg
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (CFSG.RankThree.PartOne.commute_of_centerQuotientAction_eq_one hAL
    ⟨g, Subgroup.mem_zpowers g⟩ h ⟨l, hl⟩).symm

theorem mem_zpowers_of_commute_pow_eq_one {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) (hcyc : ∀ P : Subgroup H, IsPGroup p P → IsCyclic P) {a b : H}
    (hab : a * b = b * a) (ha : a ^ p = 1) (hb : orderOf b = p) : a ∈ Subgroup.zpowers b := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases ha1 : a = 1
  · rw [ha1]; exact one_mem _
  have hao : orderOf a = p := orderOf_eq_prime ha ha1
  have hPa : IsPGroup p (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao, pow_one])
  have hPb : IsPGroup p (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  have hnorm : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set H) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_right (show Commute a b from hab) k)).symm.eq
  have hP := hPa.to_sup_of_normal_right' hPb hnorm
  have : IsCyclic ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) := hcyc _ hP
  have h1 := mem_zpowers_of_orderOf_eq_prime p hp
    (a := (⟨b, Subgroup.mem_sup_right (Subgroup.mem_zpowers b)⟩ :
      ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b)))
    (b := (⟨a, Subgroup.mem_sup_left (Subgroup.mem_zpowers a)⟩ :
      ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b)))
    (by rw [Subgroup.orderOf_mk, hb]) (by rw [Subgroup.orderOf_mk, hao])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩

theorem kFactU_of_even (hE : EvenFixedOrderP) : KFactPPrimeCompInvolutionU := by
  intro Y _ _ p hp hp2 Λ hΛ hcat hpZ u hu hup huc
  obtain ⟨⟨hperf, hsimp, hnab⟩, -⟩ := hΛ
  have : Group.IsPerfect Λ := hperf
  have : Fact p.Prime := ⟨hp⟩
  have hpS : ¬ p ∣ Nat.card (↥Λ ⧸ Subgroup.center ↥Λ) := hpZ
  have hpL : ¬ p ∣ Nat.card Λ :=
    CFSG.RankThree.PerfectCover.perfect_central_quotient_prime_support hp hpS
  have hpC : ¬ p ∣ Nat.card (Subgroup.center Λ) := fun h =>
    hpL (h.trans (Subgroup.card_subgroup_dvd_card _))
  set α := centerQuotientConj Λ ⟨u, hu⟩ with hα
  have hαp : α ^ p = 1 := CFSG.RankThree.PartOne.Sec66T.centerQuotientConj_pow hu hup
  have hα1 : α ≠ 1 := fun h1 => huc (mem_centralizer_of_conj_eq_one hu h1)
  have hαo : orderOf α = p := orderOf_eq_prime hαp hα1
  have h2 := hE _ hsimp hnab hcat p hp hp2 hpS α hαo
  obtain ⟨θ, hθ, -, -⟩ := CFSG.RankThree.PartOne.Sec66T.exists_fixed_hom hp hpC hu hup
  have hfix : signalizerFixedSubgroup α = CFSG.RankThree.PartOne.Sec66T.fixSub α :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hfix] at h2
  have h2' : 2 ∣ Nat.card (Λ ⊓ Subgroup.centralizer ({u} : Set Y) : Subgroup Y) :=
    h2.trans (Subgroup.card_dvd_of_surjective hθ)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2'
  refine ⟨x, x.2.1, fun h => ?_, ?_, ?_⟩
  · have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  · have h := pow_orderOf_eq_one x
    rw [hx] at h
    exact congrArg Subtype.val h
  · exact Subgroup.mem_centralizer_singleton_iff.mp x.2.2

theorem kFactExp_of_U (hU : KFactPPrimeCompInvolutionU) (hC : CatalogCyclicP) :
    KFactPPrimeCompInvolutionP := by
  intro Y _ _ p hp hp2 Λ hΛ hcat hpZ T₁ u hT hTp hu hup hTu huc
  obtain ⟨j, hjΛ, hj1, hj2, hju⟩ := hU Y p hp hp2 Λ hΛ hcat hpZ u hu hup huc
  refine ⟨j, hjΛ, hj1, hj2, hju, fun t ht => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨hperf, hsimp, hnab⟩, -⟩ := hΛ
  have : Group.IsPerfect Λ := hperf
  have hpS : ¬ p ∣ Nat.card (↥Λ ⧸ Subgroup.center ↥Λ) := hpZ
  have hcyc := hC _ hsimp hnab hcat p hp hp2 hpS
  set α := centerQuotientConj Λ ⟨u, hu⟩ with hα
  have hαp : α ^ p = 1 := CFSG.RankThree.PartOne.Sec66T.centerQuotientConj_pow hu hup
  have hα1 : α ≠ 1 := fun h1 => huc (mem_centralizer_of_conj_eq_one hu h1)
  have hαo : orderOf α = p := orderOf_eq_prime hαp hα1
  have htN := hT ht
  set β := centerQuotientConj Λ ⟨t, htN⟩ with hβ
  have hβp : β ^ p = 1 := by
    rw [hβ, ← map_pow]
    have hpow : (⟨t, htN⟩ : Subgroup.normalizer (Λ : Set Y)) ^ p =
        ⟨t ^ p, Subgroup.centralizer_le_normalizer _ (hTp t ht)⟩ := Subtype.ext (by simp)
    rw [hpow]
    exact CFSG.RankThree.PartOne.centerQuotientConj_of_centralizer (hTp t ht)
  have hβα : β * α = α * β := by
    rw [hβ, hα, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hTu t ht)
  obtain ⟨m, hm⟩ :=
    Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_commute_pow_eq_one hp hcyc hβα hβp hαo)
  have hwN : t * u ^ (-m) ∈ Subgroup.normalizer (Λ : Set Y) :=
    Subgroup.mul_mem _ htN (Subgroup.zpow_mem _ hu _)
  have hw : centerQuotientConj Λ ⟨t * u ^ (-m), hwN⟩ = 1 := by
    have e : (⟨t * u ^ (-m), hwN⟩ : Subgroup.normalizer (Λ : Set Y)) =
        ⟨t, htN⟩ * (⟨u, hu⟩ ^ m)⁻¹ := Subtype.ext (by simp [zpow_neg])
    rw [e, map_mul, map_inv, map_zpow, ← hα, ← hβ, ← hm, mul_inv_cancel]
  have hwC := mem_centralizer_of_conj_eq_one hwN hw
  have hjw : j * (t * u ^ (-m)) = (t * u ^ (-m)) * j :=
    Subgroup.mem_centralizer_iff.mp hwC j hjΛ
  have hjum : j * u ^ m = u ^ m * j := (Commute.zpow_right (show Commute j u from hju) m).eq
  calc j * t = j * ((t * u ^ (-m)) * u ^ m) := by group
    _ = (t * u ^ (-m)) * (j * u ^ m) := by rw [← mul_assoc, hjw, mul_assoc]
    _ = t * j := by rw [hjum]; group

section


theorem kFactPPrimeCompInvolutionP_holds : KFactPPrimeCompInvolutionP :=
  kFactExp_of_U (kFactU_of_even evenFixedOrderP) catalogCyclicP

end

end CFSG.AGLEmbedding.KFactProofs.PPrimeComp
