module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSuzFaithful
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSuzArith
public import CFSG.RankThree.PartOne.SEITZ2.SzOuter
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut szFieldAut_injective)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Suzuki

variable {a : ℕ} {F : Type} [Field F]
  [Finite F]

theorem suzuki_no_inner_plane (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup (MulAut (suzukiGroup a F))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2) (hin : E ≤ innerAut (suzukiGroup a F)) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (suzukiGroup a F) := inferInstance
  have hinj : Function.Injective (MulAut.conj : suzukiGroup a F →* MulAut (suzukiGroup a F)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hF)
  have e' : suzukiGroup a F ≃* GLASzGroup a F :=
    MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F)
  have hsyl := CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic
    a ha hF e'
  have hE₀ := CFSG.LieType.SeitzGeneration.isElemAbelian_comap_conj hinj hE
  have hin' : E ≤ (MulAut.conj : suzukiGroup a F →* MulAut (suzukiGroup a F)).range := hin
  have hcard₀ : Nat.card (E.comap (MulAut.conj : suzukiGroup a F →* _)) = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hin', hc]
  have hodd : Odd (Nat.card (E.comap (MulAut.conj : suzukiGroup a F →* _))) := by
    rw [hcard₀]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hcyc := CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.odd_commutative_subgroup_cyclic
    _ hodd hE₀.1 hsyl
  have := CFSG.LieType.SeitzGeneration.isElementaryAbelian_of_isElemAbelian hE₀
  exact CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hcard₀ hcyc

theorem suzuki_prime_faithful (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 < p) {σ : RingAut F} (hσ : orderOf σ = p) {b : ℕ} {k : Type}
    [Field k] [Finite k] (hbp : (2 * b + 1) * p = 2 * a + 1) (hkc : Nat.card k = 2 ^ (2 * b + 1))
    (eH : ↥((szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _)) ≃* suzukiGroup b k)
    (hdvd : p ∣ Nat.card ↥((szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _)))
    (g : MulAut (suzukiGroup a F)) (hgr : (orderOf g).Prime) (hgp : orderOf g ≠ p)
    (hcomm : g * szFieldAut a F σ = szFieldAut a F σ * g)
    (hfix : ∀ u ∈ (szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _), g u = u) : False := by
  have hinj : Function.Injective (MulAut.conj : suzukiGroup a F →* MulAut (suzukiGroup a F)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hF)
  have hp2 : p ≠ 2 := by omega
  set δ := szFieldAut a F σ with hδ
  by_cases hin : ∃ c : suzukiGroup a F, MulAut.conj c = g
  · obtain ⟨c, hc⟩ := hin
    have h1 : δ * MulAut.conj c = MulAut.conj c * δ := by rw [hc]; exact hcomm.symm
    have hcδ : δ c = c := (CFSG.HardMathSupport.Timmesfeld.CrossChar.mem_fixSub_of_commute hinj h1)
    have hcz : c = 1 := by
      refine CFSG.RankThree.PartOne.SEITZ2.eq_one_of_central_fixed_szFieldAut hp hp5.le hF
        (fun h => by omega) hσ ?_ (x := c) ?_ ?_
      · rw [CFSG.RankThree.PartOne.SEITZ2.fixedSubgroup_eq_eqLocus]
        exact hdvd
      · rw [CFSG.RankThree.PartOne.SEITZ2.fixedSubgroup_eq_eqLocus]
        exact hcδ
      · intro y hy
        rw [CFSG.RankThree.PartOne.SEITZ2.fixedSubgroup_eq_eqLocus] at hy
        have := hfix y hy
        rw [← hc] at this
        simp only [MulAut.conj_apply] at this
        calc c * y = (c * y * c⁻¹) * c := by group
          _ = y * c := by rw [this]
    rw [hcz, map_one] at hc
    rw [← hc] at hgr
    simp at hgr
    exact Nat.not_prime_one hgr
  ·
    set r := orderOf g with hr
    have hgord : orderOf g = r := rfl
    have hr2 : r ≠ 2 := by
      intro h2
      have hg2 : g ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one g
      have hout := (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hF).2
      have hbar1 : (QuotientGroup.mk g : Outer (suzukiGroup a F)) ≠ 1 := by
        intro h
        rw [QuotientGroup.eq_one_iff] at h
        exact hin h
      have hbar2 : (QuotientGroup.mk g : Outer (suzukiGroup a F)) ^ 2 = 1 := by
        rw [← QuotientGroup.mk_pow, hg2]; rfl
      have hord2 : orderOf (QuotientGroup.mk g : Outer (suzukiGroup a F)) = 2 :=
        orderOf_eq_prime hbar2 hbar1
      have : 2 ∣ Nat.card (Outer (suzukiGroup a F)) := hord2 ▸ orderOf_dvd_natCard _
      have := this.trans hout
      omega
    obtain ⟨σ', h', c', k', _, _, hσ', hcr, hkc', hconj', ⟨eH'⟩⟩ :=
      CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha F hF r hgr hr2 g hgord
        (fun ⟨y, hy⟩ => hin ⟨y, hy⟩)
    set m := 2 * b + 1 with hm
    set s := 2 * c' + 1 with hs
    have hJ1 : Nat.card ↥((szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _)) =
        (2 ^ m) ^ 2 * (2 ^ m - 1) * ((2 ^ m) ^ 2 + 1) := by
      rw [Nat.card_congr eH.toEquiv]
      exact CFSG.LieType.Ree.suzuki_order hkc
    have hJle : (szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _) ≤
        CFSG.HardMathSupport.Timmesfeld.CrossChar.fixSub g := fun u hu => hfix u hu
    have hdvd1 := Subgroup.card_dvd_of_le hJle
    have hfs : CFSG.HardMathSupport.Timmesfeld.CrossChar.fixSub (szFieldAut a F σ') =
        (szFieldAut a F σ').toMonoidHom.eqLocus (MonoidHom.id _) := by
      ext z; rfl
    have hC : Nat.card (CFSG.HardMathSupport.Timmesfeld.CrossChar.fixSub g) =
        (2 ^ s) ^ 2 * (2 ^ s - 1) * ((2 ^ s) ^ 2 + 1) := by
      rw [← card_fixSub_conj (MulAut.conj h') g, hconj', hfs, Nat.card_congr eH'.toEquiv]
      exact CFSG.LieType.Ree.suzuki_order hkc'
    rw [hJ1, hC] at hdvd1
    have hA : 2 ^ m - 1 ∣ (2 ^ s) ^ 2 * (2 ^ s - 1) * ((2 ^ s) ^ 2 + 1) :=
      (dvd_mul_of_dvd_left (dvd_mul_left (2 ^ m - 1) _) _).trans hdvd1
    have hnd : ¬ m ∣ s := by
      rintro ⟨t, ht⟩
      have h1 : m * p = m * (t * r) := by
        calc m * p = 2 * a + 1 := hbp
          _ = s * r := hcr.symm
          _ = m * (t * r) := by rw [ht, mul_assoc]
      have hm0 : 0 < m := by omega
      have h2 : p = t * r := Nat.eq_of_mul_eq_mul_left hm0 h1
      have h3 : r ∣ p := ⟨t, by rw [h2, mul_comm]⟩
      exact hgp ((Nat.prime_dvd_prime_iff_eq hgr hp).1 h3)
    refine not_dvd_suzuki_order (m := m) (s := s) ⟨b, rfl⟩ hnd ?_
    have : (2 ^ s) ^ 2 * (2 ^ s - 1) * ((2 ^ s) ^ 2 + 1) =
        (2 ^ s) ^ 2 * ((2 ^ s) ^ 2 + 1) * (2 ^ s - 1) := by ring
    rwa [this] at hA

end Suzuki

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
