module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.LocalAnalysis.OddStandard.AltStdBalDefs
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaC
import CFSG.LocalAnalysis.SeitzReduction.Inheritance
import CFSG.LocalAnalysis.EvenSmallLie.Setup

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup CFSG.Open

theorem standardComponentIsStandard_of_isCyclic_sylow {Y : Type*} [Group Y] [Finite Y] {t : Y}
    (ht : orderOf t = 2) {D : Subgroup Y} (hDt : D ≤ centralizer ({t} : Set Y))
    (hDn : (D.subgroupOf (centralizer ({t} : Set Y))).Normal)
    (hDq : CFSG.Open.IsQuasisimple D)
    (hKc : ∃ S : Sylow 2 (centralizer (D : Set Y)),
      IsCyclic (S : Subgroup (centralizer (D : Set Y)))) :
    standardComponentIsStandard D := by
  set K := centralizer (D : Set Y) with hK
  have htK : t ∈ K :=
    mem_centralizer_iff.2 fun x hx => mem_centralizer_singleton_iff.1 (hDt hx)
  have hCtN : centralizer ({t} : Set Y) ≤ normalizer (D : Set Y) :=
    le_normalizer_of_normal_subgroupOf hDt
  have hKN : K ≤ normalizer (D : Set Y) := centralizer_le_normalizer _
  have hNDK : normalizer (D : Set Y) ≤ normalizer (K : Set Y) := by
    intro h hh
    rw [mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => CFSG.EvenSmallLie.conj_mem_centralizer_of_mem_normalizer hh hx
    · intro hx
      have h1 := CFSG.EvenSmallLie.conj_mem_centralizer_of_mem_normalizer (inv_mem hh) hx
      rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at h1
  have hNKD : normalizer (K : Set Y) ≤ normalizer (D : Set Y) := by
    intro h hh
    have hu : h * t * h⁻¹ ∈ K := (mem_normalizer_iff.1 hh t).1 htK
    have hu2 : orderOf (h * t * h⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
    obtain ⟨k, hk, hkt⟩ := exists_conj_eq_of_isCyclic_sylow hKc htK ht hu hu2
    have hy : k⁻¹ * h ∈ centralizer ({t} : Set Y) := by
      rw [mem_centralizer_singleton_iff]
      calc k⁻¹ * h * t = k⁻¹ * (h * t * h⁻¹) * h := by group
        _ = k⁻¹ * (k * t * k⁻¹) * h := by rw [hkt]
        _ = t * (k⁻¹ * h) := by group
    rw [show h = k * (k⁻¹ * h) by group]
    exact mul_mem (hKN hk) (hCtN hy)
  refine ⟨hDq, ?_, ?_, le_antisymm hNKD hNDK, ?_⟩
  · have h2 : orderOf (⟨t, htK⟩ : K) = 2 := by rw [orderOf_mk, ht]
    exact even_iff_two_dvd.2 (h2 ▸ orderOf_dvd_natCard _)
  · intro h hh
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hodd)
    have hu2 : orderOf (u : Y) = 2 := by rw [orderOf_coe, hu]
    have huK : (u : Y) ∈ K := u.2.1
    obtain ⟨v, hvK, hvu⟩ := u.2.2
    have e : h * v * h⁻¹ = u := by simpa [MulAut.conj_apply] using hvu
    have hv2 : orderOf v = 2 := by
      rw [← hu2, ← e, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    obtain ⟨k, hk, hkt⟩ := exists_conj_eq_of_isCyclic_sylow hKc htK ht huK hu2
    obtain ⟨k', hk', hk't⟩ := exists_conj_eq_of_isCyclic_sylow hKc htK ht hvK hv2
    have hy : k⁻¹ * h * k' ∈ centralizer ({t} : Set Y) := by
      rw [mem_centralizer_singleton_iff]
      calc k⁻¹ * h * k' * t = k⁻¹ * (h * (k' * t * k'⁻¹) * h⁻¹) * (h * k') := by group
        _ = k⁻¹ * (u : Y) * (h * k') := by rw [hk't, e]
        _ = k⁻¹ * (k * t * k⁻¹) * (h * k') := by rw [hkt]
        _ = t * (k⁻¹ * h * k') := by group
    apply hh
    rw [show h = k * (k⁻¹ * h * k') * k'⁻¹ by group]
    exact mul_mem (mul_mem (le_normalizer hk) (hNDK (hCtN hy))) (inv_mem (le_normalizer hk'))
  · intro h hcomm
    have hle' : D.map (MulAut.conj h).toMonoidHom ≤ K := by
      rw [commutator_comm] at hcomm
      exact commutator_eq_bot_iff_le_centralizer.1 hcomm
    have hperf : ⁅D.map (MulAut.conj h).toMonoidHom, D.map (MulAut.conj h).toMonoidHom⁆ =
        D.map (MulAut.conj h).toMonoidHom := by
      rw [← map_commutator, isPerfect_iff.mp ⟨hDq.1⟩]
    have hbot := perfect_eq_bot_of_isCyclic_sylow hKc hle' hperf
    rw [map_eq_bot_iff_of_injective _ (MulAut.conj h).injective] at hbot
    exact CFSG.SeitzReduction.ne_bot_of_isQuasisimple hDq hbot

theorem standardComponentIsStandard_of_normal_cyclic {Y : Type*} [Group Y] [Finite Y] {z : Y}
    {H : Subgroup Y} (hz : orderOf z = 2) (hHq : CFSG.Open.IsQuasisimple H)
    (hHt : H ≤ centralizer ({z} : Set Y))
    (hHn : (H.subgroupOf (centralizer ({z} : Set Y))).Normal)
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U →
      U ≤ centralizer ({z} : Set Y) ⊓ centralizer (H : Set Y) → IsCyclic U) :
    standardComponentIsStandard H ∧ ∃ S : Sylow 2 (centralizer (H : Set Y)),
      IsCyclic (S : Subgroup (centralizer (H : Set Y))) := by
  have hzK : z ∈ centralizer (H : Set Y) :=
    CFSG.SeitzReduction.mem_centralizer_of_le_centralizer_singleton hHt
  have hall : ∀ S : Sylow 2 (centralizer (H : Set Y)),
      IsCyclic (S : Subgroup (centralizer (H : Set Y))) :=
    isCyclic_sylow_of_forall_le_inf_centralizer hzK hz
      (fun V hV hVle => hsyl V hV (le_inf (hVle.trans inf_le_right) (hVle.trans inf_le_left)))
  obtain ⟨S⟩ : Nonempty (Sylow 2 (centralizer (H : Set Y))) := inferInstance
  exact ⟨standardComponentIsStandard_of_isCyclic_sylow hz hHt hHn hHq ⟨S, hall S⟩, S, hall S⟩

theorem exists_stdHyp_of_component_cyclic {G : Type} [Group G] [Finite G]
    (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hbal : ∀ y : G, orderOf y = 2 → CFSG.oddCore (centralizer ({y} : Set G)) = ⊥)
    {x : G} (hx : orderOf x = 2) {K : Subgroup G} (hKq : CFSG.Open.IsQuasisimple K)
    (hKx : K ≤ centralizer ({x} : Set G))
    (hKn : (K.subgroupOf (centralizer ({x} : Set G))).Normal) (hKZ : IsPGroup 2 (center K))
    (hcyc : ∀ U : Subgroup G, IsPGroup 2 U →
      U ≤ centralizer ({x} : Set G) ⊓ centralizer (K : Set G) → IsCyclic U) :
    CFSG.EvenSporadicStandard.StdHyp G K := by
  obtain ⟨hstd, hcycS⟩ := standardComponentIsStandard_of_normal_cyclic hx hKq hKx hKn hcyc
  exact ⟨hG, hnab, hKP, hstd, fun t ht => hbal t ht, hcycS, hKZ⟩

theorem exists_stdHyp_of_component_cyclic_setting {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {n : ℕ} (h : CFSG.OddStandard.AltStdBal.Setting G L n) {x : G}
    (hx : orderOf x = 2) {K : Subgroup G} (hKq : CFSG.Open.IsQuasisimple K)
    (hKx : K ≤ centralizer ({x} : Set G))
    (hKn : (K.subgroupOf (centralizer ({x} : Set G))).Normal) (hKZ : IsPGroup 2 (center K))
    (hcyc : ∀ U : Subgroup G, IsPGroup 2 U →
      U ≤ centralizer ({x} : Set G) ⊓ centralizer (K : Set G) → IsCyclic U) :
    CFSG.EvenSporadicStandard.StdHyp G K :=
  exists_stdHyp_of_component_cyclic h.std.simple h.std.nonab h.std.kProper h.bal hx hKq hKx hKn hKZ
    hcyc

end CFSG.OddStandard.AltStdSec.SwapPartner
