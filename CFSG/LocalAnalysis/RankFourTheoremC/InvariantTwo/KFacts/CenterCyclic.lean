module

public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIICenter
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCentralPoint

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.GH74.Generic (card_ker_dvd_hopfMultiplier centralQuotientMap centralQuotientMap_ker
  centralQuotientMap_surjective)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (exceptionalOrders_le exists_lieModel
  genericOrders_snd_le)
open CFSG.RankThree.PartTwo.Sec4.Census (SporadicMultipliers)
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator (not_dvd_sporadicMultiplierOrder
  sporadicMultipliers_holds)

theorem not_dvd_multiplierOrders_of_five_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n q f : ℕ) :
    ¬ p ∣ (genericOrders t n q f).2 *
      ((exceptionalOrders t n q f).1 * (exceptionalOrders t n q f).2) := by
  have hb := genericOrders_snd_le t n q f
  have hex := exceptionalOrders_le t n q f
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact absurd (Nat.le_of_dvd hb.1 h) (by omega)
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact absurd (Nat.le_of_dvd hex.1.1 h) (by omega)
    · exact absurd (Nat.le_of_dvd hex.2.1 h) (by omega)

@[expose] def KFactCenterCyclicGeFive : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsCatalogGroup (K ⧸ Subgroup.center K) →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ P : Subgroup K, P ≤ Subgroup.center K → IsPGroup p P →
      IsCyclic P

theorem kFactCenterCyclicGeFive_of_tables
    (hGA : CFSG.Open.GriessAllModelsStatement) (hSp : SporadicMultipliers) :
    KFactCenterCyclicGeFive := by
  intro K _ _ hq hcat p hp hp5 P hPZ hP
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hperf : Group.IsPerfect K := ⟨hq.1⟩
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic q hq' =>
    exfalso
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
    have hc : ∀ x y : (TauCeti.CFSGIndex.cyclic q hq').Group, x * y = y * x :=
      fun x y => mul_comm x y
    exact hab (e.injective (by rw [map_mul, map_mul]; exact hc _ _))
  | alternating m hm =>
    exact CFSG.AGLEmbedding.isCyclic_of_le_center_of_alternating hm e hp (by omega) hPZ hP
  | lie d =>
    obtain ⟨t, n, q, f, hmodel⟩ := exists_lieModel d
    exact CFSG.AGLEmbedding.isCyclic_of_le_center_of_lieModel hGA e hmodel hp
      (not_dvd_multiplierOrders_of_five_le hp hp5 t n q f) hPZ hP
  | sporadic s =>
    have hdvd := card_ker_dvd_hopfMultiplier hperf (centralQuotientMap e)
      (centralQuotientMap_surjective e) (centralQuotientMap_ker e).le
    rw [centralQuotientMap_ker e, hSp.1 s] at hdvd
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rcases k.eq_zero_or_pos with rfl | hk0
    · rw [pow_zero] at hk
      have : Subsingleton P := (Nat.card_eq_one_iff_unique.1 hk).1
      exact isCyclic_of_subsingleton
    · refine absurd ?_ (not_dvd_sporadicMultiplierOrder hp hp5 s)
      exact (hk ▸ dvd_pow_self p hk0.ne').trans ((card_dvd_of_le hPZ).trans hdvd)

section Algebra

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem zpowers_eq_of_isCyclic_sup {c d : G} (hcyc : IsCyclic ↥(zpowers c ⊔ zpowers d))
    (hord : orderOf c = orderOf d) : zpowers c = zpowers d := by
  set Q : Subgroup G := zpowers c ⊔ zpowers d with hQ
  have hcQ : zpowers c ≤ Q := le_sup_left
  have hdQ : zpowers d ≤ Q := le_sup_right
  have h := (IsCyclic.subgroup_eq_iff_card_eq (G := Q) (H := (zpowers c).subgroupOf Q)
    (K := (zpowers d).subgroupOf Q)).2 (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hcQ).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe hdQ).toEquiv, Nat.card_zpowers, Nat.card_zpowers,
        hord])
  have := congrArg (Subgroup.map Q.subtype) h
  rwa [map_subgroupOf_eq_of_le hcQ, map_subgroupOf_eq_of_le hdQ] at this

theorem isPGroup_zpowers_of_pow_prime_eq_one {g : G} (hg : g ^ p = 1) :
    IsPGroup p (zpowers g) :=
  IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hg)

theorem mem_zpowers_of_isCyclic_center [Fact p.Prime]
    (hcyc : ∀ P : Subgroup G, P ≤ center G → IsPGroup p P → IsCyclic P)
    {c d : G} (hc : c ∈ center G) (hd : d ∈ center G) (hcp : c ^ p = 1) (hdp : d ^ p = 1)
    (hord : orderOf d = orderOf c) : d ∈ zpowers c := by
  have hQp : IsPGroup p (zpowers c ⊔ zpowers d : Subgroup G) :=
    (isPGroup_zpowers_of_pow_prime_eq_one hcp).to_sup_of_normal_right'
      (isPGroup_zpowers_of_pow_prime_eq_one hdp)
      ((zpowers_le.2 hc).trans (center_le_normalizer _))
  have hQZ : zpowers c ⊔ zpowers d ≤ center G := sup_le (zpowers_le.2 hc) (zpowers_le.2 hd)
  rw [zpowers_eq_of_isCyclic_sup (hcyc _ hQZ hQp) hord.symm]
  exact mem_zpowers d

end Algebra

@[expose] def GL83PElementCentralizesOmegaCenterAt (p : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    ∀ (K : Subgroup X) (x : X), p.Prime → p ≠ 2 → CFSG.Open.IsComponentOf K ⊤ →
    x ∈ normalizer (K : Set X) → (∃ k : ℕ, x ^ p ^ k = 1) → ∀ c ∈ K, (∀ g ∈ K, g * c = c * g) →
      c ^ p = 1 → x * c * x⁻¹ = c

theorem GL83PElementCentralizesOmegaCenterAt.of_kFact {p : ℕ} (hp5 : 5 ≤ p)
    (h : KFactCenterCyclicGeFive) : GL83PElementCentralizesOmegaCenterAt p := by
  intro X _ _ hcat K x hp _ hK hxN hxp c hcK hcc hcp
  obtain ⟨k, hxk⟩ := hxp
  haveI : Fact p.Prime := ⟨hp⟩
  have hxK : ∀ g, g ∈ K ↔ x * g * x⁻¹ ∈ K := fun g => mem_normalizer_iff.1 hxN g
  have hxc : x * c * x⁻¹ ∈ K := (hxK c).1 hcK
  have hxK' : ∀ g ∈ K, x⁻¹ * g * x ∈ K := fun g hg => by
    rw [hxK]
    simpa [mul_assoc] using hg
  have hcc' : ∀ g ∈ K, g * (x * c * x⁻¹) = (x * c * x⁻¹) * g := by
    intro g hg
    have h1 := hcc _ (hxK' g hg)
    calc g * (x * c * x⁻¹) = x * ((x⁻¹ * g * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * g * x)) * x⁻¹ := by rw [h1]
      _ = (x * c * x⁻¹) * g := by group
  let c₀ : K := ⟨c, hcK⟩
  let c₁ : K := ⟨x * c * x⁻¹, hxc⟩
  have hc₀ : c₀ ∈ center K := mem_center_iff.2 fun g => Subtype.ext (hcc g g.2)
  have hc₁ : c₁ ∈ center K := mem_center_iff.2 fun g => Subtype.ext (hcc' g g.2)
  have hc₀p : c₀ ^ p = 1 := Subtype.ext (by simpa [c₀] using hcp)
  have hc₁p : c₁ ^ p = 1 := Subtype.ext (by simp [c₁, conj_pow, hcp])
  have hord : orderOf c₁ = orderOf c₀ := by
    rw [← Subgroup.orderOf_coe c₁, ← Subgroup.orderOf_coe c₀]
    exact orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective c
  have hcyc := h K hK.2.2 (hcat.isCatalogGroup_center_quotient hK) p hp hp5
  have hmem : c₁ ∈ zpowers c₀ := mem_zpowers_of_isCyclic_center hcyc hc₀ hc₁ hc₀p hc₁p hord
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hmem
  have hn' : x * c * x⁻¹ = c ^ n := by
    have := congrArg Subtype.val hn
    simpa [c₀, c₁] using this.symm
  by_cases hc1 : c = 1
  · rw [hc1, mul_one, mul_inv_cancel]
  · exact CFSG.LocalAnalysis.RankThreeTheoremC.conj_eq_self_of_conj_mem_zpowers hc1 hcp hxk
      (hn' ▸ zpow_mem_zpowers c n)

section CertificateInstances

theorem kFactCenterCyclicGeFive_holds : KFactCenterCyclicGeFive :=
  kFactCenterCyclicGeFive_of_tables
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds sporadicMultipliers_holds

theorem gl83PElementCentralizesOmegaCenterAt_of_five_le {p : ℕ} (hp5 : 5 ≤ p) :
    GL83PElementCentralizesOmegaCenterAt p :=
  GL83PElementCentralizesOmegaCenterAt.of_kFact hp5 kFactCenterCyclicGeFive_holds

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC
