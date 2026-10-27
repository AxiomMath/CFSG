module

public import CFSG.GroupTheory.SteinbergBSFixedPointFree
import CFSG.LocalAnalysis.ComponentClassification.CoprimeAutomorphisms

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem le_centralizer_of_normalizes_line {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {P U X : Subgroup G} (hP : Nat.card P = p ^ 2) (hUP : U ≤ P)
    (hU : Nat.card U = p) (hX : IsPGroup q X)
    (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G))
    (hqp : q ≠ p) (hq : ¬ q ∣ p - 1) : X ≤ Subgroup.centralizer (P : Set G) := by
  classical
  haveI : IsMulCommutative ↥P :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hP
  haveI : (U.subgroupOf P).Normal := Subgroup.normal_of_isMulCommutative (U.subgroupOf P)
  have hUsubcard : Nat.card (U.subgroupOf P) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUP).toEquiv, hU]
  have hQcard : Nat.card (↥P ⧸ (U.subgroupOf P)) = p := by
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (U.subgroupOf P)
    rw [hP, hUsubcard] at hmul
    have h2 : Nat.card (↥P ⧸ (U.subgroupOf P)) * p = p * p := by
      rw [← hmul, pow_two]
    exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos h2
  haveI : IsCyclic ↥U := isCyclic_of_prime_card hU
  haveI : IsCyclic (↥P ⧸ (U.subgroupOf P)) := isCyclic_of_prime_card hQcard
  let actU : X →* MulAut ↥U :=
    (Subgroup.normalizerMonoidHom U).comp (Subgroup.inclusion hXU)
  let actP : X →* MulAut ↥P :=
    (Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hXP)
  have hcopP : ∀ x : X, Nat.Coprime (orderOf x) p := by
    intro x
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    refine Nat.Coprime.of_dvd_left (orderOf_dvd_natCard x) ?_
    rw [hk]
    exact (Nat.Coprime.pow_left k
      ((Nat.coprime_primes (Fact.out : q.Prime) (Fact.out : p.Prime)).mpr hqp))
  have hcopQ : ∀ x : X, Nat.Coprime (orderOf x) (p - 1) := by
    intro x
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    refine Nat.Coprime.of_dvd_left (orderOf_dvd_natCard x) ?_
    rw [hk]
    exact (Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).mpr hq))
  have hfixU : ∀ (x : X) (u : ↥U), actU x u = u := by
    intro x u
    have hpow : actU x ^ orderOf x = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hdvdU : orderOf (actU x) ∣ Nat.card (MulAut ↥U) := orderOf_dvd_natCard _
    have hcardU : Nat.card (MulAut ↥U) = p - 1 := by
      rw [IsCyclic.card_mulAut, hU, Nat.totient_prime (Fact.out : p.Prime)]
    have hdvd : orderOf (actU x) ∣ p - 1 := hcardU ▸ hdvdU
    have hone : orderOf (actU x) = 1 :=
      Nat.eq_one_of_dvd_coprimes (hcopQ x) (orderOf_dvd_of_pow_eq_one hpow) hdvd
    rw [orderOf_eq_one_iff] at hone
    rw [hone]
    rfl
  have hUmap : ∀ x : X,
      (U.subgroupOf P).map (actP x : ↥P →* ↥P) = U.subgroupOf P := by
    intro x
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro d ⟨e, he, rfl⟩
      have heU : (e : G) ∈ U := Subgroup.mem_subgroupOf.mp he
      have h := (Subgroup.mem_normalizer_iff.mp (hXU x.2) (e : G)).mp heU
      have hcoe : (((actP x) e : ↥P) : G) = (x : G) * (e : G) * (x : G)⁻¹ := by
        simpa [actP, MonoidHom.comp_apply, Subgroup.coe_inclusion] using
          Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hXP x) e
      change (((actP x) e : ↥P) : G) ∈ U
      rw [hcoe]
      exact h
    · have hcardmap : Nat.card ↥((U.subgroupOf P).map (actP x : ↥P →* ↥P)) =
          Nat.card ↥(U.subgroupOf P) :=
        Subgroup.card_map_of_injective (f := (actP x : ↥P →* ↥P)) (actP x).injective
      exact le_of_eq hcardmap.symm
  have hdisp : ∀ (x : X) (d : ↥P), d⁻¹ * actP x d ∈ U.subgroupOf P := by
    intro x d
    let ψ : MulAut (↥P ⧸ (U.subgroupOf P)) :=
      QuotientGroup.congr (U.subgroupOf P) (U.subgroupOf P) (actP x) (hUmap x)
    have hψeq : ψ = QuotientGroup.congr (U.subgroupOf P) (U.subgroupOf P) (actP x)
        (hUmap x) := rfl
    have hpow : ψ ^ orderOf x = 1 := by
      refine MulEquiv.ext fun z => ?_
      obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective z
      rw [hψeq, CFSG.GroupTheory.SteinbergBS.quotientCongr_pow_mk, ← map_pow,
        pow_orderOf_eq_one, map_one]
      rfl
    have hdvdU : orderOf ψ ∣ Nat.card (MulAut (↥P ⧸ (U.subgroupOf P))) :=
      orderOf_dvd_natCard _
    have hcardU : Nat.card (MulAut (↥P ⧸ (U.subgroupOf P))) = p - 1 := by
      rw [IsCyclic.card_mulAut, hQcard, Nat.totient_prime (Fact.out : p.Prime)]
    have hdvd : orderOf ψ ∣ p - 1 := hcardU ▸ hdvdU
    have hone : orderOf ψ = 1 :=
      Nat.eq_one_of_dvd_coprimes (hcopQ x) (orderOf_dvd_of_pow_eq_one hpow) hdvd
    have hfix : (((actP x) d : ↥P) : ↥P ⧸ (U.subgroupOf P)) =
        (d : ↥P ⧸ (U.subgroupOf P)) := by
      have h1 : ψ ((d : ↥P) : ↥P ⧸ (U.subgroupOf P)) =
          (d : ↥P ⧸ (U.subgroupOf P)) := by
        rw [orderOf_eq_one_iff] at hone
        rw [hone]
        rfl
      rwa [hψeq, QuotientGroup.congr_mk] at h1
    have hmem : ((d : ↥P)⁻¹ * (actP x) d ∈ U.subgroupOf P) :=
      (QuotientGroup.eq (s := U.subgroupOf P)).mp hfix.symm
    exact hmem
  intro x hxX
  rw [Subgroup.mem_centralizer_iff]
  intro d hdP
  let φ : MulAut ↥P := actP ⟨x, hxX⟩
  have hφpow : φ ^ orderOf (⟨x, hxX⟩ : X) = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hcop : Nat.Coprime (orderOf (⟨x, hxX⟩ : X)) (Nat.card (U.subgroupOf P)) := by
    rw [hUsubcard]
    simpa [Subgroup.orderOf_mk] using hcopP ⟨x, hxX⟩
  have hfixφ : ∀ e ∈ U.subgroupOf P, φ e = e := by
    intro e he
    apply Subtype.ext
    have heU : (e : G) ∈ U := Subgroup.mem_subgroupOf.mp he
    have h1 : ((actU ⟨x, hxX⟩ ⟨(e : G), heU⟩ : ↥U) : G) = (e : G) := by
      rw [hfixU ⟨x, hxX⟩ ⟨(e : G), heU⟩]
    simpa [φ, actP, actU, MonoidHom.comp_apply, Subgroup.coe_inclusion,
      Subgroup.normalizerMonoidHom_apply_apply_coe] using h1
  have hdisplacement : ∀ e : ↥P, e⁻¹ * φ e ∈ U.subgroupOf P := fun e =>
    hdisp ⟨x, hxX⟩ e
  have hφone : φ = 1 :=
    CFSG.ComponentClassification.CoprimeAutomorphisms.eq_one_of_fixed_displacement
      (U.subgroupOf P) φ (orderOf (⟨x, hxX⟩ : X)) hφpow hcop hfixφ hdisplacement
  have hφd : ((φ ⟨d, hdP⟩ : ↥P) : G) = d := by
    have h1 := congrArg (fun f : MulAut ↥P => ((f ⟨d, hdP⟩ : ↥P) : G)) hφone
    simpa using h1
  have hcoe : ((φ ⟨d, hdP⟩ : ↥P) : G) = (x : G) * d * (x : G)⁻¹ := by
    simpa [φ, actP, MonoidHom.comp_apply, Subgroup.coe_inclusion] using
      Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hXP ⟨x, hxX⟩) ⟨d, hdP⟩
  rw [hcoe] at hφd
  calc d * x = (x * d * x⁻¹) * x := by rw [hφd]
    _ = x * d := by group

end CFSG.GroupTheory
