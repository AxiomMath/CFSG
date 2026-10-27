module

public import CFSG.FeitThompson.Local.SecondCenterPlaneCharacteristicCentralizer
public import CFSG.FeitThompson.Local.CentralProductPlaneCentralizer
import CFSG.FeitThompson.Local.MaximalPlaneCentralizerPrimeTorsion
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup
open scoped commutatorElement

variable {p : ℕ} {R : Type*} [Group R] {E A₀ : Subgroup R}

def planeCyclicFactor (p : ℕ) {R : Type*} [Group R] (E : Subgroup R) : Subgroup R :=
  centralizer ((secondCenterTorsion p R : Subgroup R) : Set R) ⊓ centralizer (E : Set R)

theorem planeCyclicFactor_eq (p : ℕ) (E : Subgroup R) :
    planeCyclicFactor p E =
      centralizer ((secondCenterTorsion p R : Subgroup R) : Set R) ⊓
        centralizer (E : Set R) := (rfl)

theorem planeCyclicFactor_le_centralizer_secondCenterTorsion :
    planeCyclicFactor p E ≤ centralizer ((secondCenterTorsion p R : Subgroup R) : Set R) := by
  rw [planeCyclicFactor_eq]; exact inf_le_left

theorem planeCyclicFactor_le_centralizer :
    planeCyclicFactor p E ≤ centralizer (E : Set R) := by
  rw [planeCyclicFactor_eq]; exact inf_le_right

theorem mem_planeCyclicFactor {x : R}
    (h1 : x ∈ centralizer ((secondCenterTorsion p R : Subgroup R) : Set R))
    (h2 : x ∈ centralizer (E : Set R)) : x ∈ planeCyclicFactor p E := by
  rw [planeCyclicFactor_eq]; exact Subgroup.mem_inf.2 ⟨h1, h2⟩

theorem mem_planeCyclicFactor_iff {x : R} :
    x ∈ planeCyclicFactor p E ↔
      x ∈ centralizer ((secondCenterTorsion p R : Subgroup R) : Set R) ∧
        x ∈ centralizer (E : Set R) := by
  rw [planeCyclicFactor_eq]; exact Subgroup.mem_inf

theorem centerTorsionBy_le_planeCyclicFactor : centerTorsionBy R p ≤ planeCyclicFactor p E :=
  fun _ hz => mem_planeCyclicFactor
    (center_le_centralizer _ (centerTorsionBy_le_center p hz))
    (center_le_centralizer _ (centerTorsionBy_le_center p hz))

private theorem inf_eq_bot_of_ne_of_natCard_eq_prime {H K : Subgroup R} [Finite H] [Finite K]
    (hp : p.Prime) (hH : Nat.card H = p) (hK : Nat.card K = p) (hne : H ≠ K) : H ⊓ K = ⊥ := by
  have hdvd : Nat.card (H ⊓ K : Subgroup R) ∣ p := hH ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | hp'
  · exact Subgroup.card_eq_one.1 h1
  · have e1 : H ⊓ K = H := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hp', hH])
    have e2 : H ⊓ K = K := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hp', hK])
    exact absurd (e1 ▸ e2) hne

theorem isInternalDirectProduct_centralizer_of_inf_of_sup (hEcomm : IsMulCommutative ↥E)
    (hA₀E : A₀ ≤ E)
    (hinf : A₀ ⊓ centralizer ((secondCenterTorsion p R : Subgroup R) : Set R) = ⊥)
    (hsupT : A₀ ⊔ centralizer ((secondCenterTorsion p R : Subgroup R) : Set R) = ⊤) :
    IsInternalDirectProduct (centralizer (E : Set R)) A₀ (planeCyclicFactor p E) := by
  set T := centralizer ((secondCenterTorsion p R : Subgroup R) : Set R) with hT
  have hA₀C : A₀ ≤ centralizer (E : Set R) := hA₀E.trans (Subgroup.le_centralizer E)
  refine
    { left_le := hA₀C
      right_le := planeCyclicFactor_le_centralizer
      coe_eq_mul := ?_
      inf_eq_bot := ?_
      commutator_eq_bot := ?_ }
  · refine Set.eq_of_subset_of_subset (fun x hx => ?_) ?_
    · have hxR : x ∈ ((A₀ ⊔ T : Subgroup R) : Set R) := by rw [hsupT]; trivial
      rw [Subgroup.mul_normal] at hxR
      obtain ⟨a, ha, t, ht, rfl⟩ := hxR
      have haC : a ∈ centralizer (E : Set R) := hA₀C ha
      have htC : t ∈ centralizer (E : Set R) := by
        have hte : t = a⁻¹ * (a * t) := by group
        rw [hte]
        exact mul_mem (inv_mem haC) hx
      exact Set.mul_mem_mul ha (mem_planeCyclicFactor ht htC)
    · rintro x ⟨a, ha, y, hy, rfl⟩
      exact mul_mem (hA₀C ha) (planeCyclicFactor_le_centralizer hy)
  · rw [← le_bot_iff, ← hinf]
    exact le_inf inf_le_left
      (inf_le_right.trans planeCyclicFactor_le_centralizer_secondCenterTorsion)
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun a ha =>
      mem_centralizer_iff.2 fun y hy =>
        ((mem_centralizer_iff.1 (planeCyclicFactor_le_centralizer hy)) a (hA₀E ha)).symm

variable [Finite R]

theorem sup_centerTorsionBy_eq_of_natCard_eq_prime (hp : p.Prime) (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R)
    (hA₀E : A₀ ≤ E) (hA₀card : Nat.card A₀ = p) (hA₀ : A₀ ≠ centerTorsionBy R p) :
    A₀ ⊔ centerTorsionBy R p = E := by
  have hZE : centerTorsionBy R p ≤ E := centerTorsionBy_le_of_maximal hE
  have hZcard : Nat.card (centerTorsionBy R p) = p :=
    natCard_centerTorsionBy_of_maximal hp hRp hE hplane hrank
  have hinf : A₀ ⊓ centerTorsionBy R p = ⊥ :=
    inf_eq_bot_of_ne_of_natCard_eq_prime hp hA₀card hZcard hA₀
  have hcomm : ⁅A₀, centerTorsionBy R p⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun x _ =>
      mem_centralizer_iff.2 fun y hy => ((mem_center_iff.1 (centerTorsionBy_le_center p hy)) x).symm
  have hdp : IsInternalDirectProduct (A₀ ⊔ centerTorsionBy R p) A₀ (centerTorsionBy R p) :=
    isInternalDirectProduct_of_sup_eq rfl hinf hcomm
  refine Subgroup.eq_of_le_of_card_ge (sup_le hA₀E hZE) ?_
  rw [hdp.card_eq_mul, hA₀card, hZcard, hplane, pow_two]

theorem inf_and_sup_centralizer_secondCenterTorsion (hp : p.Prime) (hodd : Odd p)
    (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R)
    (hA₀E : A₀ ≤ E) (hA₀card : Nat.card A₀ = p) (hA₀ : A₀ ≠ centerTorsionBy R p) :
    A₀ ⊓ centralizer ((secondCenterTorsion p R : Subgroup R) : Set R) = ⊥ ∧
      A₀ ⊔ centralizer ((secondCenterTorsion p R : Subgroup R) : Set R) = ⊤ := by
  set T := centralizer ((secondCenterTorsion p R : Subgroup R) : Set R) with hT
  have hsup : A₀ ⊔ centerTorsionBy R p = E :=
    sup_centerTorsionBy_eq_of_natCard_eq_prime hp hRp hE hplane hrank hA₀E hA₀card hA₀
  have hTidx : T.index = p :=
    (characteristic_and_index_centralizer_secondCenterTorsion hp hodd hRp hE hplane hrank).2
  have hZT : centerTorsionBy R p ≤ T := fun z hz =>
    center_le_centralizer _ (centerTorsionBy_le_center p hz)
  have hA₀T : ¬ A₀ ≤ T := fun h =>
    not_le_centralizer_secondCenterTorsion hp hodd hRp hE hplane hrank (hsup ▸ sup_le h hZT)
  have hinf : A₀ ⊓ T = ⊥ := by
    have hdvd : Nat.card (A₀ ⊓ T : Subgroup R) ∣ p := hA₀card ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | hp'
    · exact Subgroup.card_eq_one.1 h1
    · exact absurd (le_of_eq_of_le
        (Subgroup.eq_of_le_of_card_ge (inf_le_left (a := A₀) (b := T))
          (by rw [hp', hA₀card])).symm inf_le_right) hA₀T
  refine ⟨hinf, ?_⟩
  have hdvd : (A₀ ⊔ T).index ∣ p := hTidx ▸ Subgroup.index_dvd_of_le le_sup_right
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | hp'
  · exact Subgroup.index_eq_one.1 h1
  · exfalso
    have h1 : (A₀ ⊔ T).index * Nat.card ↥(A₀ ⊔ T) = T.index * Nat.card ↥T := by
      rw [Subgroup.index_mul_card, Subgroup.index_mul_card]
    rw [hp', hTidx] at h1
    have h2 : T = A₀ ⊔ T :=
      Subgroup.eq_of_le_of_card_ge le_sup_right
        (Nat.le_of_eq (Nat.eq_of_mul_eq_mul_left hp.pos h1))
    exact hA₀T (h2 ▸ le_sup_left)

theorem isInternalDirectProduct_centralizer_planeCyclicFactor (hp : p.Prime) (hodd : Odd p)
    (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R)
    (hA₀E : A₀ ≤ E) (hA₀card : Nat.card A₀ = p) (hA₀ : A₀ ≠ centerTorsionBy R p) :
    IsInternalDirectProduct (centralizer (E : Set R)) A₀ (planeCyclicFactor p E) := by
  obtain ⟨hinf, hsupT⟩ := inf_and_sup_centralizer_secondCenterTorsion hp hodd hRp hE hplane hrank
    hA₀E hA₀card hA₀
  exact isInternalDirectProduct_centralizer_of_inf_of_sup hE.prop.1 hA₀E hinf hsupT

theorem inf_planeCyclicFactor_eq_centerTorsionBy (hp : p.Prime) (hodd : Odd p)
    (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R) :
    E ⊓ planeCyclicFactor p E = centerTorsionBy R p := by
  have hZE : centerTorsionBy R p ≤ E := centerTorsionBy_le_of_maximal hE
  have hZY : centerTorsionBy R p ≤ planeCyclicFactor p E := centerTorsionBy_le_planeCyclicFactor
  have hZcard : Nat.card (centerTorsionBy R p) = p :=
    natCard_centerTorsionBy_of_maximal hp hRp hE hplane hrank
  have hnotle : ¬ E ≤ planeCyclicFactor p E := fun h =>
    not_le_centralizer_secondCenterTorsion hp hodd hRp hE hplane hrank
      (h.trans planeCyclicFactor_le_centralizer_secondCenterTorsion)
  refine (Subgroup.eq_of_le_of_card_ge (le_inf hZE hZY) ?_).symm
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).1
    (hplane ▸ Subgroup.card_dvd_of_le (inf_le_left : E ⊓ planeCyclicFactor p E ≤ E))
  have hZC : Nat.card (centerTorsionBy R p) ≤ Nat.card (E ⊓ planeCyclicFactor p E : Subgroup R) :=
    Subgroup.card_le_of_le (le_inf hZE hZY)
  rw [hZcard, hk] at hZC
  rw [hZcard, hk]
  interval_cases k
  · simp only [pow_zero] at hZC
    have := hp.one_lt; omega
  · rw [pow_one]
  · exact absurd (le_of_eq_of_le
      (Subgroup.eq_of_le_of_card_ge (inf_le_left (a := E) (b := planeCyclicFactor p E))
        (by rw [hplane, hk])).symm inf_le_right) hnotle

theorem mem_centerTorsionBy_of_mem_planeCyclicFactor_of_pow_eq_one (hp : p.Prime) (hodd : Odd p)
    (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R) {y : R}
    (hy : y ∈ planeCyclicFactor p E) (hyp : y ^ p = 1) : y ∈ centerTorsionBy R p := by
  rw [← inf_planeCyclicFactor_eq_centerTorsionBy hp hodd hRp hE hplane hrank]
  exact Subgroup.mem_inf.2
    ⟨mem_of_maximal_of_mem_centralizer_of_pow_eq_one hE (planeCyclicFactor_le_centralizer hy) hyp,
      hy⟩

theorem isCyclic_planeCyclicFactor (hp : p.Prime) (hodd : Odd p) (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R) :
    IsCyclic ↥(planeCyclicFactor p E) := by
  by_contra hnc
  set Y := planeCyclicFactor p E with hY
  have hZcard : Nat.card (centerTorsionBy R p) = p :=
    natCard_centerTorsionBy_of_maximal hp hRp hE hplane hrank
  have h2 : 2 ≤ elementaryAbelianPRank p ↥Y :=
    two_le_elementaryAbelianPRank_of_not_isCyclic hp hodd (hRp.to_subgroup Y) hnc
  obtain ⟨H, ⟨f⟩⟩ := exists_subgroup_mulEquiv_of_elementaryAbelianPRank (p := p) (X := ↥Y) hp.one_lt
  have hHcard : Nat.card ↥H = p ^ elementaryAbelianPRank p ↥Y := by
    rw [Nat.card_congr f.toEquiv, card_pi_multiplicative_zmod]
  have hmap : H.map Y.subtype ≤ centerTorsionBy R p := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    have h1 : (⟨a, ha⟩ : ↥H) ^ p = 1 :=
      f.injective (by rw [map_pow, pow_eq_one_pi_multiplicative_zmod, map_one])
    have h3 : (a : R) ^ p = 1 := by
      simpa using congrArg (Subgroup.subtype Y) (congrArg (Subgroup.subtype H) h1)
    exact mem_centerTorsionBy_of_mem_planeCyclicFactor_of_pow_eq_one hp hodd hRp hE hplane hrank
      a.2 h3
  have hcard : Nat.card ↥(H.map Y.subtype) = p ^ elementaryAbelianPRank p ↥Y := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hHcard]
  have hle : p ^ elementaryAbelianPRank p ↥Y ≤ p := by
    rw [← hcard, ← hZcard]; exact Subgroup.card_le_of_le hmap
  have hge : p ^ 2 ≤ p ^ elementaryAbelianPRank p ↥Y := Nat.pow_le_pow_right hp.pos h2
  have hlt : p < p ^ 2 := by nlinarith [hp.one_lt]
  omega

theorem planeCyclicFactor_spec (hp : p.Prime) (hodd : Odd p) (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R) :
    IsCyclic ↥(planeCyclicFactor p E) ∧ centerTorsionBy R p ≤ planeCyclicFactor p E ∧
      ∀ A₀ : Subgroup R, A₀ ≤ E → Nat.card A₀ = p → A₀ ≠ centerTorsionBy R p →
        IsInternalDirectProduct (centralizer (E : Set R)) A₀ (planeCyclicFactor p E) :=
  ⟨isCyclic_planeCyclicFactor hp hodd hRp hE hplane hrank, centerTorsionBy_le_planeCyclicFactor,
    fun _ hA₀E hA₀card hA₀ => isInternalDirectProduct_centralizer_planeCyclicFactor hp hodd hRp hE
      hplane hrank hA₀E hA₀card hA₀⟩

end

end CFSG.FeitThompson
