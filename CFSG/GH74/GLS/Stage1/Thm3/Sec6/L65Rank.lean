module

public import CFSG.GH74.Generic.S3.PumpDiag

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.Generic
open scoped commutatorElement

theorem rankCertified_alt7 : RankCertified (alternatingGroup (Fin 7)) 1 := by
  refine rankCertified_of_commuting_involutions
    (![⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩,
      ⟨Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩] :
      Fin 2 → alternatingGroup (Fin 7)) ?_ ?_ ?_ (s := 1) (by norm_num)
  · decide
  · simp only [Commute, SemiconjBy]
    decide
  · decide

private theorem mem_center_of_mul_eq_central {H : Type*} [Group H] {A A' : Subgroup H}
    (hcomm : ∀ a ∈ A, ∀ a' ∈ A', a * a' = a' * a) {z : H} (hz : ∀ g : H, g * z = z * g)
    {a : ↥A} {a' : ↥A'} (h : (a : H) * a' = z) :
    a ∈ center ↥A ∧ a' ∈ center ↥A' := by
  constructor
  · rw [Subgroup.mem_center_iff]
    intro x
    have hxa' : Commute (x : H) (a' : H) := hcomm x x.2 a' a'.2
    have hxz : Commute (x : H) z := hz x
    have ha : (a : H) = z * (a' : H)⁻¹ := by rw [← h]; group
    apply Subtype.ext
    show (x : H) * (a : H) = (a : H) * (x : H)
    rw [ha]
    exact (hxz.mul_right hxa'.inv_right).eq
  · rw [Subgroup.mem_center_iff]
    intro y
    have hay : Commute (a : H) (y : H) := hcomm a a.2 y y.2
    have hyz : Commute (y : H) z := hz y
    have ha' : (a' : H) = (a : H)⁻¹ * z := by rw [← h]; group
    apply Subtype.ext
    show (y : H) * (a' : H) = (a' : H) * (y : H)
    rw [ha']
    exact ((hay.inv_left.symm).mul_right hyz).eq

theorem not_gen4_of_two_a7 {H : Type} [Group H] [Finite H] (hH : Gen4 H) {A A' : Subgroup H}
    (hcomm : ∀ a ∈ A, ∀ a' ∈ A', a * a' = a' * a)
    (hA : Nonempty (↥A ⧸ center ↥A ≃* alternatingGroup (Fin 7)))
    (hA' : Nonempty (↥A' ⧸ center ↥A' ≃* alternatingGroup (Fin 7)))
    (hZ : Odd (Nat.card (center ↥A))) (hZ' : Odd (Nat.card (center ↥A')))
    {c : H} (hc : c ∈ center H) (hc2 : orderOf c = 2) : False := by
  obtain ⟨e⟩ := hA
  obtain ⟨e'⟩ := hA'
  have hcc : ∀ g : H, g * c = c * g := Subgroup.mem_center_iff.1 hc
  have hcc2 : c * c = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hc2, sq] at this
  let ψ : ↥A × ↥A' →* H :=
    (A.subtype).noncommCoprod (A'.subtype) (fun a a' => hcomm a a.2 a' a'.2)
  let π₁ : ↥A →* alternatingGroup (Fin 7) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (center ↥A))
  let π₂ : ↥A' →* alternatingGroup (Fin 7) :=
    e'.toMonoidHom.comp (QuotientGroup.mk' (center ↥A'))
  let π : ↥A × ↥A' →* alternatingGroup (Fin 7) × alternatingGroup (Fin 7) := π₁.prodMap π₂
  have hπ : Function.Surjective π :=
    (e.surjective.comp (QuotientGroup.mk'_surjective _)).prodMap
      (e'.surjective.comp (QuotientGroup.mk'_surjective _))
  have hπ₁ : ∀ a : ↥A, a ∈ center ↥A → π₁ a = 1 := fun a ha => by
    have h1 : QuotientGroup.mk' (center ↥A) a = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff a).2 ha
    show e (QuotientGroup.mk' (center ↥A) a) = 1
    rw [h1, map_one]
  have hπ₂ : ∀ a : ↥A', a ∈ center ↥A' → π₂ a = 1 := fun a ha => by
    have h1 : QuotientGroup.mk' (center ↥A') a = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff a).2 ha
    show e' (QuotientGroup.mk' (center ↥A') a) = 1
    rw [h1, map_one]
  have hker : ψ.ker ≤ π.ker := by
    rintro ⟨a, a'⟩ hp
    have h1 : (a : H) * a' = 1 := hp
    obtain ⟨ha, ha'⟩ := mem_center_of_mul_eq_central hcomm (z := 1) (fun g => by simp) h1
    rw [MonoidHom.mem_ker]
    exact Prod.ext (hπ₁ a ha) (hπ₂ a' ha')
  have hK3 : RankCertified (alternatingGroup (Fin 7) × alternatingGroup (Fin 7)) 3 :=
    rankCertified_alt7.prod rankCertified_alt7
  let B : Subgroup H := ψ.range
  have hcertB : RankCertified ↥B 3 :=
    RankCertified.of_hom_ker_le ψ.rangeRestrict π hπ
      (by rw [MonoidHom.ker_rangeRestrict]; exact hker) hK3
  have hcB : c ∉ B := by
    rintro ⟨⟨a, a'⟩, hef⟩
    have h1 : (a : H) * a' = c := hef
    obtain ⟨ha, ha'⟩ := mem_center_of_mul_eq_central hcomm hcc h1
    have hoa : Odd (orderOf (a : H)) := by
      rw [Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat hZ (Subgroup.orderOf_dvd_natCard _ ha)
    have hoa' : Odd (orderOf (a' : H)) := by
      rw [Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat hZ' (Subgroup.orderOf_dvd_natCard _ ha')
    have hac : Commute (a : H) (a' : H) := hcomm a a.2 a' a'.2
    have hnodd : Odd (orderOf (a : H) * orderOf (a' : H)) := hoa.mul hoa'
    have hcn : c ^ (orderOf (a : H) * orderOf (a' : H)) = 1 := by
      rw [← h1, hac.mul_pow, pow_mul, pow_orderOf_eq_one, one_pow, mul_comm, pow_mul,
        pow_orderOf_eq_one, one_pow, one_mul]
    have hdvd : orderOf c ∣ orderOf (a : H) * orderOf (a' : H) := orderOf_dvd_of_pow_eq_one hcn
    rw [hc2] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    rcases hnodd with ⟨m, hm⟩
    omega
  have hcert : RankCertified H (3 + 1) :=
    RankCertified.of_central_involution (K := B) hcc hcc2 hcB hcertB
  exact hcert.not_gen4 (by norm_num) hH

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
