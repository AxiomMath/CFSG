module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4W49Lift

public section

namespace CFSG.OddStandard.AltStdSmall4.W49

open Subgroup

theorem oddCoversTrivial_of_sq_not_dvd {K : Type} [Group K] [Finite K]
    (hK : ∀ p : ℕ, p.Prime → Odd p → ¬ p ^ 2 ∣ Nat.card K) : OddCoversTrivial K := by
  intro Γ _ _ hperf π hπ hZc hodd
  classical
  rw [eq_bot_iff]
  intro x hx
  by_contra hx1
  rw [Subgroup.mem_bot] at hx1
  obtain ⟨p, hp, hpdvd⟩ : ∃ p, p.Prime ∧ p ∣ orderOf x :=
    Nat.exists_prime_and_dvd (by rwa [Ne, orderOf_eq_one_iff])
  haveI : Fact p.Prime := ⟨hp⟩
  have hxo : orderOf x ∣ Nat.card π.ker := by
    have := Subgroup.orderOf_dvd_natCard π.ker hx
    exact this
  have hpodd : Odd p := hodd.of_dvd_nat (hpdvd.trans hxo)
  obtain ⟨m, hm⟩ := hpdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact (orderOf_pos x).ne' hm
  set g := x ^ m with hgdef
  have hgo : orderOf g = p := by
    rw [hgdef, orderOf_pow' x hm0, hm, Nat.gcd_mul_left_left,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hgZ : g ∈ π.ker := pow_mem hx m
  have hgc : g ∈ center Γ := hZc hgZ
  have hgp : IsPGroup p (zpowers g) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hgo, pow_one]
  obtain ⟨P, hgP⟩ := hgp.exists_le_sylow
  have hgPm : g ∈ (P : Subgroup Γ) := hgP (mem_zpowers g)
  let f : ↥(P : Subgroup Γ) →* K := π.comp (P : Subgroup Γ).subtype
  have hfr : IsCyclic ↥f.range := by
    have hpg : IsPGroup p ↥f.range :=
      P.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := hpg.exists_card_eq
    have hdvd : p ^ k ∣ Nat.card K := hk ▸ Subgroup.card_subgroup_dvd_card f.range
    have hk1 : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      exact hK p hp hpodd ((pow_dvd_pow p hk2).trans hdvd)
    interval_cases k
    · rw [pow_zero] at hk
      have : Subsingleton ↥f.range := (Nat.card_eq_one_iff_unique.1 hk).1
      exact isCyclic_of_subsingleton
    · rw [pow_one] at hk
      exact isCyclic_of_prime_card hk
  have hfker : f.rangeRestrict.ker ≤ center ↥(P : Subgroup Γ) := by
    intro a ha
    rw [MonoidHom.ker_rangeRestrict] at ha
    have ha' : (a : Γ) ∈ π.ker := MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 ha)
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    show (b : Γ) * a = a * b
    exact Subgroup.mem_center_iff.1 (hZc ha') b
  have hcommP : IsMulCommutative ↥(P : Subgroup Γ) :=
    f.rangeRestrict.isMulCommutative_of_isCyclic_of_ker_le_center hfker
  letI : CommGroup ↥(P : Subgroup Γ) :=
    { (inferInstance : Group ↥(P : Subgroup Γ)) with
      mul_comm := fun a b => hcommP.is_comm.comm a b }
  let τ : Γ →* ↥(P : Subgroup Γ) := (MonoidHom.id ↥(P : Subgroup Γ)).transfer
  have hτ : τ g = 1 := by
    have h1 : g ∈ commutator Γ := Group.IsPerfect.mem_commutator
    exact Abelianization.commutator_subset_ker τ h1
  have hτg : τ g = ⟨g ^ (P : Subgroup Γ).index, MonoidHom.transfer_eq_pow_aux g (fun k g₀ _ => by
      rw [show g₀⁻¹ * g ^ k * g₀ = g₀⁻¹ * (g ^ k * g₀) by group,
        (Subgroup.mem_center_iff.1 (pow_mem hgc k) g₀).symm, inv_mul_cancel_left])⟩ :=
    MonoidHom.transfer_eq_pow _ g (fun k g₀ _ => by
      rw [show g₀⁻¹ * g ^ k * g₀ = g₀⁻¹ * (g ^ k * g₀) by group,
        (Subgroup.mem_center_iff.1 (pow_mem hgc k) g₀).symm, inv_mul_cancel_left])
  have hgi : g ^ (P : Subgroup Γ).index = 1 := by
    have := congrArg Subtype.val (hτg.symm.trans hτ)
    exact this
  have hdvd : orderOf g ∣ (P : Subgroup Γ).index := orderOf_dvd_of_pow_eq_one hgi
  rw [hgo] at hdvd
  exact P.not_dvd_index hdvd

end CFSG.OddStandard.AltStdSmall4.W49
