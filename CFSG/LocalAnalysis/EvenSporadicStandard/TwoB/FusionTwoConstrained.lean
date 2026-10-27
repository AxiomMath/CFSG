module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.ClaimA

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.EvenSporadicStandard.TwoFi22

variable {G : Type} [Group G]

theorem commute_of_axb_conj [Finite G] {Q B : Subgroup G} {c : G} (hQ : IsPGroup 2 Q)
    (hB : IsPGroup 2 B) (hcQ : c ∈ normalizer (Q : Set G)) (hBQ : B ≤ normalizer (Q : Set G))
    (hc : Odd (orderOf c)) (hcB : ∀ b ∈ B, c * b = b * c)
    (hfix : ∀ q ∈ Q, (∀ b ∈ B, q * b = b * q) → c * q = q * c) :
    ∀ q ∈ Q, c * q = q * c := by
  set A := zpowers c with hAdef
  have hAQ : A ≤ normalizer (Q : Set G) := zpowers_le.mpr hcQ
  let α : A →* MulAut Q := Q.normalizerMonoidHom.comp (inclusion hAQ)
  let β : B →* MulAut Q := Q.normalizerMonoidHom.comp (inclusion hBQ)
  have hα : ∀ (a : A) (q : Q), ((α a q : Q) : G) = (a : G) * q * (a : G)⁻¹ := fun _ _ => rfl
  have hβ : ∀ (b : B) (q : Q), ((β b q : Q) : G) = (b : G) * q * (b : G)⁻¹ := fun _ _ => rfl
  have hA2 : ¬ 2 ∣ Nat.card A := by
    rw [hAdef, Nat.card_zpowers]
    exact hc.not_two_dvd_nat
  have hab : ∀ (a : A) (b : B), (a : G) * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (hcB b hb) k).eq
  have hcomm : ∀ a b, α a * β b = β b * α a := by
    intro a b
    ext q
    simp only [MulAut.mul_apply]
    rw [hα, hβ, hβ, hα]
    calc (a : G) * ((b : G) * q * (b : G)⁻¹) * (a : G)⁻¹
        = ((a : G) * b) * q * ((a : G) * b)⁻¹ := by group
      _ = ((b : G) * a) * q * ((b : G) * a)⁻¹ := by rw [hab a b]
      _ = (b : G) * ((a : G) * q * (a : G)⁻¹) * (b : G)⁻¹ := by group
  have hfix' : ∀ a r, (∀ b, β b r = r) → α a r = r := by
    rintro ⟨a, ha⟩ r hr
    have hrB : ∀ b ∈ B, (r : G) * b = b * r := by
      intro b hb
      have h := congrArg Subtype.val (hr ⟨b, hb⟩)
      rw [hβ] at h
      calc (r : G) * b = b * r * b⁻¹ * b := by rw [h]
        _ = b * r := by group
    have hcr := hfix r r.2 hrB
    apply Subtype.ext
    rw [hα]
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    have : Commute (c ^ k) (r : G) := Commute.zpow_left hcr k
    change c ^ k * r * (c ^ k)⁻¹ = r
    rw [this.eq]
    group
  have h := CFSG.GroupTheory.thompson_A_times_B hQ hA2 hB α β hcomm hfix'
  intro q hq
  have hq' := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : G)) (h ⟨c, mem_zpowers c⟩)
  rw [hα] at hq'
  change c * q * c⁻¹ = ((1 : MulAut Q) ⟨q, hq⟩ : G) at hq'
  rw [MulAut.one_apply] at hq'
  calc c * q = c * q * c⁻¹ * c := by group
    _ = q * c := by rw [hq']

theorem IsTwoConstrained.eq_one_of_odd_orderOf [Finite G] {K : Subgroup G}
    (hK : IsTwoConstrained K) {u : G} (hu : u ∈ K) (hu2 : orderOf u = 2) {ρ : G}
    (hρ : ρ ∈ K ⊓ centralizer ({u} : Set G) ⊓
      centralizer (O2In (K ⊓ centralizer ({u} : Set G)) : Set G))
    (hodd : Odd (orderOf ρ)) : ρ = 1 := by
  obtain ⟨⟨hρK, hρu⟩, hρC⟩ := hρ
  have hρu' : Commute ρ u := mem_centralizer_singleton_iff.1 hρu
  have hQ2 : IsPGroup 2 (O2In K) := isPGroup_O2In K
  have hVM : O2In K ⊓ centralizer ({u} : Set G) ≤ K ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (O2In_le K)
  have hVn : ((O2In K ⊓ centralizer ({u} : Set G)).subgroupOf
      (K ⊓ centralizer ({u} : Set G))).Normal := by
    rw [normal_subgroupOf_iff hVM]
    rintro v m ⟨hvQ, hvu⟩ ⟨hmK, hmu⟩
    have hmu' : Commute m u := mem_centralizer_singleton_iff.1 hmu
    have hvu' : Commute v u := mem_centralizer_singleton_iff.1 hvu
    exact ⟨(mem_normalizer_iff.1 (mem_normalizer_O2In hmK) v).1 hvQ,
      mem_centralizer_singleton_iff.2 ((hmu'.mul_left hvu').mul_left hmu'.inv_left)⟩
  have hVO : O2In K ⊓ centralizer ({u} : Set G) ≤ O2In (K ⊓ centralizer ({u} : Set G)) :=
    le_O2In hVM hVn (hQ2.to_le inf_le_left)
  have key := commute_of_axb_conj hQ2 (isPGroup_zpowers_two hu2) (mem_normalizer_O2In hρK)
    (zpowers_le.2 (mem_normalizer_O2In hu)) hodd
    (fun b hb => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
      exact (hρu'.zpow_right k).eq)
    (fun q hq hqB => by
      have hqu : q ∈ centralizer ({u} : Set G) :=
        mem_centralizer_singleton_iff.2 (hqB u (mem_zpowers u))
      exact (mem_centralizer_iff.1 hρC q (hVO ⟨hq, hqu⟩)).symm)
  have hρQ : ρ ∈ O2In K := hK ⟨hρK, mem_centralizer_iff.2 fun q hq => (key q hq).symm⟩
  by_contra hne
  have h2 : 2 ∣ orderOf (⟨ρ, hρQ⟩ : O2In K) :=
    hQ2.dvd_orderOf fun h => hne (congrArg Subtype.val h)
  rw [orderOf_mk] at h2
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

theorem IsTwoConstrained.inf_centralizer [Finite G] {K : Subgroup G}
    (hK : IsTwoConstrained K) {u : G} (hu : u ∈ K) (hu2 : orderOf u = 2) :
    IsTwoConstrained (K ⊓ Subgroup.centralizer ({u} : Set G)) := by
  set M : Subgroup G := K ⊓ centralizer ({u} : Set G)
  have hodd : ∀ x ∈ M ⊓ centralizer (O2In M : Set G), Odd (orderOf x) → x = 1 :=
    fun x hx hx2 => hK.eq_one_of_odd_orderOf hu hu2 hx hx2
  have hCM : M ⊓ centralizer (O2In M : Set G) ≤ M := inf_le_left
  have hC2 : IsPGroup 2 ↥(M ⊓ centralizer (O2In M : Set G)) := by
    rw [IsPGroup.iff_card]
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdvd => ?_⟩
    by_contra hne
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' d hdvd
    have hx1 : x = 1 := OneMemClass.coe_eq_one.1
      (hodd x x.2 (by rw [orderOf_coe, hx]; exact hd.odd_of_ne_two hne))
    rw [hx1, orderOf_one] at hx
    exact hd.one_lt.ne hx
  have hCn : ((M ⊓ centralizer (O2In M : Set G)).subgroupOf M).Normal := by
    rw [normal_subgroupOf_iff hCM]
    rintro h k ⟨hhM, hhC⟩ hkM
    refine ⟨M.mul_mem (M.mul_mem hkM hhM) (M.inv_mem hkM), mem_centralizer_iff.2 fun x hx => ?_⟩
    have hx' : k⁻¹ * x * k ∈ O2In M := by
      simpa using (mem_normalizer_iff.1 (mem_normalizer_O2In (M.inv_mem hkM)) x).1 hx
    have hc : (k⁻¹ * x * k) * h = h * (k⁻¹ * x * k) := mem_centralizer_iff.1 hhC _ hx'
    calc x * (k * h * k⁻¹) = k * ((k⁻¹ * x * k) * h) * k⁻¹ := by group
      _ = k * (h * (k⁻¹ * x * k)) * k⁻¹ := by rw [hc]
      _ = (k * h * k⁻¹) * x := by group
  exact le_O2In hCM hCn hC2

end CFSG.EvenSporadicStandard.TwoB
