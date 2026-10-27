module

public import CFSG.GH74.GLS.C3.Layer1.Back91Setup
public import CFSG.GH74.GLS.C3.Layer1.BackConj
public import CFSG.GH74.GLS.C3.Layer1.Back93

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

namespace Aux113E

variable {G : Type} [Group G]

theorem exists_noncomm_of_equiv_A5 {H : Type*} [Group H] (e : H ≃* alternatingGroup (Fin 5)) :
    ∃ a b : H, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hc : IsMulCommutative (alternatingGroup (Fin 5)) := ⟨⟨fun a b => by
    have h := congrArg e (hcon (e.symm a) (e.symm b))
    simpa using h⟩⟩
  have h3 := alternatingGroup.isMulCommutative_iff_card_le_three.1 hc
  simp at h3

theorem factorization_sixty : (60 : ℕ).factorization 2 = 2 := by
  have h : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem factorization_two_card_of_equiv_A5 [Finite G] {K : Subgroup G}
    (e : kBar K ≃* alternatingGroup (Fin 5)) :
    (Nat.card ↥K).factorization 2 = 2 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)
  have h2 : Nat.card (kBar K) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
  have hne : Nat.card (pPrimeCore 2 ↥K) ≠ 0 := Nat.card_pos.ne'
  have h3 : Nat.card ↥K = 60 * Nat.card (pPrimeCore 2 ↥K) := by
    rw [h1]
    show Nat.card (kBar K) * _ = _
    rw [h2]
  rw [h3, Nat.factorization_mul (by norm_num) hne, Finsupp.add_apply, factorization_sixty,
    Setup91.factorization_two_of_odd hodd]

theorem comm_of_mem_sup {P Q : Subgroup G} (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p)
    (hQab : ∀ u ∈ Q, ∀ v ∈ Q, u * v = v * u) {q r : G} (hq : q ∈ Q) (hr : r ∈ P ⊔ Q) :
    q * r = r * q := by
  obtain ⟨p, hp, q', hq', rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hr
  calc q * (p * q') = (q * p) * q' := by group
    _ = (p * q) * q' := by rw [← hcomm p hp q hq]
    _ = p * (q * q') := by group
    _ = p * (q' * q) := by rw [hQab q hq q' hq']
    _ = p * q' * q := by group

section Hyp

variable {x : G} {K M T Q : Subgroup G}

theorem card_R_eq [Finite G] (hh : Hyp9A x K K M T Q) (e5 : kBar K ≃* alternatingGroup (Fin 5))
    (hQ4 : Nat.card ↥Q = 4) : Nat.card ↥((T ⊓ K) ⊔ Q) = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (kBar K) := e5.isSimpleGroup
  have hn := exists_noncomm_of_equiv_A5 e5
  have hP : Nat.card ↥(T ⊓ K) = 4 := by
    rw [(Setup91.inf_isSylowOf hh).card_eq, factorization_two_card_of_equiv_A5 e5]
    norm_num
  rw [Setup91.card_sup_Q hh hs hn, hP, hQ4]

theorem card_T_le [Finite G] (hh : Hyp9A x K K M T Q) (ψ₀ : ↥M →* Equiv.Perm (Fin 5))
    (hker : ψ₀.ker = (CMK M K).subgroupOf M) (hQ4 : Nat.card ↥Q = 4) : Nat.card ↥T ≤ 32 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : T ≤ M := hh.sylowTM.le
  set f : ↥T →* Equiv.Perm (Fin 5) := ψ₀.comp (Subgroup.inclusion hTM) with hf
  have hQeq : T ⊓ CMK M K = Q :=
    hh.sylowQ.eq_of_le (le_inf (Setup91.Q_le_T hh) hh.sylowQ.le) inf_le_right
      hh.sylowT.isPGroup.to_inf_left
  have hkerf : f.ker = Q.subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : ψ₀ (Subgroup.inclusion hTM t) = 1 ↔ (t : G) ∈ CMK M K := by
      rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
      rfl
    show ψ₀ (Subgroup.inclusion hTM t) = 1 ↔ _
    rw [h1]
    constructor
    · intro h
      rw [← hQeq]
      exact ⟨t.2, h⟩
    · intro h
      exact hh.sylowQ.le h
  have hcardker : Nat.card f.ker = 4 := by
    rw [hkerf, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Setup91.Q_le_T hh)).toEquiv, hQ4]
  have hrangeP : IsPGroup 2 f.range :=
    hh.sylowT.isPGroup.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hrangeP
  have hdvd : Nat.card f.range ∣ 120 := by
    have := Subgroup.card_subgroup_dvd_card f.range
    rwa [Nat.card_perm, Nat.card_fin] at this
  have hn3 : n ≤ 3 := by
    by_contra hcon
    push Not at hcon
    have h16 : 2 ^ 4 ∣ 2 ^ n := Nat.pow_dvd_pow 2 hcon
    rw [← hn] at h16
    have := h16.trans hdvd
    omega
  have h := Subgroup.index_mul_card f.ker
  rw [Subgroup.index_ker, hcardker, hn] at h
  have h8 : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
  omega

end Hyp

end Aux113E

theorem lemma113e {G : Type} [Group G] [Finite G] {x : G} {K L M T Q : Subgroup G}
    (hh : Hyp9A x K L M T Q) (hKL : K = L)
    (hQab : CFSG.IsElementaryAbelian 2 ↥Q) (hQ4 : Nat.card ↥Q = 4)
    (e5 : kBar K ≃* alternatingGroup (Fin 5))
    (ψ₀ : ↥M →* Equiv.Perm (Fin 5)) (hker : ψ₀.ker = (CMK M K).subgroupOf M)
    (h112 : (∀ q ∈ Q, ∀ t ∈ Subgroup.closure {u : G | u ∈ T ∧ u * u = 1}, q * t = t * q) →
        (T ⊓ K) ⊔ Q = T ∧ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (hnot : ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) :
    ∃ y ∈ T, orderOf y = 2 ∧ T = (T ⊓ K) ⊔ Q ⊔ Subgroup.zpowers y ∧ ∃ q ∈ Q, y * q ≠ q * y := by
  subst hKL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR16 := Aux113E.card_R_eq hh e5 hQ4
  have hTle := Aux113E.card_T_le hh ψ₀ hker hQ4
  have hRT : (T ⊓ K) ⊔ Q ≤ T := sup_le inf_le_left (Setup91.Q_le_T hh)
  have hQabel := (forall_of_isElementaryAbelian hQab).1
  have hcommPQ : ∀ p ∈ T ⊓ K, ∀ q ∈ Q, p * q = q * p := fun p hp q hq =>
    Setup91.comm_inf_Q hh hp hq
  have hQR : ∀ q ∈ Q, ∀ r ∈ (T ⊓ K) ⊔ Q, q * r = r * q := fun q hq r hr =>
    Aux113E.comm_of_mem_sup hcommPQ hQabel hq hr
  have hkey : (∀ q ∈ Q, ∀ t ∈ Subgroup.closure {u : G | u ∈ T ∧ u * u = 1}, q * t = t * q) →
      False := fun h => hnot (h112 h).2
  obtain ⟨y, hyT, hyy, hyR⟩ : ∃ y ∈ T, y * y = 1 ∧ y ∉ (T ⊓ K) ⊔ Q := by
    by_contra hno
    push Not at hno
    refine hkey fun q hq t ht => ?_
    have hcl : Subgroup.closure {u : G | u ∈ T ∧ u * u = 1} ≤ (T ⊓ K) ⊔ Q := by
      rw [Subgroup.closure_le]
      intro u hu
      exact hno u hu.1 hu.2
    exact hQR q hq t (hcl ht)
  have hy1 : y ≠ 1 := fun h => hyR (h ▸ Subgroup.one_mem _)
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by rwa [sq]) hy1
  have hT : T = (T ⊓ K) ⊔ Q ⊔ Subgroup.zpowers y := by
    have hle : (T ⊓ K) ⊔ Q ⊔ Subgroup.zpowers y ≤ T :=
      sup_le hRT (Subgroup.zpowers_le.2 hyT)
    have hdvd : Nat.card ↥((T ⊓ K) ⊔ Q) ∣ Nat.card ↥((T ⊓ K) ⊔ Q ⊔ Subgroup.zpowers y) :=
      Subgroup.card_dvd_of_le le_sup_left
    have hlt : Nat.card ↥((T ⊓ K) ⊔ Q) < Nat.card ↥((T ⊓ K) ⊔ Q ⊔ Subgroup.zpowers y) := by
      by_contra hcon
      push Not at hcon
      have heq := Subgroup.eq_of_le_of_card_ge
        (le_sup_left : (T ⊓ K) ⊔ Q ≤ (T ⊓ K) ⊔ Q ⊔ Subgroup.zpowers y) hcon
      have hy : y ∈ (T ⊓ K) ⊔ Q ⊔ Subgroup.zpowers y :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
      rw [← heq] at hy
      exact hyR hy
    have hle' : Nat.card ↥((T ⊓ K) ⊔ Q ⊔ Subgroup.zpowers y) ≤ Nat.card ↥T :=
      Subgroup.card_le_of_le hle
    rw [hR16] at hdvd hlt
    have hcard : Nat.card ↥T ≤ Nat.card ↥((T ⊓ K) ⊔ Q ⊔ Subgroup.zpowers y) := by omega
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  refine ⟨y, hyT, hy2, hT, ?_⟩
  by_contra hno
  push Not at hno
  refine hkey fun q hq t ht => ?_
  have hcl : Subgroup.closure {u : G | u ∈ T ∧ u * u = 1} ≤ T :=
    (Subgroup.closure_le T).2 fun u hu => hu.1
  have htT := hcl ht
  rw [hT] at htT
  have hC : (T ⊓ K) ⊔ Q ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({q} : Set G) := by
    refine sup_le (fun r hr => ?_) (Subgroup.zpowers_le.2 ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hQR q hq r hr).symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hno q hq)
  have hqt := Subgroup.mem_centralizer_singleton_iff.1 (hC htT)
  exact hqt.symm

end CFSG.GH74.GLS.C3.Layer1.Back
