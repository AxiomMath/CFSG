module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Witness
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open

namespace IsDoubleCoverA7

variable {E : Type*} [Group E] [Finite E] {π : E →* A7} {z : E}

theorem card_sylow (h : IsDoubleCoverA7 π z) (P : Sylow 2 E) : Nat.card P = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Sylow.card_eq_multiplicity, h.card_E, Nat.factorization_def _ Nat.prime_two]
  decide +kernel

theorem not_isCyclic_sylow (h : IsDoubleCoverA7 π z) (P : Sylow 2 E) :
    ¬ IsCyclic ↥(P : Subgroup E) := by
  intro hcyc
  have hmin : (Nat.card E).minFac = 2 := by
    rw [h.card_E]
    decide +kernel
  have hnorm := IsCyclic.normalizer_le_centralizer hmin hcyc
  have hcomp := IsCyclic.isComplement' hmin hcyc
  let f := MonoidHom.transferSylow P hnorm
  have hf := hom_trivial_of_perfect_of_commute h.perfect f (fun x y =>
    (IsMulCommutative.is_comm (M := ↥(P : Subgroup E))).comm (f x) (f y))
  have hker : f.ker = ⊤ := by
    ext x
    simp [hf x]
  have hcard := hcomp.card_mul_card
  rw [hker, Subgroup.card_top, h.card_sylow P, h.card_E] at hcard
  omega

end IsDoubleCoverA7

section Witness

variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}

theorem sylow_inf_oddCore_eq_one (Q : Sylow 2 ↥K) {x : ↥K} (hx : x ∈ (Q : Subgroup ↥K))
    (hxN : x ∈ classicalInvolutionOddCore ↥K) : x = 1 := by
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥K)) := odd_card_oddCore K
  have h1 : orderOf x ∣ Nat.card (classicalInvolutionOddCore ↥K) :=
    Subgroup.orderOf_dvd_natCard _ hxN
  have h2 : orderOf x ∣ Nat.card Q := Subgroup.orderOf_dvd_natCard (Q : Subgroup ↥K) hx
  obtain ⟨k, hk⟩ := Q.isPGroup'.exists_card_eq
  rw [hk] at h2
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  by_cases hm0 : m = 0
  · rw [hm0, pow_zero, orderOf_eq_one_iff] at hm
    exact hm
  · exfalso
    have h4 : 2 ∣ orderOf x := by rw [hm]; exact dvd_pow_self 2 hm0
    exact absurd (hN.of_dvd_nat (h4.trans h1)) (by decide)

theorem card_sylow_of_witness (hw : A7Witness K) (Q : Sylow 2 ↥K) : Nat.card Q = 16 := by
  obtain ⟨π, zE, hcov, -⟩ := exists_cover_of_witness hw
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥K := classicalInvolutionOddCore ↥K with hNdef
  have hf : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have h16 := hcov.card_sylow (Q.mapSurjective hf)
  rw [Sylow.coe_mapSurjective] at h16
  let f : (Q : Subgroup ↥K) →* OddQuot K := (QuotientGroup.mk' N).domRestrict (Q : Subgroup ↥K)
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : ↥K) ∈ N := (QuotientGroup.eq_one_iff (x : ↥K)).mp hx
    exact Subtype.ext (sylow_inf_oddCore_eq_one Q x.2 hxN)
  have hrange : f.range = Q.map (QuotientGroup.mk' N) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hrange] at h16
  rw [← h16]
  exact Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv

theorem exists_quaternion_sylow_of_witness (hw : A7Witness K) (Q : Sylow 2 ↥K) :
    ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((Q : Subgroup ↥K) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  obtain ⟨π, zE, hcov, -⟩ := exists_cover_of_witness hw
  set N : Subgroup ↥K := classicalInvolutionOddCore ↥K with hNdef
  have hN : Odd (Nat.card N) := odd_card_oddCore K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have hQN : ∀ x ∈ (Q : Subgroup ↥K), (QuotientGroup.mk' N) x = 1 → x = 1 := fun x hx hx1 =>
    sylow_inf_oddCore_eq_one Q hx ((QuotientGroup.eq_one_iff x).mp hx1)
  have hnc : ¬ IsCyclic ↥(Q : Subgroup ↥K) := by
    intro hcyc
    have hsurj : Function.Surjective
        (((QuotientGroup.mk' N).domRestrict (Q : Subgroup ↥K)).codRestrict
          (Q.map (QuotientGroup.mk' N)) (fun x => Subgroup.mem_map_of_mem _ x.2)) := by
      intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    have hcyc' : IsCyclic ↥(Q.map (QuotientGroup.mk' N)) := isCyclic_of_surjective _ hsurj
    have hS := hcov.not_isCyclic_sylow (Q.mapSurjective hf)
    rw [Sylow.coe_mapSurjective] at hS
    exact hS hcyc'
  have hinv : ∀ x y : ↥K, x ∈ (Q : Subgroup ↥K) → y ∈ (Q : Subgroup ↥K) → orderOf x = 2 →
      orderOf y = 2 → x = y := by
    intro x y hx hy hxo hyo
    have hx2 : x * x = 1 := by
      have := pow_orderOf_eq_one x; rwa [hxo, pow_two] at this
    have hy2 : y * y = 1 := by
      have := pow_orderOf_eq_one y; rwa [hyo, pow_two] at this
    have hx1 : (QuotientGroup.mk' N) x ≠ 1 := fun h1 => by
      have := hQN x hx h1
      rw [this, orderOf_one] at hxo
      omega
    have hy1 : (QuotientGroup.mk' N) y ≠ 1 := fun h1 => by
      have := hQN y hy h1
      rw [this, orderOf_one] at hyo
      omega
    have hxz : (QuotientGroup.mk' N) x = zE := by
      rcases hcov.eq_one_or_eq_z_of_sq_eq_one (w := (QuotientGroup.mk' N) x)
        (by rw [← map_mul, hx2, map_one]) with h1 | h1
      · exact absurd h1 hx1
      · exact h1
    have hyz : (QuotientGroup.mk' N) y = zE := by
      rcases hcov.eq_one_or_eq_z_of_sq_eq_one (w := (QuotientGroup.mk' N) y)
        (by rw [← map_mul, hy2, map_one]) with h1 | h1
      · exact absurd h1 hy1
      · exact h1
    have : (QuotientGroup.mk' N) (x⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hxz, hyz, inv_mul_cancel]
    have h5 := hQN (x⁻¹ * y) ((Q : Subgroup ↥K).mul_mem ((Q : Subgroup ↥K).inv_mem hx) hy) this
    exact (inv_mul_eq_one.mp h5)
  have hdvd : 2 ∣ Nat.card (Q : Subgroup ↥K) := by
    by_contra hnd
    apply hnc
    obtain ⟨k, hk⟩ := Q.isPGroup'.exists_card_eq
    have hk0 : k = 0 := by
      by_contra hk0
      exact hnd (by rw [hk]; exact dvd_pow_self 2 hk0)
    rw [hk0, pow_zero] at hk
    exact @isCyclic_of_subsingleton _ _ (Nat.card_eq_one_iff_unique.mp hk).1
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := (Q : Subgroup ↥K)) 2 hdvd
  have hx₀' : orderOf ((x₀ : ↥(Q : Subgroup ↥K)) : ↥K) = 2 := by
    rw [Subgroup.orderOf_coe]; exact hx₀
  have hunique : ∃ U : Subgroup ↥(Q : Subgroup ↥K), Nat.card U = 2 ∧
      ∀ V : Subgroup ↥(Q : Subgroup ↥K), Nat.card V = 2 → V = U := by
    refine ⟨Subgroup.zpowers x₀, by rw [Nat.card_zpowers, hx₀], fun V hV => ?_⟩
    have hv2 : 2 ∣ Nat.card V := by rw [hV]
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := V) 2 hv2
    have hvo : orderOf (((v : ↥(Q : Subgroup ↥K)) : ↥K)) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hv
    have hvx : (v : ↥(Q : Subgroup ↥K)) = x₀ :=
      Subtype.ext (hinv _ _ (v : ↥(Q : Subgroup ↥K)).2 x₀.2 hvo hx₀')
    have hle : Subgroup.zpowers (v : ↥(Q : Subgroup ↥K)) ≤ V := by
      rw [Subgroup.zpowers_le]; exact v.2
    have hc1 : Nat.card (Subgroup.zpowers (v : ↥(Q : Subgroup ↥K))) = 2 := by
      rw [Nat.card_zpowers]
      rw [Subgroup.orderOf_coe]; exact hv
    rw [hvx] at hle hc1
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hc1, hV])).symm
  rcases (CFSG.BenderSuzuki.External.huppert_III_8_2_pgroup_unique_order_prime_subgroup
    Nat.prime_two Q.isPGroup' hunique).2 rfl with hcyc | hq
  · exact absurd hcyc hnc
  · exact hq

theorem exists_orderOf_eight_of_witness (hw : A7Witness K) (Q : Sylow 2 ↥K) :
    ∃ x ∈ (Q : Subgroup ↥K), orderOf x = 8 := by
  obtain ⟨r, hr, ⟨e⟩⟩ := exists_quaternion_sylow_of_witness hw Q
  have hcard := card_sylow_of_witness hw Q
  have hne : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have h1 : Nat.card (QuaternionGroup (2 ^ (r - 2))) = 4 * 2 ^ (r - 2) := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [Nat.card_congr e.toEquiv, h1] at hcard
  have h2 : 2 ^ (r - 2) = 4 := by omega
  refine ⟨e.symm (QuaternionGroup.a 1), (e.symm (QuaternionGroup.a 1)).2, ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  have := QuaternionGroup.orderOf_a_one (n := 2 ^ (r - 2))
  rw [this, h2]

end Witness

end CFSG.ClassicalInvolution.Hat2A7
