module

public import CFSG.ClassicalInvolution.Q3.Basic
public import CFSG.ClassicalInvolution.Q3.Subnormal

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inf_eq_bot_of_exact {J H N : Subgroup G} (hJH : J ≤ H)
    (hN : H ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N))
    (hex : classicalInvolutionOddCore ↥J = ⊥) : J ⊓ N = ⊥ := by
  have hSodd : Odd (Nat.card ↥(J ⊓ N)) :=
    hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hnorm : J ≤ Subgroup.normalizer ((J ⊓ N : Subgroup G) : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hu' := (Subgroup.mem_normalizer_iff.mp (hN (hJH hu)) y)
    constructor
    · rintro ⟨hyJ, hyN⟩
      exact ⟨J.mul_mem (J.mul_mem hu hyJ) (J.inv_mem hu), hu'.mp hyN⟩
    · rintro ⟨hyJ, hyN⟩
      refine ⟨?_, hu'.mpr hyN⟩
      have := J.mul_mem (J.mul_mem (J.inv_mem hu) hyJ) hu
      simpa [mul_assoc] using this
  have h1 : J ⊓ N ≤ oddCoreIn J := le_oddCoreIn_of_normalizes inf_le_left hnorm hSodd
  have hex' : componentClassificationOddCore ↥J = ⊥ := hex
  have h2 : oddCoreIn J = ⊥ := by rw [oddCoreIn, hex', Subgroup.map_bot]
  rw [h2] at h1
  exact le_bot_iff.mp h1

theorem le_centralizer_of_exact {p : ℕ} (hp : p.Prime) {J H N P : Subgroup G}
    (hJ : IsSubnormal J H) (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hodd : Odd (Nat.card N)) (hcop : ¬ p ∣ Nat.card N)
    (hex : classicalInvolutionOddCore ↥J = ⊥) (hPJ : P ≤ J) (hP : IsPGroup p P) :
    P ≤ Subgroup.centralizer (N : Set G) := by
  have hN : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  have h1 := commutator_le_inf_of_isSubnormal hp hJ hNH hN hcop hPJ hP
  rw [inf_eq_bot_of_exact (isSubnormal_le hJ) hHN hodd hex, le_bot_iff] at h1
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact h1

theorem le_centralizer_of_exact_two {J H N P : Subgroup G} (hJ : IsSubnormal J H) (hNH : N ≤ H)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N))
    (hex : classicalInvolutionOddCore ↥J = ⊥) (hPJ : P ≤ J) (hP : IsPGroup 2 P) :
    P ≤ Subgroup.centralizer (N : Set G) :=
  le_centralizer_of_exact Nat.prime_two hJ hNH hHN hodd
    (fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)) hex hPJ hP

theorem exists_sup_eq_of_card_eq_twentyFour {J : Subgroup G} (h24 : Nat.card J = 24) :
    ∃ Q R : Subgroup G, Q ≤ J ∧ R ≤ J ∧ Nat.card Q = 2 ^ 3 ∧ Nat.card R = 3 ^ 1 ∧ Q ⊔ R = J := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q', hQ'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥J) 2
    (show 2 ^ 3 ∣ Nat.card ↥J by rw [h24]; norm_num)
  obtain ⟨R', hR'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥J) 3
    (show 3 ^ 1 ∣ Nat.card ↥J by rw [h24]; norm_num)
  set Q : Subgroup G := Q'.map J.subtype with hQ
  set R : Subgroup G := R'.map J.subtype with hR
  have hQJ : Q ≤ J := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hRJ : R ≤ J := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hQc : Nat.card Q = 2 ^ 3 := by
    rw [hQ, Subgroup.card_map_of_injective J.subtype_injective, hQ']
  have hRc : Nat.card R = 3 ^ 1 := by
    rw [hR, Subgroup.card_map_of_injective J.subtype_injective, hR']
  refine ⟨Q, R, hQJ, hRJ, hQc, hRc, ?_⟩
  have hd8 : 8 ∣ Nat.card ↥(Q ⊔ R) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : Q ≤ Q ⊔ R)
    rwa [hQc] at this
  have hd3 : 3 ∣ Nat.card ↥(Q ⊔ R) := by
    have := Subgroup.card_dvd_of_le (le_sup_right : R ≤ Q ⊔ R)
    rwa [hRc] at this
  have hd24 : 24 ∣ Nat.card ↥(Q ⊔ R) := by
    have : Nat.Coprime 8 3 := by norm_num
    simpa using this.mul_dvd_of_dvd_of_dvd hd8 hd3
  have hle : Q ⊔ R ≤ J := sup_le hQJ hRJ
  have hpos : 0 < Nat.card ↥(Q ⊔ R) := Nat.card_pos
  have hlt : Nat.card ↥(Q ⊔ R) ≤ 24 := h24 ▸ Subgroup.card_le_of_le hle
  have heq : Nat.card ↥(Q ⊔ R) = 24 := by
    obtain ⟨k, hk⟩ := hd24
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h24, heq])

theorem le_centralizer_of_exact_of_not_three_dvd {J H N : Subgroup G} (hJ : IsSubnormal J H)
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N))
    (h3 : ¬ 3 ∣ Nat.card N) (hex : classicalInvolutionOddCore ↥J = ⊥)
    (h24 : Nat.card J = 24) : J ≤ Subgroup.centralizer (N : Set G) := by
  obtain ⟨Q, R, hQJ, hRJ, hQc, hRc, hQR⟩ := exists_sup_eq_of_card_eq_twentyFour h24
  have hQ : IsPGroup 2 Q := IsPGroup.of_card hQc
  have hR : IsPGroup 3 R := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact IsPGroup.of_card hRc
  have hQC := le_centralizer_of_exact_two hJ hNH hHN hodd hex hQJ hQ
  have hRC := le_centralizer_of_exact Nat.prime_three hJ hNH hHN hodd h3 hex hRJ hR
  rw [← hQR]
  exact sup_le hQC hRC

omit [Finite G] in
theorem IsClassicalMember3.natCard_eq_of_exact {J : Subgroup G} {z : G}
    (h : IsClassicalMember3 J z) (hex : classicalInvolutionOddCore ↥J = ⊥) :
    Nat.card J = 24 := by
  obtain ⟨e⟩ := h.nonempty_equiv_sl2 hex
  rw [Nat.card_congr e.toEquiv, natCard_sl2Three]

theorem IsClassicalMember3.le_centralizer_oddCoreIn_of_centralizes {J : Subgroup G} {z x : G}
    (hz : IsClassicalMember3 J z) (hex : classicalInvolutionOddCore ↥J = ⊥)
    (hJx : J ≤ Subgroup.centralizer ({x} : Set G))
    (hzN : oddCoreIn (Subgroup.centralizer ({x} : Set G)) ≤
      Subgroup.centralizer ({z} : Set G)) :
    (∀ P : Subgroup G, P ≤ J → IsPGroup 2 P →
        P ≤ Subgroup.centralizer (oddCoreIn (Subgroup.centralizer ({x} : Set G)) : Set G)) ∧
      (¬ 3 ∣ Nat.card (oddCoreIn (Subgroup.centralizer ({x} : Set G))) →
        J ≤ Subgroup.centralizer (oddCoreIn (Subgroup.centralizer ({x} : Set G)) : Set G)) := by
  set N : Subgroup G := oddCoreIn (Subgroup.centralizer ({x} : Set G)) with hN
  set H : Subgroup G := Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)
    with hH
  have hJH : IsSubnormal J H := by
    have := isSubnormal_inf hz.subnormal (Subgroup.centralizer ({x} : Set G))
    rwa [inf_eq_left.mpr hJx] at this
  have hNH : N ≤ H := le_inf hzN (oddCoreIn_le _)
  have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
    inf_le_right.trans (normalizer_oddCoreIn _)
  have hodd : Odd (Nat.card N) := odd_card_oddCoreIn _
  refine ⟨fun P hPJ hP => le_centralizer_of_exact_two hJH hNH hHN hodd hex hPJ hP, fun h3 => ?_⟩
  exact le_centralizer_of_exact_of_not_three_dvd hJH hNH hHN hodd h3 hex
    (hz.natCard_eq_of_exact hex)

end CFSG.ClassicalInvolution.Q3
