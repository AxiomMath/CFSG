module

public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.ClassicalInvolution.Generic.Induction
import CFSG.ClassicalInvolution.Balance.TheoremQNormalizer
import CFSG.ClassicalInvolution.Generic.InductionLocal
import CFSG.ClassicalInvolution.Generic.StepOdd

public section

namespace CFSG.ClassicalInvolution.Generic.DeltaClosure

open CFSG.Open CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Balance (oddCoreIn)

section Members

variable {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y]

theorem sq_eq_one {L : Subgroup Y} {z : Y} (h : IsClassicalMember p f L z) : z * z = 1 := by
  rw [← pow_two]
  exact orderOf_dvd_iff_pow_eq_one.mp (by rw [h.orderOf_eq_two])

theorem comm_of_mem {L : Subgroup Y} {z : Y} (h : IsClassicalMember p f L z) {k : Y}
    (hk : k ∈ L) : z * k = k * z :=
  (Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h.subnormal hk)).symm

theorem le_centralizer {L : Subgroup Y} {z : Y} (h : IsClassicalMember p f L z) :
    L ≤ Subgroup.centralizer ({z} : Set Y) := isSubnormal_le h.subnormal

theorem eq_one_of_mem_of_odd_of_sq {X : Type*} [Group X] {N : Subgroup X} (hN : Odd (Nat.card N))
    {x : X} (hx : x ∈ N) (hsq : x * x = 1) : x = 1 := by
  have h1 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have h3 : orderOf x ∣ Nat.gcd 2 (Nat.card N) := Nat.dvd_gcd h2 h1
  have h4 : Nat.gcd 2 (Nat.card N) = 1 := (Nat.coprime_two_left.mpr hN).gcd_eq_one
  rw [h4] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem involution_unique [Finite Y] (hodd : Odd (Nat.card (GaloisField p f))) {L : Subgroup Y}
    {z z' : Y} (h : IsClassicalMember p f L z) (h' : IsClassicalMember p f L z') : z = z' := by
  obtain ⟨e⟩ := h.nonempty_equiv
  have hfin : Finite (GaloisField p f) := Nat.finite_of_card_ne_zero (by
    intro h0
    rw [h0] at hodd
    exact absurd hodd (by decide))
  set zL : L := ⟨z, h.mem⟩ with hzL
  set zL' : L := ⟨z', h'.mem⟩ with hzL'
  have o1 : orderOf zL = 2 := by rw [Subgroup.orderOf_mk]; exact h.orderOf_eq_two
  have o2 : orderOf zL' = 2 := by rw [Subgroup.orderOf_mk]; exact h'.orderOf_eq_two
  have e1 : e (QuotientGroup.mk' (classicalInvolutionOddCore L) zL) = -1 :=
    (sl2_orderOf_eq_two_iff hodd _).mp (by
      rw [MulEquiv.orderOf_eq e]
      exact orderOf_mk_oddCore_eq_two o1)
  have e2 : e (QuotientGroup.mk' (classicalInvolutionOddCore L) zL') = -1 :=
    (sl2_orderOf_eq_two_iff hodd _).mp (by
      rw [MulEquiv.orderOf_eq e]
      exact orderOf_mk_oddCore_eq_two o2)
  have hmk : QuotientGroup.mk' (classicalInvolutionOddCore L) zL =
      QuotientGroup.mk' (classicalInvolutionOddCore L) zL' := e.injective (e1.trans e2.symm)
  have hmem : zL⁻¹ * zL' ∈ classicalInvolutionOddCore L := QuotientGroup.eq.mp hmk
  have hz1 : zL * zL = 1 := Subtype.ext (sq_eq_one h)
  have hz2 : zL' * zL' = 1 := Subtype.ext (sq_eq_one h')
  have hcomm : zL * zL' = zL' * zL := Subtype.ext (comm_of_mem h h'.mem)
  have hinv : zL⁻¹ = zL := inv_eq_of_mul_eq_one_right hz1
  rw [hinv] at hmem
  have hsq : (zL * zL') * (zL * zL') = 1 := by
    calc (zL * zL') * (zL * zL') = zL * (zL' * zL) * zL' := by group
      _ = zL * (zL * zL') * zL' := by rw [← hcomm]
      _ = (zL * zL) * (zL' * zL') := by group
      _ = 1 := by rw [hz1, hz2, one_mul]
  have hodd' : Odd (Nat.card (classicalInvolutionOddCore L)) :=
    CFSG.ComponentClassification.OddCore.odd_card L
  have h3 : zL * zL' = 1 := eq_one_of_mem_of_odd_of_sq hodd' hmem hsq
  have h4 : z * z' = 1 := congrArg Subtype.val h3
  calc z = z * (z' * z') := by rw [sq_eq_one h', mul_one]
    _ = (z * z') * z' := (mul_assoc _ _ _).symm
    _ = z' := by rw [h4, one_mul]

end Members

section Conjugacy

variable {G : Type*} [Group G]

theorem exists_conj_of_mul_mem {u z : G} (hu : u * u = 1) (hz : z * z = 1) {N : Subgroup G}
    (hN : Odd (Nat.card N)) (hn : z * u ∈ N) : ∃ o ∈ N, z = o * u * o⁻¹ := by
  set n : G := z * u with hn_def
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hm : Odd (orderOf n) := hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hn)
  obtain ⟨r, hr⟩ := hm
  have hunu : u * n * u⁻¹ = n⁻¹ := by
    have h1 : n⁻¹ = u * z := by rw [hn_def, mul_inv_rev, hu', hz']
    rw [h1, hn_def, hu']
    calc u * (z * u) * u = u * z * (u * u) := by group
      _ = u * z := by rw [hu, mul_one]
  have hpow : u * n ^ (r + 1) * u⁻¹ = (n ^ (r + 1))⁻¹ := by
    have := map_pow (MulAut.conj u) n (r + 1)
    simp only [MulAut.conj_apply] at this
    rw [this, hunu, inv_pow]
  have hpow' : u * (n ^ (r + 1))⁻¹ * u⁻¹ = n ^ (r + 1) := by
    have : u * (n ^ (r + 1))⁻¹ * u⁻¹ = (u * n ^ (r + 1) * u⁻¹)⁻¹ := by group
    rw [this, hpow, inv_inv]
  have hsq : n ^ (r + 1) * n ^ (r + 1) = n := by
    have h1 : n ^ (2 * r + 1) = 1 := by rw [← hr]; exact pow_orderOf_eq_one n
    calc n ^ (r + 1) * n ^ (r + 1) = n ^ (2 * r + 1) * n := by
          rw [← pow_add, ← pow_succ]
          congr 1
          omega
      _ = n := by rw [h1, one_mul]
  have hzn : z = n * u := by rw [hn_def, mul_assoc, hu, mul_one]
  refine ⟨n ^ (r + 1), N.pow_mem hn (r + 1), ?_⟩
  calc z = n * u := hzn
    _ = (n ^ (r + 1) * n ^ (r + 1)) * u := by rw [hsq]
    _ = n ^ (r + 1) * (u * (n ^ (r + 1))⁻¹ * u⁻¹) * u := by rw [hpow']
    _ = n ^ (r + 1) * u * (n ^ (r + 1))⁻¹ := by group

end Conjugacy

section Layer

variable {G : Type} [Group G]

theorem conjSub_mem_centralizingMembers {Λ : Set (Subgroup G)} (hΛ : ConjInvariant Λ) {A : Set G}
    {n : G} (hn : n ∈ Subgroup.centralizer A) {L : Subgroup G} (hL : L ∈ centralizingMembers Λ A) :
    conjSub n L ∈ centralizingMembers Λ A := by
  refine ⟨hΛ n L hL.1, fun x hx => ?_⟩
  rw [mem_conjSub_iff] at hx
  have hx' := hL.2 hx
  have : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hx') ((Subgroup.inv_mem _) hn)

theorem conj_mem_centralizingLayer {Λ : Set (Subgroup G)} (hΛ : ConjInvariant Λ) {A : Set G}
    {n : G} (hn : n ∈ Subgroup.centralizer A) {y : G} (hy : y ∈ centralizingLayer Λ A) :
    n * y * n⁻¹ ∈ centralizingLayer Λ A := by
  have key : centralizingLayer Λ A ≤
      (centralizingLayer Λ A).comap (MulAut.conj n).toMonoidHom := by
    refine iSup₂_le fun L hL x hx => ?_
    exact le_centralizingLayer (conjSub_mem_centralizingMembers hΛ hn hL) (conj_mem_conjSub hx)
  exact key hy

theorem mem_normalizer_centralizingLayer {Λ : Set (Subgroup G)} (hΛ : ConjInvariant Λ) {A : Set G}
    {n : G} (hn : n ∈ Subgroup.centralizer A) :
    n ∈ Subgroup.normalizer (centralizingLayer Λ A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_centralizingLayer hΛ hn hy, fun hy => ?_⟩
  have := conj_mem_centralizingLayer hΛ ((Subgroup.centralizer A).inv_mem hn) hy
  simpa [mul_assoc] using this

theorem mem_normalizer_oddCoreIn_centralizingLayer [Finite G] {Λ : Set (Subgroup G)}
    (hΛ : ConjInvariant Λ) {A : Set G} {n : G} (hn : n ∈ Subgroup.centralizer A) :
    n ∈ Subgroup.normalizer (oddCoreIn (centralizingLayer Λ A) : Set G) :=
  CFSG.ClassicalInvolution.Balance.mem_normalizer_oddCoreIn_of_mem_normalizer
    (mem_normalizer_centralizingLayer hΛ hn)

end Layer

section ModOdd

variable {G : Type} [Group G]

@[expose] def modOddIn (Y L : Subgroup G) : Subgroup (↥Y ⧸ classicalInvolutionOddCore ↥Y) :=
  (L.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y))

theorem mk_comm_eq_iff {Y : Subgroup G} {x y : G} (hx : x ∈ Y) (hy : y ∈ Y) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨x, hx⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨y, hy⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨y, hy⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨x, hx⟩ ↔
      x * y * x⁻¹ * y⁻¹ ∈ oddCoreIn Y := by
  rw [← map_mul, ← map_mul]
  change ((⟨x, hx⟩ * ⟨y, hy⟩ : ↥Y) : ↥Y ⧸ classicalInvolutionOddCore ↥Y) =
    ((⟨y, hy⟩ * ⟨x, hx⟩ : ↥Y) : ↥Y ⧸ classicalInvolutionOddCore ↥Y) ↔ _
  rw [QuotientGroup.eq_iff_div_mem]
  have hc : (((⟨x, hx⟩ * ⟨y, hy⟩ : ↥Y) / (⟨y, hy⟩ * ⟨x, hx⟩ : ↥Y) : ↥Y) : G) =
      x * y * x⁻¹ * y⁻¹ := by
    rw [div_eq_mul_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
    group
  constructor
  · intro h
    exact ⟨_, h, hc⟩
  · rintro ⟨w, hw, hwe⟩
    have : w = (⟨x, hx⟩ * ⟨y, hy⟩ : ↥Y) / (⟨y, hy⟩ * ⟨x, hx⟩ : ↥Y) :=
      Subtype.ext ((hwe : (w : G) = _).trans hc.symm)
    rwa [this] at hw

variable {p f : ℕ} [Fact p.Prime]

theorem mul_mem_oddCoreIn_of_modOddIn_eq [Finite G] (hodd : Odd (Nat.card (GaloisField p f)))
    {Y K K' : Subgroup G} {z z' : G} (hK : IsClassicalMember p f K z)
    (hK' : IsClassicalMember p f K' z') (hKY : K ≤ Y) (hK'Y : K' ≤ Y)
    (h : modOddIn Y K = modOddIn Y K') : z * z' ∈ oddCoreIn Y := by
  have h1 := (hK.subgroupOf p f hKY).map_oddQuotient
  have h2 := (hK'.subgroupOf p f hK'Y).map_oddQuotient
  unfold modOddIn at h
  rw [← h] at h2
  have h3 := involution_unique hodd h1 h2
  have h4 := QuotientGroup.eq.mp h3
  refine ⟨_, h4, ?_⟩
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right (sq_eq_one hK)
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hz]

end ModOdd

end CFSG.ClassicalInvolution.Generic.DeltaClosure
