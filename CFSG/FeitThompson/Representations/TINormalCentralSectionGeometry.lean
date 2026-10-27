module

public import Mathlib.GroupTheory.Sylow
public import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
public import CFSG.FeitThompson.Definitions.TISubsetWithItsExactNormalizer
import CFSG.FeitThompson.Foundations.OrbitStabilizerIndex

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open MulAction Pointwise Subgroup

variable {G : Type*} [Group G] {p : ℕ} {P : Sylow p G} {L Z : Subgroup G} {h : ℕ}

structure IsTINormalCentralSection (p : ℕ) (P : Sylow p G) (L Z : Subgroup G) (h : ℕ) :
    Prop where
  prime : p.Prime
  sylow_ne_bot : (P : Subgroup G) ≠ ⊥
  normalizer_eq : Subgroup.normalizer ((P : Subgroup G) : Set G) = L
  odd_natCard : Odd (Nat.card L)
  ti : ∀ g ∉ L, (((P : Subgroup G) : Set G) \ {1}) ∩
      ((fun x => g⁻¹ * x * g) '' (((P : Subgroup G) : Set G) \ {1})) = ∅
  Z_ne_bot : Z ≠ ⊥
  Z_le_center : Z ≤ (P : Subgroup G) ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G)
  le_normalizer_Z : L ≤ Subgroup.normalizer (Z : Set G)
  natCard_centralizer_inf_eq : ∀ z ∈ Z, z ≠ 1 →
    Nat.card (L ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) = h

theorem conj_pow_of_conj_eq_inv {g z : G} (hgz : g * z * g⁻¹ = z⁻¹) (k : ℕ) :
    g ^ k * z * (g ^ k)⁻¹ = z ^ ((-1 : ℤ) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hz : z ^ ((-1 : ℤ) ^ (k + 1)) = (z ^ ((-1 : ℤ) ^ k))⁻¹ := by
      rw [pow_succ, zpow_mul, zpow_neg_one]
    rw [hz, pow_succ]
    calc g ^ k * g * z * (g ^ k * g)⁻¹
        = g ^ k * (g * z * g⁻¹) * (g ^ k)⁻¹ := by group
      _ = g ^ k * z⁻¹ * (g ^ k)⁻¹ := by rw [hgz]
      _ = (g ^ k * z * (g ^ k)⁻¹)⁻¹ := by group
      _ = (z ^ ((-1 : ℤ) ^ k))⁻¹ := by rw [ih]

theorem eq_one_of_conj_eq_inv_of_odd {g z : G} {m : ℕ} (hgz : g * z * g⁻¹ = z⁻¹) (hm : Odd m)
    (hg : g ^ m = 1) (hz : Odd (orderOf z)) : z = 1 := by
  have hkey := conj_pow_of_conj_eq_inv hgz m
  rw [hg, hm.neg_one_pow, one_mul, inv_one, mul_one, zpow_neg, zpow_one] at hkey
  have h2 : z ^ 2 = 1 := by rw [pow_two]; exact mul_eq_one_iff_eq_inv.2 hkey
  rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h2) with h3 | h3
  · exact orderOf_eq_one_iff.1 h3
  · rw [h3] at hz; exact absurd hz (by decide)

theorem normalizer_sdiff_singleton_one (Q : Subgroup G) :
    Subgroup.normalizer ((Q : Set G) \ {1}) = Subgroup.normalizer (Q : Set G) := by
  ext g
  simp only [Subgroup.mem_set_normalizer_iff, Set.mem_sdiff, Set.mem_singleton_iff,
    SetLike.mem_coe]
  refine ⟨fun hg u => ?_, fun hg u =>
    ⟨fun hu => ⟨(hg u).1 hu.1, by simpa [conj_eq_one_iff] using hu.2⟩,
      fun hu => ⟨(hg u).2 hu.1, by simpa [conj_eq_one_iff] using hu.2⟩⟩⟩
  by_cases hu1 : u = 1
  · subst hu1; simp
  · exact ⟨fun hu => ((hg u).1 ⟨hu, hu1⟩).1,
      fun hu => ((hg u).2 ⟨hu, by simpa [conj_eq_one_iff] using hu1⟩).1⟩

theorem setOf_isConj_eq_orbit_conjAct (z : G) :
    {g : G | IsConj g z} = MulAction.orbit (ConjAct G) z := by
  ext g; simp [ConjAct.mem_orbit_conjAct]

theorem natCard_stabilizer_conjAct (z : G) :
    Nat.card (MulAction.stabilizer (ConjAct G) z) =
      Nat.card (Subgroup.centralizer ({z} : Set G)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv ConjAct.ofConjAct.toEquiv fun x => ?_)
  simp only [MulAction.mem_stabilizer_iff, ConjAct.smul_def,
    Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
  set c := ConjAct.ofConjAct x with hc
  refine ⟨fun hx => ?_, fun hx => by rw [hx, mul_assoc, mul_inv_cancel, mul_one]⟩
  calc c * z = c * z * c⁻¹ * c := by group
    _ = z * c := by rw [hx]

theorem natCard_setOf_isConj_mul_natCard_centralizer (z : G) :
    Nat.card {g : G | IsConj g z} * Nat.card (Subgroup.centralizer ({z} : Set G)) =
      Nat.card G := by
  rw [setOf_isConj_eq_orbit_conjAct, ← natCard_stabilizer_conjAct,
    natCard_orbit_mul_natCard_stabilizer]
  exact Nat.card_congr ConjAct.ofConjAct.toEquiv

theorem natCard_setOf_isConj_eq_index_centralizer [Finite G] (z : G) :
    Nat.card {g : G | IsConj g z} = (Subgroup.centralizer ({z} : Set G)).index := by
  refine Nat.eq_of_mul_eq_mul_right Nat.card_pos
    ((natCard_setOf_isConj_mul_natCard_centralizer z).trans ?_)
  rw [← Subgroup.card_mul_index (Subgroup.centralizer ({z} : Set G)), mul_comm]

namespace IsTINormalCentralSection

variable (hs : IsTINormalCentralSection p P L Z h) {z x y g : G}
include hs

theorem sylow_le : (P : Subgroup G) ≤ L := by
  rw [← hs.normalizer_eq]; exact Subgroup.le_normalizer

theorem Z_le_sylow : Z ≤ (P : Subgroup G) := hs.Z_le_center.trans inf_le_left

theorem Z_le : Z ≤ L := hs.Z_le_sylow.trans hs.sylow_le

theorem exists_mem_Z_ne_one : ∃ z ∈ Z, z ≠ 1 := by
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hs.Z_ne_bot
  exact ⟨w, w.2, by simpa using hw⟩

theorem sylow_le_centralizer (hz : z ∈ Z) :
    (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun u hu =>
  Subgroup.mem_centralizer_singleton_iff.2
    ((Subgroup.mem_centralizer_iff.1 (hs.Z_le_center hz).2) u hu)

theorem mem_of_conj_mem_sylow (hx : x ∈ (P : Subgroup G)) (hx1 : x ≠ 1)
    (hgx : g * x * g⁻¹ ∈ (P : Subgroup G)) : g ∈ L := by
  by_contra hg
  have hg' : g⁻¹ ∉ L := fun hc => hg (by simpa using inv_mem hc)
  have hti := hs.ti g⁻¹ hg'
  rw [Set.eq_empty_iff_forall_notMem] at hti
  refine hti (g * x * g⁻¹) ⟨⟨hgx, ?_⟩, ⟨x, ⟨hx, hx1⟩, by group⟩⟩
  simpa [conj_eq_one_iff] using hx1

theorem conj_mem_Z_of_conj_mem_sylow (hz : z ∈ Z) (hz1 : z ≠ 1)
    (hgz : g * z * g⁻¹ ∈ (P : Subgroup G)) : g ∈ L ∧ g * z * g⁻¹ ∈ Z := by
  have hgL : g ∈ L := hs.mem_of_conj_mem_sylow (hs.Z_le_sylow hz) hz1 hgz
  exact ⟨hgL, (Subgroup.mem_set_normalizer_iff.1 (hs.le_normalizer_Z hgL) z).1 hz⟩

theorem isTIWithNormalizer : IsTIWithNormalizer (((P : Subgroup G) : Set G) \ {1}) L where
  nonempty := by
    obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hs.sylow_ne_bot
    exact ⟨w, w.2, by simpa using hw⟩
  one_notMem := by simp
  normalizer_eq := by
    rw [normalizer_sdiff_singleton_one]; exact hs.normalizer_eq
  disjoint_conj_image g hg := by
    have hg' : g⁻¹ ∉ L := fun hc => hg (by simpa using inv_mem hc)
    have hkey : (fun x => (g⁻¹)⁻¹ * x * g⁻¹) '' (((P : Subgroup G) : Set G) \ {1}) =
        MulAut.conj g '' (((P : Subgroup G) : Set G) \ {1}) :=
      Set.image_congr' (fun x => by simp)
    rw [Set.disjoint_iff_inter_eq_empty, ← hkey]
    exact hs.ti g⁻¹ hg'

theorem centralizer_le (hz : z ∈ Z) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≤ L := by
  intro g hg
  refine (hs.conj_mem_Z_of_conj_mem_sylow hz hz1 ?_).1
  rw [Subgroup.mem_centralizer_singleton_iff.1 hg, mul_assoc, mul_inv_cancel, mul_one]
  exact hs.Z_le_sylow hz

theorem centralizer_eq_inf (hz : z ∈ Z) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) = L ⊓ Subgroup.centralizer ({z} : Set G) :=
  (inf_eq_right.2 (hs.centralizer_le hz hz1)).symm

theorem natCard_centralizer_eq (hz : z ∈ Z) (hz1 : z ≠ 1) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) = h := by
  rw [hs.centralizer_eq_inf hz hz1]
  exact hs.natCard_centralizer_inf_eq z hz hz1

theorem mem_Z_of_isConj_of_mem_sylow (hz : z ∈ Z) (hz1 : z ≠ 1) (hy : IsConj z y)
    (hyP : y ∈ (P : Subgroup G)) : y ∈ Z ∧ y ≠ 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hy
  refine ⟨hc ▸ (hs.conj_mem_Z_of_conj_mem_sylow hz hz1 (hc ▸ hyP)).2, ?_⟩
  rw [← hc]
  simpa [conj_eq_one_iff] using hz1

theorem odd_orderOf_of_mem_sylow (hx : x ∈ (P : Subgroup G)) : Odd (orderOf x) :=
  Odd.of_dvd_nat hs.odd_natCard (L.orderOf_dvd_natCard (hs.sylow_le hx))

theorem not_isConj_inv (hz : z ∈ Z) (hz1 : z ≠ 1) : ¬ IsConj z z⁻¹ := by
  rintro hconj
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hzP : z ∈ (P : Subgroup G) := hs.Z_le_sylow hz
  have hcL : c ∈ L := hs.mem_of_conj_mem_sylow hzP hz1 (hc ▸ (P : Subgroup G).inv_mem hzP)
  have hcpow : c ^ Nat.card L = 1 := orderOf_dvd_iff_pow_eq_one.1 (L.orderOf_dvd_natCard hcL)
  exact hz1 (eq_one_of_conj_eq_inv_of_odd hc hs.odd_natCard hcpow
    (hs.odd_orderOf_of_mem_sylow hzP))

theorem setOf_isConj_ne_inv_image (hz : z ∈ Z) (hz1 : z ≠ 1) :
    {g : G | IsConj g z} ≠ (fun u : G => u⁻¹) '' {g : G | IsConj g z} := by
  intro hEq
  have hmem : z⁻¹ ∈ (fun u : G => u⁻¹) '' {g : G | IsConj g z} :=
    ⟨z, IsConj.refl z, rfl⟩
  rw [← hEq] at hmem
  have hmem' : IsConj z⁻¹ z := hmem
  exact hs.not_isConj_inv hz hz1 hmem'.symm

theorem normal_subgroupOf : ((P : Subgroup G).subgroupOf L).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hs.sylow_le).2 (le_of_eq hs.normalizer_eq.symm)

theorem h_dvd_natCard : h ∣ Nat.card G := by
  obtain ⟨z, hz, hz1⟩ := hs.exists_mem_Z_ne_one
  rw [← hs.natCard_centralizer_eq hz hz1]
  exact Subgroup.card_subgroup_dvd_card _

section Finite
variable [Finite G]

theorem h_pos : 0 < h := by
  obtain ⟨z, hz, hz1⟩ := hs.exists_mem_Z_ne_one
  rw [← hs.natCard_centralizer_eq hz hz1]
  exact Nat.card_pos

theorem odd_prime : Odd p := by
  have : Fact p.Prime := ⟨hs.prime⟩
  have hne1 : Nat.card (P : Subgroup G) ≠ 1 := fun hc =>
    hs.sylow_ne_bot (Subgroup.card_eq_one.1 hc)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := (P : Subgroup G))).1 P.2
  have hn0 : n ≠ 0 := by rintro rfl; rw [pow_zero] at hn; exact hne1 hn
  exact Odd.of_dvd_nat hs.odd_natCard
    ((hn ▸ dvd_pow_self p hn0).trans (Subgroup.card_dvd_of_le hs.sylow_le))

theorem natCard_setOf_isConj_eq (hz : z ∈ Z) (hz1 : z ≠ 1) :
    Nat.card {g : G | IsConj g z} = Nat.card G / h := by
  refine (Nat.div_eq_of_eq_mul_left hs.h_pos ?_).symm
  rw [← hs.natCard_centralizer_eq hz hz1]
  exact (natCard_setOf_isConj_mul_natCard_centralizer z).symm

theorem n_pos : 0 < Nat.card G / h := by
  obtain ⟨z, hz, hz1⟩ := hs.exists_mem_Z_ne_one
  rw [← hs.natCard_setOf_isConj_eq hz hz1]
  have : Nonempty {g : G | IsConj g z} := ⟨⟨z, IsConj.refl z⟩⟩
  exact Nat.card_pos

theorem n_eq_index_centralizer (hz : z ∈ Z) (hz1 : z ≠ 1) :
    Nat.card G / h = (Subgroup.centralizer ({z} : Set G)).index := by
  rw [← hs.natCard_setOf_isConj_eq hz hz1, natCard_setOf_isConj_eq_index_centralizer]

theorem coprime_n_t : Nat.Coprime (Nat.card G / h) (Nat.card (P : Subgroup G)) := by
  have : Fact p.Prime := ⟨hs.prime⟩
  obtain ⟨z, hz, hz1⟩ := hs.exists_mem_Z_ne_one
  have hnp : ¬ p ∣ (Subgroup.centralizer ({z} : Set G)).index := fun hc =>
    P.not_dvd_index (hc.trans (Subgroup.index_dvd_of_le (hs.sylow_le_centralizer hz)))
  rw [hs.n_eq_index_centralizer hz hz1, P.card_eq_multiplicity]
  exact Nat.Coprime.pow_right _ ((hs.prime.coprime_iff_not_dvd.2 hnp).symm)

theorem isHallPiSubgroup_subgroupOf :
    IsHallPiSubgroup ({p} : Set ℕ) ((P : Subgroup G).subgroupOf L) := by
  have : Fact p.Prime := ⟨hs.prime⟩
  have hcard : Nat.card ((P : Subgroup G).subgroupOf L) = Nat.card (P : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hs.sylow_le).toEquiv
  refine ⟨?_, fun q hq hqp => ?_⟩
  · rw [isPiSubgroup_singleton_iff hs.prime]
    exact IsPGroup.of_card (hcard.trans P.card_eq_multiplicity)
  · rw [Set.mem_singleton_iff] at hqp
    subst hqp
    exact P.not_dvd_index ((Nat.dvd_of_mem_primeFactors hq).trans
      (Subgroup.relIndex_dvd_index_of_le hs.sylow_le))

theorem mem_sylow_of_mem_of_orderOf_dvd (hyL : y ∈ L)
    (hdvd : orderOf y ∣ Nat.card (P : Subgroup G)) : y ∈ (P : Subgroup G) := by
  have : Fact p.Prime := ⟨hs.prime⟩
  have hnormal := hs.normal_subgroupOf
  have hord : orderOf (⟨y, hyL⟩ : L) = orderOf y := (orderOf_coe (⟨y, hyL⟩ : L)).symm
  have hmem : (⟨y, hyL⟩ : L) ∈ (P : Subgroup G).subgroupOf L := by
    rw [hs.isHallPiSubgroup_subgroupOf.mem_iff, hord]
    intro q hq
    rw [Set.mem_singleton_iff]
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hd : q ∣ p ^ (Nat.card G).factorization p := by
      rw [← P.card_eq_multiplicity]
      exact (Nat.dvd_of_mem_primeFactors hq).trans hdvd
    exact (Nat.prime_dvd_prime_iff_eq hqp hs.prime).1 (hqp.dvd_of_dvd_pow hd)
  exact hmem

theorem mem_Z_of_isConj_of_commute (hz : z ∈ Z) (hz1 : z ≠ 1) (hy : IsConj z y)
    (hx : x ∈ (P : Subgroup G)) (hx1 : x ≠ 1) (hcomm : x * y = y * x) : y ∈ Z ∧ y ≠ 1 := by
  have hyL : y ∈ L := by
    refine hs.mem_of_conj_mem_sylow hx hx1 ?_
    rwa [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hord : orderOf y = orderOf z := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hy
    exact (SemiconjBy.orderOf_eq c (by rw [SemiconjBy, ← hc]; group)).symm
  have hyP : y ∈ (P : Subgroup G) :=
    hs.mem_sylow_of_mem_of_orderOf_dvd hyL
      (hord ▸ (P : Subgroup G).orderOf_dvd_natCard (hs.Z_le_sylow hz))
  exact hs.mem_Z_of_isConj_of_mem_sylow hz hz1 hy hyP

end Finite

end IsTINormalCentralSection

end CFSG.FeitThompson
