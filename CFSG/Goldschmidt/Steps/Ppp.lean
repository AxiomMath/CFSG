module

public import CFSG.Goldschmidt.Basic
import CFSG.LocalAnalysis.ComponentClassification.OddCore
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
import CFSG.Milestones.OO_odd_order_solvable
import CFSG.SignalizerFunctorTheorem.Solvable.SmallPrimes

public section

namespace CFSG.Goldschmidt.Ppp

open CFSG.Open
open scoped commutatorElement

section Defs

variable {G : Type*} [Group G]

@[expose] def IsGood (A : Subgroup G) (x : G) : Prop :=
  ∀ N : Subgroup G, Odd (Nat.card N) → N ≤ ⁅Subgroup.centralizer ({x} : Set G), A⁆ →
    ⁅N, A⁆ = N → (∃ u ∈ A, u ≠ 1 ∧ N ≤ Subgroup.centralizer ({u} : Set G)) →
    N ≤ oddCoreOf (Subgroup.centralizer ({x} : Set G))

@[expose] def commSpan (A : Subgroup G) : Subgroup G :=
  ⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆

@[expose] def zCore (A B : Subgroup G) : Subgroup G :=
  oddCoreOf (Subgroup.centralizer (A : Set G)) ⊔ oddCoreOf (Subgroup.centralizer (B : Set G))

@[expose] def theta (A B : Subgroup G) (x : G) : Subgroup G :=
  ⁅oddCoreOf (Subgroup.centralizer ({x} : Set G)), A⁆ ⊔
    (zCore A B ⊓ Subgroup.centralizer ({x} : Set G))

end Defs

section General

variable {G : Type*} [Group G]

private theorem mem_normalizer_commutator {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_commutator, hH, hK]

private theorem mem_normalizer_inf {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro h
  exact and_congr (hH h) (hK h)

private theorem mem_normalizer_sup {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

private theorem comm_of_mem {A : Subgroup G} (hA : IsMulCommutative A) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) : a * b = b * a :=
  congrArg Subtype.val (hA.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)

private theorem oddCoreOf_le (H : Subgroup G) : oddCoreOf H ≤ H :=
  Subgroup.map_subtype_le _

private theorem le_normalizer_oddCoreOf (H : Subgroup G) :
    H ≤ Subgroup.normalizer (oddCoreOf H : Set G) := by
  have heq : (oddCoreOf H).subgroupOf H = goldschmidtOddCore H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hn : ((oddCoreOf H).subgroupOf H).Normal := by
    rw [heq]
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (oddCoreOf_le H)).mp hn

private theorem le_oddCoreOf {H N : Subgroup G} (hNH : N ≤ H)
    (hN : H ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N)) : N ≤ oddCoreOf H := by
  have hodd' : Odd (Nat.card (N.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
  have hle : N.subgroupOf H ≤ goldschmidtOddCore H :=
    le_sSup ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hN, hodd'⟩
  have hm := Subgroup.map_mono (f := H.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hNH] at hm

private theorem eq_bot_of_isPGroup_of_odd [Finite G] {K : Subgroup G} (hK : IsPGroup 2 K)
    (hodd : Odd (Nat.card K)) : K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hK.exists_card_eq
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  · rw [hk] at hodd
    exact absurd (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero k⟩) (Nat.not_even_iff_odd.mpr hodd)

variable [Finite G]

private theorem odd_card_oddCoreOf (H : Subgroup G) : Odd (Nat.card (oddCoreOf H)) := by
  rw [oddCoreOf, Subgroup.card_map_of_injective H.subtype_injective]
  exact CFSG.ComponentClassification.OddCore.odd_card H

private theorem oddCoreOf_mono {M X : Subgroup G} (hMX : M ≤ X) (hMn : (M.subgroupOf X).Normal) :
    oddCoreOf M ≤ oddCoreOf X := by
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨Subgroup.inclusion hMX m,
    (CFSG.ComponentClassification.OddCore.normal_step_mem_iff hMX m).mp hm, rfl⟩

omit [Finite G] in
private theorem odd_card_sup {K H : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hK : Odd (Nat.card K)) (hH : Odd (Nat.card H)) : Odd (Nat.card (K ⊔ H : Subgroup G)) := by
  rw [sup_comm]
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHK
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHK
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H K hHK
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf (H ⊔ K)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : K ≤ H ⊔ K)).toEquiv]
  exact (Odd.of_dvd_nat hH (Subgroup.card_quotient_dvd_card _)).mul hK

end General

section Coset

variable {G : Type*} [Group G] {A : Subgroup G} {t : G}

theorem mem_sup_zpowers_iff (ht : t ^ 2 = 1) (htc : t ∈ Subgroup.centralizer (A : Set G))
    {x : G} : x ∈ A ⊔ Subgroup.zpowers t ↔ x ∈ A ∨ ∃ a ∈ A, x = t * a := by
  constructor
  · intro hx
    have hle : Subgroup.zpowers t ≤ Subgroup.normalizer (A : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ htc)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A _ hle] at hx
    obtain ⟨a, ha, y, hy, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hy)
    have ht' : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, ht]
    rw [zpow_eq_zpow_emod k ht']
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      rw [hk, zpow_zero, mul_one]
      exact ha
    · right
      refine ⟨a, ha, ?_⟩
      rw [hk, zpow_one]
      exact Subgroup.mem_centralizer_iff.mp htc a ha
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact Subgroup.mem_sup_left h
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
        (Subgroup.mem_sup_left ha)

theorem isElemAbelian_sup_zpowers (hA : IsElemAbelian 2 A) (ht : t ^ 2 = 1)
    (htc : t ∈ Subgroup.centralizer (A : Set G)) :
    IsElemAbelian 2 (A ⊔ Subgroup.zpowers t) := by
  have hta : ∀ a ∈ A, a * t = t * a := fun a ha => Subgroup.mem_centralizer_iff.mp htc a ha
  have hcomm : ∀ x ∈ A ⊔ Subgroup.zpowers t, ∀ y ∈ A ⊔ Subgroup.zpowers t, x * y = y * x := by
    intro x hx y hy
    rcases (mem_sup_zpowers_iff ht htc).mp hx with hx | ⟨a, ha, rfl⟩ <;>
      rcases (mem_sup_zpowers_iff ht htc).mp hy with hy | ⟨b, hb, rfl⟩
    · exact comm_of_mem hA.1 hx hy
    · exact (show Commute x t from hta x hx).mul_right (comm_of_mem hA.1 hx hb)
    · exact (show Commute y t from hta y hy).symm.mul_left (comm_of_mem hA.1 ha hy)
    · exact ((Commute.refl t).mul_right (show Commute b t from hta b hb).symm).mul_left
        ((show Commute a t from hta a ha).mul_right (comm_of_mem hA.1 ha hb))
  refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, fun x hx => ?_⟩
  rcases (mem_sup_zpowers_iff ht htc).mp hx with hx | ⟨a, ha, rfl⟩
  · exact hA.2 x hx
  · rw [sq, mul_assoc, ← mul_assoc a, hta a ha, mul_assoc, ← sq a, hA.2 a ha, mul_one, ← sq, ht]

theorem eight_dvd_card_sup_zpowers [Finite G] (hA : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A)
    (ht : t ^ 2 = 1) (htA : t ∉ A) (htc : t ∈ Subgroup.centralizer (A : Set G)) :
    2 ^ 3 ∣ Nat.card (A ⊔ Subgroup.zpowers t : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := A ⊔ Subgroup.zpowers t with hBdef
  have hB := isElemAbelian_sup_zpowers hA ht htc
  have hBp : IsPGroup 2 B := fun x => ⟨1, Subtype.ext (by simpa using hB.2 x.1 x.2)⟩
  obtain ⟨k, hk⟩ := hBp.exists_card_eq
  have hAB : A ≤ B := le_sup_left
  have hlt : A < B := lt_of_le_of_ne hAB fun h =>
    htA (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hcardlt : Nat.card A < Nat.card B := Subgroup.card_lt_of_lt hlt
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hAB
  have hm2 : 2 ≤ m := by
    by_contra h
    have hle : Nat.card B ≤ Nat.card A :=
      calc Nat.card B = Nat.card A * m := hm
        _ ≤ Nat.card A * 1 := Nat.mul_le_mul_left _ (by omega)
        _ = Nat.card A := mul_one _
    omega
  have h8 : 8 ≤ 2 ^ k := by
    rw [← hk, hm]
    nlinarith
  rw [hk]
  refine pow_dvd_pow 2 ?_
  by_contra hlt3
  have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Coset

section Functor

variable {G : Type} [Group G] {A : Subgroup G} {t : G}

private theorem commutator_le_oddCoreOf {x : G} (hAx : A ≤ Subgroup.centralizer ({x} : Set G)) :
    ⁅oddCoreOf (Subgroup.centralizer ({x} : Set G)), A⁆ ≤
      oddCoreOf (Subgroup.centralizer ({x} : Set G)) :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp (hAx.trans (le_normalizer_oddCoreOf _))

private theorem oddCoreOf_le_zCore_left (B : Subgroup G) :
    oddCoreOf (Subgroup.centralizer (A : Set G)) ≤ zCore A B :=
  le_sup_left

private theorem oddCoreOf_le_zCore_right (B : Subgroup G) :
    oddCoreOf (Subgroup.centralizer (B : Set G)) ≤ zCore A B :=
  le_sup_right

private theorem zCore_le_centralizer {B : Subgroup G} (hAB : A ≤ B) :
    zCore A B ≤ Subgroup.centralizer (A : Set G) :=
  sup_le (oddCoreOf_le _) ((oddCoreOf_le _).trans (Subgroup.centralizer_le hAB))

private theorem odd_card_zCore [Finite G] {B : Subgroup G} (hAB : A ≤ B) :
    Odd (Nat.card (zCore A B)) :=
  odd_card_sup ((oddCoreOf_le _).trans ((Subgroup.centralizer_le hAB).trans
    (le_normalizer_oddCoreOf _))) (odd_card_oddCoreOf _) (odd_card_oddCoreOf _)

private theorem inf_le_normalizer {B : Subgroup G} (hAB : A ≤ B) (x : G) :
    zCore A B ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((⁅oddCoreOf (Subgroup.centralizer ({x} : Set G)), A⁆ :
        Subgroup G) : Set G) := fun _ hg =>
  mem_normalizer_commutator (le_normalizer_oddCoreOf _ hg.2)
    (Subgroup.centralizer_le_normalizer _ (zCore_le_centralizer hAB hg.1))

private theorem odd_card_theta [Finite G] {B : Subgroup G} (hAB : A ≤ B) {x : G}
    (hAx : A ≤ Subgroup.centralizer ({x} : Set G)) : Odd (Nat.card (theta A B x)) :=
  odd_card_sup (inf_le_normalizer hAB x)
    ((odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le (commutator_le_oddCoreOf hAx)))
    ((odd_card_zCore hAB).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))

private theorem theta_le_centralizer {B : Subgroup G} {x : G}
    (hAx : A ≤ Subgroup.centralizer ({x} : Set G)) :
    theta A B x ≤ Subgroup.centralizer ({x} : Set G) :=
  sup_le ((commutator_le_oddCoreOf hAx).trans (oddCoreOf_le _)) inf_le_right

private theorem exists_mul_of_mem_theta {B : Subgroup G} (hAB : A ≤ B) {x g : G}
    (hg : g ∈ theta A B x) :
    ∃ y ∈ ⁅oddCoreOf (Subgroup.centralizer ({x} : Set G)), A⁆,
      ∃ c ∈ zCore A B ⊓ Subgroup.centralizer ({x} : Set G), y * c = g := by
  rw [← SetLike.mem_coe, theta,
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (inf_le_normalizer hAB x)] at hg
  exact Set.mem_mul.mp hg

private theorem commutator_theta_le {B : Subgroup G} (hAB : A ≤ B) {x : G}
    (hAx : A ≤ Subgroup.centralizer ({x} : Set G)) :
    ⁅theta A B x, A⁆ ≤ ⁅oddCoreOf (Subgroup.centralizer ({x} : Set G)), A⁆ := by
  rw [Subgroup.commutator_le]
  intro g hg a ha
  obtain ⟨y, hy, c, hc, rfl⟩ := exists_mul_of_mem_theta hAB hg
  have hca : a * c = c * a := Subgroup.mem_centralizer_iff.mp (zCore_le_centralizer hAB hc.1) a ha
  have h : ⁅y * c, a⁆ = ⁅y, a⁆ := by
    rw [commutatorElement_def, commutatorElement_def, mul_assoc y c a, ← hca]
    group
  rw [h]
  exact Subgroup.commutator_mem_commutator (commutator_le_oddCoreOf hAx hy) ha

private theorem theta_inf_centralizer_le {B : Subgroup G} (hAB : A ≤ B) {x : G}
    (hAx : A ≤ Subgroup.centralizer ({x} : Set G))
    (hP : oddCoreOf (Subgroup.centralizer ({x} : Set G)) ⊓ Subgroup.centralizer (A : Set G) ≤
      zCore A B) :
    theta A B x ⊓ Subgroup.centralizer (A : Set G) ≤ zCore A B := by
  rintro g ⟨hg, hgA⟩
  obtain ⟨y, hy, c, hc, rfl⟩ := exists_mul_of_mem_theta hAB hg
  have hcA := zCore_le_centralizer hAB hc.1
  have hyA : y ∈ Subgroup.centralizer (A : Set G) := by
    have := Subgroup.mul_mem _ hgA (Subgroup.inv_mem _ hcA)
    rwa [mul_inv_cancel_right] at this
  exact Subgroup.mul_mem _ (hP ⟨commutator_le_oddCoreOf hAx hy, hyA⟩) hc.1

variable (hA : IsElemAbelian 2 A) (ht : t ^ 2 = 1) (htc : t ∈ Subgroup.centralizer (A : Set G))
include hA ht htc

private theorem comm_of_mem_B {x y : G} (hx : x ∈ A ⊔ Subgroup.zpowers t)
    (hy : y ∈ A ⊔ Subgroup.zpowers t) : x * y = y * x :=
  comm_of_mem (isElemAbelian_sup_zpowers hA ht htc).1 hx hy

private theorem le_centralizer_of_mem_B {x : G} (hx : x ∈ A ⊔ Subgroup.zpowers t) :
    A ⊔ Subgroup.zpowers t ≤ Subgroup.centralizer ({x} : Set G) := fun _ hy =>
  Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_B hA ht htc hy hx)

private theorem mem_centralizer_of_mem_B {x : G} (hx : x ∈ A ⊔ Subgroup.zpowers t) :
    x ∈ Subgroup.centralizer (A : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ ha => comm_of_mem_B hA ht htc (Subgroup.mem_sup_left ha) hx

omit hA in
private theorem mem_centralizer_B_of_mem_centralizer_A {x g : G}
    (hx : x ∈ A ⊔ Subgroup.zpowers t) (hxA : x ∉ A) (hgA : g ∈ Subgroup.centralizer (A : Set G))
    (hgx : g ∈ Subgroup.centralizer ({x} : Set G)) :
    g ∈ Subgroup.centralizer ((A ⊔ Subgroup.zpowers t : Subgroup G) : Set G) := by
  have hgx' : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hgx
  have hga : ∀ a ∈ A, a * g = g * a := fun a ha => Subgroup.mem_centralizer_iff.mp hgA a ha
  obtain ⟨b, hb, rfl⟩ := ((mem_sup_zpowers_iff ht htc).mp hx).resolve_left hxA
  have hgt : Commute g t := by
    have h := (show Commute g (t * b) from hgx').mul_right
      (show Commute b g from hga b hb).symm.inv_right
    rwa [mul_inv_cancel_right] at h
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases (mem_sup_zpowers_iff ht htc).mp hy with hy | ⟨a, ha, rfl⟩
  · exact hga y hy
  · exact (hgt.mul_right (show Commute a g from hga a ha).symm).symm

private theorem le_normalizer_theta {x : G} (hx : x ∈ A ⊔ Subgroup.zpowers t) :
    A ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer
      ((theta A (A ⊔ Subgroup.zpowers t) x : Subgroup G) : Set G) := by
  intro b hb
  have hbx := le_centralizer_of_mem_B hA ht htc hx hb
  have hbA := mem_centralizer_of_mem_B hA ht htc hb
  have hbB : b ∈ Subgroup.centralizer ((A ⊔ Subgroup.zpowers t : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun _ hy => comm_of_mem_B hA ht htc hy hb
  refine mem_normalizer_sup (mem_normalizer_commutator (le_normalizer_oddCoreOf _ hbx)
    (Subgroup.centralizer_le_normalizer _ hbA)) (mem_normalizer_inf ?_ (Subgroup.le_normalizer hbx))
  exact mem_normalizer_sup (le_normalizer_oddCoreOf _ hbA) (le_normalizer_oddCoreOf _ hbB)

omit hA in
private theorem inf_centralizer_le_zCore [Finite G] {x : G} (hx : x ∈ A ⊔ Subgroup.zpowers t) :
    oddCoreOf (Subgroup.centralizer ({x} : Set G)) ⊓ Subgroup.centralizer (A : Set G) ≤
      zCore A (A ⊔ Subgroup.zpowers t) := by
  have hodd : Odd (Nat.card (oddCoreOf (Subgroup.centralizer ({x} : Set G)) ⊓
      Subgroup.centralizer (A : Set G) : Subgroup G)) :=
    (odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  by_cases hxA : x ∈ A
  · have hCA : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxA)
    refine (le_oddCoreOf inf_le_right (fun g hg => mem_normalizer_inf
      (le_normalizer_oddCoreOf _ (hCA hg)) (Subgroup.le_normalizer hg)) hodd).trans
      (oddCoreOf_le_zCore_left _)
  · have hBA : Subgroup.centralizer ((A ⊔ Subgroup.zpowers t : Subgroup G) : Set G) ≤
        Subgroup.centralizer (A : Set G) :=
      Subgroup.centralizer_le (le_sup_left : A ≤ A ⊔ Subgroup.zpowers t)
    have hBx : Subgroup.centralizer ((A ⊔ Subgroup.zpowers t : Subgroup G) : Set G) ≤
        Subgroup.centralizer ({x} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx)
    have hPB : oddCoreOf (Subgroup.centralizer ({x} : Set G)) ⊓ Subgroup.centralizer (A : Set G) ≤
        Subgroup.centralizer ((A ⊔ Subgroup.zpowers t : Subgroup G) : Set G) := fun g hg =>
      mem_centralizer_B_of_mem_centralizer_A ht htc hx hxA hg.2 (oddCoreOf_le _ hg.1)
    refine (le_oddCoreOf hPB (fun g hg => mem_normalizer_inf (le_normalizer_oddCoreOf _ (hBx hg))
      (Subgroup.le_normalizer (hBA hg))) hodd).trans (oddCoreOf_le_zCore_right _)

theorem theta_balance [Finite G] {e f : G} (he : e ∈ A ⊔ Subgroup.zpowers t) (he1 : e ≠ 1)
    (hf : f ∈ A ⊔ Subgroup.zpowers t) (hf1 : f ≠ 1) (hgood : IsGood A f) :
    theta A (A ⊔ Subgroup.zpowers t) e ⊓ Subgroup.centralizer ({f} : Set G) ≤
      theta A (A ⊔ Subgroup.zpowers t) f := by
  by_cases hef : e = f
  · subst hef
    exact inf_le_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := A ⊔ Subgroup.zpowers t with hBdef
  set X := theta A B e ⊓ Subgroup.centralizer ({f} : Set G) with hXdef
  have hA2 : IsPGroup 2 A := fun a => ⟨1, Subtype.ext (by simpa using hA.2 a.1 a.2)⟩
  have hAB : A ≤ B := le_sup_left
  have hAe : A ≤ Subgroup.centralizer ({e} : Set G) :=
    hAB.trans (le_centralizer_of_mem_B hA ht htc he)
  have hAf : A ≤ Subgroup.centralizer ({f} : Set G) :=
    hAB.trans (le_centralizer_of_mem_B hA ht htc hf)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := fun a ha =>
    mem_normalizer_inf (le_normalizer_theta hA ht htc he (hAB ha))
      (Subgroup.le_normalizer (hAf ha))
  have hXodd : Odd (Nat.card X) :=
    (odd_card_theta hAB hAe).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hXcop : Nat.Coprime 2 (Nat.card X) := Nat.coprime_two_left.mpr hXodd
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two A X hA2 hAX hXcop
  have hidem := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 2
    Nat.prime_two A X hA2 hAX hXcop
  rw [← hfac]
  refine sup_le ?_ ?_
  ·
    set Ye := ⁅oddCoreOf (Subgroup.centralizer ({e} : Set G)), A⁆ with hYedef
    set V := Ye ⊓ Subgroup.centralizer ({f} : Set G) with hVdef
    have hYeO : Ye ≤ oddCoreOf (Subgroup.centralizer ({e} : Set G)) := commutator_le_oddCoreOf hAe
    have hYe : Ye ≤ Subgroup.centralizer ({e} : Set G) := hYeO.trans (oddCoreOf_le _)
    have hAV : A ≤ Subgroup.normalizer (V : Set G) := fun a ha =>
      mem_normalizer_inf (mem_normalizer_commutator (le_normalizer_oddCoreOf _ (hAe ha))
        (Subgroup.le_normalizer ha)) (Subgroup.le_normalizer (hAf ha))
    have hVodd : Odd (Nat.card V) :=
      (odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_left.trans hYeO))
    have hVcop : Nat.Coprime 2 (Nat.card V) := Nat.coprime_two_left.mpr hVodd
    have hXV : ⁅X, A⁆ ≤ V := le_inf
      ((Subgroup.commutator_mono inf_le_left le_rfl).trans (commutator_theta_le hAB hAe))
      ((Subgroup.le_normalizer_iff_commutator_le_left.mp hAX).trans inf_le_right)
    set N := ⁅V, A⁆ with hNdef
    have hNV : N ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hAV
    have hNodd : Odd (Nat.card N) := hVodd.of_dvd_nat (Subgroup.card_dvd_of_le hNV)
    have hNN : ⁅N, A⁆ = N := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent
      2 Nat.prime_two A V hA2 hAV hVcop
    have hXN : ⁅X, A⁆ ≤ N := by
      rw [← hidem]
      exact Subgroup.commutator_mono hXV le_rfl
    have hNC : N ≤ ⁅Subgroup.centralizer ({f} : Set G), A⁆ :=
      Subgroup.commutator_mono inf_le_right le_rfl
    have hNu : ∃ u ∈ A, u ≠ 1 ∧ N ≤ Subgroup.centralizer ({u} : Set G) := by
      by_cases heA : e ∈ A
      · exact ⟨e, heA, he1, hNV.trans (inf_le_left.trans hYe)⟩
      by_cases hfA : f ∈ A
      · exact ⟨f, hfA, hf1, hNV.trans inf_le_right⟩
      obtain ⟨a, ha, rfl⟩ := ((mem_sup_zpowers_iff ht htc).mp he).resolve_left heA
      obtain ⟨b, hb, rfl⟩ := ((mem_sup_zpowers_iff ht htc).mp hf).resolve_left hfA
      refine ⟨(t * a)⁻¹ * (t * b), ?_, fun h => hef (inv_mul_eq_one.mp h), fun g hg => ?_⟩
      · rw [show (t * a)⁻¹ * (t * b) = a⁻¹ * b by group]
        exact A.mul_mem (A.inv_mem ha) hb
      · have hge : g * (t * a) = t * a * g :=
          Subgroup.mem_centralizer_singleton_iff.mp (hYe (hNV hg).1)
        have hgf : g * (t * b) = t * b * g :=
          Subgroup.mem_centralizer_singleton_iff.mp (hNV hg).2
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Commute.inv_right hge).mul_right hgf)
    have hNO := hgood N hNodd hNC hNN hNu
    calc ⁅X, A⁆ = ⁅⁅X, A⁆, A⁆ := hidem.symm
      _ ≤ ⁅oddCoreOf (Subgroup.centralizer ({f} : Set G)), A⁆ :=
          Subgroup.commutator_mono (hXN.trans hNO) le_rfl
      _ ≤ theta A B f := le_sup_left
  ·
    rintro g ⟨⟨hge, hgf⟩, hgA⟩
    exact Subgroup.mem_sup_right ⟨theta_inf_centralizer_le hAB hAe
      (inf_centralizer_le_zCore ht htc he) ⟨hge, hgA⟩, hgf⟩

theorem isSolvableSignalizerFunctor_theta [Finite G]
    (hgood : ∀ x ∈ A ⊔ Subgroup.zpowers t, x ≠ 1 → IsGood A x) :
    IsSolvableSignalizerFunctor 2 (A ⊔ Subgroup.zpowers t)
      (theta A (A ⊔ Subgroup.zpowers t)) where
  le_centralizer _ hx _ :=
    theta_le_centralizer (le_sup_left.trans (le_centralizer_of_mem_B hA ht htc hx))
  coprime _ hx _ := Nat.coprime_two_left.mpr
    (odd_card_theta le_sup_left (le_sup_left.trans (le_centralizer_of_mem_B hA ht htc hx)))
  invariant _ hx _ _ hb :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_theta hA ht htc hx hb)
  balance _ he he1 f hf hf1 := theta_balance hA ht htc he he1 hf hf1 (hgood f hf hf1)
  solvable _ hx _ := CFSG.Milestones.odd_order_solvable
    (odd_card_theta le_sup_left (le_sup_left.trans (le_centralizer_of_mem_B hA ht htc hx)))

end Functor

theorem odd_card_commSpan {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A) {t : G} (ht : t ^ 2 = 1) (htA : t ∉ A)
    (htc : t ∈ Subgroup.centralizer (A : Set G))
    (hgood : ∀ x ∈ A ⊔ Subgroup.zpowers t, x ≠ 1 → IsGood A x) :
    Odd (Nat.card (commSpan A)) := by
  have hB := isElemAbelian_sup_zpowers hA ht htc
  obtain ⟨hcop, -, -⟩ := CFSG.SignalizerFunctorTheorem.Solvable.glauberman_of_le_three G 2
    Nat.prime_two (by norm_num) (A ⊔ Subgroup.zpowers t) hB.1 hB.2
    (eight_dvd_card_sup_zpowers hA hA4 ht htA htc) (theta A (A ⊔ Subgroup.zpowers t))
    (isSolvableSignalizerFunctor_theta hA ht htc hgood)
  refine (Nat.coprime_two_left.mp hcop).of_dvd_nat (Subgroup.card_dvd_of_le ?_)
  refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
  exact le_iSup_of_le a (le_iSup_of_le (Subgroup.mem_sup_left ha) (le_iSup_of_le ha1 le_sup_left))

theorem odd_card_commSpan' {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A) {t : G} (ht : t ^ 2 = 1) (htA : t ∉ A)
    (htc : t ∈ Subgroup.centralizer (A : Set G))
    (hgoodA : ∀ a ∈ A, a ≠ 1 → IsGood A a) (hgoodt : ∀ a ∈ A, IsGood A (t * a)) :
    Odd (Nat.card (commSpan A)) := by
  refine odd_card_commSpan hA hA4 ht htA htc fun x hx hx1 => ?_
  rcases (mem_sup_zpowers_iff ht htc).mp hx with hxA | ⟨a, ha, rfl⟩
  · exact hgoodA x hxA hx1
  · exact hgoodt a ha

section Good

variable {G : Type*} [Group G] [Finite G]

theorem le_oddCoreOf_of_le_preOf {H N : Subgroup G} {P : Subgroup (H ⧸ goldschmidtOddCore H)}
    (hP : IsPGroup 2 P) (hN : Odd (Nat.card N)) (hNP : N ≤ preOf H P) : N ≤ oddCoreOf H := by
  have hNH : N ≤ H := hNP.trans (Subgroup.map_subtype_le _)
  set π := QuotientGroup.mk' (goldschmidtOddCore H) with hπ
  have hle : (N.subgroupOf H).map π ≤ P := by
    rintro _ ⟨n, hn, rfl⟩
    obtain ⟨m, hm, hmn⟩ := hNP hn
    rw [show n = m from Subtype.ext hmn.symm]
    exact hm
  have hodd : Odd (Nat.card ((N.subgroupOf H).map π)) := by
    refine hN.of_dvd_nat ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
  have hbot := eq_bot_of_isPGroup_of_odd (hP.to_le hle) hodd
  intro n hn
  have h1 : π ⟨n, hNH hn⟩ ∈ (N.subgroupOf H).map π := ⟨⟨n, hNH hn⟩, hn, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  exact ⟨⟨n, hNH hn⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩

theorem isGood_of_le_preOf {A : Subgroup G} {x : G}
    {P : Subgroup (Subgroup.centralizer ({x} : Set G) ⧸
      goldschmidtOddCore (Subgroup.centralizer ({x} : Set G)))} (hP : IsPGroup 2 P)
    (h : ⁅Subgroup.centralizer ({x} : Set G), A⁆ ≤ preOf (Subgroup.centralizer ({x} : Set G)) P) :
    IsGood A x :=
  fun _ hN hNle _ _ => le_oddCoreOf_of_le_preOf hP hN (hNle.trans h)

theorem isGood_of_commutator_le_sup {A : Subgroup G} (hA : IsPGroup 2 A) {x : G}
    (hAx : A ≤ Subgroup.centralizer ({x} : Set G))
    (h : ⁅Subgroup.centralizer ({x} : Set G), A⁆ ≤
      oddCoreOf (Subgroup.centralizer ({x} : Set G)) ⊔ A) :
    IsGood A x := by
  refine isGood_of_le_preOf (P := barOf (Subgroup.centralizer ({x} : Set G)) A)
    (hA.comap_subtype.map _) (h.trans (sup_le ?_ ?_))
  · rintro _ ⟨o, ho, rfl⟩
    refine ⟨o, Subgroup.mem_comap.mpr ?_, rfl⟩
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff o).mpr ho]
    exact Subgroup.one_mem _
  · intro a ha
    exact ⟨⟨a, hAx ha⟩, ⟨⟨a, hAx ha⟩, ha, rfl⟩, rfl⟩

omit [Finite G] in
theorem commutator_le_normalClosureIn {X A : Subgroup G} (hAX : A ≤ X) :
    ⁅X, A⁆ ≤ normalClosureIn X A := by
  rw [Subgroup.commutator_le]
  intro c hc a ha
  have h1 : (⟨a, hAX ha⟩ : X) ∈ Subgroup.normalClosure ((A.subgroupOf X : Subgroup X) : Set X) :=
    Subgroup.subset_normalClosure (show (⟨a, hAX ha⟩ : X) ∈ A.subgroupOf X from ha)
  refine ⟨(⟨c, hc⟩ : X) * ⟨a, hAX ha⟩ * (⟨c, hc⟩ : X)⁻¹ * (⟨a, hAX ha⟩ : X)⁻¹,
    Subgroup.mul_mem _ (Subgroup.normalClosure_normal.conj_mem _ h1 _) (Subgroup.inv_mem _ h1), ?_⟩
  rfl

theorem isGood_of_normalClosureIn_eq {A : Subgroup G} (hA : IsPGroup 2 A) {x : G}
    (hAx : A ≤ Subgroup.centralizer ({x} : Set G))
    (h : normalClosureIn (Subgroup.centralizer ({x} : Set G)) A =
      oddCoreOf (normalClosureIn (Subgroup.centralizer ({x} : Set G)) A) ⊔ A) :
    IsGood A x := by
  set C := Subgroup.centralizer ({x} : Set G) with hC
  have hQC : normalClosureIn C A ≤ C := Subgroup.map_subtype_le _
  have hQn : ((normalClosureIn C A).subgroupOf C).Normal := by
    have heq : (normalClosureIn C A).subgroupOf C =
        Subgroup.normalClosure ((A.subgroupOf C : Subgroup C) : Set C) :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
    rw [heq]
    exact Subgroup.normalClosure_normal
  refine isGood_of_commutator_le_sup hA hAx ?_
  calc ⁅C, A⁆ ≤ normalClosureIn C A := commutator_le_normalClosureIn hAx
    _ = oddCoreOf (normalClosureIn C A) ⊔ A := h
    _ ≤ oddCoreOf C ⊔ A := sup_le_sup_right (oddCoreOf_mono hQC hQn) A

theorem isGood_of_barOf_le_pCore {A : Subgroup G} {x : G}
    (hAx : A ≤ Subgroup.centralizer ({x} : Set G))
    (h : barOf (Subgroup.centralizer ({x} : Set G)) A ≤
      CFSG.Open.pCore 2 (Subgroup.centralizer ({x} : Set G) ⧸
        goldschmidtOddCore (Subgroup.centralizer ({x} : Set G)))) :
    IsGood A x := by
  set C := Subgroup.centralizer ({x} : Set G) with hC
  have hPn := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal (G := C ⧸ goldschmidtOddCore C) 2
  refine isGood_of_le_preOf (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2) ?_
  rw [Subgroup.commutator_le]
  intro c hc a ha
  have hpa : QuotientGroup.mk' (goldschmidtOddCore C) (⟨a, hAx ha⟩ : C) ∈
      CFSG.Open.pCore 2 (C ⧸ goldschmidtOddCore C) := h ⟨⟨a, hAx ha⟩, ha, rfl⟩
  refine ⟨(⟨c, hc⟩ : C) * ⟨a, hAx ha⟩ * (⟨c, hc⟩ : C)⁻¹ * (⟨a, hAx ha⟩ : C)⁻¹,
    Subgroup.mem_comap.mpr ?_, rfl⟩
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  exact Subgroup.mul_mem _ (hPn.conj_mem _ hpa _) (Subgroup.inv_mem _ hpa)

end Good

end CFSG.Goldschmidt.Ppp
