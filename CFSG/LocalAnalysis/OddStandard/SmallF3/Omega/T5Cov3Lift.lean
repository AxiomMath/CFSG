module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private lemma t5c_involution_pow_odd {B : Type*} [Group B] {w : B} (hww : w * w = 1)
    {N : ℕ} (hN : Odd N) : w ^ N = w := by
  obtain ⟨k, hk⟩ := hN
  rw [hk, pow_add, pow_mul, pow_two, hww, one_pow, one_mul, pow_one]

private lemma twoRes_le {G : Type} [Group G] (H : Subgroup G) : twoRes H ≤ H := by
  rw [twoRes]
  exact (Subgroup.closure_le _).mpr (fun g hg => hg.1)

theorem t5c_odd_orderOf_of_odd_ker {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hk : Odd (Nat.card f.ker)) {a : A} (ha : Odd (orderOf (f a))) : Odd (orderOf a) := by
  have hker : a ^ orderOf (f a) ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  have hdvd : orderOf (a ^ orderOf (f a)) ∣ Nat.card f.ker :=
    Subgroup.orderOf_dvd_natCard f.ker hker
  have hpow : a ^ (orderOf (f a) * orderOf (a ^ orderOf (f a))) = 1 := by
    rw [pow_mul, pow_orderOf_eq_one]
  have hdvd2 : orderOf a ∣ orderOf (f a) * orderOf (a ^ orderOf (f a)) :=
    orderOf_dvd_of_pow_eq_one hpow
  exact (ha.mul (hk.of_dvd_nat hdvd)).of_dvd_nat hdvd2

theorem t5c_involution_pow_lift {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hk : Odd (Nat.card f.ker)) {a : A} {w : B} (ha : f a = w) (hww : w * w = 1)
    (hw1 : w ≠ 1) :
    ∃ n : ℕ, orderOf (a ^ n) = 2 ∧ f (a ^ n) = w := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have h2ker : a ^ 2 ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, ha, pow_two, hww]
  have hN : (a ^ 2) ^ Nat.card f.ker = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard f.ker h2ker)
  have hsq : (a ^ Nat.card f.ker) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm (Nat.card f.ker) 2, pow_mul]
    exact hN
  have hfN : f (a ^ Nat.card f.ker) = w := by
    rw [map_pow, ha]
    exact t5c_involution_pow_odd hww hk
  have hne : a ^ Nat.card f.ker ≠ 1 := by
    intro h1
    apply hw1
    rw [← hfN, h1, map_one]
  exact ⟨Nat.card f.ker, orderOf_eq_prime hsq hne, hfN⟩

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem t5c_lift_mem_twoRes (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (h : IsCoverMap L φ)
    {s : G} (hs2 : s * s = 1) {x : simGroup Q} (hx : CoverAct L φ s x) {w : OGroup Q}
    (hw : w ∈ twoRes (omegaGroup hQ ⊓ fixSub (simAct Q x))) :
    ∃ (u : G) (hu : u ∈ L), u ∈ twoRes (L ⊓ centralizer ({s} : Set G)) ∧ s * u = u * s ∧
      ((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q) = w := by
  rw [twoRes] at hw
  refine Subgroup.closure_induction (p := fun y _ => ∃ (u : G) (hu : u ∈ L),
    u ∈ twoRes (L ⊓ centralizer ({s} : Set G)) ∧ s * u = u * s ∧
      ((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q) = y) ?_ ?_ ?_ ?_ hw
  · rintro y ⟨hyΩ, hyodd⟩
    obtain ⟨l, hlcomm, hφl⟩ := t5_cent_exists hL h hx hs2 hyΩ
    have hyodd' : Odd (orderOf ((φ l : omegaGroup hQ) : OGroup Q)) := by
      rw [hφl]; exact hyodd
    have ha : Odd (orderOf (φ l)) := by rwa [Subgroup.orderOf_coe] at hyodd'
    have hlodd : Odd (orderOf l) :=
      t5c_odd_orderOf_of_odd_ker φ (h.oddCentralCover hL).odd_card_ker ha
    have hlgodd : Odd (orderOf (l : G)) := by
      rw [Subgroup.orderOf_coe]
      exact hlodd
    refine ⟨(l : G), l.2, ?_, hlcomm, hφl⟩
    rw [twoRes]
    exact Subgroup.subset_closure
      ⟨⟨l.2, Subgroup.mem_centralizer_singleton_iff.mpr hlcomm.symm⟩, hlgodd⟩
  · refine ⟨1, L.one_mem, ?_, ?_, ?_⟩
    · rw [twoRes]; exact Subgroup.one_mem _
    · rw [mul_one, one_mul]
    · rw [show (⟨1, L.one_mem⟩ : ↥L) = 1 from rfl, map_one, Subgroup.coe_one]
  · intro y z _ _ ihy ihz
    obtain ⟨u, hu, hu2, huc, hφu⟩ := ihy
    obtain ⟨v, hv, hv2, hvc, hφv⟩ := ihz
    refine ⟨u * v, L.mul_mem hu hv, ?_, ?_, ?_⟩
    · exact Subgroup.mul_mem _ hu2 hv2
    · exact (Commute.mul_right (show Commute s u from huc) (show Commute s v from hvc)).eq
    · have hcast : (⟨u * v, L.mul_mem hu hv⟩ : ↥L) = (⟨u, hu⟩ : ↥L) * ⟨v, hv⟩ := rfl
      rw [hcast, map_mul, Subgroup.coe_mul, hφu, hφv]
  · intro y _ ihy
    obtain ⟨u, hu, hu2, huc, hφu⟩ := ihy
    refine ⟨u⁻¹, L.inv_mem hu, ?_, ?_, ?_⟩
    · exact Subgroup.inv_mem _ hu2
    · exact (Commute.inv_right_iff.mpr (show Commute s u from huc)).eq
    · have hcast : (⟨u⁻¹, L.inv_mem hu⟩ : ↥L) = (⟨u, hu⟩ : ↥L)⁻¹ := rfl
      rw [hcast, map_inv, Subgroup.coe_inv, hφu]

theorem t5c_lift_twoRes (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (h : IsCoverMap L φ)
    {s : G} (hs2 : s * s = 1) {x : simGroup Q} (hx : CoverAct L φ s x) {w : OGroup Q}
    (hw : w ∈ twoRes (omegaGroup hQ ⊓ fixSub (simAct Q x))) (hww : w * w = 1) (hw1 : w ≠ 1) :
    ∃ (u : G) (hu : u ∈ L), u ∈ twoRes (L ⊓ centralizer ({s} : Set G)) ∧ orderOf u = 2 ∧
      s * u = u * s ∧ ((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q) = w := by
  have hwΩ : w ∈ omegaGroup hQ := (twoRes_le (omegaGroup hQ ⊓ fixSub (simAct Q x)) hw).1
  let W : omegaGroup hQ := ⟨w, hwΩ⟩
  have hWW : W * W = 1 := Subtype.ext hww
  have hW1 : W ≠ 1 := fun h1 => hw1 (Subtype.ext_iff.mp h1)
  obtain ⟨u₀, hu₀, hu₀2, hu₀c, hφu₀⟩ := t5c_lift_mem_twoRes hL h hs2 hx hw
  have hφu₀W : φ ⟨u₀, hu₀⟩ = W := Subtype.ext hφu₀
  obtain ⟨n, hn, hφn⟩ :=
    t5c_involution_pow_lift φ (h.oddCentralCover hL).odd_card_ker hφu₀W hWW hW1
  have huL : u₀ ^ n ∈ L := L.pow_mem hu₀ n
  have hu2 : u₀ ^ n ∈ twoRes (L ⊓ centralizer ({s} : Set G)) := Subgroup.pow_mem _ hu₀2 n
  have huord : orderOf (u₀ ^ n) = 2 := by
    have hcast : u₀ ^ n = (((⟨u₀, hu₀⟩ : ↥L) ^ n : ↥L) : G) := rfl
    rw [hcast, Subgroup.orderOf_coe]
    exact hn
  have huc : s * (u₀ ^ n) = (u₀ ^ n) * s :=
    (Commute.pow_right (show Commute s u₀ from hu₀c) n).eq
  have hφu : ((φ ⟨u₀ ^ n, huL⟩ : omegaGroup hQ) : OGroup Q) = w := by
    have hcast : (⟨u₀ ^ n, huL⟩ : ↥L) = (⟨u₀, hu₀⟩ : ↥L) ^ n := rfl
    rw [hcast, hφn]
  exact ⟨u₀ ^ n, huL, hu2, huord, huc, hφu⟩

end CFSG.OddStandard.SmallF3.Omega
