module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.QuotientFamily
public import CFSG.ClassicalInvolution.Q3.TL3C11

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

theorem exists_two_power_lift {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (hker : Odd (Nat.card f.ker)) {x : A} (hx : IsPGroup 2 (Subgroup.zpowers (f x))) :
    ∃ y ∈ Subgroup.zpowers x, IsPGroup 2 (Subgroup.zpowers y) ∧ f y = f x := by
  classical
  obtain ⟨j, hj⟩ := hx (⟨f x, Subgroup.mem_zpowers _⟩ : Subgroup.zpowers (f x))
  have hj' : (f x) ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hxk : x ^ 2 ^ j ∈ f.ker := by rw [MonoidHom.mem_ker, map_pow, hj']
  have hord : orderOf (x ^ 2 ^ j) ∣ Nat.card f.ker := by
    have := Subgroup.orderOf_dvd_natCard f.ker hxk
    simpa using this
  set d := orderOf (x ^ 2 ^ j) with hd
  have hdodd : Odd d := hker.of_dvd_nat hord
  have hcop : Nat.Coprime (2 ^ j) d := (Nat.coprime_two_left.mpr hdodd).pow_left j
  obtain ⟨e, he1, he2⟩ : ∃ e : ℕ, e ≡ 1 [MOD 2 ^ j] ∧ e ≡ 0 [MOD d] :=
    ⟨_, (Nat.chineseRemainder hcop 1 0).2⟩
  refine ⟨x ^ e, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) e, ?_, ?_⟩
  ·
    have h1 : (x ^ e) ^ 2 ^ j = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      have : d ∣ e := (Nat.modEq_zero_iff_dvd).mp he2
      obtain ⟨c, hc⟩ := this
      have hd1 : (x ^ 2 ^ j) ^ d = 1 := pow_orderOf_eq_one _
      rw [hc, pow_mul, hd1, one_pow]
    have h2 : orderOf (x ^ e) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one h1
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    refine IsPGroup.of_card (n := i) ?_
    rw [Nat.card_zpowers, hi]
  ·
    rw [map_pow]
    have h3 : orderOf (f x) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
    have h4 : e ≡ 1 [MOD orderOf (f x)] := he1.of_dvd h3
    calc (f x) ^ e = (f x) ^ 1 := (pow_eq_pow_iff_modEq).mpr h4
      _ = f x := pow_one _

theorem tightCore_map_odd {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B)
    (hker : Odd (Nat.card f.ker)) (X : Subgroup A) :
    tightCore (X.map f) = (tightCore X).map f := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyX, hy2⟩
    obtain ⟨x, hx, rfl⟩ := hyX
    obtain ⟨z, hz, hz2, hzx⟩ := exists_two_power_lift f hker hy2
    have hzX : z ∈ X := X.zpowers_le.mpr hx |> fun h => h hz
    rw [← hzx]
    exact Subgroup.mem_map_of_mem f (Subgroup.subset_closure ⟨hzX, hz2⟩)
  · rw [tightCore, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨hxR, hx2⟩, rfl⟩
    refine ⟨⟨x, hxR, rfl⟩, ?_⟩
    rw [← MonoidHom.map_zpowers]
    exact hx2.map _


section Sec

variable {Y : Type} [Group Y] [Finite Y]

theorem tightCore_secR (R : Subgroup Y) (u : Y) :
    tightCore (secR R u) =
      ((tightCore (R.subgroupOf (Subgroup.centralizer ({u} : Set Y)))).subgroupOf (secH R u)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))) := by
  have hKH : tightCore (R.subgroupOf (Subgroup.centralizer ({u} : Set Y))) ≤ secH R u :=
    le_subnormalClosure _
  have hker : Odd (Nat.card (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))).ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.ComponentClassification.OddCore.odd_card ↥(secH R u)
  have h1 := tightCore_map_odd (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u))) hker
    ((R.subgroupOf (Subgroup.centralizer ({u} : Set Y))).subgroupOf (secH R u))
  rw [tightCore_subgroupOf hKH] at h1
  exact h1

theorem conjClass_tightCore_secR (R : Subgroup Y) (u : Y) :
    CoreAssembly.conjClass (tightCore (secR R u)) =
      quotFamily (CoreAssembly.conjClass
        ((tightCore (R.subgroupOf (Subgroup.centralizer ({u} : Set Y)))).subgroupOf (secH R u)))
        (classicalInvolutionOddCore ↥(secH R u)) := by
  rw [tightCore_secR]
  exact (image_conjClass _).symm

end Sec

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
