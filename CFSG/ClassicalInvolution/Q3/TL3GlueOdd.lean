module

public import CFSG.ClassicalInvolution.Q3.TL3GoodLift
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAGrp
public import CFSG.ClassicalInvolution.Q3.TL3TopRestrict

public section

namespace CFSG.ClassicalInvolution.Q3.OddQ

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Basic

theorem commutatorElement_pow_mem {G : Type*} [Group G] {O : Subgroup G} {x y : G}
    (hxO : ∀ u ∈ O, x * u * x⁻¹ ∈ O) (h : ⁅x, y⁆ ∈ O) (j : ℕ) : ⁅x ^ j, y⁆ ∈ O := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : ⁅x ^ (j + 1), y⁆ = (x * ⁅x ^ j, y⁆ * x⁻¹) * ⁅x, y⁆ := by
      rw [pow_succ', commutatorElement_def, commutatorElement_def, commutatorElement_def]
      group
    rw [e]
    exact O.mul_mem (hxO _ ih) h

variable {Y : Type} [Group Y] [Finite Y]

theorem oddCoreImg_map_le {Y' : Type} [Group Y'] (f : Y →* Y') (R : Subgroup Y) :
    (oddCoreImg R).map f ≤ oddCoreImg (R.map f) := by
  rintro _ ⟨_, ⟨o, ho, rfl⟩, rfl⟩
  set g : R →* R.map f := f.subgroupMap R with hg
  have hgs : Function.Surjective g := f.subgroupMap_surjective R
  have hmap : (classicalInvolutionOddCore ↥R).map g ≤ classicalInvolutionOddCore ↥(R.map f) :=
    le_sSup ⟨(classicalInvolutionOddCore_normal ↥R).map g hgs,
      (CFSG.ComponentClassification.OddCore.odd_card ↥R).of_dvd_nat (Subgroup.card_map_dvd _ _)⟩
  exact ⟨g o, hmap ⟨o, ho, rfl⟩, rfl⟩

theorem comap_oddCore_le_of_odd {G H : Type} [Group G] [Group H] [Finite G] (f : G →* H)
    (hf : Function.Surjective f) (hk : Odd (Nat.card f.ker)) :
    (classicalInvolutionOddCore H).comap f ≤ classicalInvolutionOddCore G := by
  have : Finite H := Finite.of_surjective f hf
  have hMn : ((classicalInvolutionOddCore H).comap f).Normal :=
    (classicalInvolutionOddCore_normal H).comap f
  have hModd : Odd (Nat.card ((classicalInvolutionOddCore H).comap f)) := by
    refine Q3TIY.odd_natCard_of_forall_odd_orderOf _ fun x hx => ?_
    have h1 : Odd (orderOf (f x)) :=
      (CFSG.ComponentClassification.OddCore.odd_card H).of_dvd_nat
        (Subgroup.orderOf_dvd_natCard _ hx)
    have h2 : x ^ orderOf (f x) ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
    have h3 : (x ^ orderOf (f x)) ^ Nat.card f.ker = 1 := by
      have := congrArg Subtype.val (pow_card_eq_one' (G := f.ker) (x := ⟨_, h2⟩))
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have h4 : orderOf x ∣ orderOf (f x) * Nat.card f.ker :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact h3)
    exact (h1.mul hk).of_dvd_nat h4
  exact le_sSup ⟨hMn, hModd⟩

end Basic

variable {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
  {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem good_of (hd : TightDatum R S t) (hNodd : Odd (Nat.card ↥N))
    (h : GoodThreeElement (R.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N t)) :
    GoodThreeElement R t := by
  classical
  set π : Y →* Y ⧸ N := QuotientGroup.mk' N with hπ
  have ht2 : t * t = 1 := t_mul_t hd
  have hCbar := centralizer_mk_eq hNodd ht2
  have hd' := datum hd hNodd
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hC
  obtain ⟨xb, k, hxbC, hxb3, ⟨rb, hrb, hxr⟩, hD⟩ := h
  have hxbC' := hxbC
  rw [hCbar] at hxbC'
  obtain ⟨x, hxC, rfl⟩ := hxbC'
  obtain ⟨a, b, hb3, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 3 (by norm_num)
  set x' : Y := x ^ b with hx'
  have hx'3 : x' ^ 3 ^ a = 1 := by rw [hx', ← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
  have hx'C : x' ∈ C := C.pow_mem hxC b
  have hπx'C : π x' ∈ Subgroup.centralizer ({π t} : Set (Y ⧸ N)) := by
    rw [hCbar]
    exact Subgroup.mem_map_of_mem π hx'C
  have hcop : Nat.Coprime b (orderOf (π x)) := by
    have h1 : orderOf (π x) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hxb3
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    rw [hi]
    exact Nat.Coprime.pow_right i
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hb3))
  obtain ⟨j, hj⟩ : ∃ j : ℕ, π x = π x' ^ j := by
    by_cases h1 : orderOf (π x) = 1
    · exact ⟨0, by rw [pow_zero]; exact orderOf_eq_one_iff.mp h1⟩
    · have h1' : 1 < orderOf (π x) := lt_of_le_of_ne (orderOf_pos _) (Ne.symm h1)
      obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1'
      refine ⟨m, ?_⟩
      rw [hx', map_pow, ← pow_mul, ← pow_mod_orderOf, hm, pow_one]
  have hπO : ∀ w ∈ oddCoreImg R, π w ∈ oddCoreImg (R.map π) := fun w hw =>
    oddCoreImg_map_le π R ⟨w, hw, rfl⟩
  refine ⟨x', a, hx'C, hx'3, ?_, ?_⟩
  ·
    by_contra hcon
    push Not at hcon
    apply hxr
    obtain ⟨r, hr, rfl⟩ := hrb
    have h1 : ⁅π x', π r⁆ ∈ oddCoreImg (R.map π) := by
      rw [← map_commutatorElement]
      exact hπO _ (hcon r hr)
    have hnorm : ∀ u ∈ oddCoreImg (R.map π), π x' * u * (π x')⁻¹ ∈ oddCoreImg (R.map π) :=
      fun u hu => conj_mem_oddCoreImg (hd'.le_normalizer hπx'C) hu
    rw [hj]
    exact commutatorElement_pow_mem hnorm h1 j
  ·
    intro y hyC hyR
    have hyb : π y ∈ Subgroup.centralizer ({π t} : Set (Y ⧸ N)) := by
      rw [hCbar]
      exact Subgroup.mem_map_of_mem π hyC
    have hyRb : ∀ rb ∈ R.map π, ⁅π y, rb⁆ ∈ oddCoreImg (R.map π) := by
      rintro _ ⟨r, hr, rfl⟩
      rw [← map_commutatorElement]
      exact hπO _ (hyR r hr)
    have hw := hD _ hyb hyRb
    have hw' : ⁅π x', π y⁆ ∈ oddCoreImg (Subgroup.centralizer ({π t} : Set (Y ⧸ N))) := by
      rw [hx', map_pow]
      exact commutatorElement_pow_mem
        (fun u hu => conj_mem_oddCoreImg (Subgroup.le_normalizer hxbC) hu) hw b
    rw [← map_commutatorElement, hCbar] at hw'
    have hwC : ⁅x', y⁆ ∈ C := by
      rw [commutatorElement_def]
      exact C.mul_mem (C.mul_mem (C.mul_mem hx'C hyC) (C.inv_mem hx'C)) (C.inv_mem hyC)
    set f := π.subgroupMap C with hf
    have hfs : Function.Surjective f := π.subgroupMap_surjective C
    have hker : f.ker = N.subgroupOf C := by
      ext c
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h1
        exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1)
      · intro h1
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h1)
    have hkodd : Odd (Nat.card f.ker) := by
      rw [hker]
      have h1 : Nat.card (N.subgroupOf C) = Nat.card (N ⊓ C : Subgroup Y) := by
        rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective C.subtype_injective]
      rw [h1]
      exact hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have hle := comap_oddCore_le_of_odd f hfs hkodd
    obtain ⟨u, hu, hwu⟩ := hw'
    have hwmem : (⟨⁅x', y⁆, hwC⟩ : ↥C) ∈
        (classicalInvolutionOddCore ↥(C.map π)).comap f := by
      rw [Subgroup.mem_comap]
      have e : f ⟨_, hwC⟩ = u := Subtype.ext hwu.symm
      rw [e]
      exact hu
    exact ⟨_, hle hwmem, rfl⟩

end CFSG.ClassicalInvolution.Q3.OddQ

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TightDatum.good_of_subnormalClosure (hd : TightDatum R S t)
    {ht : t ∈ subnormalClosure (tightCore R)}
    {S' : Sylow 2 ↥(R.subgroupOf (subnormalClosure (tightCore R)))}
    (hd' : TightDatum (R.subgroupOf (subnormalClosure (tightCore R))) S' ⟨t, ht⟩)
    (hg : GoodThreeElement
      ((R.subgroupOf (subnormalClosure (tightCore R))).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(subnormalClosure (tightCore R)))))
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(subnormalClosure (tightCore R)))
        ⟨t, ht⟩)) :
    GoodThreeElement R t := by
  set H : Subgroup Y := subnormalClosure (tightCore R) with hH
  have hKH : tightCore R ≤ H := le_subnormalClosure _
  have hgH : GoodThreeElement (R.subgroupOf H) (⟨t, ht⟩ : H) :=
    OddQ.good_of hd' (CFSG.ComponentClassification.OddCore.odd_card ↥H) hg
  obtain ⟨L, hKL, hL⟩ := tightHasLift_of_good hd' hgH
  have hLY := isClassicalMember3_map_subnormal (isSubnormal_subnormalClosure _) hL
  refine hd.good_of_hasLift ⟨L.map H.subtype, ?_, hLY⟩
  rw [tightCore_subgroupOf hKH] at hKL
  have h1 := Subgroup.map_mono (f := H.subtype) hKL
  rwa [Subgroup.map_subgroupOf_eq_of_le hKH] at h1

end CFSG.ClassicalInvolution.Q3
