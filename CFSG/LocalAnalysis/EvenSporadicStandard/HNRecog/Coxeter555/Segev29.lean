module

public import Certificates.Certificate442151

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Coxeter555

open CFSG.CosetTable

abbrev P555 : Type := PG 3 rels555

theorem card_P555_le : Finite P555 ∧ Nat.card P555 ≤ 660 :=
  Certificates.certificate442151

def permA : Equiv.Perm (Fin 11) :=
  Function.Involutive.toPerm ![0, 2, 1, 5, 7, 3, 8, 4, 6, 9, 10]
    (by unfold Function.Involutive; decide)

def permX : Equiv.Perm (Fin 11) :=
  Function.Involutive.toPerm ![1, 0, 3, 2, 6, 5, 4, 7, 10, 9, 8]
    (by unfold Function.Involutive; decide)

def permY : Equiv.Perm (Fin 11) :=
  Function.Involutive.toPerm ![0, 1, 4, 6, 2, 5, 3, 9, 10, 7, 8]
    (by unfold Function.Involutive; decide)

def gens : Fin 3 → Equiv.Perm (Fin 11) := ![permA, permX, permY]

theorem gens_rels : ∀ r ∈ rels555, FreeGroup.lift gens (FreeGroup.mk r) = 1 := by
  simp only [FreeGroup.lift_mk]
  decide +kernel

def psi : P555 →* Equiv.Perm (Fin 11) :=
  PresentedGroup.toGroup (f := gens) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact gens_rels w hw

abbrev la : P555 := PresentedGroup.of 0

abbrev lx : P555 := PresentedGroup.of 1

abbrev ly : P555 := PresentedGroup.of 2

def lw : P555 := la * ly * la * ly * la * lx * la * lx * ly

theorem psi_la : psi la = permA := PresentedGroup.toGroup.of _

theorem psi_lx : psi lx = permX := PresentedGroup.toGroup.of _

theorem psi_ly : psi ly = permY := PresentedGroup.toGroup.of _

theorem psi_lw :
    psi lw = permA * permY * permA * permY * permA * permX * permA * permX * permY := by
  simp only [lw, map_mul, psi_la, psi_lx, psi_ly]

def kleinList : List (Equiv.Perm (Fin 11)) := [1, permX, permY, permX * permY]

theorem mem_kleinList {g : Equiv.Perm (Fin 11)} :
    g ∈ kleinList ↔ g = 1 ∨ g = permX ∨ g = permY ∨ g = permX * permY := by
  simp [kleinList]

def klein : Subgroup (Equiv.Perm (Fin 11)) where
  carrier := {g | g ∈ kleinList}
  mul_mem' {g h} hg hh := by
    show g * h ∈ kleinList
    rcases mem_kleinList.1 hg with rfl | rfl | rfl | rfl <;>
      rcases mem_kleinList.1 hh with rfl | rfl | rfl | rfl <;> decide +kernel
  one_mem' := List.mem_cons_self ..
  inv_mem' {g} hg := by
    show g⁻¹ ∈ kleinList
    rcases mem_kleinList.1 hg with rfl | rfl | rfl | rfl <;> decide +kernel

theorem card_klein : Nat.card klein = 4 := by
  have hnd : kleinList.Nodup := by decide +kernel
  have h : Nat.card klein = Nat.card kleinList.toFinset :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g => List.mem_toFinset.symm)
  rw [h, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hnd]
  rfl

theorem klein_le_range : klein ≤ psi.range := by
  intro g hg
  have hg' : g ∈ kleinList := hg
  simp only [kleinList, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact ⟨lx, psi_lx⟩
  · exact ⟨ly, psi_ly⟩
  · exact ⟨lx * ly, by rw [map_mul, psi_lx, psi_ly]⟩

theorem le_card_range_psi : 660 ≤ Nat.card psi.range := by
  have h4 : 4 ∣ Nat.card psi.range := by
    have h := Subgroup.card_dvd_of_le klein_le_range
    rwa [card_klein] at h
  have h3 : 3 ∣ Nat.card psi.range := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hmem : (permA * permX * permA * permY) ^ 2 ∈ psi.range :=
      ⟨(la * lx * la * ly) ^ 2, by rw [map_pow, map_mul, map_mul, map_mul, psi_la, psi_lx, psi_ly]⟩
    have hord : orderOf ((permA * permX * permA * permY) ^ 2) = 3 :=
      orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    have h := Subgroup.orderOf_dvd_natCard _ hmem
    rwa [hord] at h
  have h5 : 5 ∣ Nat.card psi.range := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hmem : permA * permX ∈ psi.range := ⟨la * lx, by rw [map_mul, psi_la, psi_lx]⟩
    have hord : orderOf (permA * permX) = 5 :=
      orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    have h := Subgroup.orderOf_dvd_natCard _ hmem
    rwa [hord] at h
  have h11 : 11 ∣ Nat.card psi.range := by
    haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    have hmem : psi lw ∈ psi.range := ⟨lw, rfl⟩
    have hord : orderOf (psi lw) = 11 := by
      rw [psi_lw]
      exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    have h := Subgroup.orderOf_dvd_natCard _ hmem
    rwa [hord] at h
  have h12 : 12 ∣ Nat.card psi.range := by
    simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 3) h4 h3
  have h60 : 60 ∣ Nat.card psi.range := by
    simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 12 5) h12 h5
  have h660 : 660 ∣ Nat.card psi.range := by
    simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 60 11) h60 h11
  exact Nat.le_of_dvd Nat.card_pos h660

theorem psi_injective : Function.Injective psi := by
  obtain ⟨hfin, hcard⟩ := card_P555_le
  have hbij := psi.rangeRestrict_surjective.bijective_of_nat_card_le
    (hcard.trans le_card_range_psi)
  intro g h hgh
  exact hbij.1 (Subtype.ext hgh)

theorem lw_pow_eleven : lw ^ 11 = 1 :=
  psi_injective (by rw [map_pow, psi_lw, map_one]; decide +kernel)

theorem conj_lw : la * lx * lw * (la * lx)⁻¹ = lw ^ 9 :=
  psi_injective (by
    simp only [map_mul, map_inv, map_pow, psi_lw, psi_la, psi_lx]
    decide +kernel)

theorem ly_eq : ly = lw⁻¹ ^ 3 * la * lw ^ 3 :=
  psi_injective (by
    simp only [map_mul, map_inv, map_pow, psi_lw, psi_la, psi_ly]
    decide +kernel)

theorem segev29_unfolded (H : Type*) [Group H] (a x y : H)
    (ha : orderOf a = 2) (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x * y = y * x)
    (hax : orderOf (a * x) = 5) (hay : orderOf (a * y) = 5)
    (haxy : orderOf (a * (x * y)) = 5) :
    ∃ ω : H, orderOf ω = 11 ∧ ω ∈ Subgroup.closure {a, x, y} ∧
      (a * x) * ω * (a * x)⁻¹ ∈ Subgroup.zpowers ω ∧
      Subgroup.closure {a, x, ω} = Subgroup.closure {a, x, y} := by
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hy2 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hax5 : (a * x) ^ 5 = 1 := by rw [← hax]; exact pow_orderOf_eq_one _
  have hay5 : (a * y) ^ 5 = 1 := by rw [← hay]; exact pow_orderOf_eq_one _
  have haxy5 : (a * (x * y)) ^ 5 = 1 := by rw [← haxy]; exact pow_orderOf_eq_one _
  have hxx : x * x = 1 := by rw [← sq]; exact hx2
  have hyy : y * y = 1 := by rw [← sq]; exact hy2
  have hxy2 : (x * y) ^ 2 = 1 := by
    rw [sq, mul_assoc, ← mul_assoc y x y, ← hxy, mul_assoc, hyy, mul_one, hxx]
  have hrel : ∀ r ∈ rels555, FreeGroup.lift ![a, x, y] (FreeGroup.mk r) = 1 := by
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · simpa [FreeGroup.lift_mk, sq] using ha2
    rcases List.mem_cons.1 hr with rfl | hr
    · simpa [FreeGroup.lift_mk, sq] using hx2
    rcases List.mem_cons.1 hr with rfl | hr
    · simpa [FreeGroup.lift_mk, sq] using hy2
    rcases List.mem_cons.1 hr with rfl | hr
    · simpa [FreeGroup.lift_mk, sq, mul_assoc] using hxy2
    rcases List.mem_cons.1 hr with rfl | hr
    · rw [mk_flatten_replicate, map_pow]
      simpa [FreeGroup.lift_mk, axWord] using hax5
    rcases List.mem_cons.1 hr with rfl | hr
    · rw [mk_flatten_replicate, map_pow]
      simpa [FreeGroup.lift_mk] using hay5
    rcases List.mem_cons.1 hr with rfl | hr
    · rw [mk_flatten_replicate, map_pow]
      simpa [FreeGroup.lift_mk] using haxy5
    exact absurd hr List.not_mem_nil
  let φ : P555 →* H := PresentedGroup.toGroup (f := ![a, x, y]) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact hrel w hw
  have φa : φ la = a := PresentedGroup.toGroup.of _
  have φx : φ lx = x := PresentedGroup.toGroup.of _
  have φy : φ ly = y := PresentedGroup.toGroup.of _
  obtain ⟨ω, hω⟩ : ∃ ω : H, ω = a * y * a * y * a * x * a * x * y := ⟨_, rfl⟩
  have φw : φ lw = ω := by simp only [lw, map_mul, φa, φx, φy, hω]
  have h11 : ω ^ 11 = 1 := by rw [← φw, ← map_pow, lw_pow_eleven, map_one]
  have hconj : (a * x) * ω * (a * x)⁻¹ = ω ^ 9 := by
    have h := congrArg φ conj_lw
    simpa only [map_mul, map_inv, map_pow, φa, φx, φw] using h
  have hyω : y = ω⁻¹ ^ 3 * a * ω ^ 3 := by
    have h := congrArg φ ly_eq
    simpa only [map_mul, map_inv, map_pow, φa, φy, φw] using h
  have hω1 : ω ≠ 1 := by
    intro h1
    rw [h1, inv_one, one_pow, one_mul, mul_one] at hyω
    rw [hyω, ← sq, ha2, orderOf_one] at hay
    norm_num at hay
  have hord : orderOf ω = 11 := by
    haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact orderOf_eq_prime h11 hω1
  have ha' : a ∈ Subgroup.closure ({a, x, y} : Set H) := Subgroup.subset_closure (by simp)
  have hx' : x ∈ Subgroup.closure ({a, x, y} : Set H) := Subgroup.subset_closure (by simp)
  have hy' : y ∈ Subgroup.closure ({a, x, y} : Set H) := Subgroup.subset_closure (by simp)
  have hωmem : ω ∈ Subgroup.closure ({a, x, y} : Set H) := by
    rw [hω]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ha' hy') ha')
      hy') ha') hx') ha') hx') hy'
  have ha'' : a ∈ Subgroup.closure ({a, x, ω} : Set H) := Subgroup.subset_closure (by simp)
  have hx'' : x ∈ Subgroup.closure ({a, x, ω} : Set H) := Subgroup.subset_closure (by simp)
  have hω'' : ω ∈ Subgroup.closure ({a, x, ω} : Set H) := Subgroup.subset_closure (by simp)
  have hy'' : y ∈ Subgroup.closure ({a, x, ω} : Set H) := by
    rw [hyω]
    exact mul_mem (mul_mem (pow_mem (inv_mem hω'') 3) ha'') (pow_mem hω'' 3)
  refine ⟨ω, hord, hωmem, ?_, le_antisymm ?_ ?_⟩
  · rw [hconj]
    exact Subgroup.npow_mem_zpowers ω 9
  · rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl | rfl
    exacts [ha', hx', hωmem]
  · rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl | rfl
    exacts [ha'', hx'', hy'']

end CFSG.EvenSporadicStandard.HNRecog.Coxeter555
