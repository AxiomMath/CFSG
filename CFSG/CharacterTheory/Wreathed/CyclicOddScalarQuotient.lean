module

public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.GroupTheory.PCore.Defs

public noncomputable section

namespace CFSG.Wreathed.CyclicOddScalarQuotient

open scoped Nat

variable (A : Type*) [Group A] [IsMulCommutative A]

@[expose] def oddElements : Subgroup A where
  carrier := {a | Odd (orderOf a)}
  one_mem' := by
    change Odd (orderOf (1 : A))
    rw [orderOf_one]
    exact odd_one
  mul_mem' := by
    intro a b ha hb
    have hab : Commute a b := mul_comm' a b
    exact Odd.of_dvd_nat (ha.mul hb)
      (hab.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd_mul _ _))
  inv_mem' := by
    intro a ha
    change Odd (orderOf a⁻¹)
    rw [orderOf_inv]
    exact ha

theorem mem_oddElements {A : Type*} [Group A] [IsMulCommutative A] {a : A} :
    a ∈ oddElements A ↔ Odd (orderOf a) := Iff.rfl

theorem oddElements_characteristic : (oddElements A).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro e
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [mem_oddElements, orderOf_injective e.toMonoidHom e.injective]
    exact hb
  · intro ha
    refine Subgroup.mem_map.mpr ⟨e.symm a, ?_, e.apply_symm_apply a⟩
    change Odd (orderOf (e.symm.toMonoidHom a))
    rw [orderOf_injective e.symm.toMonoidHom e.symm.injective]
    exact ha

theorem oddElements_le_center : oddElements A ≤ Subgroup.center A := by
  rw [Subgroup.center_eq_top]
  exact le_top

theorem oddElements_odd_card [Finite A] : Odd (Nat.card (oddElements A)) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := oddElements A) 2 heven.two_dvd
  have ho : Odd (orderOf a) := by
    rw [← Subgroup.orderOf_coe]
    exact a.property
  rw [ha] at ho
  exact Nat.not_even_iff_odd.mpr ho even_two

variable [Finite A] [IsCyclic A]

omit [Finite A] in
theorem oddElements_isCyclic : IsCyclic (oddElements A) := inferInstance

theorem oddElements_card : Nat.card (oddElements A) = ordCompl[2] (Nat.card A) := by
  have hodd := oddElements_odd_card A
  have hdiv : Nat.card (oddElements A) ∣ ordCompl[2] (Nat.card A) :=
    Nat.dvd_ordCompl_of_dvd_not_dvd (Subgroup.card_subgroup_dvd_card (oddElements A))
      (by simpa only [even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hodd)
  have hn : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hm : Odd (ordCompl[2] (Nat.card A)) :=
    Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two hn)
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
  have hb : orderOf (a ^ ordProj[2] (Nat.card A)) = ordCompl[2] (Nat.card A) := by
    rw [orderOf_pow_of_dvd (Nat.ordProj_pos _ _).ne' (by
      rw [ha]
      exact Nat.ordProj_dvd _ _), ha]
  let b : oddElements A := ⟨a ^ ordProj[2] (Nat.card A), by rw [mem_oddElements, hb]; exact hm⟩
  have hlow : ordCompl[2] (Nat.card A) ≤ Nat.card (oddElements A) := by
    have hl := orderOf_le_card (x := b)
    rw [← Subgroup.orderOf_coe] at hl
    exact hb ▸ hl
  exact le_antisymm (Nat.le_of_dvd (Nat.ordCompl_pos 2 hn) hdiv) hlow

variable {B H : Type*} [Group B] [Group H]

theorem oddCore_odd_card [Finite H] : Odd (Nat.card (CFSG.oddCore H)) :=
  CFSG.ComponentClassification.OddCore.odd_card H

theorem le_oddCore_of_normal_odd (R : Subgroup H)
    (hR : R.Normal) (hodd : Odd (Nat.card R)) : R ≤ CFSG.oddCore H :=
  le_sSup ⟨hR, hodd⟩

theorem card_comap_of_surjective (phi : B →* H)
    (hphi : Function.Surjective phi) (R : Subgroup H) :
    Nat.card (R.comap phi) = Nat.card phi.ker * Nat.card R := by
  have hle : phi.ker ≤ R.comap phi := Subgroup.ker_le_comap phi R
  have hmap : (R.comap phi).map phi = R :=
    Subgroup.map_comap_eq_self_of_surjective hphi R
  have hmul := (phi.ker.subgroupOf (R.comap phi)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hmul
  change Nat.card phi.ker * phi.ker.relIndex (R.comap phi) = Nat.card (R.comap phi)
    at hmul
  rw [Subgroup.relIndex_ker, hmap] at hmul
  exact hmul.symm

theorem comap_odd_card (phi : B →* H) (hphi : Function.Surjective phi)
    (hker : Odd (Nat.card phi.ker)) (R : Subgroup H) (hR : Odd (Nat.card R)) :
    Odd (Nat.card (R.comap phi)) := by
  rw [card_comap_of_surjective phi hphi R]
  exact hker.mul hR

theorem map_le_center_of_surjective (phi : B →* H) (hphi : Function.Surjective phi)
    (R : Subgroup B) (hR : R ≤ Subgroup.center B) : R.map phi ≤ Subgroup.center H := by
  rintro _ ⟨r, hr, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨b, rfl⟩ := hphi y
  exact (map_mul phi b r).symm.trans
    ((congrArg phi (Subgroup.mem_center_iff.mp (hR hr) b)).trans (map_mul phi r b))

section ScalarQuotient
variable {A} {B H : Type*} [Group B] [Group H]

omit [Finite A] [IsCyclic A] in
theorem odd_subgroup_le_oddScalarImage (kappa : A →* B)
    (hkappa : Function.Injective kappa) (R : Subgroup B)
    (hRodd : Odd (Nat.card R)) (hR : R ≤ kappa.range) :
    R ≤ (oddElements A).map kappa := by
  intro b hb
  obtain ⟨a, rfl⟩ := hR hb
  refine Subgroup.mem_map.mpr ⟨a, ?_, rfl⟩
  have ha : Odd (orderOf (kappa a)) :=
    hRodd.of_dvd_nat (R.orderOf_dvd_natCard hb)
  rw [mem_oddElements]
  simpa only [orderOf_injective kappa hkappa a] using ha

omit [Finite A] [IsCyclic A] in
theorem ker_le_oddScalarImage (kappa : A →* B) (hkappa : Function.Injective kappa)
    (phi : B →* H) (hkerodd : Odd (Nat.card phi.ker)) (hker : phi.ker ≤ kappa.range) :
    phi.ker ≤ (oddElements A).map kappa :=
  odd_subgroup_le_oddScalarImage kappa hkappa phi.ker hkerodd hker

omit [Finite A] [IsCyclic A] in
theorem oddScalarImage_le_center (kappa : A →* B)
    (hcenter : kappa.range ≤ Subgroup.center B) :
    (oddElements A).map kappa ≤ Subgroup.center B :=
  (Subgroup.map_le_range _ _).trans hcenter

variable [Finite B] [Finite H]

omit [Finite A] [IsCyclic A] [Finite H] in
theorem card_map_of_ker_le (phi : B →* H) (L : Subgroup B) (hL : phi.ker ≤ L) :
    Nat.card (L.map phi) = Nat.card L / Nat.card phi.ker := by
  have hmul := (phi.ker.subgroupOf L).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL).toEquiv] at hmul
  change Nat.card phi.ker * phi.ker.relIndex L = Nat.card L at hmul
  rw [Subgroup.relIndex_ker] at hmul
  rw [← hmul, Nat.mul_div_cancel_left _ Nat.card_pos]

omit [Finite H] in
theorem oddScalarQuotient_card (kappa : A →* B) (hkappa : Function.Injective kappa)
    (phi : B →* H) (hkerodd : Odd (Nat.card phi.ker)) (hker : phi.ker ≤ kappa.range) :
    Nat.card (((oddElements A).map kappa).map phi) =
      ordCompl[2] (Nat.card A) / Nat.card phi.ker := by
  rw [card_map_of_ker_le phi _ (ker_le_oddScalarImage kappa hkappa phi hkerodd hker),
    Subgroup.card_map_of_injective hkappa, oddElements_card]

theorem quotient_oddCore_eq (kappa : A →* B) (hkappa : Function.Injective kappa)
    (hcenter : kappa.range ≤ Subgroup.center B) (phi : B →* H)
    (hphi : Function.Surjective phi) (hkerodd : Odd (Nat.card phi.ker))
    (hker : phi.ker ≤ kappa.range)
    (hnormal : ∀ R : Subgroup B, R.Normal → Odd (Nat.card R) → R ≤ kappa.range) :
    CFSG.oddCore H = ((oddElements A).map kappa).map phi := by
  let R := CFSG.oddCore H
  let P := R.comap phi
  have hPodd : Odd (Nat.card P) :=
    comap_odd_card phi hphi hkerodd R oddCore_odd_card
  have hPnormal : P.Normal := Subgroup.Normal.comap inferInstance phi
  have hPscalar : P ≤ (oddElements A).map kappa :=
    odd_subgroup_le_oddScalarImage kappa hkappa P hPodd (hnormal P hPnormal hPodd)
  have hmap : P.map phi = R := Subgroup.map_comap_eq_self_of_surjective hphi R
  have hkdiv : Nat.card phi.ker ∣ ordCompl[2] (Nat.card A) := by
    have hd := Subgroup.card_dvd_of_le
      (ker_le_oddScalarImage kappa hkappa phi hkerodd hker)
    simpa only [Subgroup.card_map_of_injective hkappa, oddElements_card] using hd
  have hqodd : Odd (ordCompl[2] (Nat.card A) / Nat.card phi.ker) :=
    (Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two Nat.card_pos.ne')).of_dvd_nat
      (Nat.div_dvd_of_dvd hkdiv)
  apply le_antisymm
  · change R ≤ _
    rw [← hmap]
    exact Subgroup.map_mono hPscalar
  · apply le_oddCore_of_normal_odd
    · exact Subgroup.normal_of_le_center
        (map_le_center_of_surjective phi hphi _ (oddScalarImage_le_center kappa hcenter))
    · rw [oddScalarQuotient_card kappa hkappa phi hkerodd hker]
      exact hqodd

omit [Finite A] [IsCyclic A] [Finite B] [Finite H] in
theorem oddScalarQuotient_le_center (kappa : A →* B)
    (hcenter : kappa.range ≤ Subgroup.center B) (phi : B →* H)
    (hphi : Function.Surjective phi) :
    ((oddElements A).map kappa).map phi ≤ Subgroup.center H :=
  map_le_center_of_surjective phi hphi _ (oddScalarImage_le_center kappa hcenter)

theorem quotient_oddCore_le_center (kappa : A →* B) (hkappa : Function.Injective kappa)
    (hcenter : kappa.range ≤ Subgroup.center B) (phi : B →* H)
    (hphi : Function.Surjective phi) (hkerodd : Odd (Nat.card phi.ker))
    (hker : phi.ker ≤ kappa.range)
    (hnormal : ∀ R : Subgroup B, R.Normal → Odd (Nat.card R) → R ≤ kappa.range) :
    CFSG.oddCore H ≤ Subgroup.center H := by
  rw [quotient_oddCore_eq kappa hkappa hcenter phi hphi hkerodd hker hnormal]
  exact oddScalarQuotient_le_center kappa hcenter phi hphi

omit [Finite A] [Finite B] [Finite H] in
theorem oddScalarQuotient_isCyclic (kappa : A →* B) (phi : B →* H) :
    IsCyclic (((oddElements A).map kappa).map phi) := by
  let : IsCyclic ((oddElements A).map kappa) :=
    isCyclic_of_surjective (kappa.subgroupMap (oddElements A))
      (kappa.subgroupMap_surjective (oddElements A))
  exact isCyclic_of_surjective (phi.subgroupMap ((oddElements A).map kappa))
    (phi.subgroupMap_surjective ((oddElements A).map kappa))

theorem quotient_oddCore_isCyclic (kappa : A →* B) (hkappa : Function.Injective kappa)
    (hcenter : kappa.range ≤ Subgroup.center B) (phi : B →* H)
    (hphi : Function.Surjective phi) (hkerodd : Odd (Nat.card phi.ker))
    (hker : phi.ker ≤ kappa.range)
    (hnormal : ∀ R : Subgroup B, R.Normal → Odd (Nat.card R) → R ≤ kappa.range) :
    IsCyclic (CFSG.oddCore H) := by
  rw [quotient_oddCore_eq kappa hkappa hcenter phi hphi hkerodd hker hnormal]
  exact oddScalarQuotient_isCyclic kappa phi

theorem quotient_oddCore_card (kappa : A →* B) (hkappa : Function.Injective kappa)
    (hcenter : kappa.range ≤ Subgroup.center B) (phi : B →* H)
    (hphi : Function.Surjective phi) (hkerodd : Odd (Nat.card phi.ker))
    (hker : phi.ker ≤ kappa.range)
    (hnormal : ∀ R : Subgroup B, R.Normal → Odd (Nat.card R) → R ≤ kappa.range) :
    Nat.card (CFSG.oddCore H) = ordCompl[2] (Nat.card A) / Nat.card phi.ker := by
  rw [quotient_oddCore_eq kappa hkappa hcenter phi hphi hkerodd hker hnormal]
  exact oddScalarQuotient_card kappa hkappa phi hkerodd hker

theorem mem_quotient_oddCore_iff (kappa : A →* B) (hkappa : Function.Injective kappa)
    (hcenter : kappa.range ≤ Subgroup.center B) (phi : B →* H)
    (hphi : Function.Surjective phi) (hkerodd : Odd (Nat.card phi.ker))
    (hker : phi.ker ≤ kappa.range)
    (hnormal : ∀ R : Subgroup B, R.Normal → Odd (Nat.card R) → R ≤ kappa.range) {h : H} :
    h ∈ CFSG.oddCore H ↔ ∃ a : A, Odd (orderOf a) ∧ phi (kappa a) = h := by
  rw [quotient_oddCore_eq kappa hkappa hcenter phi hphi hkerodd hker hnormal]
  constructor
  · rintro ⟨b, ⟨a, ha, rfl⟩, heq⟩
    exact ⟨a, ha, heq⟩
  · rintro ⟨a, ha, heq⟩
    exact Subgroup.mem_map.mpr ⟨kappa a, Subgroup.mem_map.mpr ⟨a, ha, rfl⟩, heq⟩

theorem quotient_oddCore_structure (kappa : A →* B) (hkappa : Function.Injective kappa)
    (hcenter : kappa.range ≤ Subgroup.center B) (phi : B →* H)
    (hphi : Function.Surjective phi) (hkerodd : Odd (Nat.card phi.ker))
    (hker : phi.ker ≤ kappa.range)
    (hnormal : ∀ R : Subgroup B, R.Normal → Odd (Nat.card R) → R ≤ kappa.range) :
    CFSG.oddCore H = ((oddElements A).map kappa).map phi ∧
      CFSG.oddCore H ≤ Subgroup.center H ∧ IsCyclic (CFSG.oddCore H) ∧
      Nat.card (CFSG.oddCore H) = ordCompl[2] (Nat.card A) / Nat.card phi.ker :=
  ⟨quotient_oddCore_eq kappa hkappa hcenter phi hphi hkerodd hker hnormal,
    quotient_oddCore_le_center kappa hkappa hcenter phi hphi hkerodd hker hnormal,
    quotient_oddCore_isCyclic kappa hkappa hcenter phi hphi hkerodd hker hnormal,
    quotient_oddCore_card kappa hkappa hcenter phi hphi hkerodd hker hnormal⟩

omit [IsMulCommutative A] [Finite A] [IsCyclic A] [Finite B] [Finite H] in
@[expose] def scalarKernelEquiv (kappa : A →* B) (hkappa : Function.Injective kappa)
    (phi : B →* H) (D : Subgroup A) (hD : D.map kappa = phi.ker) : D ≃* phi.ker :=
  MulEquiv.ofBijective ((kappa.comp D.subtype).codRestrict phi.ker (by
    intro a
    rw [← hD]
    exact Subgroup.mem_map.mpr ⟨a, a.property, rfl⟩)) (by
      constructor
      · intro a b hab
        exact Subtype.ext (hkappa (congrArg Subtype.val hab))
      · intro b
        have hb : (b : B) ∈ D.map kappa := by
          simpa only [hD] using b.property
        obtain ⟨a, ha, hab⟩ := hb
        exact ⟨⟨a, ha⟩, Subtype.ext hab⟩)

omit [IsMulCommutative A] [Finite A] [IsCyclic A] [Finite B] [Finite H] in
theorem scalarKernelEquiv_apply (kappa : A →* B) (hkappa : Function.Injective kappa)
    (phi : B →* H) (D : Subgroup A) (hD : D.map kappa = phi.ker) (a : D) :
    (scalarKernelEquiv kappa hkappa phi D hD a : B) = kappa a := rfl

omit [IsMulCommutative A] [Finite A] [IsCyclic A] [Finite B] [Finite H] in
theorem scalarKernel_card (kappa : A →* B) (hkappa : Function.Injective kappa)
    (phi : B →* H) (D : Subgroup A) (hD : D.map kappa = phi.ker) :
    Nat.card phi.ker = Nat.card D :=
  (Nat.card_congr (scalarKernelEquiv kappa hkappa phi D hD).toEquiv).symm

theorem quotient_oddCore_structure_of_scalarKernel (kappa : A →* B)
    (hkappa : Function.Injective kappa) (hcenter : kappa.range ≤ Subgroup.center B)
    (phi : B →* H) (hphi : Function.Surjective phi) (D : Subgroup A)
    (hDodd : Odd (Nat.card D)) (hD : D.map kappa = phi.ker)
    (hnormal : ∀ R : Subgroup B, R.Normal → Odd (Nat.card R) → R ≤ kappa.range) :
    CFSG.oddCore H = ((oddElements A).map kappa).map phi ∧
      CFSG.oddCore H ≤ Subgroup.center H ∧ IsCyclic (CFSG.oddCore H) ∧
      Nat.card (CFSG.oddCore H) = ordCompl[2] (Nat.card A) / Nat.card D := by
  have hc := scalarKernel_card kappa hkappa phi D hD
  have ho : Odd (Nat.card phi.ker) := hc ▸ hDodd
  have hker : phi.ker ≤ kappa.range := by
    rw [← hD]
    exact Subgroup.map_le_range _ _
  simpa only [hc] using
    quotient_oddCore_structure kappa hkappa hcenter phi hphi ho hker hnormal

end ScalarQuotient
end CFSG.Wreathed.CyclicOddScalarQuotient
