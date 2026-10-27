module
public import CFSG.CharacterTheory.Semidihedral.FixedFieldCentralizer

public noncomputable section
namespace CFSG.Wreathed.CentralTwoPowerFieldLift
universe u v
open CFSG.Semidihedral.OddFieldLift
open CFSG.Semidihedral.SemilinearOddExtensions
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.GorensteinWalter

open CFSG.Semidihedral

theorem odd_kernel_identity {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hK : IsPGroup 2 pi.ker) (d : ℕ) (hd : Odd d)
    {x : H} (hx : pi x = 1) (hxd : x ^ d = 1) : x = 1 := by
  let a : pi.ker := ⟨x, hx⟩
  have ha : a ^ d = 1 := Subtype.ext hxd
  have heq : (hK.powEquiv hd.coprime_two_left) a =
      (hK.powEquiv hd.coprime_two_left) 1 := by
    rw [IsPGroup.powEquiv_apply, IsPGroup.powEquiv_apply, ha, one_pow]
  exact congrArg Subtype.val ((hK.powEquiv hd.coprime_two_left).injective heq)

theorem exists_odd_order_lift {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (C : Subgroup Q) [Finite C] (hd : Odd (Nat.card C)) (a : C) :
    ∃ b : C.comap pi, (b : H) ^ Nat.card C = 1 ∧ pi b = a := by
  let d := Nat.card C
  obtain ⟨b, hb⟩ := preimageProjection_surjective pi hpi C a
  have hba : pi b = a := congrArg Subtype.val hb
  have hbd : (b : H) ^ d ∈ pi.ker := by
    change pi ((b : H) ^ d) = 1
    rw [map_pow, hba]
    exact congrArg Subtype.val (pow_card_eq_one' (x := a))
  let c : pi.ker := ⟨(b : H) ^ d, hbd⟩
  let k : pi.ker := (hK.powEquiv hd.coprime_two_left).symm c⁻¹
  have hk : (k : H) ^ d = ((b : H) ^ d)⁻¹ := by
    have h := (hK.powEquiv hd.coprime_two_left).apply_symm_apply c⁻¹
    rw [IsPGroup.powEquiv_apply] at h
    exact congrArg Subtype.val h
  have hkpi : pi k = 1 := k.property
  have hcomm : Commute (b : H) (k : H) :=
    Subgroup.mem_center_iff.mp (hcentral k.property) b
  let e : C.comap pi := ⟨(b : H) * (k : H), by
    change pi ((b : H) * (k : H)) ∈ C
    rw [map_mul, hkpi, mul_one, hba]
    exact a.property⟩
  refine ⟨e, ?_, ?_⟩
  · change ((b : H) * (k : H)) ^ d = 1
    rw [hcomm.mul_pow, hk, mul_inv_cancel]
  · change pi ((b : H) * (k : H)) = a
    rw [map_mul, hkpi, mul_one, hba]

theorem oddProjection_bijective {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (C : Subgroup Q) [Finite C] (hd : Odd (Nat.card C))
    (hB : IsMulCommutative (C.comap pi)) :
    Function.Bijective (oddProjection pi C hB) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hpi' : pi x = pi y := congrArg Subtype.val hxy
    have hk : pi ((x : H) * (y : H)⁻¹) = 1 := by
      rw [map_mul, map_inv, hpi', mul_inv_cancel]
    have hxd : ((x : H) * (y : H)⁻¹) ^ Nat.card C = 1 :=
      (oddRoots (C.comap pi) (Nat.card C) hB).mul_mem x.property
        ((oddRoots (C.comap pi) (Nat.card C) hB).inv_mem y.property) |>.2
    exact mul_inv_eq_one.mp (odd_kernel_identity pi hK (Nat.card C) hd hk hxd)
  · intro a
    obtain ⟨b, hbd, hba⟩ := exists_odd_order_lift pi hpi hcentral hK C hd a
    exact ⟨⟨b, b.property, hbd⟩, Subtype.ext hba⟩

@[expose] def oddProjectionEquiv {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (C : Subgroup Q) [Finite C] (hd : Odd (Nat.card C))
    (hB : IsMulCommutative (C.comap pi)) :
    oddRoots (C.comap pi) (Nat.card C) hB ≃* C :=
  MulEquiv.ofBijective (oddProjection pi C hB)
    (oddProjection_bijective pi hpi hcentral hK C hd hB)

theorem oddProjectionEquiv_coe {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (C : Subgroup Q) [Finite C] (hd : Odd (Nat.card C))
    (hB : IsMulCommutative (C.comap pi))
    (e : oddRoots (C.comap pi) (Nat.card C) hB) :
    (oddProjectionEquiv pi hpi hcentral hK C hd hB e : Q) = pi e := rfl

theorem oddRoots_card {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (C : Subgroup Q) [Finite C] (hd : Odd (Nat.card C))
    (hB : IsMulCommutative (C.comap pi)) :
    Nat.card (oddRoots (C.comap pi) (Nat.card C) hB) = Nat.card C :=
  Nat.card_congr (oddProjectionEquiv pi hpi hcentral hK C hd hB).toEquiv

theorem oddRoots_unique {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (C : Subgroup Q) [Finite C] (hd : Odd (Nat.card C))
    (hB : IsMulCommutative (C.comap pi))
    (U : Subgroup (C.comap pi)) (hU : Nat.card U = Nat.card C) :
    U = (oddRoots (C.comap pi) (Nat.card C) hB).subgroupOf (C.comap pi) := by
  have hE : oddRoots (C.comap pi) (Nat.card C) hB ≤ C.comap pi := fun _ h => h.1
  have hc : Nat.card ((oddRoots (C.comap pi) (Nat.card C) hB).subgroupOf
      (C.comap pi)) = Nat.card C :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv).trans
      (oddRoots_card pi hpi hcentral hK C hd hB)
  let : Finite ((oddRoots (C.comap pi) (Nat.card C) hB).subgroupOf (C.comap pi)) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Nat.card_pos.ne')
  let : Finite U := Nat.finite_of_card_ne_zero (hU ▸ Nat.card_pos.ne')
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    refine ⟨x.property, ?_⟩
    have h := congrArg (fun e : U => ((e : C.comap pi) : H))
      (pow_card_eq_one' (x := (⟨x, hx⟩ : U)))
    change (x : H) ^ Nat.card C = 1
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, hU] using h
  · rw [hc, hU]

theorem oddRoots_disjoint_kernel {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hK : IsPGroup 2 pi.ker)
    (C : Subgroup Q) (hd : Odd (Nat.card C))
    (hB : IsMulCommutative (C.comap pi)) :
    Disjoint pi.ker (oddRoots (C.comap pi) (Nat.card C) hB) := by
  apply disjoint_iff_inf_le.mpr
  rintro x ⟨hk, he⟩
  exact odd_kernel_identity pi hK (Nat.card C) hd hk he.2

theorem oddRoots_factorization {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (C : Subgroup Q) [Finite C] (hd : Odd (Nat.card C))
    (hB : IsMulCommutative (C.comap pi)) (b : C.comap pi) :
    ∃ k : pi.ker, ∃ e : oddRoots (C.comap pi) (Nat.card C) hB, (b : H) = k * e := by
  let a : C := ⟨pi b, b.property⟩
  let e := (oddProjectionEquiv pi hpi hcentral hK C hd hB).symm a
  have he : pi e = pi b := congrArg Subtype.val
    ((oddProjectionEquiv pi hpi hcentral hK C hd hB).apply_symm_apply a)
  have hk : (b : H) * (e : H)⁻¹ ∈ pi.ker := by
    change pi ((b : H) * (e : H)⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  exact ⟨⟨(b : H) * (e : H)⁻¹, hk⟩, e, by simp only [mul_assoc, inv_mul_cancel, mul_one]⟩

theorem oddRoots_isComplement {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (C : Subgroup Q) [Finite C] (hd : Odd (Nat.card C))
    (hB : IsMulCommutative (C.comap pi)) :
    (pi.ker.subgroupOf (C.comap pi)).IsComplement'
      ((oddRoots (C.comap pi) (Nat.card C) hB).subgroupOf (C.comap pi)) :=
  factorization_isComplement (C.comap pi) pi.ker (oddRoots (C.comap pi) (Nat.card C) hB)
    (pi.ker_le_comap C) (fun _ h => h.1)
    (oddRoots_disjoint_kernel pi hK C hd hB)
    (oddRoots_factorization pi hpi hcentral hK C hd hB)

theorem preimage_isComplement {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (N C : Subgroup Q) [Finite C] (hd : Odd (Nat.card C))
    (hB : IsMulCommutative (C.comap pi)) (hcomp : N.IsComplement' C) :
    (N.comap pi).IsComplement' (oddRoots (C.comap pi) (Nat.card C) hB) := by
  have hdis : Disjoint (N.comap pi) (oddRoots (C.comap pi) (Nat.card C) hB) := by
    apply disjoint_iff_inf_le.mpr
    rintro x ⟨hn, he⟩
    have hpi' : pi x = 1 := disjoint_iff_inf_le.mp hcomp.disjoint ⟨hn, he.1⟩
    exact odd_kernel_identity pi hK (Nat.card C) hd hpi' he.2
  refine ⟨Subgroup.mul_injective_of_disjoint hdis, ?_⟩
  intro x
  obtain ⟨⟨n, a⟩, hna⟩ := hcomp.2 (pi x)
  let e := (oddProjectionEquiv pi hpi hcentral hK C hd hB).symm a
  have he : pi e = a := congrArg Subtype.val
    ((oddProjectionEquiv pi hpi hcentral hK C hd hB).apply_symm_apply a)
  have hn : x * (e : H)⁻¹ ∈ N.comap pi := by
    change pi (x * (e : H)⁻¹) ∈ N
    rw [map_mul, map_inv, he, ← hna]
    rw [mul_assoc, mul_inv_cancel, mul_one]
    exact n.property
  exact ⟨(⟨x * (e : H)⁻¹, hn⟩, e), by simp only [mul_assoc, inv_mul_cancel, mul_one]⟩

theorem commute_of_quotient_commute_of_odd_power
    {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (d : ℕ) (hd : Odd d) (h e : H) (hed : e ^ d = 1)
    (hcomm : Commute (pi h) (pi e)) : Commute h e := by
  let delta : H := e⁻¹ * (h * e * h⁻¹)
  have hk : delta ∈ pi.ker := by
    change pi (e⁻¹ * (h * e * h⁻¹)) = 1
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, hcomm.eq]
    group
  have hc : Commute e delta := Subgroup.mem_center_iff.mp (hcentral hk) e
  have hfactor : e * delta = h * e * h⁻¹ := by dsimp [delta]; group
  have hconj : (h * e * h⁻¹) ^ d = 1 := by
    rw [conj_pow, hed]
    simp
  have hdelta : delta ^ d = 1 := by
    rw [← hfactor, hc.mul_pow, hed, one_mul] at hconj
    exact hconj
  have hone : delta = 1 := odd_kernel_identity pi hK d hd hk hdelta
  have hconje : h * e * h⁻¹ = e := by rw [← hfactor, hone, mul_one]
  exact (mul_inv_eq_iff_eq_mul.mp hconje)

theorem centralizer_eq_comap_image_centralizer
    {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (E : Subgroup H) (d : ℕ) (hd : Odd d) (hE : ∀ e : E, (e : H) ^ d = 1) :
    Subgroup.centralizer (E : Set H) = (Subgroup.centralizer ((E.map pi : Subgroup Q) : Set Q)).comap pi := by
  ext h
  constructor
  · intro hh
    apply Subgroup.mem_centralizer_iff.mpr
    rintro q ⟨e, he, rfl⟩
    simpa only [map_mul] using congrArg pi (Subgroup.mem_centralizer_iff.mp hh e he)
  · intro hh
    apply Subgroup.mem_centralizer_iff.mpr
    intro e he
    have hcomm : Commute (pi h) (pi e) :=
      (Subgroup.mem_centralizer_iff.mp hh (pi e) ⟨e, he, rfl⟩).symm
    exact (commute_of_quotient_commute_of_odd_power pi hcentral hK d hd h e
      (hE ⟨e, he⟩) hcomm).eq.symm

@[expose] def preimageDirectEquiv {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (C : Subgroup Q) [Finite C] (hd : Odd (Nat.card C))
    (hB : IsMulCommutative (C.comap pi)) :
    pi.ker × oddRoots (C.comap pi) (Nat.card C) hB ≃* C.comap pi := by
  let B := C.comap pi
  let E := oddRoots B (Nat.card C) hB
  have hE : E ≤ B := fun _ h => h.1
  have hcenter : pi.ker.subgroupOf B ≤ Subgroup.center B := by
    intro k hk
    apply Subgroup.mem_center_iff.mpr
    intro b
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcentral hk) b
  let toSubgroups := (Subgroup.subgroupOfEquivOfLe (pi.ker_le_comap C)).symm.prodCongr
    (Subgroup.subgroupOfEquivOfLe hE).symm
  exact toSubgroups.trans (internalDirectEquiv (pi.ker.subgroupOf B) (E.subgroupOf B)
    hcenter (oddRoots_isComplement pi hpi hcentral hK C hd hB))

theorem preimageDirectEquiv_coe {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (C : Subgroup Q) [Finite C] (hd : Odd (Nat.card C))
    (hB : IsMulCommutative (C.comap pi))
    (x : pi.ker × oddRoots (C.comap pi) (Nat.card C) hB) :
    (preimageDirectEquiv pi hpi hcentral hK C hd hB x : H) = (x.1 : H) * x.2 := rfl

@[expose] def preimageSemidirectEquiv {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (N C : Subgroup Q) [N.Normal] [Finite C] (hd : Odd (Nat.card C))
    (hB : IsMulCommutative (C.comap pi)) (hcomp : N.IsComplement' C) :
    N.comap pi ⋊[internalAction (N.comap pi) (oddRoots (C.comap pi) (Nat.card C) hB)]
      oddRoots (C.comap pi) (Nat.card C) hB ≃* H :=
  internalSemidirectEquiv _ _ (preimage_isComplement pi hpi hcentral hK N C hd hB hcomp)

theorem preimageSemidirectEquiv_apply {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (N C : Subgroup Q) [N.Normal] [Finite C] (hd : Odd (Nat.card C))
    (hB : IsMulCommutative (C.comap pi)) (hcomp : N.IsComplement' C)
    (x : N.comap pi ⋊[internalAction (N.comap pi) (oddRoots (C.comap pi) (Nat.card C) hB)]
      oddRoots (C.comap pi) (Nat.card C) hB) :
    preimageSemidirectEquiv pi hpi hcentral hK N C hd hB hcomp x = x.left * x.right :=
  internalSemidirectEquiv_apply _ _ _ x

theorem B_isMulCommutative {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hcentral : pi.ker ≤ Subgroup.center H) :
    IsMulCommutative (B F Sigma pi) := by
  let : IsCyclic (F ≃+* F) := fieldAut_isCyclic F
  let : IsCyclic (gammaField F Sigma) := (gammaFieldEquiv F Sigma).isCyclic.mpr inferInstance
  exact CFSG.Semidihedral.OddFieldLift.preimage_isMulCommutative pi hcentral (gammaField F Sigma)

@[expose] def E {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hcentral : pi.ker ≤ Subgroup.center H) : Subgroup H :=
  oddRoots (B F Sigma pi) (Nat.card Sigma) (B_isMulCommutative F Sigma pi hcentral)

theorem mem_E {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hcentral : pi.ker ≤ Subgroup.center H) (e : H) :
    e ∈ E F Sigma pi hcentral ↔ e ∈ B F Sigma pi ∧ e ^ Nat.card Sigma = 1 := Iff.rfl

@[expose] def piOnE {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) : E F Sigma pi hcentral ≃* gammaField F Sigma := by
  let hB := B_isMulCommutative F Sigma pi hcentral
  let e := oddProjectionEquiv pi hpi hcentral hK (gammaField F Sigma)
    ((gammaField_card F Sigma).symm ▸ hd) hB
  have heq : E F Sigma pi hcentral =
      oddRoots ((gammaField F Sigma).comap pi) (Nat.card (gammaField F Sigma)) hB := by
    unfold E
    rw [gammaField_card]
  exact (MulEquiv.subgroupCongr heq).trans e

theorem piOnE_coe {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) (e : E F Sigma pi hcentral) :
    (piOnE F Sigma pi hpi hcentral hK hd e : Gamma F Sigma) = pi e := rfl

@[expose] def EEquivField {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) : E F Sigma pi hcentral ≃* Sigma :=
  (piOnE F Sigma pi hpi hcentral hK hd).trans (gammaFieldEquiv F Sigma)

@[expose] def eSigma {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) (sigma : Sigma) : E F Sigma pi hcentral :=
  (EEquivField F Sigma pi hpi hcentral hK hd).symm sigma

theorem eSigma_projective {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) (sigma : Sigma) :
    coordinateProjection F Sigma pi (eSigma F Sigma pi hpi hcentral hK hd sigma) =
      fieldExtension F sigma := by
  have h : pi (eSigma F Sigma pi hpi hcentral hK hd sigma) =
      ((gammaFieldEquiv F Sigma).symm sigma : Gamma F Sigma) := congrArg Subtype.val
    ((piOnE F Sigma pi hpi hcentral hK hd).apply_symm_apply
      ((gammaFieldEquiv F Sigma).symm sigma))
  change (((pi (eSigma F Sigma pi hpi hcentral hK hd sigma) : Gamma F Sigma) :
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateE F) :
      Equiv.Perm (Omega F)) = _
  rw [h, gammaFieldEquiv_symm_coe]

theorem E_card {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) : Nat.card (E F Sigma pi hcentral) = Nat.card Sigma :=
  Nat.card_congr (EEquivField F Sigma pi hpi hcentral hK hd).toEquiv

theorem E_unique {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) (U : Subgroup (B F Sigma pi))
    (hU : Nat.card U = Nat.card Sigma) :
    U = (E F Sigma pi hcentral).subgroupOf (B F Sigma pi) := by
  apply oddRoots_unique pi hpi hcentral hK (gammaField F Sigma)
    ((gammaField_card F Sigma).symm ▸ hd) (B_isMulCommutative F Sigma pi hcentral) U
    (hU.trans (gammaField_card F Sigma).symm) |>.trans
  congr 1
  unfold E
  rw [gammaField_card]

theorem H_isComplement {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) :
    (M F Sigma pi).IsComplement' (E F Sigma pi hcentral) := by
  have h := preimage_isComplement pi hpi hcentral hK (gammaLinear F Sigma) (gammaField F Sigma)
    ((gammaField_card F Sigma).symm ▸ hd) (B_isMulCommutative F Sigma pi hcentral)
    (gamma_isComplement F Sigma)
  unfold E
  rwa [gammaField_card] at h

@[expose] def HSemidirectEquiv {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) :
    M F Sigma pi ⋊[internalAction (M F Sigma pi) (E F Sigma pi hcentral)]
      E F Sigma pi hcentral ≃* H :=
  internalSemidirectEquiv _ _ (H_isComplement F Sigma pi hpi hcentral hK hd)

theorem HSemidirectEquiv_apply {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma))
    (x : M F Sigma pi ⋊[internalAction (M F Sigma pi) (E F Sigma pi hcentral)]
      E F Sigma pi hcentral) :
    HSemidirectEquiv F Sigma pi hpi hcentral hK hd x = x.left * x.right :=
  internalSemidirectEquiv_apply _ _ _ x

theorem E_map {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) : (E F Sigma pi hcentral).map pi = gammaField F Sigma := by
  ext g
  constructor
  · rintro ⟨e, he, rfl⟩
    exact he.1
  · intro hg
    let a : gammaField F Sigma := ⟨g, hg⟩
    let e := (piOnE F Sigma pi hpi hcentral hK hd).symm a
    exact ⟨e, e.property, congrArg Subtype.val
      ((piOnE F Sigma pi hpi hcentral hK hd).apply_symm_apply a)⟩

theorem E_centralizer_eq {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) :
    Subgroup.centralizer (E F Sigma pi hcentral : Set H) =
      (Subgroup.centralizer (gammaField F Sigma : Set (Gamma F Sigma))).comap pi := by
  rw [centralizer_eq_comap_image_centralizer pi hcentral hK (E F Sigma pi hcentral)
    (Nat.card Sigma) hd (fun e => e.property.2), E_map F Sigma pi hpi hcentral hK hd]

@[expose] def BDirectEquiv {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) : pi.ker × E F Sigma pi hcentral ≃* B F Sigma pi := by
  let hB := B_isMulCommutative F Sigma pi hcentral
  have heq : E F Sigma pi hcentral =
      oddRoots ((gammaField F Sigma).comap pi) (Nat.card (gammaField F Sigma)) hB := by
    unfold E
    rw [gammaField_card]
  exact (MulEquiv.refl pi.ker |>.prodCongr (MulEquiv.subgroupCongr heq)).trans
    (preimageDirectEquiv pi hpi hcentral hK (gammaField F Sigma)
      ((gammaField_card F Sigma).symm ▸ hd) hB)

theorem BDirectEquiv_coe {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) (x : pi.ker × E F Sigma pi hcentral) :
    (BDirectEquiv F Sigma pi hpi hcentral hK hd x : H) = (x.1 : H) * x.2 := rfl

theorem B_card {H : Type v} [Group H] [Finite H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) : Nat.card (B F Sigma pi) = Nat.card pi.ker * Nat.card Sigma := by
  rw [← Nat.card_congr (BDirectEquiv F Sigma pi hpi hcentral hK hd).toEquiv,
    Nat.card_prod, E_card F Sigma pi hpi hcentral hK hd]

theorem complement_centralizer_factorization {Q : Type u} [Group Q]
    (N C : Subgroup Q) (hcomp : N.IsComplement' C) (hC : IsMulCommutative C)
    (x : Subgroup.centralizer (C : Set Q)) :
    ∃ n : ↥(N ⊓ Subgroup.centralizer (C : Set Q)), ∃ c : C, (x : Q) = n * c := by
  have hCle : C ≤ Subgroup.centralizer (C : Set Q) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hC
  obtain ⟨⟨n, c⟩, hnc⟩ := hcomp.2 (x : Q)
  have hnval : (n : Q) = (x : Q) * (c : Q)⁻¹ := by
    rw [← hnc]
    group
  have hncen : (n : Q) ∈ Subgroup.centralizer (C : Set Q) := by
    rw [hnval]
    exact (Subgroup.centralizer (C : Set Q)).mul_mem x.property
      ((Subgroup.centralizer (C : Set Q)).inv_mem (hCle c.property))
  exact ⟨⟨n, n.property, hncen⟩, c, hnc.symm⟩

theorem complement_centralizer_sup {Q : Type u} [Group Q]
    (N C : Subgroup Q) (hcomp : N.IsComplement' C) (hC : IsMulCommutative C) :
    Subgroup.centralizer (C : Set Q) = (N ⊓ Subgroup.centralizer (C : Set Q)) ⊔ C := by
  apply le_antisymm
  · intro x hx
    obtain ⟨n, c, hnc⟩ := complement_centralizer_factorization N C hcomp hC ⟨x, hx⟩
    change x = (n : Q) * c at hnc
    rw [hnc]
    exact (N ⊓ Subgroup.centralizer (C : Set Q) ⊔ C).mul_mem
      ((show N ⊓ Subgroup.centralizer (C : Set Q) ≤
        N ⊓ Subgroup.centralizer (C : Set Q) ⊔ C from le_sup_left) n.property)
      ((show C ≤ N ⊓ Subgroup.centralizer (C : Set Q) ⊔ C from le_sup_right) c.property)
  · exact sup_le inf_le_right (Subgroup.le_centralizer_iff_isMulCommutative.mpr hC)

@[expose] def complementCentralizerDirectEquiv {Q : Type u} [Group Q]
    (N C : Subgroup Q) (hcomp : N.IsComplement' C) (hC : IsMulCommutative C) :
    ↥(N ⊓ Subgroup.centralizer (C : Set Q)) × C ≃* Subgroup.centralizer (C : Set Q) := by
  let Z := Subgroup.centralizer (C : Set Q)
  let N0 := N ⊓ Z
  have hCle : C ≤ Z := Subgroup.le_centralizer_iff_isMulCommutative.mpr hC
  have hCN : (C.subgroupOf Z) ≤ Subgroup.center Z := by
    intro c hc
    apply Subgroup.mem_center_iff.mpr
    intro z
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp z.property c hc).symm
  have hcomp' : (N0.subgroupOf Z).IsComplement' (C.subgroupOf Z) :=
    factorization_isComplement Z N0 C inf_le_right hCle
      (hcomp.disjoint.mono_left inf_le_left)
      (complement_centralizer_factorization N C hcomp hC)
  let pairEquiv := (Subgroup.subgroupOfEquivOfLe (show N0 ≤ Z from inf_le_right)).symm.prodCongr
    (Subgroup.subgroupOfEquivOfLe hCle).symm
  let swap : (N0.subgroupOf Z) × (C.subgroupOf Z) ≃*
      (C.subgroupOf Z) × (N0.subgroupOf Z) := MulEquiv.prodComm
  let direct := internalDirectEquiv (C.subgroupOf Z) (N0.subgroupOf Z) hCN hcomp'.symm
  exact pairEquiv.trans (swap.trans direct)

theorem complementCentralizerDirectEquiv_coe {Q : Type u} [Group Q]
    (N C : Subgroup Q) (hcomp : N.IsComplement' C) (hC : IsMulCommutative C)
    (x : ↥(N ⊓ Subgroup.centralizer (C : Set Q)) × C) :
    (complementCentralizerDirectEquiv N C hcomp hC x : Q) = (x.1 : Q) * x.2 := by
  change (x.2 : Q) * x.1 = (x.1 : Q) * x.2
  exact Subgroup.mem_centralizer_iff.mp x.1.property.2 x.2 x.2.property
theorem preimageProjection_ker {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (C : Subgroup Q) :
    (preimageProjection pi C).ker = pi.ker.subgroupOf (C.comap pi) := by
  ext b
  constructor
  · intro hb
    exact congrArg Subtype.val (show preimageProjection pi C b = 1 from hb)
  · intro hb
    exact Subtype.ext hb

theorem preimage_card {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi) (C : Subgroup Q) :
    Nat.card (C.comap pi) = Nat.card pi.ker * Nat.card C := by
  have h := Subgroup.card_ker_mul_card_of_surjective
    (preimageProjection_surjective pi hpi C)
  rw [preimageProjection_ker] at h
  have hker : Nat.card (pi.ker.subgroupOf (C.comap pi)) = Nat.card pi.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pi.ker_le_comap C)).toEquiv
  rw [hker] at h
  exact h.symm

theorem exists_sylow_two_le_of_odd_index {H : Type u} [Group H] [Finite H]
    (H0 : Subgroup H) (hindex : Odd H0.index) :
    ∃ S : Sylow 2 H, (S : Subgroup H) ≤ H0 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S0 : Sylow 2 H0 := Sylow.nonempty.some
  let S : Subgroup H := S0.map H0.subtype
  have hpS : IsPGroup 2 S := S0.2.map H0.subtype
  have hS : ¬ 2 ∣ S.index := by
    rw [Subgroup.index_map_subtype S0.1]
    exact Nat.prime_two.not_dvd_mul S0.not_dvd_index hindex.not_two_dvd_nat
  refine ⟨hpS.toSylow hS, ?_⟩
  rw [IsPGroup.toSylow_coe]
  exact Subgroup.map_subtype_le S0.1

theorem exists_sylow_two_le_centralizer_of_odd_index {H : Type u} [Group H] [Finite H]
    (H0 E : Subgroup H) (hindex : Odd H0.index)
    (hcentralizer : H0 ≤ Subgroup.centralizer (E : Set H)) :
    ∃ S : Sylow 2 H, (S : Subgroup H) ≤ H0 ∧
      (S : Subgroup H) ≤ Subgroup.centralizer (E : Set H) := by
  obtain ⟨S, hS⟩ := exists_sylow_two_le_of_odd_index H0 hindex
  exact ⟨S, hS, hS.trans hcentralizer⟩

theorem kernel_isPGroup_of_card {H : Type u} {Q : Type v} [Group H] [Group Q] [Finite H]
    (pi : H →* Q) (hcard : ∃ k : ℕ, Nat.card pi.ker = 2 ^ k) : IsPGroup 2 pi.ker := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.iff_card.mpr hcard

theorem E_isMulCommutative {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hcentral : pi.ker ≤ Subgroup.center H) :
    IsMulCommutative (E F Sigma pi hcentral) := by
  apply isMulCommutative_iff.mpr
  intro x y
  apply Subtype.ext
  exact congrArg (fun b : B F Sigma pi => (b : H))
    ((B_isMulCommutative F Sigma pi hcentral).is_comm.comm
      (⟨x, x.property.1⟩ : B F Sigma pi) (⟨y, y.property.1⟩ : B F Sigma pi))

theorem linear_inter_centralizer_eq {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) :
    M F Sigma pi ⊓ Subgroup.centralizer (E F Sigma pi hcentral : Set H) =
      (gammaLinear F Sigma ⊓
        Subgroup.centralizer (gammaField F Sigma : Set (Gamma F Sigma))).comap pi := by
  rw [E_centralizer_eq F Sigma pi hpi hcentral hK hd, Subgroup.comap_inf]

@[expose] def ECentralizerDirectEquiv {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) :
    ↥((gammaLinear F Sigma ⊓
      Subgroup.centralizer (gammaField F Sigma : Set (Gamma F Sigma))).comap pi) ×
      E F Sigma pi hcentral ≃* Subgroup.centralizer (E F Sigma pi hcentral : Set H) :=
  ((MulEquiv.subgroupCongr (linear_inter_centralizer_eq F Sigma pi hpi hcentral hK hd).symm).prodCongr
    (MulEquiv.refl (E F Sigma pi hcentral))).trans
    (complementCentralizerDirectEquiv (M F Sigma pi) (E F Sigma pi hcentral)
      (H_isComplement F Sigma pi hpi hcentral hK hd) (E_isMulCommutative F Sigma pi hcentral))

theorem ECentralizerDirectEquiv_coe {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma))
    (x : ↥((gammaLinear F Sigma ⊓
      Subgroup.centralizer (gammaField F Sigma : Set (Gamma F Sigma))).comap pi) ×
      E F Sigma pi hcentral) :
    (ECentralizerDirectEquiv F Sigma pi hpi hcentral hK hd x : H) = (x.1 : H) * x.2 :=
  complementCentralizerDirectEquiv_coe (M F Sigma pi) (E F Sigma pi hcentral)
    (H_isComplement F Sigma pi hpi hcentral hK hd) (E_isMulCommutative F Sigma pi hcentral)
    ((MulEquiv.subgroupCongr
      (linear_inter_centralizer_eq F Sigma pi hpi hcentral hK hd).symm x.1), x.2)

@[expose] def oddLinearIndex (q0 d : ℕ) : ℕ :=
  q0 ^ (d - 1) * ∑ i ∈ Finset.range d, (q0 ^ 2) ^ i

theorem oddLinearIndex_odd {q0 d : ℕ} (hqodd : Odd q0) (hd : Odd d) :
    Odd (oddLinearIndex q0 d) :=
  hqodd.pow.mul (CFSG.Semidihedral.FixedFieldData.odd_geometric_sum hqodd hd)

theorem oddLinearIndex_mul {q0 d : ℕ} (hq0 : 3 ≤ q0) (hd : Odd d) :
    q0 * (q0 ^ 2 - 1) * oddLinearIndex q0 d = q0 ^ d * ((q0 ^ d) ^ 2 - 1) := by
  have hpow : q0 * q0 ^ (d - 1) = q0 ^ d := by
    rw [← pow_succ', Nat.sub_add_cancel (show 1 ≤ d from hd.pos)]
  have hgeom : (∑ i ∈ Finset.range d, (q0 ^ 2) ^ i) * (q0 ^ 2 - 1) =
      (q0 ^ d) ^ 2 - 1 := by
    have h := geom_sum_mul_of_one_le (show 1 ≤ q0 ^ 2 by nlinarith) d
    simpa only [← pow_mul, Nat.mul_comm 2 d] using h
  unfold oddLinearIndex
  calc
    q0 * (q0 ^ 2 - 1) * (q0 ^ (d - 1) * ∑ i ∈ Finset.range d, (q0 ^ 2) ^ i) =
        (q0 * q0 ^ (d - 1)) * ((∑ i ∈ Finset.range d, (q0 ^ 2) ^ i) * (q0 ^ 2 - 1)) := by ac_rfl
    _ = q0 ^ d * ((q0 ^ d) ^ 2 - 1) := by rw [hpow, hgeom]

theorem odd_index_of_projective_card {D : Type u} [Group D] [Finite D]
    (D0 : Subgroup D) {q0 d : ℕ} (hq0 : 3 ≤ q0) (hqodd : Odd q0) (hd : Odd d)
    (hD : Nat.card D = q0 ^ d * ((q0 ^ d) ^ 2 - 1))
    (hD0 : Nat.card D0 = q0 * (q0 ^ 2 - 1)) :
    D0.index = oddLinearIndex q0 d ∧ Odd D0.index := by
  have hpos : 0 < q0 * (q0 ^ 2 - 1) := by
    have : 1 < q0 ^ 2 := by nlinarith
    exact Nat.mul_pos (by omega) (by omega)
  have heq : D0.index = oddLinearIndex q0 d := by
    apply Nat.mul_right_cancel hpos
    rw [← hD0, D0.index_mul_card, hD]
    rw [hD0, Nat.mul_comm (oddLinearIndex q0 d)]
    exact (oddLinearIndex_mul hq0 hd).symm
  exact ⟨heq, heq ▸ oddLinearIndex_odd hqodd hd⟩

theorem quotient_preimage_odd_index {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi) (Q0 : Subgroup Q) (hodd : Odd Q0.index) :
    Odd (Q0.comap pi).index := (Q0.index_comap_of_surjective hpi).symm ▸ hodd

theorem quotient_preimage_sylow_two {H : Type u} {Q : Type v} [Group H] [Group Q] [Finite H]
    (pi : H →* Q) (hpi : Function.Surjective pi) (Q0 : Subgroup Q)
    (hodd : Odd Q0.index) (E : Subgroup H)
    (hcentralizer : Q0.comap pi ≤ Subgroup.centralizer (E : Set H)) :
    ∃ S : Sylow 2 H, (S : Subgroup H) ≤ Q0.comap pi ∧
      (S : Subgroup H) ≤ Subgroup.centralizer (E : Set H) :=
  exists_sylow_two_le_centralizer_of_odd_index (Q0.comap pi) E
    (quotient_preimage_odd_index pi hpi Q0 hodd) hcentralizer

@[expose] def gammaLinearEquiv (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) : gammaLinear F Sigma ≃* coordinateD F :=
  (Subgroup.subgroupOfEquivOfLe (show linearLayer F ≤ Gamma F Sigma from le_sup_left)).trans
    (Subgroup.subgroupOfEquivOfLe (coordinateD_le_E F))

theorem gammaLinearEquiv_coe (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (d : gammaLinear F Sigma) :
    (gammaLinearEquiv F Sigma d : Equiv.Perm (Omega F)) =
      (((d : Gamma F Sigma) : coordinateE F) : Equiv.Perm (Omega F)) := by
  dsimp only [gammaLinearEquiv, MulEquiv.trans_apply]
  rw [Subgroup.subgroupOfEquivOfLe_apply_coe, Subgroup.subgroupOfEquivOfLe_apply_coe]

theorem gammaLinear_card (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) :
    Nat.card (gammaLinear F Sigma) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  calc
    Nat.card (gammaLinear F Sigma) = Nat.card (coordinateD F) :=
      Nat.card_congr (gammaLinearEquiv F Sigma).toEquiv
    _ = Nat.card (PGL2 F) := (Nat.card_congr (pglEquivCoordinateD F).toEquiv).symm
    _ = Nat.card F * (Nat.card F ^ 2 - 1) := pgl2_card_formula F

theorem Gamma_card (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) :
    Nat.card (Gamma F Sigma) = Nat.card F * (Nat.card F ^ 2 - 1) * Nat.card Sigma := by
  have h := (gamma_isComplement F Sigma).card_mul_card
  rw [gammaLinear_card, gammaField_card] at h
  exact h.symm

abbrev H1 {H : Type v} [Group H] (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (pi : H →* Gamma F Sigma) := M F Sigma pi

theorem H1_card {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi) :
    Nat.card (H1 F Sigma pi) = Nat.card pi.ker * (Nat.card F * (Nat.card F ^ 2 - 1)) := by
  rw [preimage_card pi hpi (gammaLinear F Sigma), gammaLinear_card]

theorem H_card {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi) :
    Nat.card H = Nat.card pi.ker * (Nat.card F * (Nat.card F ^ 2 - 1) * Nat.card Sigma) := by
  have h := Subgroup.card_ker_mul_card_of_surjective hpi
  rw [Gamma_card] at h
  exact h.symm

theorem gammaLinear_index (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) : (gammaLinear F Sigma).index = Nat.card Sigma := by
  rw [(gamma_isComplement F Sigma).symm.index_eq_card, gammaField_card]

theorem linear_preimage_index {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (D0 : Subgroup (Gamma F Sigma)) (hD0 : D0 ≤ gammaLinear F Sigma) :
    (D0.comap pi).index = D0.relIndex (gammaLinear F Sigma) * Nat.card Sigma := by
  rw [D0.index_comap_of_surjective hpi,
    ← Subgroup.relIndex_mul_index hD0, gammaLinear_index]

theorem original_fixed_field_data (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (F : Type u) [Field F] (hcard : Nat.card F = p ^ f)
    (Sigma : Subgroup (F ≃+* F)) (hd : Odd (Nat.card Sigma)) :
    Nat.card Sigma ∣ f ∧
      Nat.card (FixedPoints.subfield Sigma F) = p ^ (f / Nat.card Sigma) ∧
      Nat.card F = (p ^ (f / Nat.card Sigma)) ^ Nat.card Sigma ∧
      3 ≤ p ^ (f / Nat.card Sigma) ∧ Odd (p ^ (f / Nat.card Sigma)) := by
  obtain ⟨hdvd, _, hq0, hqodd, _, hsize, hpow, _, _, _⟩ :=
    CFSG.Semidihedral.FixedFieldData.odd_fixed_field_data p f hp hpodd hf F hcard Sigma hd
  exact ⟨hdvd, hsize, hpow, hq0, hqodd⟩

theorem linear_preimage_index_of_card {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (D0 : Subgroup (Gamma F Sigma)) (hD0 : D0 ≤ gammaLinear F Sigma)
    {q0 : ℕ} (hq0 : 3 ≤ q0) (hqodd : Odd q0) (hd : Odd (Nat.card Sigma))
    (hF : Nat.card F = q0 ^ Nat.card Sigma)
    (hcardD0 : Nat.card D0 = q0 * (q0 ^ 2 - 1)) :
    (D0.comap pi).index = oddLinearIndex q0 (Nat.card Sigma) * Nat.card Sigma ∧
      Odd (D0.comap pi).index := by
  have hD0' : Nat.card (D0.subgroupOf (gammaLinear F Sigma)) = q0 * (q0 ^ 2 - 1) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD0).toEquiv).trans hcardD0
  have hD' : Nat.card (gammaLinear F Sigma) =
      q0 ^ Nat.card Sigma * ((q0 ^ Nat.card Sigma) ^ 2 - 1) := by
    rw [gammaLinear_card, hF]
  obtain ⟨heq, hodd⟩ := odd_index_of_projective_card
    (D0.subgroupOf (gammaLinear F Sigma)) hq0 hqodd hd hD' hD0'
  have hexact : (D0.comap pi).index = oddLinearIndex q0 (Nat.card Sigma) * Nat.card Sigma := by
    rw [linear_preimage_index F Sigma pi hpi D0 hD0]
    change (D0.subgroupOf (gammaLinear F Sigma)).index * Nat.card Sigma = _
    rw [heq]
  exact ⟨hexact, hexact ▸ (oddLinearIndex_odd hqodd hd).mul hd⟩

theorem original_linear_preimage_index {H : Type v} [Group H]
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (F : Type u) [Field F] [Finite F] (hcard : Nat.card F = p ^ f)
    (Sigma : Subgroup (F ≃+* F)) (hd : Odd (Nat.card Sigma))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (D0 : Subgroup (Gamma F Sigma)) (hD0 : D0 ≤ gammaLinear F Sigma)
    (hcardD0 : Nat.card D0 =
      p ^ (f / Nat.card Sigma) * ((p ^ (f / Nat.card Sigma)) ^ 2 - 1)) :
    (D0.comap pi).index =
      oddLinearIndex (p ^ (f / Nat.card Sigma)) (Nat.card Sigma) * Nat.card Sigma ∧
      Odd (D0.comap pi).index := by
  obtain ⟨_, _, hpow, hq0, hqodd⟩ := original_fixed_field_data p f hp hpodd hf F hcard Sigma hd
  exact linear_preimage_index_of_card F Sigma pi hpi D0 hD0 hq0 hqodd hd hpow hcardD0

theorem linear_preimage_card_of_card {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (D0 : Subgroup (Gamma F Sigma)) {q0 : ℕ}
    (hcardD0 : Nat.card D0 = q0 * (q0 ^ 2 - 1)) :
    Nat.card (D0.comap pi) = Nat.card pi.ker * q0 * (q0 ^ 2 - 1) := by
  rw [preimage_card pi hpi D0, hcardD0, Nat.mul_assoc]

@[expose] def coordinateDToGamma (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) : coordinateD F →* Gamma F Sigma :=
  (gammaLinear F Sigma).subtype.comp (gammaLinearEquiv F Sigma).symm.toMonoidHom

theorem coordinateDToGamma_injective (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) : Function.Injective (coordinateDToGamma F Sigma) :=
  (gammaLinear F Sigma).subtype_injective.comp (gammaLinearEquiv F Sigma).symm.injective

theorem coordinateDToGamma_coe (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (d : coordinateD F) :
    (((coordinateDToGamma F Sigma d : Gamma F Sigma) : coordinateE F) :
      Equiv.Perm (Omega F)) = d := by
  dsimp only [coordinateDToGamma, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    gammaLinearEquiv, MulEquiv.symm_trans_apply, Subgroup.coe_subtype]
  rw [Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe,
    Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe]

theorem coordinateDToGamma_mem_linear (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (d : coordinateD F) :
    coordinateDToGamma F Sigma d ∈ gammaLinear F Sigma :=
  ((gammaLinearEquiv F Sigma).symm d).property

@[expose] def gammaCoordinateSubgroup (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (D0 : Subgroup (coordinateD F)) : Subgroup (Gamma F Sigma) :=
  D0.map (coordinateDToGamma F Sigma)

theorem gammaCoordinateSubgroup_le (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (D0 : Subgroup (coordinateD F)) :
    gammaCoordinateSubgroup F Sigma D0 ≤ gammaLinear F Sigma := by
  rintro g ⟨d, _, rfl⟩
  exact coordinateDToGamma_mem_linear F Sigma d

@[expose] def gammaCoordinateSubgroupEquiv (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (D0 : Subgroup (coordinateD F)) :
    D0 ≃* gammaCoordinateSubgroup F Sigma D0 :=
  D0.equivMapOfInjective (coordinateDToGamma F Sigma) (coordinateDToGamma_injective F Sigma)

theorem gammaCoordinateSubgroup_card (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (D0 : Subgroup (coordinateD F)) :
    Nat.card (gammaCoordinateSubgroup F Sigma D0) = Nat.card D0 :=
  (Nat.card_congr (gammaCoordinateSubgroupEquiv F Sigma D0).toEquiv).symm

theorem coordinateDToGamma_mem_centralizer_iff (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (d : coordinateD F) :
    coordinateDToGamma F Sigma d ∈ Subgroup.centralizer (gammaField F Sigma : Set (Gamma F Sigma)) ↔
      d ∈ FixedFieldCentralizer.D0InD F Sigma := by
  rw [FixedFieldCentralizer.D0InD_mem_iff]
  constructor
  · intro h sigma
    let a := (gammaFieldEquiv F Sigma).symm sigma
    have heq := congrArg (fun g : Gamma F Sigma =>
      ((g : coordinateE F) : Equiv.Perm (Omega F)))
      (Subgroup.mem_centralizer_iff.mp h a a.property)
    change (((a : Gamma F Sigma) : coordinateE F) : Equiv.Perm (Omega F)) *
      (((coordinateDToGamma F Sigma d : Gamma F Sigma) : coordinateE F) : Equiv.Perm (Omega F)) =
      (((coordinateDToGamma F Sigma d : Gamma F Sigma) : coordinateE F) : Equiv.Perm (Omega F)) *
      (((a : Gamma F Sigma) : coordinateE F) : Equiv.Perm (Omega F)) at heq
    rw [coordinateDToGamma_coe, gammaFieldEquiv_symm_coe] at heq
    exact heq.symm
  · intro h
    apply Subgroup.mem_centralizer_iff.mpr
    intro a ha
    let a0 : gammaField F Sigma := ⟨a, ha⟩
    let sigma := gammaFieldEquiv F Sigma a0
    have heq := congrArg (fun b : gammaField F Sigma =>
      (((b : Gamma F Sigma) : coordinateE F) : Equiv.Perm (Omega F)))
      ((gammaFieldEquiv F Sigma).symm_apply_apply a0)
    have ha' : ((a : coordinateE F) : Equiv.Perm (Omega F)) = fieldExtension F sigma :=
      heq.symm.trans (gammaFieldEquiv_symm_coe F Sigma sigma)
    apply Subtype.ext
    apply Subtype.ext
    change ((a : coordinateE F) : Equiv.Perm (Omega F)) *
      (((coordinateDToGamma F Sigma d : Gamma F Sigma) : coordinateE F) : Equiv.Perm (Omega F)) =
      (((coordinateDToGamma F Sigma d : Gamma F Sigma) : coordinateE F) : Equiv.Perm (Omega F)) *
      ((a : coordinateE F) : Equiv.Perm (Omega F))
    rw [coordinateDToGamma_coe, ha']
    exact (h sigma).eq.symm

@[expose] def D0Gamma (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) : Subgroup (Gamma F Sigma) :=
  gammaCoordinateSubgroup F Sigma (FixedFieldCentralizer.D0InD F Sigma)

@[expose] def H0 {H : Type v} [Group H] (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (pi : H →* Gamma F Sigma) : Subgroup H :=
  (D0Gamma F Sigma).comap pi

theorem D0Gamma_le_linear (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) : D0Gamma F Sigma ≤ gammaLinear F Sigma :=
  gammaCoordinateSubgroup_le F Sigma (FixedFieldCentralizer.D0InD F Sigma)

theorem gammaLinear_inter_centralizer (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) :
    gammaLinear F Sigma ⊓ Subgroup.centralizer (gammaField F Sigma : Set (Gamma F Sigma)) =
      D0Gamma F Sigma := by
  ext g
  constructor
  · rintro ⟨hlinear, hcentralizer⟩
    let g0 : gammaLinear F Sigma := ⟨g, hlinear⟩
    let d := gammaLinearEquiv F Sigma g0
    have heq : coordinateDToGamma F Sigma d = g :=
      congrArg Subtype.val ((gammaLinearEquiv F Sigma).symm_apply_apply g0)
    refine ⟨d, ?_, heq⟩
    apply (coordinateDToGamma_mem_centralizer_iff F Sigma d).mp
    rw [heq]
    exact hcentralizer
  · rintro ⟨d, hd, rfl⟩
    exact ⟨coordinateDToGamma_mem_linear F Sigma d,
      (coordinateDToGamma_mem_centralizer_iff F Sigma d).mpr hd⟩

theorem H0_le_centralizer {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) : H0 F Sigma pi ≤
      Subgroup.centralizer (E F Sigma pi hcentral : Set H) := by
  rw [E_centralizer_eq F Sigma pi hpi hcentral hK hd]
  intro h hh
  change pi h ∈ D0Gamma F Sigma at hh
  rw [← gammaLinear_inter_centralizer] at hh
  exact hh.2

theorem H1_inter_centralizer {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) :
    H1 F Sigma pi ⊓ Subgroup.centralizer (E F Sigma pi hcentral : Set H) = H0 F Sigma pi := by
  rw [linear_inter_centralizer_eq F Sigma pi hpi hcentral hK hd, gammaLinear_inter_centralizer]
  rfl

theorem H_centralizer_eq_sup {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) :
    Subgroup.centralizer (E F Sigma pi hcentral : Set H) = H0 F Sigma pi ⊔ E F Sigma pi hcentral := by
  rw [complement_centralizer_sup (H1 F Sigma pi) (E F Sigma pi hcentral)
    (H_isComplement F Sigma pi hpi hcentral hK hd) (E_isMulCommutative F Sigma pi hcentral),
    H1_inter_centralizer F Sigma pi hpi hcentral hK hd]

@[expose] def HCentralizerDirectEquiv {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) :
    H0 F Sigma pi × E F Sigma pi hcentral ≃* Subgroup.centralizer (E F Sigma pi hcentral : Set H) :=
  ((MulEquiv.subgroupCongr (H1_inter_centralizer F Sigma pi hpi hcentral hK hd).symm).prodCongr
    (MulEquiv.refl (E F Sigma pi hcentral))).trans
    (complementCentralizerDirectEquiv (H1 F Sigma pi) (E F Sigma pi hcentral)
      (H_isComplement F Sigma pi hpi hcentral hK hd) (E_isMulCommutative F Sigma pi hcentral))

theorem HCentralizerDirectEquiv_coe {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) (x : H0 F Sigma pi × E F Sigma pi hcentral) :
    (HCentralizerDirectEquiv F Sigma pi hpi hcentral hK hd x : H) = (x.1 : H) * x.2 :=
  complementCentralizerDirectEquiv_coe (H1 F Sigma pi) (E F Sigma pi hcentral)
    (H_isComplement F Sigma pi hpi hcentral hK hd) (E_isMulCommutative F Sigma pi hcentral)
    ((MulEquiv.subgroupCongr (H1_inter_centralizer F Sigma pi hpi hcentral hK hd).symm x.1), x.2)

theorem D0Gamma_card (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) :
    Nat.card (D0Gamma F Sigma) = Nat.card (FixedPoints.subfield Sigma F) *
      (Nat.card (FixedPoints.subfield Sigma F) ^ 2 - 1) :=
  (gammaCoordinateSubgroup_card F Sigma (FixedFieldCentralizer.D0InD F Sigma)).trans
    (FixedFieldCentralizer.D0InD_card F Sigma)

theorem H0_card {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi) :
    Nat.card (H0 F Sigma pi) = Nat.card pi.ker * Nat.card (FixedPoints.subfield Sigma F) *
      (Nat.card (FixedPoints.subfield Sigma F) ^ 2 - 1) := by
  exact linear_preimage_card_of_card F Sigma pi hpi (D0Gamma F Sigma) (D0Gamma_card F Sigma)

theorem H0_index {H : Type v} [Group H]
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (F : Type u) [Field F] [Finite F] (hcard : Nat.card F = p ^ f)
    (Sigma : Subgroup (F ≃+* F)) (hd : Odd (Nat.card Sigma))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi) :
    (H0 F Sigma pi).index =
      oddLinearIndex (p ^ (f / Nat.card Sigma)) (Nat.card Sigma) * Nat.card Sigma ∧
      Odd (H0 F Sigma pi).index := by
  have hfixed := (original_fixed_field_data p f hp hpodd hf F hcard Sigma hd).2.1
  apply original_linear_preimage_index p f hp hpodd hf F hcard Sigma hd pi hpi (D0Gamma F Sigma)
    (D0Gamma_le_linear F Sigma)
  rw [D0Gamma_card, hfixed]

theorem H0_contains_sylow_two {H : Type v} [Group H] [Finite H]
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (F : Type u) [Field F] [Finite F] (hcard : Nat.card F = p ^ f)
    (Sigma : Subgroup (F ≃+* F)) (hd : Odd (Nat.card Sigma))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker) :
    ∃ S : Sylow 2 H, (S : Subgroup H) ≤ H0 F Sigma pi ∧
      (S : Subgroup H) ≤ Subgroup.centralizer (E F Sigma pi hcentral : Set H) :=
  exists_sylow_two_le_centralizer_of_odd_index (H0 F Sigma pi) (E F Sigma pi hcentral)
    (H0_index p f hp hpodd hf F hcard Sigma hd pi hpi).2
    (H0_le_centralizer F Sigma pi hpi hcentral hK hd)

@[expose] def fixedCoordinateDEquivGamma (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) : coordinateD (FixedPoints.subfield Sigma F) ≃* D0Gamma F Sigma :=
  (FixedFieldCentralizer.coordinateDEquivD0 F Sigma).trans
    (gammaCoordinateSubgroupEquiv F Sigma (FixedFieldCentralizer.D0InD F Sigma))

theorem fixedCoordinateDEquivGamma_matrix (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F))
    (U : Matrix.GeneralLinearGroup (Fin 2) (FixedPoints.subfield Sigma F)) :
    ((((fixedCoordinateDEquivGamma F Sigma
      (pglEquivCoordinateD (FixedPoints.subfield Sigma F) (Matrix.ProjGenLinGroup.mk U)) : D0Gamma F Sigma) :
      Gamma F Sigma) : coordinateE F) : Equiv.Perm (Omega F)) = FixedFieldCentralizer.fixedGLAction F Sigma U := by
  change (((coordinateDToGamma F Sigma
    (FixedFieldCentralizer.coordinateDEquivD0 F Sigma
      (pglEquivCoordinateD (FixedPoints.subfield Sigma F) (Matrix.ProjGenLinGroup.mk U))) :
      Gamma F Sigma) : coordinateE F) : Equiv.Perm (Omega F)) = _
  rw [coordinateDToGamma_coe]
  exact FixedFieldCentralizer.coordinateDEquivD0_matrix F Sigma U

theorem D0Gamma_mem_iff (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (g : Gamma F Sigma) :
    g ∈ D0Gamma F Sigma ↔
      ((g : coordinateE F) : Equiv.Perm (Omega F)) ∈ FixedFieldCentralizer.D0 F Sigma := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    rw [coordinateDToGamma_coe]
    rw [← FixedFieldCentralizer.D0InD_map_subtype]
    exact ⟨d, hd, rfl⟩
  · intro hg
    rw [← FixedFieldCentralizer.D0InD_map_subtype] at hg
    obtain ⟨d, hd, hgd⟩ := hg
    refine ⟨d, hd, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (coordinateDToGamma_coe F Sigma d).trans hgd

theorem H0_eq_literal_preimage {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) :
    H0 F Sigma pi = (FixedFieldCentralizer.D0 F Sigma).comap (coordinateProjection F Sigma pi) := by
  ext h
  exact D0Gamma_mem_iff F Sigma (pi h)

@[expose] def fixedCoordinateDEquiv (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) :
    coordinateD (FixedPoints.subfield Sigma F) ≃* FixedFieldCentralizer.D0 F Sigma :=
  (FixedFieldCentralizer.coordinateDEquivD0 F Sigma).trans
    (((FixedFieldCentralizer.D0InD F Sigma).equivMapOfInjective (coordinateD F).subtype
      (coordinateD F).subtype_injective).trans
      (MulEquiv.subgroupCongr (FixedFieldCentralizer.D0InD_map_subtype F Sigma)))

theorem fixedCoordinateDEquiv_matrix (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F))
    (U : Matrix.GeneralLinearGroup (Fin 2) (FixedPoints.subfield Sigma F)) :
    (fixedCoordinateDEquiv F Sigma
      (pglEquivCoordinateD (FixedPoints.subfield Sigma F) (Matrix.ProjGenLinGroup.mk U)) :
      Equiv.Perm (Omega F)) = FixedFieldCentralizer.fixedGLAction F Sigma U :=
  FixedFieldCentralizer.coordinateDEquivD0_matrix F Sigma U

theorem D_centralizer_image (F : Type u) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) :
    ((Subgroup.centralizer (ambientLiftedField F Sigma : Set (Equiv.Perm (Omega F)))).comap
      (coordinateD F).subtype).map (coordinateD F).subtype = FixedFieldCentralizer.D0 F Sigma := by
  rw [FixedFieldCentralizer.fixed_field_projective_centralizer,
    FixedFieldCentralizer.D0InD_map_subtype]

theorem B_isComplement {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) :
    (pi.ker.subgroupOf (B F Sigma pi)).IsComplement'
      ((E F Sigma pi hcentral).subgroupOf (B F Sigma pi)) := by
  have h := oddRoots_isComplement pi hpi hcentral hK (gammaField F Sigma)
    ((gammaField_card F Sigma).symm ▸ hd) (B_isMulCommutative F Sigma pi hcentral)
  unfold E
  rwa [gammaField_card] at h

theorem HCentralizer_isComplement {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H) (hK : IsPGroup 2 pi.ker)
    (hd : Odd (Nat.card Sigma)) :
    ((H0 F Sigma pi).subgroupOf (Subgroup.centralizer (E F Sigma pi hcentral : Set H))).IsComplement'
      ((E F Sigma pi hcentral).subgroupOf (Subgroup.centralizer (E F Sigma pi hcentral : Set H))) := by
  have h0le := H0_le_centralizer F Sigma pi hpi hcentral hK hd
  have hEle : E F Sigma pi hcentral ≤ Subgroup.centralizer (E F Sigma pi hcentral : Set H) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr (E_isMulCommutative F Sigma pi hcentral)
  apply factorization_isComplement _ _ _ h0le hEle
  · exact (H_isComplement F Sigma pi hpi hcentral hK hd).disjoint.mono_left
      ((Subgroup.comap_mono (D0Gamma_le_linear F Sigma)))
  · intro x
    let p := (HCentralizerDirectEquiv F Sigma pi hpi hcentral hK hd).symm x
    refine ⟨p.1, p.2, ?_⟩
    have h := congrArg Subtype.val
      ((HCentralizerDirectEquiv F Sigma pi hpi hcentral hK hd).apply_symm_apply x)
    rw [HCentralizerDirectEquiv_coe] at h
    exact h.symm

theorem central_two_kernel_odd_field_complement_and_fixed_centralizer_of_finite
    {H : Type v} [Group H] [Finite H]
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (F : Type u) [Field F] [Finite F] (hcard : Nat.card F = p ^ f)
    (Sigma : Subgroup (F ≃+* F)) (hd : Odd (Nat.card Sigma))
    (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center H)
    (hkernel : ∃ k : ℕ, Nat.card pi.ker = 2 ^ k) :
    let E0 := E F Sigma pi hcentral
    let B0 := B F Sigma pi
    let H10 := H1 F Sigma pi
    let H00 := H0 F Sigma pi
    let q0 := p ^ (f / Nat.card Sigma)
    Nat.card Sigma ∣ f ∧
      Nat.card (FixedPoints.subfield Sigma F) = q0 ∧
      (∀ x : H, x ∈ E0 ↔ x ∈ B0 ∧ x ^ Nat.card Sigma = 1) ∧
      Nat.card E0 = Nat.card Sigma ∧
      (∀ U : Subgroup B0, Nat.card U = Nat.card Sigma → U = E0.subgroupOf B0) ∧
      (∃ e : E0 ≃* gammaField F Sigma, ∀ x : E0, (e x : Gamma F Sigma) = pi x) ∧
      (∀ sigma : Sigma, coordinateProjection F Sigma pi
        (eSigma F Sigma pi hpi hcentral (kernel_isPGroup_of_card pi hkernel) hd sigma) =
          fieldExtension F sigma) ∧
      (∃ e : pi.ker × E0 ≃* B0, ∀ x : pi.ker × E0, (e x : H) = (x.1 : H) * x.2) ∧
      H10.IsComplement' E0 ∧
      (∃ e : H10 ⋊[internalAction H10 E0] E0 ≃* H,
        ∀ x : H10 ⋊[internalAction H10 E0] E0, e x = x.left * x.right) ∧
      (∃ e : coordinateD (FixedPoints.subfield Sigma F) ≃* FixedFieldCentralizer.D0 F Sigma,
        ∀ U : Matrix.GeneralLinearGroup (Fin 2) (FixedPoints.subfield Sigma F),
          (e (pglEquivCoordinateD (FixedPoints.subfield Sigma F) (Matrix.ProjGenLinGroup.mk U)) :
            Equiv.Perm (Omega F)) = FixedFieldCentralizer.fixedGLAction F Sigma U) ∧
      (Subgroup.centralizer (ambientLiftedField F Sigma : Set (Equiv.Perm (Omega F)))).comap
        (coordinateD F).subtype = FixedFieldCentralizer.D0InD F Sigma ∧
      H00 = (FixedFieldCentralizer.D0 F Sigma).comap (coordinateProjection F Sigma pi) ∧
      Subgroup.centralizer (E0 : Set H) = H00 ⊔ E0 ∧
      (∃ e : H00 × E0 ≃* Subgroup.centralizer (E0 : Set H),
        ∀ x : H00 × E0, (e x : H) = (x.1 : H) * x.2) ∧
      Odd H00.index ∧
      Nat.card H00 = Nat.card pi.ker * q0 * (q0 ^ 2 - 1) ∧
      (∃ S : Sylow 2 H, (S : Subgroup H) ≤ H00 ∧
        (S : Subgroup H) ≤ Subgroup.centralizer (E0 : Set H)) := by
  let hK := kernel_isPGroup_of_card pi hkernel
  obtain ⟨hdiv, hfixed, _, _, _⟩ := original_fixed_field_data p f hp hpodd hf F hcard Sigma hd
  refine ⟨hdiv, hfixed, mem_E F Sigma pi hcentral,
    E_card F Sigma pi hpi hcentral hK hd,
    E_unique F Sigma pi hpi hcentral hK hd, ?_,
    eSigma_projective F Sigma pi hpi hcentral hK hd, ?_,
    H_isComplement F Sigma pi hpi hcentral hK hd, ?_, ?_,
    FixedFieldCentralizer.fixed_field_projective_centralizer F Sigma,
    H0_eq_literal_preimage F Sigma pi, H_centralizer_eq_sup F Sigma pi hpi hcentral hK hd,
    ?_, (H0_index p f hp hpodd hf F hcard Sigma hd pi hpi).2, ?_,
    H0_contains_sylow_two p f hp hpodd hf F hcard Sigma hd pi hpi hcentral hK⟩
  · exact ⟨piOnE F Sigma pi hpi hcentral hK hd, piOnE_coe F Sigma pi hpi hcentral hK hd⟩
  · exact ⟨BDirectEquiv F Sigma pi hpi hcentral hK hd, BDirectEquiv_coe F Sigma pi hpi hcentral hK hd⟩
  · exact ⟨HSemidirectEquiv F Sigma pi hpi hcentral hK hd, HSemidirectEquiv_apply F Sigma pi hpi hcentral hK hd⟩
  · exact ⟨fixedCoordinateDEquiv F Sigma, fixedCoordinateDEquiv_matrix F Sigma⟩
  · exact ⟨HCentralizerDirectEquiv F Sigma pi hpi hcentral hK hd,
      HCentralizerDirectEquiv_coe F Sigma pi hpi hcentral hK hd⟩
  · simpa only [hfixed] using H0_card F Sigma pi hpi

theorem finite_field_of_card (F : Type u) (p f : ℕ) (hp : p.Prime)
    (hcard : Nat.card F = p ^ f) : Finite F := by
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  exact pow_ne_zero f hp.ne_zero

theorem central_two_kernel_odd_field_complement_and_fixed_centralizer
    {H : Type v} [Group H] [Finite H]
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (F : Type u) [Field F] (hcard : Nat.card F = p ^ f) :
    letI : Finite F := finite_field_of_card F p f hp hcard
    ∀ (Sigma : Subgroup (F ≃+* F)) (hd : Odd (Nat.card Sigma))
      (pi : H →* Gamma F Sigma) (hpi : Function.Surjective pi)
      (hcentral : pi.ker ≤ Subgroup.center H)
      (hkernel : ∃ k : ℕ, Nat.card pi.ker = 2 ^ k),
    let E0 := E F Sigma pi hcentral
    let B0 := B F Sigma pi
    let H10 := H1 F Sigma pi
    let H00 := H0 F Sigma pi
    let q0 := p ^ (f / Nat.card Sigma)
    Nat.card Sigma ∣ f ∧
      Nat.card (FixedPoints.subfield Sigma F) = q0 ∧
      (∀ x : H, x ∈ E0 ↔ x ∈ B0 ∧ x ^ Nat.card Sigma = 1) ∧
      Nat.card E0 = Nat.card Sigma ∧
      (∀ U : Subgroup B0, Nat.card U = Nat.card Sigma → U = E0.subgroupOf B0) ∧
      (∃ e : E0 ≃* gammaField F Sigma, ∀ x : E0, (e x : Gamma F Sigma) = pi x) ∧
      (∀ sigma : Sigma, coordinateProjection F Sigma pi
        (eSigma F Sigma pi hpi hcentral (kernel_isPGroup_of_card pi hkernel) hd sigma) =
          fieldExtension F sigma) ∧
      (∃ e : pi.ker × E0 ≃* B0, ∀ x : pi.ker × E0, (e x : H) = (x.1 : H) * x.2) ∧
      H10.IsComplement' E0 ∧
      (∃ e : H10 ⋊[internalAction H10 E0] E0 ≃* H,
        ∀ x : H10 ⋊[internalAction H10 E0] E0, e x = x.left * x.right) ∧
      (∃ e : coordinateD (FixedPoints.subfield Sigma F) ≃* FixedFieldCentralizer.D0 F Sigma,
        ∀ U : Matrix.GeneralLinearGroup (Fin 2) (FixedPoints.subfield Sigma F),
          (e (pglEquivCoordinateD (FixedPoints.subfield Sigma F) (Matrix.ProjGenLinGroup.mk U)) :
            Equiv.Perm (Omega F)) = FixedFieldCentralizer.fixedGLAction F Sigma U) ∧
      (Subgroup.centralizer (ambientLiftedField F Sigma : Set (Equiv.Perm (Omega F)))).comap
        (coordinateD F).subtype = FixedFieldCentralizer.D0InD F Sigma ∧
      H00 = (FixedFieldCentralizer.D0 F Sigma).comap (coordinateProjection F Sigma pi) ∧
      Subgroup.centralizer (E0 : Set H) = H00 ⊔ E0 ∧
      (∃ e : H00 × E0 ≃* Subgroup.centralizer (E0 : Set H),
        ∀ x : H00 × E0, (e x : H) = (x.1 : H) * x.2) ∧
      Odd H00.index ∧
      Nat.card H00 = Nat.card pi.ker * q0 * (q0 ^ 2 - 1) ∧
      (∃ S : Sylow 2 H, (S : Subgroup H) ≤ H00 ∧
        (S : Subgroup H) ≤ Subgroup.centralizer (E0 : Set H)) := by
  let : Finite F := finite_field_of_card F p f hp hcard
  intro Sigma hd pi hpi hcentral hkernel
  exact central_two_kernel_odd_field_complement_and_fixed_centralizer_of_finite
    p f hp hpodd hf F hcard Sigma hd pi hpi hcentral hkernel

end CFSG.Wreathed.CentralTwoPowerFieldLift
