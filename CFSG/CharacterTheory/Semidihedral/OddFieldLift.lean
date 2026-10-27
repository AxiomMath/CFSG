module

public import CFSG.CharacterTheory.Semidihedral.SemilinearOddExtensions
public import CFSG.CharacterTheory.Semidihedral.FixedFieldData
public import CFSG.CharacterTheory.Semidihedral.ProjectiveSL2Cover

public section

namespace CFSG.Semidihedral.OddFieldLift

noncomputable section

open Matrix

universe u v w

theorem transvection_pow_nsmul {F : Type u} [Field F]
    {i j : Fin 2} (hij : i ≠ j) (a : F) (n : ℕ) :
    (SpecialLinearGroup.transvection hij a) ^ n =
      SpecialLinearGroup.transvection hij (n • a) := by
  induction n with
  | zero => simp [SpecialLinearGroup.transvection_coeff_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add, succ_nsmul]

theorem transvection_pow_char {F : Type u} [Field F]
    (p : ℕ) [CharP F p] {i j : Fin 2} (hij : i ≠ j) (a : F) :
    (SpecialLinearGroup.transvection hij a) ^ p = 1 := by
  rw [transvection_pow_nsmul]
  simp [nsmul_eq_mul, SpecialLinearGroup.transvection_coeff_zero]

theorem hom_to_exponent_two_trivial {F : Type u} [Field F]
    (p : ℕ) [CharP F p] (hp : Odd p) {T : Type v} [Group T]
    (hT : ∀ t : T, t ^ 2 = 1) (phi : SpecialLinearGroup (Fin 2) F →* T)
    (X : SpecialLinearGroup (Fin 2) F) : phi X = 1 := by
  apply Matrix.SL2.transvection_induction (fun X => phi X = 1)
  · intro i j hij a
    have hpow : (phi (SpecialLinearGroup.transvection hij a)) ^ p = 1 := by
      rw [← map_pow, transvection_pow_char p hij a, map_one]
    obtain ⟨n, hn⟩ := hp
    rw [hn, pow_succ, pow_mul, hT, one_pow, one_mul] at hpow
    exact hpow
  · intro X Y hX hY
    rw [map_mul, hX, hY, one_mul]

theorem hom_to_center_trivial {F : Type u} [Field F]
    (p : ℕ) [CharP F p] (hp : Odd p)
    (phi : SpecialLinearGroup (Fin 2) F →*
      Subgroup.center (SpecialLinearGroup (Fin 2) F))
    (X : SpecialLinearGroup (Fin 2) F) : phi X = 1 := by
  apply hom_to_exponent_two_trivial p hp _ phi X
  intro t
  apply Subtype.ext
  obtain ⟨c, hc, hct⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp t.property
  have hc2 : c ^ 2 = 1 := by simpa using hc
  apply Subtype.ext
  change ((t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ^ 2 = 1
  rw [← hct, ← map_pow, hc2, map_one]


open CFSG.Semidihedral.SemilinearOddExtensions
open CFSG.Semidihedral.SemilinearOuterQuotient
open CFSG.Semidihedral.CentralPrimeExtensions
open CFSG.Semidihedral.ProjectiveSL2Cover
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.GorensteinWalter
open scoped Pointwise

@[expose] def oddRoots {H : Type u} [Group H] (B : Subgroup H) (d : ℕ)
    (hB : IsMulCommutative B) : Subgroup H where
  carrier := {x | x ∈ B ∧ x ^ d = 1}
  one_mem' := ⟨B.one_mem, one_pow d⟩
  mul_mem' := by
    rintro x y ⟨hx, hxd⟩ ⟨hy, hyd⟩
    refine ⟨B.mul_mem hx hy, ?_⟩
    have hc : Commute x y := congrArg Subtype.val
      (hB.is_comm.comm (⟨x, hx⟩ : B) (⟨y, hy⟩ : B))
    rw [hc.mul_pow, hxd, hyd, one_mul]
  inv_mem' := by
    rintro x ⟨hx, hxd⟩
    exact ⟨B.inv_mem hx, by rw [inv_pow, hxd, inv_one]⟩

theorem mem_oddRoots {H : Type u} [Group H] (B : Subgroup H) (d : ℕ)
    (hB : IsMulCommutative B) (x : H) :
    x ∈ oddRoots B d hB ↔ x ∈ B ∧ x ^ d = 1 := Iff.rfl

@[expose] def preimageProjection {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (A : Subgroup Q) : A.comap pi →* A where
  toFun b := ⟨pi b, b.property⟩
  map_one' := Subtype.ext pi.map_one
  map_mul' x y := Subtype.ext (pi.map_mul x y)

theorem preimageProjection_surjective {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi) (A : Subgroup Q) :
    Function.Surjective (preimageProjection pi A) := by
  intro a
  obtain ⟨b, hb⟩ := hpi a
  exact ⟨⟨b, by change pi b ∈ A; rw [hb]; exact a.property⟩, Subtype.ext hb⟩

theorem preimage_isMulCommutative {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hc : pi.ker ≤ Subgroup.center H)
    (A : Subgroup Q) [IsCyclic A] : IsMulCommutative (A.comap pi) := by
  apply (preimageProjection pi A).isMulCommutative_of_isCyclic_of_ker_le_center
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  have hk : (x : H) ∈ pi.ker := by
    exact congrArg Subtype.val (show preimageProjection pi A x = 1 from hx)
  exact Subgroup.mem_center_iff.mp (hc hk) y

theorem odd_kernel_identity {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (z : H) (hz : orderOf z = 2)
    (hker : pi.ker = Subgroup.zpowers z) (d : ℕ) (hd : Odd d)
    {x : H} (hx : pi x = 1) (hxd : x ^ d = 1) : x = 1 := by
  have hk : x ∈ Subgroup.zpowers z := hker ▸ hx
  have hcard : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hz]
  have hx2 : x ^ 2 = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hk⟩ : Subgroup.zpowers z)))
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, hcard] using h
  obtain ⟨n, hn⟩ := hd
  rw [hn, pow_succ, pow_mul, hx2, one_pow, one_mul] at hxd
  exact hxd

theorem exists_odd_order_lift {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi) (z : H) (hz : orderOf z = 2)
    (hker : pi.ker = Subgroup.zpowers z) (A : Subgroup Q)
    (hd : Odd (Nat.card A)) (a : A) :
    ∃ b : A.comap pi, (b : H) ^ Nat.card A = 1 ∧ pi b = a := by
  let d := Nat.card A
  obtain ⟨b, hb⟩ := preimageProjection_surjective pi hpi A a
  have hba : pi b = a := congrArg Subtype.val hb
  have hbd : (b : H) ^ d ∈ pi.ker := by
    change pi ((b : H) ^ d) = 1
    rw [map_pow, hba]
    exact congrArg Subtype.val (pow_card_eq_one' (x := a))
  have hcard : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hz]
  have hbd2 : ((b : H) ^ d) ^ 2 = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one'
      (x := (⟨(b : H) ^ d, hker ▸ hbd⟩ : Subgroup.zpowers z)))
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, hcard] using h
  obtain ⟨n, hn⟩ := hd.add_one
  let c : A.comap pi := b ^ (d + 1)
  refine ⟨c, ?_, ?_⟩
  · change ((b : H) ^ (d + 1)) ^ d = 1
    rw [← pow_mul, Nat.mul_comm (d + 1) d, pow_mul,
      show d + 1 = 2 * n by dsimp only [d]; omega, pow_mul, hbd2, one_pow]
  · change pi ((b : H) ^ (d + 1)) = a
    rw [map_pow, hba, pow_succ]
    have had : (a : Q) ^ d = 1 := congrArg Subtype.val (pow_card_eq_one' (x := a))
    rw [had, one_mul]

@[expose] def oddProjection {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (A : Subgroup Q) (hB : IsMulCommutative (A.comap pi)) :
    oddRoots (A.comap pi) (Nat.card A) hB →* A where
  toFun e := ⟨pi e, e.property.1⟩
  map_one' := Subtype.ext pi.map_one
  map_mul' x y := Subtype.ext (pi.map_mul x y)

theorem oddProjection_bijective {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi) (z : H) (hz : orderOf z = 2)
    (hker : pi.ker = Subgroup.zpowers z) (A : Subgroup Q)
    (hd : Odd (Nat.card A)) (hB : IsMulCommutative (A.comap pi)) :
    Function.Bijective (oddProjection pi A hB) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hpi' : pi x = pi y := congrArg Subtype.val hxy
    have hk : pi ((x : H) * (y : H)⁻¹) = 1 := by rw [map_mul, map_inv, hpi', mul_inv_cancel]
    have hxd : ((x : H) * (y : H)⁻¹) ^ Nat.card A = 1 :=
      (oddRoots (A.comap pi) (Nat.card A) hB).mul_mem x.property
        ((oddRoots (A.comap pi) (Nat.card A) hB).inv_mem y.property) |>.2
    exact mul_inv_eq_one.mp (odd_kernel_identity pi z hz hker (Nat.card A) hd hk hxd)
  · intro a
    obtain ⟨b, hbd, hba⟩ := exists_odd_order_lift pi hpi z hz hker A hd a
    exact ⟨⟨b, b.property, hbd⟩, Subtype.ext hba⟩

@[expose] def oddProjectionEquiv {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi) (z : H) (hz : orderOf z = 2)
    (hker : pi.ker = Subgroup.zpowers z) (A : Subgroup Q)
    (hd : Odd (Nat.card A)) (hB : IsMulCommutative (A.comap pi)) :
    oddRoots (A.comap pi) (Nat.card A) hB ≃* A :=
  MulEquiv.ofBijective (oddProjection pi A hB)
    (oddProjection_bijective pi hpi z hz hker A hd hB)


theorem oddRoots_card {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi) (z : H) (hz : orderOf z = 2)
    (hker : pi.ker = Subgroup.zpowers z) (A : Subgroup Q)
    (hd : Odd (Nat.card A)) (hB : IsMulCommutative (A.comap pi)) :
    Nat.card (oddRoots (A.comap pi) (Nat.card A) hB) = Nat.card A :=
  Nat.card_congr (oddProjectionEquiv pi hpi z hz hker A hd hB).toEquiv

theorem oddRoots_unique {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi) (z : H) (hz : orderOf z = 2)
    (hker : pi.ker = Subgroup.zpowers z) (A : Subgroup Q)
    (hd : Odd (Nat.card A)) (hB : IsMulCommutative (A.comap pi))
    [Finite A] (U : Subgroup (A.comap pi)) (hU : Nat.card U = Nat.card A) :
    U = (oddRoots (A.comap pi) (Nat.card A) hB).subgroupOf (A.comap pi) := by
  have hE : oddRoots (A.comap pi) (Nat.card A) hB ≤ A.comap pi := fun _ h => h.1
  have hc : Nat.card ((oddRoots (A.comap pi) (Nat.card A) hB).subgroupOf
      (A.comap pi)) = Nat.card A :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv).trans
      (oddRoots_card pi hpi z hz hker A hd hB)
  let : Finite ((oddRoots (A.comap pi) (Nat.card A) hB).subgroupOf (A.comap pi)) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Nat.card_pos.ne')
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    refine ⟨x.property, ?_⟩
    have h := congrArg (fun e : U => ((e : A.comap pi) : H))
      (pow_card_eq_one' (x := (⟨x, hx⟩ : U)))
    change (x : H) ^ Nat.card A = 1
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, hU] using h
  · rw [hc, hU]

theorem oddRoots_disjoint_kernel {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (z : H) (hz : orderOf z = 2)
    (hker : pi.ker = Subgroup.zpowers z) (A : Subgroup Q)
    (hd : Odd (Nat.card A)) (hB : IsMulCommutative (A.comap pi)) :
    Disjoint (Subgroup.zpowers z) (oddRoots (A.comap pi) (Nat.card A) hB) := by
  apply disjoint_iff_inf_le.mpr
  rintro x ⟨hk, he⟩
  have hpi : pi x = 1 := MonoidHom.mem_ker.mp (hker.symm ▸ hk)
  exact odd_kernel_identity pi z hz hker (Nat.card A) hd hpi he.2

theorem oddRoots_factorization {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi) (z : H) (hz : orderOf z = 2)
    (hker : pi.ker = Subgroup.zpowers z) (A : Subgroup Q)
    (hd : Odd (Nat.card A)) (hB : IsMulCommutative (A.comap pi))
    (b : A.comap pi) :
    ∃ k : Subgroup.zpowers z, ∃ e : oddRoots (A.comap pi) (Nat.card A) hB,
      (b : H) = k * e := by
  let a : A := ⟨pi b, b.property⟩
  let e := (oddProjectionEquiv pi hpi z hz hker A hd hB).symm a
  have he : pi e = pi b := congrArg Subtype.val
    ((oddProjectionEquiv pi hpi z hz hker A hd hB).apply_symm_apply a)
  have hk : (b : H) * (e : H)⁻¹ ∈ Subgroup.zpowers z := by
    rw [← hker]
    change pi ((b : H) * (e : H)⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  exact ⟨⟨(b : H) * (e : H)⁻¹, hk⟩, e, by simp only [mul_assoc, inv_mul_cancel, mul_one]⟩

theorem oddRoots_isComplement {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi) (z : H) (hz : orderOf z = 2)
    (hker : pi.ker = Subgroup.zpowers z) (A : Subgroup Q)
    (hd : Odd (Nat.card A)) (hB : IsMulCommutative (A.comap pi)) :
    ((Subgroup.zpowers z).subgroupOf (A.comap pi)).IsComplement'
      ((oddRoots (A.comap pi) (Nat.card A) hB).subgroupOf (A.comap pi)) :=
  factorization_isComplement (A.comap pi) (Subgroup.zpowers z)
    (oddRoots (A.comap pi) (Nat.card A) hB)
    (hker ▸ pi.ker_le_comap A) (fun _ h => h.1)
    (oddRoots_disjoint_kernel pi z hz hker A hd hB)
    (oddRoots_factorization pi hpi z hz hker A hd hB)

@[expose] def internalDirectEquiv {H : Type u} [Group H] (N L : Subgroup H)
    (hc : N ≤ Subgroup.center H) (h : N.IsComplement' L) : N × L ≃* H := by
  let f : N × L →* H :=
    { toFun := fun x => (x.1 : H) * x.2
      map_one' := one_mul _
      map_mul' := by
        intro x y
        exact (Commute.mul_mul_mul_comm
          (show Commute (x.2 : H) (y.1 : H) from
            Subgroup.mem_center_iff.mp (hc y.1.property) x.2) x.1 y.2).symm }
  exact MulEquiv.ofBijective f ⟨h.1, h.2⟩

theorem internalDirectEquiv_apply {H : Type u} [Group H] (N L : Subgroup H)
    (hc : N ≤ Subgroup.center H) (h : N.IsComplement' L) (x : N × L) :
    internalDirectEquiv N L hc h x = (x.1 : H) * x.2 := rfl

theorem preimage_isComplement {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (hpi : Function.Surjective pi) (z : H) (hz : orderOf z = 2)
    (hker : pi.ker = Subgroup.zpowers z) (N A : Subgroup Q)
    (hd : Odd (Nat.card A)) (hB : IsMulCommutative (A.comap pi))
    (hcomp : N.IsComplement' A) :
    (N.comap pi).IsComplement' (oddRoots (A.comap pi) (Nat.card A) hB) := by
  have hdis : Disjoint (N.comap pi) (oddRoots (A.comap pi) (Nat.card A) hB) := by
    apply disjoint_iff_inf_le.mpr
    rintro x ⟨hn, he⟩
    have hpi' : pi x = 1 := disjoint_iff_inf_le.mp hcomp.disjoint ⟨hn, he.1⟩
    exact odd_kernel_identity pi z hz hker (Nat.card A) hd hpi' he.2
  refine ⟨Subgroup.mul_injective_of_disjoint hdis, ?_⟩
  intro x
  obtain ⟨⟨n, a⟩, hna⟩ := hcomp.2 (pi x)
  let e := (oddProjectionEquiv pi hpi z hz hker A hd hB).symm a
  have he : pi e = a := congrArg Subtype.val
    ((oddProjectionEquiv pi hpi z hz hker A hd hB).apply_symm_apply a)
  have hn : x * (e : H)⁻¹ ∈ N.comap pi := by
    change pi (x * (e : H)⁻¹) ∈ N
    rw [map_mul, map_inv, he, ← hna]
    rw [mul_assoc, mul_inv_cancel, mul_one]
    exact n.property
  exact ⟨(⟨x * (e : H)⁻¹, hn⟩, e), by simp only [mul_assoc, inv_mul_cancel, mul_one]⟩


abbrev Gamma (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F)) :=
  linearLayer F ⊔ liftedField F A

abbrev SpecialGamma (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F)) :=
  specialLayer F ⊔ liftedField F A

abbrev gammaLinear (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F)) :=
  (linearLayer F).subgroupOf (Gamma F A)

abbrev gammaSpecial (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F)) :=
  (specialLayer F).subgroupOf (Gamma F A)

abbrev gammaField (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F)) :=
  (liftedField F A).subgroupOf (Gamma F A)

@[expose] def gammaFieldEquiv (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : gammaField F A ≃* A :=
  (Subgroup.subgroupOfEquivOfLe le_sup_right).trans (liftedFieldEquiv F A)

theorem gammaFieldEquiv_symm_coe (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (a : A) :
    ((((gammaFieldEquiv F A).symm a : Gamma F A) : coordinateE F) :
      Equiv.Perm (Omega F)) = fieldExtension F a :=
  liftedFieldEquiv_symm_coe F A a

theorem gammaField_card (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) : Nat.card (gammaField F A) = Nat.card A :=
  Nat.card_congr (gammaFieldEquiv F A).toEquiv

theorem gamma_isComplement (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) :
    (gammaLinear F A).IsComplement' (gammaField F A) := by
  apply factorization_isComplement (Gamma F A) (linearLayer F) (liftedField F A)
    le_sup_left le_sup_right (linearLayer_disjoint_liftedField F A)
  intro x
  obtain ⟨n, hn, a, ha, hna⟩ := Subgroup.mem_sup_of_normal_left.mp x.property
  exact ⟨⟨n, hn⟩, ⟨a, ha⟩, hna.symm⟩

@[expose] def gammaSemidirectEquiv (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) :
    gammaLinear F A ⋊[internalAction (gammaLinear F A) (gammaField F A)]
      gammaField F A ≃* Gamma F A :=
  internalSemidirectEquiv _ _ (gamma_isComplement F A)

abbrev Lambda {H : Type v} [Group H] (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (pi : H →* Gamma F A) := (gammaSpecial F A).comap pi

abbrev M {H : Type v} [Group H] (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (pi : H →* Gamma F A) := (gammaLinear F A).comap pi

abbrev B {H : Type v} [Group H] (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (pi : H →* Gamma F A) := (gammaField F A).comap pi

abbrev SpecialPreimage {H : Type v} [Group H] (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (pi : H →* Gamma F A) :=
  ((SpecialGamma F A).subgroupOf (Gamma F A)).comap pi

@[expose] def coordinateProjection {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) : H →* Equiv.Perm (Omega F) :=
  (coordinateE F).subtype.comp ((Gamma F A).subtype.comp pi)

theorem pi_z {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (z : H) (hker : pi.ker = Subgroup.zpowers z) : pi z = 1 :=
  MonoidHom.mem_ker.mp (hker.symm ▸ Subgroup.mem_zpowers z)

theorem kernel_central {H : Type u} {Q : Type v} [Group H] [Group Q]
    (pi : H →* Q) (z : H) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) : pi.ker ≤ Subgroup.center H := by
  rw [hker]
  exact Subgroup.zpowers_le.mpr hzc

theorem B_isMulCommutative {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (z : H) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) : IsMulCommutative (B F A pi) := by
  let : IsCyclic (F ≃+* F) := fieldAut_isCyclic F
  let : IsCyclic (gammaField F A) := (gammaFieldEquiv F A).isCyclic.mpr inferInstance
  exact preimage_isMulCommutative pi (kernel_central pi z hzc hker) (gammaField F A)

@[expose] def E {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (z : H) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) : Subgroup H :=
  oddRoots (B F A pi) (Nat.card A) (B_isMulCommutative F A pi z hzc hker)

theorem mem_E {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (z : H) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (e : H) :
    e ∈ E F A pi z hzc hker ↔ e ∈ B F A pi ∧ e ^ Nat.card A = 1 := Iff.rfl

@[expose] def piOnE {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    E F A pi z hzc hker ≃* gammaField F A := by
  let hB := B_isMulCommutative F A pi z hzc hker
  let e := oddProjectionEquiv pi hpi z hz hker (gammaField F A)
    ((gammaField_card F A).symm ▸ hd) hB
  exact (subgroupEquivOfEq (by unfold E; rw [gammaField_card])).trans e

theorem piOnE_coe {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A))
    (e : E F A pi z hzc hker) : (piOnE F A pi hpi z hz hzc hker hd e : Gamma F A) = pi e := rfl

@[expose] def EEquivField {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    E F A pi z hzc hker ≃* A :=
  (piOnE F A pi hpi z hz hzc hker hd).trans (gammaFieldEquiv F A)

@[expose] def eSigma {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A))
    (sigma : A) : E F A pi z hzc hker :=
  (EEquivField F A pi hpi z hz hzc hker hd).symm sigma

theorem eSigma_projective {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) (sigma : A) :
    coordinateProjection F A pi (eSigma F A pi hpi z hz hzc hker hd sigma) =
      fieldExtension F sigma := by
  have h : pi (eSigma F A pi hpi z hz hzc hker hd sigma) =
      ((gammaFieldEquiv F A).symm sigma : Gamma F A) := congrArg Subtype.val
    ((piOnE F A pi hpi z hz hzc hker hd).apply_symm_apply
      ((gammaFieldEquiv F A).symm sigma))
  change (((pi (eSigma F A pi hpi z hz hzc hker hd sigma) : Gamma F A) : coordinateE F) :
    Equiv.Perm (Omega F)) = _
  rw [h, gammaFieldEquiv_symm_coe]

theorem E_card {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    Nat.card (E F A pi z hzc hker) = Nat.card A :=
  Nat.card_congr (EEquivField F A pi hpi z hz hzc hker hd).toEquiv

theorem E_unique {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A))
    (U : Subgroup (B F A pi)) (hU : Nat.card U = Nat.card A) :
    U = (E F A pi z hzc hker).subgroupOf (B F A pi) := by
  apply oddRoots_unique pi hpi z hz hker (gammaField F A)
    ((gammaField_card F A).symm ▸ hd) (B_isMulCommutative F A pi z hzc hker) U
    (hU.trans (gammaField_card F A).symm) |>.trans
  congr 1
  unfold E
  rw [gammaField_card]

theorem H_isComplement {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    (M F A pi).IsComplement' (E F A pi z hzc hker) := by
  have h := preimage_isComplement pi hpi z hz hker (gammaLinear F A) (gammaField F A)
    ((gammaField_card F A).symm ▸ hd) (B_isMulCommutative F A pi z hzc hker)
    (gamma_isComplement F A)
  unfold E
  rwa [gammaField_card] at h

@[expose] def HSemidirectEquiv {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    M F A pi ⋊[internalAction (M F A pi) (E F A pi z hzc hker)]
      E F A pi z hzc hker ≃* H :=
  internalSemidirectEquiv _ _ (H_isComplement F A pi hpi z hz hzc hker hd)

@[expose] def slCoordinateAction (F : Type u) [Field F] :
    Matrix.SpecialLinearGroup (Fin 2) F →* Equiv.Perm (Omega F) :=
  (coordinatePSLAction F).comp (nativeQuotient F)

theorem slCoordinateAction_ker (F : Type u) [Field F] :
    (slCoordinateAction F).ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rw [slCoordinateAction, MonoidHom.ker_comp_of_injective _ _
    (coordinatePSLAction_injective F), nativeQuotient, QuotientGroup.ker_mk']

theorem slCoordinateAction_field (F : Type u) [Field F] [Finite F]
    (sigma : F ≃+* F) (X : Matrix.SpecialLinearGroup (Fin 2) F) :
    slCoordinateAction F (Matrix.SpecialLinearGroup.map sigma.toRingHom X) =
      fieldExtension F sigma * slCoordinateAction F X * (fieldExtension F sigma)⁻¹ := by
  have h := congrArg (coordinateSemilinearAction F)
    (SemidirectProduct.inl_aut (φ := pgl2FieldAut F) sigma
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (nativeQuotient F X)))
  simp only [map_mul, map_inv, coordinateSemilinearAction_inl,
    coordinateSemilinearAction_inr] at h
  rw [← psl2FieldAut_toPGL, coordinatePGLAction_toPGL,
    coordinatePGLAction_toPGL] at h
  change coordinatePSLAction F (psl2RingEquiv sigma (nativeQuotient F X)) = _ at h
  rw [nativeQuotient, psl2RingEquiv_mk] at h
  exact h

theorem hom_eq_of_projective_eq {F : Type u} [Field F]
    (p : ℕ) [CharP F p] (hp : Odd p)
    (alpha beta : Matrix.SpecialLinearGroup (Fin 2) F →*
      Matrix.SpecialLinearGroup (Fin 2) F)
    (hproj : ∀ X, slCoordinateAction F (alpha X) = slCoordinateAction F (beta X)) :
    alpha = beta := by
  have hd : ∀ X, (alpha X)⁻¹ * beta X ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro X
    rw [← slCoordinateAction_ker]
    change slCoordinateAction F ((alpha X)⁻¹ * beta X) = 1
    rw [map_mul, map_inv, hproj, inv_mul_cancel]
  let delta := centralDifference (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
    le_rfl alpha beta hd
  apply MonoidHom.ext
  intro X
  have hdelta : (alpha X)⁻¹ * beta X = 1 := congrArg Subtype.val
    (hom_to_center_trivial p hp delta X)
  exact inv_mul_eq_one.mp hdelta

@[expose] def fixedSL2Inclusion (F : Type u) [Field F] (A : Subgroup (F ≃+* F)) :
    Matrix.SpecialLinearGroup (Fin 2) (FixedPoints.subfield A F) →*
      Matrix.SpecialLinearGroup (Fin 2) F :=
  Matrix.SpecialLinearGroup.map (FixedPoints.subfield A F).subtype

theorem fixedSL2Inclusion_entry (F : Type u) [Field F] (A : Subgroup (F ≃+* F))
    (X : Matrix.SpecialLinearGroup (Fin 2) (FixedPoints.subfield A F)) (i j : Fin 2) :
    fixedSL2Inclusion F A X i j = (X i j : F) := rfl

theorem fixedSL2Inclusion_injective (F : Type u) [Field F] (A : Subgroup (F ≃+* F)) :
    Function.Injective (fixedSL2Inclusion F A) := by
  intro X Y h
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  apply Subtype.ext
  exact congrArg (fun Z : Matrix.SpecialLinearGroup (Fin 2) F => Z i j) h

theorem entries_mem_fixed_iff (F : Type u) [Field F] (A : Subgroup (F ≃+* F))
    (X : Matrix.SpecialLinearGroup (Fin 2) F) :
    (∀ i j, X i j ∈ FixedPoints.subfield A F) ↔
      ∀ a : A, Matrix.SpecialLinearGroup.map a.val.toRingHom X = X := by
  constructor
  · intro h a
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact (h i j) a
  · intro h i j a
    exact congrArg (fun Z : Matrix.SpecialLinearGroup (Fin 2) F => Z i j) (h a)

theorem fixedSL2Inclusion_range (F : Type u) [Field F] (A : Subgroup (F ≃+* F))
    (X : Matrix.SpecialLinearGroup (Fin 2) F) :
    X ∈ (fixedSL2Inclusion F A).range ↔ ∀ i j, X i j ∈ FixedPoints.subfield A F := by
  constructor
  · rintro ⟨Y, rfl⟩ i j
    exact (Y i j).property
  · intro hX
    let Y : Matrix (Fin 2) (Fin 2) (FixedPoints.subfield A F) :=
      fun i j => ⟨X i j, hX i j⟩
    have hY : Y.det = 1 := by
      apply Subtype.ext
      change (FixedPoints.subfield A F).subtype Y.det = 1
      rw [RingHom.map_det]
      exact X.property
    exact ⟨⟨Y, hY⟩, rfl⟩

@[expose] def fixedEntrySL2 (F : Type u) [Field F] (A : Subgroup (F ≃+* F)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) := (fixedSL2Inclusion F A).range

theorem mem_fixedEntrySL2 (F : Type u) [Field F] (A : Subgroup (F ≃+* F))
    (X : Matrix.SpecialLinearGroup (Fin 2) F) :
    X ∈ fixedEntrySL2 F A ↔ ∀ a : A, Matrix.SpecialLinearGroup.map a.val.toRingHom X = X :=
  (fixedSL2Inclusion_range F A X).trans (entries_mem_fixed_iff F A X)

@[expose] def fixedSL2EquivRange (F : Type u) [Field F] (A : Subgroup (F ≃+* F)) :
    Matrix.SpecialLinearGroup (Fin 2) (FixedPoints.subfield A F) ≃* fixedEntrySL2 F A :=
  MonoidHom.ofInjective (fixedSL2Inclusion_injective F A)

@[expose] def conjugateIn {H : Type v} [Group H] (N : Subgroup H) [N.Normal]
    (e : H) : MulAut N := internalAction N ⊤ ⟨e, trivial⟩

theorem conjugateIn_coe {H : Type v} [Group H] (N : Subgroup H) [N.Normal]
    (e : H) (x : N) : (conjugateIn N e x : H) = e * x * e⁻¹ :=
  internalAction_coe N ⊤ ⟨e, trivial⟩ x

theorem compatible_conjugation_entrywise {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (p : ℕ) [CharP F p] (hp : Odd p)
    (N : Subgroup H) [N.Normal] (eta : N ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (chi : H →* Equiv.Perm (Omega F))
    (heta : ∀ x : N, slCoordinateAction F (eta x) = chi x)
    (e : H) (sigma : F ≃+* F) (he : chi e = fieldExtension F sigma) (x : N) :
    eta (conjugateIn N e x) = Matrix.SpecialLinearGroup.map sigma.toRingHom (eta x) := by
  let alpha : Matrix.SpecialLinearGroup (Fin 2) F →*
      Matrix.SpecialLinearGroup (Fin 2) F :=
    eta.toMonoidHom.comp ((conjugateIn N e).toMonoidHom.comp eta.symm.toMonoidHom)
  let beta : Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) F :=
    Matrix.SpecialLinearGroup.map sigma.toRingHom
  have hproj : ∀ X, slCoordinateAction F (alpha X) = slCoordinateAction F (beta X) := by
    intro X
    change slCoordinateAction F (eta (conjugateIn N e (eta.symm X))) = _
    rw [heta, conjugateIn_coe, map_mul, map_mul, map_inv, he,
      ← heta (eta.symm X), eta.apply_symm_apply]
    exact (slCoordinateAction_field F sigma X).symm
  have hab := hom_eq_of_projective_eq p hp alpha beta hproj
  have h := DFunLike.congr_fun hab (eta x)
  change eta (conjugateIn N e (eta.symm (eta x))) = _ at h
  rw [eta.symm_apply_apply] at h
  exact h

theorem eSigma_action {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hcard : Nat.card F = p ^ f)
    (A : Subgroup (F ≃+* F)) (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A))
    (eta : Lambda F A pi ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (heta : ∀ x : Lambda F A pi, slCoordinateAction F (eta x) = coordinateProjection F A pi x)
    (sigma : A) (x : Lambda F A pi) :
    eta (conjugateIn (Lambda F A pi) (eSigma F A pi hpi z hz hzc hker hd sigma) x) =
      Matrix.SpecialLinearGroup.map sigma.val.toRingHom (eta x) := by
  let : CharP F p := CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hcard
  exact compatible_conjugation_entrywise F p hpodd _ eta (coordinateProjection F A pi) heta
    _ sigma (eSigma_projective F A pi hpi z hz hzc hker hd sigma) x

theorem E_action {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hcard : Nat.card F = p ^ f)
    (A : Subgroup (F ≃+* F)) (pi : H →* Gamma F A)
    (z : H) (hzc : z ∈ Subgroup.center H) (hker : pi.ker = Subgroup.zpowers z)
    (eta : Lambda F A pi ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (heta : ∀ x : Lambda F A pi, slCoordinateAction F (eta x) = coordinateProjection F A pi x)
    (e : E F A pi z hzc hker) (sigma : A)
    (he : coordinateProjection F A pi e = fieldExtension F sigma) (x : Lambda F A pi) :
    eta (conjugateIn (Lambda F A pi) e x) =
      Matrix.SpecialLinearGroup.map sigma.val.toRingHom (eta x) := by
  let : CharP F p := CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hcard
  exact compatible_conjugation_entrywise F p hpodd _ eta (coordinateProjection F A pi) heta
    e sigma he x

theorem B_isComplement {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    ((Subgroup.zpowers z).subgroupOf (B F A pi)).IsComplement'
      ((E F A pi z hzc hker).subgroupOf (B F A pi)) := by
  have h := oddRoots_isComplement pi hpi z hz hker (gammaField F A)
    ((gammaField_card F A).symm ▸ hd) (B_isMulCommutative F A pi z hzc hker)
  unfold E
  rwa [gammaField_card] at h

theorem kernel_le_B {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (z : H) (hker : pi.ker = Subgroup.zpowers z) :
    Subgroup.zpowers z ≤ B F A pi := hker ▸ pi.ker_le_comap (gammaField F A)

theorem kernel_central_in_B {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (z : H) (hzc : z ∈ Subgroup.center H) :
    (Subgroup.zpowers z).subgroupOf (B F A pi) ≤ Subgroup.center (B F A pi) := by
  intro k hk
  apply Subgroup.mem_center_iff.mpr
  intro b
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hzc hk) b

@[expose] def BDirectEquiv {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    Subgroup.zpowers z × E F A pi z hzc hker ≃* B F A pi :=
  ((Subgroup.subgroupOfEquivOfLe (kernel_le_B F A pi z hker)).symm.prodCongr
    (Subgroup.subgroupOfEquivOfLe (show E F A pi z hzc hker ≤ B F A pi from fun _ h => h.1)).symm).trans
    (internalDirectEquiv _ _ (kernel_central_in_B F A pi z hzc)
      (B_isComplement F A pi hpi z hz hzc hker hd))

theorem BDirectEquiv_coe {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A))
    (x : Subgroup.zpowers z × E F A pi z hzc hker) :
    (BDirectEquiv F A pi hpi z hz hzc hker hd x : H) = (x.1 : H) * x.2 := rfl

theorem SpecialPreimage_factorization {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A))
    (x : SpecialPreimage F A pi) :
    ∃ l : Lambda F A pi, ∃ e : E F A pi z hzc hker, (x : H) = l * e := by
  have hx : ((pi (x : H) : Gamma F A) : coordinateE F) ∈ SpecialGamma F A := x.property
  obtain ⟨l, hl, a, ha, hla⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  let aG : gammaField F A := ⟨⟨a, (show liftedField F A ≤ Gamma F A from le_sup_right) ha⟩, ha⟩
  let e := (piOnE F A pi hpi z hz hzc hker hd).symm aG
  have he : pi e = aG := (piOnE_coe F A pi hpi z hz hzc hker hd e).symm.trans
    (congrArg Subtype.val ((piOnE F A pi hpi z hz hzc hker hd).apply_symm_apply aG))
  have he' : ((pi e : Gamma F A) : coordinateE F) = a := congrArg Subtype.val he
  have hm : (x : H) * (e : H)⁻¹ ∈ Lambda F A pi := by
    change ((pi ((x : H) * (e : H)⁻¹) : Gamma F A) : coordinateE F) ∈ specialLayer F
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, he', ← hla]
    rw [mul_assoc, mul_inv_cancel, mul_one]
    exact hl
  exact ⟨⟨(x : H) * (e : H)⁻¹, hm⟩, e, by simp only [mul_assoc, inv_mul_cancel, mul_one]⟩

theorem SpecialPreimage_isComplement {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    ((Lambda F A pi).subgroupOf (SpecialPreimage F A pi)).IsComplement'
      ((E F A pi z hzc hker).subgroupOf (SpecialPreimage F A pi)) := by
  apply factorization_isComplement (SpecialPreimage F A pi) (Lambda F A pi) (E F A pi z hzc hker)
  · intro x hx
    exact (show specialLayer F ≤ SpecialGamma F A from le_sup_left) hx
  · intro e he
    exact (show liftedField F A ≤ SpecialGamma F A from le_sup_right) he.1
  · exact (H_isComplement F A pi hpi z hz hzc hker hd).disjoint.mono_left
      (fun _ h => Subgroup.subgroupOf_mono (coordinateE F) (coordinateG_le_D F) h)
  · exact SpecialPreimage_factorization F A pi hpi z hz hzc hker hd

@[expose] def SpecialPreimageSemidirectEquiv {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    (Lambda F A pi).subgroupOf (SpecialPreimage F A pi) ⋊[
      internalAction ((Lambda F A pi).subgroupOf (SpecialPreimage F A pi))
        ((E F A pi z hzc hker).subgroupOf (SpecialPreimage F A pi))]
      (E F A pi z hzc hker).subgroupOf (SpecialPreimage F A pi) ≃* SpecialPreimage F A pi :=
  internalSemidirectEquiv _ _ (SpecialPreimage_isComplement F A pi hpi z hz hzc hker hd)

abbrev LambdaCentralizer {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (z : H) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) :=
  (Subgroup.centralizer (E F A pi z hzc hker : Set H)).subgroupOf (Lambda F A pi)

theorem mem_LambdaCentralizer_iff {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hcard : Nat.card F = p ^ f)
    (A : Subgroup (F ≃+* F)) (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A))
    (eta : Lambda F A pi ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (heta : ∀ x : Lambda F A pi, slCoordinateAction F (eta x) = coordinateProjection F A pi x)
    (x : Lambda F A pi) :
    x ∈ LambdaCentralizer F A pi z hzc hker ↔
      ∀ sigma : A, Matrix.SpecialLinearGroup.map sigma.val.toRingHom (eta x) = eta x := by
  constructor
  · intro hx sigma
    let e := eSigma F A pi hpi z hz hzc hker hd sigma
    have hc : (e : H) * x = (x : H) * e :=
      Subgroup.mem_centralizer_iff.mp hx e e.property
    have hc' : conjugateIn (Lambda F A pi) e x = x := by
      apply Subtype.ext
      rw [conjugateIn_coe, hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [← eSigma_action F hp hpodd hcard A pi hpi z hz hzc hker hd eta heta sigma x, hc']
  · intro hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro e he
    let eE : E F A pi z hzc hker := ⟨e, he⟩
    let sigma := EEquivField F A pi hpi z hz hzc hker hd eE
    have heq : eSigma F A pi hpi z hz hzc hker hd sigma = eE :=
      (EEquivField F A pi hpi z hz hzc hker hd).symm_apply_apply eE
    have heaction : eta (conjugateIn (Lambda F A pi) e x) = eta x := by
      have h := eSigma_action F hp hpodd hcard A pi hpi z hz hzc hker hd eta heta sigma x
      rw [heq, hx sigma] at h
      exact h
    have hefix : conjugateIn (Lambda F A pi) e x = x := eta.injective heaction
    have hh := congrArg (fun y : Lambda F A pi => (y : H)) hefix
    rw [conjugateIn_coe] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh

theorem eta_centralizer_image {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hcard : Nat.card F = p ^ f)
    (A : Subgroup (F ≃+* F)) (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A))
    (eta : Lambda F A pi ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (heta : ∀ x : Lambda F A pi, slCoordinateAction F (eta x) = coordinateProjection F A pi x) :
    (LambdaCentralizer F A pi z hzc hker).map eta.toMonoidHom = fixedEntrySL2 F A := by
  ext X
  rw [mem_fixedEntrySL2]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_LambdaCentralizer_iff F hp hpodd hcard A pi hpi z hz hzc hker hd eta heta x).mp hx
  · intro hX
    refine ⟨eta.symm X, ?_, eta.apply_symm_apply X⟩
    apply (mem_LambdaCentralizer_iff F hp hpodd hcard A pi hpi z hz hzc hker hd eta heta _).mpr
    rwa [eta.apply_symm_apply]

@[expose] def fixedCentralizerEquiv {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hcard : Nat.card F = p ^ f)
    (A : Subgroup (F ≃+* F)) (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A))
    (eta : Lambda F A pi ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (heta : ∀ x : Lambda F A pi, slCoordinateAction F (eta x) = coordinateProjection F A pi x) :
    LambdaCentralizer F A pi z hzc hker ≃*
      Matrix.SpecialLinearGroup (Fin 2) (FixedPoints.subfield A F) :=
  (eta.subgroupMap (LambdaCentralizer F A pi z hzc hker)).trans
    ((subgroupEquivOfEq (eta_centralizer_image F hp hpodd hcard A pi hpi z hz hzc hker hd eta heta)).trans
      (fixedSL2EquivRange F A).symm)

theorem fixedCentralizerEquiv_inclusion {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hcard : Nat.card F = p ^ f)
    (A : Subgroup (F ≃+* F)) (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A))
    (eta : Lambda F A pi ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (heta : ∀ x : Lambda F A pi, slCoordinateAction F (eta x) = coordinateProjection F A pi x)
    (x : LambdaCentralizer F A pi z hzc hker) :
    fixedSL2Inclusion F A
      (fixedCentralizerEquiv F hp hpodd hcard A pi hpi z hz hzc hker hd eta heta x) = eta x := by
  have h := (fixedSL2EquivRange F A).apply_symm_apply
    ((subgroupEquivOfEq (eta_centralizer_image F hp hpodd hcard A pi hpi z hz hzc hker hd eta heta))
      (eta.subgroupMap (LambdaCentralizer F A pi z hzc hker) x))
  exact congrArg Subtype.val h


theorem Lambda_le_M {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) : Lambda F A pi ≤ M F A pi :=
  fun _ h => Subgroup.subgroupOf_mono (coordinateE F) (coordinateG_le_D F) h

theorem Lambda_le_SpecialPreimage {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) : Lambda F A pi ≤ SpecialPreimage F A pi :=
  fun _ h => (show specialLayer F ≤ SpecialGamma F A from le_sup_left) h

theorem E_le_SpecialPreimage {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (z : H) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) :
    E F A pi z hzc hker ≤ SpecialPreimage F A pi :=
  fun _ h => (show liftedField F A ≤ SpecialGamma F A from le_sup_right) h.1

theorem SpecialPreimage_eq_sup {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    SpecialPreimage F A pi = Lambda F A pi ⊔ E F A pi z hzc hker := by
  apply le_antisymm
  · intro x hx
    obtain ⟨l, e, h⟩ := SpecialPreimage_factorization F A pi hpi z hz hzc hker hd ⟨x, hx⟩
    change x = (l : H) * e at h
    rw [h]
    exact (Lambda F A pi ⊔ E F A pi z hzc hker).mul_mem
      ((show Lambda F A pi ≤ Lambda F A pi ⊔ E F A pi z hzc hker from le_sup_left) l.property)
      ((show E F A pi z hzc hker ≤ Lambda F A pi ⊔ E F A pi z hzc hker from le_sup_right) e.property)
  · exact sup_le (Lambda_le_SpecialPreimage F A pi) (E_le_SpecialPreimage F A pi z hzc hker)

theorem HSemidirectEquiv_apply {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A))
    (x : M F A pi ⋊[internalAction (M F A pi) (E F A pi z hzc hker)] E F A pi z hzc hker) :
    HSemidirectEquiv F A pi hpi z hz hzc hker hd x = (x.left : H) * x.right :=
  internalSemidirectEquiv_apply _ _ (H_isComplement F A pi hpi z hz hzc hker hd) x

@[expose] def specialSemidirectEquiv {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) :
    Lambda F A pi ⋊[internalAction (Lambda F A pi) (E F A pi z hzc hker)]
      E F A pi z hzc hker ≃* SpecialPreimage F A pi := by
  let f : Lambda F A pi ⋊[internalAction (Lambda F A pi) (E F A pi z hzc hker)]
      E F A pi z hzc hker →* H :=
    SemidirectProduct.lift (Lambda F A pi).subtype (E F A pi z hzc hker).subtype
      (by intro e; apply MonoidHom.ext; intro x; exact internalAction_coe _ _ e x)
  let g := f.codRestrict (SpecialPreimage F A pi) (by
    intro x
    exact (SpecialPreimage F A pi).mul_mem
      (Lambda_le_SpecialPreimage F A pi x.left.property)
      (E_le_SpecialPreimage F A pi z hzc hker x.right.property))
  apply MulEquiv.ofBijective g
  constructor
  · intro x y hxy
    have hdis : Disjoint (Lambda F A pi) (E F A pi z hzc hker) :=
      (H_isComplement F A pi hpi z hz hzc hker hd).disjoint.mono_left (Lambda_le_M F A pi)
    have hpairs := Subgroup.mul_injective_of_disjoint hdis
      (a₁ := (x.left, x.right)) (a₂ := (y.left, y.right))
      (show (x.left : H) * x.right = (y.left : H) * y.right from congrArg Subtype.val hxy)
    exact SemidirectProduct.ext (congrArg Prod.fst hpairs) (congrArg Prod.snd hpairs)
  · intro x
    obtain ⟨l, e, hx⟩ := SpecialPreimage_factorization F A pi hpi z hz hzc hker hd x
    exact ⟨⟨l, e⟩, Subtype.ext hx.symm⟩

theorem specialSemidirectEquiv_coe {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A))
    (x : Lambda F A pi ⋊[internalAction (Lambda F A pi) (E F A pi z hzc hker)] E F A pi z hzc hker) :
    (specialSemidirectEquiv F A pi hpi z hz hzc hker hd x : H) = (x.left : H) * x.right := rfl

@[expose] def zInLambda {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (z : H) (hker : pi.ker = Subgroup.zpowers z) : Lambda F A pi :=
  ⟨z, by change pi z ∈ gammaSpecial F A; rw [pi_z pi z hker]; exact Subgroup.one_mem _⟩

theorem zInLambda_coe {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (z : H) (hker : pi.ker = Subgroup.zpowers z) :
    (zInLambda F A pi z hker : H) = z := rfl

theorem eSigma_unique {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A))
    (sigma : A) (e : E F A pi z hzc hker)
    (he : coordinateProjection F A pi e = fieldExtension F sigma) :
    e = eSigma F A pi hpi z hz hzc hker hd sigma := by
  apply (piOnE F A pi hpi z hz hzc hker hd).injective
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact he.trans (eSigma_projective F A pi hpi z hz hzc hker hd sigma).symm

theorem mem_LambdaCentralizer_iff_entries {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hcard : Nat.card F = p ^ f)
    (A : Subgroup (F ≃+* F)) (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A))
    (eta : Lambda F A pi ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (heta : ∀ x : Lambda F A pi, slCoordinateAction F (eta x) = coordinateProjection F A pi x)
    (x : Lambda F A pi) :
    x ∈ LambdaCentralizer F A pi z hzc hker ↔ ∀ i j, eta x i j ∈ FixedPoints.subfield A F :=
  (mem_LambdaCentralizer_iff F hp hpodd hcard A pi hpi z hz hzc hker hd eta heta x).trans
    (entries_mem_fixed_iff F A (eta x)).symm


theorem eSigma_pi {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hd : Odd (Nat.card A)) (sigma : A) :
    pi (eSigma F A pi hpi z hz hzc hker hd sigma) =
      ((gammaFieldEquiv F A).symm sigma : Gamma F A) :=
  congrArg Subtype.val ((piOnE F A pi hpi z hz hzc hker hd).apply_symm_apply
    ((gammaFieldEquiv F A).symm sigma))

theorem E_action_of_pi {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hcard : Nat.card F = p ^ f)
    (A : Subgroup (F ≃+* F)) (pi : H →* Gamma F A)
    (z : H) (hzc : z ∈ Subgroup.center H) (hker : pi.ker = Subgroup.zpowers z)
    (eta : Lambda F A pi ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (heta : ∀ x : Lambda F A pi, slCoordinateAction F (eta x) = coordinateProjection F A pi x)
    (e : E F A pi z hzc hker) (sigma : A)
    (he : pi e = ((gammaFieldEquiv F A).symm sigma : Gamma F A)) (x : Lambda F A pi) :
    eta (conjugateIn (Lambda F A pi) e x) =
      Matrix.SpecialLinearGroup.map sigma.val.toRingHom (eta x) := by
  apply E_action F hp hpodd hcard A pi z hzc hker eta heta e sigma
  change (((pi e : Gamma F A) : coordinateE F) : Equiv.Perm (Omega F)) = _
  rw [he, gammaFieldEquiv_symm_coe]

structure ExactLiftConclusions {H : Type v} [Group H]
    (F : Type u) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z) (hdA : Odd (Nat.card A))
    (eta : Lambda F A pi ≃* Matrix.SpecialLinearGroup (Fin 2) F) (d : ℕ) : Prop where
  gamma_internal : (gammaLinear F A).IsComplement' (gammaField F A)
  gamma_semidirect : ∃ eps : gammaLinear F A ⋊[internalAction (gammaLinear F A) (gammaField F A)]
    gammaField F A ≃* Gamma F A, ∀ x, eps x = (x.left : Gamma F A) * x.right
  roots : ∀ b : H, b ∈ E F A pi z hzc hker ↔ b ∈ B F A pi ∧ b ^ d = 1
  card : Nat.card (E F A pi z hzc hker) = d
  unique : ∀ U : Subgroup (B F A pi), Nat.card U = d →
    U = (E F A pi z hzc hker).subgroupOf (B F A pi)
  pi_restriction : ∃ eps : E F A pi z hzc hker ≃* gammaField F A,
    ∀ e : E F A pi z hzc hker, (eps e : Gamma F A) = pi e
  B_internal : ((Subgroup.zpowers z).subgroupOf (B F A pi)).IsComplement'
    ((E F A pi z hzc hker).subgroupOf (B F A pi))
  kernel_central : (Subgroup.zpowers z).subgroupOf (B F A pi) ≤ Subgroup.center (B F A pi)
  B_direct : ∃ eps : Subgroup.zpowers z × E F A pi z hzc hker ≃* B F A pi,
    ∀ x, (eps x : H) = (x.1 : H) * x.2
  M_normal : (M F A pi).Normal
  Lambda_normal : (Lambda F A pi).Normal
  H_internal : (M F A pi).IsComplement' (E F A pi z hzc hker)
  H_semidirect : ∃ eps : M F A pi ⋊[internalAction (M F A pi) (E F A pi z hzc hker)]
    E F A pi z hzc hker ≃* H, ∀ x, eps x = (x.left : H) * x.right
  special_eq : SpecialPreimage F A pi = Lambda F A pi ⊔ E F A pi z hzc hker
  special_internal : ((Lambda F A pi).subgroupOf (SpecialPreimage F A pi)).IsComplement'
    ((E F A pi z hzc hker).subgroupOf (SpecialPreimage F A pi))
  special_semidirect : ∃ eps : Lambda F A pi ⋊[internalAction (Lambda F A pi) (E F A pi z hzc hker)]
    E F A pi z hzc hker ≃* SpecialPreimage F A pi, ∀ x, (eps x : H) = (x.left : H) * x.right
  sigma_lift : ∀ sigma : A, pi (eSigma F A pi hpi z hz hzc hker hdA sigma) =
    ((gammaFieldEquiv F A).symm sigma : Gamma F A)
  sigma_unique : ∀ sigma : A, ∀ e : E F A pi z hzc hker,
    pi e = ((gammaFieldEquiv F A).symm sigma : Gamma F A) →
      e = eSigma F A pi hpi z hz hzc hker hdA sigma
  sigma_action : ∀ sigma : A, ∀ x : Lambda F A pi,
    eta (conjugateIn (Lambda F A pi) (eSigma F A pi hpi z hz hzc hker hdA sigma) x) =
      Matrix.SpecialLinearGroup.map sigma.val.toRingHom (eta x)
  action : ∀ e : E F A pi z hzc hker, ∀ sigma : A,
    pi e = ((gammaFieldEquiv F A).symm sigma : Gamma F A) → ∀ x : Lambda F A pi,
      eta (conjugateIn (Lambda F A pi) e x) = Matrix.SpecialLinearGroup.map sigma.val.toRingHom (eta x)
  action_entries : ∀ e : E F A pi z hzc hker, ∀ sigma : A,
    pi e = ((gammaFieldEquiv F A).symm sigma : Gamma F A) → ∀ x : Lambda F A pi, ∀ i j : Fin 2,
      eta (conjugateIn (Lambda F A pi) e x) i j = sigma.val (eta x i j)
  centralizer_entries : ∀ x : Lambda F A pi,
    x ∈ LambdaCentralizer F A pi z hzc hker ↔ ∀ i j, eta x i j ∈ FixedPoints.subfield A F
  centralizer_image : (LambdaCentralizer F A pi z hzc hker).map eta.toMonoidHom = fixedEntrySL2 F A
  fixed_equiv : ∃ eps : LambdaCentralizer F A pi z hzc hker ≃*
    Matrix.SpecialLinearGroup (Fin 2) (FixedPoints.subfield A F),
    ∀ x, fixedSL2Inclusion F A (eps x) = eta x

theorem central_double_cover_lifts_odd_field_action_exactly {H : Type v} [Group H] [Finite H]
    (F : Type u) [Field F] [Finite F] {p f d : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (_hf : 1 ≤ f) (hcard : Nat.card F = p ^ f)
    (A : Subgroup (F ≃+* F)) (hAd : Nat.card A = d) (hd : Odd d)
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z)
    (eta : Lambda F A pi ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (_hetaz : eta (zInLambda F A pi z hker) = (-1 : Matrix.SpecialLinearGroup (Fin 2) F))
    (heta : ∀ x : Lambda F A pi, slCoordinateAction F (eta x) = coordinateProjection F A pi x) :
    ExactLiftConclusions F A pi hpi z hz hzc hker (hAd.symm ▸ hd) eta d := by
  let hdA : Odd (Nat.card A) := hAd.symm ▸ hd
  refine
    { gamma_internal := gamma_isComplement F A
      gamma_semidirect := ⟨gammaSemidirectEquiv F A,
        internalSemidirectEquiv_apply _ _ (gamma_isComplement F A)⟩
      roots := ?_
      card := (E_card F A pi hpi z hz hzc hker hdA).trans hAd
      unique := ?_
      pi_restriction := ⟨piOnE F A pi hpi z hz hzc hker hdA,
        piOnE_coe F A pi hpi z hz hzc hker hdA⟩
      B_internal := B_isComplement F A pi hpi z hz hzc hker hdA
      kernel_central := kernel_central_in_B F A pi z hzc
      B_direct := ⟨BDirectEquiv F A pi hpi z hz hzc hker hdA,
        BDirectEquiv_coe F A pi hpi z hz hzc hker hdA⟩
      M_normal := inferInstance
      Lambda_normal := inferInstance
      H_internal := H_isComplement F A pi hpi z hz hzc hker hdA
      H_semidirect := ⟨HSemidirectEquiv F A pi hpi z hz hzc hker hdA,
        HSemidirectEquiv_apply F A pi hpi z hz hzc hker hdA⟩
      special_eq := SpecialPreimage_eq_sup F A pi hpi z hz hzc hker hdA
      special_internal := SpecialPreimage_isComplement F A pi hpi z hz hzc hker hdA
      special_semidirect := ⟨specialSemidirectEquiv F A pi hpi z hz hzc hker hdA,
        specialSemidirectEquiv_coe F A pi hpi z hz hzc hker hdA⟩
      sigma_lift := eSigma_pi F A pi hpi z hz hzc hker hdA
      sigma_unique := ?_
      sigma_action := eSigma_action F hp hpodd hcard A pi hpi z hz hzc hker hdA eta heta
      action := E_action_of_pi F hp hpodd hcard A pi z hzc hker eta heta
      action_entries := ?_
      centralizer_entries := mem_LambdaCentralizer_iff_entries F hp hpodd hcard A pi hpi z hz hzc hker hdA eta heta
      centralizer_image := eta_centralizer_image F hp hpodd hcard A pi hpi z hz hzc hker hdA eta heta
      fixed_equiv := ⟨fixedCentralizerEquiv F hp hpodd hcard A pi hpi z hz hzc hker hdA eta heta,
        fixedCentralizerEquiv_inclusion F hp hpodd hcard A pi hpi z hz hzc hker hdA eta heta⟩ }
  · intro b
    rw [← hAd]
    exact mem_E F A pi z hzc hker b
  · intro U hU
    exact E_unique F A pi hpi z hz hzc hker hdA U (hU.trans hAd.symm)
  · intro sigma e he
    apply eSigma_unique F A pi hpi z hz hzc hker hdA sigma e
    change (((pi e : Gamma F A) : coordinateE F) : Equiv.Perm (Omega F)) = _
    rw [he, gammaFieldEquiv_symm_coe]
  · intro e sigma he x i j
    exact congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F => X i j)
      (E_action_of_pi F hp hpodd hcard A pi z hzc hker eta heta e sigma he x)

theorem central_double_cover_lifts_odd_field_action_exactly_int {H : Type v} [Group H] [Finite H]
    (F : Type u) [Field F] [Finite F] {p d : ℕ} {f : ℤ}
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f.toNat)
    (A : Subgroup (F ≃+* F)) (hAd : Nat.card A = d) (hd : Odd d)
    (pi : H →* Gamma F A) (hpi : Function.Surjective pi)
    (z : H) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center H)
    (hker : pi.ker = Subgroup.zpowers z)
    (eta : Lambda F A pi ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hetaz : eta (zInLambda F A pi z hker) = (-1 : Matrix.SpecialLinearGroup (Fin 2) F))
    (heta : ∀ x : Lambda F A pi, slCoordinateAction F (eta x) = coordinateProjection F A pi x) :
    ExactLiftConclusions F A pi hpi z hz hzc hker (hAd.symm ▸ hd) eta d :=
  central_double_cover_lifts_odd_field_action_exactly F hp hpodd (by omega) hcard A hAd hd
    pi hpi z hz hzc hker eta hetaz heta


end

end CFSG.Semidihedral.OddFieldLift
