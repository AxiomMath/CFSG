module

public import CFSG.LocalAnalysis.ComponentInitial.LinearSymplecticInvolution
public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open scoped commutatorElement

namespace ExtraspecialFixed

section Commutators

variable {Q : Type*} [Group Q]

theorem commutatorElement_mem_commutator (x y : Q) : ⁅x, y⁆ ∈ commutator Q := by
  rw [_root_.commutator_def]
  exact commutator_mem_commutator (mem_top x) (mem_top y)

theorem commutatorElement_mul_right_of_mem_center {x y y' : Q} (h : ⁅x, y'⁆ ∈ center Q) :
    ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  have hc : ⁅x, y'⁆ * y⁻¹ = y⁻¹ * ⁅x, y'⁆ := (mem_center_iff.1 h y⁻¹).symm
  calc ⁅x, y * y'⁆ = x * y * x⁻¹ * (⁅x, y'⁆ * y⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = x * y * x⁻¹ * (y⁻¹ * ⁅x, y'⁆) := by rw [hc]
    _ = ⁅x, y⁆ * ⁅x, y'⁆ := by simp only [commutatorElement_def]; group

theorem commutatorElement_mul_left_of_mem_center {x x' y : Q} (h : ⁅x', y⁆ ∈ center Q) :
    ⁅x * x', y⁆ = ⁅x, y⁆ * ⁅x', y⁆ := by
  have hc : x * ⁅x', y⁆ = ⁅x', y⁆ * x := mem_center_iff.1 h x
  have hc' : ⁅x', y⁆ * ⁅x, y⁆ = ⁅x, y⁆ * ⁅x', y⁆ := (mem_center_iff.1 h ⁅x, y⁆).symm
  calc ⁅x * x', y⁆ = x * ⁅x', y⁆ * y * x⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅x', y⁆ * ⁅x, y⁆ := by rw [hc]; simp only [commutatorElement_def]; group
    _ = ⁅x, y⁆ * ⁅x', y⁆ := hc'

theorem sq_mem_center (hc : commutator Q ≤ center Q) (h2 : ∀ z ∈ center Q, z ^ 2 = 1)
    (x : Q) : x ^ 2 ∈ center Q := by
  rw [mem_center_iff]
  intro y
  have hxy : ⁅x, y⁆ ∈ center Q := hc (commutatorElement_mem_commutator x y)
  have hxy' : x * y = ⁅x, y⁆ * y * x := by simp only [commutatorElement_def]; group
  have hcx : x * ⁅x, y⁆ = ⁅x, y⁆ * x := mem_center_iff.1 hxy x
  have hsq : ⁅x, y⁆ * ⁅x, y⁆ = 1 := by rw [← sq]; exact h2 _ hxy
  generalize ⁅x, y⁆ = c at hxy' hcx hsq
  symm
  calc x ^ 2 * y = x * (x * y) := by rw [sq, mul_assoc]
    _ = x * c * y * x := by rw [hxy']; simp only [mul_assoc]
    _ = c * (x * y) * x := by rw [hcx]; simp only [mul_assoc]
    _ = c * c * y * (x * x) := by rw [hxy']; simp only [mul_assoc]
    _ = y * x ^ 2 := by rw [hsq, one_mul, sq]

theorem eq_of_ne_one_of_card_eq_two (h : Nat.card Q = 2) {a b : Q} (ha : a ≠ 1) (hb : b ≠ 1) :
    a = b := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Q)).1 h
  exact (hy a ha).trans (hy b hb).symm

theorem pow_two_eq_one_of_card_eq_two (h : Nat.card Q = 2) (a : Q) : a ^ 2 = 1 := by
  rw [← h]
  exact pow_card_eq_one'

theorem exists_ofMul_of (v : Additive (Abelianization Q)) :
    ∃ q : Q, Additive.ofMul (Abelianization.of q) = v := by
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective v.toMul
  refine ⟨q, ?_⟩
  change Additive.ofMul (QuotientGroup.mk q : Abelianization Q) = v
  rw [hq]
  rfl

end Commutators

section Form

variable {Q : Type*} [Group Q] (hc : commutator Q ≤ center Q)

@[expose] def commRight (x : Q) : Q →* center Q where
  toFun y := ⟨⁅x, y⁆, hc (commutatorElement_mem_commutator x y)⟩
  map_one' := Subtype.ext (commutatorElement_one_right x)
  map_mul' _ y' := Subtype.ext
    (commutatorElement_mul_right_of_mem_center (hc (commutatorElement_mem_commutator x y')))

theorem commRight_apply (x y : Q) : (commRight hc x y : Q) = ⁅x, y⁆ := rfl

@[expose] def commPairing (χ : center Q →* Multiplicative (ZMod 2)) :
    Abelianization Q →* Abelianization Q →* Multiplicative (ZMod 2) :=
  Abelianization.lift
    { toFun := fun x => Abelianization.lift (χ.comp (commRight hc x))
      map_one' := Abelianization.hom_ext _ _ (MonoidHom.ext fun y => by
        change χ (commRight hc 1 y) = 1
        rw [show commRight hc 1 y = 1 from Subtype.ext (commutatorElement_one_left y), map_one])
      map_mul' := fun x x' => Abelianization.hom_ext _ _ (MonoidHom.ext fun y => by
        change χ (commRight hc (x * x') y) = χ (commRight hc x y) * χ (commRight hc x' y)
        rw [← map_mul]
        exact congrArg χ (Subtype.ext (commutatorElement_mul_left_of_mem_center
          (hc (commutatorElement_mem_commutator x' y))))) }

theorem commPairing_of (χ : center Q →* Multiplicative (ZMod 2)) (x y : Q) :
    commPairing hc χ (Abelianization.of x) (Abelianization.of y) = χ (commRight hc x y) := rfl

@[expose] def commFormLeft (χ : center Q →* Multiplicative (ZMod 2))
    (w : Additive (Abelianization Q)) : Additive (Abelianization Q) →+ ZMod 2 :=
  AddMonoidHom.mk'
    (fun v => Multiplicative.toAdd (commPairing hc χ (Additive.toMul v) (Additive.toMul w)))
    fun v v' => by simp

@[expose] def commFormRight (χ : center Q →* Multiplicative (ZMod 2))
    (v : Additive (Abelianization Q)) : Additive (Abelianization Q) →+ ZMod 2 :=
  AddMonoidHom.mk'
    (fun w => Multiplicative.toAdd (commPairing hc χ (Additive.toMul v) (Additive.toMul w)))
    fun w w' => by simp

variable [Module (ZMod 2) (Additive (Abelianization Q))]

@[expose] def commForm (χ : center Q →* Multiplicative (ZMod 2)) :
    LinearMap.BilinForm (ZMod 2) (Additive (Abelianization Q)) :=
  LinearMap.mk₂ (ZMod 2)
    (fun v w => Multiplicative.toAdd (commPairing hc χ (Additive.toMul v) (Additive.toMul w)))
    (fun v v' w => map_add (commFormLeft hc χ w) v v')
    (fun c v w => ZMod.map_smul (commFormLeft hc χ w) c v)
    (fun v w w' => map_add (commFormRight hc χ v) w w')
    (fun c v w => ZMod.map_smul (commFormRight hc χ v) c w)

theorem commForm_apply (χ : center Q →* Multiplicative (ZMod 2)) (x y : Q) :
    commForm hc χ (Additive.ofMul (Abelianization.of x)) (Additive.ofMul (Abelianization.of y)) =
      Multiplicative.toAdd (χ (commRight hc x y)) := rfl

theorem commForm_nondegenerate [Finite Q] (hcz : center Q ≤ commutator Q)
    {χ : center Q →* Multiplicative (ZMod 2)} (hχ : Function.Injective χ) :
    (commForm hc χ).Nondegenerate := by
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun v hv => ?_
  obtain ⟨x, rfl⟩ := exists_ofMul_of v
  have hx : x ∈ center Q := mem_center_iff.2 fun y => by
    have h := hv (Additive.ofMul (Abelianization.of y))
    rw [commForm_apply, toAdd_eq_zero] at h
    have h1 : commRight hc x y = 1 := hχ (h.trans (map_one χ).symm)
    exact (commutatorElement_eq_one_iff_mul_comm.1 (congrArg Subtype.val h1)).symm
  have hof : Abelianization.of x = 1 := by
    rw [← MonoidHom.mem_ker, Abelianization.ker_of]
    exact hcz hx
  rw [hof]
  rfl

end Form

section Conj

variable {H : Type*} [Group H] {Q : Subgroup H} [Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

@[expose] def conjEnd : H →* Module.End (ZMod 2) (Additive (Abelianization Q)) where
  toFun g := (MonoidHom.toAdditive
    (Abelianization.map (MulAut.conjNormal g).toMonoidHom)).toZModLinearMap 2
  map_one' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨q, rfl⟩ := exists_ofMul_of v
    change Additive.ofMul (Abelianization.of (MulAut.conjNormal (1 : H) q)) = _
    rw [map_one]
    rfl
  map_mul' g g' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨q, rfl⟩ := exists_ofMul_of v
    change Additive.ofMul (Abelianization.of (MulAut.conjNormal (g * g') q)) =
      Additive.ofMul (Abelianization.of (MulAut.conjNormal g (MulAut.conjNormal g' q)))
    rw [map_mul]
    rfl

@[expose] def conjGL : H →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive (Abelianization Q)) :=
  conjEnd.toHomUnits

theorem conjGL_apply (g : H) (q : Q) :
    ((conjGL g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive (Abelianization Q))) :
        Additive (Abelianization Q) →ₗ[ZMod 2] Additive (Abelianization Q))
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul (Abelianization.of (MulAut.conjNormal g q)) := rfl

theorem conjGL_mem_bilinIsometryGroup (hc : commutator Q ≤ center Q)
    (hZ : ∀ z ∈ center Q, ∀ g : H, g * (z : H) * g⁻¹ = z)
    (χ : center Q →* Multiplicative (ZMod 2)) (g : H) :
    conjGL g ∈ bilinIsometryGroup (commForm hc χ) := by
  intro v w
  obtain ⟨x, rfl⟩ := exists_ofMul_of v
  obtain ⟨y, rfl⟩ := exists_ofMul_of w
  rw [conjGL_apply, conjGL_apply, commForm_apply, commForm_apply]
  congr 2
  apply Subtype.ext
  rw [commRight_apply, commRight_apply, ← map_commutatorElement]
  exact Subtype.ext (hZ _ (hc (commutatorElement_mem_commutator x y)) g)

end Conj

theorem conj_eq_of_mem_center {H : Type*} [Group H] {Q : Subgroup H} (hQn : Q.Normal)
    (h2 : Nat.card (center Q) = 2) {z : Q} (hz : z ∈ center Q) (g : H) :
    g * (z : H) * g⁻¹ = z := by
  have hz' : (⟨g * z * g⁻¹, hQn.conj_mem z z.2 g⟩ : Q) ∈ center Q := by
    rw [mem_center_iff]
    intro q
    apply Subtype.ext
    have hq : g⁻¹ * q * g ∈ Q := by simpa using hQn.conj_mem q q.2 g⁻¹
    have hcomm := congrArg Subtype.val (mem_center_iff.1 hz ⟨g⁻¹ * q * g, hq⟩)
    change g⁻¹ * q * g * z = z * (g⁻¹ * q * g) at hcomm
    change (q : H) * (g * z * g⁻¹) = g * z * g⁻¹ * q
    calc (q : H) * (g * z * g⁻¹) = g * (g⁻¹ * q * g * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * q * g)) * g⁻¹ := by rw [hcomm]
      _ = g * z * g⁻¹ * q := by group
  by_cases h1 : z = 1
  · rw [h1]
    simp
  · have hne : (⟨⟨g * z * g⁻¹, hQn.conj_mem z z.2 g⟩, hz'⟩ : center Q) ≠ 1 := by
      intro h
      apply h1
      have h' : g * (z : H) * g⁻¹ = 1 := congrArg (fun x : center Q => ((x : Q) : H)) h
      exact Subtype.ext (by simpa using h')
    have hne' : (⟨z, hz⟩ : center Q) ≠ 1 := fun h => h1 (congrArg Subtype.val h)
    exact congrArg (fun x : center Q => ((x : Q) : H)) (eq_of_ne_one_of_card_eq_two h2 hne hne')

theorem mul_inv_mem_of_inv_mul_mem_center {H : Type*} [Group H] {Q : Subgroup H} {a b : Q}
    (h : a⁻¹ * b ∈ center Q) : (a : H) * (b : H)⁻¹ ∈ (center Q).map Q.subtype := by
  have hcomm := mem_center_iff.1 h a
  have hb : b = a⁻¹ * b * a := by rw [← hcomm, mul_inv_cancel_left]
  have hab : a * b = b * a := by
    calc a * b = a * (a⁻¹ * b * a) := by rw [← hb]
      _ = b * a := by group
  refine ⟨(a⁻¹ * b)⁻¹, inv_mem h, ?_⟩
  have hab' : Commute (a : H) b := congrArg Subtype.val hab
  change (((a⁻¹ * b)⁻¹ : Q) : H) = a * (b : H)⁻¹
  rw [mul_inv_rev, inv_inv, coe_mul, coe_inv]
  exact (Commute.inv_right hab').eq.symm

theorem isPGroup_of_forall_mem {H : Type*} [Group H] {p : ℕ} {K M : Subgroup H}
    {L : Subgroup K} (hM : IsPGroup p M) (hL : ∀ x ∈ L, (x : H) ∈ M) : IsPGroup p L := fun x => by
  obtain ⟨k, hk⟩ := hM ⟨((x : K) : H), hL x x.2⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  simpa using congrArg Subtype.val hk

variable {H : Type*} [Group H] [Finite H] {Q : Subgroup H}

theorem sq_mem_of_mem_centralizer (hQn : Q.Normal) (hQ : CFSG.IsExtraspecialPGroup 2 Q)
    (hfaith : ∀ g : H, (∀ q ∈ Q, g * q * g⁻¹ * q⁻¹ ∈ (center Q).map Q.subtype) → g ∈ Q)
    {h : H} (hh : h ^ 2 = 1)
    (hfix : ∀ q ∈ Q, h * q * h⁻¹ * q⁻¹ ∈ (center Q).map Q.subtype →
      q ∈ (Q ⊓ centralizer {h}) ⊔ (center Q).map Q.subtype)
    {g : H} (hg : g ∈ centralizer ((Q ⊓ centralizer {h} : Subgroup H) : Set H)) :
    g ^ 2 ∈ Q := by
  obtain ⟨-, hcomm, -, hcard⟩ := hQ
  have hc : commutator Q ≤ center Q := hcomm.le
  have hZ : ∀ z ∈ center Q, ∀ x : H, x * (z : H) * x⁻¹ = z :=
    fun z hz x => conj_eq_of_mem_center hQn hcard hz x
  let _ : Module (ZMod 2) (Additive (Abelianization Q)) := AddCommGroup.zmodModule fun v => by
    obtain ⟨x, rfl⟩ := exists_ofMul_of v
    rw [← ofMul_pow, ← map_pow]
    have hx : x ^ 2 ∈ commutator Q :=
      hcomm ▸ sq_mem_center hc (fun z _ => by
        have := pow_two_eq_one_of_card_eq_two hcard ⟨z, ‹_›⟩
        exact congrArg Subtype.val this) x
    rw [← Abelianization.ker_of] at hx
    rw [MonoidHom.mem_ker.1 hx]
    rfl
  let χ : center Q ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hcard (by simp)
  set b := commForm hc χ.toMonoidHom with hbdef
  have hb : b.Nondegenerate := commForm_nondegenerate hc hcomm.ge χ.injective
  have hiso : ∀ x : H, conjGL x ∈ bilinIsometryGroup b :=
    conjGL_mem_bilinIsometryGroup hc hZ χ.toMonoidHom
  have ha2 : (conjGL h : LinearMap.GeneralLinearGroup (ZMod 2) (Additive (Abelianization Q))) ^ 2
      = 1 := by
    rw [← map_pow, hh, map_one]
  have hfixed : ∀ (k : H) (q : Q),
      ((conjGL k : LinearMap.GeneralLinearGroup (ZMod 2) (Additive (Abelianization Q))) :
        Additive (Abelianization Q) →ₗ[ZMod 2] Additive (Abelianization Q))
          (Additive.ofMul (Abelianization.of q)) = Additive.ofMul (Abelianization.of q) →
        k * q * k⁻¹ * q⁻¹ ∈ (center Q).map Q.subtype := by
    intro k q hkq
    rw [conjGL_apply] at hkq
    have h1 := Additive.ofMul.injective hkq
    have h2 : (MulAut.conjNormal k q)⁻¹ * q ∈ center Q := by
      rw [← hcomm]
      exact QuotientGroup.eq.1 h1
    simpa using mul_inv_mem_of_inv_mul_mem_center h2
  obtain ⟨-, -, -, -, hEA, -⟩ :=
    binary_symplectic_involution_fixed_space_pointwise_stabilizer hb (hiso h) ha2 rfl
  have hgW : (⟨conjGL g, hiso g⟩ : bilinIsometryGroup b) ∈ pointwiseStabilizer b
      (LinearMap.ker (((conjGL h : LinearMap.GeneralLinearGroup (ZMod 2)
        (Additive (Abelianization Q))) : Additive (Abelianization Q) →ₗ[ZMod 2]
          Additive (Abelianization Q)) - 1)) := by
    rw [mem_pointwiseStabilizer]
    intro w hw
    obtain ⟨q, rfl⟩ := exists_ofMul_of w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw
    have hqUZ := hfix q q.2 (hfixed h q hw)
    have hgq : g * (q : H) = q * g := by
      have hle : (Q ⊓ centralizer {h}) ⊔ (center Q).map Q.subtype ≤ centralizer {g} := by
        refine sup_le (fun u hu => ?_) (fun z hz => ?_)
        · rw [mem_centralizer_singleton_iff]
          exact (mem_centralizer_iff.1 hg) u hu
        · obtain ⟨z, hz, rfl⟩ := hz
          rw [mem_centralizer_singleton_iff]
          have := hZ z hz g
          calc (z : H) * g = g * z * g⁻¹ * g := by rw [this]
            _ = g * z := by group
      have := mem_centralizer_singleton_iff.1 (hle hqUZ)
      exact this.symm
    change Additive.ofMul (Abelianization.of (MulAut.conjNormal g q)) = _
    congr 2
    apply Subtype.ext
    change g * (q : H) * g⁻¹ = q
    rw [hgq]
    group
  have hsq := (Monoid.exponent_dvd_iff_forall_pow_eq_one.1
    (@IsElementaryAbelian.exponent_dvd_p 2 _ _ hEA)) ⟨_, hgW⟩
  have hg2 : conjGL (g ^ 2) = (1 : LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (Abelianization Q))) := by
    rw [map_pow]
    have := congrArg (fun x : pointwiseStabilizer b _ =>
      ((x : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2)
        (Additive (Abelianization Q)))) hsq
    simpa using this
  refine hfaith _ fun q hq => hfixed (g ^ 2) ⟨q, hq⟩ ?_
  rw [hg2]
  rfl

end ExtraspecialFixed

open ExtraspecialFixed

theorem extraspecial_full_fixed_space_centralizer_normal_two_subgroup
    {H : Type*} [Group H] [Finite H] {Q Z : Subgroup H} (hQn : Q.Normal)
    (hQ : CFSG.IsExtraspecialPGroup 2 Q) (hZ : Z = (center Q).map Q.subtype)
    (hfaith : ∀ g : H, (∀ q ∈ Q, g * q * g⁻¹ * q⁻¹ ∈ Z) → g ∈ Q)
    {h : H} (hh : orderOf h = 2) {C U : Subgroup H} (hC : C = centralizer {h})
    (hU : U = Q ⊓ C) (hfix : ∀ q ∈ Q, h * q * h⁻¹ * q⁻¹ ∈ Z → q ∈ U ⊔ Z) :
    IsPGroup 2 ↥(C ⊓ centralizer (U : Set H)) ∧ CFSG.IsCharacteristicP 2 C ∧
      (∀ K : Subgroup C, ¬ CFSG.IsComponent K) ∧
      ordProj[2] (Nat.card C) ≤ Nat.card U * ordProj[2] (Nat.card (H ⧸ Q)) := by
  subst hZ hC hU
  have hh2 : h ^ 2 = 1 := by rw [← hh]; exact pow_orderOf_eq_one h
  set C := centralizer ({h} : Set H) with hCdef
  set U := Q ⊓ C with hUdef
  have hP : IsPGroup 2 ↥(C ⊓ centralizer (U : Set H)) := fun x => by
    have hx2 := sq_mem_of_mem_centralizer hQn hQ hfaith hh2 hfix x.2.2
    obtain ⟨k, hk⟩ := hQ.1 ⟨_, hx2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : ((x : H) ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    simpa [pow_succ', pow_mul] using hk'
  set U' : Subgroup C := U.subgroupOf C with hU'def
  have hU'eq : U' = Q.subgroupOf C := by rw [hU'def, hUdef, inf_subgroupOf_right]
  have hU'n : U'.Normal := by rw [hU'eq]; infer_instance
  have hU'p : IsPGroup 2 U' :=
    isPGroup_of_forall_mem (M := Q) hQ.1 fun x hx => (mem_subgroupOf.1 hx).1
  have hCU : IsPGroup 2 (centralizer (U' : Set C)) := by
    refine isPGroup_of_forall_mem hP fun x hx => mem_inf.2 ⟨x.2, ?_⟩
    rw [mem_centralizer_iff]
    intro u hu
    have hu' : (⟨u, hu.2⟩ : C) ∈ U' := mem_subgroupOf.2 hu
    exact congrArg Subtype.val ((mem_centralizer_iff.1 hx) _ hu')
  have hO1 : U' ≤ CFSG.pCore 2 C := le_sSup ⟨hU'n, hU'p⟩
  have hO2 : centralizer (U' : Set C) ≤ CFSG.pCore 2 C :=
    le_sSup ⟨Subgroup.normal_centralizer, hCU⟩
  have hchar : CFSG.IsCharacteristicP 2 C := (centralizer_le hO1).trans hO2
  refine ⟨hP, hchar, fun K hK => ?_, ?_⟩
  · have hKO : K ≤ CFSG.pCore 2 C := by
      rcases component_normal_subgroup hK CFSG.pCore_normal with hle | hbot
      · exact hle
      · exact (commutator_eq_bot_iff_le_centralizer.1 hbot).trans hchar
    have : Group.IsNilpotent (CFSG.pCore 2 C) := CFSG.pCore_isPGroup.isNilpotent
    exact not_le_of_isComponent_of_isSolvable hK inferInstance hKO
  · let f : C →* H ⧸ Q := (QuotientGroup.mk' Q).comp C.subtype
    have hker : f.ker = U' := by
      rw [hU'eq]
      ext x
      simp [f, mem_subgroupOf]
    have hcard : Nat.card C = Nat.card f.range * Nat.card U := by
      rw [card_eq_card_quotient_mul_card_subgroup f.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hker, hU'def,
        Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : U ≤ C)).toEquiv]
    have hpos1 : Nat.card f.range ≠ 0 := Nat.card_pos.ne'
    have hpos2 : Nat.card U ≠ 0 := Nat.card_pos.ne'
    rw [hcard, Nat.ordProj_mul 2 hpos1 hpos2, mul_comm]
    refine Nat.mul_le_mul (Nat.ordProj_le 2 hpos2) (Nat.le_of_dvd ?_ ?_)
    · exact Nat.ordProj_pos _ _
    · exact Nat.ordProj_dvd_ordProj_of_dvd Nat.card_pos.ne' (card_subgroup_dvd_card f.range) 2

end CFSG.LocalAnalysis.ComponentInitial
