module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeFullAffine

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix
open scoped commutatorElement

local notation "𝕍" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}
local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)
local notation "𝔼" => Fin 3 → ZMod 2

@[expose] def symThreeAltUnit : 𝕍 :=
  symThreePolarSym ![1, 0, 0] ![0, 1, 0]

theorem diag_symThreeAltUnit : symThreeDiag (symThreeAltUnit : M₃) = 0 :=
  symThreeDiag_polarSym _ _

theorem symThreeAltUnit_ne_zero : symThreeAltUnit ≠ 0 := by
  decide

theorem smul_polarSym_zero_left (B : 𝕍) (c : ZMod 2) :
    c • symThreePolarSym (0 : 𝔼) (symThreeDiag (B : M₃)) = 0 := by
  rw [symThreePolarSym_zero_left, smul_zero]

theorem eq_zero_of_smul_symThreeAltUnit {ε : ZMod 2} (h : ε • symThreeAltUnit = 0) : ε = 0 := by
  have key : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases key ε with rfl | rfl
  · rfl
  · rw [one_smul] at h
    exact absurd h symThreeAltUnit_ne_zero

namespace SymThreeFullCoset

open SymThreeFullAffine

variable {M : Type*} [Group M] {R : Subgroup M} (θ : R ≃* Multiplicative (𝕍 × ZMod 2))

@[expose] def th (x : 𝕍 × ZMod 2) : M :=
  (θ.symm (Multiplicative.ofAdd x) : M)

theorem th_mem (x : 𝕍 × ZMod 2) : th θ x ∈ R :=
  (θ.symm _).2

theorem th_add (x y : 𝕍 × ZMod 2) : th θ (x + y) = th θ x * th θ y := by
  rw [th, ofAdd_add, map_mul]
  rfl

theorem th_zero : th θ (0 : 𝕍 × ZMod 2) = 1 := by
  rw [th, ofAdd_zero, map_one]
  rfl

theorem th_injective : Function.Injective (th θ) := fun _ _ h =>
  Multiplicative.ofAdd.injective (θ.symm.injective (Subtype.ext h))

theorem exists_th {r : M} (hr : r ∈ R) : ∃ x, th θ x = r :=
  ⟨Multiplicative.toAdd (θ ⟨r, hr⟩), by
    rw [th, ofAdd_toAdd, MulEquiv.symm_apply_apply]⟩

include θ in
theorem mul_comm_of_mem {a b : M} (ha : a ∈ R) (hb : b ∈ R) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := exists_th θ ha
  obtain ⟨y, rfl⟩ := exists_th θ hb
  rw [← th_add, ← th_add, add_comm]

variable [R.Normal]

theorem conj_mem (m : M) (x : 𝕍 × ZMod 2) : m⁻¹ * th θ x * m ∈ R := by
  have h := (inferInstance : R.Normal).conj_mem _ (th_mem θ x) m⁻¹
  rwa [inv_inv] at h

@[expose] noncomputable def cAct (m : M) (x : 𝕍 × ZMod 2) : 𝕍 × ZMod 2 :=
  Multiplicative.toAdd (θ ⟨m⁻¹ * th θ x * m, conj_mem θ m x⟩)

theorem th_cAct (m : M) (x : 𝕍 × ZMod 2) : th θ (cAct θ m x) = m⁻¹ * th θ x * m := by
  rw [th, cAct, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem cAct_add (m : M) (x y : 𝕍 × ZMod 2) : cAct θ m (x + y) = cAct θ m x + cAct θ m y := by
  apply th_injective θ
  rw [th_cAct, th_add, th_add, th_cAct, th_cAct]
  group

theorem cAct_mul (m m' : M) (x : 𝕍 × ZMod 2) : cAct θ (m * m') x = cAct θ m' (cAct θ m x) := by
  apply th_injective θ
  rw [th_cAct, th_cAct, th_cAct]
  group

theorem cAct_one (x : 𝕍 × ZMod 2) : cAct θ 1 x = x := by
  apply th_injective θ
  rw [th_cAct]
  group

theorem cAct_of_mem {m : M} (hm : m ∈ R) (x : 𝕍 × ZMod 2) : cAct θ m x = x := by
  apply th_injective θ
  rw [th_cAct, mul_assoc, mul_comm_of_mem θ (th_mem θ x) hm, inv_mul_cancel_left]

theorem cAct_inv_cAct (m : M) (x : 𝕍 × ZMod 2) : cAct θ m⁻¹ (cAct θ m x) = x := by
  rw [← cAct_mul, mul_inv_cancel, cAct_one]

structure Hyp : Prop where
  omega : ∀ (m : M) (B : 𝕍), (cAct θ m (B, 1)).2 = 1
  faith : ∀ m : M, (∀ B : 𝕍, cAct θ m (B, 1) = (B, 1)) → m ∈ R
  trans : ∀ B B' : 𝕍, ∃ m : M, cAct θ m (B, 1) = (B', 1)
  stab : ∀ m : M, cAct θ m (0, 1) = (0, 1) →
    ∃ L : GL (Fin 3) (ZMod 2), ∀ B : 𝕍, cAct θ m (B, 1) = (symThreeCongr L B, 1)
  stab' : ∀ L : GL (Fin 3) (ZMod 2),
    ∃ m : M, ∀ B : 𝕍, cAct θ m (B, 1) = (symThreeCongr L B, 1)

variable {θ}

theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem cAct_snd (hH : Hyp θ) (m : M) (x : 𝕍 × ZMod 2) : (cAct θ m x).2 = x.2 := by
  obtain ⟨B, ε⟩ := x
  rcases zmod_two_cases ε with rfl | rfl
  · have h : ((B, 0) : 𝕍 × ZMod 2) = (B, 1) + (0, 1) :=
      Prod.ext (add_zero B).symm (show (0 : ZMod 2) = 1 + 1 from rfl)
    rw [h, cAct_add, Prod.snd_add, hH.omega, hH.omega]
    rfl
  · exact hH.omega m B

theorem cAct_zero_eq (hH : Hyp θ) (m : M) (B : 𝕍) :
    cAct θ m (B, 0) = ((cAct θ m (B, 0)).1, 0) :=
  Prod.ext rfl (cAct_snd hH m _)

theorem cAct_eq (hH : Hyp θ) (m : M) (B : 𝕍) (ε : ZMod 2) :
    cAct θ m (B, ε) = ((cAct θ m (B, 0)).1 + ε • (cAct θ m (0, 1)).1, ε) := by
  rcases zmod_two_cases ε with rfl | rfl
  · rw [zero_smul, add_zero]
    exact cAct_zero_eq hH m B
  · have h : ((B, 1) : 𝕍 × ZMod 2) = (B, 0) + (0, 1) :=
      Prod.ext (add_zero B).symm (zero_add 1).symm
    rw [h, cAct_add, one_smul]
    exact Prod.ext rfl (by rw [Prod.snd_add, cAct_snd hH, cAct_snd hH]; rfl)

@[expose] noncomputable def linAdd (m : M) : 𝕍 →+ 𝕍 :=
  AddMonoidHom.mk' (fun B => (cAct θ m (B, 0)).1) fun B C => by
    have h : ((B + C, 0) : 𝕍 × ZMod 2) = (B, 0) + (C, 0) := Prod.ext rfl (add_zero 0).symm
    rw [h, cAct_add, Prod.fst_add]

theorem linAdd_apply (m : M) (B : 𝕍) : linAdd (θ := θ) m B = (cAct θ m (B, 0)).1 :=
  rfl

theorem linAdd_inv_linAdd (hH : Hyp θ) (m : M) (B : 𝕍) :
    linAdd (θ := θ) m⁻¹ (linAdd (θ := θ) m B) = B := by
  rw [linAdd_apply, linAdd_apply, ← cAct_zero_eq hH, cAct_inv_cAct]

@[expose] noncomputable def linEquiv (hH : Hyp θ) (m : M) : 𝕍 ≃ₗ[ZMod 2] 𝕍 where
  toFun := linAdd m
  invFun := linAdd m⁻¹
  map_add' := map_add _
  map_smul' c B := by
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul, RingHom.id_apply, zero_smul, map_zero]
    · rw [one_smul, RingHom.id_apply, one_smul]
  left_inv := linAdd_inv_linAdd hH m
  right_inv B := by
    have h := linAdd_inv_linAdd hH m⁻¹ B
    rwa [inv_inv] at h

theorem linEquiv_apply (hH : Hyp θ) (m : M) (B : 𝕍) :
    linEquiv hH m B = (cAct θ m (B, 0)).1 :=
  rfl

@[expose] noncomputable def affOf (hH : Hyp θ) (m : M) : 𝕍 ≃ᵃ[ZMod 2] 𝕍 :=
  tr (cAct θ m (0, 1)).1 * toAff (linEquiv hH m)

theorem affOf_apply (hH : Hyp θ) (m : M) (B : 𝕍) : affOf hH m B = (cAct θ m (B, 1)).1 := by
  change (cAct θ m (0, 1)).1 + (cAct θ m (B, 0)).1 = _
  rw [cAct_eq hH m B 1, one_smul, add_comm]

theorem cAct_one_eq (hH : Hyp θ) (m : M) (B : 𝕍) : cAct θ m (B, 1) = (affOf hH m B, 1) :=
  Prod.ext (affOf_apply hH m B).symm (hH.omega m B)

theorem affOf_mul (hH : Hyp θ) (m m' : M) : affOf hH (m * m') = affOf hH m' * affOf hH m :=
  AffineEquiv.ext fun B => by
    rw [AffineEquiv.coe_mul, Function.comp_apply, affOf_apply, affOf_apply, affOf_apply,
      cAct_mul, cAct_one_eq hH m B]

theorem affOf_one (hH : Hyp θ) : affOf hH (1 : M) = 1 :=
  AffineEquiv.ext fun B => by
    rw [affOf_apply, cAct_one]
    rfl

theorem affOf_inv (hH : Hyp θ) (m : M) : affOf hH m⁻¹ = (affOf hH m)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← affOf_mul, mul_inv_cancel, affOf_one]

@[expose] noncomputable def phi (hH : Hyp θ) : M →* (𝕍 ≃ᵃ[ZMod 2] 𝕍) where
  toFun m := affOf hH m⁻¹
  map_one' := by rw [inv_one, affOf_one]
  map_mul' m m' := by rw [_root_.mul_inv_rev, affOf_mul]

theorem phi_apply (hH : Hyp θ) (m : M) : phi hH m = affOf hH m⁻¹ :=
  rfl

theorem affOf_eq_phi_inv (hH : Hyp θ) (m : M) : affOf hH m = phi hH m⁻¹ := by
  rw [phi_apply, inv_inv]

theorem mem_ker_phi (hH : Hyp θ) {m : M} : m ∈ (phi hH).ker ↔ m ∈ R := by
  rw [MonoidHom.mem_ker, phi_apply]
  constructor
  · intro h
    have h1 : m⁻¹ ∈ R := hH.faith _ fun B => by
      rw [cAct_one_eq hH, h]
      rfl
    simpa using h1
  · intro h
    refine AffineEquiv.ext fun B => ?_
    rw [affOf_apply, cAct_of_mem θ (R.inv_mem h)]
    rfl

theorem mem_R_of_centralizes (hH : Hyp θ) {m : M} (hm : ∀ r ∈ R, m * r = r * m) : m ∈ R :=
  hH.faith m fun B => by
    apply th_injective θ
    rw [th_cAct, mul_assoc, ← hm _ (th_mem θ _), inv_mul_cancel_left]

theorem range_hyp (hH : Hyp θ) :
    (∀ x y : 𝕍, ∃ k ∈ (phi hH).range, k x = y) ∧
      ∀ g : 𝕍 ≃ₗ[ZMod 2] 𝕍, g.toAffineEquiv ∈ (phi hH).range ↔ g ∈ symThreeCongrGroup := by
  refine ⟨fun x y => ?_, fun g => ⟨?_, ?_⟩⟩
  · obtain ⟨m, hm⟩ := hH.trans x y
    refine ⟨affOf hH m, ⟨m⁻¹, by rw [phi_apply, inv_inv]⟩, ?_⟩
    rw [affOf_apply, hm]
  · rintro ⟨m, hm⟩
    rw [phi_apply] at hm
    have h0 : cAct θ m⁻¹ (0, 1) = (0, 1) := by
      rw [cAct_one_eq hH, hm]
      exact Prod.ext (map_zero g) rfl
    obtain ⟨L, hL⟩ := hH.stab _ h0
    refine ⟨L, LinearEquiv.ext fun B => ?_⟩
    have h1 := congrArg Prod.fst (hL B)
    rw [cAct_one_eq hH, hm] at h1
    exact h1.symm
  · rintro ⟨L, rfl⟩
    obtain ⟨m, hm⟩ := hH.stab' L
    refine ⟨m⁻¹, ?_⟩
    rw [phi_apply, inv_inv]
    refine AffineEquiv.ext fun B => ?_
    rw [affOf_apply, hm]
    rfl

structure Core (hH : Hyp θ) (κ : ZMod 2) : Prop where
  pmem : ∀ A : 𝕍, symThreeTwoCoreMap κ A ∈ (phi hH).range
  pcore : CFSG.Assembly.pCoreOf 2 (phi hH).range = symThreeTwoCoreGroup κ
  abelP : CFSG.Assembly.IsElemAbelian 2 (symThreeTwoCoreGroup κ)
  cardP : Nat.card (symThreeTwoCoreGroup κ) = 64
  regular : ∀ x y : 𝕍, ∃! p, p ∈ symThreeTwoCoreGroup κ ∧ p x = y
  normal : ∀ k ∈ (phi hH).range, ∀ p ∈ symThreeTwoCoreGroup κ,
    k * p * k⁻¹ ∈ symThreeTwoCoreGroup κ
  prod : ∀ k ∈ (phi hH).range, ∃ p ∈ symThreeTwoCoreGroup κ, ∃ g ∈ symThreeCongrGroup,
    k = p * g.toAffineEquiv
  lin : ∀ k ∈ (phi hH).range, ∀ B : 𝕍, symThreeDiag (B : M₃) = 0 →
    symThreeDiag (k.linear B : M₃) = 0
  ker : ∀ k ∈ (phi hH).range,
    (∀ B : 𝕍, symThreeDiag (k B : M₃) = symThreeDiag (B : M₃)) ↔ k ∈ symThreeAltTranslations
  abelU : CFSG.Assembly.IsElemAbelian 2 symThreeAltTranslations
  cardU : Nat.card symThreeAltTranslations = 8
  normalU : ∀ k ∈ (phi hH).range, ∀ u ∈ symThreeAltTranslations,
    k * u * k⁻¹ ∈ symThreeAltTranslations
  UleP : symThreeAltTranslations ≤ symThreeTwoCoreGroup κ

theorem exists_core (hH : Hyp θ) : ∃ κ : ZMod 2, Core hH κ := by
  obtain ⟨κ, h1, h2, -, h4, h5, h6, h7, -, h9, h10, -, -, h13, h14, h15, -, h17, h18, -, -⟩ :=
    binary_symmetric_three_full_affine_orbit_two_core_and_actions (phi hH).range
      (range_hyp hH).1 (range_hyp hH).2
  exact ⟨κ, ⟨h1, h2, h4, h5, h6, h7, h9, h10, h13, h14, h15, h17, h18⟩⟩

omit [R.Normal] in
theorem card_R_of_equiv (e : R ≃* Multiplicative (𝕍 × ZMod 2)) : Nat.card R = 128 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_prod, card_symThree,
    Nat.card_zmod]

theorem card_comap_eq {G G' : Type*} [Group G] [Group G'] (f : G →* G') {H : Subgroup G'}
    (hH : H ≤ f.range) : Nat.card (H.comap f) = Nat.card f.ker * Nat.card H := by
  let g : H.comap f →* H := (f.comp (H.comap f).subtype).codRestrict H fun x => x.2
  have hg : Function.Surjective g := fun h => by
    obtain ⟨x, hx⟩ := hH h.2
    exact ⟨⟨x, by rw [Subgroup.mem_comap, hx]; exact h.2⟩, Subtype.ext hx⟩
  have hker : Nat.card g.ker = Nat.card f.ker := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, by
          have h := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
          exact MonoidHom.mem_ker.mpr h⟩
        invFun := fun y => ⟨⟨y.1, by
          rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp y.2]; exact H.one_mem⟩, by
          rw [MonoidHom.mem_ker]
          exact Subtype.ext (MonoidHom.mem_ker.mp y.2)⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv, hker, mul_comm]

@[expose] noncomputable def dSub (hH : Hyp θ) (κ : ZMod 2) : Subgroup M :=
  (symThreeTwoCoreGroup κ).comap (phi hH)

@[expose] noncomputable def fSub (hH : Hyp θ) : Subgroup M :=
  symThreeAltTranslations.comap (phi hH)

@[expose] noncomputable def lab (hH : Hyp θ) (m : M) : 𝕍 :=
  affOf hH m 0

omit [R.Normal] in
theorem th_inv (v : 𝕍 × ZMod 2) : (th θ v)⁻¹ = th θ v := by
  have hv : v + v = 0 := Prod.ext (symThree_add_self v.1) (symThree_zmod_add_self v.2)
  rw [inv_eq_iff_mul_eq_one, ← th_add, hv, th_zero]

@[expose] def aSub (θ : R ≃* Multiplicative (𝕍 × ZMod 2)) : Subgroup M where
  carrier := {x | ∃ B : 𝕍, x = th θ (B, 0)}
  mul_mem' := by
    rintro _ _ ⟨B, rfl⟩ ⟨C, rfl⟩
    exact ⟨B + C, by rw [← th_add]; rfl⟩
  one_mem' := ⟨0, (th_zero θ).symm⟩
  inv_mem' := by
    rintro _ ⟨B, rfl⟩
    exact ⟨B, th_inv _⟩

@[expose] def iSub (θ : R ≃* Multiplicative (𝕍 × ZMod 2)) : Subgroup M where
  carrier := {x | ∃ B : 𝕍, symThreeDiag (B : M₃) = 0 ∧ x = th θ (B, 0)}
  mul_mem' := by
    rintro _ _ ⟨B, hB, rfl⟩ ⟨C, hC, rfl⟩
    refine ⟨B + C, ?_, by rw [← th_add]; rfl⟩
    rw [AddSubgroup.coe_add, symThreeDiag_add, hB, hC, add_zero]
  one_mem' := ⟨0, rfl, (th_zero θ).symm⟩
  inv_mem' := by
    rintro _ ⟨B, hB, rfl⟩
    exact ⟨B, hB, th_inv _⟩

section Core

variable {hH : Hyp θ} {κ : ZMod 2}

theorem phi_eq_inv (m : M) : phi hH m = (affOf hH m)⁻¹ := by
  rw [phi_apply, affOf_inv]

theorem affOf_mem_range (m : M) : affOf hH m ∈ (phi hH).range :=
  ⟨m⁻¹, by rw [phi_apply, inv_inv]⟩

theorem mem_dSub {m : M} : m ∈ dSub hH κ ↔ affOf hH m ∈ symThreeTwoCoreGroup κ := by
  rw [dSub, Subgroup.mem_comap, phi_eq_inv]
  exact ⟨fun h => by simpa using (symThreeTwoCoreGroup κ).inv_mem h,
    (symThreeTwoCoreGroup κ).inv_mem⟩

theorem mem_fSub {m : M} : m ∈ fSub hH ↔ affOf hH m ∈ symThreeAltTranslations := by
  rw [fSub, Subgroup.mem_comap, phi_eq_inv]
  exact ⟨fun h => by simpa using symThreeAltTranslations.inv_mem h,
    symThreeAltTranslations.inv_mem⟩

theorem ker_phi : (phi hH).ker = R := by
  ext m
  exact mem_ker_phi hH

theorem affOf_eq_one_iff {m : M} : affOf hH m = 1 ↔ m ∈ R := by
  rw [affOf_eq_phi_inv, ← MonoidHom.mem_ker, mem_ker_phi]
  exact ⟨fun h => by simpa using R.inv_mem h, R.inv_mem⟩

theorem twoCoreMap_apply_zero (A : 𝕍) : symThreeTwoCoreMap κ A 0 = A := by
  rw [coe_symThreeTwoCoreMap, symThreeAffine_zero_right]

theorem affOf_eq {m : M} (hm : m ∈ dSub hH κ) : affOf hH m = symThreeTwoCoreMap κ (lab hH m) := by
  obtain ⟨A, hA⟩ := mem_dSub.mp hm
  rw [← hA, lab, ← hA, twoCoreMap_apply_zero]

theorem R_le_fSub : R ≤ fSub hH := fun r hr => mem_fSub.mpr (by
  rw [affOf_eq_one_iff.mpr hr]
  exact symThreeAltTranslations.one_mem)

variable (hc : Core hH κ)
include hc

omit hc in
theorem lab_mul_of_mem {m m' : M} (hm' : m' ∈ dSub hH κ) :
    lab hH (m * m') = symThreeTwoCoreMap κ (lab hH m') (lab hH m) := by
  rw [lab, affOf_mul, AffineEquiv.coe_mul, Function.comp_apply, ← lab, affOf_eq hm']

omit hc in
theorem cAct_of_mem_dSub {m : M} (hm : m ∈ dSub hH κ) (B : 𝕍) (ε : ZMod 2) :
    cAct θ m (B, ε) = (B + κ • symThreePolarSym (symThreeDiag (lab hH m : M₃))
      (symThreeDiag (B : M₃)) + ε • lab hH m, ε) := by
  have h2 : (cAct θ m (0, 1)).1 = lab hH m := by rw [lab, affOf_apply]
  have h1 : B + lab hH m + κ • symThreePolarSym (symThreeDiag (lab hH m : M₃))
      (symThreeDiag (B : M₃)) = (cAct θ m (B, 0)).1 + lab hH m := by
    have h := affOf_apply hH m B
    rw [affOf_eq hm, symThreeTwoCoreMap_apply, cAct_eq hH m B 1, one_smul, h2] at h
    exact h
  rw [cAct_eq hH m B ε, h2]
  refine Prod.ext ?_ rfl
  change (cAct θ m (B, 0)).1 + ε • lab hH m = _
  congr 1
  calc (cAct θ m (B, 0)).1 = (cAct θ m (B, 0)).1 + lab hH m + lab hH m := by
        rw [add_assoc, symThree_add_self, add_zero]
    _ = B + lab hH m + κ • symThreePolarSym (symThreeDiag (lab hH m : M₃))
          (symThreeDiag (B : M₃)) + lab hH m := by rw [← h1]
    _ = B + κ • symThreePolarSym (symThreeDiag (lab hH m : M₃)) (symThreeDiag (B : M₃)) +
          (lab hH m + lab hH m) := by abel
    _ = B + κ • symThreePolarSym (symThreeDiag (lab hH m : M₃)) (symThreeDiag (B : M₃)) := by
        rw [symThree_add_self, add_zero]

theorem regular_eq {p p' : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hp : p ∈ symThreeTwoCoreGroup κ)
    (hp' : p' ∈ symThreeTwoCoreGroup κ) (h : p 0 = p' 0) : p = p' :=
  (hc.regular 0 (p 0)).unique ⟨hp, rfl⟩ ⟨hp', h.symm⟩

theorem lab_eq_iff {m m' : M} (hm : m ∈ dSub hH κ) (hm' : m' ∈ dSub hH κ) :
    lab hH m = lab hH m' ↔ m⁻¹ * m' ∈ R := by
  rw [← affOf_eq_one_iff, affOf_mul, affOf_inv]
  constructor
  · intro h
    rw [regular_eq hc (mem_dSub.mp hm') (mem_dSub.mp hm) h.symm, mul_inv_cancel]
  · intro h
    have h1 : affOf hH m' = affOf hH m := by
      rw [← mul_inv_eq_one]
      exact h
    rw [lab, lab, h1]

theorem exists_lab (B : 𝕍) : ∃ m ∈ dSub hH κ, lab hH m = B := by
  obtain ⟨m, hm⟩ := hc.pmem B
  refine ⟨m⁻¹, mem_dSub.mpr ?_, ?_⟩
  · rw [affOf_eq_phi_inv, inv_inv, hm]
    exact ⟨B, rfl⟩
  · rw [lab, affOf_eq_phi_inv, inv_inv, hm, twoCoreMap_apply_zero]

theorem fSub_le_dSub : fSub hH ≤ dSub hH κ := fun _ hm =>
  mem_dSub.mpr (hc.UleP (mem_fSub.mp hm))

theorem R_le_dSub : R ≤ dSub hH κ :=
  R_le_fSub.trans (fSub_le_dSub hc)

theorem dSub_normal : (dSub hH κ).Normal :=
  ⟨fun d hd m => by
    rw [dSub, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hc.normal _ ⟨m, rfl⟩ _ hd⟩

theorem fSub_normal : (fSub hH).Normal :=
  ⟨fun d hd m => by
    rw [fSub, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hc.normalU _ ⟨m, rfl⟩ _ hd⟩

theorem card_dSub : Nat.card (dSub hH κ) = 8192 := by
  rw [dSub, card_comap_eq (phi hH) fun p hp => ?_, ker_phi, card_R_of_equiv θ, hc.cardP]
  obtain ⟨A, rfl⟩ := hp
  exact hc.pmem A

theorem card_fSub : Nat.card (fSub hH) = 1024 := by
  rw [fSub, card_comap_eq (phi hH) fun u hu => ?_, ker_phi, card_R_of_equiv θ, hc.cardU]
  obtain ⟨A, rfl⟩ := hc.UleP hu
  exact hc.pmem A

theorem mem_fSub_iff {m : M} :
    m ∈ fSub hH ↔ m ∈ dSub hH κ ∧ symThreeDiag (lab hH m : M₃) = 0 := by
  constructor
  · intro hm
    have hU := mem_fSub.mp hm
    refine ⟨fSub_le_dSub hc hm, ?_⟩
    obtain ⟨i, hi, hiU⟩ := hU
    rw [lab, hiU, tr_apply, add_zero]
    exact hi
  · rintro ⟨hm, h0⟩
    refine mem_fSub.mpr ⟨lab hH m, h0, AffineEquiv.ext fun B => ?_⟩
    rw [affOf_eq hm, coe_symThreeTwoCoreMap, symThreeAffine_of_diag_eq_zero κ h0, tr_apply,
      add_comm]

omit hc in
theorem lab_one : lab hH (1 : M) = 0 := by
  rw [lab, affOf_one]
  rfl

omit hc in
theorem cAct_z (m : M) : cAct θ m (0, 1) = (lab hH m, 1) := by
  rw [cAct_one_eq hH]
  rfl

omit hc in
theorem mem_centralizer_z_iff {m : M} :
    m ∈ Subgroup.centralizer {th θ (0, 1)} ↔ lab hH m = 0 := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : cAct θ m (0, 1) = (0, 1) := by
      apply th_injective θ
      rw [th_cAct, mul_assoc, ← h, inv_mul_cancel_left]
    rw [cAct_z] at h1
    exact congrArg Prod.fst h1
  · intro h
    have h1 := th_cAct θ m (0, 1)
    rw [cAct_z (hH := hH) m, h] at h1
    calc m * th θ (0, 1) = m * (m⁻¹ * th θ (0, 1) * m) := by rw [← h1]
      _ = th θ (0, 1) * m := by group

theorem dSub_inf_centralizer : dSub hH κ ⊓ Subgroup.centralizer {th θ (0, 1)} = R := by
  ext m
  rw [Subgroup.mem_inf, mem_centralizer_z_iff (hH := hH)]
  constructor
  · rintro ⟨hm, h0⟩
    have h := (lab_eq_iff hc hm (dSub hH κ).one_mem).mp (by rw [h0, lab_one])
    simpa using h
  · intro hm
    refine ⟨R_le_dSub hc hm, ?_⟩
    rw [lab, affOf_eq_one_iff.mpr hm]
    rfl

theorem exists_dSub_affOf (p : 𝕍 ≃ᵃ[ZMod 2] 𝕍) (hp : p ∈ symThreeTwoCoreGroup κ) :
    ∃ d ∈ dSub hH κ, affOf hH d = p := by
  obtain ⟨d, hd, hd0⟩ := exists_lab hc (p 0)
  exact ⟨d, hd, regular_eq hc (mem_dSub.mp hd) hp hd0⟩

theorem exists_dSub_mul_centralizer (m : M) :
    ∃ d ∈ dSub hH κ, ∃ c ∈ Subgroup.centralizer {th θ (0, 1)}, m = d * c := by
  obtain ⟨p, hp, g, -, hpg⟩ := hc.prod _ (affOf_mem_range m)
  obtain ⟨d, hd, hdp⟩ := exists_dSub_affOf hc p hp
  have hc0 : lab hH (m * d⁻¹) = 0 := by
    rw [lab, affOf_mul, affOf_inv, hdp, hpg, inv_mul_cancel_left]
    exact map_zero g
  refine ⟨(m * d⁻¹) * d * (m * d⁻¹)⁻¹, (dSub_normal hc).conj_mem d hd _, m * d⁻¹,
    mem_centralizer_z_iff.mpr hc0, ?_⟩
  group

omit hc in
theorem th_comm_dSub {d : M} (hd : d ∈ dSub hH κ) (B : 𝕍) (ε : ZMod 2) :
    (th θ (B, ε))⁻¹ * (d⁻¹ * th θ (B, ε) * d) = th θ
      (κ • symThreePolarSym (symThreeDiag (lab hH d : M₃)) (symThreeDiag (B : M₃)) +
        ε • lab hH d, 0) := by
  rw [th_inv, ← th_cAct, cAct_of_mem_dSub hd, ← th_add]
  congr 1
  refine Prod.ext ?_ ?_
  · change B + (B + _ + _) = _
    rw [← add_assoc, ← add_assoc, symThree_add_self, zero_add]
  · change ε + ε = 0
    exact symThree_zmod_add_self _

omit hc in
theorem th_mul_comm_of_mem_dSub {d : M} (hd : d ∈ dSub hH κ) {B : 𝕍} {ε : ZMod 2}
    (h : κ • symThreePolarSym (symThreeDiag (lab hH d : M₃)) (symThreeDiag (B : M₃)) +
      ε • lab hH d = 0) : d * th θ (B, ε) = th θ (B, ε) * d := by
  have h1 := th_cAct θ d (B, ε)
  rw [cAct_of_mem_dSub hd, add_assoc, h, add_zero] at h1
  calc d * th θ (B, ε) = d * (d⁻¹ * th θ (B, ε) * d) := by rw [← h1]
    _ = th θ (B, ε) * d := by group

theorem cAct_of_mem_fSub {f : M} (hf : f ∈ fSub hH) (B : 𝕍) (ε : ZMod 2) :
    cAct θ f (B, ε) = (B + ε • lab hH f, ε) := by
  obtain ⟨hfD, hf0⟩ := (mem_fSub_iff hc).mp hf
  rw [cAct_of_mem_dSub hfD, hf0, smul_polarSym_zero_left, add_zero]

theorem exists_fSub_symThreeAltUnit : ∃ f ∈ fSub hH, lab hH f = symThreeAltUnit := by
  obtain ⟨d, hd, hd0⟩ := exists_lab hc symThreeAltUnit
  exact ⟨d, (mem_fSub_iff hc).mpr ⟨hd, by rw [hd0]; exact diag_symThreeAltUnit⟩, hd0⟩

theorem mem_center_fSub_iff (x : M) :
    (∃ y : fSub hH, y ∈ Subgroup.center (fSub hH) ∧ (y : M) = x) ↔
      ∃ B : 𝕍, x = th θ (B, 0) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hR : (y : M) ∈ R := mem_R_of_centralizes hH fun r hr => by
      have h := Subgroup.mem_center_iff.mp hy ⟨r, R_le_fSub hr⟩
      exact (congrArg Subtype.val h).symm
    obtain ⟨⟨B, ε⟩, hBε⟩ := exists_th θ hR
    obtain ⟨f, hf, hf0⟩ := exists_fSub_symThreeAltUnit hc
    have h1 := Subgroup.mem_center_iff.mp hy ⟨f, hf⟩
    have h2 : cAct θ f (B, ε) = (B, ε) := by
      apply th_injective θ
      rw [th_cAct, hBε]
      have h3 := congrArg Subtype.val h1
      change f * (y : M) = (y : M) * f at h3
      rw [mul_assoc, ← h3, inv_mul_cancel_left]
    rw [cAct_of_mem_fSub hc hf, hf0] at h2
    have h4 : ε • symThreeAltUnit = 0 := by
      have h5 := congrArg Prod.fst h2
      change B + ε • symThreeAltUnit = B at h5
      exact add_eq_left.mp h5
    rw [eq_zero_of_smul_symThreeAltUnit h4] at hBε
    exact ⟨B, hBε.symm⟩
  · rintro ⟨B, rfl⟩
    refine ⟨⟨th θ (B, 0), R_le_fSub (th_mem θ _)⟩, Subgroup.mem_center_iff.mpr fun f => ?_, rfl⟩
    apply Subtype.ext
    change (f : M) * th θ (B, 0) = th θ (B, 0) * f
    have hfD := fSub_le_dSub hc f.2
    refine th_mul_comm_of_mem_dSub hfD ?_
    rw [((mem_fSub_iff hc).mp f.2).2, smul_polarSym_zero_left, zero_smul, add_zero]

omit hc in
theorem commutatorElement_eq (x d : M) : ⁅x, d⁆ = x⁻¹⁻¹ * ((d⁻¹)⁻¹ * x⁻¹ * d⁻¹) := by
  rw [commutatorElement_def]
  group

omit hc in
theorem comm_th_dSub {d : M} (hd : d ∈ dSub hH κ) (B : 𝕍) (ε : ZMod 2) :
    ⁅th θ (B, ε), d⁆ = th θ (κ • symThreePolarSym (symThreeDiag (lab hH d⁻¹ : M₃))
      (symThreeDiag (B : M₃)) + ε • lab hH d⁻¹, 0) := by
  rw [commutatorElement_eq, th_inv, th_comm_dSub ((dSub hH κ).inv_mem hd)]

theorem commutator_R_dSub : ⁅R, dSub hH κ⁆ = aSub θ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro r hr d hd
    obtain ⟨⟨B, ε⟩, rfl⟩ := exists_th θ hr
    rw [comm_th_dSub hd]
    exact ⟨_, rfl⟩
  · rintro _ ⟨B, rfl⟩
    obtain ⟨d, hd, hdB⟩ := exists_lab hc B
    have h := comm_th_dSub (θ := θ) ((dSub hH κ).inv_mem hd) 0 1
    rw [inv_inv, hdB, show symThreeDiag ((0 : 𝕍) : M₃) = 0 from rfl,
      symThreePolarSym_zero_right, smul_zero, zero_add, one_smul] at h
    rw [← h]
    exact Subgroup.commutator_mem_commutator (th_mem θ _) ((dSub hH κ).inv_mem hd)

omit [R.Normal] hc in
theorem polarSym_forall_eq_zero_iff : ∀ b : 𝔼, (∀ a : 𝔼, symThreePolarSym a b = 0) ↔ b = 0 := by
  decide

theorem mem_center_dSub_iff (x : M) :
    (∃ y : dSub hH κ, y ∈ Subgroup.center (dSub hH κ) ∧ (y : M) = x) ↔
      ∃ B : 𝕍, (∀ a : 𝔼, κ • symThreePolarSym a (symThreeDiag (B : M₃)) = 0) ∧
        x = th θ (B, 0) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hR : (y : M) ∈ R := mem_R_of_centralizes hH fun r hr => by
      have h := Subgroup.mem_center_iff.mp hy ⟨r, R_le_dSub hc hr⟩
      exact (congrArg Subtype.val h).symm
    obtain ⟨⟨B, ε⟩, hBε⟩ := exists_th θ hR
    have hfix : ∀ d ∈ dSub hH κ, cAct θ d (B, ε) = (B, ε) := fun d hd => by
      apply th_injective θ
      rw [th_cAct, hBε]
      have h3 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨d, hd⟩)
      change d * (y : M) = (y : M) * d at h3
      rw [mul_assoc, ← h3, inv_mul_cancel_left]
    have hcoord : ∀ d ∈ dSub hH κ, κ • symThreePolarSym (symThreeDiag (lab hH d : M₃))
        (symThreeDiag (B : M₃)) + ε • lab hH d = 0 := fun d hd => by
      have h := congrArg Prod.fst (hfix d hd)
      rw [cAct_of_mem_dSub hd] at h
      change B + _ + _ = B at h
      rw [add_assoc] at h
      exact add_eq_left.mp h
    obtain ⟨f, hf, hf0⟩ := exists_fSub_symThreeAltUnit hc
    have hε : ε = 0 := by
      have h := hcoord f (fSub_le_dSub hc hf)
      rw [hf0, diag_symThreeAltUnit, smul_polarSym_zero_left, zero_add] at h
      exact eq_zero_of_smul_symThreeAltUnit h
    subst hε
    refine ⟨B, fun a => ?_, hBε.symm⟩
    obtain ⟨d, hd, hdB⟩ := exists_lab hc (symThreeDiagSection a)
    have h := hcoord d hd
    rw [zero_smul, add_zero, hdB, symThreeDiag_diagSection] at h
    exact h
  · rintro ⟨B, hB, rfl⟩
    refine ⟨⟨th θ (B, 0), R_le_dSub hc (th_mem θ _)⟩, Subgroup.mem_center_iff.mpr fun d => ?_,
      rfl⟩
    apply Subtype.ext
    change (d : M) * th θ (B, 0) = th θ (B, 0) * d
    exact th_mul_comm_of_mem_dSub d.2 (by rw [hB, zero_smul, add_zero])

omit hc in
theorem commutator_iSub_dSub : ⁅iSub θ, dSub hH κ⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rintro _ ⟨B, hB, rfl⟩ d hd
  exact th_mul_comm_of_mem_dSub hd (B := B) (ε := 0) (by
    rw [hB, symThreePolarSym_zero_right, smul_zero, zero_smul, add_zero])

omit hc in
theorem commutator_aSub_dSub_of_zero (hκ : κ = 0) : ⁅aSub θ, dSub hH κ⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rintro _ ⟨B, rfl⟩ d hd
  exact th_mul_comm_of_mem_dSub hd (B := B) (ε := 0) (by rw [hκ, zero_smul, zero_smul, add_zero])

omit [R.Normal] hc in
theorem eq_sum_polar : ∀ C : 𝕍, symThreeDiag (C : M₃) = 0 →
    C = (C : M₃) 0 1 • symThreePolarSym ![1, 0, 0] ![0, 1, 0] +
      (C : M₃) 0 2 • symThreePolarSym ![1, 0, 0] ![0, 0, 1] +
        (C : M₃) 1 2 • symThreePolarSym ![0, 1, 0] ![0, 0, 1] := by
  decide +kernel

theorem commutator_aSub_dSub_of_one (hκ : κ = 1) : ⁅aSub θ, dSub hH κ⁆ = iSub θ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    rintro _ ⟨B, rfl⟩ d hd
    rw [comm_th_dSub hd, zero_smul, add_zero]
    refine ⟨_, ?_, rfl⟩
    rw [coe_smul_binarySymMatrices, symThreeDiag_smul, symThreeDiag_polarSym, smul_zero]
  ·
    have hgen : ∀ u v : 𝔼, th θ (symThreePolarSym u v, 0) ∈ ⁅aSub θ, dSub hH κ⁆ := by
      intro u v
      obtain ⟨d, hd, hdu⟩ := exists_lab hc (symThreeDiagSection u)
      have h := comm_th_dSub (θ := θ) ((dSub hH κ).inv_mem hd) (symThreeDiagSection v) 0
      rw [inv_inv, hdu, symThreeDiag_diagSection, symThreeDiag_diagSection, hκ, one_smul,
        zero_smul, add_zero] at h
      rw [← h]
      exact Subgroup.commutator_mem_commutator
        (⟨_, rfl⟩ : th θ (symThreeDiagSection v, 0) ∈ aSub θ) ((dSub hH κ).inv_mem hd)
    have hsmul : ∀ (c : ZMod 2) (u v : 𝔼),
        th θ (c • symThreePolarSym u v, 0) ∈ ⁅aSub θ, dSub hH κ⁆ := by
      intro c u v
      rcases zmod_two_cases c with rfl | rfl
      · rw [zero_smul, show ((0 : 𝕍), (0 : ZMod 2)) = 0 from rfl, th_zero]
        exact Subgroup.one_mem _
      · rw [one_smul]
        exact hgen u v
    rintro _ ⟨C, hC, rfl⟩
    rw [eq_sum_polar C hC]
    have hadd : ∀ X Y : 𝕍, th θ (X + Y, 0) = th θ (X, 0) * th θ (Y, 0) := fun X Y => by
      rw [← th_add]
      rfl
    rw [hadd, hadd]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hsmul _ _ _) (hsmul _ _ _)) (hsmul _ _ _)

theorem comm_aSub_mem_center {a : M} (ha : a ∈ aSub θ) {d : M}
    (hd : d ∈ dSub hH κ) : a⁻¹ * (d⁻¹ * a * d) ∈ (Subgroup.center (dSub hH κ)).map
      (dSub hH κ).subtype := by
  obtain ⟨B, rfl⟩ := ha
  rw [th_comm_dSub hd, zero_smul, add_zero]
  obtain ⟨y, hy, hyx⟩ := (mem_center_dSub_iff hc _).mpr ⟨_, fun a' => by
    rw [coe_smul_binarySymMatrices, symThreeDiag_smul, symThreeDiag_polarSym, smul_zero,
      symThreePolarSym_zero_right, smul_zero], rfl⟩
  exact ⟨y, hy, hyx⟩

omit hc in
theorem comm_z_dSub {d : M} (hd : d ∈ dSub hH κ) :
    (th θ (0, 1))⁻¹ * (d⁻¹ * th θ (0, 1) * d) = th θ (lab hH d, 0) := by
  rw [th_comm_dSub hd, show symThreeDiag ((0 : 𝕍) : M₃) = 0 from rfl, symThreePolarSym_zero_right,
    smul_zero, zero_add, one_smul]

omit hc in
theorem lab_mul_dSub {d d' : M} (hd' : d' ∈ dSub hH κ) :
    lab hH (d * d') = lab hH d + lab hH d' + κ • symThreePolarSym
      (symThreeDiag (lab hH d' : M₃)) (symThreeDiag (lab hH d : M₃)) := by
  rw [lab_mul_of_mem hd', symThreeTwoCoreMap_apply, add_comm (lab hH d)]

omit hc in
theorem th_lab_mem_iSub_iff {m : M} :
    th θ (lab hH m, 0) ∈ iSub θ ↔ symThreeDiag (lab hH m : M₃) = 0 := by
  constructor
  · rintro ⟨B, hB, h⟩
    rw [Prod.mk.inj (th_injective θ h) |>.1]
    exact hB
  · intro h
    exact ⟨_, h, rfl⟩

omit hc in
theorem comm_z_mul_mem_iSub {d d' : M} (hd : d ∈ dSub hH κ) (hd' : d' ∈ dSub hH κ) :
    (th θ (0, 1))⁻¹ * ((d * d')⁻¹ * th θ (0, 1) * (d * d')) *
      ((th θ (0, 1))⁻¹ * (d⁻¹ * th θ (0, 1) * d) *
        ((th θ (0, 1))⁻¹ * (d'⁻¹ * th θ (0, 1) * d')))⁻¹ ∈ iSub θ := by
  rw [comm_z_dSub ((dSub hH κ).mul_mem hd hd'), comm_z_dSub hd, comm_z_dSub hd', ← th_add,
    th_inv, ← th_add, lab_mul_dSub hd']
  refine ⟨_, ?_, rfl⟩
  have key : ∀ a b c : 𝕍, a + b + c + (a + b) = c := fun a b c => by
    rw [show a + b + c + (a + b) = c + ((a + b) + (a + b)) by abel, symThree_add_self, add_zero]
  have h := key (lab hH d) (lab hH d') (κ • symThreePolarSym (symThreeDiag (lab hH d' : M₃))
    (symThreeDiag (lab hH d : M₃)))
  change symThreeDiag ((lab hH d + lab hH d' + _ + (lab hH d + lab hH d') : 𝕍) : M₃) = 0
  rw [h, coe_smul_binarySymMatrices, symThreeDiag_smul, symThreeDiag_polarSym, smul_zero]

theorem comm_z_mul_fSub {f f' : M} (hf : f ∈ fSub hH) (hf' : f' ∈ fSub hH) :
    (th θ (0, 1))⁻¹ * ((f * f')⁻¹ * th θ (0, 1) * (f * f')) =
      (th θ (0, 1))⁻¹ * (f⁻¹ * th θ (0, 1) * f) *
        ((th θ (0, 1))⁻¹ * (f'⁻¹ * th θ (0, 1) * f')) := by
  have hfD := fSub_le_dSub hc hf
  have hfD' := fSub_le_dSub hc hf'
  rw [comm_z_dSub ((dSub hH κ).mul_mem hfD hfD'), comm_z_dSub hfD, comm_z_dSub hfD', ← th_add,
    lab_mul_dSub hfD', ((mem_fSub_iff hc).mp hf').2, smul_polarSym_zero_left, add_zero]
  rfl

theorem sq_mem_R {d : M} (hd : d ∈ dSub hH κ) : d ^ 2 ∈ R := by
  rw [← mem_ker_phi hH, MonoidHom.mem_ker, map_pow]
  exact hc.abelP.2 _ hd

theorem comm_mem_R {d d' : M} (hd : d ∈ dSub hH κ) (hd' : d' ∈ dSub hH κ) : ⁅d, d'⁆ ∈ R := by
  rw [← mem_ker_phi hH, MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact congrArg Subtype.val (hc.abelP.1.is_comm.comm ⟨_, hd⟩ ⟨_, hd'⟩)

theorem relIndex_R_dSub : R.relIndex (dSub hH κ) = 64 := by
  have h := Subgroup.relIndex_mul_card R (dSub hH κ)
  rw [inf_of_le_left (R_le_dSub hc), card_R_of_equiv θ, card_dSub hc] at h
  omega

theorem relIndex_R_fSub : R.relIndex (fSub hH) = 8 := by
  have h := Subgroup.relIndex_mul_card R (fSub hH)
  rw [inf_of_le_left R_le_fSub, card_R_of_equiv θ, card_fSub hc] at h
  omega

theorem relIndex_fSub_dSub : (fSub hH).relIndex (dSub hH κ) = 8 := by
  have h := Subgroup.relIndex_mul_card (fSub hH) (dSub hH κ)
  rw [inf_of_le_left (fSub_le_dSub hc), card_fSub hc, card_dSub hc] at h
  omega

theorem pCore_eq_dSub : CFSG.Assembly.pCore 2 M = dSub hH κ := by
  apply le_antisymm
  · rw [CFSG.pCore_eq_iSup]
    refine iSup_le fun N => iSup_le fun hN => iSup_le fun hNp => ?_
    let f : M →* (phi hH).range := (phi hH).rangeRestrict
    have hf : Function.Surjective f := MonoidHom.rangeRestrict_surjective _
    have hle : N.map f ≤ CFSG.Assembly.pCore 2 (phi hH).range :=
      le_sSup ⟨hN.map f hf, hNp.map f⟩
    intro n hn
    have h2 : ((f n : (phi hH).range) : 𝕍 ≃ᵃ[ZMod 2] 𝕍) ∈
        CFSG.Assembly.pCoreOf 2 (phi hH).range := ⟨f n, hle ⟨n, hn, rfl⟩, rfl⟩
    rw [hc.pcore] at h2
    exact h2
  · rw [CFSG.pCore_eq_iSup]
    refine le_iSup_of_le (dSub hH κ) (le_iSup_of_le (dSub_normal hc) (le_iSup_of_le ?_ le_rfl))
    exact IsPGroup.of_card (n := 13) (by rw [card_dSub hc]; norm_num)

omit hc in
theorem affOf_linear (m : M) : (affOf hH m).linear = linEquiv hH m := by
  rw [affOf, linear_mul, tr_linear, one_mul, toAff_linear]

omit hc in
theorem aSub_normal (hH : Hyp θ) : (aSub θ).Normal :=
  ⟨fun _ ⟨B, hB⟩ g => ⟨(cAct θ g⁻¹ (B, 0)).1, by
    rw [hB, ← cAct_zero_eq hH, th_cAct, inv_inv]⟩⟩

theorem iSub_normal : (iSub θ).Normal :=
  ⟨fun _ ⟨B, hB0, hB⟩ g => ⟨(cAct θ g⁻¹ (B, 0)).1, by
    rw [← linEquiv_apply hH, ← affOf_linear]
    exact hc.lin _ (affOf_mem_range g⁻¹) B hB0, by
    rw [hB, ← cAct_zero_eq hH, th_cAct, inv_inv]⟩⟩

end Core

end SymThreeFullCoset

open SymThreeFullCoset SymThreeFullAffine in
theorem binary_symmetric_three_full_coset_two_group_structure
    {M : Type*} [Group M] (R : Subgroup M) [R.Normal]
    (θ : R ≃* Multiplicative (↥(binarySymMatrices 3) × ZMod 2))
    (z : M) (hz : z = θ.symm (.ofAdd (0, 1))) (A I : Subgroup M)
    (hA : ∀ x : M, x ∈ A ↔ ∃ B : ↥(binarySymMatrices 3), x = θ.symm (.ofAdd (B, 0)))
    (hI : ∀ x : M, x ∈ I ↔ ∃ B : ↥(binarySymMatrices 3),
      symThreeDiag (B : M₃) = 0 ∧ x = θ.symm (.ofAdd (B, 0)))
    (hΩ : ∀ (m : M) (B : ↥(binarySymMatrices 3)), ∃ B' : ↥(binarySymMatrices 3),
      m⁻¹ * (θ.symm (.ofAdd (B, 1)) : M) * m = θ.symm (.ofAdd (B', 1)))
    (hfaith : ∀ m : M, (∀ B : ↥(binarySymMatrices 3),
      m⁻¹ * (θ.symm (.ofAdd (B, 1)) : M) * m = θ.symm (.ofAdd (B, 1))) → m ∈ R)
    (htrans : ∀ B B' : ↥(binarySymMatrices 3), ∃ m : M,
      m⁻¹ * (θ.symm (.ofAdd (B, 1)) : M) * m = θ.symm (.ofAdd (B', 1)))
    (hstab : ∀ m : M, m⁻¹ * z * m = z → ∃ L : GL (Fin 3) (ZMod 2),
      ∀ B : ↥(binarySymMatrices 3),
        m⁻¹ * (θ.symm (.ofAdd (B, 1)) : M) * m = θ.symm (.ofAdd (symThreeCongr L B, 1)))
    (hstab' : ∀ L : GL (Fin 3) (ZMod 2), ∃ m : M, ∀ B : ↥(binarySymMatrices 3),
      m⁻¹ * (θ.symm (.ofAdd (B, 1)) : M) * m = θ.symm (.ofAdd (symThreeCongr L B, 1))) :
    ∃ (κ : ZMod 2) (D F : Subgroup M) (ν : M → ↥(binarySymMatrices 3)),
      F ≤ D ∧ D.Normal ∧ F.Normal ∧ CFSG.Assembly.pCore 2 M = D ∧
      Nat.card D = 8192 ∧ Nat.card F = 1024 ∧ R ≤ F ∧
      ((∀ d ∈ D, d ^ 2 ∈ R) ∧ (∀ d ∈ D, ∀ d' ∈ D, ⁅d, d'⁆ ∈ R) ∧ R.relIndex D = 64) ∧
      ((∀ f ∈ F, f ^ 2 ∈ R) ∧ (∀ f ∈ F, ∀ f' ∈ F, ⁅f, f'⁆ ∈ R) ∧ R.relIndex F = 8) ∧
      ((∀ d ∈ D, d ^ 2 ∈ F) ∧ (∀ d ∈ D, ∀ d' ∈ D, ⁅d, d'⁆ ∈ F) ∧ F.relIndex D = 8) ∧
      (∀ d ∈ D, d⁻¹ * z * d = θ.symm (.ofAdd (ν d, 1))) ∧
      (∀ d ∈ D, ∀ d' ∈ D, ν d = ν d' ↔ d⁻¹ * d' ∈ R) ∧
      (∀ B : ↥(binarySymMatrices 3), ∃ d ∈ D, ν d = B) ∧
      (∀ d ∈ D, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
        d⁻¹ * (θ.symm (.ofAdd (B, ε)) : M) * d = θ.symm (.ofAdd
          (B + κ • symThreePolarSym (symThreeDiag (ν d : M₃)) (symThreeDiag (B : M₃)) +
            ε • ν d, ε))) ∧
      (∀ d : M, d ∈ F ↔ d ∈ D ∧ symThreeDiag (ν d : M₃) = 0) ∧
      (∀ m : M, ∃ d ∈ D, ∃ c ∈ Subgroup.centralizer {z}, m = d * c) ∧
      D ⊓ Subgroup.centralizer {z} = R ∧
      A.Normal ∧ I.Normal ∧
      (Subgroup.center F).map F.subtype = A ∧
      ⁅R, D⁆ = A ∧
      (κ = 0 → (Subgroup.center D).map D.subtype = A ∧ ⁅A, D⁆ = ⊥) ∧
      (κ = 1 → (Subgroup.center D).map D.subtype = I ∧ ⁅A, D⁆ = I ∧
        A ≤ (Subgroup.upperCentralSeries D 2).map D.subtype) ∧
      ⁅I, D⁆ = ⊥ ∧
      ((∀ d ∈ D, z⁻¹ * (d⁻¹ * z * d) ∈ A) ∧
        (∀ d ∈ D, ∀ d' ∈ D, z⁻¹ * ((d * d')⁻¹ * z * (d * d')) *
          (z⁻¹ * (d⁻¹ * z * d) * (z⁻¹ * (d'⁻¹ * z * d')))⁻¹ ∈ I) ∧
        (∀ d ∈ D, z⁻¹ * (d⁻¹ * z * d) ∈ I ↔ d ∈ F) ∧
        (∀ a ∈ A, ∃ d ∈ D, (z⁻¹ * (d⁻¹ * z * d))⁻¹ * a ∈ I)) ∧
      ((∀ f ∈ F, z⁻¹ * (f⁻¹ * z * f) ∈ I) ∧
        (∀ f ∈ F, ∀ f' ∈ F, z⁻¹ * ((f * f')⁻¹ * z * (f * f')) =
          z⁻¹ * (f⁻¹ * z * f) * (z⁻¹ * (f'⁻¹ * z * f'))) ∧
        (∀ f ∈ F, z⁻¹ * (f⁻¹ * z * f) = 1 ↔ f ∈ R) ∧
        (∀ i ∈ I, ∃ f ∈ F, z⁻¹ * (f⁻¹ * z * f) = i)) ∧
      (∀ c ∈ Subgroup.centralizer {z}, ∀ d : M,
        z⁻¹ * ((c⁻¹ * d * c)⁻¹ * z * (c⁻¹ * d * c)) = c⁻¹ * (z⁻¹ * (d⁻¹ * z * d)) * c) := by
  have hH : Hyp θ :=
    { omega := fun m B => by
        obtain ⟨B', hB'⟩ := hΩ m B
        rw [th_injective θ ((th_cAct θ m (B, 1)).trans hB')]
      faith := fun m hm => hfaith m fun B => (th_cAct θ m (B, 1)).symm.trans (by rw [hm B]; rfl)
      trans := fun B B' => by
        obtain ⟨m, hm⟩ := htrans B B'
        exact ⟨m, th_injective θ ((th_cAct θ m (B, 1)).trans hm)⟩
      stab := fun m hm => by
        have hz' : m⁻¹ * z * m = z := by
          rw [hz]
          exact (th_cAct θ m (0, 1)).symm.trans (by rw [hm]; rfl)
        obtain ⟨L, hL⟩ := hstab m hz'
        exact ⟨L, fun B => th_injective θ ((th_cAct θ m (B, 1)).trans (hL B))⟩
      stab' := fun L => by
        obtain ⟨m, hm⟩ := hstab' L
        exact ⟨m, fun B => th_injective θ ((th_cAct θ m (B, 1)).trans (hm B))⟩ }
  obtain ⟨κ, hc⟩ := exists_core hH
  have hAeq : A = aSub θ := by
    ext x
    rw [hA]
    rfl
  have hIeq : I = iSub θ := by
    ext x
    rw [hI]
    rfl
  subst hz hAeq hIeq
  have hz : (θ.symm (.ofAdd (0, 1)) : M) = th θ (0, 1) := rfl
  refine ⟨κ, dSub hH κ, fSub hH, lab hH, fSub_le_dSub hc, dSub_normal hc, fSub_normal hc,
    pCore_eq_dSub hc, card_dSub hc, card_fSub hc, R_le_fSub,
    ⟨fun d hd => sq_mem_R hc hd, fun d hd d' hd' => comm_mem_R hc hd hd', relIndex_R_dSub hc⟩,
    ⟨fun f hf => sq_mem_R hc (fSub_le_dSub hc hf),
      fun f hf f' hf' => comm_mem_R hc (fSub_le_dSub hc hf) (fSub_le_dSub hc hf'),
      relIndex_R_fSub hc⟩,
    ⟨fun d hd => R_le_fSub (sq_mem_R hc hd), fun d hd d' hd' => R_le_fSub (comm_mem_R hc hd hd'),
      relIndex_fSub_dSub hc⟩,
    fun d _ => ?_, fun d hd d' hd' => lab_eq_iff hc hd hd', exists_lab hc,
    fun d hd B ε => ?_, fun d => mem_fSub_iff hc, ?_, ?_, aSub_normal hH, iSub_normal hc,
    ?_, commutator_R_dSub hc, ?_, ?_, commutator_iSub_dSub, ?_, ?_, ?_⟩
  · rw [hz, ← th_cAct, cAct_z]
    rfl
  · change d⁻¹ * th θ (B, ε) * d = th θ _
    rw [← th_cAct, cAct_of_mem_dSub hd]
  · rw [hz]
    exact exists_dSub_mul_centralizer hc
  · rw [hz]
    exact dSub_inf_centralizer hc
  · ext x
    rw [Subgroup.mem_map]
    exact mem_center_fSub_iff hc x
  · intro hκ
    refine ⟨Subgroup.ext fun x => ?_, commutator_aSub_dSub_of_zero hκ⟩
    rw [Subgroup.mem_map]
    refine (mem_center_dSub_iff hc x).trans ⟨fun ⟨B, _, hB⟩ => ⟨B, hB⟩, fun ⟨B, hB⟩ =>
      ⟨B, fun a => by rw [hκ, zero_smul], hB⟩⟩
  · intro hκ
    refine ⟨Subgroup.ext fun x => ?_, commutator_aSub_dSub_of_one hc hκ, fun a ha => ?_⟩
    · rw [Subgroup.mem_map]
      refine (mem_center_dSub_iff hc x).trans ⟨fun ⟨B, hB0, hB⟩ => ⟨B, ?_, hB⟩,
        fun ⟨B, hB0, hB⟩ => ⟨B, fun a => ?_, hB⟩⟩
      · refine (polarSym_forall_eq_zero_iff _).1 fun a => ?_
        have h := hB0 a
        rwa [hκ, one_smul] at h
      · rw [hκ, one_smul, hB0, symThreePolarSym_zero_right]
    · have haD : a ∈ dSub hH κ := by
        obtain ⟨B, rfl⟩ := ha
        exact R_le_dSub hc (θ.symm _).2
      refine ⟨⟨a, haD⟩, Subgroup.mem_upperCentralSeries_succ_iff.mpr fun y => ?_, rfl⟩
      rw [Subgroup.upperCentralSeries_one]
      obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp
        (comm_aSub_mem_center hc ((aSub θ).inv_mem ha) ((dSub hH κ).inv_mem y.2))
      have hwy : ⁅(⟨a, haD⟩ : dSub hH κ), y⁆ = w := Subtype.ext (by
        rw [Subgroup.subtype_apply] at hwx
        rw [hwx, commutatorElement_def]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, mul_assoc])
      rw [hwy]
      exact hw
  · rw [hz]
    refine ⟨fun d hd => ?_, fun d hd d' hd' => comm_z_mul_mem_iSub hd hd', fun d hd => ?_,
      fun a ha => ?_⟩
    · rw [comm_z_dSub hd]
      exact ⟨_, rfl⟩
    · rw [comm_z_dSub hd, th_lab_mem_iSub_iff, mem_fSub_iff hc]
      exact ⟨fun h => ⟨hd, h⟩, fun h => h.2⟩
    · obtain ⟨B, rfl⟩ := ha
      obtain ⟨d, hd, hdB⟩ := exists_lab hc B
      refine ⟨d, hd, ?_⟩
      rw [comm_z_dSub hd, hdB, inv_mul_cancel]
      exact (iSub θ).one_mem
  · rw [hz]
    refine ⟨fun f hf => ?_, fun f hf f' hf' => comm_z_mul_fSub hc hf hf', fun f hf => ?_,
      fun i hi => ?_⟩
    · rw [comm_z_dSub (fSub_le_dSub hc hf)]
      exact ⟨_, ((mem_fSub_iff hc).mp hf).2, rfl⟩
    · have hfD := fSub_le_dSub hc hf
      rw [comm_z_dSub hfD, ← th_zero θ]
      constructor
      · intro h
        have h1 := (Prod.mk.inj (th_injective θ h)).1
        have h2 := (lab_eq_iff hc hfD (dSub hH κ).one_mem).mp (by rw [h1, lab_one])
        simpa using h2
      · intro h
        rw [lab, affOf_eq_one_iff.mpr h]
        rfl
    · obtain ⟨B, hB0, rfl⟩ := hi
      obtain ⟨d, hd, hdB⟩ := exists_lab hc B
      exact ⟨d, (mem_fSub_iff hc).mpr ⟨hd, by rw [hdB]; exact hB0⟩, by rw [comm_z_dSub hd, hdB]⟩
  · intro c hc' d
    rw [Subgroup.mem_centralizer_singleton_iff] at hc'
    have h1 : c⁻¹ * (θ.symm (.ofAdd (0, 1)) : M) * c = θ.symm (.ofAdd (0, 1)) := by
      rw [mul_assoc, ← hc', inv_mul_cancel_left]
    conv_lhs => rw [← h1]
    group

end CFSG.LocalAnalysis.ComponentInitial
