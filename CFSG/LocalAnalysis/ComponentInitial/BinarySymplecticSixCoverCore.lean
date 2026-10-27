module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverComplement
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverDihedral

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Matrix CFSG.Assembly.LowTwoRank SymplecticFlag SymplecticTorusWeyl MatrixExtension
open scoped commutatorElement Pointwise

section Actions

variable {G E : Type*} [Group G] [Group E]

@[expose] def restrictAct (α : G →* MulAut E) (H : Subgroup E)
    (hH : ∀ g, ∀ x ∈ H, α g x ∈ H) : G →* MulAut H where
  toFun g :=
    { toFun := fun x => ⟨α g (x : E), hH g x x.2⟩
      invFun := fun x => ⟨α g⁻¹ (x : E), hH g⁻¹ x x.2⟩
      left_inv := fun x => Subtype.ext (by
        change α g⁻¹ (α g (x : E)) = (x : E)
        rw [map_inv, MulAut.inv_apply_self])
      right_inv := fun x => Subtype.ext (by
        change α g (α g⁻¹ (x : E)) = (x : E)
        rw [map_inv, MulAut.apply_inv_self])
      map_mul' := fun x y => Subtype.ext (map_mul (α g) (x : E) (y : E)) }
  map_one' := MulEquiv.ext fun x => Subtype.ext (by
    change α 1 (x : E) = (x : E)
    rw [map_one, MulAut.one_apply])
  map_mul' g h := MulEquiv.ext fun x => Subtype.ext (by
    change α (g * h) (x : E) = α g (α h (x : E))
    rw [map_mul, MulAut.mul_apply])

theorem coe_restrictAct (α : G →* MulAut E) (H : Subgroup E)
    (hH : ∀ g, ∀ x ∈ H, α g x ∈ H) (g : G) (x : H) :
    ((restrictAct α H hH g x : H) : E) = α g x :=
  rfl

@[expose] def quotientAct (α : G →* MulAut E) (N : Subgroup E) [N.Normal]
    (hN : ∀ g, ∀ x ∈ N, α g x ∈ N) : G →* MulAut (E ⧸ N) where
  toFun g := QuotientGroup.congr N N (α g) (by
    refine le_antisymm ?_ fun x hx => ⟨α g⁻¹ x, hN g⁻¹ x hx, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hN g x hx
    · change α g (α g⁻¹ x) = x
      rw [map_inv, MulAut.apply_inv_self])
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [QuotientGroup.congr_mk, map_one, MulAut.one_apply, MulAut.one_apply]
  map_mul' g h := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk, map_mul, MulAut.mul_apply]

theorem quotientAct_mk (α : G →* MulAut E) (N : Subgroup E) [N.Normal]
    (hN : ∀ g, ∀ x ∈ N, α g x ∈ N) (g : G) (x : E) :
    quotientAct α N hN g (x : E ⧸ N) = (α g x : E ⧸ N) :=
  rfl

theorem commutator_sup_le {A Z : Subgroup E} (hZ : Z ≤ Subgroup.center E) :
    ⁅A ⊔ Z, A ⊔ Z⁆ ≤ ⁅A, A⁆ := by
  have : Z.Normal := Subgroup.normal_of_le_center hZ
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul] at hx hy
  obtain ⟨a, ha, z, hz, rfl⟩ := hx
  obtain ⟨b, hb, w, hw, rfl⟩ := hy
  have hk : (QuotientGroup.mk' Z).ker ≤ Subgroup.center E := by
    rw [QuotientGroup.ker_mk']
    exact hZ
  rw [commutatorElement_eq_of_map_eq (QuotientGroup.mk' Z) hk (x' := a) (y' := b)
    (by rw [map_mul, show QuotientGroup.mk' Z z = 1 from (QuotientGroup.eq_one_iff z).mpr hz,
      mul_one])
    (by rw [map_mul, show QuotientGroup.mk' Z w = 1 from (QuotientGroup.eq_one_iff w).mpr hw,
      mul_one])]
  exact Subgroup.commutator_mem_commutator ha hb

end Actions

section Lift

variable {E X : Type*} [Group E] [Group X] {θ : E →* X} (hθ : Function.Surjective θ)
  (hC : θ.ker ≤ Subgroup.center E)

include hC in
theorem conj_eq_of_map_eq {a b : E} (h : θ a = θ b) : MulAut.conj a = MulAut.conj b := by
  have hk : a⁻¹ * b ∈ Subgroup.center E := hC (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel])
  have hb : b = a * (a⁻¹ * b) := by group
  rw [hb, map_mul]
  have : MulAut.conj (a⁻¹ * b) = 1 := MulEquiv.ext fun x => by
    rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.mp hk x,
      mul_inv_cancel_right]
  rw [this, mul_one]

@[expose] def liftConj : X →* MulAut E where
  toFun x := MulAut.conj (Function.surjInv hθ x)
  map_one' := by
    rw [conj_eq_of_map_eq hC (b := 1) (by rw [Function.surjInv_eq hθ 1, map_one]), map_one]
  map_mul' x y := by
    rw [conj_eq_of_map_eq hC (b := Function.surjInv hθ x * Function.surjInv hθ y)
      (by rw [Function.surjInv_eq hθ, map_mul, Function.surjInv_eq hθ, Function.surjInv_eq hθ]),
      map_mul]

theorem liftConj_apply (a : E) : liftConj hθ hC (θ a) = MulAut.conj a :=
  conj_eq_of_map_eq hC (Function.surjInv_eq hθ _)

theorem liftConj_apply_of_mem_ker (x : X) {c : E} (hc : θ c = 1) : liftConj hθ hC x c = c := by
  change MulAut.conj (Function.surjInv hθ x) c = c
  rw [MulAut.conj_apply, Subgroup.mem_center_iff.mp (hC hc) (Function.surjInv hθ x),
    mul_inv_cancel_right]

theorem map_liftConj_apply (x : X) (y : E) : θ (liftConj hθ hC x y) = x * θ y * x⁻¹ := by
  change θ (MulAut.conj (Function.surjInv hθ x) y) = x * θ y * x⁻¹
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, Function.surjInv_eq hθ]

end Lift

section Cover

variable {E : Type*} [Group E] (θ : E →* StatedSp 3 (ZMod 2))

@[expose] def kerTwo : Subgroup E where
  carrier := {c | c ∈ Subgroup.center E ∧ θ c = 1 ∧ c ^ 2 = 1}
  mul_mem' {a b} ha hb := ⟨Subgroup.mul_mem _ ha.1 hb.1, by rw [map_mul, ha.2.1, hb.2.1, mul_one],
    by rw [(show Commute a b from (Subgroup.mem_center_iff.mp ha.1 b).symm).mul_pow, ha.2.2,
      hb.2.2, mul_one]⟩
  one_mem' := ⟨Subgroup.one_mem _, map_one θ, one_pow 2⟩
  inv_mem' {a} ha := ⟨Subgroup.inv_mem _ ha.1, by rw [map_inv, ha.2.1, inv_one],
    by rw [inv_pow, ha.2.2, inv_one]⟩

theorem kerTwo_le_center : kerTwo θ ≤ Subgroup.center E := fun _ h => h.1

instance kerTwo_normal : (kerTwo θ).Normal :=
  Subgroup.normal_of_le_center (kerTwo_le_center θ)

@[expose] def preTau : Subgroup E :=
  (tauSym 3).range.comap θ

theorem kerTwo_le_preTau : kerTwo θ ≤ preTau θ := fun c hc =>
  ⟨1, by rw [map_one, hc.2.1]⟩

instance kerTwo_subgroupOf_normal : ((kerTwo θ).subgroupOf (preTau θ)).Normal :=
  (kerTwo_normal θ).subgroupOf _

abbrev MBar := preTau θ ⧸ (kerTwo θ).subgroupOf (preTau θ)

@[expose] def piM : preTau θ →* Multiplicative (binarySymMatrices 3) :=
  (MonoidHom.ofInjective tauSym_injective).symm.toMonoidHom.comp
    ((θ.comp (preTau θ).subtype).codRestrict _ fun x => x.2)

theorem tauSym_piM (x : preTau θ) : tauSym 3 (piM θ x) = θ x := by
  have h := (MonoidHom.ofInjective (tauSym_injective (n := 3))).apply_symm_apply
    ⟨θ x, x.2⟩
  exact congrArg Subtype.val h

theorem piM_eq_one_iff (x : preTau θ) : piM θ x = 1 ↔ θ x = 1 := by
  rw [← tauSym_piM θ x]
  exact ⟨fun h => by rw [h, map_one], fun h => tauSym_injective (by rw [h, map_one])⟩

theorem kerTwo_subgroupOf_le_ker : (kerTwo θ).subgroupOf (preTau θ) ≤ (piM θ).ker :=
  fun x hx => (piM_eq_one_iff θ x).mpr (Subgroup.mem_subgroupOf.mp hx).2.1

@[expose] def piBar : MBar θ →* Multiplicative (binarySymMatrices 3) :=
  QuotientGroup.lift _ (piM θ) (kerTwo_subgroupOf_le_ker θ)

theorem piBar_mk (x : preTau θ) : piBar θ (x : MBar θ) = piM θ x :=
  QuotientGroup.lift_mk _ _ _

variable {θ} (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

@[expose] def act : GL (Fin 3) (ZMod 2) →* MulAut E :=
  (liftConj hθ hC).comp leviSp

theorem map_act_apply (g : GL (Fin 3) (ZMod 2)) (y : E) :
    θ (act hθ hC g y) = leviSp g * θ y * (leviSp g)⁻¹ :=
  map_liftConj_apply hθ hC _ y

theorem act_apply_of_mem_ker (g : GL (Fin 3) (ZMod 2)) {c : E} (hc : θ c = 1) :
    act hθ hC g c = c :=
  liftConj_apply_of_mem_ker hθ hC _ hc

theorem act_mem_preTau (g : GL (Fin 3) (ZMod 2)) {y : E} (hy : y ∈ preTau θ) :
    act hθ hC g y ∈ preTau θ := by
  obtain ⟨B, hB⟩ := hy
  exact ⟨Multiplicative.ofAdd ⟨(g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
    (B.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ,
    congr_mem_binarySymMatrices _ _⟩, by rw [map_act_apply, ← hB, leviSp_mul_tauSym_mul_inv]⟩

theorem act_mem_kerTwo (g : GL (Fin 3) (ZMod 2)) {c : E} (hc : c ∈ kerTwo θ) :
    act hθ hC g c ∈ kerTwo θ := by
  rw [act_apply_of_mem_ker hθ hC g hc.2.1]
  exact hc

@[expose] def actM : GL (Fin 3) (ZMod 2) →* MulAut (preTau θ) :=
  restrictAct (act hθ hC) (preTau θ) fun g _ hy => act_mem_preTau hθ hC g hy

@[expose] def actBar : GL (Fin 3) (ZMod 2) →* MulAut (MBar θ) :=
  quotientAct (actM hθ hC) _ fun g x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact act_mem_kerTwo hθ hC g hx

theorem actBar_mk (g : GL (Fin 3) (ZMod 2)) (x : preTau θ) :
    actBar hθ hC g (x : MBar θ) = (actM hθ hC g x : MBar θ) :=
  quotientAct_mk _ _ _ _ _

theorem coe_actM (g : GL (Fin 3) (ZMod 2)) (x : preTau θ) :
    ((actM hθ hC g x : preTau θ) : E) = act hθ hC g x :=
  rfl

theorem piM_actM (g : GL (Fin 3) (ZMod 2)) (x : preTau θ) :
    ((piM θ (actM hθ hC g x)).toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        ((piM θ x).toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ := by
  have h : tauSym 3 (piM θ (actM hθ hC g x)) = tauSym 3 (Multiplicative.ofAdd
      ⟨(g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * ((piM θ x).toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2))
        * (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ, congr_mem_binarySymMatrices _ _⟩) := by
    rw [tauSym_piM, coe_actM, map_act_apply, ← tauSym_piM θ x, leviSp_mul_tauSym_mul_inv]
  have := congrArg (fun B : Multiplicative (binarySymMatrices 3) =>
    ((B.toAdd : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2))) (tauSym_injective h)
  exact this

theorem piBar_actBar (g : GL (Fin 3) (ZMod 2)) (x : MBar θ) :
    ((piBar θ (actBar hθ hC g x)).toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        ((piBar θ x).toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ := by
  induction x using QuotientGroup.induction_on with
  | H x => rw [actBar_mk, piBar_mk, piBar_mk, piM_actM]

include hθ in
theorem piBar_surjective : Function.Surjective (piBar θ) := by
  intro B
  obtain ⟨y, hy⟩ := hθ (tauSym 3 B)
  refine ⟨((⟨y, ⟨B, hy.symm⟩⟩ : preTau θ) : MBar θ), ?_⟩
  rw [piBar_mk]
  exact tauSym_injective (by rw [tauSym_piM]; exact hy)

theorem actBar_apply_of_mem_ker (g : GL (Fin 3) (ZMod 2)) {c : MBar θ}
    (hc : c ∈ (piBar θ).ker) : actBar hθ hC g c = c := by
  induction c using QuotientGroup.induction_on with
  | H x =>
    rw [MonoidHom.mem_ker, piBar_mk, piM_eq_one_iff] at hc
    rw [actBar_mk]
    congr 1
    exact Subtype.ext (act_apply_of_mem_ker hθ hC g hc)

theorem map_sq_eq_one {y : E} (hy : y ∈ preTau θ) : θ (y ^ 2) = 1 := by
  obtain ⟨B, hB⟩ := hy
  rw [map_pow, ← hB, ← map_pow]
  have : B ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [toAdd_pow, AddSubgroup.coe_nsmul, two_nsmul]
    exact binary_add_self _
  rw [this, map_one]

include hC in
theorem commutatorElement_mem_kerTwo {x y : E} (hx : x ∈ preTau θ) (hy : y ∈ preTau θ) :
    ⁅x, y⁆ ∈ kerTwo θ := by
  have hcomm : θ ⁅x, y⁆ = 1 := by
    obtain ⟨B, hB⟩ := hx
    obtain ⟨B', hB'⟩ := hy
    rw [map_commutatorElement, ← hB, ← hB', commutatorElement_eq_one_iff_mul_comm, ← map_mul,
      ← map_mul, mul_comm]
  have hc : ⁅x, y⁆ ∈ Subgroup.center E := hC hcomm
  refine ⟨hc, hcomm, ?_⟩
  have hx2 : x ^ 2 ∈ Subgroup.center E := hC (map_sq_eq_one hx)
  have h : ⁅x ^ 2, y⁆ = ⁅x, y⁆ ^ 2 := by
    have hxc : x * ⁅x, y⁆ = ⁅x, y⁆ * x := (Subgroup.mem_center_iff.mp hc x)
    simp only [commutatorElement_def, sq] at hxc ⊢
    calc x * x * y * (x * x)⁻¹ * y⁻¹ = x * (x * y * x⁻¹ * y⁻¹) * (y * x⁻¹ * y⁻¹) := by group
      _ = (x * y * x⁻¹ * y⁻¹) * x * (y * x⁻¹ * y⁻¹) := by rw [hxc]
      _ = (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
  rw [← h, commutatorElement_eq_one_of_mem_center_left hx2]

include hC in
theorem mBar_mul_comm (a b : MBar θ) : a * b = b * a := by
  induction a using QuotientGroup.induction_on with
  | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      rw [Subgroup.mem_subgroupOf]
      have h := commutatorElement_mem_kerTwo hC (inv_mem y.2) (inv_mem x.2)
      have : (((x * y)⁻¹ * (y * x) : preTau θ) : E) = ⁅(y : E)⁻¹, (x : E)⁻¹⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [this]
      exact h

include hC in
theorem piBar_ker_sq (h4 : ∀ c, θ c = 1 → c ^ 4 = 1) {c : MBar θ} (hc : c ∈ (piBar θ).ker) :
    c ^ 2 = 1 := by
  induction c using QuotientGroup.induction_on with
  | H x =>
    rw [MonoidHom.mem_ker, piBar_mk, piM_eq_one_iff] at hc
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    have hx2 : θ ((x : E) ^ 2) = 1 := by rw [map_pow, hc, one_pow]
    refine ⟨hC hx2, hx2, ?_⟩
    rw [← pow_mul]
    exact h4 _ hc

include hθ hC in
theorem mBar_sq_eq_one (h4 : ∀ c, θ c = 1 → c ^ 4 = 1) (x : MBar θ) : x ^ 2 = 1 :=
  binarySym_sq_eq_one (n := 3) le_rfl (actBar hθ hC) (piBar θ) (piBar_surjective hθ)
    (piBar_actBar hθ hC) (fun _ hc => piBar_ker_sq hC h4 hc)
    (fun g _ hc => actBar_apply_of_mem_ker hθ hC g hc) (mBar_mul_comm hC) x

@[expose] def tauE : StatedSp 3 (ZMod 2) :=
  tauSym 3 (Multiplicative.ofAdd ⟨single 0 0 1, single_mem_binarySymMatrices 0⟩)

include hC in
theorem act_mul_inv_mem_kerTwo {x : E} (hx : θ x = tauE) {h : GL (Fin 3) (ZMod 2)}
    (hh : (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    act hθ hC h x * x⁻¹ ∈ kerTwo θ := by
  obtain ⟨φ, hφ⟩ : ∃ φ : GL (Fin 3) (ZMod 2) → E, ∀ h, φ h = act hθ hC h x * x⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have hker : ∀ h : GL (Fin 3) (ZMod 2),
      (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1 → θ (φ h) = 1 := by
    intro h hh
    have hE : (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) * single 0 0 1 *
        (h : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = single 0 0 1 := by
      rw [← vecMulVec_single_single, mul_vecMulVec_mul_transpose, hh]
    have hτ : leviSp h * tauE * (leviSp h)⁻¹ = tauE := by
      rw [tauE, leviSp_mul_tauSym_mul_inv]
      congr 2
      exact Subtype.ext hE
    rw [hφ, map_mul, map_act_apply, hx, hτ, map_inv, hx, mul_inv_cancel]
  have hcen : ∀ h : GL (Fin 3) (ZMod 2),
      (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
        φ h ∈ Subgroup.center E := fun h hh => hC (hker h hh)
  have hmul : ∀ h₁ h₂ : GL (Fin 3) (ZMod 2),
      (h₂ : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
        φ (h₁ * h₂) = φ h₂ * φ h₁ := by
    intro h₁ h₂ hh₂
    have h₂x : act hθ hC h₂ x = φ h₂ * x := by rw [hφ, inv_mul_cancel_right]
    have hfix : act hθ hC h₁ (φ h₂) = φ h₂ := act_apply_of_mem_ker hθ hC h₁ (hker h₂ hh₂)
    rw [hφ (h₁ * h₂), map_mul, MulAut.mul_apply, h₂x, map_mul, hfix, hφ h₁, mul_assoc]
  have hone : φ 1 = 1 := by rw [hφ, map_one, MulAut.one_apply, mul_inv_cancel]
  set T : Subgroup (GL (Fin 3) (ZMod 2)) :=
    { carrier := {h | (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
        φ h ^ 2 = 1}
      mul_mem' := fun {a b} ha hb => ⟨by rw [Units.val_mul, ← mulVec_mulVec, hb.1, ha.1], by
        rw [hmul a b hb.1, (show Commute (φ b) (φ a) from
          (Subgroup.mem_center_iff.mp (hcen a ha.1) (φ b))).mul_pow, ha.2, hb.2, mul_one]⟩
      one_mem' := ⟨by rw [Units.val_one, one_mulVec], by rw [hone, one_pow]⟩
      inv_mem' := fun {a} ha => by
        have hinv : (((a⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) *ᵥ
            Pi.single 0 1 = Pi.single 0 1 := by
          conv_lhs => rw [← ha.1]
          rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
        refine ⟨hinv, ?_⟩
        have h1 := hmul a a⁻¹ hinv
        rw [mul_inv_cancel, hone] at h1
        have h2 : φ a⁻¹ = (φ a)⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
        rw [h2, inv_pow, ha.2, inv_one] }
  have hT : h ∈ T := by
    refine (Subgroup.closure_le T).mpr ?_ (mem_closure_involutions hh)
    rintro t ⟨ht, htt⟩
    refine ⟨ht, ?_⟩
    rw [sq, ← hmul t t ht, htt, hone]
  have hT' := hT.2
  rw [hφ] at hT'
  have hc' := hcen h hh
  have hk' := hker h hh
  rw [hφ] at hc' hk'
  exact ⟨hc', hk', hT'⟩

include hC in
theorem actBar_apply_eq_of_stab {x : MBar θ}
    (hx : ((piBar θ x).toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) = single 0 0 1)
    {h : GL (Fin 3) (ZMod 2)}
    (hh : (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    actBar hθ hC h x = x := by
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [piBar_mk] at hx
    have hy : θ y = tauE := by
      rw [← tauSym_piM, tauE]
      congr 1
      exact Multiplicative.toAdd.injective (Subtype.ext hx)
    have hm := act_mul_inv_mem_kerTwo hθ hC hy hh
    rw [actBar_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      coe_actM]
    have heq : (act hθ hC h y)⁻¹ * y = (y : E)⁻¹ * (act hθ hC h y * (y : E)⁻¹)⁻¹ * (y : E)⁻¹⁻¹ :=
      by group
    rw [heq]
    exact (kerTwo_normal θ).conj_mem _ (inv_mem hm) _

include hθ hC in
theorem exists_invariant_complement (h4 : ∀ c, θ c = 1 → c ^ 4 = 1) :
    ∃ V : Subgroup E, V ≤ preTau θ ∧ kerTwo θ ≤ V ∧ (∀ g, ∀ v ∈ V, act hθ hC g v ∈ V) ∧
      (∀ v ∈ V, θ v = 1 → v ∈ kerTwo θ) ∧ ∀ B, ∃ v ∈ V, θ v = tauSym 3 B := by
  let _ : CommGroup (MBar θ) := { (inferInstance : Group (MBar θ)) with
    mul_comm := mBar_mul_comm hC }
  let _ : Module (ZMod 2) (Additive (MBar θ)) := AddCommGroup.zmodModule fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, mBar_sq_eq_one hθ hC h4, ofMul_one]
  let actA : GL (Fin 3) (ZMod 2) →* AddMonoid.End (Additive (MBar θ)) :=
    { toFun := fun g => MonoidHom.toAdditive (actBar hθ hC g).toMonoidHom
      map_one' := by
        ext x
        rw [map_one]
        rfl
      map_mul' := fun g h => by
        ext x
        rw [map_mul]
        rfl }
  have hactA : ∀ g x, actA g x = Additive.ofMul (actBar hθ hC g x.toMul) := fun _ _ => rfl
  let πA : Additive (MBar θ) →+ Matrix (Fin 3) (Fin 3) (ZMod 2) :=
    { toFun := fun x => ((piBar θ x.toMul).toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2))
      map_zero' := by simp
      map_add' := fun x y => by simp }
  have hπA : ∀ x, πA x = ((piBar θ x.toMul).toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    fun _ => rfl
  have hkerA : ∀ c : Additive (MBar θ), πA c = 0 → c.toMul ∈ (piBar θ).ker := fun c h => by
    rw [MonoidHom.mem_ker]
    exact Multiplicative.toAdd.injective (Subtype.ext h)
  obtain ⟨S, hSinv, hSinj, hSsurj⟩ := sym_three_exists_invariant_complement (act := actA)
    (π := πA) (fun g x => by rw [hactA, hπA, hπA, toMul_ofMul, piBar_actBar])
    (fun g c hc => by rw [hactA, actBar_apply_of_mem_ker hθ hC g (hkerA c hc), ofMul_toMul])
    (fun X hX => by
      obtain ⟨x, hx⟩ := piBar_surjective hθ (Multiplicative.ofAdd ⟨X, hX⟩)
      exact ⟨Additive.ofMul x, by rw [hπA, toMul_ofMul, hx]; rfl⟩)
    (fun x hx g hg => by
      rw [hactA, actBar_apply_eq_of_stab hθ hC (hπA x ▸ hx) hg, ofMul_toMul])
  let SM : Subgroup (MBar θ) :=
    { carrier := {x | Additive.ofMul x ∈ S}
      mul_mem' := fun {a b} ha hb => by
        change Additive.ofMul (a * b) ∈ S
        rw [ofMul_mul]
        exact S.add_mem ha hb
      one_mem' := by
        change Additive.ofMul (1 : MBar θ) ∈ S
        rw [ofMul_one]
        exact S.zero_mem
      inv_mem' := fun {a} ha => by
        change Additive.ofMul a⁻¹ ∈ S
        rw [ofMul_inv]
        exact S.neg_mem ha }
  have hSM : ∀ x, x ∈ SM ↔ Additive.ofMul x ∈ S := fun _ => Iff.rfl
  refine ⟨(SM.comap (QuotientGroup.mk' _)).map (preTau θ).subtype, Subgroup.map_subtype_le _,
    fun c hc => Subgroup.mem_map.mpr ⟨⟨c, kerTwo_le_preTau θ hc⟩, ?_, rfl⟩, ?_, ?_, fun B => ?_⟩
  · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hc)]
    exact SM.one_mem
  · intro g v hv
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hv
    refine Subgroup.mem_map.mpr ⟨actM hθ hC g y, ?_, rfl⟩
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, ← actBar_mk, hSM]
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, hSM] at hy
    have := hSinv g _ hy
    rwa [hactA, toMul_ofMul] at this
  · intro v hv hθy
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hv
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, hSM] at hy
    have h0 := hSinj _ hy (by
      rw [hπA, toMul_ofMul, piBar_mk, (piM_eq_one_iff θ y).mpr hθy]
      rfl)
    rw [← ofMul_one, Additive.ofMul.injective.eq_iff, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h0
    exact h0
  · obtain ⟨s, hs, hsB⟩ := hSsurj _ B.toAdd.2
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective s.toMul
    refine ⟨y, Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩, ?_⟩
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, hy, hSM, ofMul_toMul]
      exact hs
    · rw [← tauSym_piM]
      congr 1
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      rw [← hsB, hπA, ← hy, piBar_mk]

include hθ hC in
theorem kernel_sq_eq_one [Finite E] [Group.IsPerfect E] (h4 : ∀ c, θ c = 1 → c ^ 4 = 1)
    {c : E} (hc : θ c = 1) : c ^ 2 = 1 := by
  obtain ⟨V, hVM, -, hVinv, hVker, hVsurj⟩ := exists_invariant_complement hθ hC h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := (leviSp : GL (Fin 3) (ZMod 2) →* StatedSp 3 (ZMod 2)).range with hR
  have : Group.IsPerfect (GL (Fin 3) (ZMod 2)) := isPerfect_GL_three_zmod_two
  have : Group.IsPerfect R := Group.IsPerfect.range _
  set H := R.comap θ with hH
  set F := ⁅H, H⁆ with hF
  have hFR : F.map θ = R := by
    rw [hF, Subgroup.map_commutator, hH, Subgroup.map_comap_eq_self_of_surjective hθ,
      Subgroup.commutator_eq_self]
  have hFH : F ≤ H := Subgroup.commutator_le_self H
  have hHF : H ≤ F ⊔ θ.ker := by
    intro h hh
    have hhR : θ h ∈ F.map θ := by rw [hFR]; exact hh
    obtain ⟨f, hf, hfh⟩ := hhR
    have hk : f⁻¹ * h ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfh, inv_mul_cancel]
    have := Subgroup.mul_mem_sup hf hk
    rwa [mul_inv_cancel_left] at this
  have hFF : ⁅F, F⁆ = F := le_antisymm (Subgroup.commutator_le_self F)
    ((Subgroup.commutator_mono hHF hHF).trans (commutator_sup_le hC))
  have : Group.IsPerfect F := Subgroup.isPerfect_iff.mpr hFF
  set θF : F →* R := (θ.comp F.subtype).codRestrict R fun f => hFH f.2 with hθF
  have hθFsurj : Function.Surjective θF := by
    rintro ⟨r, hr⟩
    rw [← hFR] at hr
    obtain ⟨f, hf, hfr⟩ := hr
    exact ⟨⟨f, hf⟩, Subtype.ext hfr⟩
  have hθFker : ∀ f : F, θF f = 1 ↔ θ f = 1 := fun f =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hθFcen : θF.ker ≤ Subgroup.center F := fun f hf => Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((hθFker f).mp hf)) g)
  have hθF2 : IsPGroup 2 θF.ker := fun k => ⟨2, Subtype.ext (Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact h4 _ ((hθFker k).mp k.2)))⟩
  have hbound := (LinearCover.linear_three_two_cover_kernel_bound θF hθFsurj hθFcen hθF2
    lieModel_range_leviSp).2
  have hFC₀ : ∀ f ∈ F, θ f = 1 → f ∈ kerTwo θ := by
    intro f hf hθf
    set k : θF.ker := ⟨⟨f, hf⟩, (hθFker ⟨f, hf⟩).mpr hθf⟩
    have hk : k ^ 2 = 1 := by
      have hpos : 0 < Nat.card θF.ker := Nat.card_pos
      have hpow : k ^ Nat.card θF.ker = 1 := pow_card_eq_one'
      rcases (show Nat.card θF.ker = 1 ∨ Nat.card θF.ker = 2 by omega) with h | h
      · rw [h, pow_one] at hpow
        rw [hpow, one_pow]
      · rwa [h] at hpow
    have hf2 : f ^ 2 = 1 := by
      have := congrArg (fun z : θF.ker => ((z : F) : E)) hk
      simpa using this
    exact ⟨hC hθf, hθf, hf2⟩
  set UR := (unitriangularGL 3 (ZMod 2)).map leviSp with hUR
  set Ũ := UR.comap θ ⊓ (F ⊔ kerTwo θ) with hŨ
  have hŨ₁ : ∀ u ∈ Ũ, ∃ A ∈ unitriangularGL 3 (ZMod 2), θ u = leviSp A := by
    rintro u ⟨⟨A, hA, hAu⟩, -⟩
    exact ⟨A, hA, hAu.symm⟩
  have hŨ₂ : ∀ A ∈ unitriangularGL 3 (ZMod 2), ∃ u ∈ Ũ, θ u = leviSp A := by
    intro A hA
    have hAR : leviSp A ∈ F.map θ := by rw [hFR]; exact ⟨A, rfl⟩
    obtain ⟨f, hf, hfA⟩ := hAR
    exact ⟨f, ⟨⟨A, hA, hfA.symm⟩, Subgroup.mem_sup_left hf⟩, hfA⟩
  have hŨ₃ : ∀ u ∈ Ũ, θ u = 1 → u ∈ kerTwo θ := by
    intro u hu' hθu
    have hu : u ∈ F ⊔ kerTwo θ := (Subgroup.mem_inf.mp hu').2
    rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul] at hu
    obtain ⟨f, hf, z, hz, rfl⟩ := hu
    have hθf : θ f = 1 := by
      rw [map_mul, hz.2.1, mul_one] at hθu
      exact hθu
    exact Subgroup.mul_mem _ (hFC₀ f hf hθf) hz
  have hŨN : Ũ ≤ Subgroup.normalizer (V : Set E) := by
    intro u hu
    obtain ⟨A, -, hAu⟩ := hŨ₁ u hu
    have hconj : act hθ hC A = MulAut.conj u := by
      change liftConj hθ hC (leviSp A) = MulAut.conj u
      rw [← hAu, liftConj_apply]
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      have := hVinv A v hv
      rwa [hconj, MulAut.conj_apply] at this
    · intro hv
      have := hVinv A⁻¹ _ hv
      rwa [map_inv, hconj, ← MulAut.conj_apply, MulAut.inv_apply_self] at this
  set P₀ := Ũ ⊔ V with hP₀
  have hP₀mul : (P₀ : Set E) = (Ũ : Set E) * (V : Set E) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Ũ V hŨN
  have hP₀ker : ∀ p ∈ P₀, θ p = 1 → p ∈ kerTwo θ := by
    intro p hp hθp
    rw [← SetLike.mem_coe, hP₀mul, Set.mem_mul] at hp
    obtain ⟨u, hu, v, hv, rfl⟩ := hp
    obtain ⟨A, -, hAu⟩ := hŨ₁ u hu
    obtain ⟨B, hB⟩ := hVM hv
    rw [map_mul, hAu, ← hB, mul_eq_one_iff_eq_inv, ← map_inv] at hθp
    obtain ⟨hB1, hA1⟩ := tauSym_eq_leviSp hθp.symm
    have hθv : θ v = 1 := by rw [← hB, inv_eq_one.mp hB1, map_one]
    have hθu : θ u = 1 := by rw [hAu, hA1, map_one]
    exact Subgroup.mul_mem _ (hŨ₃ u hu hθu) (hVker v hv hθv)
  have hP₀surj : ∀ g ∈ unipotent 3 (ZMod 2), ∃ p ∈ P₀, θ p = g := by
    intro g hg
    obtain ⟨A, hA, B, rfl⟩ := exists_eq_leviSp_mul_tauSym hg
    obtain ⟨u, hu, hθu⟩ := hŨ₂ A hA
    obtain ⟨v, hv, hθv⟩ := hVsurj B
    exact ⟨u * v, Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hv),
      by rw [map_mul, hθu, hθv]⟩
  obtain ⟨PU, hPU⟩ := exists_sylow_unipotent (K := ZMod 2) 2 3
  have hkerP : IsPGroup 2 θ.ker := fun k => ⟨2, Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact h4 _ k.2)⟩
  have hrange : (PU : Subgroup (StatedSp 3 (ZMod 2))) ≤ θ.range := by
    rw [MonoidHom.range_eq_top_of_surjective θ hθ]
    exact le_top
  set P₂ := PU.comapOfKerIsPGroup θ hkerP hrange with hP₂def
  have hP₂ : (P₂ : Subgroup E) = (unipotent 3 (ZMod 2)).comap θ := by
    rw [hP₂def, Sylow.coe_comapOfKerIsPGroup, hPU]
  have htrans : θ.ker ≤ ⁅(P₂ : Subgroup E), (P₂ : Subgroup E)⁆ := by
    have h := CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived P₂ θ.ker hC hkerP
    rwa [Subgroup.map_subtype_commutator] at h
  have hP₂P₀ : (P₂ : Subgroup E) ≤ P₀ ⊔ θ.ker := by
    intro x hx
    rw [hP₂, Subgroup.mem_comap] at hx
    obtain ⟨p, hp, hpx⟩ := hP₀surj _ hx
    have hk : p⁻¹ * x ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpx, inv_mul_cancel]
    have := Subgroup.mul_mem_sup hp hk
    rwa [mul_inv_cancel_left] at this
  have hcP₀ : c ∈ P₀ :=
    Subgroup.commutator_le_self P₀ ((commutator_sup_le hC)
      (Subgroup.commutator_mono hP₂P₀ hP₂P₀ (htrans hc)))
  exact (hP₀ker c hcP₀ hc).2.2

end Cover

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
