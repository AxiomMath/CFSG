module

public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveFullAffineTwoCore
public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveSplitting

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive

open BinarySymplecticTransvection FullAffine Orth
open scoped commutatorElement

namespace FullCoset

variable {E : Type} [AddCommGroup E]
variable {M : Type} [Group M] {R : Subgroup M} (θ : R ≃* Multiplicative ((E × ZMod 2) × ZMod 2))

variable [R.Normal]

theorem conj_mem (m : M) (x : (E × ZMod 2) × ZMod 2) : m⁻¹ * bv θ x * m ∈ R := by
  have h := (inferInstance : R.Normal).conj_mem _ (bv_mem θ x) m⁻¹
  rwa [inv_inv] at h

@[expose] noncomputable def cAct (m : M) (x : (E × ZMod 2) × ZMod 2) : (E × ZMod 2) × ZMod 2 :=
  Multiplicative.toAdd (θ ⟨m⁻¹ * bv θ x * m, conj_mem θ m x⟩)

theorem bv_cAct (m : M) (x : (E × ZMod 2) × ZMod 2) : bv θ (cAct θ m x) = m⁻¹ * bv θ x * m := by
  rw [bv, cAct, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem cAct_add (m : M) (x y : (E × ZMod 2) × ZMod 2) :
    cAct θ m (x + y) = cAct θ m x + cAct θ m y := by
  apply bv_injective θ
  rw [bv_cAct, bv_add, bv_add, bv_cAct, bv_cAct]
  group

theorem cAct_mul (m m' : M) (x : (E × ZMod 2) × ZMod 2) :
    cAct θ (m * m') x = cAct θ m' (cAct θ m x) := by
  apply bv_injective θ
  rw [bv_cAct, bv_cAct, bv_cAct]
  group

theorem cAct_one (x : (E × ZMod 2) × ZMod 2) : cAct θ 1 x = x := by
  apply bv_injective θ
  rw [bv_cAct]
  group

theorem cAct_of_mem {m : M} (hm : m ∈ R) (x : (E × ZMod 2) × ZMod 2) : cAct θ m x = x := by
  apply bv_injective θ
  rw [bv_cAct, mul_assoc, B_comm θ (bv_mem θ x) hm, inv_mul_cancel_left]

theorem cAct_inv_cAct (m : M) (x : (E × ZMod 2) × ZMod 2) : cAct θ m⁻¹ (cAct θ m x) = x := by
  rw [← cAct_mul, mul_inv_cancel, cAct_one]

variable [Module (ZMod 2) E] {b : LinearMap.BilinForm (ZMod 2) E} {Q : QuadraticForm (ZMod 2) E}

structure Hyp (hQ : QuadraticMap.polarBilin Q = b) : Prop where
  omega : ∀ (m : M) (v : E × ZMod 2), (cAct θ m (v, 1)).2 = 1
  faith : ∀ m : M, (∀ v : E × ZMod 2, cAct θ m (v, 1) = (v, 1)) → m ∈ R
  trans : ∀ v v' : E × ZMod 2, ∃ m : M, cAct θ m (v, 1) = (v', 1)
  stab : ∀ m : M, cAct θ m (0, 1) = (0, 1) →
    ∃ s : bilinIsometryGroup b, ∀ v : E × ZMod 2, cAct θ m (v, 1) = (hV hQ s v, 1)
  stab' : ∀ s : bilinIsometryGroup b,
    ∃ m : M, ∀ v : E × ZMod 2, cAct θ m (v, 1) = (hV hQ s v, 1)

variable {θ} {hQ : QuadraticMap.polarBilin Q = b}

theorem cAct_snd (hH : Hyp θ hQ) (m : M) (x : (E × ZMod 2) × ZMod 2) :
    (cAct θ m x).2 = x.2 := by
  obtain ⟨v, ε⟩ := x
  rcases zmod_two_cases ε with rfl | rfl
  · have h : ((v, 0) : (E × ZMod 2) × ZMod 2) = (v, 1) + (0, 1) :=
      Prod.ext (add_zero v).symm (show (0 : ZMod 2) = 1 + 1 from rfl)
    rw [h, cAct_add, Prod.snd_add, hH.omega, hH.omega]
    rfl
  · exact hH.omega m v

theorem cAct_zero_eq (hH : Hyp θ hQ) (m : M) (v : E × ZMod 2) :
    cAct θ m (v, 0) = ((cAct θ m (v, 0)).1, 0) :=
  Prod.ext rfl (cAct_snd hH m _)

theorem cAct_eq (hH : Hyp θ hQ) (m : M) (v : E × ZMod 2) (ε : ZMod 2) :
    cAct θ m (v, ε) = ((cAct θ m (v, 0)).1 + ε • (cAct θ m (0, 1)).1, ε) := by
  rcases zmod_two_cases ε with rfl | rfl
  · rw [zero_smul, add_zero]
    exact cAct_zero_eq hH m v
  · have h : ((v, 1) : (E × ZMod 2) × ZMod 2) = (v, 0) + (0, 1) :=
      Prod.ext (add_zero v).symm (zero_add 1).symm
    rw [h, cAct_add, one_smul]
    exact Prod.ext rfl (by rw [Prod.snd_add, cAct_snd hH, cAct_snd hH]; rfl)

@[expose] noncomputable def linAdd (m : M) : (E × ZMod 2) →+ (E × ZMod 2) :=
  AddMonoidHom.mk' (fun v => (cAct θ m (v, 0)).1) fun v w => by
    have h : ((v + w, 0) : (E × ZMod 2) × ZMod 2) = (v, 0) + (w, 0) :=
      Prod.ext rfl (add_zero 0).symm
    rw [h, cAct_add, Prod.fst_add]

omit [Module (ZMod 2) E] in
theorem linAdd_apply (m : M) (v : E × ZMod 2) : linAdd (θ := θ) m v = (cAct θ m (v, 0)).1 :=
  rfl

theorem linAdd_inv_linAdd (hH : Hyp θ hQ) (m : M) (v : E × ZMod 2) :
    linAdd (θ := θ) m⁻¹ (linAdd (θ := θ) m v) = v := by
  rw [linAdd_apply, linAdd_apply, ← cAct_zero_eq hH, cAct_inv_cAct]

@[expose] noncomputable def linEquiv (hH : Hyp θ hQ) (m : M) :
    (E × ZMod 2) ≃ₗ[ZMod 2] (E × ZMod 2) where
  toFun := linAdd m
  invFun := linAdd m⁻¹
  map_add' := map_add _
  map_smul' c v := by
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul, RingHom.id_apply, zero_smul, map_zero]
    · rw [one_smul, RingHom.id_apply, one_smul]
  left_inv := linAdd_inv_linAdd hH m
  right_inv v := by
    have h := linAdd_inv_linAdd hH m⁻¹ v
    rwa [inv_inv] at h

@[expose] noncomputable def affOf (hH : Hyp θ hQ) (m : M) : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2) :=
  tr (cAct θ m (0, 1)).1 * toAff (linEquiv hH m)

theorem affOf_apply (hH : Hyp θ hQ) (m : M) (v : E × ZMod 2) :
    affOf hH m v = (cAct θ m (v, 1)).1 := by
  change (cAct θ m (0, 1)).1 + (cAct θ m (v, 0)).1 = _
  rw [cAct_eq hH m v 1, one_smul, add_comm]

theorem cAct_one_eq (hH : Hyp θ hQ) (m : M) (v : E × ZMod 2) :
    cAct θ m (v, 1) = (affOf hH m v, 1) :=
  Prod.ext (affOf_apply hH m v).symm (hH.omega m v)

theorem affOf_mul (hH : Hyp θ hQ) (m m' : M) : affOf hH (m * m') = affOf hH m' * affOf hH m :=
  AffineEquiv.ext fun v => by
    rw [AffineEquiv.coe_mul, Function.comp_apply, affOf_apply, affOf_apply, affOf_apply,
      cAct_mul, cAct_one_eq hH m v]

theorem affOf_one (hH : Hyp θ hQ) : affOf hH (1 : M) = 1 :=
  AffineEquiv.ext fun v => by
    rw [affOf_apply, cAct_one]
    rfl

theorem affOf_inv (hH : Hyp θ hQ) (m : M) : affOf hH m⁻¹ = (affOf hH m)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← affOf_mul, mul_inv_cancel, affOf_one]

@[expose] noncomputable def phi (hH : Hyp θ hQ) : M →* ((E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) where
  toFun m := affOf hH m⁻¹
  map_one' := by rw [inv_one, affOf_one]
  map_mul' m m' := by rw [_root_.mul_inv_rev, affOf_mul]

theorem phi_apply (hH : Hyp θ hQ) (m : M) : phi hH m = affOf hH m⁻¹ :=
  rfl

theorem affOf_eq_phi_inv (hH : Hyp θ hQ) (m : M) : affOf hH m = phi hH m⁻¹ := by
  rw [phi_apply, inv_inv]

theorem mem_ker_phi (hH : Hyp θ hQ) {m : M} : m ∈ (phi hH).ker ↔ m ∈ R := by
  rw [MonoidHom.mem_ker, phi_apply]
  constructor
  · intro h
    have h1 : m⁻¹ ∈ R := hH.faith _ fun v => by
      rw [cAct_one_eq hH, h]
      rfl
    simpa using h1
  · intro h
    refine AffineEquiv.ext fun v => ?_
    rw [affOf_apply, cAct_of_mem θ (R.inv_mem h)]
    rfl

theorem mem_R_of_centralizes (hH : Hyp θ hQ) {m : M} (hm : ∀ r ∈ R, m * r = r * m) : m ∈ R :=
  hH.faith m fun v => by
    apply bv_injective θ
    rw [bv_cAct, mul_assoc, ← hm _ (bv_mem θ _), inv_mul_cancel_left]

theorem affOf_mem_range (hH : Hyp θ hQ) (m : M) : affOf hH m ∈ (phi hH).range :=
  ⟨m⁻¹, by rw [phi_apply, inv_inv]⟩

theorem affOf_eq_hEquiv_of (hH : Hyp θ hQ) {m : M} {s : bilinIsometryGroup b}
    (hm : ∀ v : E × ZMod 2, cAct θ m (v, 1) = (hV hQ s v, 1)) :
    affOf hH m = toAff (hEquiv hQ s) :=
  AffineEquiv.ext fun v => by
    rw [affOf_apply, hm]
    rfl

theorem range_hyp [FiniteDimensional (ZMod 2) E] (hnd : b.Nondegenerate) (hH : Hyp θ hQ) :
    AffHyp Q (phi hH).range := by
  refine ⟨fun x y => ?_, fun g => ⟨?_, ?_⟩⟩
  · obtain ⟨m, hm⟩ := hH.trans x y
    refine ⟨affOf hH m, affOf_mem_range hH m, ?_⟩
    rw [affOf_apply, hm]
  · rintro ⟨m, hm⟩
    rw [phi_apply] at hm
    have h0 : cAct θ m⁻¹ (0, 1) = (0, 1) := by
      rw [cAct_one_eq hH, hm]
      exact Prod.ext (map_zero g) rfl
    obtain ⟨s, hs⟩ := hH.stab _ h0
    have h1 : g = hEquiv hQ s := LinearEquiv.ext fun v => by
      have h2 := congrArg (fun k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2) => k v)
        ((affOf_eq_hEquiv_of hH hs).symm.trans hm)
      exact h2.symm
    rw [h1]
    exact hEquiv_mem hQ s
  · intro hg
    obtain ⟨s, rfl⟩ := exists_hEquiv_eq hnd hQ hg
    obtain ⟨m, hm⟩ := hH.stab' s
    rw [← affOf_eq_hEquiv_of hH hm]
    exact affOf_mem_range hH m

structure Core (hH : Hyp θ hQ) (hb : b.IsAlt) (lam : ZMod 2) : Prop where
  pcore : CFSG.Assembly.pCoreOf 2 (phi hH).range = twoCoreGroup hb lam
  abelP : CFSG.Assembly.IsElemAbelian 2 (twoCoreGroup hb lam)
  cardP : Nat.card (twoCoreGroup hb lam) = 32
  regular : ∀ x y : E × ZMod 2, ∃! p, p ∈ twoCoreGroup hb lam ∧ p x = y
  PleK : twoCoreGroup hb lam ≤ (phi hH).range
  normal : ∀ k ∈ (phi hH).range, ∀ p ∈ twoCoreGroup hb lam, k * p * k⁻¹ ∈ twoCoreGroup hb lam
  prod : ∀ k ∈ (phi hH).range, ∃ p ∈ twoCoreGroup hb lam,
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm Q), k = p * g.toAffineEquiv
  linr : ∀ k ∈ (phi hH).range, k.linear rV = rV
  trP : tr rV ∈ twoCoreGroup hb lam

theorem exists_core [FiniteDimensional (ZMod 2) E] (hE : Module.finrank (ZMod 2) E = 4)
    (hb : b.IsAlt) (hnd : b.Nondegenerate) (hH : Hyp θ hQ) : ∃ lam : ZMod 2, Core hH hb lam := by
  obtain ⟨-, -, -, lam, h1, -, h3, h4, h5, h6, h7, -, h9, h10, -, -, -, -, -, h16, -, -⟩ :=
    binary_odd_quadratic_five_full_affine_two_core_and_actions hE hb hnd hQ (phi hH).range
      (range_hyp hnd hH).trans (range_hyp hnd hH).stab
  exact ⟨lam, ⟨h1, h3, h4, h5, h6, h7, h9, h10, h16⟩⟩

omit [R.Normal] [Module (ZMod 2) E] in
theorem card_R_of_equiv [Finite E] (hE : Nat.card E = 16)
    (e : R ≃* Multiplicative ((E × ZMod 2) × ZMod 2)) : Nat.card R = 64 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_prod,
    Nat.card_prod, hE, Nat.card_zmod]

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

@[expose] noncomputable def dSub (hH : Hyp θ hQ) (hb : b.IsAlt) (lam : ZMod 2) : Subgroup M :=
  (twoCoreGroup hb lam).comap (phi hH)

abbrev uSub : Subgroup ((E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) :=
  Subgroup.zpowers (tr rV)

@[expose] noncomputable def fSub (hH : Hyp θ hQ) : Subgroup M :=
  uSub.comap (phi hH)

@[expose] noncomputable def lab (hH : Hyp θ hQ) (m : M) : E × ZMod 2 :=
  affOf hH m 0

theorem tr_rV_inv : (tr (rV : E × ZMod 2))⁻¹ = tr rV :=
  inv_eq_of_mul_eq_one_left tr_rV_mul_self

theorem mem_uSub_iff {k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)} :
    k ∈ (uSub : Subgroup ((E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2))) ↔ k = 1 ∨ k = tr rV := by
  constructor
  · rintro ⟨n, rfl⟩
    simp only
    induction n using Int.induction_on with
    | zero => exact Or.inl (zpow_zero _)
    | succ n ih =>
      rw [zpow_add_one]
      rcases ih with h | h <;> rw [h]
      · exact Or.inr (one_mul _)
      · exact Or.inl tr_rV_mul_self
    | pred n ih =>
      rw [zpow_sub_one, tr_rV_inv]
      rcases ih with h | h <;> rw [h]
      · exact Or.inr (one_mul _)
      · exact Or.inl tr_rV_mul_self
  · rintro (rfl | rfl)
    · exact (uSub : Subgroup _).one_mem
    · exact Subgroup.mem_zpowers _

section Core

variable {hH : Hyp θ hQ} {hb : b.IsAlt} {lam : ZMod 2}

theorem phi_eq_inv (m : M) : phi hH m = (affOf hH m)⁻¹ := by
  rw [phi_apply, affOf_inv]

theorem mem_dSub {m : M} : m ∈ dSub hH hb lam ↔ affOf hH m ∈ twoCoreGroup hb lam := by
  rw [dSub, Subgroup.mem_comap, phi_eq_inv]
  exact ⟨fun h => by simpa using (twoCoreGroup hb lam).inv_mem h,
    (twoCoreGroup hb lam).inv_mem⟩

theorem mem_fSub {m : M} : m ∈ fSub hH ↔ affOf hH m ∈ (uSub : Subgroup _) := by
  rw [fSub, Subgroup.mem_comap, phi_eq_inv]
  exact ⟨fun h => by simpa using (uSub : Subgroup _).inv_mem h, (uSub : Subgroup _).inv_mem⟩

theorem ker_phi : (phi hH).ker = R := by
  ext m
  exact mem_ker_phi hH

theorem affOf_eq_one_iff {m : M} : affOf hH m = 1 ↔ m ∈ R := by
  rw [affOf_eq_phi_inv, ← MonoidHom.mem_ker, mem_ker_phi]
  exact ⟨fun h => by simpa using R.inv_mem h, R.inv_mem⟩

theorem affOf_eq {m : M} (hm : m ∈ dSub hH hb lam) :
    affOf hH m = twoCoreMap b lam (lab hH m) := by
  obtain ⟨A, hA⟩ := (mem_twoCoreGroup hb lam).1 (mem_dSub.mp hm)
  rw [← hA, lab, ← hA, twoCoreMap_apply]
  simp

theorem R_le_fSub : R ≤ fSub hH := fun r hr => mem_fSub.mpr (by
  rw [affOf_eq_one_iff.mpr hr]
  exact (uSub : Subgroup _).one_mem)

theorem lab_mul_of_mem {m m' : M} (hm' : m' ∈ dSub hH hb lam) :
    lab hH (m * m') = twoCoreMap b lam (lab hH m') (lab hH m) := by
  rw [lab, affOf_mul, AffineEquiv.coe_mul, Function.comp_apply, ← lab, affOf_eq hm']

theorem cAct_of_mem_dSub {m : M} (hm : m ∈ dSub hH hb lam) (v : E × ZMod 2) (ε : ZMod 2) :
    cAct θ m (v, ε) = (v + (lam * b (lab hH m).1 v.1) • rV + ε • lab hH m, ε) := by
  have h2 : (cAct θ m (0, 1)).1 = lab hH m := by rw [lab, affOf_apply]
  have h1 : v + lab hH m + (lam * b (lab hH m).1 v.1) • rV = (cAct θ m (v, 0)).1 + lab hH m := by
    have h := affOf_apply hH m v
    rw [affOf_eq hm, twoCoreMap_apply, cAct_eq hH m v 1, one_smul, h2] at h
    exact h
  have h3 : (cAct θ m (v, 0)).1 = v + (lam * b (lab hH m).1 v.1) • rV :=
    add_right_cancel (h1.symm.trans (by abel))
  rw [cAct_eq hH m v ε, h2, h3]

theorem lab_one : lab hH (1 : M) = 0 := by
  rw [lab, affOf_one]
  rfl

theorem cAct_z (m : M) : cAct θ m (0, 1) = (lab hH m, 1) := by
  rw [cAct_one_eq hH]
  rfl

theorem mem_centralizer_z_iff {m : M} :
    m ∈ Subgroup.centralizer {zz θ} ↔ lab hH m = 0 := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : cAct θ m (0, 1) = (0, 1) := by
      apply bv_injective θ
      rw [bv_cAct, ← zz, mul_assoc, ← h, inv_mul_cancel_left]
    rw [cAct_z] at h1
    exact congrArg Prod.fst h1
  · intro h
    have h1 := bv_cAct θ m (0, 1)
    rw [cAct_z (hH := hH) m, h, ← zz] at h1
    calc m * zz θ = m * (m⁻¹ * zz θ * m) := by rw [← h1]
      _ = zz θ * m := by group

theorem comm_bv_dSub {d : M} (hd : d ∈ dSub hH hb lam) (v : E × ZMod 2) (ε : ZMod 2) :
    (bv θ (v, ε))⁻¹ * (d⁻¹ * bv θ (v, ε) * d) =
      bv θ ((lam * b (lab hH d).1 v.1) • rV + ε • lab hH d, 0) := by
  rw [bv_inv, ← bv_cAct, cAct_of_mem_dSub hd, ← bv_add]
  congr 1
  refine Prod.ext ?_ (zmod2_add_self ε)
  change v + (v + _ + _) = _
  rw [← add_assoc, ← add_assoc, add_self_eq_zero_zmod_two, zero_add]

theorem mul_comm_bv_of_mem_dSub {d : M} (hd : d ∈ dSub hH hb lam) {v : E × ZMod 2} {ε : ZMod 2}
    (h : (lam * b (lab hH d).1 v.1) • rV + ε • lab hH d = 0) :
    d * bv θ (v, ε) = bv θ (v, ε) * d := by
  have h1 := bv_cAct θ d (v, ε)
  rw [cAct_of_mem_dSub hd, add_assoc, h, add_zero] at h1
  calc d * bv θ (v, ε) = d * (d⁻¹ * bv θ (v, ε) * d) := by rw [← h1]
    _ = bv θ (v, ε) * d := by group

theorem comm_z_dSub {d : M} (hd : d ∈ dSub hH hb lam) :
    (zz θ)⁻¹ * (d⁻¹ * zz θ * d) = bv θ (lab hH d, 0) := by
  rw [zz, comm_bv_dSub hd]
  simp only [Prod.fst_zero, map_zero, mul_zero, zero_smul, zero_add, one_smul]

theorem lab_mul_dSub {d d' : M} (hd' : d' ∈ dSub hH hb lam) :
    lab hH (d * d') = lab hH d + lab hH d' + (lam * b (lab hH d').1 (lab hH d).1) • rV := by
  rw [lab_mul_of_mem hd', twoCoreMap_apply, add_comm (lab hH d)]

theorem tr_rV_ne_one : tr (rV : E × ZMod 2) ≠ 1 := by
  intro h
  have h1 := congrArg (fun k : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2) => k 0) h
  simp only [tr_apply, add_zero, AffineEquiv.coe_one, id_eq] at h1
  have h2 := congrArg Prod.snd h1
  exact absurd h2 (by simp [rV])

theorem card_uSub : Nat.card (uSub : Subgroup ((E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2))) = 2 := by
  rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact tr_rV_mul_self) tr_rV_ne_one]

theorem eq_zero_of_smul_rV {ε : ZMod 2} (h : ε • (rV : E × ZMod 2) = 0) : ε = 0 := by
  have h1 := congrArg Prod.snd h
  simpa [rV] using h1

theorem commutatorElement_eq (x d : M) : ⁅x, d⁆ = x⁻¹⁻¹ * ((d⁻¹)⁻¹ * x⁻¹ * d⁻¹) := by
  rw [commutatorElement_def]
  group

theorem comm_bv_dSub' {d : M} (hd : d ∈ dSub hH hb lam) (v : E × ZMod 2) (ε : ZMod 2) :
    ⁅bv θ (v, ε), d⁆ = bv θ ((lam * b (lab hH d⁻¹).1 v.1) • rV + ε • lab hH d⁻¹, 0) := by
  rw [commutatorElement_eq, bv_inv, comm_bv_dSub ((dSub hH hb lam).inv_mem hd)]

variable (hc : Core hH hb lam)
include hc

theorem regular_eq {p p' : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)} (hp : p ∈ twoCoreGroup hb lam)
    (hp' : p' ∈ twoCoreGroup hb lam) (h : p 0 = p' 0) : p = p' :=
  (hc.regular 0 (p 0)).unique ⟨hp, rfl⟩ ⟨hp', h.symm⟩

theorem lab_eq_iff {m m' : M} (hm : m ∈ dSub hH hb lam) (hm' : m' ∈ dSub hH hb lam) :
    lab hH m = lab hH m' ↔ m⁻¹ * m' ∈ R := by
  rw [← affOf_eq_one_iff (hH := hH), affOf_mul, affOf_inv]
  constructor
  · intro h
    rw [regular_eq hc (mem_dSub.mp hm') (mem_dSub.mp hm) h.symm, mul_inv_cancel]
  · intro h
    have h1 : affOf hH m' = affOf hH m := by
      rw [← mul_inv_eq_one]
      exact h
    rw [lab, lab, h1]

theorem exists_lab (v : E × ZMod 2) : ∃ m ∈ dSub hH hb lam, lab hH m = v := by
  obtain ⟨m, hm⟩ := hc.PleK ⟨v, rfl⟩
  refine ⟨m⁻¹, mem_dSub.mpr ?_, ?_⟩
  · rw [affOf_eq_phi_inv, inv_inv, hm]
    exact ⟨v, rfl⟩
  · rw [lab, affOf_eq_phi_inv, inv_inv, hm, twoCoreMap_apply]
    simp

theorem uSub_le_twoCoreGroup : (uSub : Subgroup ((E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2))) ≤
    twoCoreGroup hb lam := by
  intro k hk
  rcases mem_uSub_iff.1 hk with rfl | rfl
  · exact (twoCoreGroup hb lam).one_mem
  · exact hc.trP

theorem fSub_le_dSub : fSub hH ≤ dSub hH hb lam := fun _ hm =>
  mem_dSub.mpr (uSub_le_twoCoreGroup hc (mem_fSub.mp hm))

theorem R_le_dSub : R ≤ dSub hH hb lam :=
  R_le_fSub.trans (fSub_le_dSub hc)

theorem dSub_normal : (dSub hH hb lam).Normal :=
  ⟨fun d hd m => by
    rw [dSub, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hc.normal _ ⟨m, rfl⟩ _ hd⟩

theorem fSub_normal : (fSub hH).Normal :=
  ⟨fun d hd m => by
    rw [fSub, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    have hk : phi hH m ∈ (phi hH).range := ⟨m, rfl⟩
    rcases mem_uSub_iff.1 hd with h | h
    · rw [h, mul_one, mul_inv_cancel]
      exact (uSub : Subgroup _).one_mem
    · rw [h, conj_tr, hc.linr _ hk]
      exact Subgroup.mem_zpowers _⟩

theorem card_dSub [Finite E] (hE : Nat.card E = 16) : Nat.card (dSub hH hb lam) = 2048 := by
  rw [dSub, card_comap_eq (phi hH) hc.PleK, ker_phi, card_R_of_equiv hE θ, hc.cardP]

theorem card_fSub [Finite E] (hE : Nat.card E = 16) : Nat.card (fSub hH) = 128 := by
  rw [fSub, card_comap_eq (phi hH) ((uSub_le_twoCoreGroup hc).trans hc.PleK), ker_phi,
    card_R_of_equiv hE θ, card_uSub]

theorem mem_fSub_iff {m : M} :
    m ∈ fSub hH ↔ m ∈ dSub hH hb lam ∧ (lab hH m).1 = 0 := by
  constructor
  · intro hm
    refine ⟨fSub_le_dSub hc hm, ?_⟩
    rcases mem_uSub_iff.1 (mem_fSub.mp hm) with h | h
    · rw [lab, h]
      rfl
    · rw [lab, h, tr_apply, add_zero]
      rfl
  · rintro ⟨hm, h0⟩
    refine mem_fSub.mpr (mem_uSub_iff.2 ?_)
    have hlab : lab hH m = (lab hH m).2 • rV := Prod.ext (by simp [rV, h0]) (by simp [rV])
    have h1 : affOf hH m = tr (lab hH m) := AffineEquiv.ext fun v => by
      rw [affOf_eq hm, twoCoreMap_apply, h0, map_zero, LinearMap.zero_apply, mul_zero,
        zero_smul, add_zero, tr_apply, add_comm]
    rw [h1, hlab]
    rcases zmod_two_cases (lab hH m).2 with h2 | h2 <;> rw [h2]
    · left
      rw [zero_smul, tr_zero]
    · right
      rw [one_smul]

theorem dSub_inf_centralizer : dSub hH hb lam ⊓ Subgroup.centralizer {zz θ} = R := by
  ext m
  rw [Subgroup.mem_inf, mem_centralizer_z_iff (hH := hH)]
  constructor
  · rintro ⟨hm, h0⟩
    have h := (lab_eq_iff hc hm (dSub hH hb lam).one_mem).mp (by rw [h0, lab_one])
    simpa using h
  · intro hm
    refine ⟨R_le_dSub hc hm, ?_⟩
    rw [lab, affOf_eq_one_iff.mpr hm]
    rfl

theorem exists_dSub_affOf (p : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2))
    (hp : p ∈ twoCoreGroup hb lam) : ∃ d ∈ dSub hH hb lam, affOf hH d = p := by
  obtain ⟨d, hd, hd0⟩ := exists_lab hc (p 0)
  exact ⟨d, hd, regular_eq hc (mem_dSub.mp hd) hp hd0⟩

theorem exists_dSub_mul_centralizer (m : M) :
    ∃ d ∈ dSub hH hb lam, ∃ c ∈ Subgroup.centralizer {zz θ}, m = d * c := by
  obtain ⟨p, hp, g, -, hpg⟩ := hc.prod _ (affOf_mem_range hH m)
  obtain ⟨d, hd, hdp⟩ := exists_dSub_affOf hc p hp
  have hc0 : lab hH (m * d⁻¹) = 0 := by
    rw [lab, affOf_mul, affOf_inv, hdp, hpg, inv_mul_cancel_left]
    exact map_zero g
  refine ⟨(m * d⁻¹) * d * (m * d⁻¹)⁻¹, (dSub_normal hc).conj_mem d hd _, m * d⁻¹,
    mem_centralizer_z_iff.mpr hc0, ?_⟩
  group

theorem cAct_of_mem_fSub {f : M} (hf : f ∈ fSub hH) (v : E × ZMod 2) (ε : ZMod 2) :
    cAct θ f (v, ε) = (v + ε • lab hH f, ε) := by
  obtain ⟨hfD, hf0⟩ := (mem_fSub_iff hc).mp hf
  rw [cAct_of_mem_dSub hfD, hf0, map_zero, LinearMap.zero_apply, mul_zero, zero_smul, add_zero]

theorem exists_fSub_rV : ∃ f ∈ fSub hH, lab hH f = rV := by
  obtain ⟨d, hd, hd0⟩ := exists_lab hc rV
  exact ⟨d, (mem_fSub_iff hc).mpr ⟨hd, by rw [hd0]; rfl⟩, hd0⟩

theorem mem_center_fSub_iff (x : M) :
    (∃ y : fSub hH, y ∈ Subgroup.center (fSub hH) ∧ (y : M) = x) ↔ x ∈ subA θ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hR : (y : M) ∈ R := mem_R_of_centralizes hH fun r hr => by
      have h := Subgroup.mem_center_iff.mp hy ⟨r, R_le_fSub hr⟩
      exact (congrArg Subtype.val h).symm
    obtain ⟨⟨v, ε⟩, hvε⟩ := exists_bv_eq θ hR
    obtain ⟨f, hf, hf0⟩ := exists_fSub_rV hc
    have h1 := Subgroup.mem_center_iff.mp hy ⟨f, hf⟩
    have h2 : cAct θ f (v, ε) = (v, ε) := by
      apply bv_injective θ
      rw [bv_cAct, hvε]
      have h3 := congrArg Subtype.val h1
      change f * (y : M) = (y : M) * f at h3
      rw [mul_assoc, ← h3, inv_mul_cancel_left]
    rw [cAct_of_mem_fSub hc hf, hf0] at h2
    have h4 : ε • (rV : E × ZMod 2) = 0 := by
      have h5 := congrArg Prod.fst h2
      exact add_eq_left.mp h5
    rw [eq_zero_of_smul_rV h4] at hvε
    exact ⟨v, hvε⟩
  · rintro ⟨v, rfl⟩
    refine ⟨⟨bv θ (v, 0), R_le_fSub (bv_mem θ _)⟩, Subgroup.mem_center_iff.mpr fun f => ?_, rfl⟩
    apply Subtype.ext
    change (f : M) * bv θ (v, 0) = bv θ (v, 0) * f
    have hfD := fSub_le_dSub hc f.2
    refine mul_comm_bv_of_mem_dSub hfD ?_
    rw [((mem_fSub_iff hc).mp f.2).2, map_zero, LinearMap.zero_apply, mul_zero, zero_smul,
      zero_smul, add_zero]

theorem commutator_R_dSub : ⁅R, dSub hH hb lam⁆ = subA θ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro r hr d hd
    obtain ⟨⟨v, ε⟩, rfl⟩ := exists_bv_eq θ hr
    rw [comm_bv_dSub' hd]
    exact ⟨_, rfl⟩
  · rintro _ ⟨v, rfl⟩
    obtain ⟨d, hd, hdv⟩ := exists_lab hc v
    have h := comm_bv_dSub' (θ := θ) ((dSub hH hb lam).inv_mem hd) 0 1
    rw [inv_inv, hdv] at h
    simp only [Prod.fst_zero, map_zero, mul_zero, zero_smul, zero_add, one_smul] at h
    rw [← h]
    exact Subgroup.commutator_mem_commutator (bv_mem θ _) ((dSub hH hb lam).inv_mem hd)

theorem mem_center_dSub_iff [FiniteDimensional (ZMod 2) E] (x : M) :
    (∃ y : dSub hH hb lam, y ∈ Subgroup.center (dSub hH hb lam) ∧ (y : M) = x) ↔
      ∃ v : E × ZMod 2, (∀ a : E, lam * b a v.1 = 0) ∧ x = bv θ (v, 0) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hR : (y : M) ∈ R := mem_R_of_centralizes hH fun r hr => by
      have h := Subgroup.mem_center_iff.mp hy ⟨r, R_le_dSub hc hr⟩
      exact (congrArg Subtype.val h).symm
    obtain ⟨⟨v, ε⟩, hvε⟩ := exists_bv_eq θ hR
    have hfix : ∀ d ∈ dSub hH hb lam, cAct θ d (v, ε) = (v, ε) := fun d hd => by
      apply bv_injective θ
      rw [bv_cAct, hvε]
      have h3 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨d, hd⟩)
      change d * (y : M) = (y : M) * d at h3
      rw [mul_assoc, ← h3, inv_mul_cancel_left]
    have hcoord : ∀ d ∈ dSub hH hb lam,
        (lam * b (lab hH d).1 v.1) • rV + ε • lab hH d = 0 := fun d hd => by
      have h := congrArg Prod.fst (hfix d hd)
      rw [cAct_of_mem_dSub hd] at h
      change v + _ + _ = v at h
      rw [add_assoc] at h
      exact add_eq_left.mp h
    obtain ⟨f, hf, hf0⟩ := exists_fSub_rV hc
    have hε : ε = 0 := by
      have h := hcoord f (fSub_le_dSub hc hf)
      rw [hf0] at h
      simp only [rV, map_zero, LinearMap.zero_apply, mul_zero, zero_smul, zero_add] at h
      exact eq_zero_of_smul_rV h
    subst hε
    refine ⟨v, fun a => ?_, hvε.symm⟩
    obtain ⟨d, hd, hda⟩ := exists_lab hc (a, 0)
    have h := hcoord d hd
    rw [zero_smul, add_zero, hda] at h
    exact eq_zero_of_smul_rV h
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨bv θ (v, 0), R_le_dSub hc (bv_mem θ _)⟩, Subgroup.mem_center_iff.mpr fun d => ?_,
      rfl⟩
    apply Subtype.ext
    change (d : M) * bv θ (v, 0) = bv θ (v, 0) * d
    exact mul_comm_bv_of_mem_dSub d.2 (by rw [hv, zero_smul, zero_smul, add_zero])

omit hc in
theorem commutator_subI_dSub : ⁅subI θ, dSub hH hb lam⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rintro _ ⟨c, rfl⟩ d hd
  exact mul_comm_bv_of_mem_dSub hd (v := c • rV) (ε := 0) (by
    simp only [Prod.smul_fst, rV, smul_zero, map_zero, mul_zero, zero_smul, add_zero])

omit hc in
theorem commutator_subA_dSub_of_zero (hl : lam = 0) : ⁅subA θ, dSub hH hb lam⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rintro _ ⟨v, rfl⟩ d hd
  exact mul_comm_bv_of_mem_dSub hd (v := v) (ε := 0) (by rw [hl, zero_mul, zero_smul, zero_smul,
    add_zero])

theorem commutator_subA_dSub_of_one (hnd : b.Nondegenerate) (hex : ∃ w : E, w ≠ 0)
    (hl : lam = 1) :
    ⁅subA θ, dSub hH hb lam⁆ = subI θ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    rintro _ ⟨v, rfl⟩ d hd
    rw [comm_bv_dSub' hd, zero_smul, add_zero]
    exact ⟨_, rfl⟩
  · rintro _ ⟨c, rfl⟩
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul, Prod.mk_zero_zero, bv_zero]
      exact Subgroup.one_mem _
    ·
      obtain ⟨w, hw⟩ := hex
      obtain ⟨u, hu⟩ := exists_apply_eq_one hnd hw
      obtain ⟨d, hd, hdu⟩ := exists_lab hc (u, 0)
      have h := comm_bv_dSub' (θ := θ) ((dSub hH hb lam).inv_mem hd) (w, 0) 0
      rw [inv_inv, hdu, zero_smul, add_zero, hl, one_mul] at h
      dsimp only at h
      rw [hu] at h
      rw [← h]
      exact Subgroup.commutator_mem_commutator ⟨(w, 0), rfl⟩ ((dSub hH hb lam).inv_mem hd)

theorem comm_subA_mem_center [FiniteDimensional (ZMod 2) E] {a : M} (ha : a ∈ subA θ) {d : M}
    (hd : d ∈ dSub hH hb lam) :
    a⁻¹ * (d⁻¹ * a * d) ∈ (Subgroup.center (dSub hH hb lam)).map (dSub hH hb lam).subtype := by
  obtain ⟨v, rfl⟩ := ha
  rw [comm_bv_dSub hd, zero_smul, add_zero]
  obtain ⟨y, hy, hyx⟩ := (mem_center_dSub_iff hc _).mpr
    ⟨(lam * b (lab hH d).1 v.1) • rV, fun a' => by simp [rV], rfl⟩
  exact ⟨y, hy, hyx⟩

theorem sq_mem_R {d : M} (hd : d ∈ dSub hH hb lam) : d ^ 2 ∈ R := by
  rw [← mem_ker_phi hH, MonoidHom.mem_ker, map_pow]
  exact hc.abelP.2 _ hd

theorem comm_mem_R {d d' : M} (hd : d ∈ dSub hH hb lam) (hd' : d' ∈ dSub hH hb lam) :
    ⁅d, d'⁆ ∈ R := by
  rw [← mem_ker_phi hH, MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact congrArg Subtype.val (hc.abelP.1.is_comm.comm ⟨_, hd⟩ ⟨_, hd'⟩)

theorem relIndex_R_dSub [Finite E] (hE : Nat.card E = 16) : R.relIndex (dSub hH hb lam) = 32 := by
  have h := Subgroup.relIndex_mul_card R (dSub hH hb lam)
  rw [inf_of_le_left (R_le_dSub hc), card_R_of_equiv hE θ, card_dSub hc hE] at h
  omega

theorem relIndex_R_fSub [Finite E] (hE : Nat.card E = 16) : R.relIndex (fSub hH) = 2 := by
  have h := Subgroup.relIndex_mul_card R (fSub hH)
  rw [inf_of_le_left R_le_fSub, card_R_of_equiv hE θ, card_fSub hc hE] at h
  omega

theorem relIndex_fSub_dSub [Finite E] (hE : Nat.card E = 16) :
    (fSub hH).relIndex (dSub hH hb lam) = 16 := by
  have h := Subgroup.relIndex_mul_card (fSub hH) (dSub hH hb lam)
  rw [inf_of_le_left (fSub_le_dSub hc), card_fSub hc hE, card_dSub hc hE] at h
  omega

theorem pCore_eq_dSub [Finite E] (hE : Nat.card E = 16) :
    CFSG.Assembly.pCore 2 M = dSub hH hb lam := by
  apply le_antisymm
  · rw [CFSG.pCore_eq_iSup]
    refine iSup_le fun N => iSup_le fun hN => iSup_le fun hNp => ?_
    let f : M →* (phi hH).range := (phi hH).rangeRestrict
    have hf : Function.Surjective f := MonoidHom.rangeRestrict_surjective _
    have hle : N.map f ≤ CFSG.Assembly.pCore 2 (phi hH).range :=
      le_sSup ⟨hN.map f hf, hNp.map f⟩
    intro n hn
    have h2 : ((f n : (phi hH).range) : (E × ZMod 2) ≃ᵃ[ZMod 2] (E × ZMod 2)) ∈
        CFSG.Assembly.pCoreOf 2 (phi hH).range := ⟨f n, hle ⟨n, hn, rfl⟩, rfl⟩
    rw [hc.pcore] at h2
    exact h2
  · rw [CFSG.pCore_eq_iSup]
    refine le_iSup_of_le (dSub hH hb lam) (le_iSup_of_le (dSub_normal hc)
      (le_iSup_of_le ?_ le_rfl))
    exact IsPGroup.of_card (n := 11) (by rw [card_dSub hc hE]; norm_num)

omit hc in
theorem subA_normal (hH : Hyp θ hQ) : (subA θ).Normal :=
  ⟨fun _ ⟨v, hv⟩ g => ⟨(cAct θ g⁻¹ (v, 0)).1, by
    rw [← hv, ← cAct_zero_eq hH, bv_cAct, inv_inv]⟩⟩

theorem subI_le_center : subI θ ≤ Subgroup.center M := by
  rintro _ ⟨c, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro m
  have hlin : (affOf hH m).linear rV = rV := hc.linr _ (affOf_mem_range hH m)
  have h1 : cAct θ m (c • rV, 0) = (c • rV, 0) := by
    rw [cAct_zero_eq hH]
    refine Prod.ext ?_ rfl
    change linEquiv hH m (c • rV) = c • rV
    have h2 : (affOf hH m).linear = linEquiv hH m := by
      change (tr (cAct θ m (0, 1)).1).linear * (toAff (linEquiv hH m)).linear = linEquiv hH m
      rw [show (tr (cAct θ m (0, 1)).1).linear = 1 from
        AffineEquiv.linear_constVAdd (ZMod 2) _ _, one_mul]
      rfl
    rw [map_smul, ← h2, hlin]
  have h3 := bv_cAct θ m (c • rV, 0)
  rw [h1] at h3
  calc m * bv θ (c • rV, 0) = m * (m⁻¹ * bv θ (c • rV, 0) * m) := by rw [← h3]
    _ = bv θ (c • rV, 0) * m := by group

omit hc in
theorem lab_inv_dSub {d : M} (hd : d ∈ dSub hH hb lam) (hd1 : (lab hH d).1 = 0) :
    lab hH d⁻¹ = lab hH d := by
  have h := lab_mul_dSub (hH := hH) (d := d) (d' := d⁻¹) ((dSub hH hb lam).inv_mem hd)
  rw [mul_inv_cancel, lab_one, hd1, map_zero, mul_zero, zero_smul, add_zero] at h
  exact (eq_of_add_eq_zero_zmod2 h.symm).symm

theorem sq_mem_subI [FiniteDimensional (ZMod 2) E] (hnd : b.Nondegenerate) {f : M}
    (hf : f ∈ fSub hH) : f ^ 2 ∈ subI θ := by
  by_cases hfR : f ∈ R
  · rw [sq_eq_one_of_mem θ hfR]
    exact (subI θ).one_mem
  obtain ⟨hfD, hf1⟩ := (mem_fSub_iff hc).mp hf
  have hfr : lab hH f = rV := by
    have hne : lab hH f ≠ 0 := fun h => hfR (by
      have h1 := (lab_eq_iff hc hfD (dSub hH hb lam).one_mem).mp (by rw [h, lab_one])
      simpa using h1)
    refine Prod.ext (by rw [hf1]; rfl) ?_
    rcases zmod_two_cases (lab hH f).2 with h2 | h2
    · exact absurd (Prod.ext hf1 h2) hne
    · rw [h2]
      rfl
  obtain ⟨⟨w, ε⟩, hwε⟩ := exists_bv_eq θ (sq_mem_R hc hfD)
  have hε : ε = 0 := by
    have h1 : cAct θ f (w, ε) = (w, ε) := by
      apply bv_injective θ
      rw [bv_cAct, hwε]
      group
    rw [cAct_of_mem_fSub hc hf, hfr] at h1
    exact eq_zero_of_smul_rV (add_eq_left.mp (congrArg Prod.fst h1))
  subst hε
  have hfix : ∀ s : bilinIsometryGroup b, sE s w.1 = w.1 := by
    intro s
    obtain ⟨m, hm⟩ := hH.stab' s
    have hm0 : lab hH m⁻¹ = 0 := by
      have h0 : cAct θ m (0, 1) = (0, 1) := by
        rw [hm]
        exact Prod.ext (map_zero _) rfl
      have h1 : cAct θ m⁻¹ (0, 1) = (0, 1) := by
        rw [← h0, cAct_inv_cAct, h0]
      rw [cAct_z (hH := hH)] at h1
      exact congrArg Prod.fst h1
    have hlab : lab hH (m⁻¹ * f * m) = lab hH f := by
      have h1 : cAct θ (m⁻¹ * f * m) (0, 1) = (rV, 1) := by
        rw [cAct_mul, cAct_mul, cAct_z (hH := hH), hm0, cAct_z (hH := hH), hfr, hm,
          hV_eq_self hQ s (by simp [rV])]
      rw [cAct_z (hH := hH)] at h1
      rw [hfr]
      exact congrArg Prod.fst h1
    have hconjD : m⁻¹ * f * m ∈ dSub hH hb lam := by
      have h := (dSub_normal hc).conj_mem f hfD m⁻¹
      rwa [inv_inv] at h
    obtain ⟨⟨y, δ⟩, hyδ⟩ := exists_bv_eq θ ((lab_eq_iff hc hfD hconjD).mp hlab.symm)
    have hfx : m⁻¹ * f * m = f * bv θ (y, δ) := by
      rw [hyδ]
      group
    have h1 : (m⁻¹ * f * m) ^ 2 = bv θ (hV hQ s w, 0) := by
      have h2 : cAct θ m (w, 0) = (hV hQ s w, 0) := by
        have h3 : ((w, 0) : (E × ZMod 2) × ZMod 2) = (w, 1) + (0, 1) :=
          Prod.ext (add_zero w).symm (by change (0 : ZMod 2) = 1 + 1; decide)
        rw [h3, cAct_add, hm, hm]
        exact Prod.ext (by simp [map_zero]) (by change (1 : ZMod 2) + 1 = 0; decide)
      rw [← h2, bv_cAct, hwε, sq, sq]
      group
    have h4 : (f * bv θ (y, δ)) ^ 2 = bv θ (w + δ • rV, 0) := by
      have h5 : f⁻¹ * bv θ (y, δ) * f = bv θ (y + δ • rV, δ) := by
        rw [← bv_cAct, cAct_of_mem_fSub hc hf, hfr]
      have h6 : (f * bv θ (y, δ)) ^ 2 = f ^ 2 * ((f⁻¹ * bv θ (y, δ) * f) * bv θ (y, δ)) := by
        rw [sq, sq]
        group
      rw [h6, h5, ← hwε, ← bv_add, ← bv_add]
      congr 1
      refine Prod.ext ?_ (by simp [zmod2_add_self])
      change w + (y + δ • rV + y) = w + δ • rV
      rw [add_right_comm y, add_self_eq_zero_zmod_two, zero_add]
    rw [hfx, h4] at h1
    have h7 := congrArg Prod.fst (congrArg Prod.fst (bv_injective θ h1))
    simp only [Prod.fst_add, Prod.smul_fst, rV, smul_zero, add_zero] at h7
    rw [hV_fst] at h7
    exact h7.symm
  have hw1 : w.1 = 0 := eq_zero_of_forall_fixed hb hnd hfix
  rw [← hwε]
  exact ⟨w.2, by congr 2; exact Prod.ext (by simp [rV, hw1]) (by simp [rV])⟩

theorem closure_sq_fSub [FiniteDimensional (ZMod 2) E] (hnd : b.Nondegenerate) :
    Subgroup.closure {x | ∃ f ∈ fSub hH, f ^ 2 = x} = subI θ := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨f, hf, rfl⟩
    exact sq_mem_subI hc hnd hf
  · rintro _ ⟨c, rfl⟩
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul, Prod.mk_zero_zero, bv_zero]
      exact Subgroup.one_mem _
    obtain ⟨f, hf, hfr⟩ := exists_fSub_rV hc
    have hzF : zz θ ∈ fSub hH := R_le_fSub (zz_mem θ)
    have hfD := fSub_le_dSub hc hf
    have hinv : lab hH f⁻¹ = rV := by
      rw [lab_inv_dSub hfD ((mem_fSub_iff hc).mp hf).2, hfr]
    have h1 : (zz θ * f) ^ 2 = bv θ (rV, 0) * f ^ 2 := by
      have h2 : f * zz θ * f⁻¹ = bv θ (rV, 1) := by
        have h3 := bv_cAct θ f⁻¹ (0, 1)
        rw [cAct_z (hH := hH), hinv, inv_inv] at h3
        rw [h3]
        rfl
      have h4 : (zz θ * f) ^ 2 = zz θ * (f * zz θ * f⁻¹) * f ^ 2 := by
        rw [sq, sq]
        group
      rw [h4, h2, zz, ← bv_add]
      congr 2
      exact Prod.ext (zero_add _) (by change (1 : ZMod 2) + 1 = 0; decide)
    have h5 : bv θ ((1 : ZMod 2) • rV, 0) = (zz θ * f) ^ 2 * (f ^ 2)⁻¹ := by
      rw [h1, mul_inv_cancel_right, one_smul]
    rw [h5]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, (fSub hH).mul_mem hzF hf, rfl⟩)
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨f, hf, rfl⟩))

end Core

end FullCoset

open FullCoset in
theorem binary_odd_quadratic_five_full_coset_two_group_structure
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (hE : Module.finrank (ZMod 2) E = 4) {b : LinearMap.BilinForm (ZMod 2) E} (hb : b.IsAlt)
    (hnd : b.Nondegenerate) {Q : QuadraticForm (ZMod 2) E} (hQ : QuadraticMap.polarBilin Q = b)
    {M : Type} [Group M] (R : Subgroup M) [R.Normal]
    (θ : R ≃* Multiplicative ((E × ZMod 2) × ZMod 2))
    (hΩ : ∀ (m : M) (v : E × ZMod 2), ∃ v' : E × ZMod 2,
      m⁻¹ * bv θ (v, 1) * m = bv θ (v', 1))
    (hfaith : ∀ m : M, (∀ v : E × ZMod 2, m⁻¹ * bv θ (v, 1) * m = bv θ (v, 1)) → m ∈ R)
    (htrans : ∀ v v' : E × ZMod 2, ∃ m : M, m⁻¹ * bv θ (v, 1) * m = bv θ (v', 1))
    (hstab : ∀ m : M, m⁻¹ * zz θ * m = zz θ → ∃ s : bilinIsometryGroup b,
      ∀ v : E × ZMod 2, m⁻¹ * bv θ (v, 1) * m = bv θ (hV hQ s v, 1))
    (hstab' : ∀ s : bilinIsometryGroup b, ∃ m : M,
      ∀ v : E × ZMod 2, m⁻¹ * bv θ (v, 1) * m = bv θ (hV hQ s v, 1)) :
    ∃ (lam : ZMod 2) (D F : Subgroup M) (ν : M → E × ZMod 2),
      F ≤ D ∧ D.Normal ∧ F.Normal ∧ CFSG.Assembly.pCore 2 M = D ∧
      Nat.card D = 2048 ∧ Nat.card F = 128 ∧ R ≤ F ∧
      ((∀ d ∈ D, d ^ 2 ∈ R) ∧ (∀ d ∈ D, ∀ d' ∈ D, ⁅d, d'⁆ ∈ R) ∧ R.relIndex D = 32) ∧
      R.relIndex F = 2 ∧
      ((∀ d ∈ D, d ^ 2 ∈ F) ∧ (∀ d ∈ D, ∀ d' ∈ D, ⁅d, d'⁆ ∈ F) ∧ F.relIndex D = 16) ∧
      (∀ d ∈ D, d⁻¹ * zz θ * d = bv θ (ν d, 1)) ∧
      (∀ d ∈ D, ∀ d' ∈ D, ν d = ν d' ↔ d⁻¹ * d' ∈ R) ∧
      (∀ v : E × ZMod 2, ∃ d ∈ D, ν d = v) ∧
      (∀ d ∈ D, ∀ (v : E × ZMod 2) (ε : ZMod 2),
        d⁻¹ * bv θ (v, ε) * d = bv θ (v + (lam * b (ν d).1 v.1) • rV + ε • ν d, ε)) ∧
      (∀ d : M, d ∈ F ↔ d ∈ D ∧ (ν d).1 = 0) ∧
      (∀ m : M, ∃ d ∈ D, ∃ c ∈ Subgroup.centralizer {zz θ}, m = d * c) ∧
      D ⊓ Subgroup.centralizer {zz θ} = R ∧
      (subA θ).Normal ∧ subI θ ≤ Subgroup.center M ∧
      (Subgroup.center F).map F.subtype = subA θ ∧
      Subgroup.closure {x | ∃ f ∈ F, f ^ 2 = x} = subI θ ∧
      ⁅R, D⁆ = subA θ ∧ ⁅subI θ, D⁆ = ⊥ ∧
      (lam = 0 → (Subgroup.center D).map D.subtype = subA θ ∧ ⁅subA θ, D⁆ = ⊥) ∧
      (lam = 1 → (Subgroup.center D).map D.subtype = subI θ ∧ ⁅subA θ, D⁆ = subI θ ∧
        subA θ ≤ (Subgroup.upperCentralSeries D 2).map D.subtype) ∧
      ((∀ d ∈ D, (zz θ)⁻¹ * (d⁻¹ * zz θ * d) ∈ subA θ) ∧
        (∀ d ∈ D, ∀ d' ∈ D, (zz θ)⁻¹ * ((d * d')⁻¹ * zz θ * (d * d')) *
          ((zz θ)⁻¹ * (d⁻¹ * zz θ * d) * ((zz θ)⁻¹ * (d'⁻¹ * zz θ * d')))⁻¹ ∈ subI θ) ∧
        (∀ d ∈ D, (zz θ)⁻¹ * (d⁻¹ * zz θ * d) ∈ subI θ ↔ d ∈ F) ∧
        (∀ a ∈ subA θ, ∃ d ∈ D, ((zz θ)⁻¹ * (d⁻¹ * zz θ * d))⁻¹ * a ∈ subI θ)) ∧
      ((∀ f ∈ F, (zz θ)⁻¹ * (f⁻¹ * zz θ * f) ∈ subI θ) ∧
        (∀ f ∈ F, ∀ f' ∈ F, (zz θ)⁻¹ * ((f * f')⁻¹ * zz θ * (f * f')) =
          (zz θ)⁻¹ * (f⁻¹ * zz θ * f) * ((zz θ)⁻¹ * (f'⁻¹ * zz θ * f'))) ∧
        (∀ f ∈ F, (zz θ)⁻¹ * (f⁻¹ * zz θ * f) = 1 ↔ f ∈ R) ∧
        (∀ i ∈ subI θ, ∃ f ∈ F, (zz θ)⁻¹ * (f⁻¹ * zz θ * f) = i)) ∧
      (∀ c ∈ Subgroup.centralizer {zz θ}, ∀ d : M,
        (zz θ)⁻¹ * ((c⁻¹ * d * c)⁻¹ * zz θ * (c⁻¹ * d * c)) =
          c⁻¹ * ((zz θ)⁻¹ * (d⁻¹ * zz θ * d)) * c) := by
  have hH : Hyp θ hQ :=
    { omega := fun m v => by
        obtain ⟨v', hv'⟩ := hΩ m v
        rw [bv_injective θ ((bv_cAct θ m (v, 1)).trans hv')]
      faith := fun m hm => hfaith m fun v =>
        (bv_cAct θ m (v, 1)).symm.trans (by rw [hm v])
      trans := fun v v' => by
        obtain ⟨m, hm⟩ := htrans v v'
        exact ⟨m, bv_injective θ ((bv_cAct θ m (v, 1)).trans hm)⟩
      stab := fun m hm => by
        have hz' : m⁻¹ * zz θ * m = zz θ :=
          (bv_cAct θ m (0, 1)).symm.trans (by rw [hm]; rfl)
        obtain ⟨s, hs⟩ := hstab m hz'
        exact ⟨s, fun v => bv_injective θ ((bv_cAct θ m (v, 1)).trans (hs v))⟩
      stab' := fun s => by
        obtain ⟨m, hm⟩ := hstab' s
        exact ⟨m, fun v => bv_injective θ ((bv_cAct θ m (v, 1)).trans (hm v))⟩ }
  have : Finite E := Module.finite_of_finite (ZMod 2)
  have hE16 : Nat.card E = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hE, Nat.card_zmod]
    norm_num
  have hex : ∃ w : E, w ≠ 0 := by
    by_contra h
    push Not at h
    have : Subsingleton E := ⟨fun x y => by rw [h x, h y]⟩
    have h1 := Nat.card_unique (α := E)
    rw [hE16] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨lam, hc⟩ := exists_core hE hb hnd hH
  refine ⟨lam, dSub hH hb lam, fSub hH, lab hH, fSub_le_dSub hc, dSub_normal hc, fSub_normal hc,
    pCore_eq_dSub hc hE16, card_dSub hc hE16, card_fSub hc hE16, R_le_fSub,
    ⟨fun d hd => sq_mem_R hc hd, fun d hd d' hd' => comm_mem_R hc hd hd', relIndex_R_dSub hc hE16⟩,
    relIndex_R_fSub hc hE16,
    ⟨fun d hd => R_le_fSub (sq_mem_R hc hd), fun d hd d' hd' => R_le_fSub (comm_mem_R hc hd hd'),
      relIndex_fSub_dSub hc hE16⟩,
    fun d _ => ?_, fun d hd d' hd' => lab_eq_iff hc hd hd', exists_lab hc,
    fun d hd v ε => ?_, fun d => mem_fSub_iff hc, exists_dSub_mul_centralizer hc,
    dSub_inf_centralizer hc, subA_normal hH, subI_le_center hc, ?_, closure_sq_fSub hc hnd,
    commutator_R_dSub hc, commutator_subI_dSub, ?_, ?_, ?_, ?_, ?_⟩
  · rw [zz, ← bv_cAct, cAct_z]
  · rw [← bv_cAct, cAct_of_mem_dSub hd]
  · ext x
    rw [Subgroup.mem_map]
    exact mem_center_fSub_iff hc x
  · intro hl
    refine ⟨Subgroup.ext fun x => ?_, commutator_subA_dSub_of_zero hl⟩
    rw [Subgroup.mem_map]
    refine (mem_center_dSub_iff hc x).trans ⟨fun ⟨v, _, hv⟩ => ⟨v, hv.symm⟩, fun ⟨v, hv⟩ =>
      ⟨v, fun a => by rw [hl, zero_mul], hv.symm⟩⟩
  · intro hl
    refine ⟨Subgroup.ext fun x => ?_, commutator_subA_dSub_of_one hc hnd hex hl, fun a ha => ?_⟩
    · rw [Subgroup.mem_map]
      refine (mem_center_dSub_iff hc x).trans ⟨fun ⟨v, hv0, hv⟩ => ⟨v.2, ?_⟩,
        fun ⟨c, hc'⟩ => ⟨c • rV, fun a => by simp [rV], hc'.symm⟩⟩
      have hv1 : v.1 = 0 := hnd.2 _ fun a => by
        have h := hv0 a
        rwa [hl, one_mul] at h
      rw [hv]
      congr 2
      exact Prod.ext (by simp [rV, hv1]) (by simp [rV])
    · have haD : a ∈ dSub hH hb lam := R_le_dSub hc (subA_le θ ha)
      refine ⟨⟨a, haD⟩, Subgroup.mem_upperCentralSeries_succ_iff.mpr fun y => ?_, rfl⟩
      rw [Subgroup.upperCentralSeries_one]
      obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp
        (comm_subA_mem_center hc ((subA θ).inv_mem ha) ((dSub hH hb lam).inv_mem y.2))
      have hwy : ⁅(⟨a, haD⟩ : dSub hH hb lam), y⁆ = w := Subtype.ext (by
        rw [Subgroup.subtype_apply] at hwx
        rw [hwx, commutatorElement_def]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, mul_assoc])
      rw [hwy]
      exact hw
  · refine ⟨fun d hd => ?_, fun d hd d' hd' => ?_, fun d hd => ?_, fun a ha => ?_⟩
    · rw [comm_z_dSub hd]
      exact ⟨_, rfl⟩
    · rw [comm_z_dSub ((dSub hH hb lam).mul_mem hd hd'), comm_z_dSub hd, comm_z_dSub hd',
        ← bv_add, bv_inv, ← bv_add, lab_mul_dSub hd']
      refine ⟨lam * b (lab hH d').1 (lab hH d).1, ?_⟩
      congr 1
      refine Prod.ext ?_ (by simp)
      change _ = lab hH d + lab hH d' + _ + (lab hH d + lab hH d')
      rw [add_right_comm (lab hH d + lab hH d'), add_self_eq_zero_zmod_two, zero_add]
    · rw [comm_z_dSub hd, mem_fSub_iff hc]
      constructor
      · rintro ⟨c, hc'⟩
        have h1 := congrArg Prod.fst (bv_injective θ hc')
        refine ⟨hd, ?_⟩
        change (c • rV : E × ZMod 2) = lab hH d at h1
        rw [← h1]
        simp [rV]
      · rintro ⟨-, h0⟩
        refine ⟨(lab hH d).2, ?_⟩
        congr 2
        exact Prod.ext (by simp [rV, h0]) (by simp [rV])
    · obtain ⟨v, rfl⟩ := ha
      obtain ⟨d, hd, hdv⟩ := exists_lab hc v
      refine ⟨d, hd, ?_⟩
      rw [comm_z_dSub hd, hdv, inv_mul_cancel]
      exact (subI θ).one_mem
  · refine ⟨fun f hf => ?_, fun f hf f' hf' => ?_, fun f hf => ?_, fun i hi => ?_⟩
    · have hfD := fSub_le_dSub hc hf
      rw [comm_z_dSub hfD]
      refine ⟨(lab hH f).2, ?_⟩
      congr 2
      exact Prod.ext (by simp [rV, ((mem_fSub_iff hc).mp hf).2]) (by simp [rV])
    · have hfD := fSub_le_dSub hc hf
      have hfD' := fSub_le_dSub hc hf'
      rw [comm_z_dSub ((dSub hH hb lam).mul_mem hfD hfD'), comm_z_dSub hfD, comm_z_dSub hfD',
        ← bv_add, lab_mul_dSub hfD', ((mem_fSub_iff hc).mp hf').2, map_zero,
        LinearMap.zero_apply, mul_zero, zero_smul, add_zero]
      rfl
    · have hfD := fSub_le_dSub hc hf
      rw [comm_z_dSub hfD, ← bv_zero θ]
      constructor
      · intro h
        have h1 := (Prod.mk.inj (bv_injective θ h)).1
        have h2 := (lab_eq_iff hc hfD (dSub hH hb lam).one_mem).mp (by rw [h1, lab_one])
        simpa using h2
      · intro h
        rw [lab, affOf_eq_one_iff.mpr h]
        rfl
    · obtain ⟨c, rfl⟩ := hi
      obtain ⟨d, hd, hdv⟩ := exists_lab hc (c • rV)
      refine ⟨d, (mem_fSub_iff hc).mpr ⟨hd, by rw [hdv]; simp [rV]⟩, ?_⟩
      rw [comm_z_dSub hd, hdv]
  · intro c hc' d
    rw [Subgroup.mem_centralizer_singleton_iff] at hc'
    have h1 : c⁻¹ * zz θ * c = zz θ := by
      rw [mul_assoc, ← hc', inv_mul_cancel_left]
    conv_lhs => rw [← h1]
    group

end CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive
