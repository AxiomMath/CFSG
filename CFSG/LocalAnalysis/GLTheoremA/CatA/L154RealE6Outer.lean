module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154RealE6Inner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcDataTw
public import CFSG.LieType.Steinberg.Isogeny.TwistedE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Assembly (LargeEvenInduces LargeEvenMarking LargeEvenCenterQuot LargeEvenCenterMk
  LargeEvenChevH LargeEvenChevIDImage LargeEvenChevGL LargeEvenIsRoot LargeEvenCartanE
  LargeEvenLabel LargeEvenLieTag LargeEvenRawDatum LargeEvenRecipeChevalley LargeEvenTwistedH)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType CFSG.StandardType.RecipeExcLang CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup mem_fixedGroup sigma sigma_xm_single)

theorem l154_conj_eq_aux {G : Type*} [Group G] (d c A : G) :
    d * c * A * c⁻¹ * d⁻¹ = (d * c) * A * (d * c)⁻¹ := by
  group

section Untransport

theorem l154_tw_untransport {t : TwistTag} {K : Type} [Field K] {n : ℕ} (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hperf : ⁅twistedFixedGroup t K σ.toRingHom, twistedFixedGroup t K σ.toRingHom⁆ =
      graphFixedRootGroup t K σ.toRingHom)
    {Q : (R : Type) → [Group R] → Set (MulAut R) → Prop}
    (h : Q (LargeEvenCenterQuot (graphFixedRootGroup t K σ.toRingHom))
      (markIDImage (IsRoot t.tag) K (graphFixedRootGroup t K σ.toRingHom))) :
    Q (LargeEvenCenterQuot (LargeEvenTwistedH t.tag.cartan K t.perm n))
      (LargeEvenChevIDImage t.tag.cartan K (LargeEvenTwistedH t.tag.cartan K t.perm n)) := by
  have hH : MarkChev.twistedH t.tag.cartan (IsRoot t.tag) K t.perm n =
      graphFixedRootGroup t K σ.toRingHom :=
    (twistedH_eq_commutator K t n σ.toRingHom hσ).trans hperf
  have h1 : ∀ S : (Fin t.tag.rank → ℤ) → Prop, LargeEvenIsRoot t.tag.cartan = S →
      Q (LargeEvenCenterQuot (MarkChev.twistedH t.tag.cartan S K t.perm n))
        (markIDImage S K (MarkChev.twistedH t.tag.cartan S K t.perm n)) →
      Q (LargeEvenCenterQuot (MarkChev.twistedH t.tag.cartan (LargeEvenIsRoot t.tag.cartan) K
        t.perm n))
        (markIDImage (LargeEvenIsRoot t.tag.cartan) K
          (MarkChev.twistedH t.tag.cartan (LargeEvenIsRoot t.tag.cartan) K t.perm n)) := by
    intro S hS
    subst hS
    exact id
  have h2 := h1 (IsRoot t.tag) (largeEvenIsRoot_eq_isRoot t.tag) (by
    rw [hH]
    exact h)
  have h3 : ∀ H : Subgroup (LargeEvenChevGL t.tag.cartan K),
      Q (LargeEvenCenterQuot H) (markIDImage (LargeEvenIsRoot t.tag.cartan) K H) →
      Q (LargeEvenCenterQuot H) (LargeEvenChevIDImage t.tag.cartan K H) := by
    intro H hQ
    rw [largeEvenChevIDImage_eq]
    exact hQ
  refine h3 _ ?_
  rw [largeEvenTwistedH_eq]
  exact h2

end Untransport

section Frob

variable {L : Type} [Field L] [CharP L 2] {f : ℕ}

variable (L f) in
@[expose] noncomputable def theta2Equiv : K2 L 2 f ≃+* K2 L 2 f :=
  RingEquiv.ofRingHom (theta2 L 2 f) (theta2 L 2 f) (RingHom.ext theta2_theta2)
    (RingHom.ext theta2_theta2)

theorem theta2Equiv_pow (c : K2 L 2 f) : theta2Equiv L f c = c ^ 2 ^ f :=
  iterateFrobenius_def 2 f c

theorem theta2Equiv_toRingHom : (theta2Equiv L f).toRingHom = theta2 L 2 f :=
  RingHom.ext fun _ => rfl

end Frob

section Card

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {f : ℕ}

theorem card_K2_two (hf : 1 ≤ f) : Nat.card (K2 L 2 f) = (2 ^ f) ^ 2 := by
  rw [card_K2 hf, pow_mul']

theorem four_le_card_K2_two (hf : 1 ≤ f) : 4 ≤ Nat.card (K2 L 2 f) := by
  rw [card_K2_two hf]
  have h2 : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.le_self_pow (by omega) 2)
  nlinarith

end Card

section Iota

variable
  {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [CharP L 2] {f : ℕ}

variable (τ L f) in
@[expose] noncomputable def e6Iota :
    ↥(fixedGroup (K2 L 2 f) (theta2 L 2 f)) →* ModGL τ (K2 L 2 f) :=
  (subsystemGroup τ (K2 L 2 f) (e6Set τ)).subtype.comp
    ((m27Equiv τ (K2 L 2 f)).symm.toMonoidHom.comp
      (fixedGroup (K2 L 2 f) (theta2 L 2 f)).subtype)

theorem coe_e6Iota (z : ↥(fixedGroup (K2 L 2 f) (theta2 L 2 f))) :
    e6Iota τ L f z =
      (((m27Equiv τ (K2 L 2 f)).symm z.1 : ↥(subsystemGroup τ (K2 L 2 f) (e6Set τ))) :
        ModGL τ (K2 L 2 f)) :=
  rfl

theorem e6Iota_injective : Function.Injective (e6Iota τ L f) := by
  intro x y h
  apply Subtype.ext
  apply (m27Equiv τ (K2 L 2 f)).symm.injective
  exact Subtype.ext h

end Iota

section IotaConj

variable
  {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [CharP L 2] {f : ℕ}

theorem theta2Q_comp_diagConj {b : Fin Tag.E6.rank → (K2 L 2 f)ˣ}
    (hb : ∀ i, b (rho6 i) = Units.map (theta2 L 2 f).toMonoidHom (b i)) :
    (theta2Q τ L 2 f).comp (diagConj τ (K2 L 2 f) (e6DiagExt b)) =
      (diagConj τ (K2 L 2 f) (e6DiagExt b)).comp (theta2Q τ L 2 f) := by
  have hb' : ∀ i, ((b (rho6 i) : (K2 L 2 f)ˣ) : K2 L 2 f) = theta2 L 2 f (b i : K2 L 2 f) :=
    fun i => by rw [hb i]; rfl
  have hb'' : ∀ i, (((b (rho6 i))⁻¹ : (K2 L 2 f)ˣ) : K2 L 2 f) =
      theta2 L 2 f (((b i)⁻¹ : (K2 L 2 f)ˣ) : K2 L 2 f) :=
    fun i => by rw [hb i, ← map_inv (Units.map (theta2 L 2 f).toMonoidHom)]; rfl
  refine hom_ext_Q (fun i c => ?_) (fun i c => ?_)
  · simp only [MonoidHom.comp_apply, diagConj_xUnit, theta2Q_xUnit]
    apply Subtype.ext
    simp only [map_mul, hb' i]
  · simp only [MonoidHom.comp_apply, diagConj_yUnit, theta2Q_yUnit]
    apply Subtype.ext
    simp only [map_mul, hb'' i]

theorem e6Iota_conj {b : Fin Tag.E6.rank → (K2 L 2 f)ˣ}
    (hb : ∀ i, b (rho6 i) = Units.map (theta2 L 2 f).toMonoidHom (b i))
    (x : ↥(fixedGroup (K2 L 2 f) (theta2 L 2 f))) :
    ∃ x' : ↥(fixedGroup (K2 L 2 f) (theta2 L 2 f)),
      rootDiagUnit τ (e6DiagExt b) * e6Iota τ L f x * (rootDiagUnit τ (e6DiagExt b))⁻¹ =
        e6Iota τ L f x' := by
  obtain ⟨q, hqx⟩ : ∃ q, m27Equiv τ (K2 L 2 f) q = x.1 :=
    ⟨(m27Equiv τ (K2 L 2 f)).symm x.1, by simp⟩
  have hq : theta2Q τ L 2 f q = q := by
    rw [theta2Q_apply, hqx, (mem_fixedGroup _).1 x.2, ← hqx, MulEquiv.symm_apply_apply]
  have hκ : theta2Q τ L 2 f (diagConj τ (K2 L 2 f) (e6DiagExt b) q) =
      diagConj τ (K2 L 2 f) (e6DiagExt b) q := by
    have := DFunLike.congr_fun (theta2Q_comp_diagConj (τ := τ) (L := L) (f := f) hb) q
    simpa only [MonoidHom.comp_apply, hq] using this
  have hfix : m27Equiv τ (K2 L 2 f) (diagConj τ (K2 L 2 f) (e6DiagExt b) q) ∈
      fixedGroup (K2 L 2 f) (theta2 L 2 f) := by
    rw [mem_fixedGroup]
    have h := hκ
    rw [theta2Q_apply] at h
    have h' := congrArg (m27Equiv τ (K2 L 2 f)) h
    simpa only [MulEquiv.apply_symm_apply] using h'
  refine ⟨⟨_, hfix⟩, ?_⟩
  change rootDiagUnit τ _ * (((m27Equiv τ (K2 L 2 f)).symm x.1 : ↥(subsystemGroup τ (K2 L 2 f)
      (e6Set τ))) : ModGL τ (K2 L 2 f)) * _ = (((m27Equiv τ (K2 L 2 f)).symm
        (m27Equiv τ (K2 L 2 f) (diagConj τ (K2 L 2 f) (e6DiagExt b) q)) : ↥(subsystemGroup τ
          (K2 L 2 f) (e6Set τ))) : ModGL τ (K2 L 2 f))
  rw [MulEquiv.symm_apply_apply, coe_diagConj, ← hqx, MulEquiv.symm_apply_apply]

end IotaConj

section OuterAd0

variable
  {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {f : ℕ} [Finite (K2 L 2 f)]

theorem twisted_commutator_eq_C0 (hf : 1 ≤ f) :
    ⁅twistedFixedGroup TwistTag.E6 (K2 L 2 f) (theta2Equiv L f).toRingHom,
        twistedFixedGroup TwistTag.E6 (K2 L 2 f) (theta2Equiv L f).toRingHom⁆ =
      graphFixedRootGroup TwistTag.E6 (K2 L 2 f) (theta2Equiv L f).toRingHom := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcomm, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf (K2 L 2 f)
      (card_K2_two hf) (theta2Equiv L f) (fun c => theta2Equiv_pow c)
  exact hcomm

end OuterAd0

section OuterAd

variable
  {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {f : ℕ} [Finite (K2 L 2 f)]

theorem e6IsogenyFixed_mem_C0 (hf : 1 ≤ f) (x : ↥(fixedGroup (K2 L 2 f) (theta2 L 2 f))) :
    e6IsogenyFixed (theta2 L 2 f) x ∈
      twistedE6RootGroup (K2 L 2 f) (theta2Equiv L f) := by
  have h1 : e6IsogenyFixed (theta2 L 2 f) x ∈ (e6IsogenyFixed (theta2 L 2 f)).range := ⟨x, rfl⟩
  rw [range_e6IsogenyFixed (theta2 L 2 f) theta2_theta2 (four_le_card_K2_two hf)] at h1
  have h2 := twisted_commutator_eq_C0 (L := L) hf
  rw [theta2Equiv_toRingHom] at h2
  rw [h2] at h1
  exact h1

variable (L f) in
@[expose] noncomputable def e6AdT (hf : 1 ≤ f) :
    ↥(fixedGroup (K2 L 2 f) (theta2 L 2 f)) →*
      ↥(twistedE6RootGroup (K2 L 2 f) (theta2Equiv L f)) :=
  (e6IsogenyFixed (theta2 L 2 f)).codRestrict _ (e6IsogenyFixed_mem_C0 hf)

theorem coe_e6AdT (hf : 1 ≤ f) (x : ↥(fixedGroup (K2 L 2 f) (theta2 L 2 f))) :
    ((e6AdT L f hf x : ↥(twistedE6RootGroup (K2 L 2 f) (theta2Equiv L f))) :
        ModGL TwistTag.E6.tag (K2 L 2 f)) = e6IsogenyFixed (theta2 L 2 f) x :=
  rfl

theorem e6AdT_surjective (hf : 1 ≤ f) : Function.Surjective (e6AdT L f hf) := by
  rintro ⟨c, hc⟩
  have h2 := twisted_commutator_eq_C0 (L := L) hf
  rw [theta2Equiv_toRingHom] at h2
  have h1 : c ∈ (e6IsogenyFixed (theta2 L 2 f)).range := by
    rw [range_e6IsogenyFixed (theta2 L 2 f) theta2_theta2 (four_le_card_K2_two hf), h2]
    exact hc
  obtain ⟨x, hx⟩ := h1
  exact ⟨x, Subtype.ext hx⟩

theorem e6AdT_ne_one (hf : 1 ≤ f) : ∃ x, e6AdT L f hf x ≠ 1 := by
  set i : Fin (Tag.rank .E6) := ⟨1, by decide⟩
  have hfix : e6Data_valid.xm (K2 L 2 f) (Pi.single i 1) 1 ∈
      fixedGroup (K2 L 2 f) (theta2 L 2 f) := by
    rw [mem_fixedGroup, sigma_xm_single, map_one]
    rfl
  refine ⟨⟨_, hfix⟩, fun h => ?_⟩
  have h' := congrArg (fun y : ↥(twistedE6RootGroup (K2 L 2 f) (theta2Equiv L f)) =>
    (y : ModGL TwistTag.E6.tag (K2 L 2 f))) h
  simp only [coe_e6AdT, OneMemClass.coe_one] at h'
  exact e6Isogeny_xm_single_one_ne_one _ i (Subtype.ext h')

end OuterAd

section OuterReal

variable
  {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {f : ℕ}
  [Finite (K2 L 2 f)]

theorem coe_e6AdT_eq_e6Ad (hf : 1 ≤ f) (x : ↥(fixedGroup (K2 L 2 f) (theta2 L 2 f))) :
    ((e6AdT L f hf x : ↥(twistedE6RootGroup (K2 L 2 f) (theta2Equiv L f))) :
        ModGL TwistTag.E6.tag (K2 L 2 f)) =
      ((e6Ad τ (K2 L 2 f) ((m27Equiv τ (K2 L 2 f)).symm x.1) : ↥(adjointGroup Tag.E6
        (K2 L 2 f))) : ModGL Tag.E6 (K2 L 2 f)) := by
  rw [coe_e6AdT]
  change ((e6IsogenyT (K2 L 2 f) x.1 : ↥(adjointGroup TwistTag.E6.tag (K2 L 2 f))) :
    ModGL TwistTag.E6.tag (K2 L 2 f)) = _
  simp only [e6Ad, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rfl

theorem l154_outer_hI (hf : 1 ≤ f)
    {φ : MulAut (LargeEvenCenterQuot (twistedE6RootGroup (K2 L 2 f) (theta2Equiv L f)))}
    (hφ : φ ∈ markIDImage (IsRoot TwistTag.E6.tag) (K2 L 2 f)
      (twistedE6RootGroup (K2 L 2 f) (theta2Equiv L f))) :
    ∃ (α : MulAut ↥(twistedE6RootGroup (K2 L 2 f) (theta2Equiv L f)))
      (Wq : ModGL τ (K2 L 2 f)),
      (∀ c, QuotientGroup.mk (α c) = φ (QuotientGroup.mk c)) ∧
      (∀ x, ∃ x', Wq * e6Iota τ L f x * Wq⁻¹ = e6Iota τ L f x') ∧
      (∀ x, ∃ x', Wq⁻¹ * e6Iota τ L f x * Wq = e6Iota τ L f x') ∧
      ∀ x x', Wq * e6Iota τ L f x * Wq⁻¹ = e6Iota τ L f x' →
        e6AdT L f hf x' = α (e6AdT L f hf x) := by
  classical
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 (K2 L 2 f) (theta2Equiv L f)
  obtain ⟨w, hw⟩ := excTwE6_exists_twConj_of_mem_markID (theta2Equiv L f) hφ
  haveI : CharP (AlgebraicClosure (K2 L 2 f)) 2 :=
    charP_of_injective_algebraMap (algebraMap (K2 L 2 f)
      (AlgebraicClosure (K2 L 2 f))).injective 2
  obtain ⟨b, hb, c, hc, hwbc⟩ : ∃ b : Fin Tag.E6.rank → (K2 L 2 f)ˣ,
      IsCompatE6 (theta2Equiv L f).toRingHom b ∧
      ∃ c ∈ graphFixedRootGroup TwistTag.E6 (K2 L 2 f) (theta2Equiv L f).toRingHom,
        (w : ModGL TwistTag.E6.tag (K2 L 2 f)) = rootDiagUnit TwistTag.E6.tag b * c :=
    exists_decomp_of_mem_twInndiag hf (card_K2_two hf)
      (σ := theta2Equiv L f) (fun c => theta2Equiv_pow c)
      (L := AlgebraicClosure (K2 L 2 f))
      (Fr := iterateFrobenius (AlgebraicClosure (K2 L 2 f)) 2 f)
      (fun c => iterateFrobenius_def 2 f c) w.2
  have hb' : ∀ i, b (rho6 i) = Units.map (theta2 L 2 f).toMonoidHom (b i) := fun i => by
    have h := hb i
    rw [show TwistTag.E6.perm i = rho6 i from rhoPerm_eq_rho6 i, theta2Equiv_toRingHom] at h
    exact h
  have hbinv : ∀ i, b⁻¹ (rho6 i) = Units.map (theta2 L 2 f).toMonoidHom (b⁻¹ i) := fun i => by
    simp only [Pi.inv_apply, hb' i, map_inv]
  obtain ⟨y₀, hy₀⟩ := e6AdT_surjective (L := L) (f := f) hf ⟨c, hc⟩
  have hc' : ((e6AdT L f hf y₀ : ↥(twistedE6RootGroup (K2 L 2 f) (theta2Equiv L f))) :
      ModGL TwistTag.E6.tag (K2 L 2 f)) = c := by rw [hy₀]
  have hdinv : (rootDiagUnit τ (e6DiagExt (τ := τ) b))⁻¹ = rootDiagUnit τ (e6DiagExt b⁻¹) := by
    rw [rootDiagUnit_inv_eq, ← e6DiagExt_inv]
  refine ⟨twConj (K2 L 2 f) (theta2Equiv L f) w,
    rootDiagUnit τ (e6DiagExt b) * e6Iota τ L f y₀, ?_, ?_, ?_, ?_⟩
  · intro c'
    show LargeEvenCenterMk _ (twConj (K2 L 2 f) (theta2Equiv L f) w c') = φ (LargeEvenCenterMk _ c')
    rw [congr_centerQuotEquivOfBot_mk hZ φ c', hw]
  · intro x
    obtain ⟨x', hx'⟩ := e6Iota_conj (τ := τ) hb' (y₀ * x * y₀⁻¹)
    refine ⟨x', ?_⟩
    rw [← hx']
    simp only [map_mul, map_inv]
    group
  · intro x
    obtain ⟨x₁, hx₁⟩ := e6Iota_conj (τ := τ) hbinv x
    refine ⟨y₀⁻¹ * x₁ * y₀, ?_⟩
    rw [← hdinv, inv_inv] at hx₁
    simp only [map_mul, map_inv]
    rw [← hx₁]
    group
  · intro x x' hxx'
    simp only [coe_e6Iota] at hxx'
    have h := e6Ad_conj_rel (τ := τ) b ((m27Equiv τ (K2 L 2 f)).symm y₀.1)
      ((m27Equiv τ (K2 L 2 f)).symm x.1) ((m27Equiv τ (K2 L 2 f)).symm x'.1) hxx'
    apply Subtype.ext
    have ey := coe_e6AdT_eq_e6Ad (τ := τ) (L := L) (f := f) hf y₀
    have ex := coe_e6AdT_eq_e6Ad (τ := τ) (L := L) (f := f) hf x
    have ex' := coe_e6AdT_eq_e6Ad (τ := τ) (L := L) (f := f) hf x'
    simp only [← ey, ← ex, ← ex'] at h
    have hcw := coe_twConj (theta2Equiv L f) w (e6AdT L f hf x)
    refine (h.trans ?_).trans hcw.symm
    simp only [hwbc, hc']
    exact l154_conj_eq_aux _ _ _

theorem l154_realizedMarking_outer {M : Type} [Group M] (hf : 1 ≤ f)
    {j : ModGL τ (K2 L 2 f) →* M} (hj : Function.Injective j)
    (hX : CFSG.IsQuasisimple ↥(j.comp (e6Iota τ L f)).range) :
    L154RealizedMarking (j.comp (e6Iota τ L f)).range := by
  obtain ⟨hqC, θ, hθ⟩ := l154_realized_of_range hj e6Iota_injective hX (e6AdT L f hf)
    (e6AdT_surjective hf) (e6AdT_ne_one hf)
    (I := markIDImage (IsRoot TwistTag.E6.tag) (K2 L 2 f)
      (twistedE6RootGroup (K2 L 2 f) (theta2Equiv L f)))
    fun φ hφ => l154_outer_hI hf hφ
  refine ⟨hX.1.commutator_eq_top, ⟨.twE6, 0, f⟩, ⟨hf, rfl⟩, ?_⟩
  refine ⟨K2 L 2 f, inferInstance, inferInstance, card_K2_two hf, ?_⟩
  exact l154_tw_untransport (t := TwistTag.E6) (theta2Equiv L f) (fun c => theta2Equiv_pow c)
    (twisted_commutator_eq_C0 hf)
    (Q := fun R _ I => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ' : ↥(j.comp (e6Iota τ L f)).range ⧸ Subgroup.center ↥(j.comp (e6Iota τ L f)).range ≃* R,
        ∀ φ ∈ I, ∃ w ∈ Subgroup.normalizer (((j.comp (e6Iota τ L f)).range : Subgroup M) :
            Set M),
          LargeEvenInduces θ' (fun r r' : ↥(j.comp (e6Iota τ L f)).range =>
            w * (r : M) * w⁻¹ = (r' : M)) φ)
    ⟨hqC.2.1, hqC.2.2, θ, hθ⟩

end OuterReal

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
