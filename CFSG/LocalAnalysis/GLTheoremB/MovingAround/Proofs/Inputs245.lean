module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs123b
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1211b
import CFSG.LargeExtraspecial.GLRCentCount

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Prop1116Design
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

section InnDiag

variable {n : ℕ} {F : Type} [Field F]

theorem inducedByConj_one (H : Subgroup (GL (Fin n) F)) : InducedByConj H 1 1 := by
  refine ⟨Subgroup.one_mem _, fun A A' hA => ?_⟩
  have e : A' = A := Subtype.ext (by rw [hA]; group)
  rw [e]
  rfl

theorem InducedByConj.mul {H : Subgroup (GL (Fin n) F)} {g g' : GL (Fin n) F}
    {φ φ' : MulAut (StatedProj H)} (h : InducedByConj H g φ) (h' : InducedByConj H g' φ') :
    InducedByConj H (g * g') (φ * φ') := by
  refine ⟨Subgroup.mul_mem _ h.1 h'.1, fun A A' hA => ?_⟩
  have hB : g' * (A : GL (Fin n) F) * g'⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 h'.1 _).1 A.2
  have e1 : φ' (QuotientGroup.mk A) = QuotientGroup.mk (⟨_, hB⟩ : ↥H) := h'.2 A ⟨_, hB⟩ rfl
  have e2 : φ (QuotientGroup.mk (⟨_, hB⟩ : ↥H)) = QuotientGroup.mk A' :=
    h.2 ⟨_, hB⟩ A' (by rw [hA]; group)
  show φ (φ' (QuotientGroup.mk A)) = QuotientGroup.mk A'
  rw [e1, e2]

theorem InducedByConj.inv {H : Subgroup (GL (Fin n) F)} {g : GL (Fin n) F}
    {φ : MulAut (StatedProj H)} (h : InducedByConj H g φ) : InducedByConj H g⁻¹ φ⁻¹ := by
  refine ⟨Subgroup.inv_mem _ h.1, fun A A' hA => ?_⟩
  have e : φ (QuotientGroup.mk A') = QuotientGroup.mk A := h.2 A' A (by rw [hA]; group)
  calc φ⁻¹ (QuotientGroup.mk A) = φ⁻¹ (φ (QuotientGroup.mk A')) := by rw [e]
    _ = QuotientGroup.mk A' := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

variable {Y : Type*} [Group Y]

theorem actsAsConj_one (H : Subgroup (GL (Fin n) F)) (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H) :
    ActsAsConj H θ 1 1 :=
  ⟨1, inducedByConj_one H, fun _ => rfl⟩

theorem ActsAsConj.mul {H : Subgroup (GL (Fin n) F)} {θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H}
    {g g' : GL (Fin n) F} {b b' : MulAut Y} (h : ActsAsConj H θ g b) (h' : ActsAsConj H θ g' b') :
    ActsAsConj H θ (g * g') (b * b') := by
  obtain ⟨φ, hφ, hb⟩ := h
  obtain ⟨φ', hφ', hb'⟩ := h'
  refine ⟨φ * φ', InducedByConj.mul hφ hφ', fun y => ?_⟩
  show θ (QuotientGroup.mk (b (b' y))) = φ (φ' (θ (QuotientGroup.mk y)))
  rw [hb, hb']

theorem ActsAsConj.inv {H : Subgroup (GL (Fin n) F)} {θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H}
    {g : GL (Fin n) F} {b : MulAut Y} (h : ActsAsConj H θ g b) : ActsAsConj H θ g⁻¹ b⁻¹ := by
  obtain ⟨φ, hφ, hb⟩ := h
  refine ⟨φ⁻¹, InducedByConj.inv hφ, fun y => ?_⟩
  have e := hb (b⁻¹ y)
  rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply] at e
  rw [e, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

@[expose] def innDiag (H Γ : Subgroup (GL (Fin n) F)) (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H) :
    Subgroup (MulAut Y) where
  carrier := {b | ∃ g ∈ Γ, ActsAsConj H θ g b}
  one_mem' := ⟨1, Γ.one_mem, actsAsConj_one H θ⟩
  mul_mem' := by
    rintro b b' ⟨g, hg, hb⟩ ⟨g', hg', hb'⟩
    exact ⟨g * g', Γ.mul_mem hg hg', ActsAsConj.mul hb hb'⟩
  inv_mem' := by
    rintro b ⟨g, hg, hb⟩
    exact ⟨g⁻¹, Γ.inv_mem hg, ActsAsConj.inv hb⟩

theorem mem_innDiag {H Γ : Subgroup (GL (Fin n) F)} {θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H}
    {b : MulAut Y} : b ∈ innDiag H Γ θ ↔ ∃ g ∈ Γ, ActsAsConj H θ g b :=
  Iff.rfl

theorem exists_actsAsConj_conj (H : Subgroup (GL (Fin n) F))
    (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H) (y : Y) :
    ∃ g ∈ H, ActsAsConj H θ g (MulAut.conj y) := by
  obtain ⟨A₀, hA₀⟩ := QuotientGroup.mk_surjective (θ (QuotientGroup.mk y))
  refine ⟨(A₀ : GL (Fin n) F), A₀.2, MulAut.conj (θ (QuotientGroup.mk y)), ⟨?_, ?_⟩, ?_⟩
  · exact Subgroup.le_normalizer A₀.2
  · intro A A' hA
    have e : A' = A₀ * A * A₀⁻¹ := Subtype.ext (by rw [hA]; rfl)
    rw [e, MulAut.conj_apply, ← hA₀]
    rfl
  · intro y'
    rw [MulAut.conj_apply, MulAut.conj_apply]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]

theorem conj_mem_innDiag {H Γ : Subgroup (GL (Fin n) F)} (hHΓ : H ≤ Γ)
    (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H) (y : Y) : MulAut.conj y ∈ innDiag H Γ θ := by
  obtain ⟨g, hg, h⟩ := exists_actsAsConj_conj H θ y
  exact ⟨g, hHΓ hg, h⟩

theorem le_innDiag_of_isImage {p : ℕ} {H Γ : Subgroup (GL (Fin n) F)}
    {θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H} {B : Subgroup (MulAut Y)}
    (h : IsImageOfNonabelianP p H Γ θ B) : B ≤ innDiag H Γ θ := by
  obtain ⟨P, hPΓ, -, -, hBP, -⟩ := h
  intro b hb
  obtain ⟨g, hg, hgb⟩ := hBP b hb
  exact ⟨g, hPΓ hg, hgb⟩

end InnDiag

section Heis

@[expose] def HeisData (p Q : ℕ) (F : Type) [Field F] (H Γ : Subgroup (GL (Fin p) F)) : Prop :=
  (H = StatedSL p F ∧ Γ = ⊤ ∧ Nat.card F = Q ∧ p ∣ Q - 1) ∨
    (H = StatedSU p Q F ∧ Γ = GUn p Q F ∧ Nat.card F = Q ^ 2 ∧ p ∣ Q + 1)

theorem statedSU_le_gUn (p Q : ℕ) (F : Type) [Field F] : StatedSU p Q F ≤ GUn p Q F := by
  unfold StatedSU GUn
  exact Subgroup.closure_mono fun A hA => hA.2

theorem HeisData.le {p Q : ℕ} {F : Type} [Field F] {H Γ : Subgroup (GL (Fin p) F)}
    (h : HeisData p Q F H Γ) : H ≤ Γ := by
  rcases h with ⟨rfl, rfl, -, -⟩ | ⟨rfl, rfl, -, -⟩
  · exact le_top
  · exact statedSU_le_gUn p Q F

@[expose] def Input27_2_innDiag : Prop :=
  ∀ (p q n : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore p Y = ⊥ →
    ∀ (F : Type) [Field F] [Finite F] (H Γ : Subgroup (GL (Fin p) F)), HeisData p (q ^ n) F H Γ →
    ∀ (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H) (A : Subgroup (MulAut Y)),
      IsElemAbelian p A → Nat.card A = p ^ 2 → IsImageOfNonabelianP p H Γ θ A →
      ∀ W : Subgroup (MulAut Y), W ≤ innDiag H Γ θ → IsPGroup 2 ↥W →
        A ≤ Subgroup.normalizer (W : Set (MulAut Y)) →
        (∀ α ∈ A, α ≠ 1 → ∀ y ∈ GLAPPrimeCoreOf p (fixSub α),
          MulAut.conj y ∈ Subgroup.normalizer (W : Set (MulAut Y))) →
        W = ⊥

@[expose] def Input27_2_outer : Prop :=
  ∀ (p q n : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore p Y = ⊥ →
    ∀ (F : Type) [Field F] [Finite F] (H Γ : Subgroup (GL (Fin p) F)), HeisData p (q ^ n) F H Γ →
    ∀ (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H) (A : Subgroup (MulAut Y)),
      IsElemAbelian p A → Nat.card A = p ^ 2 → IsImageOfNonabelianP p H Γ θ A →
      ∀ z : MulAut Y, z ^ 2 = 1 → z ∉ innDiag H Γ θ → (∀ a ∈ A, z * a = a * z) →
        (∀ α ∈ A, α ≠ 1 → ∀ y ∈ GLAPPrimeCoreOf p (fixSub α), z * MulAut.conj y = MulAut.conj y * z) →
        False

@[expose] def Input27_2_normal : Prop :=
  ∀ (p q n : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore p Y = ⊥ →
    ∀ (F : Type) [Field F] [Finite F] (H Γ : Subgroup (GL (Fin p) F)), HeisData p (q ^ n) F H Γ →
    ∀ θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H, (innDiag H Γ θ).Normal

theorem mem_normalizer_inf {G : Type*} [Group G] {W D : Subgroup G} {x : G}
    (hW : x ∈ Subgroup.normalizer (W : Set G)) (hD : x ∈ Subgroup.normalizer (D : Set G)) :
    x ∈ Subgroup.normalizer ((W ⊓ D : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hW hD ⊢
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  rw [hW h, hD h]

theorem commute_of_inf_eq_bot {G : Type*} [Group G] {W D : Subgroup G} (hWD : W ⊓ D = ⊥)
    (hDn : D.Normal) {x : G} (hxD : x ∈ D) (hxW : x ∈ Subgroup.normalizer (W : Set G)) {w : G}
    (hw : w ∈ W) : w * x = x * w := by
  have h1 : w * x * w⁻¹ * x⁻¹ ∈ W := by
    have : x * w⁻¹ * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 hxW _).1 (W.inv_mem hw)
    have e : w * x * w⁻¹ * x⁻¹ = w * (x * w⁻¹ * x⁻¹) := by group
    rw [e]
    exact W.mul_mem hw this
  have h2 : w * x * w⁻¹ * x⁻¹ ∈ D := D.mul_mem (hDn.conj_mem x hxD w) (D.inv_mem hxD)
  have h3 : w * x * w⁻¹ * x⁻¹ ∈ W ⊓ D := ⟨h1, h2⟩
  rw [hWD, Subgroup.mem_bot] at h3
  calc w * x = (w * x * w⁻¹ * x⁻¹) * (x * w) := by group
    _ = x * w := by rw [h3, one_mul]

theorem eq_bot_of_heisData (hI : Input27_2_innDiag) (hO : Input27_2_outer) (hN : Input27_2_normal)
    {p q n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y) (hYO : GLAPPrimeCore p Y = ⊥)
    {F : Type} [Field F] [Finite F] {H Γ : Subgroup (GL (Fin p) F)} (hD : HeisData p (q ^ n) F H Γ)
    {θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H} {A : Subgroup (MulAut Y)}
    (hAel : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) (hIm : IsImageOfNonabelianP p H Γ θ A)
    {W : Subgroup (MulAut Y)} (hW2 : IsPGroup 2 ↥W) (hAW : A ≤ Subgroup.normalizer (W : Set (MulAut Y)))
    (hJW : ∀ α ∈ A, α ≠ 1 → ∀ y ∈ GLAPPrimeCoreOf p (fixSub α),
      MulAut.conj y ∈ Subgroup.normalizer (W : Set (MulAut Y))) : W = ⊥ := by
  set D : Subgroup (MulAut Y) := innDiag H Γ θ with hDdef
  have hAD : A ≤ D := le_innDiag_of_isImage hIm
  have hJD : ∀ y : Y, MulAut.conj y ∈ D := fun y => conj_mem_innDiag hD.le θ y
  have hDD : ∀ x ∈ D, x ∈ Subgroup.normalizer (D : Set (MulAut Y)) := fun x hx =>
    Subgroup.le_normalizer hx
  have hWD : W ⊓ D = ⊥ := by
    refine hI p q n hp hp2 hq hq2 hqp Y hY hYO F H Γ hD θ A hAel hAc hIm (W ⊓ D) inf_le_right
      (hW2.to_le inf_le_left) (fun a ha => mem_normalizer_inf (hAW ha) (hDD a (hAD ha))) ?_
    intro α hα hα1 y hy
    exact mem_normalizer_inf (hJW α hα hα1 y hy) (hDD _ (hJD y))
  have hDn : D.Normal := hN p q n hp hp2 hq hq2 hqp Y hY hYO F H Γ hD θ
  by_contra hne
  haveI : Finite (MulAut Y) :=
    Finite.of_injective (fun β : MulAut Y => (β : Y → Y)) fun _ _ h => MulEquiv.ext (congrFun h)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card ↥W := by
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    rcases k with _ | k
    · exact absurd (Subgroup.eq_bot_of_card_eq W (by rw [hk, pow_zero])) hne
    · rw [hk, pow_succ]
      exact Dvd.intro_left _ rfl
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hz2 : (z : MulAut Y) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  have hz1 : (z : MulAut Y) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hzD : (z : MulAut Y) ∉ D := by
    intro h
    have : (z : MulAut Y) ∈ W ⊓ D := ⟨z.2, h⟩
    rw [hWD, Subgroup.mem_bot] at this
    exact hz1 this
  refine hO p q n hp hp2 hq hq2 hqp Y hY hYO F H Γ hD θ A hAel hAc hIm z hz2 hzD
    (fun a ha => commute_of_inf_eq_bot hWD hDn (hAD ha) (hAW ha) z.2) ?_
  intro α hα hα1 y hy
  exact commute_of_inf_eq_bot hWD hDn (hJD y) (hJW α hα hα1 y hy) z.2

theorem input27_2Q_of_inputs (hI : Input27_2_innDiag) (hO : Input27_2_outer) (hN : Input27_2_normal) :
    Inputs123b.Input27_2Q := by
  intro p q n hp hp2 hq hq2 hqp Y _ _ hY hYO A hAel hAc hHeis W hW2 hAW hJW
  rcases hHeis with ⟨-, hdvd, F, _, _, θ, hcard, hIm⟩ | ⟨-, hdvd, F, _, _, θ, hcard, hIm⟩
  · exact eq_bot_of_heisData hI hO hN hp hp2 hq hq2 hqp hY hYO (Or.inl ⟨rfl, rfl, hcard, hdvd⟩)
      hAel hAc hIm hW2 hAW hJW
  · exact eq_bot_of_heisData hI hO hN hp hp2 hq hq2 hqp hY hYO (Or.inr ⟨rfl, rfl, hcard, hdvd⟩)
      hAel hAc hIm hW2 hAW hJW

end Heis

section NormalL

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL
  projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient
  onCenterQuotient_apply_mk)

variable (n : ℕ) (F : Type) [Field F]

@[expose] noncomputable def statedToProj : StatedProj (StatedSL n F) ≃* projectiveSL n F :=
  (projectiveSpecialLinearGroupEquivStatedProj n F).symm.trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL n F)

theorem statedToProj_mk (u : Matrix.SpecialLinearGroup (Fin n) F) :
    statedToProj n F (QuotientGroup.mk (specialLinearGroupEquivStatedSL n F u)) = proj n F u := by
  have h1 : (projectiveSpecialLinearGroupEquivStatedProj n F).symm
      (QuotientGroup.mk (specialLinearGroupEquivStatedSL n F u) : StatedProj (StatedSL n F)) =
      QuotientGroup.mk' (Subgroup.center _) u := by
    apply (projectiveSpecialLinearGroupEquivStatedProj n F).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [statedToProj, MulEquiv.trans_apply, h1]
  exact QuotientGroup.quotientMulEquivOfEq_mk _ u

theorem statedToProj_symm_proj (u : Matrix.SpecialLinearGroup (Fin n) F) :
    (statedToProj n F).symm (proj n F u) =
      QuotientGroup.mk (specialLinearGroupEquivStatedSL n F u) :=
  (statedToProj n F).symm_apply_eq.2 (statedToProj_mk n F u).symm

variable {n F} {Y : Type*} [Group Y]

@[expose] noncomputable def projAct (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL n F)) :
    MulAut Y →* MulAut (projectiveSL n F) :=
  (MulAut.congr (θ.trans (statedToProj n F))).toMonoidHom.comp (centerQuotientHom Y)

theorem projAct_apply (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL n F)) (b : MulAut Y)
    (y : Y) : projAct θ b (statedToProj n F (θ (QuotientGroup.mk y))) =
      statedToProj n F (θ (QuotientGroup.mk (b y))) := by
  show (θ.trans (statedToProj n F)) (onCenterQuotient b
    ((θ.trans (statedToProj n F)).symm ((θ.trans (statedToProj n F)) (QuotientGroup.mk y)))) = _
  rw [MulEquiv.symm_apply_apply]
  have h := onCenterQuotient_apply_mk b y
  simp only [QuotientGroup.mk'_apply] at h
  rw [h]
  rfl

theorem mem_normalizer_statedSL (g : GL (Fin n) F) :
    g ∈ Subgroup.normalizer ((StatedSL n F : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) := by
  rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det]
  have h : Subgroup.normalizer
      (((Matrix.GeneralLinearGroup.det : GL (Fin n) F →* Fˣ).ker : Subgroup (GL (Fin n) F)) :
        Set (GL (Fin n) F)) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.2 inferInstance
  rw [h]
  exact Subgroup.mem_top g

theorem mem_innDiag_iff_projAct (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL n F))
    (b : MulAut Y) : b ∈ innDiag (StatedSL n F) ⊤ θ ↔ projAct θ b ∈ linearAutGroup n F := by
  rw [linearAutGroup_eq_range]
  constructor
  · rintro ⟨g, -, φ, ⟨-, hφ⟩, hb⟩
    refine ⟨g, ?_⟩
    ext x
    obtain ⟨u, rfl⟩ := proj_surjective n F x
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (θ.symm (QuotientGroup.mk
      (specialLinearGroupEquivStatedSL n F u)))
    have hθy : θ (QuotientGroup.mk y) = QuotientGroup.mk (specialLinearGroupEquivStatedSL n F u) := by
      rw [hy, MulEquiv.apply_symm_apply]
    have hu : proj n F u = statedToProj n F (θ (QuotientGroup.mk y)) := by
      rw [hθy, statedToProj_mk]
    have hφu : φ (QuotientGroup.mk (specialLinearGroupEquivStatedSL n F u)) =
        QuotientGroup.mk (specialLinearGroupEquivStatedSL n F
          (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F g u)) := by
      refine hφ _ _ ?_
      apply Units.ext
      rw [Units.val_mul, Units.val_mul,
        CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe, coe_slConjugation,
        CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
    symm
    calc projAct θ b (proj n F u)
        = projAct θ b (statedToProj n F (θ (QuotientGroup.mk y))) := by rw [← hu]
      _ = statedToProj n F (θ (QuotientGroup.mk (b y))) := projAct_apply θ b y
      _ = statedToProj n F (φ (QuotientGroup.mk (specialLinearGroupEquivStatedSL n F u))) := by
          rw [hb, hθy]
      _ = proj n F (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F g u) := by
          rw [hφu, statedToProj_mk]
      _ = conjAut n F g (proj n F u) := (conjAut_proj g u).symm
  · rintro ⟨g, hg⟩
    refine ⟨g, Subgroup.mem_top g, MulAut.congr (statedToProj n F).symm (conjAut n F g),
      ⟨mem_normalizer_statedSL g, fun A A' hA => ?_⟩, fun y => ?_⟩
    · obtain ⟨u, rfl⟩ := (specialLinearGroupEquivStatedSL n F).surjective A
      show (statedToProj n F).symm (conjAut n F g (statedToProj n F (QuotientGroup.mk _))) = _
      rw [statedToProj_mk, conjAut_proj, statedToProj_symm_proj]
      congr 1
      apply Subtype.ext
      apply Units.ext
      rw [hA, CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe, coe_slConjugation,
        Units.val_mul, Units.val_mul, CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
    · show θ (QuotientGroup.mk (b y)) =
        (statedToProj n F).symm (conjAut n F g (statedToProj n F (θ (QuotientGroup.mk y))))
      rw [hg, projAct_apply, MulEquiv.symm_apply_apply]

theorem innDiag_eq_comap (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL n F)) :
    innDiag (StatedSL n F) ⊤ θ = (linearAutGroup n F).comap (projAct θ) := by
  ext b
  exact mem_innDiag_iff_projAct θ b

theorem innDiag_normal_SL [Finite F] (hn : 3 ≤ n)
    (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL n F)) :
    (innDiag (StatedSL n F) ⊤ θ).Normal := by
  rw [innDiag_eq_comap]
  haveI := linearAutGroup_normal_of_three_le (K := F) hn
  exact Subgroup.Normal.comap inferInstance _

end NormalL

section NormalU

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OutcomeLocal (primeFormOneEquiv primeFormOneEquiv_mk gramSU_one_eq)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient
  onCenterQuotient_apply_mk)

open scoped Matrix

variable {q e : ℕ} {F : Type} [Field F] (h : UnitaryFieldData q e F) {m : ℕ} (hm : 1 ≤ m)

theorem gUn_eq_primeFormUnitary :
    GUn m (q ^ e) F = primeFormUnitary h ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by
  have hbar : (fun x : F => x ^ (q ^ e)) = ⇑h.bar := funext fun c => (h.bar_apply c).symm
  apply le_antisymm
  · unfold GUn
    rw [Subgroup.closure_le]
    intro A hA
    show ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ * ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
      (A : Matrix (Fin m) (Fin m) F) = ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)
    rw [Units.val_one, Matrix.mul_one, ← hbar]
    exact hA
  · intro A hA
    apply Subgroup.subset_closure
    have hA' : ((A : Matrix (Fin m) (Fin m) F).map h.bar)ᵀ *
        ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * (A : Matrix (Fin m) (Fin m) F) =
        ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := hA
    rw [Units.val_one, Matrix.mul_one, ← hbar] at hA'
    exact hA'

@[expose] noncomputable def statedToPrimeForm :
    StatedProj (StatedSU m (q ^ e) F) ≃* primeFormP h ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) :=
  (unitaryPSUEquiv h hm).symm.trans (primeFormOneEquiv h m).symm

theorem statedToPrimeForm_mk (s : StatedSU m (q ^ e) F)
    (s' : gramSU h ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) (hs : (s : GL (Fin m) F) = s') :
    statedToPrimeForm h hm (QuotientGroup.mk s) = (s' : primeFormP h _) := by
  rw [statedToPrimeForm, MulEquiv.trans_apply]
  have h1 : (unitaryPSUEquiv h hm).symm (QuotientGroup.mk s) = unitaryProj h m s :=
    (unitaryPSUEquiv h hm).symm_apply_eq.2 (unitaryPSUEquiv_unitaryProj h hm s).symm
  rw [h1, MulEquiv.symm_apply_eq]
  exact (primeFormOneEquiv_mk h s' s hs).symm

variable {Y : Type*} [Group Y]

@[expose] noncomputable def primeAct (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSU m (q ^ e) F)) :
    MulAut Y →* MulAut (primeFormP h ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) :=
  (MulAut.congr (θ.trans (statedToPrimeForm h hm))).toMonoidHom.comp (centerQuotientHom Y)

theorem primeAct_apply (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSU m (q ^ e) F))
    (b : MulAut Y) (y : Y) :
    primeAct h hm θ b (statedToPrimeForm h hm (θ (QuotientGroup.mk y))) =
      statedToPrimeForm h hm (θ (QuotientGroup.mk (b y))) := by
  show (θ.trans (statedToPrimeForm h hm)) (onCenterQuotient b
    ((θ.trans (statedToPrimeForm h hm)).symm ((θ.trans (statedToPrimeForm h hm))
      (QuotientGroup.mk y)))) = _
  rw [MulEquiv.symm_apply_apply]
  have h' := onCenterQuotient_apply_mk b y
  simp only [QuotientGroup.mk'_apply] at h'
  rw [h']
  rfl

theorem mem_gramSU_iff_mem_statedSU {g : GL (Fin m) F} :
    g ∈ gramSU h ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) ↔ g ∈ StatedSU m (q ^ e) F :=
  Subgroup.ext_iff.1 (gramSU_one_eq h m) g

theorem mem_gramSU_of_mem (s : StatedSU m (q ^ e) F) :
    (s : GL (Fin m) F) ∈ gramSU h ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) :=
  (mem_gramSU_iff_mem_statedSU h).2 s.2

theorem mem_statedSU_of_mem (s : gramSU h ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) :
    (s : GL (Fin m) F) ∈ StatedSU m (q ^ e) F :=
  (mem_gramSU_iff_mem_statedSU h).1 s.2

theorem primeAct_eq_of_actsAsConj (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSU m (q ^ e) F))
    {g : GL (Fin m) F} (hg : g ∈ primeFormUnitary h ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F))
    {b : MulAut Y} (hgb : ActsAsConj (StatedSU m (q ^ e) F) θ g b) :
    primeAct h hm θ b = primeFormConjHom h _ ⟨g, hg⟩ := by
  obtain ⟨φ, ⟨hgN, hφ⟩, hb⟩ := hgb
  · ext x
    obtain ⟨s', rfl⟩ := QuotientGroup.mk_surjective x
    set s : StatedSU m (q ^ e) F := ⟨s', mem_statedSU_of_mem h s'⟩ with hsdef
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (θ.symm (QuotientGroup.mk s))
    have hθy : θ (QuotientGroup.mk y) = QuotientGroup.mk s := by
      rw [hy, MulEquiv.apply_symm_apply]
    have hx : ((s' : primeFormP h _)) = statedToPrimeForm h hm (θ (QuotientGroup.mk y)) := by
      rw [hθy, statedToPrimeForm_mk h hm s s' rfl]
    have hmem : g * (s : GL (Fin m) F) * g⁻¹ ∈ StatedSU m (q ^ e) F :=
      (Subgroup.mem_normalizer_iff.1 hgN _).1 s.2
    have hφs : φ (QuotientGroup.mk s) = QuotientGroup.mk (⟨_, hmem⟩ : StatedSU m (q ^ e) F) :=
      hφ s ⟨_, hmem⟩ rfl
    calc primeAct h hm θ b (s' : primeFormP h _)
        = primeAct h hm θ b (statedToPrimeForm h hm (θ (QuotientGroup.mk y))) := by rw [← hx]
      _ = statedToPrimeForm h hm (θ (QuotientGroup.mk (b y))) := primeAct_apply h hm θ b y
      _ = statedToPrimeForm h hm (QuotientGroup.mk (⟨_, hmem⟩ : StatedSU m (q ^ e) F)) := by
          rw [hb, hθy, hφs]
      _ = ((⟨g * s' * g⁻¹, conj_mem_gramSU h _ hg s'.2⟩ :
            gramSU h ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) : primeFormP h _) :=
          statedToPrimeForm_mk h hm _ _ rfl
      _ = primeFormConjHom h _ ⟨g, hg⟩ (s' : primeFormP h _) :=
          (primeFormConjHom_mk h _ ⟨g, hg⟩ s').symm

theorem mem_innDiag_iff_primeAct (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSU m (q ^ e) F))
    (b : MulAut Y) : b ∈ innDiag (StatedSU m (q ^ e) F) (GUn m (q ^ e) F) θ ↔
      primeAct h hm θ b ∈ primeFormD h ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by
  constructor
  · rintro ⟨g, hg, hgb⟩
    rw [gUn_eq_primeFormUnitary h] at hg
    exact ⟨⟨g, hg⟩, (primeAct_eq_of_actsAsConj h hm θ hg hgb).symm⟩
  · rintro ⟨A, hA⟩
    have hAg : (A : GL (Fin m) F) ∈ GUn m (q ^ e) F := by
      rw [gUn_eq_primeFormUnitary h]
      exact A.2
    refine ⟨A, hAg, MulAut.congr (statedToPrimeForm h hm).symm (primeFormConjHom h _ A),
      ⟨?_, fun A₁ A₁' hA₁ => ?_⟩, fun y => ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro t
      constructor
      · intro ht
        exact (mem_gramSU_iff_mem_statedSU h).1
          (conj_mem_gramSU h _ A.2 ((mem_gramSU_iff_mem_statedSU h).2 ht))
      · intro ht
        have h2 := conj_mem_gramSU h _ (inv_mem A.2) ((mem_gramSU_iff_mem_statedSU h).2 ht)
        have e1 : (A : GL (Fin m) F)⁻¹ * ((A : GL (Fin m) F) * t * (A : GL (Fin m) F)⁻¹) *
            (A : GL (Fin m) F)⁻¹⁻¹ = t := by group
        rw [e1] at h2
        exact (mem_gramSU_iff_mem_statedSU h).1 h2
    · show (statedToPrimeForm h hm).symm (primeFormConjHom h _ A
        (statedToPrimeForm h hm (QuotientGroup.mk A₁))) = _
      rw [statedToPrimeForm_mk h hm A₁ ⟨_, mem_gramSU_of_mem h A₁⟩ rfl, primeFormConjHom_mk,
        MulEquiv.symm_apply_eq]
      exact (statedToPrimeForm_mk h hm A₁' ⟨_, conj_mem_gramSU h _ A.2 (mem_gramSU_of_mem h A₁)⟩
        hA₁).symm
    · show θ (QuotientGroup.mk (b y)) =
        (statedToPrimeForm h hm).symm (primeFormConjHom h _ A
          (statedToPrimeForm h hm (θ (QuotientGroup.mk y))))
      rw [hA, primeAct_apply, MulEquiv.symm_apply_apply]

include h in
theorem innDiag_normal_SU (hm3 : 3 ≤ m) (hq : ¬(m = 3 ∧ q ^ e = 2))
    (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSU m (q ^ e) F)) :
    (innDiag (StatedSU m (q ^ e) F) (GUn m (q ^ e) F) θ).Normal := by
  have heq : innDiag (StatedSU m (q ^ e) F) (GUn m (q ^ e) F) θ =
      (primeFormD h ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)).comap
        (primeAct h (by omega : 1 ≤ m) θ) := by
    ext b
    exact mem_innDiag_iff_primeAct h (by omega) θ b
  rw [heq]
  have hker := ker_primeFormFieldFactor h (C := (1 : GL (Fin m) F)) isPrimeFormGram_one hm3 hq
  haveI : (primeFormD h ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)).Normal := by
    rw [← hker]
    infer_instance
  exact Subgroup.Normal.comap inferInstance _

omit h in
theorem glAut_scalar (φ : F ≃+* F) (c : Fˣ) :
    glAut φ (Matrix.GeneralLinearGroup.scalar (Fin m) c) =
      Matrix.GeneralLinearGroup.scalar (Fin m) (Units.map (φ : F →* F) c) := by
  apply Units.ext
  rw [coe_glAut, Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero φ), Units.coe_map]
  rfl

omit h in
theorem scalar_injective' (hm : 1 ≤ m) {c d : Fˣ}
    (hcd : Matrix.GeneralLinearGroup.scalar (Fin m) c = Matrix.GeneralLinearGroup.scalar (Fin m) d) :
    c = d := by
  have h1 := congrArg (fun g : GL (Fin m) F => (g : Matrix (Fin m) (Fin m) F) ⟨0, hm⟩ ⟨0, hm⟩) hcd
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h1
  exact Units.ext h1

omit h in
theorem commutator_mul_central {G : Type*} [Group G] {a b x y : G} (ha : ∀ g, a * g = g * a)
    (hb : ∀ g, b * g = g * b) :
    (a * x) * (b * y) * (a * x)⁻¹ * (b * y)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  calc (a * x) * (b * y) * (a * x)⁻¹ * (b * y)⁻¹
      = a * (x * b * y * x⁻¹) * a⁻¹ * (y⁻¹ * b⁻¹) := by group
    _ = (x * b * y * x⁻¹) * (y⁻¹ * b⁻¹) := by rw [ha (x * b * y * x⁻¹), mul_inv_cancel_right]
    _ = x * b * (y * x⁻¹ * y⁻¹) * b⁻¹ := by group
    _ = b * (x * (y * x⁻¹ * y⁻¹)) * b⁻¹ := by rw [← hb x]; group
    _ = x * (y * x⁻¹ * y⁻¹) := by rw [hb (x * (y * x⁻¹ * y⁻¹)), mul_inv_cancel_right]
    _ = x * y * x⁻¹ * y⁻¹ := by group

include h in
theorem not_outer_SU (hm3 : 3 ≤ m) (hq : ¬(m = 3 ∧ q ^ e = 2)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSU m (q ^ e) F))
    {A : Subgroup (MulAut Y)} (hAel : IsElemAbelian p A)
    (hIm : IsImageOfNonabelianP p (StatedSU m (q ^ e) F) (GUn m (q ^ e) F) θ A)
    {z : MulAut Y} (hz2 : z ^ 2 = 1)
    (hzD : z ∉ innDiag (StatedSU m (q ^ e) F) (GUn m (q ^ e) F) θ)
    (hzA : ∀ a ∈ A, z * a = a * z) : False := by
  have hm1 : 1 ≤ m := by omega
  haveI : Finite F := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin m) F) := isPrimeFormGram_one
  set U : Subgroup (GL (Fin m) F) := primeFormUnitary h ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)
    with hUdef
  set Z := primeAct h hm1 θ z with hZdef
  have hZD : Z ∉ primeFormD h ((1 : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := fun hZ =>
    hzD ((mem_innDiag_iff_primeAct h hm1 θ z).2 hZ)
  obtain ⟨φ, ⟨B, hZ⟩, -⟩ := existsUnique_primeFormFieldFactor h hC hm3 hq Z
  have hφ : primeFormFieldFactor h hC hm3 hq Z = φ := by
    rw [hZ]
    exact primeFormFieldFactor_apply h hC hm3 hq B φ
  have hφ1 : φ ≠ 1 := by
    intro h1
    apply hZD
    rw [← ker_primeFormFieldFactor h hC hm3 hq, MonoidHom.mem_ker, hφ, h1]
  have hφφ : φ * φ = 1 := by
    have h2 : primeFormFieldFactor h hC hm3 hq (Z ^ 2) = 1 := by
      rw [hZdef, ← map_pow, hz2, map_one, map_one]
    rwa [map_pow, hφ, sq] at h2
  have hφQ : ∀ x : F, φ x = x ^ q ^ e := by
    obtain ⟨-, hpow⟩ := LinearFlag.even_and_eq_pow_of_involution_prime h.prime
      (by have := h.one_le; omega) h.card hφ1 hφφ
    intro x
    rw [hpow x, show 2 * e / 2 = e by omega]
  let ψ : ↥U →* ↥U := (MulAut.conj B).toMonoidHom.comp (primeFormFieldU h hC φ).toMonoidHom
  have hψ : ∀ x : ↥U, Z * primeFormConjHom h _ x * Z⁻¹ = primeFormConjHom h _ (ψ x) := by
    intro x
    rw [hZ]
    have e1 := primeFormField_conj_eq h hC φ x
    calc primeFormConjHom h _ B * primeFormFieldHom h hC φ * primeFormConjHom h _ x *
          (primeFormConjHom h _ B * primeFormFieldHom h hC φ)⁻¹
        = primeFormConjHom h _ B * (primeFormFieldHom h hC φ * primeFormConjHom h _ x *
            (primeFormFieldHom h hC φ)⁻¹) * (primeFormConjHom h _ B)⁻¹ := by group
      _ = primeFormConjHom h _ (ψ x) := by
          rw [e1, ← map_inv, ← map_mul, ← map_mul]
          rfl
  have hker : ∀ x : ↥U, primeFormConjHom h _ x = 1 →
      ∃ c : Fˣ, h.norm (c : F) = 1 ∧ (x : GL (Fin m) F) = Matrix.GeneralLinearGroup.scalar (Fin m) c := by
    intro x hx
    have h1 : primeFormPsi h hC ⟨x, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_one, mul_one, hx]
    exact ((primeFormPsi_eq_one_iff h hC hm3 _).1 h1).2
  obtain ⟨P, hPΓ, hPp, ⟨g₀, hg₀P, h₀, hh₀P, hgh⟩, -, hPA⟩ := hIm
  have hPU : ∀ g ∈ P, g ∈ U := fun g hg => by
    have := hPΓ hg
    rwa [gUn_eq_primeFormUnitary h] at this
  obtain ⟨b₀, hb₀A, hb₀⟩ := hPA g₀ hg₀P
  obtain ⟨b₁, hb₁A, hb₁⟩ := hPA h₀ hh₀P
  set g₀' : ↥U := ⟨g₀, hPU g₀ hg₀P⟩
  set h₀' : ↥U := ⟨h₀, hPU h₀ hh₀P⟩
  have hc₀ : primeAct h hm1 θ b₀ = primeFormConjHom h _ g₀' :=
    primeAct_eq_of_actsAsConj h hm1 θ _ hb₀
  have hc₁ : primeAct h hm1 θ b₁ = primeFormConjHom h _ h₀' :=
    primeAct_eq_of_actsAsConj h hm1 θ _ hb₁
  have hfix : ∀ (x : ↥U) (b : MulAut Y), b ∈ A → primeAct h hm1 θ b = primeFormConjHom h _ x →
      ∃ c : Fˣ, ((ψ x * x⁻¹ : ↥U) : GL (Fin m) F) = Matrix.GeneralLinearGroup.scalar (Fin m) c := by
    intro x b hbA hbx
    have hcomm : Z * primeFormConjHom h _ x = primeFormConjHom h _ x * Z := by
      rw [← hbx, hZdef, ← map_mul, ← map_mul, hzA b hbA]
    have h1 : primeFormConjHom h _ (ψ x * x⁻¹) = 1 := by
      rw [map_mul, ← hψ x, map_inv, hcomm]
      group
    obtain ⟨c, -, hc⟩ := hker _ h1
    exact ⟨c, hc⟩
  obtain ⟨l₀, hl₀⟩ := hfix g₀' b₀ hb₀A hc₀
  obtain ⟨l₁, hl₁⟩ := hfix h₀' b₁ hb₁A hc₁
  set k : ↥U := g₀' * h₀' * g₀'⁻¹ * h₀'⁻¹ with hk
  have hck : primeFormConjHom h _ k = 1 := by
    have hab : b₀ * b₁ = b₁ * b₀ := congrArg Subtype.val
      (hAel.1.is_comm.comm (⟨b₀, hb₀A⟩ : ↥A) ⟨b₁, hb₁A⟩)
    have h2 : primeFormConjHom h _ g₀' * primeFormConjHom h _ h₀' =
        primeFormConjHom h _ h₀' * primeFormConjHom h _ g₀' := by
      rw [← hc₀, ← hc₁, ← map_mul, ← map_mul, hab]
    rw [hk, map_mul, map_mul, map_mul, map_inv, map_inv, h2]
    group
  obtain ⟨c, hcN, hc⟩ := hker k hck
  have hc1 : c ≠ 1 := by
    intro h1
    apply hgh
    have h2 : (k : GL (Fin m) F) = 1 := by rw [hc, h1, map_one]
    have h3 : (g₀ * h₀ * g₀⁻¹ * h₀⁻¹ : GL (Fin m) F) = 1 := h2
    calc g₀ * h₀ = (g₀ * h₀ * g₀⁻¹ * h₀⁻¹) * (h₀ * g₀) := by group
      _ = h₀ * g₀ := by rw [h3, one_mul]
  have hscal : ∀ (x : ↥U) (d : Fˣ), ((ψ x * x⁻¹ : ↥U) : GL (Fin m) F) =
      Matrix.GeneralLinearGroup.scalar (Fin m) d →
      ((ψ x : ↥U) : GL (Fin m) F) = Matrix.GeneralLinearGroup.scalar (Fin m) d * x := by
    intro x d hd
    rw [← hd]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  have hcen : ∀ (d : Fˣ) (g : GL (Fin m) F), Matrix.GeneralLinearGroup.scalar (Fin m) d * g =
      g * Matrix.GeneralLinearGroup.scalar (Fin m) d :=
    fun d g => Matrix.GeneralLinearGroup.scalar_commute d g
  have hψk : ((ψ k : ↥U) : GL (Fin m) F) = k := by
    have e0 := hscal g₀' l₀ hl₀
    have e1 := hscal h₀' l₁ hl₁
    rw [hk, map_mul, map_mul, map_mul, map_inv, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e0, e1]
    exact commutator_mul_central (hcen l₀) (hcen l₁)
  have hψk' : ((ψ k : ↥U) : GL (Fin m) F) =
      Matrix.GeneralLinearGroup.scalar (Fin m) (Units.map (φ : F →* F) c) := by
    show (B : GL (Fin m) F) * ((primeFormFieldU h hC φ k : ↥U) : GL (Fin m) F) * (B : GL (Fin m) F)⁻¹ = _
    rw [coe_primeFormFieldU, hc, glAut_scalar, ← hcen _ (B : GL (Fin m) F), mul_inv_cancel_right]
  have hφc : Units.map (φ : F →* F) c = c :=
    scalar_injective' hm1 (by rw [← hψk', hψk, hc])
  have hcQ : (c : F) ^ q ^ e = c := by
    have h1 := congrArg Units.val hφc
    rw [Units.coe_map] at h1
    rw [← hφQ]
    exact h1
  have hc2 : (c : F) * c = 1 := by
    have h1 := hcN
    rw [UnitaryFieldData.norm, h.bar_apply, hcQ] at h1
    exact h1
  have hkP : (k : GL (Fin m) F) ∈ P := by
    show g₀ * h₀ * g₀⁻¹ * h₀⁻¹ ∈ P
    exact P.mul_mem (P.mul_mem (P.mul_mem hg₀P hh₀P) (P.inv_mem hg₀P)) (P.inv_mem hh₀P)
  obtain ⟨j, hj⟩ := hPp ⟨k, hkP⟩
  have hkj : (k : GL (Fin m) F) ^ p ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hcj : c ^ p ^ j = 1 := by
    apply scalar_injective' hm1
    rw [map_pow, ← hc, hkj, map_one]
  have hcc : c ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, sq, hc2, Units.val_one])
  have hdvd : orderOf c ∣ Nat.gcd 2 (p ^ j) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcc) (orderOf_dvd_of_pow_eq_one hcj)
  have hg : Nat.gcd 2 (p ^ j) = 1 :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  exact hc1 hdvd

end NormalU

section Normal

theorem three_le_of_prime_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : 3 ≤ p := by
  have := hp.two_le
  rcases Nat.lt_or_ge p 3 with h | h
  · exfalso
    exact hp2 (by omega)
  · exact h

theorem unitaryFieldData_of_card {q n : ℕ} (hq : q.Prime) {F : Type} [Field F] [Finite F]
    (hcard : Nat.card F = (q ^ n) ^ 2) : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData q n F := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, pow_zero, one_pow] at hcard
      have h2 : 1 < Nat.card F := Finite.one_lt_card
      omega
    · exact h0
  exact ⟨hq, hn, by rw [hcard, ← pow_mul, mul_comm]⟩

theorem pow_ne_two_of_odd {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {p : ℕ} : ¬(p = 3 ∧ q ^ n = 2) := by
  rintro ⟨-, h2⟩
  have hodd : Odd (q ^ n) := (hq.odd_of_ne_two hq2).pow
  rw [h2] at hodd
  exact absurd hodd (by decide)

theorem input27_2_normal_holds : Input27_2_normal := by
  intro p q n hp hp2 hq hq2 hqp Y _ _ hY hYO F _ _ H Γ hD θ
  have hp3 := three_le_of_prime_ne_two hp hp2
  rcases hD with ⟨rfl, rfl, -, -⟩ | ⟨rfl, rfl, hcard, -⟩
  · exact innDiag_normal_SL hp3 θ
  · exact innDiag_normal_SU (unitaryFieldData_of_card hq hcard) hp3 (pow_ne_two_of_odd hq hq2) θ

@[expose] def Input27_2_outerL : Prop :=
  ∀ (p q n : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore p Y = ⊥ →
    ∀ (F : Type) [Field F] [Finite F], Nat.card F = q ^ n → p ∣ q ^ n - 1 →
    ∀ (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL p F)) (A : Subgroup (MulAut Y)),
      IsElemAbelian p A → Nat.card A = p ^ 2 → IsImageOfNonabelianP p (StatedSL p F) ⊤ θ A →
      ∀ z : MulAut Y, z ^ 2 = 1 → z ∉ innDiag (StatedSL p F) ⊤ θ → (∀ a ∈ A, z * a = a * z) →
        (∀ α ∈ A, α ≠ 1 → ∀ y ∈ GLAPPrimeCoreOf p (fixSub α), z * MulAut.conj y = MulAut.conj y * z) →
        False

theorem input27_2_outer_of_L (hL : Input27_2_outerL) : Input27_2_outer := by
  intro p q n hp hp2 hq hq2 hqp Y _ _ hY hYO F _ _ H Γ hD θ A hAel hAc hIm z hz2 hzD hzA hzJ
  rcases hD with ⟨rfl, rfl, hcard, hdvd⟩ | ⟨rfl, rfl, hcard, -⟩
  · exact hL p q n hp hp2 hq hq2 hqp Y hY hYO F hcard hdvd θ A hAel hAc hIm z hz2 hzD hzA hzJ
  · exact not_outer_SU (unitaryFieldData_of_card hq hcard) (three_le_of_prime_ne_two hp hp2)
      (pow_ne_two_of_odd hq hq2) hp hp2 θ hAel hIm hz2 hzD hzA

theorem input27_2Q_of_innDiag_outer (hI : Input27_2_innDiag) (hO : Input27_2_outer) :
    Inputs123b.Input27_2Q :=
  input27_2Q_of_inputs hI hO input27_2_normal_holds

theorem input27_2Q_of_innDiag_outerL (hI : Input27_2_innDiag) (hL : Input27_2_outerL) :
    Inputs123b.Input27_2Q :=
  input27_2Q_of_innDiag_outer hI (input27_2_outer_of_L hL)

end Normal

section X0

variable {X : Type*} [Group X] [Finite X]

@[expose] noncomputable def x0 (p : ℕ) (P : Subgroup X) : Subgroup X :=
  GLBCore p 4 P ⊔ ⨆ (E : Subgroup X) (_ : IsEkIn p 4 P E), GLBCore p 2 E

theorem normalizer_le_x0 {p : ℕ} {P Q : Subgroup X} (hQP : Q ≤ P)
    (hQ : 4 ≤ CFSG.Open.pRank p Q) : Subgroup.normalizer (Q : Set X) ≤ x0 p P := by
  have h : Subgroup.normalizer (Q : Set X) ≤ GLBCore p 4 P := le_sSup ⟨Q, hQP, hQ, rfl⟩
  exact h.trans le_sup_left

theorem normalizer_le_x0' {p : ℕ} {P E D : Subgroup X} (hE : IsEkIn p 4 P E) (hDE : D ≤ E)
    (hD : 2 ≤ CFSG.Open.pRank p D) : Subgroup.normalizer (D : Set X) ≤ x0 p P := by
  have h : Subgroup.normalizer (D : Set X) ≤ GLBCore p 2 E := le_sSup ⟨D, hDE, hD, rfl⟩
  exact (h.trans (le_iSup₂_of_le E hE le_rfl)).trans le_sup_right

end X0

@[expose] def Input24_5_comp : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), CFSG.Open.IsKGroup X → p.Prime → p ≠ 2 →
    GLAPPrimeCore p X = ⊥ → Subgroup.center X ≠ ⊥ → 5 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) →
    ∀ P : Subgroup X, IsSylowIn p ⊤ P → IsCyclic ↥(centerOf P) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ → P ≤ Subgroup.normalizer (K : Set X) →
      Subgroup.center ↥K ≠ ⊥ → IsCyclic ↥(pCoreOf p (P ⊔ K)) → K ≤ x0 p P

@[expose] def Input24_5_small : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), CFSG.Open.IsKGroup X → p.Prime → p ≠ 2 →
    GLAPPrimeCore p X = ⊥ → Subgroup.center X ≠ ⊥ → 5 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) →
    ∀ P : Subgroup X, IsSylowIn p ⊤ P → IsCyclic ↥(centerOf P) →
      ¬ CFSG.ABGLocalTools.IsPConstrained p X →
      (∀ K : Subgroup X, IsComponentOf K ⊤ → Subgroup.center ↥K ≠ ⊥) →
      CFSG.ComponentClassification.Layer.subgroup X ≤ x0 p P →
      CFSG.Open.pRank p (P ⊓ (CFSG.ComponentClassification.Layer.subgroup X ⊔ CFSG.pCore p X)) ≤ 3 →
        x0 p P = ⊤

section Basic

variable {X : Type} [Group X] [Finite X]

@[expose] def sylowOf {p : ℕ} {P : Subgroup X} (hP : IsSylowIn p ⊤ P) : Sylow p X where
  toSubgroup := P
  isPGroup' := hP.2.1
  is_maximal' := fun hQ hle => hP.2.2 _ le_top hQ hle

theorem coe_sylowOf {p : ℕ} {P : Subgroup X} (hP : IsSylowIn p ⊤ P) :
    ((sylowOf hP : Sylow p X) : Subgroup X) = P :=
  rfl

theorem isElemAbelian_zpowers' {p : ℕ} {x : X} (hx : x ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers x) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
    show (a : X) * b = b * a
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem mem_of_pow_eq_one_of_cyclic {p : ℕ} (hp : p.Prime) {C Z : Subgroup X} [IsCyclic ↥C]
    (hZC : Z ≤ C) (hZ : Nat.card Z = p) {c : X} (hcC : c ∈ C) (hcp : c ^ p = 1) : c ∈ Z := by
  by_cases hc1 : c = 1
  · rw [hc1]; exact Z.one_mem
  haveI : Fact p.Prime := ⟨hp⟩
  have hcZ : Nat.card (Subgroup.zpowers (⟨c, hcC⟩ : ↥C)) = p := by
    rw [Nat.card_zpowers]
    refine orderOf_eq_prime (Subtype.ext hcp) ?_
    intro h
    exact hc1 (congrArg Subtype.val h)
  have hZ' : Nat.card (Z.subgroupOf C) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv, hZ]
  have heq : Subgroup.zpowers (⟨c, hcC⟩ : ↥C) = Z.subgroupOf C :=
    (IsCyclic.subgroup_eq_iff_card_eq).2 (by rw [hcZ, hZ'])
  have hmem : (⟨c, hcC⟩ : ↥C) ∈ Z.subgroupOf C := by
    rw [← heq]
    exact Subgroup.mem_zpowers _
  exact Subgroup.mem_subgroupOf.1 hmem

theorem card_sup_zpowers {p : ℕ} (hp : p.Prime) {A : Subgroup X} {x : X} (hx : x ^ p = 1)
    (hxA : x ∉ A) (hc : ∀ a ∈ A, a * x = x * a) :
    Nat.card ↥(A ⊔ Subgroup.zpowers x) = Nat.card A * p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := fun h => hxA (h ▸ A.one_mem)
  have hcz : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx hx1
  have hcomm : ∀ a ∈ A, ∀ k ∈ Subgroup.zpowers x, a * k = k * a := by
    intro a ha k hk
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact ((Commute.zpow_right (hc a ha) i)).eq
  have h := Lemma1111.card_sup_mul_card_inf A (Subgroup.zpowers x) hcomm
  have hinf : A ⊓ Subgroup.zpowers x = ⊥ := by
    have hdvd : Nat.card ↥(A ⊓ Subgroup.zpowers x) ∣ p := by
      rw [← hcz]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : A ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hcz])
      apply hxA
      have hmem : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
      rw [← heq] at hmem
      exact hmem.1
  rw [hinf, Subgroup.card_bot, mul_one, hcz] at h
  exact h

theorem isElemAbelian_sup_zpowers {p : ℕ} {A : Subgroup X} {x : X} (hA : IsElemAbelian p A)
    (hx : x ^ p = 1) (hc : ∀ a ∈ A, a * x = x * a) : IsElemAbelian p (A ⊔ Subgroup.zpowers x) := by
  refine CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p hA
    (isElemAbelian_zpowers' hx) ?_
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  exact ((Commute.zpow_right (hc a ha) i)).eq.symm

theorem not_isPGroup_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hq : CFSG.Open.IsQuasisimple Q) (hQ : IsPGroup p Q) : False := by
  haveI : Group.IsNilpotent Q := hQ.isNilpotent
  have hperf := hq.1
  have htop : ∀ n, derivedSeries Q n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih]; exact hperf
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := Q)
  rw [htop n] at hn
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hq.2
  have hnt : Nontrivial (Q ⧸ Subgroup.center Q) := IsSimpleGroup.toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  apply hx
  have hy : y ∈ (⊥ : Subgroup Q) := hn ▸ Subgroup.mem_top y
  rw [Subgroup.mem_bot] at hy
  rw [hy, QuotientGroup.mk_one]

theorem exists_mem_center_orderOf {p : ℕ} (hp : p.Prime) (hO : GLAPPrimeCore p X = ⊥)
    (hZ : Subgroup.center X ≠ ⊥) : ∃ z ∈ Subgroup.center X, orderOf z = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZp : IsPGroup p ↥(Subgroup.center X) := by
    have h := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112_isPGroup_inf_centralizer hp hO
      (N := ⊤) (CFSG.Open.IsSubnormal.refl ⊤)
    have e : (⊤ : Subgroup X) ⊓ Subgroup.centralizer ((⊤ : Subgroup X) : Set X) =
        Subgroup.center X := by
      rw [top_inf_eq, Subgroup.coe_top, Subgroup.centralizer_univ]
    rwa [e] at h
  have hdvd : p ∣ Nat.card ↥(Subgroup.center X) := by
    obtain ⟨k, hk⟩ := hZp.exists_card_eq
    rcases k with _ | k
    · exact absurd (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])) hZ
    · rw [hk, pow_succ]
      exact Dvd.intro_left _ rfl
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨z, z.2, by rw [← hz, Subgroup.orderOf_coe]⟩

theorem mem_centerOf_of_mem_center {p : ℕ} [Fact p.Prime] {P : Subgroup X} (hP : IsSylowIn p ⊤ P)
    {z : X} (hzZ : z ∈ Subgroup.center X) (hz : orderOf z = p) : z ∈ P ∧ z ∈ centerOf P := by
  haveI hzn : (Subgroup.zpowers z).Normal :=
    Subgroup.normal_of_le_center ((Subgroup.zpowers_le).2 hzZ)
  have hzp : IsPGroup p ↥(Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz, pow_one]
  have hzP : z ∈ P :=
    (hzp.le_sylow_of_normal (sylowOf hP)) (Subgroup.mem_zpowers z)
  refine ⟨hzP, ⟨⟨z, hzP⟩, ?_, rfl⟩⟩
  show (⟨z, hzP⟩ : ↥P) ∈ Subgroup.center ↥P
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext ((Subgroup.mem_center_iff.1 hzZ) g)

theorem mem_of_le_normalizer {p : ℕ} (hp : p.Prime) {P : Subgroup X} (hP : IsSylowIn p ⊤ P)
    (hZP : IsCyclic ↥(centerOf P)) {z : X} (hzZ : z ∈ Subgroup.center X) (hz : orderOf z = p)
    {N : Subgroup X} (hPN : P ≤ Subgroup.normalizer (N : Set X)) (hPN' : P ⊓ N ≠ ⊥) : z ∈ N := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hN' : (N.subgroupOf P).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hPN g.2) n).1 hn
  have hne : N.subgroupOf P ≠ ⊥ := by
    intro h
    apply hPN'
    rw [eq_bot_iff]
    rintro x ⟨hxP, hxN⟩
    have : (⟨x, hxP⟩ : ↥P) ∈ N.subgroupOf P := Subgroup.mem_subgroupOf.2 hxN
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  haveI : Group.IsNilpotent ↥P := hP.2.1.isNilpotent
  have hT := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hTp : IsPGroup p ↥(N.subgroupOf P ⊓ Subgroup.center ↥P) := hP.2.1.to_subgroup _
  have hdvd : p ∣ Nat.card ↥(N.subgroupOf P ⊓ Subgroup.center ↥P) := by
    obtain ⟨k, hk⟩ := hTp.exists_card_eq
    rcases k with _ | k
    · exact absurd (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])) hT
    · rw [hk, pow_succ]
      exact Dvd.intro_left _ rfl
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hwN : ((w : ↥P) : X) ∈ N := Subgroup.mem_subgroupOf.1 w.2.1
  have hwC : ((w : ↥P) : X) ∈ centerOf P := ⟨w, w.2.2, rfl⟩
  have hwo : orderOf ((w : ↥P) : X) = p := by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  obtain ⟨-, hzC⟩ := mem_centerOf_of_mem_center hP hzZ hz
  haveI := hZP
  have hZle : Subgroup.zpowers ((w : ↥P) : X) ≤ centerOf P := (Subgroup.zpowers_le).2 hwC
  have hzW := mem_of_pow_eq_one_of_cyclic hp hZle (by rw [Nat.card_zpowers, hwo]) hzC
    (by rw [← hz]; exact pow_orderOf_eq_one z)
  exact (Subgroup.zpowers_le.2 hwN) hzW

open CFSG.HardMathSupport.Timmesfeld.ComponentBalance in
theorem center_ne_bot_of_isComponentOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hO : GLAPPrimeCore p X = ⊥) {P : Subgroup X} (hP : IsSylowIn p ⊤ P)
    (hZP : IsCyclic ↥(centerOf P)) {z : X} (hzZ : z ∈ Subgroup.center X) (hz : orderOf z = p)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) : Subgroup.center ↥K ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  set J : Subgroup X := i112J P K with hJ
  have hPJ : P ≤ Subgroup.normalizer (J : Set X) := i112_B_le_normalizer_J
  obtain ⟨t, htPK, ht, -⟩ :=
    CFSG.AGLEmbedding.exists_mem_sylow_inf_component hp hp2 hO (sylowOf hP) hK
  have hKJ : K ≤ J := i112_orbit_le_J i112_self_mem_orbit
  have hPJ' : P ⊓ J ≠ ⊥ := by
    intro h
    have : t ∈ P ⊓ J := ⟨htPK.1, hKJ htPK.2⟩
    rw [h, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at ht
    exact hp.one_lt.ne ht
  have hzJ : z ∈ J := mem_of_le_normalizer hp hP hZP hzZ hz hPJ hPJ'
  have hzC : z ∈ J ⊓ Subgroup.centralizer (J : Set X) :=
    ⟨hzJ, Subgroup.mem_centralizer_iff.2 fun g _ => (Subgroup.mem_center_iff.1 hzZ g)⟩
  rw [i112_centre_J_eq hK] at hzC
  intro hbot
  have hM : ∀ M : ↥(i112Orbit P K), (M : Subgroup X) ⊓ Subgroup.centralizer ((M : Subgroup X) : Set X) = ⊥ := by
    rintro ⟨M, hMo⟩
    obtain ⟨g, -, rfl⟩ := mem_i112Orbit.1 hMo
    have h1 : Nat.card (centreIn (GLBConj g K)) = Nat.card (Subgroup.center ↥K) := by
      rw [card_centreIn]
      exact Nat.card_congr (Subgroup.centerCongr (conjEquiv g K)).toEquiv.symm
    rw [hbot, Subgroup.card_bot] at h1
    exact Subgroup.eq_bot_of_card_eq _ h1
  simp only [hM, iSup_bot, Subgroup.mem_bot] at hzC
  rw [hzC, orderOf_one] at hz
  exact hp.one_lt.ne hz

end Basic

section NotNormal

variable {X : Type} [Group X] [Finite X]

theorem comm_of_ne_component {K L : Subgroup X} (hK : IsComponentOf K ⊤) (hL : IsComponentOf L ⊤)
    (hne : K ≠ L) {a b : X} (ha : a ∈ K) (hb : b ∈ L) : a * b = b * a := by
  have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne K L hK hL hne
  have hmem := Subgroup.commutator_mem_commutator ha hb
  rw [hcomm, Subgroup.mem_bot] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hmem

theorem le_centralizer_of_ne_component {K L : Subgroup X} (hK : IsComponentOf K ⊤)
    (hL : IsComponentOf L ⊤) (hne : L ≠ K) : L ≤ Subgroup.centralizer (K : Set X) :=
  fun _ ha => Subgroup.mem_centralizer_iff.2 fun _ hb => comm_of_ne_component hK hL hne.symm hb ha

theorem mem_of_mul_self_mem {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P H : Subgroup X}
    (hP : IsPGroup p ↥P) {b : X} (hb : b ∈ P) (hb2 : b * b ∈ H) : b ∈ H := by
  obtain ⟨k, hk⟩ := hP ⟨b, hb⟩
  have hbk : b ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨m, hm⟩ : Odd (p ^ k) := (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have e : b = (b * b) ^ (m + 1) := by
    rw [← sq, ← pow_mul, show 2 * (m + 1) = p ^ k + 1 by omega, pow_succ, hbk, one_mul]
  rw [e]
  exact H.pow_mem hb2 _

theorem conj_not_mem_centralizer {H : Subgroup X} {x : X} (hx : x ∉ Subgroup.centralizer (H : Set X))
    (b : X) : b⁻¹ * x * b ∉ Subgroup.centralizer (GLBConj b H : Set X) := by
  intro h
  apply hx
  rw [Subgroup.mem_centralizer_iff] at h ⊢
  intro y hy
  have hy' : b⁻¹ * y * b ∈ GLBConj b H := mem_gLBConj.2 (by group; exact hy)
  have := h _ hy'
  have e1 : y * x = b * ((b⁻¹ * y * b) * (b⁻¹ * x * b)) * b⁻¹ := by group
  have e2 : x * y = b * ((b⁻¹ * x * b) * (b⁻¹ * y * b)) * b⁻¹ := by group
  rw [e1, e2, this]

theorem conj_mem_gLBConj {H : Subgroup X} {x : X} (hx : x ∈ H) (b : X) : b⁻¹ * x * b ∈ GLBConj b H :=
  mem_gLBConj.2 (by group; exact hx)

theorem conj_pow_eq_one {p : ℕ} {x : X} (hx : x ^ p = 1) (b : X) : (b⁻¹ * x * b) ^ p = 1 := by
  have h := conj_pow (a := b⁻¹) (b := x) (i := p)
  rw [inv_inv] at h
  rw [h, hx, mul_one, inv_mul_cancel]

theorem sup_zpowers_le_centralizer {A : Subgroup X} {x y : X}
    (hA : A ≤ Subgroup.centralizer ({y} : Set X)) (hxy : x * y = y * x) :
    A ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({y} : Set X) :=
  sup_le hA ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 hxy))

theorem sup_zpowers_le_centralizer' {A K : Subgroup X} {x : X}
    (hA : A ≤ Subgroup.centralizer (K : Set X)) (hx : x ∈ Subgroup.centralizer (K : Set X)) :
    A ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set X) :=
  sup_le hA ((Subgroup.zpowers_le).2 hx)

theorem comm_of_le_centralizer_singleton {A : Subgroup X} {x : X}
    (hA : A ≤ Subgroup.centralizer ({x} : Set X)) : ∀ a ∈ A, a * x = x * a := fun a ha =>
  Subgroup.mem_centralizer_singleton_iff.1 (hA ha)

theorem le_x0_of_not_le_normalizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hO : GLAPPrimeCore p X = ⊥) {P : Subgroup X} (hP : IsSylowIn p ⊤ P) {z : X}
    (hzZ : z ∈ Subgroup.center X) (hz : orderOf z = p) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hPK : ¬ P ≤ Subgroup.normalizer (K : Set X)) : K ≤ x0 p P := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, hbP, hbK⟩ := Set.not_subset.1 hPK
  set K₂ : Subgroup X := GLBConj b K with hK₂def
  set K₃ : Subgroup X := GLBConj b K₂ with hK₃def
  have hK₂ : IsComponentOf K₂ ⊤ := isComponentOf_gLBConj hK b
  have hK₃ : IsComponentOf K₃ ⊤ := isComponentOf_gLBConj hK₂ b
  have h12 : K ≠ K₂ := fun h => hbK (mem_normalizer_iff_gLBConj_eq.2 h.symm)
  have h23 : K₂ ≠ K₃ := by
    intro h
    apply h12
    have := congrArg (GLBConj b⁻¹) h
    rwa [hK₃def, gLBConj_inv_gLBConj, hK₂def, gLBConj_inv_gLBConj] at this
  have h13 : K ≠ K₃ := by
    intro h
    apply hbK
    have hbb : b * b ∈ Subgroup.normalizer (K : Set X) := by
      rw [mem_normalizer_iff_gLBConj_eq, ← gLBConj_gLBConj]
      exact h.symm
    exact mem_of_mul_self_mem hp2 hP.2.1 hbP hbb
  obtain ⟨e₁, he₁PK, he₁, he₁C⟩ :=
    CFSG.AGLEmbedding.exists_mem_sylow_inf_component hp hp2 hO (sylowOf hP) hK
  have he₁p : e₁ ^ p = 1 := he₁ ▸ pow_orderOf_eq_one e₁
  set e₂ : X := b⁻¹ * e₁ * b with he₂def
  set e₃ : X := b⁻¹ * e₂ * b with he₃def
  have he₂K : e₂ ∈ K₂ := conj_mem_gLBConj he₁PK.2 b
  have he₃K : e₃ ∈ K₃ := conj_mem_gLBConj he₂K b
  have he₂C : e₂ ∉ Subgroup.centralizer (K₂ : Set X) := conj_not_mem_centralizer he₁C b
  have he₃C : e₃ ∉ Subgroup.centralizer (K₃ : Set X) := conj_not_mem_centralizer he₂C b
  have he₂p : e₂ ^ p = 1 := conj_pow_eq_one he₁p b
  have he₃p : e₃ ^ p = 1 := conj_pow_eq_one he₂p b
  have hbP' : b⁻¹ ∈ P := P.inv_mem hbP
  have he₂P : e₂ ∈ P := P.mul_mem (P.mul_mem hbP' he₁PK.1) hbP
  have he₃P : e₃ ∈ P := P.mul_mem (P.mul_mem hbP' he₂P) hbP
  obtain ⟨hzP, -⟩ := mem_centerOf_of_mem_center hP hzZ hz
  have hzp : z ^ p = 1 := hz ▸ pow_orderOf_eq_one z
  have hzc : ∀ y : X, z ∈ Subgroup.centralizer ({y} : Set X) := fun y =>
    Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_center_iff.1 hzZ) y).symm
  have hzK : ∀ L : Subgroup X, Subgroup.zpowers z ≤ Subgroup.centralizer (L : Set X) := fun L =>
    (Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_iff.2 fun g _ => (Subgroup.mem_center_iff.1 hzZ) g)
  have c12 : e₁ * e₂ = e₂ * e₁ := comm_of_ne_component hK hK₂ h12 he₁PK.2 he₂K
  have c13 : e₁ * e₃ = e₃ * e₁ := comm_of_ne_component hK hK₃ h13 he₁PK.2 he₃K
  have c23 : e₂ * e₃ = e₃ * e₂ := comm_of_ne_component hK₂ hK₃ h23 he₂K he₃K
  have he₁K₂ : e₁ ∈ Subgroup.centralizer (K₂ : Set X) := le_centralizer_of_ne_component hK₂ hK h12 he₁PK.2
  have he₁K₃ : e₁ ∈ Subgroup.centralizer (K₃ : Set X) := le_centralizer_of_ne_component hK₃ hK h13 he₁PK.2
  have he₂K₃ : e₂ ∈ Subgroup.centralizer (K₃ : Set X) := le_centralizer_of_ne_component hK₃ hK₂ h23 he₂K
  set A₁ : Subgroup X := Subgroup.zpowers z with hA₁
  set A₂ : Subgroup X := A₁ ⊔ Subgroup.zpowers e₁ with hA₂
  set A₃ : Subgroup X := A₂ ⊔ Subgroup.zpowers e₂ with hA₃
  set A₄ : Subgroup X := A₃ ⊔ Subgroup.zpowers e₃ with hA₄
  have hA₂e₂ : A₂ ≤ Subgroup.centralizer ({e₂} : Set X) :=
    sup_zpowers_le_centralizer ((Subgroup.zpowers_le).2 (hzc e₂)) c12
  have hA₃e₃ : A₃ ≤ Subgroup.centralizer ({e₃} : Set X) :=
    sup_zpowers_le_centralizer (sup_zpowers_le_centralizer ((Subgroup.zpowers_le).2 (hzc e₃)) c13) c23
  have hA₁e₁ : A₁ ≤ Subgroup.centralizer ({e₁} : Set X) := (Subgroup.zpowers_le).2 (hzc e₁)
  have hA₁C : A₁ ≤ Subgroup.centralizer (K : Set X) := hzK K
  have hA₂C : A₂ ≤ Subgroup.centralizer (K₂ : Set X) := sup_zpowers_le_centralizer' (hzK K₂) he₁K₂
  have hA₃C : A₃ ≤ Subgroup.centralizer (K₃ : Set X) :=
    sup_zpowers_le_centralizer' (sup_zpowers_le_centralizer' (hzK K₃) he₁K₃) he₂K₃
  have hc₁ : Nat.card A₁ = p := by rw [hA₁, Nat.card_zpowers, hz]
  have hc₂ : Nat.card A₂ = p * p := by
    rw [hA₂, card_sup_zpowers hp he₁p (fun h => he₁C (hA₁C h)) (comm_of_le_centralizer_singleton hA₁e₁),
      hc₁]
  have hc₃ : Nat.card A₃ = p * p * p := by
    rw [hA₃, card_sup_zpowers hp he₂p (fun h => he₂C (hA₂C h)) (comm_of_le_centralizer_singleton hA₂e₂),
      hc₂]
  have hc₄ : Nat.card A₄ = p ^ 4 := by
    rw [hA₄, card_sup_zpowers hp he₃p (fun h => he₃C (hA₃C h)) (comm_of_le_centralizer_singleton hA₃e₃),
      hc₃]
    ring
  have hel₄ : IsElemAbelian p A₄ :=
    isElemAbelian_sup_zpowers (isElemAbelian_sup_zpowers (isElemAbelian_sup_zpowers
      (isElemAbelian_zpowers' hzp) he₁p (comm_of_le_centralizer_singleton hA₁e₁)) he₂p
      (comm_of_le_centralizer_singleton hA₂e₂)) he₃p (comm_of_le_centralizer_singleton hA₃e₃)
  have hA₄P : A₄ ≤ P :=
    sup_le (sup_le (sup_le ((Subgroup.zpowers_le).2 hzP) ((Subgroup.zpowers_le).2 he₁PK.1))
      ((Subgroup.zpowers_le).2 he₂P)) ((Subgroup.zpowers_le).2 he₃P)
  have hE : IsEkIn p 4 P A₄ := ⟨hA₄P, hel₄, hc₄⟩
  set D : Subgroup X := Subgroup.zpowers e₂ ⊔ Subgroup.zpowers e₃ with hD
  have hDE : D ≤ A₄ := sup_le ((le_sup_right : Subgroup.zpowers e₂ ≤ A₃).trans le_sup_left) le_sup_right
  have he₂1 : e₂ ≠ 1 := fun h => he₂C (h ▸ Subgroup.one_mem _)
  have hcD : Nat.card D = p ^ 2 := by
    have hz2 : Subgroup.zpowers e₂ ≤ Subgroup.centralizer ({e₃} : Set X) :=
      (Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 c23)
    rw [hD, card_sup_zpowers hp he₃p
      (fun h => he₃C ((Subgroup.zpowers_le).2 he₂K₃ h)) (comm_of_le_centralizer_singleton hz2),
      Nat.card_zpowers, orderOf_eq_prime he₂p he₂1, sq]
  have hDel : IsElemAbelian p D :=
    isElemAbelian_sup_zpowers (isElemAbelian_zpowers' he₂p) he₃p
      (comm_of_le_centralizer_singleton
        ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 c23)))
  have hDr : 2 ≤ CFSG.Open.pRank p D := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hDel hcD
  have hKD : K ≤ Subgroup.normalizer (D : Set X) := by
    have h1 : D ≤ Subgroup.centralizer (K : Set X) :=
      sup_le ((Subgroup.zpowers_le).2 (le_centralizer_of_ne_component hK hK₂ h12.symm he₂K))
        ((Subgroup.zpowers_le).2 (le_centralizer_of_ne_component hK hK₃ h13.symm he₃K))
    exact (Subgroup.le_centralizer_iff.1 h1).trans (Subgroup.centralizer_le_normalizer _)
  exact hKD.trans (normalizer_le_x0' hE hDE hDr)

end NotNormal

section NotCyclic

variable {X : Type} [Group X] [Finite X]

theorem isComponentOf_subgroupOf_top {K Y : Subgroup X} (hK : IsComponentOf K ⊤) (hKY : K ≤ Y) :
    IsComponentOf (K.subgroupOf Y) ⊤ := by
  have hKY' : IsComponentOf K Y := ⟨hKY, isSubnormal_of_le_of_le hK.2.1 hKY le_top, hK.2.2⟩
  refine ⟨le_top, ?_, CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (Subgroup.subgroupOfEquivOfLe hKY'.1) hKY'.2.2⟩
  have := hKY'.2.1.comap Y.subtype
  exact (Subgroup.subgroupOf_self (H := Y)) ▸ this

theorem le_centralizer_pCoreOf {p : ℕ} [Fact p.Prime] {K Y : Subgroup X} (hK : IsComponentOf K ⊤)
    (hKY : K ≤ Y) : K ≤ Subgroup.centralizer (pCoreOf p Y : Set X) := by
  have hK' := isComponentOf_subgroupOf_top hK hKY
  rcases CFSG.ComponentClassification.LocalComponents.normal_contains_or_commutes (K.subgroupOf Y)
    (CFSG.pCore p ↥Y) hK' with hle | hcomm
  · exfalso
    have hp : IsPGroup p ↥(K.subgroupOf Y) := (CFSG.pCore_isPGroup (p := p) (G := ↥Y)).to_le hle
    exact not_isPGroup_of_isQuasisimple hK'.2.2 hp
  · intro k hk
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    have hmem := Subgroup.commutator_mem_commutator
      (Subgroup.mem_subgroupOf.2 hk : (⟨k, hKY hk⟩ : ↥Y) ∈ K.subgroupOf Y) hq
    rw [hcomm, Subgroup.mem_bot] at hmem
    have h := commutatorElement_eq_one_iff_mul_comm.mp hmem
    exact (congrArg Subtype.val h).symm

theorem pCoreOf_le_of_isSylowIn {p : ℕ} [Fact p.Prime] {P Y : Subgroup X} (hP : IsSylowIn p ⊤ P)
    (hPY : P ≤ Y) : pCoreOf p Y ≤ P := by
  let S : Sylow p ↥Y :=
    { toSubgroup := P.subgroupOf Y
      isPGroup' := hP.2.1.comap_of_injective _ Y.subtype_injective
      is_maximal' := by
        intro Q hQ hle
        have h1 : Q.map Y.subtype = P := by
          refine hP.2.2 _ le_top (hQ.map _) ?_
          intro x hx
          exact ⟨⟨x, hPY hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩
        apply le_antisymm _ hle
        intro x hx
        rw [Subgroup.mem_subgroupOf, ← h1]
        exact ⟨x, hx, rfl⟩ }
  have hle : CFSG.pCore p ↥Y ≤ S := (CFSG.pCore_isPGroup (p := p) (G := ↥Y)).le_sylow_of_normal S
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact Subgroup.mem_subgroupOf.1 (hle hy)

theorem le_x0_of_not_isCyclic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup X} (hP : IsSylowIn p ⊤ P) (hZP : IsCyclic ↥(centerOf P))
    (h5 : 5 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) {z : X} (hzZ : z ∈ Subgroup.center X)
    (hz : orderOf z = p) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hPK : P ≤ Subgroup.normalizer (K : Set X)) (hQ : ¬ IsCyclic ↥(pCoreOf p (P ⊔ K))) :
    K ≤ x0 p P := by
  haveI : Fact p.Prime := ⟨hp⟩
  set Y : Subgroup X := P ⊔ K with hY
  set Q : Subgroup X := pCoreOf p Y with hQdef
  have hQP : Q ≤ P := pCoreOf_le_of_isSylowIn hP le_sup_left
  have hPQ : P ≤ Subgroup.normalizer (Q : Set X) :=
    (le_sup_left : P ≤ Y).trans (CFSG.ABGTheoremB.le_normalizer_map_subtype Y (CFSG.pCore p ↥Y))
  obtain ⟨U, hUQ, hPU, hUel, hUc⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_normal_E2 hp2 hP.2.1 hQP hPQ hQ
  have hUP : U ≤ P := hUQ.trans hQP
  have hKU : K ≤ Subgroup.centralizer (U : Set X) :=
    (le_centralizer_pCoreOf hK le_sup_right).trans (Subgroup.centralizer_le hUQ)
  have hUne : P ⊓ U ≠ ⊥ := by
    rw [inf_eq_right.2 hUP]
    intro h
    rw [h, Subgroup.card_bot] at hUc
    exact absurd hUc (by have := Nat.one_lt_pow (n := 2) (by norm_num) hp.one_lt; omega)
  have hzU : z ∈ U := mem_of_le_normalizer hp hP hZP hzZ hz hPU hUne
  have hzp : z ^ p = 1 := hz ▸ pow_orderOf_eq_one z
  have hcz : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hz]
  have hzUle : Subgroup.zpowers z ≤ U := (Subgroup.zpowers_le).2 hzU
  obtain ⟨y, hyU, hyz⟩ : ∃ y ∈ U, y ∉ Subgroup.zpowers z := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (fun x hx => hall x hx : U ≤ Subgroup.zpowers z)
    rw [hUc, hcz] at this
    have := Nat.lt_pow_self (n := 2) hp.one_lt
    nlinarith [hp.one_lt]
  have hyp : y ^ p = 1 := hUel.2 y hyU
  have hzc : ∀ g : X, g * z = z * g := fun g => (Subgroup.mem_center_iff.1 hzZ) g
  have hUzy : U = Subgroup.zpowers z ⊔ Subgroup.zpowers y := by
    have hle : Subgroup.zpowers z ⊔ Subgroup.zpowers y ≤ U := sup_le hzUle ((Subgroup.zpowers_le).2 hyU)
    have hcard : Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers y) = p ^ 2 := by
      rw [card_sup_zpowers hp hyp hyz, hcz, sq]
      intro a ha
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      exact (Commute.zpow_left (hzc y).symm i).eq
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hUc])).symm
  obtain ⟨B, hBP, hBel, hBc⟩ := Claims1211b.exists_ekIn' hP h5
  have hBp : IsPGroup p ↥B := hP.2.1.to_le hBP
  set S : Set X := (U : Set X) \ (Subgroup.zpowers z : Set X) with hSdef
  have hSf : S.Finite := Set.toFinite _
  have hBS : ∀ k ∈ B, k * y * k⁻¹ ∈ S := by
    intro k hk
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hPU (hBP hk)) y).1 hyU, fun h => hyz ?_⟩
    have e : y = k⁻¹ * (k * y * k⁻¹) * k := by group
    rw [e]
    have hn : (Subgroup.zpowers z).Normal :=
      Subgroup.normal_of_le_center ((Subgroup.zpowers_le).2 hzZ)
    have := hn.conj_mem _ h k⁻¹
    rwa [inv_inv] at this
  have hSc : S.ncard = p ^ 2 - p := by
    rw [hSdef, Set.ncard_diff (fun x hx => hzUle hx), ← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq]
    simp only [SetLike.coe_sort_coe]
    rw [hUc, hcz]
  have hidx := CFSG.LargeExtraspecial.GLR.relIndex_centralizer_le_ncard hSf hBS
  rw [hSc] at hidx
  have hidx' : (Subgroup.centralizer ({y} : Set X)).relIndex B ≤ p := by
    obtain ⟨n, hn⟩ := hBp.index ((Subgroup.centralizer ({y} : Set X)).subgroupOf B)
    have hn' : (Subgroup.centralizer ({y} : Set X)).relIndex B = p ^ n := hn
    rw [hn'] at hidx ⊢
    have hlt : p ^ n < p ^ 2 := lt_of_le_of_lt hidx (Nat.sub_lt (pow_pos hp.pos 2) hp.pos)
    have hn2 : n < 2 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
    interval_cases n <;> simp [hp.one_lt.le]
  set C : Subgroup X := Subgroup.centralizer ({y} : Set X) ⊓ B with hCdef
  have hCB : C ≤ B := inf_le_right
  have hCcard : p ^ 4 ≤ Nat.card C := by
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer ({y} : Set X)) (K := B)
    rw [hBc] at h1
    have h2 : p ^ 5 ≤ p * Nat.card C := by
      calc p ^ 5 = _ := h1.symm
        _ ≤ p * Nat.card C := Nat.mul_le_mul_right _ hidx'
    have h3 : p ^ 5 = p * p ^ 4 := by ring
    rw [h3] at h2
    exact Nat.le_of_mul_le_mul_left h2 hp.pos
  have hCel : IsElemAbelian p C := Lemma1112.isElemAbelian_of_le hBel hCB
  have hUC : U ≤ Subgroup.centralizer (C : Set X) := by
    rw [hUzy]
    refine sup_le ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_iff.2 fun c _ => hzc c)) ?_
    refine (Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_iff.2 fun c hc => ?_)
    exact (Subgroup.mem_centralizer_singleton_iff.1 hc.1)
  have hE'el : IsElemAbelian p (U ⊔ C) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p hUel hCel hUC
  have hE'P : U ⊔ C ≤ P := sup_le hUP (hCB.trans hBP)
  have hE'p : IsPGroup p ↥(U ⊔ C) := hP.2.1.to_le hE'P
  have hdvd : p ^ 4 ∣ Nat.card ↥(U ⊔ C) := by
    obtain ⟨m, hm⟩ := hE'p.exists_card_eq
    have h1 : p ^ 4 ≤ p ^ m := by
      rw [← hm]
      exact hCcard.trans (Subgroup.card_le_of_le le_sup_right)
    rw [hm]
    exact pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.one_lt).1 h1)
  obtain ⟨E, hEc, hUE, hEE'⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp
    (by rw [hUc]; exact pow_dvd_pow p (by norm_num)) hdvd (le_sup_left : U ≤ U ⊔ C)
  have hE : IsEkIn p 4 P E := ⟨hEE'.trans hE'P, Lemma1112.isElemAbelian_of_le hE'el hEE', hEc⟩
  have hUr : 2 ≤ CFSG.Open.pRank p U := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hUel hUc
  exact (hKU.trans (Subgroup.centralizer_le_normalizer _)).trans (normalizer_le_x0' hE hUE hUr)

end NotCyclic

section Main

variable {X : Type} [Group X] [Finite X]

theorem component_le_x0 (hA : Input24_5_comp) {p : ℕ} (hK : CFSG.Open.IsKGroup X) (hp : p.Prime)
    (hp2 : p ≠ 2) (hO : GLAPPrimeCore p X = ⊥) (hZ : Subgroup.center X ≠ ⊥)
    (h5 : 5 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) {P : Subgroup X} (hP : IsSylowIn p ⊤ P)
    (hZP : IsCyclic ↥(centerOf P)) {K : Subgroup X} (hKc : IsComponentOf K ⊤) : K ≤ x0 p P := by
  obtain ⟨z, hzZ, hz⟩ := exists_mem_center_orderOf hp hO hZ
  by_cases hPK : P ≤ Subgroup.normalizer (K : Set X)
  · by_cases hcyc : IsCyclic ↥(pCoreOf p (P ⊔ K))
    · exact hA X p hK hp hp2 hO hZ h5 P hP hZP K hKc hPK
        (center_ne_bot_of_isComponentOf hp hp2 hO hP hZP hzZ hz hKc) hcyc
    · exact le_x0_of_not_isCyclic hp hp2 hP hZP h5 hzZ hz hKc hPK hcyc
  · exact le_x0_of_not_le_normalizer hp hp2 hO hP hzZ hz hKc hPK

theorem x0_eq_top_of_normal {p : ℕ} [Fact p.Prime] {P : Subgroup X} (hP : IsSylowIn p ⊤ P)
    {N : Subgroup X} [hN : N.Normal] (hNx : N ≤ x0 p P) (hr : 4 ≤ CFSG.Open.pRank p (P ⊓ N)) :
    x0 p P = ⊤ := by
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal (sylowOf hP) hN.isSubnormal
  have hF := Sylow.normalizer_sup_eq_top T
  rw [eq_top_iff, ← hF]
  refine sup_le ?_ hNx
  have e : ((T : Subgroup ↥N).map N.subtype) = P ⊓ N := hT
  rw [e]
  exact normalizer_le_x0 inf_le_left hr

theorem five_le_pRank_sylow {p : ℕ} [Fact p.Prime] {P : Subgroup X} (hP : IsSylowIn p ⊤ P)
    (h5 : 5 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) : 5 ≤ CFSG.Open.pRank p P := by
  obtain ⟨B, hBP, hBel, hBc⟩ := Claims1211b.exists_ekIn' hP h5
  exact CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt hBP hBel hBc

theorem input24_5_of_inputs (hA : Input24_5_comp) (hB : Input24_5_small) : Lemma1211.Input24_5 := by
  intro X _ _ p hK hp hp2 hO hZ h5 P hP hZP
  by_cases hcon : CFSG.ABGLocalTools.IsPConstrained p X
  · exact Or.inl hcon
  right
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hzZ, hz⟩ := exists_mem_center_orderOf hp hO hZ
  have hcZ : ∀ K : Subgroup X, IsComponentOf K ⊤ → Subgroup.center ↥K ≠ ⊥ := fun K hKc =>
    center_ne_bot_of_isComponentOf hp hp2 hO hP hZP hzZ hz hKc
  have hE : CFSG.ComponentClassification.Layer.subgroup X ≤ x0 p P :=
    sSup_le fun K hKc => component_le_x0 hA hK hp hp2 hO hZ h5 hP hZP hKc
  have hPx : P ≤ x0 p P :=
    Subgroup.le_normalizer.trans (normalizer_le_x0 le_rfl (by have := five_le_pRank_sylow hP h5; omega))
  have hOp : CFSG.pCore p X ≤ x0 p P :=
    ((CFSG.pCore_isPGroup (p := p) (G := X)).le_sylow_of_normal (sylowOf hP)).trans hPx
  haveI : (CFSG.ComponentClassification.Layer.subgroup X).Normal :=
    CFSG.ComponentClassification.Layer.normal X
  by_cases hr : 4 ≤ CFSG.Open.pRank p (P ⊓ (CFSG.ComponentClassification.Layer.subgroup X ⊔ CFSG.pCore p X))
  · exact (x0_eq_top_of_normal hP (sup_le hE hOp) hr).symm
  · exact (hB X p hK hp hp2 hO hZ h5 P hP hZP hcon hcZ hE (by omega)).symm

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245
