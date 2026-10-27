module

public import CFSG.LieType.SeitzGeneration.QuasiHigh2Kron
public import CFSG.LieType.SeitzGeneration.QuasiHighClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighDiagLinear

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh2

open Matrix CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2

section Model

variable {K : Type*} [Group K] {n : ℕ} {F : Type*} [Field F] {P : Type*} [Group P]

@[expose] noncomputable def modelAut (θ : K ⧸ Subgroup.center K ≃* P) : MulAut K →* MulAut P :=
  (MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K)

theorem quotAut_eq_quotientCenterAut_model (f : MulAut K) : quotAut f = quotientCenterAut' K f := by
  ext s
  induction s using QuotientGroup.induction_on with
  | H x =>
    rw [quotAut_mk]
    simp [quotientCenterAut', QuotientGroup.congr_mk]

theorem modelAut_apply (θ : K ⧸ Subgroup.center K ≃* P) (f : MulAut K) (x : P) :
    modelAut θ f x = θ (quotAut f (θ.symm x)) := by
  rw [quotAut_eq_quotientCenterAut_model]
  rfl

theorem modelAut_injective (hperf : commutator K = ⊤) (θ : K ⧸ Subgroup.center K ≃* P) :
    Function.Injective (modelAut θ) :=
  (MulAut.congr θ).injective.comp (quotientCenterAut'_injective hperf)

end Model

@[expose] def LinearDiag {K : Type*} [Group K] (p : ℕ) (E : Subgroup (MulAut K)) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F)
    (θ : K ⧸ Subgroup.center K ≃* projectiveSL n F),
    3 ≤ n ∧ (p : F) ≠ 0 ∧ p ∣ Nat.card F - 1 ∧ E.map (modelAut θ) ≤ linearAutGroup n F

section Lift

variable {n : ℕ} {F : Type*} [Field F]

@[expose] def liftSet (p : ℕ) (E : Subgroup (MulAut (projectiveSL n F))) :
    Set (SpecialLinearGroup (Fin n) F) :=
  {g | (∃ m : ℕ, ¬ p ∣ m ∧ g ^ m = 1) ∧ ∃ F' : Subgroup (MulAut (projectiveSL n F)), F' ≤ E ∧
    F'.relIndex E = p ∧ ∀ A : GL (Fin n) F, conjAut n F A ∈ F' →
      (A : Matrix (Fin n) (Fin n) F) * g = g * A}

theorem conjAut_proj_eq_of_commute {A : GL (Fin n) F} {g : SpecialLinearGroup (Fin n) F}
    (h : (A : Matrix (Fin n) (Fin n) F) * g = g * A) :
    conjAut n F A (proj n F g) = proj n F g := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, h, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one]

theorem seitzHyperGamma_eq_top_of_closure_liftSet {K : Type*} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {p : ℕ} [Fact p.Prime] {E : Subgroup (MulAut K)}
    (hE : IsPGroup p E) (θ : K ⧸ Subgroup.center K ≃* projectiveSL n F)
    (hlin : E.map (modelAut θ) ≤ linearAutGroup n F)
    (h : Subgroup.closure (liftSet p (E.map (modelAut θ))) = ⊤) : seitzHyperGamma p E = ⊤ := by
  have hinj := modelAut_injective hperf θ
  refine seitzHyperGamma_eq_top_of_quot hperf hE ?_
  set ψ : SpecialLinearGroup (Fin n) F →* K ⧸ Subgroup.center K :=
    θ.symm.toMonoidHom.comp (proj n F) with hψ
  have hψs : Function.Surjective ψ := θ.symm.surjective.comp (proj_surjective n F)
  have htop : (⊤ : Subgroup (K ⧸ Subgroup.center K)) =
      Subgroup.closure (ψ '' liftSet p (E.map (modelAut θ))) := by
    rw [← MonoidHom.map_closure, h, Subgroup.map_top_of_surjective _ hψs]
  rw [htop]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨g, ⟨⟨m, hm, hgm⟩, F', hF'E, hrel, hF'⟩, rfl⟩
  refine ⟨Or.inr ⟨m, hm, by rw [← map_pow, hgm, map_one]⟩, F'.comap (modelAut θ) ⊓ E,
    inf_le_right, ?_, ?_⟩
  · have hmap : (F'.comap (modelAut θ) ⊓ E).map (modelAut θ) = F' := by
      apply le_antisymm
      · rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
        exact hx
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := hF'E hy
        exact ⟨x, ⟨hy, hx⟩, rfl⟩
    rw [← Subgroup.relIndex_map_map_of_injective (F'.comap (modelAut θ) ⊓ E) E hinj, hmap, hrel]
  · rintro f ⟨hf, hfE⟩
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 (hlin ⟨f, hfE, rfl⟩)
    have hfix : modelAut θ f (proj n F g) = proj n F g := by
      rw [← hA]
      exact conjAut_proj_eq_of_commute (hF' A (by rw [hA]; exact hf))
    rw [modelAut_apply] at hfix
    show quotAut f (θ.symm (proj n F g)) = θ.symm (proj n F g)
    exact θ.injective (by rw [hfix, MulEquiv.apply_symm_apply])

end Lift

section Reducible

variable {K : Type*} [Group K] {n : ℕ} {F : Type} [Field F] [Finite F]

theorem diagReducible_of_liftStable (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (θ : K ⧸ Subgroup.center K ≃* projectiveSL n F) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian p (E.map (modelAut θ))) (hlin : E.map (modelAut θ) ≤ linearAutGroup n F)
    {W : Submodule F (Fin n → F)} (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hWE : LiftStable (E.map (modelAut θ)) W) : DiagReducible p E := by
  set e := LinearCover.projectiveSpecialLinearEquivProjectiveSL n F with he
  refine ⟨n, F, inferInstance, inferInstance, θ.trans e.symm,
    (E.map (modelAut θ)).comap (conjAut n F), card_comap_conjAut_ne_zero hn hp hpF hE, hpF, W,
    hW0, hWt, fun g hg w hw => hWE g hg w hw, fun f hf => ?_⟩
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 (hlin ⟨f, hf, rfl⟩)
  refine ⟨A, by rw [Subgroup.mem_comap, hA]; exact ⟨f, hf, rfl⟩, fun s => ?_⟩
  have hes : e (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) s) =
      proj n F s := rfl
  have hes' : e.symm (proj n F (glConj A s)) =
      QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) (glConj A s) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have hsl : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A s =
      glConj A s := Subtype.ext (by rw [coe_slConjugation, coe_glConj])
  have hact : θ (quotAut f (θ.symm (proj n F s))) = proj n F (glConj A s) := by
    rw [← modelAut_apply, ← hA, conjAut_proj, hsl]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_trans_apply, MulEquiv.symm_symm, hes, hact, hes']

end Reducible

section Irreducible

variable {F : Type} [Field F] [Finite F]

theorem transvection_pow_ringChar {m : Type*} [Fintype m] [DecidableEq m] {i j : m}
    (hij : i ≠ j) (c : F) : SpecialLinearGroup.transvection hij c ^ ringChar F = 1 := by
  have h : ∀ k : ℕ, SpecialLinearGroup.transvection hij c ^ k =
      SpecialLinearGroup.transvection hij ((k : F) * c) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add]
      congr 1
      push_cast
      ring
  rw [h, ringChar.Nat.cast_ringChar, zero_mul, SpecialLinearGroup.transvection_coeff_zero]

theorem det_eq_one_of_perfect {G : Type*} [Group G] (hG : commutator G = ⊤) {m : ℕ}
    (φ : G →* GL (Fin m) F) (g : G) : GeneralLinearGroup.det (φ g) = 1 := by
  have h := Abelianization.commutator_subset_ker (GeneralLinearGroup.det.comp φ)
  rw [hG] at h
  exact h (Subgroup.mem_top g)

@[expose] noncomputable def toSLOfPerfect {G : Type*} [Group G] (hG : commutator G = ⊤) {m : ℕ}
    (φ : G →* GL (Fin m) F) : G →* SpecialLinearGroup (Fin m) F where
  toFun g := ⟨(φ g : Matrix (Fin m) (Fin m) F), by
    rw [← GeneralLinearGroup.val_det_apply, det_eq_one_of_perfect hG φ g, Units.val_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    show (φ (a * b) : Matrix (Fin m) (Fin m) F) = (φ a : Matrix (Fin m) (Fin m) F) * (φ b)
    rw [map_mul, Units.val_mul])

@[expose] noncomputable def twistHom {G : Type*} [Group G] (α : MulAut G) (p : ℕ) :
    G →* (Fin p → G) :=
  Pi.monoidHom fun k : Fin p => (α ^ (k : ℕ)).toMonoidHom

@[expose] noncomputable def twistBlock {p : ℕ} (hp3 : 3 ≤ p) {Q : Fin p → Matrix (Fin p) (Fin p) F}
    (hQ : OrthDecomp Q) (Cu : GL (Fin p) F) :
    SpecialLinearGroup (Fin p) F →* SpecialLinearGroup (Fin (p * p)) F :=
  toSLOfPerfect (CFSG.LinearGroups.special_linear_isPerfect (by omega) (Or.inl hp3)).commutator_eq_top
    ((blockHom hQ).comp (twistHom (conjAutSL Cu) p))

theorem coe_twistBlock {p : ℕ} (hp3 : 3 ≤ p) {Q : Fin p → Matrix (Fin p) (Fin p) F}
    (hQ : OrthDecomp Q) (Cu : GL (Fin p) F) (v : SpecialLinearGroup (Fin p) F) :
    ((twistBlock hp3 hQ Cu v : SpecialLinearGroup (Fin (p * p)) F) :
      Matrix (Fin (p * p)) (Fin (p * p)) F) =
        blockMat Q (fun k => ((conjAutSL Cu ^ (k : ℕ)) v : Matrix (Fin p) (Fin p) F)) := rfl

theorem conjAutSL_pow_shiftIdx {p : ℕ} (hp : 0 < p) {Cu : GL (Fin p) F}
    (hαp : conjAutSL Cu ^ p = 1) (v : SpecialLinearGroup (Fin p) F) (k : Fin p) :
    (conjAutSL Cu ^ ((shiftIdx hp k : Fin p) : ℕ)) v = conjAutSL Cu ((conjAutSL Cu ^ (k : ℕ)) v) := by
  rw [shiftIdx]
  simp only
  rw [← pow_eq_pow_mod _ hαp, pow_succ', MulAut.mul_apply]

theorem kr_mul_twist_comm {p : ℕ} (hp : 0 < p) {Q : Fin p → Matrix (Fin p) (Fin p) F}
    {T : Matrix (Fin p) (Fin p) F} (hT : ∀ k, T * Q k = Q (shiftIdx hp k) * T)
    {Cu : GL (Fin p) F} (hαp : conjAutSL Cu ^ p = 1) (v : SpecialLinearGroup (Fin p) F) :
    kr T (Cu : Matrix (Fin p) (Fin p) F) *
        blockMat Q (fun k => ((conjAutSL Cu ^ (k : ℕ)) v : Matrix (Fin p) (Fin p) F)) =
      blockMat Q (fun k => ((conjAutSL Cu ^ (k : ℕ)) v : Matrix (Fin p) (Fin p) F)) *
        kr T (Cu : Matrix (Fin p) (Fin p) F) := by
  refine kr_mul_blockMat_comm (shiftEquiv hp) (fun k => hT k) (fun k => ?_)
  rw [shiftEquiv_apply, conjAutSL_pow_shiftIdx hp hαp, conjAutSL_apply, conjUnit_coe,
    Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.mul_one]

theorem closure_liftSet_of_irreducible {n : ℕ} (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : (p : F) ≠ 0) (hpq : p ∣ Nat.card F - 1) {E : Subgroup (MulAut (projectiveSL n F))}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) (hlin : E ≤ linearAutGroup n F)
    (hirr : ∀ W : Submodule F (Fin n → F), LiftStable E W → W = ⊥ ∨ W = ⊤) :
    Subgroup.closure (liftSet p E) = ⊤ := by
  classical
  have : Finite (MulAut (projectiveSL n F)) := MulEquiv.finite_left
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨e₁, he₁, e₂, he₂, he₂1, he₁₂⟩ := exists_indep_of_card_cube hp hE.2 hcard
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_noncomm_lifts hn hp hp2 hpq hE hlin he₁ he₂ he₂1 he₁₂ hirr
  obtain ⟨x', y', r, sx, sy, ζ, c, A, B, C, u₀, hx'E, hy'E, hrE, hgen, hxA, hyB, hrC, hk⟩ :=
    exists_kron_data_gl hn hp hp2 hpF hE hcard hlin hx hy hxy hirr
  obtain rfl : n = p * p := hk.card_eq_sq
  obtain ⟨P, hAP, hBP, hCP⟩ := exists_kron_model hk
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp0 : 0 < p := hp.pos
  have hKp := compMat_pow_eq hp0 hk.hC P hCP
  have hc0 : c ≠ 0 := by
    intro h0
    apply hk.notPow 0
    rw [zero_pow hp.ne_zero, h0]
  have hxP : (x' : Matrix (Fin (p * p)) (Fin (p * p)) F) *
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * (sx • kr (shiftMat p F) 1) := by
    rw [hxA, Matrix.smul_mul, hAP, Matrix.mul_smul]
  have hyP : (y' : Matrix (Fin (p * p)) (Fin (p * p)) F) *
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * (sy • kr (charMat p ζ⁻¹) 1) := by
    rw [hyB, Matrix.smul_mul, hBP, Matrix.mul_smul]
  have hrP : (r : Matrix (Fin (p * p)) (Fin (p * p)) F) *
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * kr 1 (compMat p c) := by
    rw [hrC]
    exact hCP
  have hxrP : ((x' * r : GL (Fin (p * p)) F) : Matrix (Fin (p * p)) (Fin (p * p)) F) *
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * (sx • kr (shiftMat p F) (compMat p c)) := by
    rw [Units.val_mul, Matrix.mul_assoc, hrP, ← Matrix.mul_assoc, hxP, Matrix.mul_assoc,
      Matrix.smul_mul, kr_mul, Matrix.mul_one, Matrix.one_mul]
  have hyrP : ((y' * r : GL (Fin (p * p)) F) : Matrix (Fin (p * p)) (Fin (p * p)) F) *
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * (sy • kr (charMat p ζ⁻¹) (compMat p c)) := by
    rw [Units.val_mul, Matrix.mul_assoc, hrP, ← Matrix.mul_assoc, hyP, Matrix.mul_assoc,
      Matrix.smul_mul, kr_mul, Matrix.mul_one, Matrix.one_mul]
  have hxrE : conjAut (p * p) F (x' * r) ∈ E := by rw [map_mul]; exact E.mul_mem hx'E hrE
  have hyrE : conjAut (p * p) F (y' * r) ∈ E := by rw [map_mul]; exact E.mul_mem hy'E hrE
  have hrel1 := (relIndex_three_pairs hp0 hx'E hy'E hrE (hcomm _ hx'E _ hy'E) (hcomm _ hx'E _ hrE)
    (hcomm _ hy'E _ hrE) (hE.2 _ hx'E) (hE.2 _ hy'E) (hE.2 _ hrE) hgen hcard).1
  have hgen2 : E ≤ Subgroup.closure ({conjAut (p * p) F (x' * r), conjAut (p * p) F y',
      conjAut (p * p) F r} : Set (MulAut (projectiveSL (p * p) F))) := by
    refine hgen.trans ((Subgroup.closure_le _).2 ?_)
    rintro z (rfl | rfl | rfl)
    · have e : conjAut (p * p) F x' = conjAut (p * p) F (x' * r) * (conjAut (p * p) F r)⁻¹ := by
        rw [map_mul]; group
      rw [SetLike.mem_coe, e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have hgen3 : E ≤ Subgroup.closure ({conjAut (p * p) F (y' * r), conjAut (p * p) F x',
      conjAut (p * p) F r} : Set (MulAut (projectiveSL (p * p) F))) := by
    refine hgen.trans ((Subgroup.closure_le _).2 ?_)
    rintro z (rfl | rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · have e : conjAut (p * p) F y' = conjAut (p * p) F (y' * r) * (conjAut (p * p) F r)⁻¹ := by
        rw [map_mul]; group
      rw [SetLike.mem_coe, e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
    · exact Subgroup.subset_closure (by simp)
  have hrel2 := relIndex_closure_pair hp0 hxrE hy'E hrE (hcomm _ hxrE _ hy'E)
    (hcomm _ hxrE _ hrE) (hcomm _ hy'E _ hrE) (hE.2 _ hxrE) (hE.2 _ hy'E) (hE.2 _ hrE) hgen2 hcard
  have hrel3 := relIndex_closure_pair hp0 hyrE hx'E hrE (hcomm _ hyrE _ hx'E)
    (hcomm _ hyrE _ hrE) (hcomm _ hx'E _ hrE) (hE.2 _ hyrE) (hE.2 _ hx'E) (hE.2 _ hrE) hgen3 hcard
  set K'' : Subgroup (SpecialLinearGroup (Fin (p * p)) F) :=
    (Subgroup.closure (liftSet p E)).comap (conjUnit P) with hK''
  have hr : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  have hrp : ¬ p ∣ ringChar F := by
    intro hd
    have h1 : p = ringChar F := (Nat.prime_dvd_prime_iff_eq hp hr).1 hd
    apply hpF
    rw [h1]
    exact ringChar.Nat.cast_ringChar
  have key : ∀ (a b : GL (Fin (p * p)) F) (Na Nb : Matrix (Fin (p * p)) (Fin (p * p)) F),
      conjAut (p * p) F a ∈ E → conjAut (p * p) F b ∈ E →
      (Subgroup.closure ({conjAut (p * p) F a, conjAut (p * p) F b} :
        Set (MulAut (projectiveSL (p * p) F)))).relIndex E = p →
      (a : Matrix (Fin (p * p)) (Fin (p * p)) F) * (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
        (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * Na →
      (b : Matrix (Fin (p * p)) (Fin (p * p)) F) * (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
        (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * Nb →
      ∀ g₀ : SpecialLinearGroup (Fin (p * p)) F, g₀ ^ ringChar F = 1 →
      Na * (g₀ : Matrix (Fin (p * p)) (Fin (p * p)) F) =
        (g₀ : Matrix (Fin (p * p)) (Fin (p * p)) F) * Na →
      Nb * (g₀ : Matrix (Fin (p * p)) (Fin (p * p)) F) =
        (g₀ : Matrix (Fin (p * p)) (Fin (p * p)) F) * Nb → g₀ ∈ K'' := by
    intro a b Na Nb haE hbE hrel hMa hMb g₀ hg₀ hga hgb
    refine Subgroup.mem_comap.2 (Subgroup.subset_closure ⟨⟨ringChar F, hrp, ?_⟩,
      Subgroup.closure {conjAut (p * p) F a, conjAut (p * p) F b}, closure_pair_le haE hbE, hrel,
      fun A' hA' => ?_⟩)
    · rw [← map_pow, hg₀, map_one]
    · refine mem_commGL.1 (mem_of_conjAut_mem_pair (by omega)
        (K := commGL ((conjUnit P g₀ : SpecialLinearGroup (Fin (p * p)) F) :
          Matrix (Fin (p * p)) (Fin (p * p)) F)) (scalar_mem_commGL _)
        (mem_commGL.2 (commute_conjUnit P hMa hga)) (mem_commGL.2 (commute_conjUnit P hMb hgb)) hA')
  let Cu : GL (Fin p) F :=
    ⟨compMat p c, c⁻¹ • compMat p c ^ (p - 1), by
      rw [Matrix.mul_smul, ← pow_succ', Nat.sub_add_cancel hp0, hKp, smul_smul,
        inv_mul_cancel₀ hc0, one_smul], by
      rw [Matrix.smul_mul, ← pow_succ, Nat.sub_add_cancel hp0, hKp, smul_smul,
        inv_mul_cancel₀ hc0, one_smul]⟩
  have hCu : (Cu : Matrix (Fin p) (Fin p) F) = compMat p c := rfl
  have hCp : ((Cu ^ p : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = c • 1 := by
    rw [Units.val_pow_eq_pow_val, hCu, hKp]
  have hαp := conjAutSL_pow_eq_one hCp
  have hε : IsPrimitiveRoot ζ⁻¹ p := hk.prim.inv
  have hεp : ζ⁻¹ ^ p = 1 := hε.pow_eq_one
  have hε0 : ζ⁻¹ ≠ 0 := inv_ne_zero (hk.prim.ne_zero hp.ne_zero)
  have htr : ∀ φ : SpecialLinearGroup (Fin p) F →* SpecialLinearGroup (Fin (p * p)) F,
      (∀ (i j : Fin p) (hij : i ≠ j) (c : F),
        φ (SpecialLinearGroup.transvection hij c) ∈ K'') → ∀ u, φ u ∈ K'' := by
    intro φ hφ u
    have htop := Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
      (ι := Fin p) (K := F)
    have hle : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
        Matrix.TransvectionStruct (Fin p) F → SpecialLinearGroup (Fin p) F)) ≤ K''.comap φ := by
      rw [Subgroup.closure_le]
      rintro _ ⟨t, rfl⟩
      exact hφ t.i t.j t.hij t.c
    rw [htop] at hle
    exact hle (Subgroup.mem_top u)
  have hpow : ∀ (φ : SpecialLinearGroup (Fin p) F →* SpecialLinearGroup (Fin (p * p)) F)
      (i j : Fin p) (hij : i ≠ j) (c : F),
      φ (SpecialLinearGroup.transvection hij c) ^ ringChar F = 1 := by
    intro φ i j hij c
    rw [← map_pow, transvection_pow_ringChar, map_one]
  have hd : ∀ u : SpecialLinearGroup (Fin p) F, dHom u ∈ K'' := by
    refine htr dHom fun i j hij c => key x' y' _ _ hx'E hy'E hrel1 hxP hyP _ (hpow _ i j hij c)
      ?_ ?_
    · rw [coe_dHom, Matrix.smul_mul, Matrix.mul_smul, kr_mul, kr_mul, Matrix.one_mul,
        Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
    · rw [coe_dHom, Matrix.smul_mul, Matrix.mul_smul, kr_mul, kr_mul, Matrix.one_mul,
        Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  have hE' : ∀ v : SpecialLinearGroup (Fin p) F, ∃ s ∈ K'',
      (s : Matrix (Fin (p * p)) (Fin (p * p)) F) = blockMat (fun k => Matrix.single k k 1)
        (fun k => ((conjAutSL Cu ^ (k : ℕ)) v : Matrix (Fin p) (Fin p) F)) := by
    intro v
    refine ⟨twistBlock hp3 orthDecomp_single Cu v, htr _ (fun i j hij c => ?_) v, rfl⟩
    refine key (x' * r) y' _ _ hxrE hy'E hrel2 hxrP hyP _ (hpow _ i j hij c) ?_ ?_
    · rw [coe_twistBlock, Matrix.smul_mul, Matrix.mul_smul]
      congr 1
      exact kr_mul_twist_comm hp0 (fun k => shiftMat_mul_single hp0 k) hαp _
    · rw [coe_twistBlock, Matrix.smul_mul, Matrix.mul_smul]
      congr 1
      exact kr_one_mul_blockMat_comm (fun k => diagonal_mul_single _ k) _
  have hP' : ∀ v : SpecialLinearGroup (Fin p) F, ∃ s ∈ K'',
      (s : Matrix (Fin (p * p)) (Fin (p * p)) F) = blockMat (fourierProj ζ⁻¹)
        (fun k => ((conjAutSL Cu ^ (k : ℕ)) v : Matrix (Fin p) (Fin p) F)) := by
    intro v
    refine ⟨twistBlock hp3 (orthDecomp_fourierProj hpF hε) Cu v, htr _ (fun i j hij c => ?_) v,
      rfl⟩
    refine key (y' * r) x' _ _ hyrE hx'E hrel3 hyrP hxP _ (hpow _ i j hij c) ?_ ?_
    · rw [coe_twistBlock, Matrix.smul_mul, Matrix.mul_smul]
      congr 1
      exact kr_mul_twist_comm hp0 (fun k => charMat_mul_fourierProj hp0 hεp hε0 k) hαp _
    · rw [coe_twistBlock, Matrix.smul_mul, Matrix.mul_smul]
      congr 1
      exact kr_one_mul_blockMat_comm (fun k => shiftMat_comm_fourierProj hp0 hεp hε0 k) _
  have htop : K'' = ⊤ := eq_top_of_kron_families hp3 hpF hε hCu hCp hd hE' hP'
  rw [eq_top_iff]
  intro g _
  have h1 : conjUnit P⁻¹ g ∈ K'' := htop ▸ Subgroup.mem_top _
  have h2 : conjUnit P (conjUnit P⁻¹ g) ∈ Subgroup.closure (liftSet p E) := h1
  rwa [conjUnit_conjUnit_inv_self] at h2

end Irreducible

theorem seitzHyperGamma_eq_top_of_linearDiag {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) (hL : LinearDiag p E) :
    seitzHyperGamma p E = ⊤ := by
  obtain ⟨n, F, _, _, θ, hn, hpF, hpq, hlin⟩ := hL
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj := modelAut_injective hperf θ
  have hE' : IsElemAbelian p (E.map (modelAut θ)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hcard' : Nat.card (E.map (modelAut θ)) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective hinj, hcard]
  by_cases hred : ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧ LiftStable (E.map (modelAut θ)) W
  · obtain ⟨W, hW0, hWt, hWE⟩ := hred
    have hE1 : E ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.card_bot] at hcard
      have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    exact seitzHyperGamma_eq_top_of_diagReducible hperf hp hE hE1
      (diagReducible_of_liftStable hn hp hpF θ hE' hlin hW0 hWt hWE)
  · have hirr : ∀ W : Submodule F (Fin n → F), LiftStable (E.map (modelAut θ)) W →
        W = ⊥ ∨ W = ⊤ := by
      intro W hW
      by_contra hcon
      push Not at hcon
      exact hred ⟨W, hcon.1, hcon.2, hW⟩
    exact seitzHyperGamma_eq_top_of_closure_liftSet hperf (isPGroup_of_isElemAbelian hE) θ hlin
      (closure_liftSet_of_irreducible hn hp hp2 hpF hpq hE' hcard' hlin hirr)

end CFSG.LieType.SeitzGeneration.QuasiHigh2
