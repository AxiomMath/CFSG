module

public import CFSG.LieType.SeitzGeneration.QuasiHigh2
public import CFSG.LieType.SeitzGeneration.QuasiHigh3Linear
public import CFSG.LieType.SeitzGeneration.SingerTorusLinear
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeHeisOuter

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh5

open Matrix CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh CFSG.LieType.SeitzGeneration.QuasiHigh2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open CFSG.RankThree.PartOne.CTP (slSub mem_slSub)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

section Cover

variable {G K : Type*} [Group G] [Group K]

theorem hom_eq_of_mk_eq (hG : commutator G = ⊤) (f₁ f₂ : G →* K)
    (h : ∀ g, ((f₁ g : K) : K ⧸ Subgroup.center K) = ((f₂ g : K) : K ⧸ Subgroup.center K)) :
    f₁ = f₂ := by
  have hz : ∀ g, (f₁ g)⁻¹ * f₂ g ∈ Subgroup.center K := fun g => QuotientGroup.eq.1 (h g)
  let δ : G →* Subgroup.center K :=
    { toFun := fun g => ⟨(f₁ g)⁻¹ * f₂ g, hz g⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hza := Subgroup.mem_center_iff.mp (hz a) ((f₁ b)⁻¹)
        change (f₁ (a * b))⁻¹ * f₂ (a * b) = (f₁ a)⁻¹ * f₂ a * ((f₁ b)⁻¹ * f₂ b)
        calc (f₁ (a * b))⁻¹ * f₂ (a * b)
            = ((f₁ b)⁻¹ * ((f₁ a)⁻¹ * f₂ a)) * f₂ b := by
              rw [map_mul, map_mul]; group
          _ = (f₁ a)⁻¹ * f₂ a * ((f₁ b)⁻¹ * f₂ b) := by
              rw [hza]; group }
  have hle : commutator G ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [hG] at hle
  ext g
  have h1 : δ g = 1 := hle (Subgroup.mem_top g)
  have h2 : (f₁ g)⁻¹ * f₂ g = 1 := congrArg Subtype.val h1
  exact inv_mul_eq_one.1 h2

theorem seitzHyperGamma_eq_top_of_cover (hG : commutator G = ⊤) (φ : G →* K)
    (hφ : Function.Surjective φ) {p : ℕ} (hp : p.Prime) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) {S : Set G}
    (hS : Subgroup.closure S = ⊤)
    (hfix : ∀ g ∈ S, ∃ e ∈ E, e ≠ 1 ∧ ∃ α : G →* G, α g = g ∧
      ∀ h, ((e (φ h) : K) : K ⧸ Subgroup.center K) = ((φ (α h) : K) : K ⧸ Subgroup.center K)) :
    seitzHyperGamma p E = ⊤ := by
  rw [eq_top_iff]
  have hmap : (⊤ : Subgroup K) ≤ (Subgroup.closure S).map φ := by
    rw [hS, Subgroup.map_top_of_surjective φ hφ]
  refine hmap.trans ?_
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨e, he, he1, α, hαg, hα⟩ := hfix g hg
  have heq := hom_eq_of_mk_eq hG ((e : K ≃* K).toMonoidHom.comp φ) (φ.comp α) hα
  have hfixg : e (φ g) = φ g := by
    have h1 := DFunLike.congr_fun heq g
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply] at h1
    rw [h1, hαg]
  have hmem := CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.mem_fixedPoints_zpowers hfixg
  exact (le_iSup₂_of_le (f := fun (F : Subgroup (MulAut K)) (_ : F ≤ E ∧ F.relIndex E = p) =>
      fixedPoints F) (Subgroup.zpowers e) ⟨(Subgroup.zpowers_le).2 he,
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.relIndex_zpowers hp hE hcard he he1⟩
      le_rfl) hmem

end Cover

section SLCover

variable {K : Type*} [Group K]

theorem model_mk_apply {P : Type*} [Group P] (θ : K ⧸ Subgroup.center K ≃* P) (f : MulAut K)
    (x : K) : θ ((f x : K) : K ⧸ Subgroup.center K) =
      modelAut θ f (θ (x : K ⧸ Subgroup.center K)) := by
  rw [modelAut_apply, MulEquiv.symm_apply_apply, quotAut_mk]

theorem modelAut_trans {P : Type*} [Group P] (θ : K ⧸ Subgroup.center K ≃* P) (α : MulAut P)
    (f : MulAut K) : modelAut (θ.trans α) f = MulAut.congr α (modelAut θ f) := by
  ext x
  simp only [modelAut_apply, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply]

theorem exists_sl_lift (hperf : commutator K = ⊤) {m : ℕ} {F : Type} [Field F] [Finite F]
    (hm : 2 ≤ m) (hsep : CFSG.LieType.Steinberg.CentralExt.SLClosed.Separating m F)
    (θ : K ⧸ Subgroup.center K ≃* projectiveSL (m + 1) F) :
    ∃ φ : SpecialLinearGroup (Fin (m + 1)) F →* K, Function.Surjective φ ∧
      ∀ g, θ ((φ g : K) : K ⧸ Subgroup.center K) = proj (m + 1) F g := by
  haveI : Group.IsPerfect K := ⟨hperf⟩
  set Ψ := LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) F with hΨ
  let ρ : K →* ProjectiveSpecialLinearGroup (Fin (m + 1)) F :=
    (Ψ.symm.toMonoidHom.comp θ.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center K))
  have hρ : Function.Surjective ρ :=
    Ψ.symm.surjective.comp (θ.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : ρ.ker ≤ Subgroup.center K := by
    intro x hx
    have h1 : Ψ.symm (θ (x : K ⧸ Subgroup.center K)) = 1 := hx
    have h2 : ((x : K) : K ⧸ Subgroup.center K) = 1 := by
      have h3 : θ (x : K ⧸ Subgroup.center K) = 1 := by
        rw [← Ψ.symm.map_eq_one_iff]
        exact h1
      exact (θ.map_eq_one_iff).1 h3
    exact (QuotientGroup.eq_one_iff x).1 h2
  obtain ⟨φ, hφ, hφρ⟩ := exists_sl_cover_hom hm hsep ρ hρ hker
  refine ⟨φ, hφ, fun g => ?_⟩
  have h1 : Ψ.symm (θ ((φ g : K) : K ⧸ Subgroup.center K)) =
      QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) g := hφρ g
  have h2 : θ ((φ g : K) : K ⧸ Subgroup.center K) =
      Ψ (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) g) := by
    rw [← h1, MulEquiv.apply_symm_apply]
  rw [h2]
  rfl

theorem seitzHyperGamma_eq_top_of_slModel {n : ℕ} {F : Type} [Field F] (hn : 3 ≤ n)
    (θ : K ⧸ Subgroup.center K ≃* projectiveSL n F) (φ : SpecialLinearGroup (Fin n) F →* K)
    (hφ : Function.Surjective φ)
    (hφθ : ∀ g, θ ((φ g : K) : K ⧸ Subgroup.center K) = proj n F g) {p : ℕ} (hp : p.Prime)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    {S : Set (SpecialLinearGroup (Fin n) F)} (hS : Subgroup.closure S = ⊤)
    (hfix : ∀ g ∈ S, ∃ e ∈ E, e ≠ 1 ∧ ∃ α : SpecialLinearGroup (Fin n) F →*
      SpecialLinearGroup (Fin n) F, α g = g ∧ ∀ h, modelAut θ e (proj n F h) = proj n F (α h)) :
    seitzHyperGamma p E = ⊤ := by
  refine seitzHyperGamma_eq_top_of_cover
    (CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le hn) φ hφ hp hE hcard hS ?_
  intro g hg
  obtain ⟨e, he, he1, α, hαg, hα⟩ := hfix g hg
  refine ⟨e, he, he1, α, hαg, fun h => θ.injective ?_⟩
  rw [model_mk_apply, hφθ, hφθ, hα]

end SLCover

section Field

variable {n : ℕ} {F : Type} [Field F]

theorem map_slConjugation (σ : F ≃+* F) (M : GL (Fin n) F) (B : SpecialLinearGroup (Fin n) F) :
    SpecialLinearGroup.map σ.toRingHom (slConjugation n F M B) =
      slConjugation n F (GeneralLinearGroup.map (σ : F →+* F) M)
        (SpecialLinearGroup.map σ.toRingHom B) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, slConjugation_matrix, slConjugation_matrix,
    SpecialLinearGroup.map_apply_coe, ← map_inv, QuasiHigh3.coe_GLmap, QuasiHigh3.coe_GLmap,
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul]
  rfl

theorem map_eq_of_mem_slSub (σ : F ≃+* F) {B : SpecialLinearGroup (Fin n) F}
    (hB : B ∈ slSub n (semilinearFixedSubfield σ)) :
    SpecialLinearGroup.map σ.toRingHom B = B := by
  apply Subtype.ext
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact (mem_slSub.1 hB) i j

variable {K : Type} [Group K] [Finite K]

theorem seitzHyperGamma_eq_top_linear_field
    (hperf : commutator K = ⊤) {m : ℕ} [Finite F] {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hF : Nat.card F = ℓ ^ f) (hm : 2 ≤ m)
    (hsep : CFSG.LieType.Steinberg.CentralExt.SLClosed.Separating m F) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (θ₀ : K ⧸ Subgroup.center K ≃* projectiveSL (m + 1) F)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (hout : ¬ E.map (modelAut θ₀) ≤ linearAutGroup (m + 1) F) :
    seitzHyperGamma p E = ⊤ := by
  classical
  have hn : 3 ≤ m + 1 := by omega
  have hinj := modelAut_injective hperf θ₀
  have hĒ : IsElemAbelian p (E.map (modelAut θ₀)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hĒc : Nat.card (E.map (modelAut θ₀)) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hinj, hcard]
  obtain ⟨h, σ, x, c, hσ, hKk, hσout, hσE, hxE, hxσ, hxns, hxp, hcσ⟩ :=
    exists_field_normal_form hℓ hf hn hF hp hp2 hpℓ hĒ hĒc hout
  set θ : K ⧸ Subgroup.center K ≃* projectiveSL (m + 1) F := θ₀.trans h⁻¹ with hθ
  have hlift : ∀ β ∈ (E.map (modelAut θ₀)).map (MulAut.congr h⁻¹).toMonoidHom,
      ∃ e ∈ E, modelAut θ e = β := by
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨e, he, modelAut_trans θ₀ h⁻¹ e⟩
  obtain ⟨e₁, he₁, he₁σ⟩ := hlift _ hσE
  obtain ⟨eₓ, heₓ, heₓx⟩ := hlift _ hxE
  set k : Subfield F := semilinearFixedSubfield σ with hkdef
  have hk : ∀ y, y ∈ k ↔ σ y = y := fun y => Iff.rfl
  have hn0 : 0 < m + 1 := by omega
  have hc0 : c ≠ 0 :=
    ne_zero_of_gl_coe_eq_smul hn0 (G := x ^ p) (a := c) (by
      rw [Units.val_pow_eq_pow_val]
      exact hxp)
  obtain ⟨μ, hμ⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq σ (c := c⁻¹) (by rw [map_inv₀, hcσ])
  rw [hσ] at hμ
  have hμ0 : μ ≠ 0 := by
    intro h0
    have h1 : ∏ i ∈ Finset.range p, (σ ^ i) μ = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hp.pos) (by simp [h0])
    rw [hμ] at h1
    exact inv_ne_zero hc0 h1
  obtain ⟨M₀, hdet, hM₀⟩ := exists_fixed_matrix_smul hp hℓ hf hF σ hσ hxσ hxp
    (by rw [hμ]; exact inv_mul_cancel₀ hc0)
  let M : GL (Fin (m + 1)) F := Matrix.nonsingInvUnit M₀ hdet
  let G : GL (Fin (m + 1)) F := GeneralLinearGroup.scalar (Fin (m + 1)) (Units.mk0 μ hμ0) * x
  have hGcoe : (G : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      μ • (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
    rw [Units.val_mul, scalarGL_coe_eq_smul, Matrix.smul_mul, Matrix.one_mul]
    rfl
  have hGconj : conjAut (m + 1) F G = conjAut (m + 1) F x := by
    rw [map_mul, conjAut_scalar, one_mul]
  have hGns : ∀ a : F, (G : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ≠ a • 1 := by
    intro a ha
    apply hxns (μ⁻¹ * a)
    rw [hGcoe] at ha
    have h1 := congrArg (fun Z => μ⁻¹ • Z) ha
    simpa [smul_smul, hμ0] using h1
  have hGM : (G : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map σ = M := by
    rw [hGcoe]
    exact hM₀
  have hGM' : G * GeneralLinearGroup.map (σ : F →+* F) M = M :=
    Units.ext (by rw [Units.val_mul, QuasiHigh3.coe_GLmap]; exact hGM)
  have hpair := pairSL_closure (k := k) hp hp2 hKk hn M
    (slConjugation_map_ne_of_unit σ hk G hGns M hGM)
  have hf1 : fieldAut (m + 1) F σ ≠ 1 := fun h' => hσout 1 (by rw [h', map_one])
  have he₁1 : e₁ ≠ 1 := by
    rintro rfl
    rw [map_one] at he₁σ
    exact hf1 he₁σ.symm
  have he₂ : eₓ * e₁ ∈ E := E.mul_mem heₓ he₁
  have he₂β : modelAut θ (eₓ * e₁) = conjAut (m + 1) F G * fieldAut (m + 1) F σ := by
    rw [map_mul, heₓx, he₁σ, hGconj]
  have he₂1 : eₓ * e₁ ≠ 1 := by
    intro h1
    rw [h1, map_one] at he₂β
    apply hσout G⁻¹
    have h2 : fieldAut (m + 1) F σ = (conjAut (m + 1) F G)⁻¹ :=
      eq_inv_of_mul_eq_one_right he₂β.symm
    rw [h2, map_inv]
  obtain ⟨φ, hφ, hφθ⟩ := exists_sl_lift hperf hm hsep θ
  refine seitzHyperGamma_eq_top_of_slModel hn θ φ hφ hφθ hp hE hcard hpair ?_
  rintro g (hg | ⟨B, hB, rfl⟩)
  · refine ⟨e₁, he₁, he₁1, SpecialLinearGroup.map σ.toRingHom, map_eq_of_mem_slSub σ hg,
      fun h' => ?_⟩
    rw [he₁σ, fieldAut_proj]
  · refine ⟨eₓ * e₁, he₂, he₂1,
      (slConjugation (m + 1) F G).toMonoidHom.comp (SpecialLinearGroup.map σ.toRingHom), ?_,
      fun h' => ?_⟩
    · change slConjugation (m + 1) F G (SpecialLinearGroup.map σ.toRingHom
        (slConjugation (m + 1) F M B)) = slConjugation (m + 1) F M B
      rw [map_slConjugation, map_eq_of_mem_slSub σ hB, ← MulAut.mul_apply, ← map_mul, hGM']
    · rw [he₂β, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
      rfl

end Field

section Heis

variable {F : Type} [Field F]

theorem companionMat_three_eq_heisC (c : F) : companionMat 3 c = heisC c := by
  ext i j
  rw [companionMat_apply]
  fin_cases i <;> fin_cases j <;> simp [heisC] <;> decide

theorem companionMat_one_mul_heisShiftMat {p : ℕ} [NeZero p] :
    companionMat p (1 : F) * heisShiftMat F p = 1 := by
  refine Matrix.ext_of_mulVec_single fun k => ?_
  rw [← Matrix.mulVec_mulVec, CFSG.LieType.SeitzGeneration.heisShiftMat_mulVec_single,
    companionMat_mulVec_single, Matrix.one_mulVec, Equiv.apply_symm_apply]
  simp

theorem comm_of_comm_of_mul_eq_one {n : ℕ} {g S C : Matrix (Fin n) (Fin n) F} (hCS : C * S = 1)
    (hg : g * S = S * g) : g * C = C * g := by
  have hSC : S * C = 1 := mul_eq_one_comm.1 hCS
  calc g * C = C * S * g * C := by rw [hCS, Matrix.one_mul]
    _ = C * (g * S) * C := by rw [Matrix.mul_assoc C S g, ← hg]
    _ = C * g * (S * C) := by simp only [Matrix.mul_assoc]
    _ = C * g := by rw [hSC, Matrix.mul_one]

theorem singerTorusGen_three [Finite F] (hF : 4 < Nat.card F) (h3 : 3 ∣ Nat.card F - 1) :
    SingerTorusGen F 3 := by
  intro c hc H hdiag hcomm
  obtain ⟨ω, hω⟩ := exists_primitiveRoot_of_dvd_card_sub_one Nat.prime_three h3
  have hω1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hω2 : ω ^ 2 + ω + 1 = 0 := by
    have h1 := hω.geom_sum_eq_zero (by norm_num : 1 < 3)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at h1
    linear_combination h1
  have hnc : ¬ ∃ μ : F, μ ^ 3 = (c : F) := by
    rintro ⟨μ, hμ⟩
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hμ
      exact c.ne_zero hμ.symm
    exact hc ⟨Units.mk0 μ hμ0, Units.ext (by simpa using hμ)⟩
  refine CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.eq_top_of_torus_centralizer_noncube
    hω2 hω1 hnc hF (fun a b d h => hdiag _ ⟨![a, b, d], ?_⟩) (fun k hk => hcomm k ?_)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [diagSL]
  · rwa [companionMat_three_eq_heisC]

theorem comm_conjUnit_of_inv_conj {p : ℕ} {P : GL (Fin p) F} {a A : Matrix (Fin p) (Fin p) F}
    (hA : ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * a * (P : Matrix (Fin p) (Fin p) F) =
      A) {g : SpecialLinearGroup (Fin p) F} (hg : (g : Matrix (Fin p) (Fin p) F) * A = A * g) :
    ((conjUnit P g : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) * a =
      a * (conjUnit P g : SpecialLinearGroup (Fin p) F) := by
  rw [conjUnit_coe, heisGen_eq_conj_of_inv_conj P hA, heisGen_conj_mul, heisGen_conj_mul, hg]

theorem diag_comm_smul_heisDiagMat {p : ℕ} {t : Fin p → F} (ξ ω : F) :
    Matrix.diagonal t * (ξ • heisDiagMat ω) = (ξ • heisDiagMat ω) * Matrix.diagonal t := by
  rw [heisDiagMat, ← Matrix.diagonal_smul]
  exact heisGen_diag_comm _ _

theorem eq_top_of_comap_conjUnit {p : ℕ} {H : Subgroup (SpecialLinearGroup (Fin p) F)}
    (P : GL (Fin p) F) (h : H.comap (conjUnit P) = ⊤) : H = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have h1 : conjUnit P⁻¹ g ∈ H.comap (conjUnit P) := h ▸ Subgroup.mem_top _
  rwa [Subgroup.mem_comap, heisGen_conjUnit_conjUnit_inv] at h1

theorem closure_comm_heis_eq_top {p : ℕ} (hp : p.Prime) (hT : TorusFourierGen F p)
    (hSg : SingerTorusGen F p) {ω c : F} (hω : IsPrimitiveRoot ω p) {x y : GL (Fin p) F}
    (hxp : (x : Matrix (Fin p) (Fin p) F) ^ p = c • 1)
    (hyp : (y : Matrix (Fin p) (Fin p) F) ^ p = 1)
    (hrel : (y : Matrix (Fin p) (Fin p) F) * x = ω • ((x : Matrix (Fin p) (Fin p) F) * y)) :
    Subgroup.closure ({g : SpecialLinearGroup (Fin p) F |
        (g : Matrix (Fin p) (Fin p) F) * x = x * g} ∪
      {g | (g : Matrix (Fin p) (Fin p) F) * y = y * g}) = ⊤ := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set H := Subgroup.closure ({g : SpecialLinearGroup (Fin p) F |
        (g : Matrix (Fin p) (Fin p) F) * x = x * g} ∪
      {g | (g : Matrix (Fin p) (Fin p) F) * y = y * g}) with hH
  have hζ : ∃ ζ : F, IsPrimitiveRoot ζ p := ⟨ω, hω⟩
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : ((x ^ p : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) ≠ 0 := Units.ne_zero _
    rw [Units.val_pow_eq_pow_val, hxp, h0, zero_smul] at h1
    exact h1 rfl
  have hdiagP : ∀ (P : GL (Fin p) F) (ξ : F),
      ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * (y : Matrix (Fin p) (Fin p) F) *
        (P : Matrix (Fin p) (Fin p) F) = ξ • heisDiagMat ω →
      ∀ g : SpecialLinearGroup (Fin p) F,
        (∃ t : Fin p → F, (g : Matrix (Fin p) (Fin p) F) = Matrix.diagonal t) →
          g ∈ H.comap (conjUnit P) := by
    rintro P ξ hyP g ⟨t, ht⟩
    refine Subgroup.subset_closure (Or.inr ?_)
    refine comm_conjUnit_of_inv_conj hyP ?_
    rw [ht]
    exact diag_comm_smul_heisDiagMat ξ ω
  by_cases hcp : ∃ μ : F, μ ^ p = c
  ·
    obtain ⟨μ, hμ⟩ := hcp
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hμ
      exact hc0 hμ.symm
    set x' : GL (Fin p) F := GeneralLinearGroup.scalar (Fin p) (Units.mk0 μ hμ0)⁻¹ * x with hx'
    have hx'coe : (x' : Matrix (Fin p) (Fin p) F) = μ⁻¹ • (x : Matrix (Fin p) (Fin p) F) := by
      rw [hx', Units.val_mul, scalarGL_coe_eq_smul, Matrix.smul_mul, Matrix.one_mul]
      simp
    have hxx' : (x : Matrix (Fin p) (Fin p) F) = μ • (x' : Matrix (Fin p) (Fin p) F) := by
      rw [hx'coe, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
    have hx'p : (x' : Matrix (Fin p) (Fin p) F) ^ p = 1 := by
      rw [hx'coe, smul_pow, hxp, smul_smul, inv_pow, hμ, inv_mul_cancel₀ hc0, one_smul]
    have hrel' : (y : Matrix (Fin p) (Fin p) F) * x' =
        ω • ((x' : Matrix (Fin p) (Fin p) F) * y) := by
      rw [hx'coe, Matrix.mul_smul, hrel, Matrix.smul_mul, smul_comm]
    obtain ⟨P, ξ, -, hyP, hxP⟩ := exists_heisenberg_basis_gl_p hp hω hζ (c := 1)
      (by rw [hx'p, one_smul]) hyp hrel'
    refine eq_top_of_comap_conjUnit P (hT ω hω _ (hdiagP P ξ hyP) fun g ⟨t, ht⟩ => ?_)
    refine Subgroup.subset_closure (Or.inl ?_)
    have hcomm := comm_conjUnit_of_inv_conj hxP (comm_of_comm_of_mul_eq_one
      companionMat_one_mul_heisShiftMat (heisGen_comm_shift hω ht))
    change ((conjUnit P g : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) * x =
      x * (conjUnit P g : SpecialLinearGroup (Fin p) F)
    rw [hxx', Matrix.mul_smul, hcomm, Matrix.smul_mul]
  ·
    obtain ⟨P, ξ, -, hyP, hxP⟩ := exists_heisenberg_basis_gl_p hp hω hζ hxp hyp hrel
    have hnc : ¬ ∃ μ : Fˣ, μ ^ p = Units.mk0 c hc0 := by
      rintro ⟨μ, hμ⟩
      exact hcp ⟨μ, by rw [← Units.val_pow_eq_pow_val, hμ, Units.val_mk0]⟩
    refine eq_top_of_comap_conjUnit P (hSg (Units.mk0 c hc0) hnc _ (hdiagP P ξ hyP)
      fun g hg => ?_)
    exact Subgroup.subset_closure (Or.inl (comm_conjUnit_of_inv_conj hxP hg))

end Heis

section Dichotomy

variable {n : ℕ} {F : Type} [Field F]

@[expose] def stabGL (W : Submodule F (Fin n → F)) : Subgroup (GL (Fin n) F) where
  carrier := {A | (∀ w ∈ W, (A : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W) ∧
    ∀ w ∈ W, ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W}
  one_mem' := ⟨fun w hw => by simpa using hw, fun w hw => by simpa using hw⟩
  mul_mem' := by
    rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact hA1 _ (hB1 w hw)
    · rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
      exact hB2 _ (hA2 w hw)
  inv_mem' := by
    rintro A ⟨hA1, hA2⟩
    exact ⟨hA2, by simpa using hA1⟩

theorem exists_heis_pair_of_irreducible [Finite F] (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup (MulAut (projectiveSL n F))} (hE1 : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hlin : E ≤ linearAutGroup n F) (hpn : p ∣ n)
    (hpq : p ∣ Nat.card F - 1)
    (hirr : ∀ W : Submodule F (Fin n → F), LiftStable E W → W = ⊥ ∨ W = ⊤) :
    n = p ∧ ∃ (x y : GL (Fin n) F) (ω c : F), conjAut n F x ∈ E ∧ conjAut n F x ≠ 1 ∧
      conjAut n F y ∈ E ∧ conjAut n F y ≠ 1 ∧ IsPrimitiveRoot ω p ∧
      (x : Matrix (Fin n) (Fin n) F) ^ p = c • 1 ∧ (y : Matrix (Fin n) (Fin n) F) ^ p = 1 ∧
      (y : Matrix (Fin n) (Fin n) F) * x = ω • ((x : Matrix (Fin n) (Fin n) F) * y) := by
  classical
  have hn0 : 0 < n := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e₁, he₁, e₂, he₂, he₂1, he₁₂⟩ := exists_independent_pair hp E hE1.2 hc
  obtain ⟨X, rfl⟩ := mem_linearAutGroup_iff.1 (hlin he₁)
  obtain ⟨Y, rfl⟩ := mem_linearAutGroup_iff.1 (hlin he₂)
  obtain ⟨i, j, z₀, hij, hz₀c, hz₀p⟩ := exists_pth_root_element hn hp hp2 hE1 he₁ he₂
  have hz₀E : conjAut n F z₀ ∈ E := by
    rw [hz₀c]
    exact E.mul_mem (E.pow_mem he₁ i) (E.pow_mem he₂ j)
  have hē₀ : conjAut n F z₀ ≠ 1 := by
    rw [hz₀c]
    exact pow_mul_pow_ne_one_of_indep hp (hE1.2 _ he₁) (hE1.2 _ he₂) he₂1 he₁₂ hij
  have hz₀pM : (z₀ : Matrix (Fin n) (Fin n) F) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hz₀p, Units.val_one]
  obtain ⟨ξ, v, -, hv0, hzv⟩ := exists_eigenvector_of_pow_eq_one hp.pos
    (exists_primitiveRoot_of_dvd_card_sub_one hp hpq) hn0 hz₀pM
  have hz₀ns : ∀ a : F, (z₀ : Matrix (Fin n) (Fin n) F) ≠ a • 1 := by
    intro a ha
    obtain ⟨u, hu⟩ := exists_scalarGL_of_gl_coe_eq_smul hn0 ha
    apply hē₀
    rw [← hu, conjAut_scalar]
  obtain ⟨e'', he''E, he''⟩ := exists_notMem_zpowers_of_card_sq hp hE1.2 hc hz₀E hē₀
  obtain ⟨z', rfl⟩ := mem_linearAutGroup_iff.1 (hlin he''E)
  have hz'1 : conjAut n F z' ≠ 1 := fun h => he'' (h ▸ Subgroup.one_mem _)
  have hgen := zpowers_sup_zpowers_eq_of_card_sq hp hE1.2 hc hz₀E hē₀ he''E he''
  obtain ⟨ζ, hζ⟩ := exists_scalarGL_comm hn hE1 he''E hz₀E
  obtain ⟨c', hc'⟩ := exists_scalarGL_pow hn hE1 he''E
  have hζp : ζ ^ p = 1 := by
    have h1 := qcomm_pow_eq_one (A := z') (B := z₀) (mul_scalarGL_comm ζ) (mul_scalarGL_comm c')
      hζ hc'
    rw [← map_pow] at h1
    exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2.scalarGL_injective hn0
      (by rw [h1, map_one])
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [h1, map_one, one_mul] at hζ
    set S : Set (GL (Fin n) F) := {z₀, z'} ∪ Set.range (GeneralLinearGroup.scalar (Fin n))
      with hS
    have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
      intro x hx y hy
      simp only [hS, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_range] at hx hy
      rcases hx with (rfl | rfl) | ⟨c, rfl⟩ <;> rcases hy with (rfl | rfl) | ⟨d, rfl⟩
      all_goals first
        | rfl
        | exact hζ
        | exact hζ.symm
        | exact (mul_scalarGL_comm _ _).symm
        | exact mul_scalarGL_comm _ _
    have hK : ∀ c : Fˣ, GeneralLinearGroup.scalar (Fin n) c ∈ Subgroup.closure S := fun c =>
      Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
    have hz₀K : z₀ ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inl (Or.inl rfl))
    have hz'K : z' ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inl (Or.inr rfl))
    letI : CommGroup (Subgroup.closure S) :=
      Subgroup.closureCommGroupOfComm fun x hx y hy _ => hSc x hx y hy
    let W : Submodule F (Fin n → F) :=
      LinearMap.ker (Matrix.toLin' ((z₀ : Matrix (Fin n) (Fin n) F) - ξ • 1))
    have hW : ∀ w, w ∈ W ↔ (z₀ : Matrix (Fin n) (Fin n) F) *ᵥ w = ξ • w := fun w => by
      simp [W, LinearMap.mem_ker, Matrix.toLin'_apply, sub_eq_zero]
    have hWs : LiftStable E W := by
      intro A hA w hw
      have hAK := mem_of_conjAut_mem_of_sup_eq hn hgen hK hz₀K hz'K rfl rfl hA
      have hcm : (z₀ : Matrix (Fin n) (Fin n) F) * A = A * z₀ :=
        congrArg (fun g : Subgroup.closure S => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
          (mul_comm (⟨z₀, hz₀K⟩ : Subgroup.closure S) ⟨A, hAK⟩)
      rw [hW] at hw ⊢
      rw [Matrix.mulVec_mulVec, hcm, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
    rcases hirr W hWs with h | h
    · have hv : v ∈ (⊥ : Submodule F (Fin n → F)) := h ▸ (hW v).2 hzv
      exact hv0 (by simpa using hv)
    · have hall : ∀ w, (z₀ : Matrix (Fin n) (Fin n) F) *ᵥ w = ξ • w := fun w =>
        (hW w).1 (h ▸ Submodule.mem_top)
      apply hz₀ns ξ
      rw [Matrix.ext_iff_mulVec]
      intro w
      rw [hall, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hζ1' : (ζ : F) ≠ 1 := fun h => hζ1 (Units.val_eq_one.1 h)
  have hζp' : (ζ : F) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hζp, Units.val_one]
  have hω : IsPrimitiveRoot (ζ : F) p := isPrimitiveRoot_of_pow_eq_one_ne_one hp hζp' hζ1'
  have hrel : (z₀ : Matrix (Fin n) (Fin n) F) * z' = (ζ : F) • ((z' : Matrix (Fin n) (Fin n) F) *
      z₀) := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2.coe_eq_smul_of_eq_scalar_mul hζ
  have hz'p : (z' : Matrix (Fin n) (Fin n) F) ^ p = (c' : F) • 1 := by
    rw [← Units.val_pow_eq_pow_val, hc', scalarGL_coe_eq_smul]
  refine ⟨?_, z', z₀, ζ, c', he''E, hz'1, hz₀E, hē₀, hω, hz'p, hz₀pM, hrel⟩
  have hzvk : ∀ k : ℕ, (z₀ : Matrix (Fin n) (Fin n) F) *ᵥ
      (((z' ^ k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v) =
      (((ζ ^ k : Fˣ) : F) * ξ) • (((z' ^ k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v) := by
    intro k
    have h1 := qcomm_pow_left (A := z') (B := z₀) (mul_scalarGL_comm ζ) hζ k
    have h2 : (z₀ : Matrix (Fin n) (Fin n) F) * ((z' ^ k : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = ((ζ ^ k : Fˣ) : F) • (((z' ^ k : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) * (z₀ : Matrix (Fin n) (Fin n) F)) := by
      have h3 := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) h1
      simp only [Units.val_mul] at h3
      rw [← map_pow, scalarGL_coe_eq_smul, Matrix.smul_mul, Matrix.one_mul] at h3
      exact h3
    rw [Matrix.mulVec_mulVec, h2, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hzv,
      Matrix.mulVec_smul, smul_smul]
  set vk : Fin p → (Fin n → F) :=
    fun k => ((z' ^ (k : ℕ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v with hvk
  set W : Submodule F (Fin n → F) := Submodule.span F (Set.range vk) with hWdef
  have hvW : v ∈ W := by
    have h0 : vk ⟨0, hp.pos⟩ = v := by simp [hvk]
    rw [← h0]
    exact Submodule.subset_span ⟨_, rfl⟩
  have hz₀W : ∀ w ∈ W, (z₀ : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := by
    have hle : W ≤ W.comap (Matrix.mulVecLin (z₀ : Matrix (Fin n) (Fin n) F)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      rw [hvk]
      show (z₀ : Matrix (Fin n) (Fin n) F) *ᵥ (((z' ^ (k : ℕ) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) *ᵥ v) ∈ W
      rw [hzvk (k : ℕ)]
      exact W.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
    exact fun w hw => hle hw
  have hz'W : ∀ w ∈ W, (z' : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := by
    have hle : W ≤ W.comap (Matrix.mulVecLin (z' : Matrix (Fin n) (Fin n) F)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      have hstep : (z' : Matrix (Fin n) (Fin n) F) *ᵥ vk k =
          ((z' ^ ((k : ℕ) + 1) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v := by
        rw [hvk, pow_succ', Units.val_mul, ← Matrix.mulVec_mulVec]
      rw [hstep]
      by_cases hk : (k : ℕ) + 1 < p
      · exact Submodule.subset_span ⟨⟨(k : ℕ) + 1, hk⟩, rfl⟩
      · have hkp : (k : ℕ) + 1 = p := by omega
        rw [hkp, hc', scalarGL_coe_eq_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact W.smul_mem _ hvW
    exact fun w hw => hle hw
  have hKs : ∀ c : Fˣ, GeneralLinearGroup.scalar (Fin n) c ∈ stabGL W := by
    intro c
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rw [scalarGL_coe_eq_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact W.smul_mem _ hw
    · rw [← map_inv, scalarGL_coe_eq_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact W.smul_mem _ hw
  have hz₀S : z₀ ∈ stabGL W :=
    ⟨hz₀W, inv_mulVec_mem_of_pow_scalar hp.pos (c := 1) (by rw [hz₀p, map_one]) hz₀W⟩
  have hz'S : z' ∈ stabGL W := ⟨hz'W, inv_mulVec_mem_of_pow_scalar hp.pos hc' hz'W⟩
  have hWs : LiftStable E W := fun A hA =>
    (mem_of_conjAut_mem_of_sup_eq hn hgen hKs hz₀S hz'S rfl rfl hA).1
  rcases hirr W hWs with h | h
  · exact absurd (h ▸ hvW) (by simpa using hv0)
  · have hle : n ≤ p := by
      calc n = Module.finrank F (Fin n → F) := (Module.finrank_fin_fun F).symm
        _ = Module.finrank F W := by rw [h, finrank_top]
        _ ≤ Fintype.card (Fin p) := finrank_range_le_card vk
        _ = p := Fintype.card_fin p
    exact le_antisymm hle (Nat.le_of_dvd hn0 hpn)

end Dichotomy

section Diag

variable {F : Type} [Field F]

theorem slConjugation_eq_self_of_comm {n : ℕ} {A : GL (Fin n) F}
    {g : SpecialLinearGroup (Fin n) F} (h : (g : Matrix (Fin n) (Fin n) F) * A = A * g) :
    slConjugation n F A g = g := by
  apply Subtype.ext
  rw [slConjugation_matrix, ← h, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.mul_one]

theorem diagReducible_of_liftStable {K : Type*} [Group K] {n : ℕ} [Finite F] (hn : 3 ≤ n)
    {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0) (θ : K ⧸ Subgroup.center K ≃* projectiveSL n F)
    {E : Subgroup (MulAut K)} (hĒ : IsElemAbelian p (E.map (modelAut θ)))
    (hlin : E.map (modelAut θ) ≤ linearAutGroup n F) {W : Submodule F (Fin n → F)}
    (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤) (hWs : LiftStable (E.map (modelAut θ)) W) :
    DiagReducible p E := by
  set Ψ := LinearCover.projectiveSpecialLinearEquivProjectiveSL n F with hΨdef
  have hΨ : ∀ s : SpecialLinearGroup (Fin n) F,
      Ψ (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) s) = proj n F s :=
    fun s => rfl
  refine ⟨n, F, inferInstance, inferInstance, θ.trans Ψ.symm,
    (E.map (modelAut θ)).comap (conjAut n F), card_comap_conjAut_ne_zero hn hp hpF hĒ, hpF, W,
    hW0, hWt, fun g hg w hw => hWs g hg w hw, fun f hf => ?_⟩
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 (hlin ⟨f, hf, rfl⟩)
  refine ⟨A, by rw [Subgroup.mem_comap, hA]; exact ⟨f, hf, rfl⟩, fun s => ?_⟩
  apply Ψ.injective
  rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, hΨ, hΨ, ← modelAut_apply, ← hA, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [slConjugation_matrix, coe_glConj]

variable {K : Type} [Group K] [Finite K]

theorem seitzHyperGamma_eq_top_linear_diag (hperf : commutator K = ⊤) {m : ℕ} [Finite F]
    {p : ℕ} (hm : 2 ≤ m) (hsep : CFSG.LieType.Steinberg.CentralExt.SLClosed.Separating m F)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0) (hpn : p ∣ m + 1)
    (hpq : p ∣ Nat.card F - 1) (h34 : ¬ (m = 2 ∧ Nat.card F = 4))
    (θ₀ : K ⧸ Subgroup.center K ≃* projectiveSL (m + 1) F)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (hlin : E.map (modelAut θ₀) ≤ linearAutGroup (m + 1) F) :
    seitzHyperGamma p E = ⊤ := by
  classical
  have hn : 3 ≤ m + 1 := by omega
  have hinj := modelAut_injective hperf θ₀
  have hĒ : IsElemAbelian p (E.map (modelAut θ₀)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hĒc : Nat.card (E.map (modelAut θ₀)) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hinj, hcard]
  by_cases hred : ∃ W : Submodule F (Fin (m + 1) → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      LiftStable (E.map (modelAut θ₀)) W
  · obtain ⟨W, hW0, hWt, hWs⟩ := hred
    exact seitzHyperGamma_eq_top_of_diagReducible hperf hp hE
      (ne_bot_of_card hp (by norm_num) hcard)
      (diagReducible_of_liftStable hn hp hpF θ₀ hĒ hlin hW0 hWt hWs)
  have hirr : ∀ W : Submodule F (Fin (m + 1) → F), LiftStable (E.map (modelAut θ₀)) W →
      W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_contra hcon
    push Not at hcon
    exact hred ⟨W, hcon.1, hcon.2, hW⟩
  obtain ⟨hnp, x, y, ω, c, hxE, hx1, hyE, hy1, hω, hxp, hyp, hrel⟩ :=
    exists_heis_pair_of_irreducible hn hp hp2 hĒ hĒc hlin hpn hpq hirr
  obtain ⟨φ, hφ, hφθ⟩ := exists_sl_lift hperf hm hsep θ₀
  have hcl : Subgroup.closure ({g : SpecialLinearGroup (Fin (m + 1)) F |
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * x = x * g} ∪
      {g | (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * y = y * g}) = ⊤ := by
    subst hnp
    haveI : Fact (m + 1).Prime := ⟨hp⟩
    have hF2 : 2 ≤ Nat.card F := Finite.one_lt_card
    by_cases h5 : 5 ≤ m + 1
    · exact closure_comm_heis_eq_top hp (torusFourierGen_of_prime h5)
        (singerTorusGen_of_prime h5 hpq) hω hxp hyp hrel
    · have hm3 : m + 1 = 3 := by
        have := hp.two_le
        rcases (show m + 1 = 3 ∨ m + 1 = 4 by omega) with h | h
        · exact h
        · exact absurd (h ▸ hp) (by norm_num)
      have hm2 : m = 2 := by omega
      have hF4 : Nat.card F ≠ 4 := fun h => h34 ⟨hm2, h⟩
      have hpq3 : 3 ∣ Nat.card F - 1 := hm3 ▸ hpq
      have hF7 := QuasiHigh3.seven_le_of_dvd_sub_one hF2 hF4 hpq3
      subst hm2
      exact closure_comm_heis_eq_top hp (QuasiHigh3.torusFourierGen_three hF7)
        (singerTorusGen_three (by omega) hpq3) hω hxp hyp hrel
  have hlift : ∀ A : GL (Fin (m + 1)) F, conjAut (m + 1) F A ∈ E.map (modelAut θ₀) →
      conjAut (m + 1) F A ≠ 1 → ∃ e ∈ E, e ≠ 1 ∧ modelAut θ₀ e = conjAut (m + 1) F A := by
    rintro A ⟨e, he, heA⟩ hA1
    refine ⟨e, he, fun h1 => hA1 ?_, heA⟩
    rw [← heA, h1, map_one]
  refine seitzHyperGamma_eq_top_of_slModel hn θ₀ φ hφ hφθ hp hE hcard hcl ?_
  rintro g (hg | hg)
  · obtain ⟨e, he, he1, hex⟩ := hlift x hxE hx1
    exact ⟨e, he, he1, (slConjugation (m + 1) F x).toMonoidHom,
      slConjugation_eq_self_of_comm hg, fun h => by rw [hex, conjAut_proj]; rfl⟩
  · obtain ⟨e, he, he1, hey⟩ := hlift y hyE hy1
    exact ⟨e, he, he1, (slConjugation (m + 1) F y).toMonoidHom,
      slConjugation_eq_self_of_comm hg, fun h => by rw [hey, conjAut_proj]; rfl⟩

end Diag

section Linear

theorem seitzHyperGamma_eq_top_linear {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤) {m : ℕ}
    {q : TauCeti.PrimePower} {hv : (TauCeti.LieTypeIndex.A m q).Valid}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.A m q, hv⟩).Group)
    (hpq : p ≠ q.p) (hci : CoverIndex p (.A m q)) (h34 : ¬ (p = 3 ∧ m = 2 ∧ q.card = 4))
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) :
    seitzHyperGamma p E = ⊤ := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hF : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [hF, TauCeti.PrimePower.card_def]
  have hpF : (p : GaloisField q.p q.exponent) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p p).1 h
    exact hpq ((Nat.prime_dvd_prime_iff_eq q.prime_p hp).1 this).symm
  have hpn : p ∣ m + 1 := hci.1
  have hm : 2 ≤ m := by
    have := Nat.le_of_dvd (by omega) hpn
    have := hp.two_le
    omega
  have hpq1 : p ∣ Nat.card (GaloisField q.p q.exponent) - 1 := by
    rw [hcardF]
    exact hci.2
  have hF2 : Nat.card (GaloisField q.p q.exponent) ≠ 2 := by
    intro h
    rw [h] at hpq1
    exact hp.one_lt.ne' (Nat.dvd_one.1 hpq1)
  have h34' : ¬ (m = 2 ∧ Nat.card (GaloisField q.p q.exponent) = 4) := by
    rintro ⟨rfl, h4⟩
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpn
    exact h34 ⟨hp3, rfl, by rw [← hcardF, h4]⟩
  have h33 : ¬ (m = 3 ∧ Nat.card (GaloisField q.p q.exponent) = 3) := by
    rintro ⟨rfl, -⟩
    have h4 : p ∣ 2 ^ 2 := hpn
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  have hsep := CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card hm hF2 h34' h33
  set θ₀ := standardLinearModel e with hθ₀
  by_cases hD : E.map (modelAut θ₀) ≤ linearAutGroup (m + 1) (GaloisField q.p q.exponent)
  · exact seitzHyperGamma_eq_top_linear_diag hperf hm hsep hp hp2 hpF hpn hpq1 h34' θ₀ hE hcard hD
  · exact seitzHyperGamma_eq_top_linear_field hperf q.prime_p q.exponent_pos hF hm hsep hp hp2
      hpq θ₀ hE hcard hD

end Linear

end CFSG.LieType.SeitzGeneration.QuasiHigh5
