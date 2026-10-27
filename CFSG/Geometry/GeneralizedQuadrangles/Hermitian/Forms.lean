module

public import CFSG.LieType.BorelTits.FormFlag
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveGeometryRealization

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open Matrix CFSG.LieType.BorelTits CFSG.LocalAnalysis.ComponentInitial

private noncomputable def dotOrthEquiv (K : Type*) [Field K] :
    ProjectiveGeometry.Point 5 K ≃ ProjectiveGeometry.Hyperplane 5 K where
  toFun L := ⟨LinearFlag.dotOrth (L : Submodule K (Fin 5 → K)), by
    rw [LinearFlag.finrank_dotOrth, L.2]⟩
  invFun H := ⟨LinearFlag.dotOrth (H : Submodule K (Fin 5 → K)), by
    rw [LinearFlag.finrank_dotOrth, H.2]⟩
  left_inv L := Subtype.ext (LinearFlag.dotOrth_dotOrth (L : Submodule K (Fin 5 → K)))
  right_inv H := Subtype.ext (LinearFlag.dotOrth_dotOrth (H : Submodule K (Fin 5 → K)))

private theorem injective_of_forall_le_iff {K : Type*} [Field K]
    (π : ProjectiveGeometry.Point 5 K → ProjectiveGeometry.Hyperplane 5 K)
    (hπ : ∀ x y : ProjectiveGeometry.Point 5 K,
      (x : Submodule K (Fin 5 → K)) ≤ π y ↔
        (y : Submodule K (Fin 5 → K)) ≤ π x) :
    Function.Injective π := by
  intro x y hxy
  by_contra hne
  have hx_ne_y : (x : Submodule K (Fin 5 → K)) ≠
      (y : Submodule K (Fin 5 → K)) := by
    intro h
    exact hne (Subtype.ext h)
  have hproper : ∃ w : Fin 5 → K, w ∉ (π x : Submodule K (Fin 5 → K)) := by
    by_contra h
    push Not at h
    have htop : (π x : Submodule K (Fin 5 → K)) = ⊤ := eq_top_iff.mpr fun w _ => h w
    have h4 := (π x).2
    rw [htop, finrank_top, Module.finrank_fin_fun] at h4
    norm_num at h4
  obtain ⟨w, hw⟩ := hproper
  have hw0 : w ≠ 0 := by
    intro h0
    exact hw (h0 ▸ (π x : Submodule K (Fin 5 → K)).zero_mem)
  let Pw : ProjectiveGeometry.Point 5 K := ⟨K ∙ w, finrank_span_singleton hw0⟩
  have hxy_inf : (x : Submodule K (Fin 5 → K)) ⊓
      (y : Submodule K (Fin 5 → K)) = ⊥ := by
    by_contra hbot
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hvx : v ∈ (x : Submodule K (Fin 5 → K)) := (Submodule.mem_inf.mp hv).1
    have hvy : v ∈ (y : Submodule K (Fin 5 → K)) := (Submodule.mem_inf.mp hv).2
    have hx_eq : (x : Submodule K (Fin 5 → K)) = K ∙ v :=
      (Submodule.eq_of_le_of_finrank_eq
        ((Submodule.span_singleton_le_iff_mem _ _).mpr hvx)
        (by rw [finrank_span_singleton hv0, x.2])).symm
    have hy_eq : (y : Submodule K (Fin 5 → K)) = K ∙ v :=
      (Submodule.eq_of_le_of_finrank_eq
        ((Submodule.span_singleton_le_iff_mem _ _).mpr hvy)
        (by rw [finrank_span_singleton hv0, y.2])).symm
    exact hx_ne_y (hx_eq.trans hy_eq.symm)
  have hXY_finrank : Module.finrank K
      ↥((x : Submodule K (Fin 5 → K)) ⊔ (y : Submodule K (Fin 5 → K))) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (x : Submodule K (Fin 5 → K)) (y : Submodule K (Fin 5 → K))
    rw [hxy_inf, x.2, y.2, finrank_bot] at h
    omega
  have hH_le : ∀ q : ProjectiveGeometry.Point 5 K,
      (q : Submodule K (Fin 5 → K)) ≤
        ((x : Submodule K (Fin 5 → K)) ⊔ (y : Submodule K (Fin 5 → K))) →
      (π x : Submodule K (Fin 5 → K)) ≤ π q := by
    intro q hq h hh
    by_cases hh0 : h = 0
    · rw [hh0]
      exact (π q : Submodule K (Fin 5 → K)).zero_mem
    let p : ProjectiveGeometry.Point 5 K := ⟨K ∙ h, finrank_span_singleton hh0⟩
    have hp : (p : Submodule K (Fin 5 → K)) ≤ π x := by
      change K ∙ h ≤ (π x : Submodule K (Fin 5 → K))
      exact (Submodule.span_singleton_le_iff_mem h
        (π x : Submodule K (Fin 5 → K))).mpr hh
    have hxq : (x : Submodule K (Fin 5 → K)) ≤ π p := (hπ x p).mpr hp
    have hyq : (y : Submodule K (Fin 5 → K)) ≤ π p := (hπ y p).mpr (hxy ▸ hp)
    have hXYq : ((x : Submodule K (Fin 5 → K)) ⊔
        (y : Submodule K (Fin 5 → K))) ≤ π p := sup_le hxq hyq
    have hqp : (q : Submodule K (Fin 5 → K)) ≤ π p := hq.trans hXYq
    have hpq : (p : Submodule K (Fin 5 → K)) ≤ π q := (hπ q p).mp hqp
    exact hpq (Submodule.mem_span_singleton_self h)
  have hpiq_eq : ∀ q : ProjectiveGeometry.Point 5 K,
      (q : Submodule K (Fin 5 → K)) ≤
        ((x : Submodule K (Fin 5 → K)) ⊔ (y : Submodule K (Fin 5 → K))) →
      (π q : Submodule K (Fin 5 → K)) = π x := by
    intro q hq
    refine (Submodule.eq_of_le_of_finrank_eq (hH_le q hq) ?_).symm
    rw [(π q).2, (π x).2]
  have hZ : ((x : Submodule K (Fin 5 → K)) ⊔ (y : Submodule K (Fin 5 → K))) ⊓
      (π Pw : Submodule K (Fin 5 → K)) ≠ ⊥ := by
    intro hbot
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      ((x : Submodule K (Fin 5 → K)) ⊔ (y : Submodule K (Fin 5 → K)))
      (π Pw : Submodule K (Fin 5 → K))
    rw [hbot, finrank_bot] at hsum
    have hle : Module.finrank K ↥(((x : Submodule K (Fin 5 → K)) ⊔
        (y : Submodule K (Fin 5 → K))) ⊔ (π Pw : Submodule K (Fin 5 → K))) ≤ 5 := by
      have h := Submodule.finrank_le (((x : Submodule K (Fin 5 → K)) ⊔
        (y : Submodule K (Fin 5 → K))) ⊔ (π Pw : Submodule K (Fin 5 → K)))
      rwa [Module.finrank_fin_fun] at h
    rw [hXY_finrank, (π Pw).2] at hsum
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ
  have hzXY : z ∈ ((x : Submodule K (Fin 5 → K)) ⊔
      (y : Submodule K (Fin 5 → K))) := (Submodule.mem_inf.mp hz).1
  have hzW : z ∈ (π Pw : Submodule K (Fin 5 → K)) := (Submodule.mem_inf.mp hz).2
  let q : ProjectiveGeometry.Point 5 K := ⟨K ∙ z, finrank_span_singleton hz0⟩
  have hqXY : (q : Submodule K (Fin 5 → K)) ≤
      ((x : Submodule K (Fin 5 → K)) ⊔ (y : Submodule K (Fin 5 → K))) :=
    (Submodule.span_singleton_le_iff_mem z _).mpr hzXY
  have hqPw : (q : Submodule K (Fin 5 → K)) ≤ π Pw :=
    (Submodule.span_singleton_le_iff_mem z _).mpr hzW
  have hq_eq : (π q : Submodule K (Fin 5 → K)) = π x := hpiq_eq q hqXY
  have hPw_le : (Pw : Submodule K (Fin 5 → K)) ≤ π q := (hπ q Pw).mp hqPw
  have hw_piq : w ∈ (π q : Submodule K (Fin 5 → K)) :=
    hPw_le (Submodule.mem_span_singleton_self w)
  rw [hq_eq] at hw_piq
  exact hw hw_piq

private def polarForm {K : Type*} [Field K] (A : Matrix (Fin 5) (Fin 5) K)
    (σ : K ≃+* K) (u v : Fin 5 → K) : K :=
  (A *ᵥ fun i => σ (u i)) ⬝ᵥ v

private theorem polarForm_add_left {K : Type*} [Field K]
    (A : Matrix (Fin 5) (Fin 5) K) (σ : K ≃+* K) (u u' v : Fin 5 → K) :
    polarForm A σ (u + u') v = polarForm A σ u v + polarForm A σ u' v := by
  simp only [polarForm]
  have h : (fun i => σ ((u + u') i)) = (fun i => σ (u i)) + fun i => σ (u' i) := by
    funext i
    simp
  rw [h, Matrix.mulVec_add, add_dotProduct]

private theorem polarForm_smul_left {K : Type*} [Field K]
    (A : Matrix (Fin 5) (Fin 5) K) (σ : K ≃+* K) (c : K) (u v : Fin 5 → K) :
    polarForm A σ (c • u) v = σ c * polarForm A σ u v := by
  simp only [polarForm]
  have h : (fun i => σ ((c • u) i)) = σ c • (fun i => σ (u i)) := by
    funext i
    simp
  rw [h, Matrix.mulVec_smul, smul_dotProduct]
  rfl

private theorem polarForm_add_right {K : Type*} [Field K]
    (A : Matrix (Fin 5) (Fin 5) K) (σ : K ≃+* K) (u v v' : Fin 5 → K) :
    polarForm A σ u (v + v') = polarForm A σ u v + polarForm A σ u v' := by
  simp only [polarForm, dotProduct_add]

private theorem polarForm_smul_right {K : Type*} [Field K]
    (A : Matrix (Fin 5) (Fin 5) K) (σ : K ≃+* K) (c : K) (u v : Fin 5 → K) :
    polarForm A σ u (c • v) = c * polarForm A σ u v := by
  simp only [polarForm, dotProduct_smul]
  rfl

private theorem polarForm_zero_left {K : Type*} [Field K]
    (A : Matrix (Fin 5) (Fin 5) K) (σ : K ≃+* K) (v : Fin 5 → K) :
    polarForm A σ 0 v = 0 := by
  simp only [polarForm, Pi.zero_apply, map_zero]
  change (A *ᵥ (0 : Fin 5 → K)) ⬝ᵥ v = 0
  rw [Matrix.mulVec_zero, zero_dotProduct]

private theorem polarForm_zero_right {K : Type*} [Field K]
    (A : Matrix (Fin 5) (Fin 5) K) (σ : K ≃+* K) (u : Fin 5 → K) :
    polarForm A σ u 0 = 0 := by
  simp only [polarForm, dotProduct_zero]

private def rawPerp {K : Type*} [Field K] (A : Matrix (Fin 5) (Fin 5) K)
    (σ : K ≃+* K) (W : Submodule K (Fin 5 → K)) : Submodule K (Fin 5 → K) :=
  LinearFlag.dotOrth ((LinearFlag.coordImage σ W).map (Matrix.mulVecLin A))

private theorem mem_rawPerp_span {K : Type*} [Field K]
    {A : Matrix (Fin 5) (Fin 5) K} {σ : K ≃+* K} {u v : Fin 5 → K} :
    v ∈ rawPerp A σ (K ∙ u) ↔ polarForm A σ u v = 0 := by
  simp only [rawPerp, LinearFlag.mem_dotOrth,
    ProjectiveGeometry.coordImage_span_singleton]
  constructor
  · intro h
    have h1 : v ⬝ᵥ (A *ᵥ (fun i => σ (u i))) = 0 :=
      h _ ⟨fun i => σ (u i), Submodule.mem_span_singleton_self _,
        Matrix.mulVecLin_apply A (fun i => σ (u i))⟩
    rw [polarForm]
    rw [dotProduct_comm] at h1
    exact h1
  · intro h z hz
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [polarForm] at h
    have h' : v ⬝ᵥ (A *ᵥ (fun i => σ (u i))) = 0 := by
      rw [dotProduct_comm]
      exact h
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_smul, dotProduct_smul, h', smul_zero]

private noncomputable def reflFormOf {K : Type*} [Field K]
    (A : GL (Fin 5) K) (τ : K ≃+* K)
    (hrefl : ∀ u v : Fin 5 → K,
      polarForm (A : Matrix (Fin 5) (Fin 5) K) τ u v = 0 →
      polarForm (A : Matrix (Fin 5) (Fin 5) K) τ v u = 0) :
    ReflForm K (Fin 5 → K) where
  σ := τ
  β := polarForm (A : Matrix (Fin 5) (Fin 5) K) τ
  add_left := polarForm_add_left (A : Matrix (Fin 5) (Fin 5) K) τ
  smul_left := polarForm_smul_left (A : Matrix (Fin 5) (Fin 5) K) τ
  add_right := polarForm_add_right (A : Matrix (Fin 5) (Fin 5) K) τ
  smul_right := polarForm_smul_right (A : Matrix (Fin 5) (Fin 5) K) τ
  refl := hrefl
  nondeg := by
    intro u hu
    have hAu : (A : Matrix (Fin 5) (Fin 5) K) *ᵥ (fun i => τ (u i)) = 0 :=
      dotProduct_eq_zero _ fun v => hu v
    have hσu : (fun i => τ (u i)) = 0 :=
      Matrix.mulVec_injective_of_isUnit A.isUnit (by
        rw [hAu]
        exact (Matrix.mulVec_zero (A : Matrix (Fin 5) (Fin 5) K)).symm)
    funext i
    exact τ.injective (by simpa using congrFun hσu i)

private theorem perp_reflFormOf {K : Type*} [Field K] {A : GL (Fin 5) K}
    {τ : K ≃+* K}
    {hrefl : ∀ u v : Fin 5 → K,
      polarForm (A : Matrix (Fin 5) (Fin 5) K) τ u v = 0 →
      polarForm (A : Matrix (Fin 5) (Fin 5) K) τ v u = 0}
    (u : Fin 5 → K) :
    (reflFormOf A τ hrefl).perp (K ∙ u) =
      rawPerp (A : Matrix (Fin 5) (Fin 5) K) τ (K ∙ u) := by
  ext v
  rw [ReflForm.mem_perp_span_singleton, mem_rawPerp_span]
  rfl

theorem exists_reflForm_of_polarity {K : Type*} [Field K] [Finite K]
    (π : ProjectiveGeometry.Point 5 K → ProjectiveGeometry.Hyperplane 5 K)
    (hπ : ∀ x y : ProjectiveGeometry.Point 5 K,
      (x : Submodule K (Fin 5 → K)) ≤ π y ↔ (y : Submodule K (Fin 5 → K)) ≤ π x) :
    ∃ F : ReflForm K (Fin 5 → K), ∀ x : ProjectiveGeometry.Point 5 K,
      (π x : Submodule K (Fin 5 → K)) = F.perp x := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (ProjectiveGeometry.Point 5 K) := Fintype.ofFinite _
  letI : Fintype (ProjectiveGeometry.Hyperplane 5 K) := Fintype.ofFinite _
  have hinj : Function.Injective π := injective_of_forall_le_iff π hπ
  have hcard : Fintype.card (ProjectiveGeometry.Point 5 K) =
      Fintype.card (ProjectiveGeometry.Hyperplane 5 K) :=
    Fintype.card_congr (dotOrthEquiv K)
  have hbij : Function.Bijective π :=
    (Fintype.bijective_iff_injective_and_card π).mpr ⟨hinj, hcard⟩
  let πe : ProjectiveGeometry.Point 5 K ≃ ProjectiveGeometry.Hyperplane 5 K :=
    Equiv.ofBijective π hbij
  let f : ProjectiveGeometry.Point 5 K ≃ ProjectiveGeometry.Point 5 K :=
    πe.trans (dotOrthEquiv K).symm
  let h : ProjectiveGeometry.Hyperplane 5 K ≃ ProjectiveGeometry.Hyperplane 5 K :=
    πe.symm.trans (dotOrthEquiv K)
  have hfh : ∀ (L : ProjectiveGeometry.Point 5 K)
      (H : ProjectiveGeometry.Hyperplane 5 K),
      ((L : Submodule K (Fin 5 → K)) ≤ H) ↔
        ((f L : Submodule K (Fin 5 → K)) ≤
          (h H : Submodule K (Fin 5 → K))) := by
    intro L H
    have hfL : (f L : Submodule K (Fin 5 → K)) =
        LinearFlag.dotOrth (π L) := rfl
    have hhH : (h H : Submodule K (Fin 5 → K)) =
        LinearFlag.dotOrth (πe.symm H) := rfl
    rw [hfL, hhH]
    have h1 : ((L : Submodule K (Fin 5 → K)) ≤ H) ↔
        (((πe.symm H : ProjectiveGeometry.Point 5 K) :
          Submodule K (Fin 5 → K)) ≤ π L) := by
      have e : π (πe.symm H) = H := πe.apply_symm_apply H
      exact (iff_of_eq (congrArg (fun Z : ProjectiveGeometry.Hyperplane 5 K =>
        (L : Submodule K (Fin 5 → K)) ≤
          (Z : Submodule K (Fin 5 → K))) e)).symm.trans (hπ L (πe.symm H))
    have h2 : (((πe.symm H : ProjectiveGeometry.Point 5 K) :
          Submodule K (Fin 5 → K)) ≤ π L) ↔
        (LinearFlag.dotOrth (π L : Submodule K (Fin 5 → K)) ≤
          LinearFlag.dotOrth ((πe.symm H : ProjectiveGeometry.Point 5 K) :
            Submodule K (Fin 5 → K))) := by
      constructor
      · intro h v hv
        rw [LinearFlag.mem_dotOrth] at hv ⊢
        exact fun w hw => hv w (h hw)
      · intro h
        have h' : LinearFlag.dotOrth (LinearFlag.dotOrth
              ((πe.symm H : ProjectiveGeometry.Point 5 K) :
                Submodule K (Fin 5 → K))) ≤
            LinearFlag.dotOrth (LinearFlag.dotOrth
              (π L : Submodule K (Fin 5 → K))) := by
          intro v hv
          rw [LinearFlag.mem_dotOrth] at hv ⊢
          exact fun w hw => hv w (h hw)
        rwa [LinearFlag.dotOrth_dotOrth, LinearFlag.dotOrth_dotOrth] at h'
    exact h1.trans h2
  obtain ⟨A, σ, hA, -⟩ :=
    ProjectiveGeometry.semilinear_realization (n := 5) (K := K) (by norm_num) f h hfh
  have hπ_raw : ∀ x : ProjectiveGeometry.Point 5 K,
      (π x : Submodule K (Fin 5 → K)) =
        rawPerp (A : Matrix (Fin 5) (Fin 5) K) σ x := by
    intro x
    have hfx : (f x : Submodule K (Fin 5 → K)) = LinearFlag.dotOrth (π x) := rfl
    calc
      (π x : Submodule K (Fin 5 → K))
          = LinearFlag.dotOrth (f x : Submodule K (Fin 5 → K)) := by
            rw [hfx, LinearFlag.dotOrth_dotOrth]
      _ = rawPerp (A : Matrix (Fin 5) (Fin 5) K) σ x := by
            rw [hA x]
            rfl
  have hrefl : ∀ u v : Fin 5 → K,
      polarForm (A : Matrix (Fin 5) (Fin 5) K) σ u v = 0 →
      polarForm (A : Matrix (Fin 5) (Fin 5) K) σ v u = 0 := by
    intro u v huv
    by_cases hu : u = 0
    · rw [hu]
      exact polarForm_zero_right (A : Matrix (Fin 5) (Fin 5) K) σ v
    by_cases hv : v = 0
    · rw [hv]
      exact polarForm_zero_left (A : Matrix (Fin 5) (Fin 5) K) σ u
    let x : ProjectiveGeometry.Point 5 K := ⟨K ∙ u, finrank_span_singleton hu⟩
    let y : ProjectiveGeometry.Point 5 K := ⟨K ∙ v, finrank_span_singleton hv⟩
    have hxπy : ((x : ProjectiveGeometry.Point 5 K) :
          Submodule K (Fin 5 → K)) ≤ π y ↔
        polarForm (A : Matrix (Fin 5) (Fin 5) K) σ v u = 0 := by
      have hxval : ((x : ProjectiveGeometry.Point 5 K) :
          Submodule K (Fin 5 → K)) = K ∙ u := rfl
      rw [hxval, hπ_raw y]
      exact (Submodule.span_singleton_le_iff_mem u
        (rawPerp (A : Matrix (Fin 5) (Fin 5) K) σ (K ∙ v))).trans
        (mem_rawPerp_span (A := (A : Matrix (Fin 5) (Fin 5) K)) (σ := σ)
          (u := v) (v := u))
    have hyπx : ((y : ProjectiveGeometry.Point 5 K) :
          Submodule K (Fin 5 → K)) ≤ π x ↔
        polarForm (A : Matrix (Fin 5) (Fin 5) K) σ u v = 0 := by
      have hyval : ((y : ProjectiveGeometry.Point 5 K) :
          Submodule K (Fin 5 → K)) = K ∙ v := rfl
      rw [hyval, hπ_raw x]
      exact (Submodule.span_singleton_le_iff_mem v
        (rawPerp (A : Matrix (Fin 5) (Fin 5) K) σ (K ∙ u))).trans
        (mem_rawPerp_span (A := (A : Matrix (Fin 5) (Fin 5) K)) (σ := σ)
          (u := u) (v := v))
    have hsym := hπ x y
    rw [hxπy, hyπx] at hsym
    exact hsym.mpr huv
  let F : ReflForm K (Fin 5 → K) :=
    reflFormOf A σ hrefl
  refine ⟨F, ?_⟩
  intro x
  obtain ⟨u, hu, hWu⟩ := ProjectiveGeometry.exists_eq_span_singleton x.2
  have hπx : (π x : Submodule K (Fin 5 → K)) =
      rawPerp (A : Matrix (Fin 5) (Fin 5) K) σ (K ∙ u) := by
    rw [hπ_raw x, hWu]
  have hFx : (F.perp x : Submodule K (Fin 5 → K)) =
      rawPerp (A : Matrix (Fin 5) (Fin 5) K) σ (K ∙ u) := by
    rw [show (x : Submodule K (Fin 5 → K)) = K ∙ u from hWu]
    exact perp_reflFormOf (A := A) (τ := σ) (hrefl := hrefl) u
  rw [hπx, hFx]

end CFSG.Geometry.GeneralizedQuadrangles
