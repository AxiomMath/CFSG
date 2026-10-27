module

public import CFSG.ClassicalInvolution.Phan.PhanQ37Jop
public import CFSG.ClassicalInvolution.Phan.PhanQ13Bridge

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits

section Solid

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

structure PhanSolid (W : Submodule K (V8 K)) : Prop where
  ts : ∀ u ∈ W, ∀ v ∈ W, B8 u v = 0
  inf : ∀ v ∈ W, conj D v ∈ W → v = 0
  sup : ∀ v : V8 K, ∃ w₁ ∈ W, ∃ w₂ ∈ W, v = w₁ + conj D w₂

@[expose] def lam : K := -(algebraMap F K ε) * D.θ

theorem lam_sq (hε : ε ≠ 0) : lam D * lam D = -algebraMap F K ε := by
  unfold lam
  have h := theta_mul_theta D
  have h1 : algebraMap F K ε * algebraMap F K (1 / ε) = 1 := by
    rw [← map_mul]
    field_simp
    simp
  calc -algebraMap F K ε * D.θ * (-algebraMap F K ε * D.θ)
      = algebraMap F K ε * algebraMap F K ε * (D.θ * D.θ) := by ring
    _ = -algebraMap F K ε * (algebraMap F K ε * algebraMap F K (1 / ε)) := by rw [h]; ring
    _ = -algebraMap F K ε := by rw [h1, mul_one]

theorem tau_lam : D.τ (lam D) = -lam D := by
  unfold lam
  rw [map_mul, map_neg, D.tau_alg, D.tau_theta]
  ring

theorem lam_ne_zero (hε : ε ≠ 0) : lam D ≠ 0 := by
  intro h
  have := lam_sq D hε
  rw [h, mul_zero] at this
  have h2 : algebraMap F K ε = 0 := by linear_combination this
  exact hε ((map_eq_zero_iff (algebraMap F K) (algebraMap F K).injective).1 h2)

structure PhanJK (J : V8 K →ₗ[K] V8 K) : Prop where
  sq : ∀ v, J (J v) = (-algebraMap F K ε) • v
  skew : ∀ u v, B8 (J u) v = -B8 u (J v)
  rat : ∀ v, conj D (J v) = J (conj D v)

@[expose] def solidOf (J : V8 K →ₗ[K] V8 K) : Submodule K (V8 K) :=
  LinearMap.ker (J - lam D • LinearMap.id)

theorem mem_solidOf {J : V8 K →ₗ[K] V8 K} {v : V8 K} : v ∈ solidOf D J ↔ J v = lam D • v := by
  unfold solidOf
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

variable {D} {J : V8 K →ₗ[K] V8 K} (hJ : PhanJK D J) (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0)

include hJ h2 hε in
theorem PhanJK.solidOf_ts {u v : V8 K} (hu : u ∈ solidOf D J) (hv : v ∈ solidOf D J) :
    B8 u v = 0 := by
  rw [mem_solidOf] at hu hv
  have h := hJ.skew u v
  rw [hu, hv, B8_smul_left, B8_smul_right] at h
  have : (2 * lam D) * B8 u v = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h' | h'
  · exact absurd h' (mul_ne_zero h2 (lam_ne_zero D hε))
  · exact h'

include hJ h2 hε in
theorem PhanJK.solidOf_inf {v : V8 K} (hv : v ∈ solidOf D J) (hcv : conj D v ∈ solidOf D J) :
    v = 0 := by
  rw [mem_solidOf] at hv hcv
  have h1 := hJ.rat v
  rw [hv, conj_smul, tau_lam, hcv] at h1
  rw [neg_smul] at h1
  have h3 : (lam D + lam D) • conj D v = 0 := by
    rw [add_smul]
    exact neg_eq_iff_add_eq_zero.1 h1
  rcases smul_eq_zero.1 h3 with h' | h'
  · exact absurd (by rw [← two_mul] at h'; exact h') (mul_ne_zero h2 (lam_ne_zero D hε))
  · have := congrArg (conj D) h'
    rw [conj_conj] at this
    ext i
    have := congrFun this i
    simpa [conj] using this

include hJ h2 hε in
theorem PhanJK.solidOf_sup (v : V8 K) :
    ∃ w₁ ∈ solidOf D J, ∃ w₂ ∈ solidOf D J, v = w₁ + conj D w₂ := by
  have hl : lam D ≠ 0 := lam_ne_zero D hε
  have hl2 : lam D * lam D = -algebraMap F K ε := lam_sq D hε
  have e3 : lam D * (lam D)⁻¹ = 1 := mul_inv_cancel₀ hl
  have hu : J ((2 : K)⁻¹ • (v - (lam D)⁻¹ • J v)) =
      (-lam D) • ((2 : K)⁻¹ • (v - (lam D)⁻¹ • J v)) := by
    simp only [map_smul, map_sub, hJ.sq, smul_smul]
    match_scalars
    all_goals field_simp
    all_goals
      first
      | ring1
      | linear_combination hl2
  refine ⟨(2 : K)⁻¹ • (v + (lam D)⁻¹ • J v), ?_,
    conj D ((2 : K)⁻¹ • (v - (lam D)⁻¹ • J v)), ?_, ?_⟩
  · rw [mem_solidOf]
    simp only [map_smul, map_add, hJ.sq, smul_smul]
    match_scalars
    all_goals field_simp
    all_goals
      first
      | ring1
      | linear_combination hl2
      | linear_combination (-1) * hl2
  · rw [mem_solidOf, ← hJ.rat, hu, conj_smul, map_neg, tau_lam, neg_neg]
  · rw [conj_conj]
    match_scalars <;> field_simp <;> ring

include hJ h2 hε in
theorem PhanJK.phanSolid : PhanSolid D (solidOf D J) :=
  ⟨fun _ hu _ hv => hJ.solidOf_ts h2 hε hu hv, fun _ hv hcv => hJ.solidOf_inf h2 hε hv hcv,
    hJ.solidOf_sup h2 hε⟩

omit hJ h2 hε in
theorem PhanSolid.finrank_eq {W : Submodule K (V8 K)} (hW : PhanSolid D W) (h2 : (2 : K) ≠ 0) :
    Module.finrank K W = 4 := by
  obtain ⟨Wc, hWc⟩ : ∃ Wc : Submodule K (V8 K), ∀ v, v ∈ Wc ↔ conj D v ∈ W := ⟨
    { carrier := {v | conj D v ∈ W}
      add_mem' := fun {a b} ha hb => by
        show conj D (a + b) ∈ W
        rw [conj_add]
        exact W.add_mem ha hb
      zero_mem' := by
        show conj D 0 ∈ W
        have : conj D (0 : V8 K) = 0 := by ext i; simp [conj]
        rw [this]
        exact W.zero_mem
      smul_mem' := fun c {v} hv => by
        show conj D (c • v) ∈ W
        rw [conj_smul]
        exact W.smul_mem _ hv }, fun _ => Iff.rfl⟩
  have hfin : Module.finrank K (V8 K) = 8 := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hQ8 : ∀ v : V8 K, (quadPlusForm 4 K).Q v = Q8 v := fun v => by
    rw [Q8_eq_sum]
    rfl
  have hQW : (quadPlusForm 4 K).IsTotallySingular W := by
    intro w hw
    have h1 := hW.ts w hw w hw
    rw [B8_self] at h1
    rw [hQ8]
    exact (mul_eq_zero.1 h1).resolve_left h2
  have hQWc : (quadPlusForm 4 K).IsTotallySingular Wc := by
    intro w hw
    rw [hWc] at hw
    have h1 := hW.ts _ hw _ hw
    rw [B8_self] at h1
    have h3 := (mul_eq_zero.1 h1).resolve_left h2
    rw [hQ8]
    have h4 := Q8_conj D w
    rw [h3] at h4
    have := congrArg D.τ h4
    rw [D.tau_tau, map_zero] at this
    exact this.symm
  have hdisj : Disjoint W Wc := by
    rw [Submodule.disjoint_def]
    exact fun v hv hcv => hW.inf v hv ((hWc v).1 hcv)
  have hsup : W ⊔ Wc = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hW.sup v
    refine Submodule.add_mem_sup hw₁ ?_
    rw [hWc, conj_conj]
    exact hw₂
  have h1 := hQW.two_mul_finrank_le
  have h2' := hQWc.two_mul_finrank_le
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq W Wc
  rw [hsup, disjoint_iff.1 hdisj, finrank_top, finrank_bot, hfin] at h3
  have hfin' : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := hfin
  have k1 : 2 * Module.finrank K W ≤ 8 := by rw [← hfin']; exact h1
  have k2 : 2 * Module.finrank K Wc ≤ 8 := by rw [← hfin']; exact h2'
  have k3 : 8 = Module.finrank K W + Module.finrank K Wc := by
    simpa using h3
  omega

theorem extV_theta_indep (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) {u v : V8 F}
    (h : extV K u + D.θ • extV K v = 0) : u = 0 ∧ v = 0 := by
  have key : ∀ i, u i = 0 ∧ v i = 0 := fun i => by
    have := congrFun h i
    simp only [extV, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact theta_indep D h2 hε (by linear_combination this)
  exact ⟨funext fun i => (key i).1, funext fun i => (key i).2⟩

variable (JF : V8 F → V8 F)

include h2 hε in
theorem vecK_mem_solidOf_iff (hext : ∀ x, J (extV K x) = extV K (JF x))
    (hsq : ∀ x, JF (JF x) = (-ε) • x) (z : NPair ε) :
    vecK D z ∈ solidOf D J ↔ JF z.x = z.y := by
  rw [mem_solidOf]
  have hε' : algebraMap F K ε * algebraMap F K (1 / ε) = 1 := by
    rw [← map_mul]
    field_simp
    simp
  have hJv : J (vecK D z) = extV K (JF z.x) + D.θ • extV K (JF z.y) := by
    unfold vecK
    rw [map_add, map_smul, map_smul, hext, hext, one_smul]
  have hlam : lam D • vecK D z = extV K z.y + D.θ • extV K ((-ε) • z.x) := by
    unfold lam vecK
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, extV, map_mul, map_neg, one_mul]
    have h := theta_mul_theta D
    linear_combination (-(algebraMap F K ε) * algebraMap F K (z.y i)) * h +
      (algebraMap F K (z.y i)) * hε'
  rw [hJv, hlam]
  constructor
  · intro h
    have h' : extV K (JF z.x - z.y) + D.θ • extV K (JF z.y - (-ε) • z.x) = 0 := by
      ext i
      have := congrFun h i
      simp only [extV, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub, Pi.sub_apply,
        Pi.zero_apply] at this ⊢
      linear_combination this
    have := (extV_theta_indep h2 hε h').1
    exact sub_eq_zero.1 this
  · intro h
    have h1 : JF z.y = (-ε) • z.x := by rw [← h, hsq]
    rw [h, h1]

end Solid

section Inst

variable {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] (ε : F)

@[expose] noncomputable def jGK : V8 K →ₗ[K] V8 K where
  toFun := jG (algebraMap F K ε)
  map_add' := jG_add _
  map_smul' c v := jG_smul _ c v

@[expose] noncomputable def jHK : V8 K →ₗ[K] V8 K where
  toFun := jH (algebraMap F K ε)
  map_add' := jH_add _
  map_smul' c v := jH_smul _ c v

theorem jGK_apply (v : V8 K) : jGK K ε v = jG (algebraMap F K ε) v := rfl

theorem jHK_apply (v : V8 K) : jHK K ε v = jH (algebraMap F K ε) v := rfl

theorem jGK_extV (x : V8 F) : jGK K ε (extV K x) = extV K (jG ε x) := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [jGK_apply, jG, extV]

theorem jHK_extV (x : V8 F) : jHK K ε (extV K x) = extV K (jH ε x) := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [jHK_apply, jH, extV]

variable {K ε} (D : KData F K ε)

theorem conj_jGK (v : V8 K) : conj D (jGK K ε v) = jGK K ε (conj D v) := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [jGK_apply, jG, conj, D.tau_alg]

theorem conj_jHK (v : V8 K) : conj D (jHK K ε v) = jHK K ε (conj D v) := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [jHK_apply, jH, conj, D.tau_alg]

theorem phanJK_jGK : PhanJK D (jGK K ε) :=
  ⟨fun v => jG_jG _ v, fun u v => B8_jG _ u v, conj_jGK D⟩

theorem phanJK_jHK : PhanJK D (jHK K ε) :=
  ⟨fun v => jH_jH _ v, fun u v => B8_jH _ u v, conj_jHK D⟩

end Inst

end CFSG.ClassicalInvolution.PhanQ
