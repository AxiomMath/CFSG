module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256e
public import CFSG.LieType.SeitzGeneration.OutdiagParabolic
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.BalanceLp
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12L28
public import CFSG.GH74.GLS.LU.Local.FiveCbarF

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256e

open CFSG.Open

section Heis

open Matrix

variable {F : Type*} [Field F]

theorem heis_nilpotent_eq_zero {X B N : Matrix (Fin 3) (Fin 3) F} (hX : IsUnit X) (hB : IsUnit B) {c : F}
    (hBX : B * X = c • (X * B)) (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1) {k : ℕ} (hN : N ^ k = 0)
    (hNX : N * X = X * N) : N = 0 := by
  classical
  by_contra hN0
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc3
  have hXinj : ∀ v : Fin 3 → F, X *ᵥ v = 0 → v = 0 := fun v hv => by
    obtain ⟨u, hu⟩ := hX
    have := congrArg (fun w => ((u⁻¹ : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) hv
    simpa [← hu, Matrix.mulVec_mulVec] using this
  have hBinj : ∀ v : Fin 3 → F, B *ᵥ v = 0 → v = 0 := fun v hv => by
    obtain ⟨u, hu⟩ := hB
    have := congrArg (fun w => ((u⁻¹ : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) hv
    simpa [← hu, Matrix.mulVec_mulVec] using this
  obtain ⟨μ, v, hv0, hXv⟩ : ∃ (μ : F) (v : Fin 3 → F), v ≠ 0 ∧ X *ᵥ v = μ • v := by
    set f : (Fin 3 → F) →ₗ[F] (Fin 3 → F) := Matrix.toLin' N with hf
    have hker : ∀ u ∈ LinearMap.ker f, X *ᵥ u ∈ LinearMap.ker f := by
      intro u hu
      rw [LinearMap.mem_ker, hf, Matrix.toLin'_apply] at hu ⊢
      rw [Matrix.mulVec_mulVec, hNX, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
    have hrange : ∀ u ∈ LinearMap.range f, X *ᵥ u ∈ LinearMap.range f := by
      rintro _ ⟨w, rfl⟩
      refine ⟨X *ᵥ w, ?_⟩
      rw [hf, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hNX, ← Matrix.mulVec_mulVec]
    have hsum := LinearMap.finrank_range_add_finrank_ker f
    rw [Module.finrank_fin_fun] at hsum
    have hr : Module.finrank F (LinearMap.range f) ≠ 0 := by
      intro h0
      apply hN0
      have : LinearMap.range f = ⊥ := Submodule.finrank_eq_zero.1 h0
      rw [LinearMap.range_eq_bot, hf] at this
      exact Matrix.toLin'.injective (by rw [this, map_zero])
    have hk : Module.finrank F (LinearMap.ker f) ≠ 0 := by
      intro h0
      have hbot : LinearMap.ker f = ⊥ := Submodule.finrank_eq_zero.1 h0
      have hdet : N.det ≠ 0 := by
        intro hd
        obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
        have : w ∈ LinearMap.ker f := by rw [LinearMap.mem_ker, hf, Matrix.toLin'_apply]; exact hw
        rw [hbot] at this
        exact hw0 ((Submodule.mem_bot F).1 this)
      have h1 : (N ^ k).det ≠ 0 := by rw [Matrix.det_pow]; exact pow_ne_zero _ hdet
      rw [hN, Matrix.det_zero] at h1
      exact h1 rfl
    rcases (by omega : Module.finrank F (LinearMap.ker f) = 1 ∨
        Module.finrank F (LinearMap.range f) = 1) with h1 | h1
    · obtain ⟨μ, w, hw0, hw⟩ := CFSG.LieType.SeitzGeneration.exists_eigenvector_of_finrank_one h1 hker
      exact ⟨μ, w, hw0, hw⟩
    · obtain ⟨μ, w, hw0, hw⟩ := CFSG.LieType.SeitzGeneration.exists_eigenvector_of_finrank_one h1 hrange
      exact ⟨μ, w, hw0, hw⟩
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hXv
    exact hv0 (hXinj v hXv)
  have hXB : X * B = c⁻¹ • (B * X) := by
    rw [hBX, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hstep : ∀ (w : Fin 3 → F) (l : F), X *ᵥ w = l • w → X *ᵥ (B *ᵥ w) = (c⁻¹ * l) • (B *ᵥ w) := by
    intro w l hw
    rw [Matrix.mulVec_mulVec, hXB, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul,
      smul_smul]
  set ws : Fin 3 → (Fin 3 → F) := ![v, B *ᵥ v, B *ᵥ (B *ᵥ v)] with hws
  set μs : Fin 3 → F := ![μ, c⁻¹ * μ, c⁻¹ * (c⁻¹ * μ)] with hμs
  have hXws : ∀ i, X *ᵥ ws i = μs i • ws i := by
    intro i
    fin_cases i
    · exact hXv
    · exact hstep v μ hXv
    · exact hstep _ _ (hstep v μ hXv)
  have hws0 : ∀ i, ws i ≠ 0 := by
    intro i
    fin_cases i
    · exact hv0
    · exact fun h => hv0 (hBinj v h)
    · exact fun h => hv0 (hBinj v (hBinj _ h))
  have hci : c⁻¹ ≠ 1 := fun h => hc1 (by rw [← inv_inv c, h, inv_one])
  have hci2 : c⁻¹ * c⁻¹ ≠ 1 := by
    intro h
    have h3 : c⁻¹ ^ 3 = 1 := by rw [inv_pow, hc3, inv_one]
    apply hci
    calc c⁻¹ = c⁻¹ ^ 3 * (c⁻¹ * c⁻¹)⁻¹ := by field_simp
      _ = 1 := by rw [h3, h, inv_one, one_mul]
  have hinj : Function.Injective μs := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [hμs] at hij <;> first
      | rfl
      | (exfalso
         first
          | exact hci (mul_right_cancel₀ hμ0 (by simpa using hij.symm))
          | exact hci (mul_right_cancel₀ hμ0 (by simpa using hij))
          | exact hci2 (mul_right_cancel₀ hμ0 (by simpa [mul_assoc] using hij.symm))
          | exact hci2 (mul_right_cancel₀ hμ0 (by simpa [mul_assoc] using hij))
          | exact hci (mul_right_cancel₀ (mul_ne_zero (inv_ne_zero hc0) hμ0)
              (by simpa [mul_assoc] using hij.symm))
          | exact hci (mul_right_cancel₀ (mul_ne_zero (inv_ne_zero hc0) hμ0)
              (by simpa [mul_assoc] using hij)))
  have hli : LinearIndependent F ws :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' X) μs hinj ws fun i =>
      ⟨by rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hXws i, hws0 i⟩
  have hspan : Submodule.span F (Set.range ws) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  have hNws : ∀ i, N *ᵥ ws i = 0 := by
    intro i
    set y := N *ᵥ ws i with hy
    have hXy : X *ᵥ y = μs i • y := by
      rw [hy, Matrix.mulVec_mulVec, ← hNX, ← Matrix.mulVec_mulVec, hXws i, Matrix.mulVec_smul]
    have hymem : y ∈ Submodule.span F (Set.range ws) := hspan ▸ Submodule.mem_top
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hymem
    have hcoef : ∀ j, r j * (μs j - μs i) = 0 := by
      have h0 : ∑ j, (r j * (μs j - μs i)) • ws j = 0 := by
        have e1 : X *ᵥ y - μs i • y = 0 := by rw [hXy, sub_self]
        rw [← hr] at e1
        rw [← e1, Matrix.mulVec_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.mulVec_smul, hXws j, smul_smul, smul_smul, ← sub_smul, mul_sub, mul_comm (μs i)]
      exact fun j => Fintype.linearIndependent_iff.1 hli _ h0 j
    have hrj : ∀ j, j ≠ i → r j = 0 := fun j hji =>
      (mul_eq_zero.1 (hcoef j)).resolve_right (sub_ne_zero.2 fun h => hji (hinj h))
    have hyi : y = r i • ws i := by
      rw [← hr, Finset.sum_eq_single i (fun j _ hji => by rw [hrj j hji, zero_smul])
        (fun h => absurd (Finset.mem_univ i) h)]
    have hpow : ∀ m : ℕ, (N ^ m) *ᵥ ws i = r i ^ m • ws i := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, ← hy, hyi, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
          mul_comm]
    have h1 := hpow k
    rw [hN, Matrix.zero_mulVec] at h1
    have hri : r i ^ k = 0 := ((smul_eq_zero.1 h1.symm).resolve_right (hws0 i))
    rw [hyi, eq_zero_of_pow_eq_zero hri, zero_smul]
  apply hN0
  have hlin : Matrix.toLin' N = 0 := by
    refine LinearMap.ext_on_range hspan fun i => ?_
    rw [Matrix.toLin'_apply, hNws i, LinearMap.zero_apply]
  exact Matrix.toLin'.injective (by rw [hlin, map_zero])

end Heis

section UniLift

open Matrix CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [Finite F] {n : ℕ}

@[expose] def uniLiftFixSL (E : Subgroup (MulAut (projectiveSL n F))) :
    Set (SpecialLinearGroup (Fin n) F) :=
  {k | (∃ A : GL (Fin n) F, conjAut n F A ∈ E ∧ conjAut n F A ≠ 1 ∧
    k ∈ FixSL (A : Matrix (Fin n) (Fin n) F)) ∧ k ^ ringChar F = 1}

theorem unip_mem_closure_uniLiftFixSL (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    {E : Subgroup (MulAut (projectiveSL n F))} (hE1 : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hlin : E ≤ linearAutGroup n F) {W : Submodule F (Fin n → F)} (hW : LiftStable E W)
    {g : SpecialLinearGroup (Fin n) F} (hg : (g : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W) :
    g ∈ Subgroup.closure (uniLiftFixSL E) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set K := Subgroup.closure (uniLiftFixSL E) with hK
  set φ : Matrix (Fin n) (Fin n) F := (g : Matrix (Fin n) (Fin n) F) - 1 with hφ
  obtain ⟨x, hxE, y, hyE, hy1, hxy⟩ := exists_independent_pair hp E hE1.2 hc
  obtain ⟨a, rfl⟩ := mem_linearAutGroup_iff.1 (hlin hxE)
  obtain ⟨b, rfl⟩ := mem_linearAutGroup_iff.1 (hlin hyE)
  obtain ⟨cA, hap⟩ := exists_scalarGL_pow hn hE1 hxE
  obtain ⟨cB, hbp⟩ := exists_scalarGL_pow hn hE1 hyE
  obtain ⟨u, hba⟩ := exists_scalarGL_comm hn hE1 hxE hyE
  have hA : conjActionGL a ^ p = (1 : Module.End F (Matrix (Fin n) (Fin n) F)) := by
    rw [← map_pow, hap, conjActionGL_scalar]
  have hB : conjActionGL b ^ p = (1 : Module.End F (Matrix (Fin n) (Fin n) F)) := by
    rw [← map_pow, hbp, conjActionGL_scalar]
  have hAB : Commute (conjActionGL a) (conjActionGL b) := by
    have h1 : conjActionGL (b * a) = conjActionGL (a * b) := by
      rw [hba]
      simp only [map_mul, conjActionGL_scalar, one_mul]
    simp only [map_mul] at h1
    exact h1.symm
  have haW : ∀ w ∈ W, (a : Matrix (Fin n) (Fin n) F).mulVec w ∈ W := hW a hxE
  have haW' : ∀ w ∈ W, ((a⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec w ∈ W :=
    hW a⁻¹ (by rw [map_inv]; exact E.inv_mem hxE)
  have hbW : ∀ w ∈ W, (b : Matrix (Fin n) (Fin n) F).mulVec w ∈ W := hW b hyE
  have hbW' : ∀ w ∈ W, ((b⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec w ∈ W :=
    hW b⁻¹ (by rw [map_inv]; exact E.inv_mem hyE)
  have hline_mem : ∀ j : ℕ, conjAut n F (a * b ^ j) ∈ E := fun j => by
    rw [map_mul, map_pow]
    exact E.mul_mem hxE (E.pow_mem hyE j)
  have hline_ne : ∀ j : ℕ, conjAut n F (a * b ^ j) ≠ 1 := fun j h => by
    rw [map_mul, map_pow] at h
    apply hxy
    have : conjAut n F a = (conjAut n F b ^ j)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j)
  obtain ⟨u, v, hu, hv, hsum, hmem⟩ := exists_decomp_lines hpF hAB hA hB φ
  have hAS : ∀ z ∈ thetaSpace W, conjActionGL a z ∈ thetaSpace W := fun z hz =>
    conjActionGL_mem_thetaSpace haW haW' hz
  have hBS : ∀ z ∈ thetaSpace W, conjActionGL b z ∈ thetaSpace W := fun z hz =>
    conjActionGL_mem_thetaSpace hbW hbW' hz
  obtain ⟨huS, hvS⟩ := hmem (thetaSpace W) hAS hBS hg
  let T : AddSubmonoid (Matrix (Fin n) (Fin n) F) :=
    { carrier := {ψ | ∃ h : ψ ∈ thetaSpace W, unipSL h ∈ K}
      zero_mem' := ⟨(thetaSpace W).zero_mem, by
        have : unipSL (thetaSpace W).zero_mem = 1 := Subtype.ext (by simp [coe_unipSL])
        rw [this]; exact K.one_mem⟩
      add_mem' := by
        rintro ψ ψ' ⟨h, hKψ⟩ ⟨h', hKψ'⟩
        refine ⟨(thetaSpace W).add_mem h h', ?_⟩
        have : unipSL ((thetaSpace W).add_mem h h') = unipSL h * unipSL h' := Subtype.ext (by
          show 1 + (ψ + ψ') = (1 + ψ) * (1 + ψ')
          simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, thetaSpace_mul h h', add_zero]
          abel)
        rw [this]; exact K.mul_mem hKψ hKψ' }
  have hu_mem : ∀ j : ZMod p, u j ∈ T := fun j => by
    refine ⟨huS j, Subgroup.subset_closure ⟨⟨a * b ^ j.val, hline_mem _, hline_ne _, ?_⟩,
      Inputs2311c.unipSL_pow_ringChar _⟩⟩
    have hfix : conjActionGL (a * b ^ j.val) (u j) = u j := by
      simpa only [map_mul, map_pow] using hu j
    exact unipSL_mem_FixSL (huS j) (commute_of_conjActionGL_eq hfix)
  have hv_mem : v ∈ T := by
    refine ⟨hvS, Subgroup.subset_closure ⟨⟨b, hyE, hy1, ?_⟩, Inputs2311c.unipSL_pow_ringChar _⟩⟩
    exact unipSL_mem_FixSL hvS (commute_of_conjActionGL_eq hv)
  have hφT : φ ∈ T := by
    rw [hsum]
    exact T.add_mem (T.sum_mem fun j _ => hu_mem j) hv_mem
  obtain ⟨h, hKφ⟩ := hφT
  have : unipSL h = g := Subtype.ext (by
    show 1 + φ = (g : Matrix (Fin n) (Fin n) F)
    rw [hφ]; abel)
  rwa [this] at hKφ

theorem uniPlaneGen_of_liftStable (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    {E : Subgroup (MulAut (projectiveSL n F))} (hE1 : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hlin : E ≤ linearAutGroup n F) {W : Submodule F (Fin n → F)} (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hWE : LiftStable E W) : Inputs2311c.UniPlaneGen (ringChar F) E := by
  obtain ⟨W', hcompl, hW'H⟩ :=
    CFSG.LieType.SeitzGeneration.exists_invariant_compl_gl (H := E.comap (conjAut n F))
      (card_comap_conjAut_ne_zero hn hp hpF hE1) (W := W)
      (fun x hx w hw => hWE x (Subgroup.mem_comap.1 hx) w hw)
  have hW'E : LiftStable E W' := fun A hA w hw => hW'H A (Subgroup.mem_comap.2 hA) w hw
  have hW'0 : W' ≠ ⊥ := by
    intro h
    apply hWt
    have := codisjoint_iff.1 hcompl.2
    rwa [h, sup_bot_eq] at this
  have htop : Subgroup.closure (uniLiftFixSL E) = ⊤ := eq_top_of_unip_isCompl hcompl hW0 hW'0
    (fun g hg => unip_mem_closure_uniLiftFixSL hn hp hpF hE1 hc hlin hWE hg)
    (fun g hg => unip_mem_closure_uniLiftFixSL hn hp hpF hE1 hc hlin hW'E hg)
  refine Inputs2311c.uniPlaneGen_of_comap_eq_top (eq_top_iff.mpr fun k _ => ?_)
  have hk : k ∈ Subgroup.closure (uniLiftFixSL E) := htop ▸ Subgroup.mem_top k
  refine (Subgroup.closure_le ((Inputs2311c.uniPlaneClosure (ringChar F) E).comap (proj n F))).2 ?_ hk
  rintro k' ⟨⟨A, hA, hA1, hk'⟩, hk'r⟩
  exact Inputs2311c.mem_uniPlaneClosure hA hA1 (conjAut_proj_eq_of_mem_fixSL (by omega) hk') (n := 1)
    (by rw [pow_one, ← map_pow, hk'r, map_one])

end UniLift

section Dichotomy

open Matrix CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {F : Type} [Field F]

@[expose] def stabSubGL' (W : Submodule F (Fin n → F)) : Subgroup (GL (Fin n) F) where
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

theorem lift_dichotomy [Finite F] (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut (projectiveSL n F))} (hE1 : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hlin : E ≤ linearAutGroup n F) (hpn : p ∣ n) (hpq : p ∣ Nat.card F - 1) :
    (∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧ LiftStable E W) ∨
      (n = p ∧ ∃ A B : GL (Fin n) F, conjAut n F A ∈ E ∧ conjAut n F B ∈ E ∧ A * B ≠ B * A) := by
  classical
  have hn0 : 0 < n := by omega
  have : Fact p.Prime := ⟨hp⟩
  by_cases hred : ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧ LiftStable E W
  · exact Or.inl hred
  right
  have hirr : ∀ W : Submodule F (Fin n → F), LiftStable E W → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_contra hcon
    push Not at hcon
    exact hred ⟨W, hcon.1, hcon.2, hW⟩
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
  have hnonab : ∃ A B : GL (Fin n) F, conjAut n F A ∈ E ∧ conjAut n F B ∈ E ∧ A * B ≠ B * A := by
    by_contra hab
    push Not at hab
    let W : Submodule F (Fin n → F) :=
      LinearMap.ker (Matrix.toLin' ((z₀ : Matrix (Fin n) (Fin n) F) - ξ • 1))
    have hW : ∀ w, w ∈ W ↔ (z₀ : Matrix (Fin n) (Fin n) F) *ᵥ w = ξ • w := fun w => by
      simp [W, LinearMap.mem_ker, Matrix.toLin'_apply, sub_eq_zero]
    have hWs : LiftStable E W := by
      intro A hA w hw
      rw [hW] at hw ⊢
      have hcm : (z₀ : Matrix (Fin n) (Fin n) F) * A = A * z₀ :=
        congrArg Units.val (hab z₀ A hz₀E hA)
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
  refine ⟨?_, hnonab⟩
  obtain ⟨e'', he''E, he''⟩ := exists_notMem_zpowers_of_card_sq hp hE1.2 hc hz₀E hē₀
  obtain ⟨z', rfl⟩ := mem_linearAutGroup_iff.1 (hlin he''E)
  have hgen := zpowers_sup_zpowers_eq_of_card_sq hp hE1.2 hc hz₀E hē₀ he''E he''
  obtain ⟨ζ, hζ⟩ := exists_scalarGL_comm hn hE1 he''E hz₀E
  have hncomm : z₀ * z' ≠ z' * z₀ := by
    intro hcomm
    obtain ⟨A, B, hA, hB, hAB⟩ := hnonab
    set S : Set (GL (Fin n) F) := {z₀, z'} ∪ Set.range (GeneralLinearGroup.scalar (Fin n)) with hS
    have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
      intro x hx y hy
      simp only [hS, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_range] at hx hy
      rcases hx with (rfl | rfl) | ⟨c, rfl⟩ <;> rcases hy with (rfl | rfl) | ⟨d, rfl⟩
      all_goals first
        | rfl
        | exact hcomm
        | exact hcomm.symm
        | exact (mul_scalarGL_comm _ _).symm
        | exact mul_scalarGL_comm _ _
    have hK : ∀ c : Fˣ, GeneralLinearGroup.scalar (Fin n) c ∈ Subgroup.closure S := fun c =>
      Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
    have hz₀K : z₀ ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inl (Or.inl rfl))
    have hz'K : z' ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inl (Or.inr rfl))
    have hAK := mem_of_conjAut_mem_of_sup_eq hn hgen hK hz₀K hz'K rfl rfl hA
    have hBK := mem_of_conjAut_mem_of_sup_eq hn hgen hK hz₀K hz'K rfl rfl hB
    letI : CommGroup (Subgroup.closure S) :=
      Subgroup.closureCommGroupOfComm fun x hx y hy _ => hSc x hx y hy
    exact hAB (congrArg Subtype.val (mul_comm (⟨A, hAK⟩ : Subgroup.closure S) ⟨B, hBK⟩))
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
  obtain ⟨c', hc'⟩ := exists_scalarGL_pow hn hE1 he''E
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
  have hKs : ∀ c : Fˣ, GeneralLinearGroup.scalar (Fin n) c ∈ stabSubGL' W := by
    intro c
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rw [scalarGL_coe_eq_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact W.smul_mem _ hw
    · rw [← map_inv, scalarGL_coe_eq_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact W.smul_mem _ hw
  have hz₀S : z₀ ∈ stabSubGL' W :=
    ⟨hz₀W, inv_mulVec_mem_of_pow_scalar hp.pos (c := 1) (by rw [hz₀p, map_one]) hz₀W⟩
  have hz'S : z' ∈ stabSubGL' W := ⟨hz'W, inv_mulVec_mem_of_pow_scalar hp.pos hc' hz'W⟩
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

section HeisFive

open Matrix CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [Finite F]

theorem heis_fixed_five_eq_one (h5 : ringChar F = 5) {E : Subgroup (MulAut (projectiveSL 3 F))}
    (hE1 : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2) (hlin : E ≤ linearAutGroup 3 F)
    (hnonab : ∃ A B : GL (Fin 3) F, conjAut 3 F A ∈ E ∧ conjAut 3 F B ∈ E ∧ A * B ≠ B * A)
    {e₀ : MulAut (projectiveSL 3 F)} (he₀ : e₀ ∈ E) (he₀1 : e₀ ≠ 1) {s : projectiveSL 3 F}
    (hs : e₀ s = s) (hs5 : s ^ 5 = 1) : s = 1 := by
  classical
  have hn : 3 ≤ 3 := le_rfl
  obtain ⟨e'', he''E, he''⟩ := exists_notMem_zpowers_of_card_sq Nat.prime_three hE1.2 hc he₀ he₀1
  have hgen := zpowers_sup_zpowers_eq_of_card_sq Nat.prime_three hE1.2 hc he₀ he₀1 he''E he''
  obtain ⟨X, rfl⟩ := mem_linearAutGroup_iff.1 (hlin he₀)
  obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.1 (hlin he''E)
  have hncomm : X * B ≠ B * X := by
    intro hcomm
    obtain ⟨A₁, A₂, hA₁, hA₂, hA⟩ := hnonab
    set S : Set (GL (Fin 3) F) := {X, B} ∪ Set.range (GeneralLinearGroup.scalar (Fin 3)) with hS
    have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
      intro x hx y hy
      simp only [hS, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_range] at hx hy
      rcases hx with (rfl | rfl) | ⟨c, rfl⟩ <;> rcases hy with (rfl | rfl) | ⟨d, rfl⟩
      all_goals first
        | rfl
        | exact hcomm
        | exact hcomm.symm
        | exact (mul_scalarGL_comm _ _).symm
        | exact mul_scalarGL_comm _ _
    have hK : ∀ c : Fˣ, GeneralLinearGroup.scalar (Fin 3) c ∈ Subgroup.closure S := fun c =>
      Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
    have hXK : X ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inl (Or.inl rfl))
    have hBK : B ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inl (Or.inr rfl))
    have h1 := mem_of_conjAut_mem_of_sup_eq hn hgen hK hXK hBK rfl rfl hA₁
    have h2 := mem_of_conjAut_mem_of_sup_eq hn hgen hK hXK hBK rfl rfl hA₂
    letI : CommGroup (Subgroup.closure S) :=
      Subgroup.closureCommGroupOfComm fun x hx y hy _ => hSc x hx y hy
    exact hA (congrArg Subtype.val (mul_comm (⟨A₁, h1⟩ : Subgroup.closure S) ⟨A₂, h2⟩))
  obtain ⟨c, hcBX⟩ := exists_scalarGL_comm hn hE1 he₀ he''E
  obtain ⟨cX, hcX⟩ := exists_scalarGL_pow hn hE1 he₀
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hncomm
    rw [map_one, one_mul] at hcBX
    exact hcBX.symm
  have hc3 : c ^ 3 = 1 := by
    have h := qcomm_pow_eq_one (A := X) (B := B) (mul_scalarGL_comm c) (mul_scalarGL_comm cX) hcBX hcX
    rw [← map_pow] at h
    have h1 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h
    simp only [scalarGL_coe_eq_smul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      map_one, Units.val_one] at h1
    exact Units.ext h1
  obtain ⟨hker, hcop⟩ := proj_ker_facts Nat.prime_five h5 3
  obtain ⟨k, rfl, hk5⟩ := exists_pow_lift (proj 3 F) (proj_surjective 3 F) hcop (n := 1)
    (by rw [pow_one]; exact hs5)
  rw [pow_one] at hk5
  have hz : k⁻¹ * CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F X k ∈
      (proj 3 F).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← conjAut_proj, hs, inv_mul_cancel]
  have hzc := hker hz
  set y := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F X k with hy
  have hcomm : Commute k (k⁻¹ * y) := Subgroup.mem_center_iff.1 hzc k
  have hz5 : (k⁻¹ * y) ^ 5 ^ 1 = 1 := by
    have hyz : y = k * (k⁻¹ * y) := by group
    have h1 : y ^ 5 = 1 := by rw [hy, ← map_pow, hk5, map_one]
    rw [pow_one]
    rw [hyz, hcomm.mul_pow, hk5, one_mul] at h1
    exact h1
  have hz1 := eq_one_of_mem_of_coprime hcop hz hz5
  have hyk : y = k := (inv_mul_eq_one.1 hz1).symm
  have hkX : (k : Matrix (Fin 3) (Fin 3) F) * X = X * k := by
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hyk
    simp only [hy, coe_slConjugation] at h1
    calc (k : Matrix (Fin 3) (Fin 3) F) * X
        = (X * k * ((X⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) * X := by rw [h1]
      _ = X * k := by rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  haveI : CharP F 5 := h5 ▸ ringChar.charP F
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set N : Matrix (Fin 3) (Fin 3) F := (k : Matrix (Fin 3) (Fin 3) F) - 1 with hN
  have hN5 : N ^ 5 = 0 := by
    rw [hN, sub_pow_char_of_commute (R := Matrix (Fin 3) (Fin 3) F) (p := 5)
      (x := (k : Matrix (Fin 3) (Fin 3) F)) (y := 1) (Commute.one_right _), one_pow,
      ← Matrix.SpecialLinearGroup.coe_pow, hk5, Matrix.SpecialLinearGroup.coe_one, sub_self]
  have hNX : N * X = X * N := by
    rw [hN, Matrix.sub_mul, Matrix.mul_sub, hkX, Matrix.one_mul, Matrix.mul_one]
  have hBXm : (B : Matrix (Fin 3) (Fin 3) F) * X = (c : F) • ((X : Matrix (Fin 3) (Fin 3) F) * B) := by
    have h1 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hcBX
    simp only [Units.val_mul] at h1
    rw [h1, scalarGL_coe_eq_smul, Matrix.smul_mul, Matrix.one_mul]
  have hcF1 : (c : F) ≠ 1 := fun h => hc1 (Units.ext h)
  have hcF3 : (c : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hN0 := heis_nilpotent_eq_zero X.isUnit B.isUnit hBXm hcF1 hcF3 hN5 hNX
  have hk1 : k = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact sub_eq_zero.1 hN0
  rw [hk1, map_one]

theorem uniPlaneGen_projectiveSL_five (h5 : ringChar F = 5) {n : ℕ} (hn : 3 ≤ n)
    (h3n : 3 ∣ n) (h3q : 3 ∣ Nat.card F - 1) {E : Subgroup (MulAut (projectiveSL n F))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2)
    (hfive : ∃ e₀ ∈ E, e₀ ≠ 1 ∧ ∃ s : projectiveSL n F, s ≠ 1 ∧ e₀ s = s ∧ s ^ 5 = 1) :
    Inputs2311c.UniPlaneGen 5 E := by
  obtain ⟨f, hf, hK⟩ := exists_card_eq_pow Nat.prime_five h5
  have h3F : ((3 : ℕ) : F) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff F (ringChar F), h5] at h0
    exact absurd h0 (by norm_num)
  by_cases hD : E ≤ linearAutGroup n F
  · rcases lift_dichotomy hn Nat.prime_three (by norm_num) hE hc hD h3n h3q with
      ⟨W, hW0, hWt, hWE⟩ | ⟨rfl, hnonab⟩
    · have h := uniPlaneGen_of_liftStable hn Nat.prime_three h3F hE hc hD hW0 hWt hWE
      rwa [h5] at h
    · obtain ⟨e₀, he₀, he₀1, s, hs1, hs, hs5⟩ := hfive
      exact absurd (heis_fixed_five_eq_one h5 hE hc hD hnonab he₀ he₀1 hs hs5) hs1
  · haveI : CharP F 5 := h5 ▸ ringChar.charP F
    have h := Inputs2311c.uniPlaneGen_of_field_outer Nat.prime_five hf hn hK Nat.prime_three (by norm_num)
      (by norm_num) hE hc hD
    rwa [h5] at h

end HeisFive

section Pair

variable {G : Type*} [Group G]

theorem sup_zpowers_facts {p : ℕ} (hp : p.Prime) {a b : G} (hab : Commute a b) (ha : a ^ p = 1)
    (hb : b ^ p = 1) (ha1 : a ≠ 1) (hba : b ∉ Subgroup.zpowers a) :
    IsElemAbelian p (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ∧
      Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = p ^ 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set H := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hH
  have hHcl : H = Subgroup.closure ({a, b} : Set G) := by
    rw [hH, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    rfl
  let φ : ZMod p × ZMod p → G := fun ij => a ^ ij.1.val * b ^ ij.2.val
  have hapow : ∀ m : ℕ, a ^ m = a ^ (m % p) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m p, pow_add, pow_mul, ha, one_pow, mul_one]
  have hbpow : ∀ m : ℕ, b ^ m = b ^ (m % p) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m p, pow_add, pow_mul, hb, one_pow, mul_one]
  have hφmul : ∀ x y, φ x * φ y = φ (x + y) := by
    rintro ⟨i, j⟩ ⟨k, l⟩
    simp only [φ, Prod.mk_add_mk, ZMod.val_add]
    rw [← hapow, ← hbpow, pow_add, pow_add]
    have h1 : Commute (b ^ j.val) (a ^ k.val) := (hab.pow_pow k.val j.val).symm
    calc a ^ i.val * b ^ j.val * (a ^ k.val * b ^ l.val)
        = a ^ i.val * (b ^ j.val * a ^ k.val) * b ^ l.val := by group
      _ = a ^ i.val * (a ^ k.val * b ^ j.val) * b ^ l.val := by rw [h1.eq]
      _ = a ^ i.val * a ^ k.val * (b ^ j.val * b ^ l.val) := by group
  let S : Subgroup G :=
    { carrier := Set.range φ
      mul_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, (hφmul x y).symm⟩
      one_mem' := ⟨0, by simp [φ]⟩
      inv_mem' := by
        rintro _ ⟨x, rfl⟩
        refine ⟨-x, ?_⟩
        apply eq_inv_of_mul_eq_one_left
        rw [hφmul, neg_add_cancel]
        simp [φ] }
  have haS : a ∈ S := ⟨(1, 0), by
    simp only [φ, ZMod.val_zero, pow_zero, mul_one]
    rw [ZMod.val_one_eq_one_mod, ← hapow, pow_one]⟩
  have hbS : b ∈ S := ⟨(0, 1), by
    simp only [φ, ZMod.val_zero, pow_zero, one_mul]
    rw [ZMod.val_one_eq_one_mod, ← hbpow, pow_one]⟩
  have hHS : H ≤ S := by
    rw [hHcl, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact haS
    · exact hbS
  have hc : ∀ u ∈ ({a, b} : Set G), ∀ v ∈ ({a, b} : Set G), Commute u v := by
    intro u hu v hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have hcomm : IsMulCommutative H := by
    rw [hHcl]
    exact Subgroup.isMulCommutative_closure fun u hu v hv _ => hc u hu v hv
  have hexp : ∀ z ∈ H, z ^ p = 1 := by
    intro z hz
    rw [hHcl] at hz
    induction hz using Subgroup.closure_induction with
    | mem u hu =>
      rcases hu with rfl | rfl
      · exact ha
      · exact hb
    | one => exact one_pow p
    | mul u v hu hv ihu ihv =>
      have huv : Commute u v := by
        rw [← hHcl] at hu hv
        exact congrArg Subtype.val (hcomm.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
      rw [huv.mul_pow, ihu, ihv, one_mul]
    | inv u hu ihu => rw [inv_pow, ihu, inv_one]
  refine ⟨⟨hcomm, hexp⟩, ?_⟩
  have hpg : IsPGroup p H := fun z => ⟨1, Subtype.ext (by simpa using hexp z z.2)⟩
  haveI hSfin : Finite S := by
    have : Finite (Set.range φ) := Set.finite_range φ |>.to_subtype
    exact this
  have hfinH : Finite H :=
    Finite.of_injective (Subgroup.inclusion hHS) (Subgroup.inclusion_injective hHS)
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  have hord : orderOf a = p := orderOf_eq_prime ha ha1
  have hle1 : Subgroup.zpowers a ≤ H := le_sup_left
  have hbH : b ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    have hcz : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hord]
    have hdvd : Nat.card (Subgroup.zpowers a) ∣ Nat.card H := Subgroup.card_dvd_of_le hle1
    rw [hcz, hk] at hdvd
    have hk1 : k = 1 := by
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · rw [pow_zero] at hdvd
        exact absurd (Nat.le_of_dvd one_pos hdvd) (by have := hp.two_le; omega)
      · rfl
    subst hk1
    have heq : Subgroup.zpowers a = H := Subgroup.eq_of_le_of_card_ge hle1 (by rw [hk, hcz, pow_one])
    exact hba (heq ▸ hbH)
  have hkle : k ≤ 2 := by
    have h1 : Nat.card H ≤ Nat.card S := Subgroup.card_le_of_le hHS
    have h2 : Nat.card S ≤ Nat.card (ZMod p × ZMod p) := Finite.card_range_le φ
    rw [Nat.card_prod, Nat.card_zmod, hk] at *
    have h3 : p ^ k ≤ p ^ 2 := by
      calc p ^ k ≤ Nat.card S := h1
        _ ≤ p * p := h2
        _ = p ^ 2 := by ring
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h3
  rw [hk, le_antisymm hkle hk2]

end Pair

section General

open Matrix CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [Finite F]

theorem uniPlaneGen_or_heis {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card F = ℓ ^ f) {n : ℕ} (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hpn : p ∣ n) (hpF : p ∣ Nat.card F - 1) {E : Subgroup (MulAut (projectiveSL n F))}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2) :
    Inputs2311c.UniPlaneGen ℓ E ∨ (E ≤ linearAutGroup n F ∧ n = p ∧
      ∃ A B : GL (Fin n) F, conjAut n F A ∈ E ∧ conjAut n F B ∈ E ∧ A * B ≠ B * A) := by
  haveI : CharP F ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hchar : ringChar F = ℓ := ringChar.eq F ℓ
  have hpF0 : (p : F) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff F ℓ] at h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h0).symm
  by_cases hD : E ≤ linearAutGroup n F
  · rcases lift_dichotomy hn hp hp2 hE hc hD hpn hpF with ⟨W, hW0, hWt, hWE⟩ | ⟨hnp, hnonab⟩
    · left
      have h := uniPlaneGen_of_liftStable hn hp hpF0 hE hc hD hW0 hWt hWE
      rwa [hchar] at h
    · exact Or.inr ⟨hD, hnp, hnonab⟩
  · left
    have h := Inputs2311c.uniPlaneGen_of_field_outer hℓ hf hn hK hp hp2 hpℓ hE hc hD
    rwa [hchar] at h

theorem lifts_commute_of_commute {n : ℕ} (hn : 3 ≤ n) {E : Subgroup (MulAut (projectiveSL n F))}
    {X W : GL (Fin n) F} (hgen : Subgroup.zpowers (conjAut n F X) ⊔ Subgroup.zpowers (conjAut n F W) = E)
    (hXW : X * W = W * X) {A B : GL (Fin n) F} (hA : conjAut n F A ∈ E) (hB : conjAut n F B ∈ E) :
    A * B = B * A := by
  set S : Set (GL (Fin n) F) := {X, W} ∪ Set.range (GeneralLinearGroup.scalar (Fin n)) with hS
  have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    simp only [hS, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hx hy
    rcases hx with (rfl | rfl) | ⟨c, rfl⟩ <;> rcases hy with (rfl | rfl) | ⟨d, rfl⟩
    all_goals first
      | rfl
      | exact hXW
      | exact hXW.symm
      | exact (mul_scalarGL_comm _ _).symm
      | exact mul_scalarGL_comm _ _
  have hK : ∀ c : Fˣ, GeneralLinearGroup.scalar (Fin n) c ∈ Subgroup.closure S := fun c =>
    Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
  have hXK : X ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inl (Or.inl rfl))
  have hWK : W ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inl (Or.inr rfl))
  have h1 := mem_of_conjAut_mem_of_sup_eq hn hgen hK hXK hWK rfl rfl hA
  have h2 := mem_of_conjAut_mem_of_sup_eq hn hgen hK hXK hWK rfl rfl hB
  letI : CommGroup (Subgroup.closure S) :=
    Subgroup.closureCommGroupOfComm fun x hx y hy _ => hSc x hx y hy
  exact congrArg Subtype.val (mul_comm (⟨A, h1⟩ : Subgroup.closure S) ⟨B, h2⟩)

theorem qcomm_pow_left' {G : Type*} [Group G] {A B w : G} (hw : ∀ g : G, g * w = w * g)
    (hBA : B * A = w * (A * B)) (k : ℕ) : B ^ k * A = w ^ k * (A * B ^ k) := by
  have hwk : ∀ (m : ℕ) (g : G), g * w ^ m = w ^ m * g := by
    intro m g
    induction m with
    | zero => simp
    | succ j ihj => rw [pow_succ, ← mul_assoc, ihj, mul_assoc, hw, ← mul_assoc]
  induction k with
  | zero => simp
  | succ k ih =>
    calc B ^ (k + 1) * A = B * (B ^ k * A) := by rw [pow_succ', mul_assoc]
      _ = B * (w ^ k * (A * B ^ k)) := by rw [ih]
      _ = w ^ k * (B * A * B ^ k) := by
        rw [← mul_assoc, hwk k B, mul_assoc, mul_assoc]
      _ = w ^ k * (w * (A * B) * B ^ k) := by rw [hBA]
      _ = w ^ (k + 1) * (A * B ^ (k + 1)) := by
        rw [pow_succ w k, pow_succ' B k]
        simp only [mul_assoc]

end General

section Thm4Rest

open Matrix CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut autBar)

variable {G : Type} [Group G] [Finite G]

theorem catAct_eq_one {p : ℕ} (hp : p.Prime) {a : G} {K A0 : Subgroup G} (hK : GLAPComponent p (Cg a) K)
    {d : TauCeti.ValidLieTypeIndex} (θ : barOf p K ⧸ Subgroup.center (barOf p K) ≃* Cat d)
    (hF : ∀ x ∈ A0, x ∈ centBar p ⊤ K → x = 1) {x : ↥(Subgroup.normalizer (K : Set G))}
    (hx : (x : G) ∈ A0) (h1 : Inputs2311c.catAct θ x = 1) : (x : G) = 1 := by
  have hperf : commutator (barOf p K) = ⊤ := (l119_isQuasisimple_barOf hp hK).1
  have h2 : quotientCenterAut' (barOf p K) (barAut p K x) = 1 := by
    have h3 : (MulAut.congr θ) (quotientCenterAut' (barOf p K) (barAut p K x)) = 1 := h1
    rwa [MulEquiv.map_eq_one_iff] at h3
  have h4 : barAut p K x = 1 := quotientCenterAut'_injective hperf (by rw [h2, map_one])
  exact hF _ hx (Subgroup.mem_inf.2 ⟨⟨x, MonoidHom.mem_ker.2 h4, rfl⟩, Subgroup.mem_top _⟩)

theorem thm4Rest_linear {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hqp : q ≠ p) {a : G} {K E A : Subgroup G} (hK : GLAPComponent p (Cg a) K)
    {m : ℕ} {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A m Q).Valid) (hQq : Q.p = q)
    (hpQ : p ∣ Q.card - 1) (hpm : p ∣ m + 1)
    (θ : barOf p K ⧸ Subgroup.center (barOf p K) ≃* Cat ⟨.A m Q, hv⟩)
    (hA0C : E ⊓ A ≤ Cg a) (hA0el : IsElemAbelian p (E ⊓ A)) (hA0r : 2 ≤ CFSG.Open.pRank p (E ⊓ A))
    (hN : E ⊓ A ≤ Subgroup.normalizer (K : Set G)) (hF : ∀ x ∈ E ⊓ A, x ∈ centBar p ⊤ K → x = 1)
    (hIii : ¬ Prop1116Iii p q E A K) :
    barX p (Cg a) K ≤ ⨆ (z : ↥(Cg a)) (_ : (z : G) ∈ E ⊓ A) (_ : z ≠ 1),
      CFSG.GH74.GLS.oPrimeResidualOf q (barX p (Cg a) K ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  set A0 := E ⊓ A with hA0
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hNdef
  set F := GaloisField Q.p Q.exponent with hFdef
  have hcardF : Nat.card F = Q.p ^ Q.exponent := GaloisField.card _ _ Q.exponent_pos.ne'
  have hpF : p ∣ Nat.card F - 1 := by rw [hcardF, ← TauCeti.PrimePower.card_def]; exact hpQ
  have hpℓ : p ≠ Q.p := by rw [hQq]; exact Ne.symm hqp
  have hn3 : 3 ≤ m + 1 := by
    obtain ⟨j, hj⟩ := hpm
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    rcases j with _ | j
    · omega
    · nlinarith
  let e : Cat ⟨.A m Q, hv⟩ ≃* projectiveSL (m + 1) F :=
    ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m Q hv).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (m + 1) F)).trans
      (BalanceLp.statedProjEquivProjectiveSL (m + 1) F)
  set ψ : ↥N →* MulAut (projectiveSL (m + 1) F) :=
    (MulAut.congr e).toMonoidHom.comp (Inputs2311c.catAct θ) with hψ
  suffices hD : ∃ D : Subgroup G, D ≤ A0 ∧ Inputs2311c.UniPlaneGen q ((D.subgroupOf N).map ψ) by
    obtain ⟨D, hDA, hgen⟩ := hD
    have hgen' : Inputs2311c.UniPlaneGen q ((D.subgroupOf N).map (Inputs2311c.catAct θ)) := by
      have h1 : (D.subgroupOf N).map ψ =
          ((D.subgroupOf N).map (Inputs2311c.catAct θ)).map (MulAut.congr e).toMonoidHom := by
        rw [hψ, Subgroup.map_map]
      rw [h1] at hgen
      exact (Inputs2311c.uniPlaneGen_map_congr e q _).1 hgen
    exact Inputs2311c.le_iSup_of_uniPlaneGen hp hq hqp hK θ hA0C hN hDA hgen'
  have hψ1 : ∀ x : ↥N, (x : G) ∈ A0 → ψ x = 1 → (x : G) = 1 := fun x hx h1 =>
    catAct_eq_one hp hK θ hF hx ((MulAut.congr e).map_eq_one_iff.1 h1)
  have hA0comm : ∀ x ∈ A0, ∀ y ∈ A0, Commute x y := fun x hx y hy =>
    congrArg Subtype.val (hA0el.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hplane : ∀ x : ↥N, (x : G) ∈ A0 → (x : G) ≠ 1 → ∀ y : ↥N, (y : G) ∈ A0 →
      (y : G) ∉ Subgroup.zpowers (x : G) →
      Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G) ≤ A0 ∧
        IsElemAbelian p (((Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G)).subgroupOf N).map ψ) ∧
        Nat.card (((Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G)).subgroupOf N).map ψ) = p ^ 2 ∧
        Subgroup.zpowers (ψ x) ⊔ Subgroup.zpowers (ψ y) =
          ((Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G)).subgroupOf N).map ψ := by
    intro x hx hx1 y hy hyx
    set D := Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G) with hDdef
    have hDA : D ≤ A0 := sup_le (Subgroup.zpowers_le.2 hx) (Subgroup.zpowers_le.2 hy)
    obtain ⟨hDel, hDc⟩ := sup_zpowers_facts hp (hA0comm _ hx _ hy) (hA0el.2 _ hx) (hA0el.2 _ hy) hx1 hyx
    obtain ⟨hE1, hEc⟩ := Inputs2311c.catAct_plane hp hK θ hN hF hDA hDel hDc
    have hEel : IsElemAbelian p ((D.subgroupOf N).map ψ) := by
      rw [hψ, ← Subgroup.map_map]
      exact CFSG.Open.IsElemAbelian.map hE1 _
    have hEcard : Nat.card ((D.subgroupOf N).map ψ) = p ^ 2 := by
      rw [hψ, ← Subgroup.map_map, Subgroup.card_map_of_injective (MulAut.congr e).injective, hEc]
    have hxD : x ∈ D.subgroupOf N := Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    have hyD : y ∈ D.subgroupOf N := Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    have hψx1 : ψ x ≠ 1 := fun h => hx1 (hψ1 x hx h)
    have hψyx : ψ y ∉ Subgroup.zpowers (ψ x) := by
      intro hmemz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmemz
      apply hyx
      have h1 : ψ (y * (x ^ k)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
      have hmem : ((y * (x ^ k)⁻¹ : ↥N) : G) ∈ A0 := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
        exact A0.mul_mem hy (A0.inv_mem (A0.zpow_mem hx k))
      have h2 := hψ1 _ hmem h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow] at h2
      exact ⟨k, (mul_inv_eq_one.1 h2).symm⟩
    refine ⟨hDA, hEel, hEcard, ?_⟩
    exact zpowers_sup_zpowers_eq_of_card_sq hp hEel.2 hEcard (Subgroup.mem_map_of_mem _ hxD) hψx1
      (Subgroup.mem_map_of_mem _ hyD) hψyx
  have hmodel : ∀ x : ↥N, (x : G) ∈ A0 → (x : G) ≠ 1 → ∀ y : ↥N, (y : G) ∈ A0 →
      (y : G) ∉ Subgroup.zpowers (x : G) →
      Inputs2311c.UniPlaneGen q
          (((Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G)).subgroupOf N).map ψ) ∨
        ((((Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G)).subgroupOf N).map ψ ≤
            linearAutGroup (m + 1) F) ∧ m + 1 = p ∧
          ∃ A' B' : GL (Fin (m + 1)) F,
            conjAut (m + 1) F A' ∈ ((Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G)).subgroupOf N).map ψ ∧
            conjAut (m + 1) F B' ∈ ((Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G)).subgroupOf N).map ψ ∧
            A' * B' ≠ B' * A') := by
    intro x hx hx1 y hy hyx
    obtain ⟨-, hEel, hEcard, -⟩ := hplane x hx hx1 y hy hyx
    rcases uniPlaneGen_or_heis Q.prime_p Q.exponent_pos hcardF hn3 hp hp2 hpℓ hpm hpF hEel hEcard with h | h
    · left
      rw [← hQq]
      exact h
    · exact Or.inr h
  have hcommPlane : ∀ x : ↥N, (x : G) ∈ A0 → (x : G) ≠ 1 → ∀ y : ↥N, (y : G) ∈ A0 →
      (y : G) ∉ Subgroup.zpowers (x : G) → ∀ X Y : GL (Fin (m + 1)) F, conjAut (m + 1) F X = ψ x →
      conjAut (m + 1) F Y = ψ y → X * Y = Y * X →
      ∃ D : Subgroup G, D ≤ A0 ∧ Inputs2311c.UniPlaneGen q ((D.subgroupOf N).map ψ) := by
    intro x hx hx1 y hy hyx X Y hX hY hXY
    obtain ⟨hDA, -, -, hgen⟩ := hplane x hx hx1 y hy hyx
    rcases hmodel x hx hx1 y hy hyx with h | ⟨-, -, A', B', hA', hB', hAB'⟩
    · exact ⟨_, hDA, h⟩
    · rw [← hX, ← hY] at hgen
      exact absurd (lifts_commute_of_commute hn3 hgen hXY hA' hB') hAB'
  have hA0card : p ^ 2 ≤ Nat.card A0 := by
    obtain ⟨D₀, hD₀A, -, hD₀c⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hA0r
    rw [← hD₀c]
    exact Subgroup.card_le_of_le hD₀A
  have hindep : ∀ x ∈ A0, ∃ y ∈ A0, y ∉ Subgroup.zpowers x := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have hle : A0 ≤ Subgroup.zpowers x := hcon
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card (Subgroup.zpowers x) ≤ p := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hA0el.2 x hx))
    have : p ^ 2 ≤ p := hA0card.trans (h1.trans h2)
    nlinarith [hp.two_le]
  obtain ⟨x₀, hx₀A, hx₀1⟩ : ∃ x ∈ A0, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : A0 = ⊥ := (Subgroup.eq_bot_iff_forall A0).2 hcon
    rw [this, Subgroup.card_bot] at hA0card
    nlinarith [hp.two_le]
  by_cases hout : ∃ x : ↥N, (x : G) ∈ A0 ∧ ψ x ∉ linearAutGroup (m + 1) F
  · obtain ⟨x, hx, hxl⟩ := hout
    have hx1 : (x : G) ≠ 1 := fun h => hxl (by
      rw [show x = 1 from Subtype.ext h, map_one]; exact one_mem _)
    obtain ⟨y, hy, hyx⟩ := hindep _ hx
    set y' : ↥N := ⟨y, hN hy⟩
    obtain ⟨hDA, -, -, hgen⟩ := hplane x hx hx1 y' hy hyx
    rcases hmodel x hx hx1 y' hy hyx with h | ⟨hle, -⟩
    · exact ⟨_, hDA, h⟩
    · exact absurd (hle (hgen ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers _))) hxl
  push Not at hout
  set x' : ↥N := ⟨x₀, hN hx₀A⟩ with hx'
  obtain ⟨y₀, hy₀A, hy₀x⟩ := hindep _ hx₀A
  set y' : ↥N := ⟨y₀, hN hy₀A⟩ with hy'
  obtain ⟨X, hX⟩ := mem_linearAutGroup_iff.1 (hout x' hx₀A)
  obtain ⟨Y, hY⟩ := mem_linearAutGroup_iff.1 (hout y' hy₀A)
  by_cases hXY : X * Y = Y * X
  · exact hcommPlane x' hx₀A hx₀1 y' hy₀A hy₀x X Y hX hY hXY
  obtain ⟨hD₁A, hE₁el, hE₁c, hgen₁⟩ := hplane x' hx₀A hx₀1 y' hy₀A hy₀x
  by_cases hcard : Nat.card A0 = p ^ 2
  ·
    have hD₁eq : Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀ = A0 :=
      Subgroup.eq_of_le_of_card_ge hD₁A (by
        rw [hcard, (sup_zpowers_facts hp (hA0comm _ hx₀A _ hy₀A) (hA0el.2 _ hx₀A) (hA0el.2 _ hy₀A)
          hx₀1 hy₀x).2])
    rcases hmodel x' hx₀A hx₀1 y' hy₀A hy₀x with h | ⟨hle, hmp, A', B', hA', hB', hAB'⟩
    · exact ⟨_, hD₁A, h⟩
    exfalso
    apply hIii
    subst hmp
    let θ'' : barOf (m + 1) K ⧸ Subgroup.center (barOf (m + 1) K) ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSL (m + 1) F) :=
      θ.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m Q hv).trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (m + 1) F))
    have hBmap : (autBar (m + 1) A0 K).map
        (BalanceLp.modelHom (θ''.trans (BalanceLp.statedProjEquivProjectiveSL (m + 1) F))) =
          ((Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀).subgroupOf N).map ψ := by
      rw [hD₁eq, autBar, Subgroup.map_map, inf_eq_left.2 hN]
      congr 1
    have hDp : IsPGroup (m + 1) ((autBar (m + 1) A0 K).map
        (BalanceLp.modelHom (θ''.trans (BalanceLp.statedProjEquivProjectiveSL (m + 1) F)))) := by
      rw [hBmap]
      exact CFSG.Open.IsElemAbelian.isPGroup hE₁el
    have hDr : (autBar (m + 1) A0 K).map
        (BalanceLp.modelHom (θ''.trans (BalanceLp.statedProjEquivProjectiveSL (m + 1) F))) ≤
          (conjAut (m + 1) F).range := by
      rw [hBmap]
      intro d hd
      obtain ⟨A'', hA''⟩ := mem_linearAutGroup_iff.1 (hle hd)
      exact ⟨A'', hA''⟩
    obtain ⟨P, hP, hPD, hDP⟩ := BalanceLp.exists_pGroup_image (conjAut (m + 1) F) hDp hDr
    have hnab : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
      obtain ⟨x'', hx''P, hx''⟩ := hDP _ (by rw [hBmap]; exact hA')
      obtain ⟨y'', hy''P, hy''⟩ := hDP _ (by rw [hBmap]; exact hB')
      refine ⟨x'', hx''P, y'', hy''P, fun hxy => hAB' ?_⟩
      obtain ⟨c, hc⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.eq_scalar_of_conjAut_eq_one hn3
        (B := A'⁻¹ * x'') (by rw [map_mul, map_inv, hx'', inv_mul_cancel])
      obtain ⟨d, hd⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.eq_scalar_of_conjAut_eq_one hn3
        (B := B'⁻¹ * y'') (by rw [map_mul, map_inv, hy'', inv_mul_cancel])
      have hx''e : x'' = A' * GeneralLinearGroup.scalar (Fin (m + 1)) c := by rw [hc]; group
      have hy''e : y'' = B' * GeneralLinearGroup.scalar (Fin (m + 1)) d := by rw [hd]; group
      rw [hx''e, hy''e] at hxy
      exact BalanceLp.mul_comm_of_central (fun g => GeneralLinearGroup.scalar_commute c g)
        (fun g => GeneralLinearGroup.scalar_commute d g) hxy
    have hFq : Nat.card F = q ^ Q.exponent := by rw [hcardF, hQq]
    refine ⟨⟨Q.exponent, Or.inl ⟨⟨F, inferInstance, inferInstance, hFq, ⟨θ''⟩⟩, ?_,
      F, inferInstance, inferInstance, θ'', hFq, P, le_top, hP, hnab, fun b hb => ?_, fun g hg => ?_⟩⟩,
      hN, hcard, hF⟩
    · rw [← hQq, ← TauCeti.PrimePower.card_def]
      exact hpQ
    · obtain ⟨g, hgP, hg⟩ := hDP _ ⟨b, hb, rfl⟩
      exact ⟨g, hgP, BalanceLp.actsAsConj_linear θ'' b g hg.symm⟩
    · obtain ⟨b, hb, hbg⟩ := hPD g hg
      exact ⟨b, hb, BalanceLp.actsAsConj_linear θ'' b g hbg⟩
  ·
    have hD₁c : Nat.card ↥(Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀) = p ^ 2 :=
      (sup_zpowers_facts hp (hA0comm _ hx₀A _ hy₀A) (hA0el.2 _ hx₀A) (hA0el.2 _ hy₀A) hx₀1 hy₀x).2
    obtain ⟨z₀, hz₀A, hz₀D⟩ : ∃ z ∈ A0, z ∉ Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀ := by
      by_contra hcon
      push Not at hcon
      have hle : A0 ≤ Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀ := hcon
      exact hcard (le_antisymm (hD₁c ▸ Subgroup.card_le_of_le hle) hA0card)
    set z' : ↥N := ⟨z₀, hN hz₀A⟩ with hz'
    obtain ⟨Z, hZ⟩ := mem_linearAutGroup_iff.1 (hout z' hz₀A)
    have hĀel : IsElemAbelian p ((A0.subgroupOf N).map ψ) :=
      CFSG.Open.IsElemAbelian.map (l119_isElemAbelian_subgroupOf hA0el N) _
    have hXĀ : conjAut (m + 1) F X ∈ (A0.subgroupOf N).map ψ :=
      hX ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx₀A)
    have hYĀ : conjAut (m + 1) F Y ∈ (A0.subgroupOf N).map ψ :=
      hY ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hy₀A)
    have hZĀ : conjAut (m + 1) F Z ∈ (A0.subgroupOf N).map ψ :=
      hZ ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hz₀A)
    obtain ⟨u, hu⟩ := exists_scalarGL_comm hn3 hĀel hXĀ hYĀ
    obtain ⟨v, hv⟩ := exists_scalarGL_comm hn3 hĀel hXĀ hZĀ
    obtain ⟨cX, hcX⟩ := exists_scalarGL_pow hn3 hĀel hXĀ
    have hscal : ∀ {c d : Fˣ}, GeneralLinearGroup.scalar (Fin (m + 1)) c =
        GeneralLinearGroup.scalar (Fin (m + 1)) d → c = d := by
      intro c d h
      have h1 := congrArg (fun g : GL (Fin (m + 1)) F => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) 0 0) h
      simp only [scalarGL_coe_eq_smul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
      exact Units.ext h1
    have hup : u ^ p = 1 := by
      have h := qcomm_pow_eq_one (A := X) (B := Y) (mul_scalarGL_comm u) (mul_scalarGL_comm cX) hu hcX
      rw [← map_pow] at h
      exact hscal (h.trans (map_one _).symm)
    have hvp : v ^ p = 1 := by
      have h := qcomm_pow_eq_one (A := X) (B := Z) (mul_scalarGL_comm v) (mul_scalarGL_comm cX) hv hcX
      rw [← map_pow] at h
      exact hscal (h.trans (map_one _).symm)
    have hu1 : u ≠ 1 := by
      rintro rfl
      apply hXY
      rw [map_one, one_mul] at hu
      exact hu.symm
    have hprim : IsPrimitiveRoot (u : F) p := by
      rw [IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.iff_orderOf]
      exact orderOf_eq_prime hup hu1
    haveI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨t, htp, hut⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (v : F))
      (by rw [← Units.val_pow_eq_pow_val, hvp, Units.val_one])
    have hvt : v = u ^ t := Units.ext (by rw [Units.val_pow_eq_pow_val, hut])
    set i := p - t with hi
    set W : GL (Fin (m + 1)) F := Y ^ i * Z with hW
    have hYiX := qcomm_pow_left' (mul_scalarGL_comm u) hu i
    have hWX : W * X = X * W := by
      have hc1 : ∀ (c : Fˣ) (g : GL (Fin (m + 1)) F),
          g * GeneralLinearGroup.scalar (Fin (m + 1)) c = GeneralLinearGroup.scalar (Fin (m + 1)) c * g :=
        fun c g => mul_scalarGL_comm c g
      have hvu : GeneralLinearGroup.scalar (Fin (m + 1)) v * GeneralLinearGroup.scalar (Fin (m + 1)) u ^ i = 1 := by
        rw [← map_pow, ← map_mul, hvt, ← pow_add, show t + i = p by omega, hup, map_one]
      calc W * X = Y ^ i * (Z * X) := by rw [hW, mul_assoc]
        _ = Y ^ i * (GeneralLinearGroup.scalar (Fin (m + 1)) v * (X * Z)) := by rw [hv]
        _ = GeneralLinearGroup.scalar (Fin (m + 1)) v * (Y ^ i * X * Z) := by
          rw [← mul_assoc, hc1 v (Y ^ i), mul_assoc, mul_assoc]
        _ = GeneralLinearGroup.scalar (Fin (m + 1)) v *
            (GeneralLinearGroup.scalar (Fin (m + 1)) u ^ i * (X * Y ^ i) * Z) := by rw [hYiX]
        _ = (GeneralLinearGroup.scalar (Fin (m + 1)) v * GeneralLinearGroup.scalar (Fin (m + 1)) u ^ i) *
            (X * W) := by rw [hW]; simp only [mul_assoc]
        _ = X * W := by rw [hvu, one_mul]
    set w : G := y₀ ^ i * z₀ with hw
    have hwA : w ∈ A0 := A0.mul_mem (A0.pow_mem hy₀A i) hz₀A
    set w' : ↥N := ⟨w, hN hwA⟩ with hw'
    have hwW : conjAut (m + 1) F W = ψ w' := by
      have hw'e : w' = y' ^ i * z' := Subtype.ext rfl
      rw [hw'e, map_mul ψ, map_pow ψ, ← hY, ← hZ, hW, map_mul, map_pow]
    have hwx : (w' : G) ∉ Subgroup.zpowers (x' : G) := by
      intro hmem
      apply hz₀D
      have hz : z₀ = (y₀ ^ i)⁻¹ * w := by rw [hw]; group
      rw [hz]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) _)) (Subgroup.mem_sup_left hmem)
    exact hcommPlane x' hx₀A hx₀1 w' hwA hwx X W hX hwW hWX.symm

@[expose] def Thm4RestUnitary : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ {a : G} {K E A : Subgroup G}, GLAPComponent p (Cg a) K →
      (∃ (m : ℕ) (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA m Q).Valid), Q.p = q ∧
        ¬ CentralPrimeFree p (TauCeti.LieTypeIndex.twistedA m Q) ∧
        Nonempty (barOf p K ⧸ Subgroup.center (barOf p K) ≃* Cat ⟨.twistedA m Q, hv⟩)) →
      E ⊓ A ≤ Cg a → IsElemAbelian p (E ⊓ A) → 2 ≤ CFSG.Open.pRank p (E ⊓ A) →
      E ⊓ A ≤ Subgroup.normalizer (K : Set G) → (∀ x ∈ E ⊓ A, x ∈ centBar p ⊤ K → x = 1) →
      ¬ Prop1116Iii p q E A K →
      barX p (Cg a) K ≤ ⨆ (z : ↥(Cg a)) (_ : (z : G) ∈ E ⊓ A) (_ : z ≠ 1),
        CFSG.GH74.GLS.oPrimeResidualOf q (barX p (Cg a) K ⊓ Subgroup.centralizer
          ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))))

@[expose] def Thm4RestAmbig : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ {a : G} {K E A : Subgroup G}, GLAPComponent p (Cg a) K →
      CFSG.Yardstones.Md0ec50421ce4.catalogIs (barOf p K ⧸ Subgroup.center (barOf p K))
        (CFSG.Yardstones.Md0ec50421ce4.ambiguousChev q) →
      E ⊓ A ≤ Cg a → IsElemAbelian p (E ⊓ A) → 2 ≤ CFSG.Open.pRank p (E ⊓ A) →
      E ⊓ A ≤ Subgroup.normalizer (K : Set G) → (∀ x ∈ E ⊓ A, x ∈ centBar p ⊤ K → x = 1) →
      ¬ Prop1116Iii p q E A K →
      barX p (Cg a) K ≤ ⨆ (z : ↥(Cg a)) (_ : (z : G) ∈ E ⊓ A) (_ : z ≠ 1),
        CFSG.GH74.GLS.oPrimeResidualOf q (barX p (Cg a) K ⊓ Subgroup.centralizer
          ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))))

theorem input23_11Thm4Rest_of_residuals (hU : Thm4RestUnitary)
    (hAmb : Thm4RestAmbig) : Inputs2311c.Input23_11Thm4Rest := by
  intro G _ _ p q hp hp2 hq hq2 hqp a K E A hK hchev hcpf hA0C hA0el hA0r hN hF hIii
  rcases hchev with ⟨i, hi, ⟨θ⟩⟩ | hamb
  · cases i with
    | lie d =>
      have hdq : d.1.characteristic = q := hi
      have hncpf : ¬ CentralPrimeFree p d.1 := fun h => (hcpf d hdq h).false θ
      obtain ⟨d', hv⟩ := d
      cases d' with
      | A m Q =>
        have hQq : Q.p = q := by simpa using hdq
        simp only [CentralPrimeFree, not_not] at hncpf
        exact thm4Rest_linear hp hp2 hq hqp hK hv hQq hncpf.1 hncpf.2 θ hA0C hA0el hA0r hN hF hIii
      | twistedA m Q =>
        have hQq : Q.p = q := by simpa using hdq
        exact hU hp hp2 hq hq2 hqp hK ⟨m, Q, hv, hQq, hncpf, ⟨θ⟩⟩ hA0C hA0el hA0r hN hF hIii
      | _ => exact absurd (by simp [CentralPrimeFree]) hncpf
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
  · exact hAmb hp hp2 hq hq2 hqp hK hamb hA0C hA0el hA0r hN hF hIii

theorem sq_dvd_card_mulAut {p : ℕ} (hp : p.Prime) {a : G} {K A0 : Subgroup G} (hK : GLAPComponent p (Cg a) K)
    {T : Type} [Group T] [Finite T] (θ' : barOf p K ⧸ Subgroup.center (barOf p K) ≃* T)
    (hA0el : IsElemAbelian p A0) (hA0r : 2 ≤ CFSG.Open.pRank p A0)
    (hN : A0 ≤ Subgroup.normalizer (K : Set G)) (hF : ∀ x ∈ A0, x ∈ centBar p ⊤ K → x = 1) :
    p ^ 2 ∣ Nat.card (MulAut T) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut T) := Finite.of_injective (fun e : MulAut T => (e : T → T)) DFunLike.coe_injective
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hNdef
  set φ : ↥N →* MulAut T :=
    (MulAut.congr θ').toMonoidHom.comp ((quotientCenterAut' (barOf p K)).comp (barAut p K)) with hφ
  have hperf : commutator (barOf p K) = ⊤ := (l119_isQuasisimple_barOf hp hK).1
  set φ' : ↥(A0.subgroupOf N) →* MulAut T := φ.comp (A0.subgroupOf N).subtype with hφ'
  have hinj : Function.Injective φ' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h2 : quotientCenterAut' (barOf p K) (barAut p K x) = 1 := by
      have h3 : (MulAut.congr θ') (quotientCenterAut' (barOf p K) (barAut p K x)) = 1 := hx
      rwa [MulEquiv.map_eq_one_iff] at h3
    have h4 : barAut p K x = 1 := quotientCenterAut'_injective hperf (by rw [h2, map_one])
    have h5 : ((x : ↥N) : G) = 1 :=
      hF _ (Subgroup.mem_subgroupOf.1 x.2) (Subgroup.mem_inf.2 ⟨⟨x, MonoidHom.mem_ker.2 h4, rfl⟩,
        Subgroup.mem_top _⟩)
    exact (Subgroup.mem_bot).2 (Subtype.ext (Subtype.ext h5))
  have hcard : Nat.card A0 = Nat.card φ'.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv]
  obtain ⟨D₀, hD₀A, -, hD₀c⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hA0r
  have h1 : p ^ 2 ∣ Nat.card A0 := hD₀c ▸ Subgroup.card_dvd_of_le hD₀A
  rw [hcard] at h1
  exact h1.trans (Subgroup.card_subgroup_dvd_card _)

@[expose] def Thm4RestU42 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ}, p.Prime → p ≠ 2 → 3 ≠ p →
    ∀ {a : G} {K E A : Subgroup G}, GLAPComponent p (Cg a) K →
      (∃ (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 3 Q).Valid), Q.card = 2 ∧
        Nonempty (barOf p K ⧸ Subgroup.center (barOf p K) ≃* Cat ⟨.twistedA 3 Q, hv⟩)) →
      E ⊓ A ≤ Cg a → IsElemAbelian p (E ⊓ A) → 2 ≤ CFSG.Open.pRank p (E ⊓ A) →
      E ⊓ A ≤ Subgroup.normalizer (K : Set G) → (∀ x ∈ E ⊓ A, x ∈ centBar p ⊤ K → x = 1) →
      ¬ Prop1116Iii p 3 E A K →
      barX p (Cg a) K ≤ ⨆ (z : ↥(Cg a)) (_ : (z : G) ∈ E ⊓ A) (_ : z ≠ 1),
        CFSG.GH74.GLS.oPrimeResidualOf 3 (barX p (Cg a) K ⊓ Subgroup.centralizer
          ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))))

theorem not_sq_dvd_120 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ 120 := by
  intro h
  have hle : p ≤ 10 := by have := Nat.le_of_dvd (by norm_num) h; nlinarith
  have key : ∀ r : ℕ, r ≤ 10 → r.Prime → r ≠ 2 → ¬ r ^ 2 ∣ 120 := by decide
  exact key p hle hp hp2 h

theorem not_sq_dvd_1440 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ p ^ 2 ∣ 1440 := by
  intro h
  have hle : p ≤ 38 := by have := Nat.le_of_dvd (by norm_num) h; nlinarith
  have key : ∀ r : ℕ, r ≤ 38 → r.Prime → r ≠ 2 → r ≠ 3 → ¬ r ^ 2 ∣ 1440 := by decide
  exact key p hle hp hp2 hp3 h

theorem not_sq_dvd_1512 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ p ^ 2 ∣ 1512 := by
  intro h
  have hle : p ≤ 38 := by have := Nat.le_of_dvd (by norm_num) h; nlinarith
  have key : ∀ r : ℕ, r ≤ 38 → r.Prime → r ≠ 2 → r ≠ 3 → ¬ r ^ 2 ∣ 1512 := by decide
  exact key p hle hp hp2 hp3 h

theorem thm4RestAmbig_of_u42 (hU42 : Thm4RestU42) : Thm4RestAmbig := by
  intro G _ _ p q hp hp2 hq hq2 hqp a K E A hK hamb hA0C hA0el hA0r hN hF hIii
  obtain ⟨i, hi, ⟨e⟩⟩ := hamb
  cases i with
  | cyclic _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | alternating n hn =>
    rcases hi with ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩ | ⟨-, h⟩
    · exact absurd h hq2
    · exfalso
      subst h
      have h := sq_dvd_card_mulAut hp hK e hA0el hA0r hN hF
      rw [CFSG.GH74.GLS.LU.Local.Five.nat_card_mulAut_alternatingGroup_five] at h
      exact not_sq_dvd_120 hp hp2 h
    · exact absurd h hq2
    · exfalso
      subst h
      have h := (sq_dvd_card_mulAut hp hK e hA0el hA0r hN hF).trans InputsSeitz.card_mulAut_alt6_dvd
      exact not_sq_dvd_1440 hp hp2 (Ne.symm hqp) h
    · exact absurd h hq2
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | A k Q =>
      rcases k with _ | _ | k
      · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      · have hi' : (Q.card = 7 ∧ q = 2) ∨ (Q.card = 8 ∧ q = 3) := by
          simpa [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] using hi
        rcases hi' with ⟨-, h⟩ | ⟨h8, rfl⟩
        · exact absurd h hq2
        · exfalso
          have : Fact Q.p.Prime := ⟨Q.prime_p⟩
          set F := GaloisField Q.p Q.exponent
          have hF8 : Nat.card F = 2 ^ 3 := by
            rw [GaloisField.card _ _ Q.exponent_pos.ne', ← TauCeti.PrimePower.card_def, h8]
            norm_num
          let e' : barOf p K ⧸ Subgroup.center (barOf p K) ≃* CFSG.GorensteinWalter.PSL2 F :=
            e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 Q hv)
          have h := sq_dvd_card_mulAut hp hK e' hA0el hA0r hN hF
          have hAutF : Nat.card (F ≃+* F) = 3 := by
            obtain ⟨-, -, -, -, h3, -⟩ :=
              CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
                Nat.prime_two (n := 3) (by norm_num) hF8
            exact h3
          rw [CFSG.GH74.GLS.IVK.Proofs2.ivk93m12_card_aut_psl2, hAutF, hF8] at h
          norm_num at h
          exact not_sq_dvd_1512 hp hp2 (Ne.symm hqp) h
      · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
    | twistedA k Q =>
      rcases k with _ | _ | _ | _ | k
      · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      · have hi' : Q.card = 3 ∧ q = 2 := by simpa [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] using hi
        exact absurd hi'.2 hq2
      · have hi' : Q.card = 2 ∧ q = 3 := by simpa [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] using hi
        obtain ⟨h2, rfl⟩ := hi'
        exact hU42 hp hp2 hqp hK ⟨Q, hv, h2, ⟨e⟩⟩ hA0C hA0el hA0r hN hF hIii
      · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
    | _ => simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi

theorem input23_11Thm4Rest_of_unitary_u42 (hU : Thm4RestUnitary)
    (hU42 : Thm4RestU42) : Inputs2311c.Input23_11Thm4Rest :=
  input23_11Thm4Rest_of_residuals hU (thm4RestAmbig_of_u42 hU42)

theorem not_sq_dvd_155520 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ p ^ 2 ∣ 155520 := by
  intro h
  have h1 : p ∣ 2 ^ 7 * 3 ^ 5 * 5 := (dvd_pow_self p two_ne_zero).trans (by norm_num; exact h)
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h5
  · rcases (Nat.Prime.dvd_mul hp).1 h2 with h2 | h3
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3))
  · have h5' := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h5
    subst h5'
    norm_num at h

theorem thm4RestU42_holds :
    Thm4RestU42 := by
  intro G _ _ p hp hp2 hp3 a K E A hK hU42 _ hA0el hA0r hN hF _
  exfalso
  obtain ⟨Q, hv, hQ2, ⟨θ⟩⟩ := hU42
  have : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have hQ2' : Q.p ^ Q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hQ2
  obtain ⟨hQp, hQe⟩ := (Nat.prime_two.pow_eq_iff).1 hQ2'
  obtain ⟨⟨hℓ, hf, hn3, hq⟩, Kf, _, _, hKf, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 Q hv (MulEquiv.refl _)
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData Q.p Q.exponent Kf :=
    ⟨hℓ, hf, by rw [hKf, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.nonempty_primeFormP_mulEquiv h
    (CFSG.RankThree.PartOne.KCUnitaryModel.isPrimeFormGram_idGram (n := 3 + 1) (K := Kf))
  let e' : Cat ⟨.twistedA 3 Q, hv⟩ ≃*
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Kf (3 + 1)) :=
    (eT.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hq' : ¬(3 + 1 = 3 ∧ Q.p ^ Q.exponent = 2) := fun h3 => by omega
  have hC : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.IsPrimeFormGram (1 : GL (Fin (3 + 1)) Kf) :=
    CFSG.RankThree.PartOne.KCUnitaryModel.isPrimeFormGram_idGram
  obtain ⟨-, -, -, -, -, -, hsurj, hkerD, -, hinn, hDI⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_prime_form_full_semilinear_realization h hC hn3 hq'
  have h1 := sq_dvd_card_mulAut hp hK (θ.trans e') hA0el hA0r hN hF
  have hAut : Nat.card (MulAut (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Kf (3 + 1)))) =
      Nat.card (Kf ≃+* Kf) * Nat.card (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormD h
        ((1 : GL (Fin (3 + 1)) Kf) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) Kf)) := by
    have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor h hC hn3 hq').ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv] at e1
    rw [e1, hkerD]
  have hKf4 : Nat.card Kf = 2 ^ 2 := by rw [hKf, hQp, hQe]; norm_num
  obtain ⟨-, -, -, -, hAutK, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality Nat.prime_two
      (n := 2) (by norm_num) hKf4
  set P := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
    ((1 : GL (Fin (3 + 1)) Kf) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) Kf) with hPdef
  set D := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormD h
    ((1 : GL (Fin (3 + 1)) Kf) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) Kf) with hDdef
  have hinnD : CFSG.ComponentClassification.OuterAutomorphisms.inner P ≤ D := by
    intro α hα
    obtain ⟨s, rfl⟩ := (hinn α).1 hα
    exact ⟨_, rfl⟩
  have hD : Nat.card D = Nat.card (D ⧸ (CFSG.ComponentClassification.OuterAutomorphisms.inner P).subgroupOf D) *
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner P) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((CFSG.ComponentClassification.OuterAutomorphisms.inner P).subgroupOf D),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hinnD).toEquiv]
  have hP : Nat.card P = 25920 := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.twistedA 3 Q, hv⟩ P ⟨e'.symm⟩]
    show CFSG.Open.orderTwistedA 3 Q.card = 25920
    rw [hQ2]
    decide
  have hinnP : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner P) ∣ 25920 := by
    rw [← hP]
    exact Subgroup.card_range_dvd (MulAut.conj : P →* MulAut P)
  have hDI3 : Nat.card (D ⧸ (CFSG.ComponentClassification.OuterAutomorphisms.inner P).subgroupOf D) ∣ 3 := by
    have := hDI
    rwa [hQ2'] at this
  have hdvd : Nat.card (MulAut P) ∣ 155520 := by
    rw [hAut, hAutK, hD]
    exact (mul_dvd_mul_left 2 (mul_dvd_mul hDI3 hinnP)).trans (by norm_num)
  exact not_sq_dvd_155520 hp hp2 (Ne.symm hp3) (h1.trans hdvd)

theorem input23_11Thm4Rest_of_unitary
    (hU : Thm4RestUnitary) : Inputs2311c.Input23_11Thm4Rest :=
  input23_11Thm4Rest_of_unitary_u42 hU thm4RestU42_holds

end Thm4Rest

section NonCpf

open CFSG.LieType.SeitzGeneration (Cat CentralPrimeFree IsLinearIndex IsUnitaryIndex')
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

@[expose] def UniGenFiveNonCpfOn (P : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, P d → d.1.characteristic = 5 → ¬ CentralPrimeFree 3 d.1 →
    ∀ E : Subgroup (MulAut (Cat d)), IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
      (∃ e₀ ∈ E, e₀ ≠ 1 ∧ ∃ s : Cat d, s ≠ 1 ∧ e₀ s = s ∧ s ^ 5 = 1) → Inputs2311c.UniPlaneGen 5 E

theorem uniGenFiveNonCpf_linear :
    UniGenFiveNonCpfOn fun d => IsLinearIndex d.1 := by
  rintro ⟨d, hv⟩ ⟨m, q, rfl⟩ hd5 hcpf E hE hc hfive
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hq5 : q.p = 5 := by simpa using hd5
  simp only [CentralPrimeFree, not_not] at hcpf
  obtain ⟨h3q, h3m⟩ := hcpf
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  let e : Cat ⟨.A m q, hv⟩ ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL (m + 1)
      (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)
  have hchar : ringChar (GaloisField q.p q.exponent) = 5 := by rw [ringChar.eq _ q.p, hq5]
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hm3 : 3 ≤ m + 1 := by
    have h1 : 1 ≤ m := hrange.1
    obtain ⟨j, hj⟩ := h3m
    omega
  set E' := E.map (MulAut.congr e).toMonoidHom with hE'
  have hE'el : IsElemAbelian 3 E' := CFSG.Open.IsElemAbelian.map hE _
  have hE'c : Nat.card E' = 3 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.congr e).injective, hc]
  have hfive' : ∃ e₀ ∈ E', e₀ ≠ 1 ∧ ∃ s, s ≠ 1 ∧ e₀ s = s ∧ s ^ 5 = 1 := by
    obtain ⟨e₀, he₀, he₀1, s, hs1, hs, hs5⟩ := hfive
    refine ⟨MulAut.congr e e₀, Subgroup.mem_map_of_mem _ he₀, fun h => he₀1 ?_, e s,
      fun h => hs1 (e.injective (by rw [h, map_one])), ?_, by rw [← map_pow, hs5, map_one]⟩
    · exact (MulAut.congr e).injective (by rw [h, map_one])
    · simp [MulAut.congr_apply, hs]
  have h := uniPlaneGen_projectiveSL_five hchar hm3 h3m (by rw [hcardF]; exact h3q) hE'el hE'c hfive'
  exact (Inputs2311c.uniPlaneGen_map_congr e 5 E).1 h

@[expose] def UniGenFiveNonCpfUnitary : Prop := UniGenFiveNonCpfOn fun d => IsUnitaryIndex' d.1

theorem exists_orderOf_five_of_alt5 {K : Type} [Group K] [Finite K] {L : Subgroup K}
    (hL5 : IsAltType 5 (barOf 3 L)) : ∃ l ∈ L, orderOf l = 5 := by
  obtain ⟨e⟩ := hL5
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 5)) 5
    (by rw [Inputs256b.card_alt5]; norm_num)
  obtain ⟨l₀, hl₀⟩ := QuotientGroup.mk_surjective (e.symm g)
  have ht : orderOf (e.symm g) = 5 := by rw [MulEquiv.orderOf_eq, hg]
  have hdvd : 5 ∣ orderOf l₀ := by
    rw [← ht, ← hl₀]
    exact orderOf_map_dvd (QuotientGroup.mk' (GLAPPrimeCore 3 L)) l₀
  have hne : orderOf l₀ ≠ 0 := (orderOf_pos l₀).ne'
  refine ⟨((l₀ ^ (orderOf l₀ / 5) : L) : K), (l₀ ^ (orderOf l₀ / 5)).2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact orderOf_pow_orderOf_div hne hdvd

theorem agrp_image_facts {K : Type} [Group K] [Finite K] (hK : CFSG.LocalAnalysis.GLTheoremA.IsKHat K)
    (hcore : GLAPPrimeCore 3 K = ⊥) {d : TauCeti.ValidLieTypeIndex} (θ : K ⧸ Subgroup.center K ≃* Cat d)
    {x : MulAut K} (hx : orderOf x = 3) {L : Subgroup K} (hL : GLAPComponent 3 (Prop1310a5.fixedSub x) L)
    (hL5 : IsAltType 5 (barOf 3 L)) {y : K} (hyL : y ∈ L) (hy : orderOf y = 3) :
    IsElemAbelian 3 ((Prop1310a5b.Agrp x y).map ((MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K))) ∧
      Nat.card ((Prop1310a5b.Agrp x y).map ((MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K))) = 3 ^ 2 ∧
      ∃ e₀ ∈ (Prop1310a5b.Agrp x y).map ((MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K)), e₀ ≠ 1 ∧
        ∃ s : Cat d, s ≠ 1 ∧ e₀ s = s ∧ s ^ 5 = 1 := by
  set ψ : MulAut K →* MulAut (Cat d) := (MulAut.congr θ).toMonoidHom.comp (quotientCenterAut' K) with hψ
  have hψi : Function.Injective ψ :=
    (MulAut.congr θ).injective.comp (quotientCenterAut'_injective hK.1.1)
  obtain ⟨hAel, hA9⟩ := Inputs256c.agrp_facts hx hL hL5 hyL hy
  refine ⟨CFSG.Open.IsElemAbelian.map hAel ψ, by rw [Subgroup.card_map_of_injective hψi, hA9]; norm_num, ?_⟩
  obtain ⟨l, hlL, hl5⟩ := exists_orderOf_five_of_alt5 hL5
  have hxl : x l = l := hL.1 hlL
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  have hcop := Inputs2311c.coprime_card_center Nat.prime_three Nat.prime_five (by norm_num) hcore
  refine ⟨ψ x, Subgroup.mem_map_of_mem ψ (Subgroup.subset_closure (by simp)), fun h => hx1 (hψi (by
    rw [h, map_one])), θ (QuotientGroup.mk l), ?_, ?_, ?_⟩
  · intro h
    have hlZ : l ∈ Subgroup.center K := by
      rw [← QuotientGroup.eq_one_iff]
      exact θ.injective (by rw [h, map_one])
    have hdvd : orderOf l ∣ Nat.card (Subgroup.center K) := by
      have h1 := orderOf_dvd_natCard (⟨l, hlZ⟩ : Subgroup.center K)
      rwa [Subgroup.orderOf_mk] at h1
    rw [hl5] at hdvd
    exact absurd (Nat.Coprime.coprime_dvd_left hdvd hcop) (by norm_num)
  · simp [hψ, MulAut.congr, quotientCenterAut', hxl]
  · rw [← map_pow, ← QuotientGroup.mk_pow, ← hl5, pow_orderOf_eq_one, QuotientGroup.mk_one, map_one]

theorem uniGen2311FiveNonCpf_of_cat (hLin : UniGenFiveNonCpfOn fun d => IsLinearIndex d.1)
    (hUni : UniGenFiveNonCpfOn fun d => IsUnitaryIndex' d.1) : Inputs256c.UniGen2311FiveNonCpf := by
  intro K _ _ hK hcore d θ hd5 hcpf x hx L hL hL5 y hyL hy
  obtain ⟨hel, hc, hfive⟩ := agrp_image_facts hK hcore θ hx hL hL5 hyL hy
  obtain ⟨d', hv⟩ := d
  cases d' with
  | A m q => exact hLin ⟨_, hv⟩ ⟨m, q, rfl⟩ hd5 hcpf _ hel hc hfive
  | twistedA m q => exact hUni ⟨_, hv⟩ ⟨m, q, rfl⟩ hd5 hcpf _ hel hc hfive
  | _ => exact absurd (by simp [CentralPrimeFree]) hcpf

theorem uniGen2311FiveNonCpf_of_unitary (hU : UniGenFiveNonCpfUnitary) :
    Inputs256c.UniGen2311FiveNonCpf :=
  uniGen2311FiveNonCpf_of_cat uniGenFiveNonCpf_linear hU

end NonCpf

section Struct

open CFSG.LieType.SeitzGeneration (Cat)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

theorem le_glaPPrimeCoreOf_of_isSubnormal' {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {L C : Subgroup X} (h : IsSubnormal L C) (hcop : Nat.Coprime p (Nat.card L)) :
    L ≤ GLAPPrimeCoreOf p C :=
  (CFSG.HardMathSupport.Timmesfeld.Proving.le_GLAPPrimeCoreOf_of_normal le_rfl
    (fun g hg x hx => L.mul_mem (L.mul_mem hg hx) (L.inv_mem hg)) hcop).trans
    (CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal hp h)

variable {G : Type} [Group G] [Finite G]

theorem oPrimeResidualOf_le_of_qGen {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    {a : G} {K : Subgroup G} (hK : GLAPComponent p (Cg a) K) {d : TauCeti.ValidLieTypeIndex}
    (θ : barOf p K ⧸ Subgroup.center (barOf p K) ≃* Cat d) {z : ↥(Cg a)}
    (hzN : (z : G) ∈ Subgroup.normalizer (K : Set G))
    (hβ : QGen q (Inputs2311c.catAct θ ⟨(z : G), hzN⟩)) :
    CFSG.GH74.GLS.oPrimeResidualOf q (barX p (Cg a) K ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) ≤
      GLAPPrimeCoreOf p (barX p (Cg a) K ⊓ Subgroup.centralizer
          ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) ⊔
        ⨆ (Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))
          (_ : GLAPComponent p (barX p (Cg a) K ⊓ Subgroup.centralizer
              ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q ∧
            IsChevSimple q (barOf p Q ⧸ Subgroup.center (barOf p Q))),
          Q := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hNdef
  set zb : ↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a) := QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z with hzb
  set C : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) :=
    barX p (Cg a) K ⊓ Subgroup.centralizer ({zb} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))) with hC
  set R : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) := GLAPPrimeCoreOf p C ⊔
    ⨆ (Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))) (_ : GLAPComponent p C Q ∧
      IsChevSimple q (barOf p Q ⧸ Subgroup.center (barOf p Q))), Q with hR
  have hO : GLAPPrimeCore p (barOf p K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hcopZ : Nat.Coprime (Nat.card (Subgroup.center (barOf p K))) q :=
    Inputs2311c.coprime_card_center hp hq hqp hO
  set zN : ↥N := ⟨(z : G), hzN⟩ with hzN'
  set α : MulAut (barOf p K) := barAut p K zN with hα
  set β : MulAut (Cat d) := Inputs2311c.catAct θ zN with hβdef
  set π : barOf p K →* Cat d := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (barOf p K))) with hπ
  have hπs : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerπ : π.ker = Subgroup.center (barOf p K) := by
    ext x
    rw [MonoidHom.mem_ker]
    simp [π]
  have hπβ : ∀ y, π (α y) = β (π y) := fun y => (Inputs2311c.catAct_apply θ zN y).symm
  set f := quotEquivBarX hp hK.1 hK.2.1 with hf
  set F : barOf p K →* ↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a) :=
    (barX p (Cg a) K).subtype.comp f.toMonoidHom with hF
  have hFinj : Function.Injective F := Subtype.val_injective.comp f.injective
  have hFα : ∀ y, F (α y) = zb * F y * zb⁻¹ := fun y => Lemma129b.quotEquivBarX_barAut hp hK z.2 hzN y
  have hFC : (fixSubgroup α).map F = C := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.2 ⟨(f y).2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      have h := hFα y
      rw [show α y = y from hy] at h
      calc zb * F y = zb * F y * zb⁻¹ * zb := by group
        _ = F y * zb := by rw [← h]
    · intro hwCm
      obtain ⟨hwK, hwC⟩ := Subgroup.mem_inf.1 hwCm
      have hw : F (f.symm ⟨w, hwK⟩) = w := by simp [F]
      refine ⟨f.symm ⟨w, hwK⟩, ?_, hw⟩
      show α (f.symm ⟨w, hwK⟩) = f.symm ⟨w, hwK⟩
      apply hFinj
      rw [hFα, hw]
      have h1 : zb * w = w * zb := (Subgroup.mem_centralizer_iff.1 hwC) zb (Set.mem_singleton zb)
      rw [h1, mul_inv_cancel_right]
  set M : Subgroup (barOf p K) := ⨆ (L : Subgroup (barOf p K)) (_ : IsSubnormal L (fixSubgroup α) ∧
      CFSG.Open.IsQuasisimple L ∧ IsChevSimple q (L ⧸ Subgroup.center L)), L with hM
  have hMπ : (⨆ (J : Subgroup (Cat d)) (_ : IsChevSub q β J), J) ≤ M.map π := by
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨hJsn, hJq, hJchev⟩ := hJ
    obtain ⟨L, hLsn, hLq, hLmap, ⟨e⟩⟩ := exists_quasisimple_lift π hπs hkerπ.le α β hπβ hJsn hJq
    rw [← hLmap]
    exact Subgroup.map_mono (le_iSup₂_of_le (f := fun (L : Subgroup (barOf p K))
      (_ : IsSubnormal L (fixSubgroup α) ∧ CFSG.Open.IsQuasisimple L ∧
        IsChevSimple q (L ⧸ Subgroup.center L)) => L) L
      ⟨hLsn, hLq, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr e.symm hJchev⟩ le_rfl)
  have hLR : ∀ L : Subgroup (barOf p K), IsSubnormal L (fixSubgroup α) ∧ CFSG.Open.IsQuasisimple L ∧
      IsChevSimple q (L ⧸ Subgroup.center L) → L.map F ≤ R := by
    rintro L ⟨hLsn, hLq, hLchev⟩
    have hsn : IsSubnormal (L.map F) C := by rw [← hFC]; exact hLsn.map F
    set eL : L ≃* L.map F := Subgroup.equivMapOfInjective L F hFinj with heL
    have hq' : CFSG.Open.IsQuasisimple (L.map F) := hLq.of_mulEquiv eL.symm
    have e₂ : (L ⧸ Subgroup.center L) ≃* (L.map F ⧸ Subgroup.center (L.map F)) :=
      QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)
    by_cases hpL : p ∣ Nat.card (L.map F ⧸ Subgroup.center (L.map F))
    · refine le_sup_of_le_right (le_iSup₂_of_le (f := fun (Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))
        (_ : GLAPComponent p C Q ∧ IsChevSimple q (barOf p Q ⧸ Subgroup.center (barOf p Q))) => Q)
        (L.map F) ⟨?_, ?_⟩ le_rfl)
      · exact CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple hp hsn hq' hpL
      · obtain ⟨e'⟩ := nonempty_pSimple_equiv hp hq' hpL
        exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr (e₂.trans e') hLchev
    · exact le_sup_of_le_left
        (le_glaPPrimeCoreOf_of_isSubnormal' hp hsn (coprime_card_of_perfect hq'.1 hp hpL))
  have hMR : M.map F ≤ R := by
    rw [hM, Subgroup.map_iSup]
    refine iSup_le fun L => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hL => hLR L hL
  rw [CFSG.GH74.GLS.oPrimeResidualOf, Subgroup.map_le_iff_le_comap, CFSG.GH74.GLS.oPrimeResidual,
    Subgroup.closure_le]
  intro x hx
  obtain ⟨n, hn⟩ := hx
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  have hxn : (x : ↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) ^ q ^ n = 1 := by
    have h := congrArg Subtype.val hn
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
  have hxC : (x : ↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) ∈ (fixSubgroup α).map F := by rw [hFC]; exact x.2
  obtain ⟨y, hy, hyx⟩ := hxC
  show (x : ↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) ∈ R
  rw [← hyx]
  have hyn : y ^ q ^ n = 1 := hFinj (by rw [map_pow, map_one, hyx]; exact hxn)
  have hs : π y ∈ ⨆ (J : Subgroup (Cat d)) (_ : IsChevSub q β J), J :=
    hβ (π y) (by rw [← hπβ, show α y = y from hy]) ⟨n, by rw [← map_pow, hyn, map_one]⟩
  obtain ⟨m, hm, hmy⟩ := hMπ hs
  have hz : m⁻¹ * y ∈ Subgroup.center (barOf p K) := by
    rw [← hkerπ, MonoidHom.mem_ker, map_mul, map_inv, hmy, inv_mul_cancel]
  have hyM : y ∈ M := mem_of_mul_central le_rfl hcopZ hm hz hyn
  exact hMR (Subgroup.mem_map_of_mem F hyM)

@[expose] def Input14_2StructAt (R : ℕ → Prop) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p → R q →
    ∀ {a : G} {K E A : Subgroup G}, GLAPComponent p (Cg a) K →
      IsChevSimple q (barOf p K ⧸ Subgroup.center (barOf p K)) →
      E ⊓ A ≤ Cg a → IsElemAbelian p (E ⊓ A) → 2 ≤ CFSG.Open.pRank p (E ⊓ A) →
      E ⊓ A ≤ Subgroup.normalizer (K : Set G) → (∀ x ∈ E ⊓ A, x ∈ centBar p ⊤ K → x = 1) →
      ¬ Prop1116Iii p q E A K →
      (∀ z : ↥(Cg a), (z : G) ∈ E ⊓ A → z ≠ 1 →
        CFSG.GH74.GLS.oPrimeResidualOf q (barX p (Cg a) K ⊓ Subgroup.centralizer
            ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) ≤
          GLAPPrimeCoreOf p (barX p (Cg a) K ⊓ Subgroup.centralizer
              ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} :
                Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) ⊔
            ⨆ (Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))
              (_ : GLAPComponent p (barX p (Cg a) K ⊓ Subgroup.centralizer
                  ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} :
                    Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q ∧
                IsChevSimple q (barOf p Q ⧸ Subgroup.center (barOf p Q))),
              Q) ∨
      barX p (Cg a) K ≤
        ⨆ (z : ↥(Cg a)) (_ : (z : G) ∈ E ⊓ A) (_ : z ≠ 1),
          ⨆ (Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))
            (_ : GLAPComponent p (barX p (Cg a) K ⊓ Subgroup.centralizer
                ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} :
                  Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q ∧
              IsChevSimple q (barOf p Q ⧸ Subgroup.center (barOf p Q))),
            Q

theorem input14_2Struct_of_at (h : Input14_2StructAt fun _ => True) : Inputs2311.Input14_2Struct := by
  intro G _ _ p q hp hp2 hq hq2 hqp a K E A hK hchev hA0C hA0el hA0r hN hF hIii
  exact h hp hp2 hq hq2 hqp trivial hK hchev hA0C hA0el hA0r hN hF hIii

theorem input14_2StructAt_five_le (hQ : QGenOn fun _ => True) : Input14_2StructAt (5 ≤ ·) := by
  intro G _ _ p q hp hp2 hq hq2 hqp hq5 a K E A hK hchev hA0C hA0el hA0r hN hF hIii
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hchev with ⟨i, hi, ⟨θ⟩⟩ | hamb
  · cases i with
    | lie d =>
      have hdq : d.1.characteristic = q := hi
      left
      intro z hzA hz1
      have hzN : (z : G) ∈ Subgroup.normalizer (K : Set G) := hN hzA
      have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
      have hord : orderOf (Inputs2311c.catAct θ ⟨(z : G), hzN⟩) = p := by
        have hzp : (⟨(z : G), hzN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ p = 1 :=
          Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hA0el.2 _ hzA)
        refine orderOf_eq_prime (by rw [← map_pow, hzp, map_one]) fun h1 => hz1' ?_
        exact catAct_eq_one hp hK θ hF hzA h1
      have hQd := hQ d trivial (by rw [hdq]; exact hq5) p hp hp2 (by rw [hdq]; exact Ne.symm hqp) _ hord
      rw [hdq] at hQd
      exact oPrimeResidualOf_le_of_qGen hp hq hqp hK θ hzN hQd
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
  · exfalso
    obtain ⟨i, hi, ⟨e⟩⟩ := hamb
    cases i with
    | cyclic _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | alternating n hn =>
      rcases hi with ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩ | ⟨-, h⟩
      · omega
      · have h120 := sq_dvd_card_mulAut hp hK e hA0el hA0r hN hF
        rw [CFSG.GH74.GLS.LU.Local.Five.nat_card_mulAut_alternatingGroup_five] at h120
        exact not_sq_dvd_120 hp hp2 h120
      · omega
      · omega
      · omega
    | lie d =>
      obtain ⟨d1, hv⟩ := d
      cases d1 with
      | A k Q =>
        rcases k with _ | _ | k
        · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
        · have hi' : (Q.card = 7 ∧ q = 2) ∨ (Q.card = 8 ∧ q = 3) := by
            simpa [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] using hi
          omega
        · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      | twistedA k Q =>
        rcases k with _ | _ | _ | _ | k
        · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
        · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
        · have hi' : Q.card = 3 ∧ q = 2 := by simpa [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] using hi
          omega
        · have hi' : Q.card = 2 ∧ q = 3 := by simpa [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] using hi
          omega
        · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      | _ => simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi

@[expose] def Input14_2StructThree : Prop := Input14_2StructAt (· = 3)

theorem input14_2Struct_of_residuals (hSO : QGenSympOrth) (hE : QGenExc) (h3 : Input14_2StructThree) :
    Inputs2311.Input14_2Struct := by
  intro G _ _ p q hp hp2 hq hq2 hqp a K E A hK hchev hA0C hA0el hA0r hN hF hIii
  rcases Nat.lt_or_ge q 5 with h | h
  · have hq3 : q = 3 := by
      have h2 := hq.two_le
      have h234 : q = 2 ∨ q = 3 ∨ q = 4 := by omega
      rcases h234 with rfl | rfl | rfl
      · exact absurd rfl hq2
      · rfl
      · exact absurd hq (by norm_num)
    exact h3 hp hp2 hq hq2 hqp hq3 hK hchev hA0C hA0el hA0r hN hF hIii
  · exact input14_2StructAt_five_le (qGenOn_of_residuals hSO hE) hp hp2 hq hq2 hqp h hK hchev hA0C hA0el hA0r
      hN hF hIii

end Struct

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256e

end
