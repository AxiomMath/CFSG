module

public import CFSG.LieType.SeitzGeneration.OuterLinearWide

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Action

variable {F : Type*} [Field F] {n : ℕ}

@[expose] def conjActionGL : GL (Fin n) F →* Module.End F (Matrix (Fin n) (Fin n) F) where
  toFun g := (LinearMap.mulLeft F (g : Matrix (Fin n) (Fin n) F)).comp
    (LinearMap.mulRight F ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
  map_one' := LinearMap.ext fun φ => by simp
  map_mul' x y := LinearMap.ext fun φ => by
    simp only [LinearMap.comp_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem conjActionGL_apply (g : GL (Fin n) F) (φ : Matrix (Fin n) (Fin n) F) :
    conjActionGL g φ = (g : Matrix (Fin n) (Fin n) F) * φ *
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  simp [conjActionGL, Matrix.mul_assoc]

theorem conjActionGL_scalar (c : Fˣ) :
    conjActionGL (GeneralLinearGroup.scalar (Fin n) c) =
      (1 : Module.End F (Matrix (Fin n) (Fin n) F)) := by
  refine LinearMap.ext fun φ => ?_
  have h1 : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      φ = φ *
        ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    rw [coe_scalarGL, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  rw [conjActionGL_apply, h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rfl

theorem commute_of_conjActionGL_eq {g : GL (Fin n) F} {φ : Matrix (Fin n) (Fin n) F}
    (h : conjActionGL g φ = φ) : (g : Matrix (Fin n) (Fin n) F) * φ = φ * g := by
  have h1 := congrArg (fun M => M * (g : Matrix (Fin n) (Fin n) F)) h
  simp only [conjActionGL_apply, Matrix.mul_assoc] at h1
  rw [Units.inv_mul, Matrix.mul_one] at h1
  exact h1

theorem conjActionGL_mem_thetaSpace {W : Submodule F (Fin n → F)} {g : GL (Fin n) F}
    (hg : ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) F).mulVec w ∈ W)
    (hg' : ∀ w ∈ W, ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec w ∈ W)
    {φ : Matrix (Fin n) (Fin n) F} (hφ : φ ∈ thetaSpace W) :
    conjActionGL g φ ∈ thetaSpace W := by
  rw [conjActionGL_apply, mem_thetaSpace]
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hg _ ((mem_thetaSpace.1 hφ).1 _)
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      (mem_thetaSpace.1 hφ).2 _ (hg' w hw), Matrix.mulVec_zero]

end Action

section Maschke

variable {F : Type*} [Field F] {n : ℕ}

theorem exists_invariant_compl_gl [Finite F] {H : Subgroup (GL (Fin n) F)}
    (hH : (Nat.card H : F) ≠ 0) {W : Submodule F (Fin n → F)}
    (hW : ∀ x ∈ H, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) :
    ∃ W' : Submodule F (Fin n → F), IsCompl W W' ∧
      ∀ x ∈ H, ∀ w ∈ W', (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W' := by
  have : NeZero (Nat.card H : F) := ⟨hH⟩
  let ρ : Representation F H (Fin n → F) :=
    { toFun := fun h => Matrix.toLin' (((h : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F)
      map_one' := LinearMap.ext fun v => by simp
      map_mul' := fun a b => LinearMap.ext fun v => by
        simp [Matrix.toLin'_mul] }
  let σ : Subrepresentation ρ := ⟨W, fun g v hv => hW g g.2 v hv⟩
  obtain ⟨σ', hσ'⟩ := exists_isCompl σ
  refine ⟨σ'.toSubmodule, ⟨?_, ?_⟩, fun x hx w hw => σ'.apply_mem_toSubmodule ⟨x, hx⟩ hw⟩
  · rw [disjoint_iff]
    have := congrArg Subrepresentation.toSubmodule (disjoint_iff.1 hσ'.1)
    exact this
  · rw [codisjoint_iff]
    have := congrArg Subrepresentation.toSubmodule (codisjoint_iff.1 hσ'.2)
    exact this

end Maschke

section Order

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem card_comap_conjAut_ne_zero (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian p E) :
    (Nat.card (E.comap (conjAut n F)) : F) ≠ 0 := by
  intro h0
  set ℓ := ringChar F with hℓ
  have hℓp : ℓ.Prime := CharP.char_is_prime F ℓ
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  have hdvd : ℓ ∣ Nat.card (E.comap (conjAut n F)) := (CharP.cast_eq_zero_iff F ℓ _).1 h0
  obtain ⟨⟨A, hA⟩, hord⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  obtain ⟨c, hc⟩ := exists_scalarGL_pow hn hE (Subgroup.mem_comap.1 hA)
  have h1 : A ^ (p * Nat.card Fˣ) = 1 := by
    rw [pow_mul, hc, ← map_pow, pow_card_eq_one', map_one]
  have hordA : orderOf A = ℓ := by
    rw [← Subgroup.orderOf_mk A hA]
    exact hord
  have h2 : ℓ ∣ p * Nat.card Fˣ := hordA ▸ orderOf_dvd_of_pow_eq_one h1
  rcases (Nat.Prime.dvd_mul hℓp).1 h2 with h3 | h3
  · have h4 : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓp hp).1 h3
    apply hpF
    rw [← h4]
    exact ringChar.Nat.cast_ringChar
  · have h4 : ℓ ∣ Nat.card F := by
      letI := Fintype.ofFinite F
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff F ℓ _).1 (FiniteField.cast_card_eq_zero F)
    rw [Nat.card_eq_card_units_add_one F] at h4
    exact hℓp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h3).1 h4))

end Order

section Unip

variable {F : Type*} [Field F] [Finite F] {n : ℕ}

def unipAddSubmonoid (W : Submodule F (Fin n → F))
    (K : Subgroup (SpecialLinearGroup (Fin n) F)) : AddSubmonoid (Matrix (Fin n) (Fin n) F) where
  carrier := {ψ | ∃ h : ψ ∈ thetaSpace W, unipSL h ∈ K}
  zero_mem' := ⟨(thetaSpace W).zero_mem, by
    have : unipSL (thetaSpace W).zero_mem = 1 := Subtype.ext (by simp [coe_unipSL])
    rw [this]; exact K.one_mem⟩
  add_mem' := by
    rintro ψ ψ' ⟨h, hKψ⟩ ⟨h', hKψ'⟩
    refine ⟨(thetaSpace W).add_mem h h', ?_⟩
    have : unipSL ((thetaSpace W).add_mem h h') = unipSL h * unipSL h' := Subtype.ext (by
      show 1 + (ψ + ψ') = (1 + ψ) * (1 + ψ')
      simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, thetaSpace_mul h h',
        add_zero]
      abel)
    rw [this]; exact K.mul_mem hKψ hKψ'

theorem unipSL_mem_FixSL {W : Submodule F (Fin n → F)} {φ : Matrix (Fin n) (Fin n) F}
    (hφ : φ ∈ thetaSpace W) {g : Matrix (Fin n) (Fin n) F} (h : g * φ = φ * g) :
    unipSL hφ ∈ FixSL g := by
  apply mem_FixSL_of_mul_comm
  show g * (1 + φ) = (1 + φ) * g
  rw [Matrix.mul_add, Matrix.add_mul, h, Matrix.mul_one, Matrix.one_mul]

@[expose] def liftFixSL (E : Subgroup (MulAut (projectiveSL n F))) :
    Set (SpecialLinearGroup (Fin n) F) :=
  {k | ∃ A : GL (Fin n) F, conjAut n F A ∈ E ∧ conjAut n F A ≠ 1 ∧
    k ∈ FixSL (A : Matrix (Fin n) (Fin n) F)}

end Unip

section Main

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem unip_mem_closure_liftFixSL (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    {E : Subgroup (MulAut (projectiveSL n F))} (hE1 : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hlin : E ≤ linearAutGroup n F) {W : Submodule F (Fin n → F)} (hW : LiftStable E W)
    {g : SpecialLinearGroup (Fin n) F} (hg : (g : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W) :
    g ∈ Subgroup.closure (liftFixSL E) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set K := Subgroup.closure (liftFixSL E) with hK
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
  have hu_mem : ∀ j : ZMod p, u j ∈ unipAddSubmonoid W K := fun j => by
    refine ⟨huS j, Subgroup.subset_closure ⟨a * b ^ j.val, hline_mem _, hline_ne _, ?_⟩⟩
    have hfix : conjActionGL (a * b ^ j.val) (u j) = u j := by
      simpa only [map_mul, map_pow] using hu j
    exact unipSL_mem_FixSL (huS j) (commute_of_conjActionGL_eq hfix)
  have hv_mem : v ∈ unipAddSubmonoid W K := by
    refine ⟨hvS, Subgroup.subset_closure ⟨b, hyE, hy1, ?_⟩⟩
    exact unipSL_mem_FixSL hvS (commute_of_conjActionGL_eq hv)
  have hφT : φ ∈ unipAddSubmonoid W K := by
    rw [hsum]
    exact (unipAddSubmonoid W K).add_mem ((unipAddSubmonoid W K).sum_mem fun j _ => hu_mem j)
      hv_mem
  obtain ⟨h, hKφ⟩ := hφT
  have : unipSL h = g := Subtype.ext (by
    show 1 + φ = (g : Matrix (Fin n) (Fin n) F)
    rw [hφ]; abel)
  rwa [this] at hKφ

end Main

section Final

theorem outdiagReduciblePlanes_holds : OutdiagReduciblePlanes := by
  intro F _ _ n p hn hp _ hpF E hE hred
  obtain ⟨W, hW0, hWt, hWE⟩ := hred
  obtain ⟨hE1, hc, hlin, -⟩ := hE
  have hn3 : 3 ≤ n := by omega
  obtain ⟨W', hcompl, hW'H⟩ := exists_invariant_compl_gl (H := E.comap (conjAut n F))
    (card_comap_conjAut_ne_zero hn3 hp hpF hE1) (W := W)
    (fun x hx w hw => hWE x (Subgroup.mem_comap.1 hx) w hw)
  have hW'E : LiftStable E W' := fun A hA w hw => hW'H A (Subgroup.mem_comap.2 hA) w hw
  have hW'0 : W' ≠ ⊥ := by
    intro h
    apply hWt
    have := codisjoint_iff.1 hcompl.2
    rwa [h, sup_bot_eq] at this
  refine planeGen_of_closure_fixSL (by omega) ?_
  exact eq_top_of_unip_isCompl hcompl hW0 hW'0
    (fun g hg => unip_mem_closure_liftFixSL hn3 hp hpF hE1 hc hlin hWE hg)
    (fun g hg => unip_mem_closure_liftFixSL hn3 hp hpF hE1 hc hlin hW'E hg)

end Final

end CFSG.LieType.SeitzGeneration
