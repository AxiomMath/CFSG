module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114FactBDefs
import CFSG.RankThree.PartOne.KF.R12Lin
import CFSG.Mathlib.FieldTheory.Finite.CubeRoots
import CFSG.RankThree.PartTwo.Sec4.LThreePiRank
import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterAut
import CFSG.LocalAnalysis.GLTheoremA.CatB.SL3TorMat

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

noncomputable section

open Matrix CFSG.Open CFSG.ComponentClassification
open CFSG.HardMathSupport.Curtis.Coordinator CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.GLTheoremA.CatB.SL3Tor CFSG.RankThree.PartTwo.Sec4

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private lemma mul_comm_of_slConj_eq_one {A : GL (Fin 3) F}
    (h : CatalogueBHigherLinearAction.slConjugation 3 F A = 1)
    (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    A * (g : GL (Fin 3) F) = (g : GL (Fin 3) F) * A := by
  have h1 : A * (g : GL (Fin 3) F) * A⁻¹ = (g : GL (Fin 3) F) := by
    have h2 : Matrix.SpecialLinearGroup.toGL
        (CatalogueBHigherLinearAction.slConjugation 3 F A g) =
        (g : GL (Fin 3) F) := by
      rw [congrArg (fun e : MulAut (Matrix.SpecialLinearGroup (Fin 3) F) => e g) h]
      rfl
    rwa [CatalogueBHigherLinearAction.toGL_slConjugation] at h2
  calc A * (g : GL (Fin 3) F) = A * (g : GL (Fin 3) F) * A⁻¹ * A := by group
    _ = (g : GL (Fin 3) F) * A := by rw [h1]

private lemma exists_scalar_of_slConj_eq_one {A : GL (Fin 3) F}
    (h : CatalogueBHigherLinearAction.slConjugation 3 F A = 1) :
    ∃ c : Fˣ, A = GeneralLinearGroup.scalar (Fin 3) c := by
  have hsingle : ∀ i j : Fin 3, i ≠ j →
      Commute (Matrix.single i j 1) (A : Matrix (Fin 3) (Fin 3) F) := by
    intro i j hij
    have hmat : (A : Matrix (Fin 3) (Fin 3) F) * (1 + Matrix.single i j 1) =
        (1 + Matrix.single i j 1) * (A : Matrix (Fin 3) (Fin 3) F) := by
      have hc := mul_comm_of_slConj_eq_one h
        (⟨Matrix.transvection i j 1, by rw [Matrix.det_transvection_of_ne _ _ hij]⟩ :
          Matrix.SpecialLinearGroup (Fin 3) F)
      have hc' := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hc
      exact hc'
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at hmat
    exact (add_left_cancel hmat).symm
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (hM := hsingle)
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hunit : IsUnit (A : Matrix (Fin 3) (Fin 3) F) := A.isUnit
    rw [← hc] at hunit
    have hzero : Matrix.scalar (Fin 3) (0 : F) = 0 := by
      rw [Matrix.scalar_apply, Matrix.diagonal_zero]
    rw [hzero] at hunit
    exact hunit.ne_zero rfl
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, Units.val_mk0]
  exact hc.symm

private lemma slConj_eq_of_div_mem_statedScalars {A B : GL (Fin 3) F}
    (h : A / B ∈ StatedScalars (Fin 3) F) :
    CatalogueBHigherLinearAction.slConjugation 3 F A =
      CatalogueBHigherLinearAction.slConjugation 3 F B := by
  obtain ⟨c, hc⟩ := h
  have h1 : CatalogueBHigherLinearAction.slConjugation 3 F (A / B) = 1 := by
    rw [← hc, CatalogueBHigherLinearAction.slConjugation_scalar]
  rw [map_div] at h1
  exact div_eq_one.mp h1

private lemma exists_gl_of_mem {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card F = 2 ^ f) (h3 : ¬ 3 ∣ f)
    {H : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) F))} (hH : IsElemAbelian 3 H)
    {h : MulAut (Matrix.SpecialLinearGroup (Fin 3) F)} (hh : h ∈ H) :
    ∃ A : GL (Fin 3) F, CatalogueBHigherLinearAction.slConjugation 3 F A = h := by
  obtain ⟨A, hA⟩ := exists_slConjugation_of_three_pow (K := F) hf hk h3 (k := 1) (by
    simpa using hH.2 h hh)
  exact ⟨A, hA.symm⟩

private def pglImage (H : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) F))) :
    Subgroup (GL (Fin 3) F ⧸ StatedScalars (Fin 3) F) :=
  (H.comap (CatalogueBHigherLinearAction.slConjugation 3 F)).map
    (QuotientGroup.mk' (StatedScalars (Fin 3) F))

private lemma mem_pglImage {H : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) F))}
    {A : GL (Fin 3) F} :
    QuotientGroup.mk' (StatedScalars (Fin 3) F) A ∈ pglImage H ↔
      CatalogueBHigherLinearAction.slConjugation 3 F A ∈ H := by
  constructor
  · intro hA
    obtain ⟨B, hB, hBA⟩ := Subgroup.mem_map.mp hA
    rw [Subgroup.mem_comap] at hB
    have h1 : B / A ∈ StatedScalars (Fin 3) F := QuotientGroup.eq_iff_div_mem.mp hBA
    rw [← slConj_eq_of_div_mem_statedScalars h1]
    exact hB
  · intro hA
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_comap.mpr hA)

private lemma exists_lift_of_mem_pglImage
    {H : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) F))}
    {x : GL (Fin 3) F ⧸ StatedScalars (Fin 3) F} (hx : x ∈ pglImage H) :
    ∃ A : GL (Fin 3) F, QuotientGroup.mk' (StatedScalars (Fin 3) F) A = x ∧
      CatalogueBHigherLinearAction.slConjugation 3 F A ∈ H := by
  obtain ⟨A, hA⟩ := QuotientGroup.mk'_surjective (StatedScalars (Fin 3) F) x
  exact ⟨A, hA, mem_pglImage.mp (hA ▸ hx)⟩

private lemma pglImage_comm {H : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) F))}
    (hH : IsElemAbelian 3 H) :
    ∀ x ∈ pglImage H, ∀ y ∈ pglImage H, x * y = y * x := by
  intro x hx y hy
  obtain ⟨A, rfl, hA⟩ := exists_lift_of_mem_pglImage hx
  obtain ⟨B, rfl, hB⟩ := exists_lift_of_mem_pglImage hy
  have hcomm : CatalogueBHigherLinearAction.slConjugation 3 F A *
      CatalogueBHigherLinearAction.slConjugation 3 F B =
      CatalogueBHigherLinearAction.slConjugation 3 F B *
      CatalogueBHigherLinearAction.slConjugation 3 F A := by
    have h := (isMulCommutative_iff.mp hH.1) ⟨_, hA⟩ ⟨_, hB⟩
    simpa using h
  have h1 : CatalogueBHigherLinearAction.slConjugation 3 F (A * B * A⁻¹ * B⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  obtain ⟨c, hc⟩ := exists_scalar_of_slConj_eq_one h1
  have h2 : A * B * A⁻¹ * B⁻¹ ∈ StatedScalars (Fin 3) F := ⟨c, hc.symm⟩
  have h3 : QuotientGroup.mk' (StatedScalars (Fin 3) F) (A * B * A⁻¹ * B⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr h2
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
  have h3' : QuotientGroup.mk' (StatedScalars (Fin 3) F) A *
      QuotientGroup.mk' (StatedScalars (Fin 3) F) B *
      (QuotientGroup.mk' (StatedScalars (Fin 3) F) B *
        QuotientGroup.mk' (StatedScalars (Fin 3) F) A)⁻¹ = 1 := by
    rw [_root_.mul_inv_rev]
    simpa [mul_assoc] using h3
  exact mul_inv_eq_one.mp h3'

private lemma pglImage_pow_three {H : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) F))}
    (hH : IsElemAbelian 3 H) : ∀ x ∈ pglImage H, x ^ 3 = 1 := by
  intro x hx
  obtain ⟨A, rfl, hA⟩ := exists_lift_of_mem_pglImage hx
  have h1 : CatalogueBHigherLinearAction.slConjugation 3 F (A ^ 3) = 1 := by
    rw [map_pow, hH.2 _ hA]
  obtain ⟨c, hc⟩ := exists_scalar_of_slConj_eq_one h1
  have h2 : A ^ 3 ∈ StatedScalars (Fin 3) F := ⟨c, hc.symm⟩
  have h3 : QuotientGroup.mk' (StatedScalars (Fin 3) F) (A ^ 3) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr h2
  rwa [map_pow] at h3

private lemma three_lt_card_pglImage {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card F = 2 ^ f)
    (h3 : ¬ 3 ∣ f) {H : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) F))}
    (hH : IsElemAbelian 3 H) (hHcard : Nat.card H = 9) : 3 < Nat.card (pglImage H) := by
  have hex : ∀ h : H, ∃ A : GL (Fin 3) F,
      CatalogueBHigherLinearAction.slConjugation 3 F A = (h : MulAut _) :=
    fun h => exists_gl_of_mem hf hk h3 hH h.2
  choose A hA using hex
  have hinj : Function.Injective fun h : H =>
      (⟨QuotientGroup.mk' (StatedScalars (Fin 3) F) (A h),
        mem_pglImage.mpr (hA h ▸ h.2)⟩ : pglImage H) := by
    intro h₁ h₂ hh
    have h1 : QuotientGroup.mk' (StatedScalars (Fin 3) F) (A h₁) =
        QuotientGroup.mk' (StatedScalars (Fin 3) F) (A h₂) := congrArg Subtype.val hh
    have h2 : A h₁ / A h₂ ∈ StatedScalars (Fin 3) F := QuotientGroup.eq_iff_div_mem.mp h1
    have h3 := slConj_eq_of_div_mem_statedScalars h2
    rw [hA h₁, hA h₂] at h3
    exact Subtype.ext h3
  have hle := Nat.card_le_card_of_injective _ hinj
  omega

private def slAction : Matrix.SpecialLinearGroup (Fin 3) F →* Module.End F (Fin 3 → F) where
  toFun s := Matrix.toLin' (s : Matrix (Fin 3) (Fin 3) F)
  map_one' := by rw [Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one, Module.End.one_eq_id]
  map_mul' a b := by simp [Matrix.toLin'_mul, Module.End.mul_eq_comp]

private def fixedSpace (S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) :
    Submodule F (Fin 3 → F) where
  carrier := {v | ∀ s ∈ S, (s : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v}
  add_mem' := by
    intro a b ha hb s hs
    rw [Matrix.mulVec_add, ha s hs, hb s hs]
  zero_mem' := by
    intro s _
    exact Matrix.mulVec_zero _
  smul_mem' := by
    intro c a ha s hs
    rw [Matrix.mulVec_smul, ha s hs]

private lemma fixedSpace_ne_bot {S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)}
    (hS2 : IsPGroup 2 S) : fixedSpace S ≠ ⊥ := by
  obtain ⟨v, hv0, hv⟩ := exists_fixed_ne_zero (ρ := slAction) (K := F) (V := Fin 3 → F) 2 S hS2
  intro hbot
  have hvW : v ∈ fixedSpace S := fun s hs => hv s hs
  rw [hbot] at hvW
  exact hv0 (by simpa using hvW)

private lemma fixedSpace_ne_top {S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)}
    (hSbot : S ≠ ⊥) : fixedSpace S ≠ ⊤ := by
  intro htop
  apply hSbot
  rw [Subgroup.eq_bot_iff_forall]
  intro s hs
  have h1 : Matrix.toLin' (s : Matrix (Fin 3) (Fin 3) F) = LinearMap.id := by
    apply LinearMap.ext
    intro v
    have hv : v ∈ fixedSpace S := by rw [htop]; trivial
    simpa using hv s hs
  have h2 : (s : Matrix (Fin 3) (Fin 3) F) = 1 := by
    have hh := congrArg LinearMap.toMatrix' h1
    simpa using hh
  have h3 : (s : Matrix.SpecialLinearGroup (Fin 3) F) = 1 := Subtype.ext h2
  exact h3

private lemma fixedSpace_map {H : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) F))}
    {S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)}
    (hSnorm : ∀ h ∈ H, S.map h.toMonoidHom = S) {A : GL (Fin 3) F}
    (hA : CatalogueBHigherLinearAction.slConjugation 3 F A ∈ H)
    {w : Fin 3 → F} (hw : w ∈ fixedSpace S) :
    (A : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ fixedSpace S := by
  intro s hs
  have hA' : CatalogueBHigherLinearAction.slConjugation 3 F A⁻¹ ∈ H := by
    rw [map_inv]
    exact inv_mem hA
  have ht : CatalogueBHigherLinearAction.slConjugation 3 F A⁻¹ s ∈ S := by
    rw [← hSnorm _ hA']
    exact Subgroup.mem_map_of_mem _ hs
  have hGL : (s : GL (Fin 3) F) * A =
      A * (CatalogueBHigherLinearAction.slConjugation 3 F A⁻¹ s : GL (Fin 3) F) := by
    rw [CatalogueBHigherLinearAction.toGL_slConjugation]
    group
  have hmat : (s : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) *
        (CatalogueBHigherLinearAction.slConjugation 3 F A⁻¹ s :
          Matrix (Fin 3) (Fin 3) F) := by
    have h := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hGL
    simpa using h
  calc (s : Matrix (Fin 3) (Fin 3) F) *ᵥ ((A : Matrix (Fin 3) (Fin 3) F) *ᵥ w)
      = ((s : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)) *ᵥ w :=
        Matrix.mulVec_mulVec _ _ _
    _ = ((A : Matrix (Fin 3) (Fin 3) F) *
          (CatalogueBHigherLinearAction.slConjugation 3 F A⁻¹ s :
            Matrix (Fin 3) (Fin 3) F)) *ᵥ w := by rw [hmat]
    _ = (A : Matrix (Fin 3) (Fin 3) F) *ᵥ
          ((CatalogueBHigherLinearAction.slConjugation 3 F A⁻¹ s :
            Matrix (Fin 3) (Fin 3) F) *ᵥ w) := (Matrix.mulVec_mulVec _ _ _).symm
    _ = (A : Matrix (Fin 3) (Fin 3) F) *ᵥ w := by rw [hw _ ht]

private lemma false_of_heisenberg {H : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) F))}
    {S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)}
    (hSnorm : ∀ h ∈ H, S.map h.toMonoidHom = S) (hSbot : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    {y₁ y₂ : GL (Fin 3) F} (hy₁ : CatalogueBHigherLinearAction.slConjugation 3 F y₁ ∈ H)
    (hy₂ : CatalogueBHigherLinearAction.slConjugation 3 F y₂ ∈ H) {ζ : Fˣ} (hζ1 : ζ ≠ 1)
    (hrel : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) : False := by
  have hGL : y₁ * y₂ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂ * y₁ := by
    calc y₁ * y₂ = y₁ * y₂ * y₁⁻¹ * y₁ := by group
      _ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂ * y₁ := by rw [hrel]
  have hmat : (y₁ : Matrix (Fin 3) (Fin 3) F) * (y₂ : Matrix (Fin 3) (Fin 3) F) =
      (ζ : F) • ((y₂ : Matrix (Fin 3) (Fin 3) F) * (y₁ : Matrix (Fin 3) (Fin 3) F)) := by
    have h := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hGL
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h
    have hdiag : Matrix.scalar (Fin 3) (ζ : F) = (ζ : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    rw [hdiag] at h
    simpa [Matrix.smul_mul, Matrix.one_mul] using h
  have hinj : ∀ y : GL (Fin 3) F,
      Function.Injective (Matrix.toLin' (y : Matrix (Fin 3) (Fin 3) F)) := by
    intro y a b hab
    have h1 : (y : Matrix (Fin 3) (Fin 3) F) *ᵥ (a - b) = 0 := by
      rw [Matrix.mulVec_sub, sub_eq_zero]
      simpa using hab
    have h2 : (((y⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *ᵥ
        ((y : Matrix (Fin 3) (Fin 3) F) *ᵥ (a - b)) = 0 := by rw [h1, Matrix.mulVec_zero]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at h2
    exact sub_eq_zero.mp h2
  have hcomp : Matrix.toLin' (y₁ : Matrix (Fin 3) (Fin 3) F) ∘ₗ
      Matrix.toLin' (y₂ : Matrix (Fin 3) (Fin 3) F) =
      (ζ : F) • (Matrix.toLin' (y₂ : Matrix (Fin 3) (Fin 3) F) ∘ₗ
        Matrix.toLin' (y₁ : Matrix (Fin 3) (Fin 3) F)) := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat, Matrix.smul_mulVec]
  have hW₁ : ∀ w ∈ fixedSpace S,
      Matrix.toLin' (y₁ : Matrix (Fin 3) (Fin 3) F) w ∈ fixedSpace S :=
    fun w hw => fixedSpace_map hSnorm hy₁ hw
  have hW₂ : ∀ w ∈ fixedSpace S,
      Matrix.toLin' (y₂ : Matrix (Fin 3) (Fin 3) F) w ∈ fixedSpace S :=
    fun w hw => fixedSpace_map hSnorm hy₂ hw
  have hdim : Module.finrank F (fixedSpace S) = 1 ∨ Module.finrank F (fixedSpace S) = 2 := by
    have hV : Module.finrank F (Fin 3 → F) = 3 := by simp
    have hlt := Submodule.finrank_lt (K := F) (V := Fin 3 → F) (fixedSpace_ne_top hSbot)
    rw [hV] at hlt
    have hpos : 0 < Module.finrank F (fixedSpace S) := by
      rw [Module.finrank_pos_iff_of_free]
      exact Submodule.nontrivial_iff_ne_bot.mpr (fixedSpace_ne_bot hS2)
    omega
  have hxy : ∀ v, Matrix.toLin' (y₁ : Matrix (Fin 3) (Fin 3) F)
      (Matrix.toLin' (y₂ : Matrix (Fin 3) (Fin 3) F) v) =
      (ζ : F) • Matrix.toLin' (y₂ : Matrix (Fin 3) (Fin 3) F)
        (Matrix.toLin' (y₁ : Matrix (Fin 3) (Fin 3) F) v) :=
    fun v => LinearMap.congr_fun hcomp v
  have h1 := CFSG.RankThree.PartOne.KFU.comm_scalar_pow_finrank (fixedSpace S) _ _
    hW₁ hW₂ (hinj y₁) (hinj y₂) (ζ : F) hxy
  have h2 := CFSG.RankThree.PartOne.KFU.comm_scalar_pow_finrank (⊤ : Submodule F (Fin 3 → F)) _ _
    (fun _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top) (hinj y₁) (hinj y₂) (ζ : F) hxy
  have h2' : (ζ : F) ^ 3 = 1 := by simpa using h2
  have hζeq : (ζ : F) = 1 := by
    rcases hdim with hd | hd
    · rw [hd, pow_one] at h1
      exact h1
    · rw [hd] at h1
      have h3 : (ζ : F) ^ 3 = (ζ : F) ^ 2 * (ζ : F) := by ring
      rw [h2', h1, one_mul] at h3
      exact h3.symm
  exact hζ1 (Units.ext hζeq)

private def frameDiag (c : Fin 3 → Fˣ) : GL (Fin 3) F := diagUnit (c 0) (c 1) (c 2)

private lemma frameDiag_val (c : Fin 3 → Fˣ) :
    ((frameDiag c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal fun i => (c i : F) := by
  rw [frameDiag, diagUnit_val]
  congr 1
  funext i
  fin_cases i <;> rfl

private lemma frameDiag_mul (c c' : Fin 3 → Fˣ) :
    frameDiag c * frameDiag c' = frameDiag (c * c') := by
  rw [frameDiag, frameDiag, frameDiag, diagUnit_mul]
  rfl

private lemma frameDiag_inv (c : Fin 3 → Fˣ) : (frameDiag c)⁻¹ = frameDiag c⁻¹ := by
  rw [frameDiag, frameDiag, diagUnit_inv]
  rfl

private lemma frameDiag_comm (c c' : Fin 3 → Fˣ) :
    frameDiag c * frameDiag c' = frameDiag c' * frameDiag c := by
  rw [frameDiag_mul, frameDiag_mul]
  congr 1
  funext i
  exact mul_comm _ _

private lemma det_frameDiag (c : Fin 3 → Fˣ) :
    ((frameDiag c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det =
      (c 0 : F) * (c 1 : F) * (c 2 : F) := by
  rw [frameDiag, det_diagUnit]

private lemma frameDiag_conj_mem_utriG (c : Fin 3 → Fˣ) (u : GL (Fin 3) F)
    (hu : u ∈ utriG (K := F)) :
    frameDiag c * u * (frameDiag c)⁻¹ ∈ utriG (K := F) := by
  simpa [frameDiag] using conj_diagUnit_mem_utriG (c 0) (c 1) (c 2) u hu

private lemma frameDiag_mem_normalizer (c : Fin 3 → Fˣ) :
    frameDiag c ∈ Subgroup.normalizer ((utriG (K := F)) : Set (GL (Fin 3) F)) := by
  simpa [frameDiag] using diagUnit_mem_normalizer (K := F) (c 0) (c 1) (c 2)

private lemma exists_frame_gl {b : Fin 3 → (Fin 3 → F)} (hb : LinearIndependent F b) :
    ∃ g : GL (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F) = colMat b ∧
      ∀ i, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single i 1 = b i := by
  obtain ⟨u, hu⟩ := isUnit_colMat hb
  refine ⟨u, hu, fun i => ?_⟩
  rw [hu, Matrix.mulVec_single_one]
  funext r
  rfl

private lemma frame_diag {H : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) F))}
    {b : Fin 3 → (Fin 3 → F)} (hb : LinearIndependent F b)
    (hdiag : ∀ y : GL (Fin 3) F, (y : GL (Fin 3) F ⧸ StatedScalars (Fin 3) F) ∈ pglImage H →
      ∀ i, ∃ c : F, (y : Matrix (Fin 3) (Fin 3) F) *ᵥ b i = c • b i)
    {g : GL (Fin 3) F} (hg : (g : Matrix (Fin 3) (Fin 3) F) = colMat b)
    {A : GL (Fin 3) F} (hA : (A : GL (Fin 3) F ⧸ StatedScalars (Fin 3) F) ∈ pglImage H) :
    ∃ c : Fin 3 → Fˣ, A = g * frameDiag c * g⁻¹ := by
  choose c hc using hdiag A hA
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i h0
    have hinj : Function.Injective (A : Matrix (Fin 3) (Fin 3) F).mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit]
      exact A.isUnit
    refine hb.ne_zero i ?_
    have h1 : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ b i = 0 := by rw [hc i, h0, zero_smul]
    have h2 : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ (0 : Fin 3 → F) =
        (A : Matrix (Fin 3) (Fin 3) F) *ᵥ b i := by rw [h1, Matrix.mulVec_zero]
    exact (hinj h2).symm
  refine ⟨fun i => Units.mk0 (c i) (hc0 i), ?_⟩
  have hc' : ∀ i, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ b i =
      ((fun i => Units.mk0 (c i) (hc0 i)) i : F) • b i :=
    fun i => by rw [Units.val_mk0]; exact hc i
  have h1GL : A * g = g * frameDiag (fun i => Units.mk0 (c i) (hc0 i)) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, frameDiag_val, hg]
    exact mul_colMat_eq hc'
  calc A = A * g * g⁻¹ := by group
    _ = g * frameDiag (fun i => Units.mk0 (c i) (hc0 i)) * g⁻¹ := by rw [h1GL]

private def frameConj (g : GL (Fin 3) F) :
    Matrix.SpecialLinearGroup (Fin 3) F →* GL (Fin 3) F :=
  (MulAut.conj g⁻¹).toMonoidHom.comp Matrix.SpecialLinearGroup.toGL

private lemma frameConj_apply (g : GL (Fin 3) F) (s : Matrix.SpecialLinearGroup (Fin 3) F) :
    frameConj g s = g⁻¹ * (s : GL (Fin 3) F) * g := by
  simp [frameConj, MulAut.conj_apply]

private lemma frameConj_injective (g : GL (Fin 3) F) : Function.Injective (frameConj g) := by
  intro a b hab
  apply Matrix.SpecialLinearGroup.toGL_injective
  have h := congrArg (fun x : GL (Fin 3) F => g * x * g⁻¹) hab
  rwa [show g * frameConj g a * g⁻¹ = (a : GL (Fin 3) F) from by
        rw [frameConj_apply]; group,
      show g * frameConj g b * g⁻¹ = (b : GL (Fin 3) F) from by
        rw [frameConj_apply]; group] at h

private lemma frameConj_mul_apply (g : GL (Fin 3) F) (a b : Matrix.SpecialLinearGroup (Fin 3) F) :
    frameConj g (a * b) = frameConj g a * frameConj g b := map_mul _ _ _

private def frameU (g : GL (Fin 3) F) : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
  (utriG (K := F)).comap (frameConj g)

private lemma mem_frameU {g : GL (Fin 3) F} {s : Matrix.SpecialLinearGroup (Fin 3) F} :
    s ∈ frameU g ↔ frameConj g s ∈ utriG (K := F) := Subgroup.mem_comap

private lemma frameConj_mem_normalizer {g : GL (Fin 3) F} {w : Matrix.SpecialLinearGroup (Fin 3) F}
    (hw : frameConj g w ∈ Subgroup.normalizer ((utriG (K := F)) : Set (GL (Fin 3) F))) :
    w ∈ Subgroup.normalizer (frameU g : Set (Matrix.SpecialLinearGroup (Fin 3) F)) := by
  rw [Subgroup.mem_normalizer_iff] at hw
  rw [Subgroup.mem_normalizer_iff]
  intro s
  have key : frameConj g (w * s * w⁻¹) =
      frameConj g w * frameConj g s * (frameConj g w)⁻¹ := by
    rw [frameConj_mul_apply, frameConj_mul_apply, map_inv]
  show s ∈ frameU g ↔ w * s * w⁻¹ ∈ frameU g
  rw [mem_frameU, mem_frameU, key]
  exact hw (frameConj g s)

private def omegaVec (ω : Fˣ) : Fin 3 → Fˣ := fun i => ω ^ (i : ℕ)

private lemma omegaVec_zero {ω : Fˣ} : omegaVec ω 0 = 1 := pow_zero ω

private lemma omegaVec_one {ω : Fˣ} : omegaVec ω 1 = ω := pow_one ω

private lemma omegaVec_two {ω : Fˣ} : omegaVec ω 2 = ω ^ 2 := rfl

private lemma omegaVec_pow_three {ω : Fˣ} (hω : ω ^ 3 = 1) : omegaVec ω ^ 3 = 1 := by
  funext i
  show (ω ^ (i : ℕ)) ^ 3 = 1
  rw [← pow_mul, mul_comm, pow_mul, hω, one_pow]

private lemma omegaVec_ne_one {ω : Fˣ} (hω : ω ≠ 1) : omegaVec ω ≠ 1 := by
  intro h
  apply hω
  have := congrFun h 1
  simpa [omegaVec] using this

private lemma frameDiag_eq_one {c : Fin 3 → Fˣ} (h : frameDiag c = 1) : c = 1 := by
  obtain ⟨h0, h1, h2⟩ :=
    diagUnit_eq_one (x := c 0) (y := c 1) (z := c 2) (by rw [← frameDiag]; exact h)
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private lemma frameDiag_injective : Function.Injective (frameDiag (F := F)) := by
  intro c c' h
  have h1 : frameDiag (c * c'⁻¹) = 1 := by
    rw [← frameDiag_mul, ← frameDiag_inv, h, mul_inv_cancel]
  have h2 := frameDiag_eq_one h1
  funext i
  have h3 := congrFun h2 i
  exact mul_inv_eq_one.mp (by simpa [Pi.mul_apply] using h3)

private lemma frameDiag_const (β : Fˣ) :
    frameDiag (fun _ => β) = GeneralLinearGroup.scalar (Fin 3) β := by
  apply Units.ext
  rw [frameDiag_val, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

private def utriInvol : GL (Fin 3) F := by
  have hmul : Matrix.transvection (0 : Fin 3) 1 (1 : F) * Matrix.transvection 0 1 1 = 1 := by
    rw [Matrix.transvection_mul_transvection_same (i := 0) (j := 1) (by decide) 1 1,
      CharTwo.add_self_eq_zero (1 : F), Matrix.transvection_zero]
  exact ⟨Matrix.transvection 0 1 1, Matrix.transvection 0 1 1, hmul, hmul⟩

private lemma utriInvol_mem : utriInvol (F := F) ∈ utriG (K := F) := by
  intro i j
  constructor
  · intro hji
    fin_cases i <;> fin_cases j <;>
      simp_all [utriInvol, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
        Matrix.single_apply]
  · intro hij
    subst hij
    fin_cases i <;>
      simp [utriInvol, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
        Matrix.single_apply]

private lemma utriInvol_det : Matrix.GeneralLinearGroup.det (utriInvol (F := F)) = 1 := by
  apply Units.ext
  rw [Units.val_one]
  exact Matrix.det_transvection_of_ne (i := 0) (j := 1) (by decide) 1

private lemma utriInvol_ne_one : utriInvol (F := F) ≠ 1 := by
  intro h
  have h01 := congrArg (fun x : GL (Fin 3) F => ((x : Matrix (Fin 3) (Fin 3) F)) 0 1) h
  have h1 : ((utriInvol (F := F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1 = 1 := by
    simp [utriInvol, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  rw [h1] at h01
  simp at h01

private def slOfConj (g x : GL (Fin 3) F) (hx : GeneralLinearGroup.det x = 1) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨↑(g * x * g⁻¹), by
    have h : GeneralLinearGroup.det (g * x * g⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hx, mul_one, mul_inv_cancel]
    exact congrArg (fun u : Fˣ => (u : F)) h⟩

private lemma slOfConj_val (g x : GL (Fin 3) F) (hx : GeneralLinearGroup.det x = 1) :
    ((slOfConj g x hx : GL (Fin 3) F)) = g * x * g⁻¹ := by
  refine Units.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  rfl

private lemma frameConj_slOfConj (g x : GL (Fin 3) F) (hx : GeneralLinearGroup.det x = 1) :
    frameConj g (slOfConj g x hx) = x := by
  rw [frameConj_apply, slOfConj_val]
  group

private lemma frameConj_slConj (g : GL (Fin 3) F) (c : Fin 3 → Fˣ)
    (s : Matrix.SpecialLinearGroup (Fin 3) F) :
    frameConj g (CatalogueBHigherLinearAction.slConjugation 3 F (g * frameDiag c * g⁻¹) s) =
      frameDiag c * frameConj g s * (frameDiag c)⁻¹ := by
  rw [frameConj_apply, frameConj_apply, CatalogueBHigherLinearAction.toGL_slConjugation]
  group

private lemma frameU_isPGroup (g : GL (Fin 3) F) : IsPGroup 2 (frameU g) :=
  utriG_isPGroup (K := F) |>.comap_of_injective (frameConj g) (frameConj_injective g)

private lemma frameU_ne_bot (g : GL (Fin 3) F) : frameU g ≠ ⊥ := by
  intro hbot
  have h1 : slOfConj g utriInvol utriInvol_det ∈ frameU g := by
    rw [mem_frameU, frameConj_slOfConj]
    exact utriInvol_mem
  rw [hbot] at h1
  have h2 : slOfConj g utriInvol utriInvol_det = 1 := by simpa using h1
  have h3 : utriInvol (F := F) = 1 := by
    rw [← frameConj_slOfConj g utriInvol utriInvol_det, h2, map_one]
  exact utriInvol_ne_one (F := F) h3

private lemma frameU_map {H : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) F))}
    {g : GL (Fin 3) F}
    (hframe : ∀ α ∈ H, ∃ c : Fin 3 → Fˣ,
      α = CatalogueBHigherLinearAction.slConjugation 3 F (g * frameDiag c * g⁻¹)) :
    ∀ h ∈ H, (frameU g).map h.toMonoidHom = frameU g := by
  intro h hh
  have hle : ∀ (h : MulAut (Matrix.SpecialLinearGroup (Fin 3) F)), h ∈ H →
      ∀ s : Matrix.SpecialLinearGroup (Fin 3) F, s ∈ frameU g → h s ∈ frameU g := by
    intro h hh s hs
    obtain ⟨c, hc⟩ := hframe h hh
    rw [mem_frameU] at hs ⊢
    have h1 : frameConj g (h s) = frameDiag c * frameConj g s * (frameDiag c)⁻¹ := by
      rw [hc]
      exact frameConj_slConj g c s
    rw [h1]
    exact frameDiag_conj_mem_utriG c (frameConj g s) hs
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    exact hle h hh t ht
  · intro s hs
    have hinv : (h⁻¹ : MulAut (Matrix.SpecialLinearGroup (Fin 3) F)) s ∈ frameU g :=
      hle h⁻¹ (inv_mem hh) s hs
    exact Subgroup.mem_map.mpr
      ⟨(h⁻¹ : MulAut (Matrix.SpecialLinearGroup (Fin 3) F)) s, hinv,
        MulEquiv.apply_symm_apply h s⟩

private lemma frameDiag_one : frameDiag (fun _ : Fin 3 => (1 : Fˣ)) = 1 := by
  rw [show frameDiag (fun _ : Fin 3 => (1 : Fˣ)) = diagUnit (1 : Fˣ) 1 1 from rfl]
  exact diagUnit_one

private lemma det_frameDiag_omegaVec {ω : Fˣ} (hω : ω ^ 3 = 1) :
    Matrix.GeneralLinearGroup.det (frameDiag (omegaVec ω)) = 1 := by
  have h : omegaVec ω 0 * omegaVec ω 1 * omegaVec ω 2 = 1 := by
    rw [omegaVec_zero, omegaVec_one, omegaVec_two, one_mul, mul_comm ω (ω ^ 2), ← pow_succ, hω]
  apply Units.ext
  rw [Units.val_one,
    show ((Matrix.GeneralLinearGroup.det (frameDiag (omegaVec ω)) : Fˣ) : F) =
      ((frameDiag (omegaVec ω) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det from rfl,
    det_frameDiag]
  simpa using congrArg (fun x : Fˣ => (x : F)) h

private def frameY (g : GL (Fin 3) F) (ω : Fˣ) (hω : ω ^ 3 = 1) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  slOfConj g (frameDiag (omegaVec ω)) (det_frameDiag_omegaVec hω)

private lemma conj_frameY (g : GL (Fin 3) F) (ω : Fˣ) (hω : ω ^ 3 = 1) :
    frameConj g (frameY g ω hω) = frameDiag (omegaVec ω) :=
  frameConj_slOfConj g _ _

private lemma orderOf_frameY {g : GL (Fin 3) F} {ω : Fˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    orderOf (frameY g ω hω3) = 3 := by
  rw [← orderOf_injective (frameConj g) (frameConj_injective g), conj_frameY]
  refine orderOf_eq_prime ?_ ?_
  · rw [show frameDiag (omegaVec ω) ^ 3 = frameDiag ((omegaVec ω) ^ 3) from by
      rw [pow_three, pow_three, frameDiag_mul, frameDiag_mul], omegaVec_pow_three hω3]
    exact frameDiag_one
  · intro h
    exact omegaVec_ne_one hω1 (frameDiag_eq_one (c := omegaVec ω) h)

private lemma utriInvol_frameDiag_ne (ω : Fˣ) (hω1 : ω ≠ 1) :
    utriInvol * frameDiag (omegaVec ω) ≠ frameDiag (omegaVec ω) * utriInvol := by
  intro h
  have hω1F : ((ω : F)) ≠ 1 := fun hh => hω1 (Units.ext hh)
  have h01 := congrArg (fun x : GL (Fin 3) F => ((x : Matrix (Fin 3) (Fin 3) F)) 0 1) h
  rw [Units.val_mul, Units.val_mul] at h01
  have h1 : (((utriInvol (F := F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (frameDiag (omegaVec ω) : Matrix (Fin 3) (Fin 3) F)) 0 1 = (ω : F) := by
    simp [utriInvol, frameDiag_val, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transvection,
      Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Matrix.diagonal_apply, omegaVec_one]
  have h2 : ((frameDiag (omegaVec ω) : Matrix (Fin 3) (Fin 3) F) *
      ((utriInvol (F := F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) 0 1 = 1 := by
    simp [utriInvol, frameDiag_val, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transvection,
      Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Matrix.diagonal_apply,
      omegaVec_zero]
  rw [h1, h2] at h01
  exact hω1F h01

private lemma frameY_not_central (g : GL (Fin 3) F) (ω : Fˣ) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ∃ z : Matrix.SpecialLinearGroup (Fin 3) F, z * frameY g ω hω3 ≠ frameY g ω hω3 * z := by
  refine ⟨slOfConj g utriInvol utriInvol_det, ?_⟩
  intro h
  refine utriInvol_frameDiag_ne ω hω1 ?_
  have h' := congrArg (frameConj g) h
  rwa [map_mul, map_mul, frameConj_slOfConj, conj_frameY] at h'

private lemma frameY_mem_normalizer (g : GL (Fin 3) F) (ω : Fˣ) (hω3 : ω ^ 3 = 1) :
    frameY g ω hω3 ∈
      Subgroup.normalizer (frameU g : Set (Matrix.SpecialLinearGroup (Fin 3) F)) := by
  apply frameConj_mem_normalizer
  rw [conj_frameY]
  exact frameDiag_mem_normalizer (omegaVec ω)

private lemma frameY_fixed {H : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) F))}
    {g : GL (Fin 3) F} {ω : Fˣ} (hω3 : ω ^ 3 = 1)
    (hframe : ∀ α ∈ H, ∃ c : Fin 3 → Fˣ,
      α = CatalogueBHigherLinearAction.slConjugation 3 F (g * frameDiag c * g⁻¹)) :
    ∀ h ∈ H, h (frameY g ω hω3) = frameY g ω hω3 := by
  intro h hh
  obtain ⟨c, hc⟩ := hframe h hh
  apply frameConj_injective g
  rw [hc, frameConj_slConj, conj_frameY]
  rw [frameDiag_comm c (omegaVec ω), mul_assoc, mul_inv_cancel, mul_one]

private lemma frameDiag_smul (β : Fˣ) (c : Fin 3 → Fˣ) :
    frameDiag (fun i => β * c i) = GeneralLinearGroup.scalar (Fin 3) β * frameDiag c := by
  rw [← frameDiag_const β, frameDiag_mul]
  rfl

private lemma det_frameDiag_units (c : Fin 3 → Fˣ) :
    Matrix.GeneralLinearGroup.det (frameDiag c) = c 0 * c 1 * c 2 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  simpa using det_frameDiag c

private lemma cube_ratio {g : GL (Fin 3) F} {c : Fin 3 → Fˣ}
    (h3 : CatalogueBHigherLinearAction.slConjugation 3 F (g * frameDiag c * g⁻¹) ^ 3 = 1) :
    c 1 ^ 3 = c 0 ^ 3 ∧ c 2 ^ 3 = c 0 ^ 3 := by
  obtain ⟨μ, hμ⟩ := exists_scalar_of_slConj_eq_one (A := (g * frameDiag c * g⁻¹) ^ 3) (by
    rwa [map_pow])
  have hpow : (frameDiag c) ^ 3 = frameDiag (c ^ 3) := by
    rw [pow_three, pow_three, frameDiag_mul, frameDiag_mul]
  have hconj : (g * frameDiag c * g⁻¹) ^ 3 = g * frameDiag (c ^ 3) * g⁻¹ := by
    calc (g * frameDiag c * g⁻¹) ^ 3
        = (g * frameDiag c * g⁻¹) *
            ((g * frameDiag c * g⁻¹) * (g * frameDiag c * g⁻¹)) := by rw [pow_three]
      _ = g * ((frameDiag c) * (frameDiag c) * (frameDiag c)) * g⁻¹ := by group
      _ = g * frameDiag (c ^ 3) * g⁻¹ := by
          have hd3 : frameDiag c * frameDiag c * frameDiag c = (frameDiag c) ^ 3 := by
            rw [pow_three]
            group
          rw [hd3, hpow]
  have hμ' : g * frameDiag (c ^ 3) * g⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ := by
    rw [← hconj]
    exact hμ
  have hdiag : frameDiag (c ^ 3) = GeneralLinearGroup.scalar (Fin 3) μ := by
    calc frameDiag (c ^ 3) = g⁻¹ * (g * frameDiag (c ^ 3) * g⁻¹) * g := by group
      _ = g⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ * g := by rw [hμ']
      _ = GeneralLinearGroup.scalar (Fin 3) μ := by
        rw [← Matrix.GeneralLinearGroup.scalar_commute]
        group
  have hc : c ^ 3 = fun _ => μ := by
    apply frameDiag_injective
    rw [hdiag, frameDiag_const]
  have h1' : c 1 ^ 3 = μ := by simpa using congrFun hc 1
  have h0' : c 0 ^ 3 = μ := by simpa using congrFun hc 0
  have h2' : c 2 ^ 3 = μ := by simpa using congrFun hc 2
  exact ⟨by rw [h1', h0'], by rw [h2', h0']⟩

private lemma det_cube_of_inner {g : GL (Fin 3) F} {c : Fin 3 → Fˣ}
    {k : Matrix.SpecialLinearGroup (Fin 3) F}
    (hk : ∀ z, CatalogueBHigherLinearAction.slConjugation 3 F (g * frameDiag c * g⁻¹) z =
      k * z * k⁻¹) :
    ∃ lam : Fˣ, c 0 * c 1 * c 2 = lam ^ 3 := by
  have hconj : CatalogueBHigherLinearAction.slConjugation 3 F
      (Matrix.SpecialLinearGroup.toGL k) = MulAut.conj k := by
    apply MulEquiv.ext
    intro z
    rw [MulAut.conj_apply]
    apply Matrix.SpecialLinearGroup.toGL_injective
    simpa using CatalogueBHigherLinearAction.toGL_slConjugation 3 F
      (Matrix.SpecialLinearGroup.toGL k) z
  have hA : CatalogueBHigherLinearAction.slConjugation 3 F (g * frameDiag c * g⁻¹) =
      MulAut.conj k := by
    apply MulEquiv.ext
    intro z
    rw [hk z, MulAut.conj_apply]
  have h1 : CatalogueBHigherLinearAction.slConjugation 3 F
      ((g * frameDiag c * g⁻¹) * (Matrix.SpecialLinearGroup.toGL k)⁻¹) = 1 := by
    rw [map_mul, map_inv, hA, hconj, mul_inv_cancel]
  obtain ⟨lam, hlam⟩ := exists_scalar_of_slConj_eq_one h1
  have hdet : Matrix.GeneralLinearGroup.det ((g * frameDiag c * g⁻¹) *
      (Matrix.SpecialLinearGroup.toGL k)⁻¹) =
      Matrix.GeneralLinearGroup.det (frameDiag c) := by
    rw [map_mul, map_inv, Matrix.SpecialLinearGroup.coeToGL_det, inv_one, mul_one]
    rw [map_mul, map_mul, map_inv]
    simp [mul_comm, mul_left_comm, mul_assoc]
  have hdet2 : Matrix.GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) lam) =
      Matrix.GeneralLinearGroup.det (frameDiag c) := by
    rw [← hlam]
    exact hdet
  have h3 : lam ^ 3 = Matrix.GeneralLinearGroup.det (frameDiag c) := by
    have h := hdet2
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h
    exact h
  refine ⟨lam, ?_⟩
  calc c 0 * c 1 * c 2 = Matrix.GeneralLinearGroup.det (frameDiag c) :=
        (det_frameDiag_units c).symm
    _ = lam ^ 3 := h3.symm

private lemma ratio_eq_one {g : GL (Fin 3) F} {c : Fin 3 → Fˣ}
    (h9 : ¬ 9 ∣ Nat.card F - 1)
    (hord : CatalogueBHigherLinearAction.slConjugation 3 F (g * frameDiag c * g⁻¹) ^ 3 = 1)
    (hinner : ∃ lam : Fˣ, c 0 * c 1 * c 2 = lam ^ 3) :
    (c 1 / c 0) * (c 2 / c 0) = 1 := by
  classical
  obtain ⟨h1, h2⟩ := cube_ratio hord
  obtain ⟨lam, hlam⟩ := hinner
  have hx3u : ((c 1 / c 0) * (c 2 / c 0)) ^ 3 = 1 := by
    rw [mul_pow, div_pow, div_pow, h1, h2]
    simp
  have hxu : (c 1 / c 0) * (c 2 / c 0) = (lam / c 0) ^ 3 := by
    rw [div_mul_div_comm, div_pow, ← hlam, div_eq_div_iff_mul_eq_mul]
    simp [pow_three, mul_assoc, mul_comm, mul_left_comm]
  have hx3 : (((c 1 / c 0) * (c 2 / c 0) : Fˣ) : F) ^ 3 = 1 := by
    simpa using congrArg (fun u : Fˣ => (u : F)) hx3u
  have hx : (((c 1 / c 0) * (c 2 / c 0) : Fˣ) : F) = ((lam : F) / (c 0 : F)) ^ 3 := by
    simpa using congrArg (fun u : Fˣ => (u : F)) hxu
  by_contra hx1
  exact CFSG.FiniteField.pow_three_ne_of_not_nine_dvd h9 hx3
    (fun h => hx1 (Units.ext h)) ((lam : F) / (c 0 : F)) hx.symm

private lemma ratio_injective {H : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) F))}
    {g : GL (Fin 3) F} {c : H → Fin 3 → Fˣ}
    (hc : ∀ α : H, (α : MulAut (Matrix.SpecialLinearGroup (Fin 3) F)) =
      CatalogueBHigherLinearAction.slConjugation 3 F (g * frameDiag (c α) * g⁻¹))
    (hratio1 : ∀ α : H, (c α 1 / c α 0) * (c α 2 / c α 0) = 1) :
    ∀ α α' : H, c α 1 / c α 0 = c α' 1 / c α' 0 → α = α' := by
  intro α α' hrr
  have hx2 : c α' 2 / c α' 0 = c α 2 / c α 0 := by
    have h1 := hratio1 α
    have h2 := hratio1 α'
    rw [← hrr] at h2
    exact (mul_left_cancel (h1.trans h2.symm)).symm
  apply Subtype.ext
  have hpoint : c α' = fun i => (c α' 0 / c α 0) * c α i := by
    funext i
    fin_cases i
    · exact (div_mul_cancel _ _).symm
    · calc c α' 1 = (c α' 1 / c α' 0) * c α' 0 := (div_mul_cancel _ _).symm
        _ = (c α 1 / c α 0) * c α' 0 := by rw [← hrr]
        _ = (c α' 0 / c α 0) * c α 1 := by
          simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    · calc c α' 2 = (c α' 2 / c α' 0) * c α' 0 := (div_mul_cancel _ _).symm
        _ = (c α 2 / c α 0) * c α' 0 := by rw [hx2]
        _ = (c α' 0 / c α 0) * c α 2 := by
          simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  have hdiag : frameDiag (c α') =
      GeneralLinearGroup.scalar (Fin 3) (c α' 0 / c α 0) * frameDiag (c α) := by
    conv_lhs => rw [hpoint]
    rw [frameDiag_smul]
  have hA : g * frameDiag (c α') * g⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (c α' 0 / c α 0) *
        (g * frameDiag (c α) * g⁻¹) := by
    rw [hdiag]
    have hcomm : g * GeneralLinearGroup.scalar (Fin 3) (c α' 0 / c α 0) =
        GeneralLinearGroup.scalar (Fin 3) (c α' 0 / c α 0) * g :=
      (Matrix.GeneralLinearGroup.scalar_commute _ g).symm
    calc g * (GeneralLinearGroup.scalar (Fin 3) (c α' 0 / c α 0) *
          frameDiag (c α)) * g⁻¹
        = g * GeneralLinearGroup.scalar (Fin 3) (c α' 0 / c α 0) *
            frameDiag (c α) * g⁻¹ := by group
      _ = GeneralLinearGroup.scalar (Fin 3) (c α' 0 / c α 0) * g *
            frameDiag (c α) * g⁻¹ := by rw [hcomm]
      _ = GeneralLinearGroup.scalar (Fin 3) (c α' 0 / c α 0) *
            (g * frameDiag (c α) * g⁻¹) := by group
  have hmem : (g * frameDiag (c α') * g⁻¹) / (g * frameDiag (c α) * g⁻¹) ∈
      StatedScalars (Fin 3) F := by
    rw [hA]
    have h : (GeneralLinearGroup.scalar (Fin 3) (c α' 0 / c α 0) *
        (g * frameDiag (c α) * g⁻¹)) / (g * frameDiag (c α) * g⁻¹) =
        GeneralLinearGroup.scalar (Fin 3) (c α' 0 / c α 0) := by
      rw [← mul_div_assoc', div_self', mul_one]
    rw [h]
    exact ⟨_, rfl⟩
  calc (α : MulAut (Matrix.SpecialLinearGroup (Fin 3) F)) =
      CatalogueBHigherLinearAction.slConjugation 3 F (g * frameDiag (c α) * g⁻¹) := hc α
    _ = CatalogueBHigherLinearAction.slConjugation 3 F
        (g * frameDiag (c α') * g⁻¹) := (slConj_eq_of_div_mem_statedScalars hmem).symm
    _ = (α' : MulAut (Matrix.SpecialLinearGroup (Fin 3) F)) := (hc α').symm

private lemma false_of_all_inner {H : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) F))}
    (h9 : ¬ 9 ∣ Nat.card F - 1) (hH : IsElemAbelian 3 H) (hHcard : Nat.card H = 9)
    {g : GL (Fin 3) F}
    (hframe : ∀ α ∈ H, ∃ c : Fin 3 → Fˣ,
      α = CatalogueBHigherLinearAction.slConjugation 3 F (g * frameDiag c * g⁻¹))
    (hInner : ∀ α ∈ H, orderOf α = 3 →
      ∃ k : Matrix.SpecialLinearGroup (Fin 3) F, ∀ z, α z = k * z * k⁻¹) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hex : ∀ α : H, ∃ c : Fin 3 → Fˣ,
      (α : MulAut (Matrix.SpecialLinearGroup (Fin 3) F)) =
        CatalogueBHigherLinearAction.slConjugation 3 F (g * frameDiag c * g⁻¹) ∧
      ∃ lam : Fˣ, c 0 * c 1 * c 2 = lam ^ 3 := by
    intro α
    by_cases h : (α : MulAut (Matrix.SpecialLinearGroup (Fin 3) F)) = 1
    · refine ⟨fun _ => 1, ?_, ⟨1, ?_⟩⟩
      · rw [h, frameDiag_one]
        simp
      · simp
    · obtain ⟨c, hc⟩ := hframe α α.2
      have hα3 : (α : MulAut (Matrix.SpecialLinearGroup (Fin 3) F)) ^ 3 = 1 := hH.2 α α.2
      have hord : orderOf (α : MulAut (Matrix.SpecialLinearGroup (Fin 3) F)) = 3 :=
        orderOf_eq_prime hα3 h
      obtain ⟨k, hk⟩ := hInner α α.2 hord
      refine ⟨c, hc, det_cube_of_inner (g := g) (k := k) ?_⟩
      intro z
      rw [← hc]
      exact hk z
  choose c hc hcube using hex
  have hratio1 : ∀ α : H, (c α 1 / c α 0) * (c α 2 / c α 0) = 1 := by
    intro α
    exact ratio_eq_one h9 (by rw [← hc α, hH.2 α α.2]) (hcube α)
  have hratio3 : ∀ α : H, (c α 1 / c α 0) ^ 3 = 1 := by
    intro α
    obtain ⟨h1, -⟩ := cube_ratio (g := g) (c := c α) (by rw [← hc α, hH.2 α α.2])
    rw [div_pow, h1]
    exact div_self' _
  let ratio : H → rootsOfUnity 3 F := fun α =>
    ⟨c α 1 / c α 0, by
      rw [mem_rootsOfUnity']
      simpa using congrArg (fun u : Fˣ => (u : F)) (hratio3 α)⟩
  have hinj : Function.Injective ratio := fun α α' h =>
    ratio_injective hc hratio1 α α' (congrArg Subtype.val h)
  have hle : Nat.card H ≤ Nat.card (rootsOfUnity 3 F) :=
    Nat.card_le_card_of_injective ratio hinj
  have hroot : Nat.card (rootsOfUnity 3 F) ≤ 3 := card_rootsOfUnity (R := F) (k := 3)
  omega

theorem i114CoreSL_holds : I114CoreSL := by
  intro F _ _ _ f hf hk h3 hmod H S hH hcard hSbot hS2 hSnorm
  classical
  have h3F : (3 : F) ≠ 0 := by
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have h31 : (3 : F) = 1 := by
      rw [show (3 : F) = 2 + 1 by norm_num]
      simp [h2]
    rw [h31]
    exact one_ne_zero
  have h9 : ¬ 9 ∣ Nat.card F - 1 := by
    rcases hmod with h | h <;> omega
  have h3dvd : 3 ∣ Nat.card F - 1 := by
    rcases hmod with h | h <;> omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rwa [Nat.card_units])
  have hω3 : ω ^ 3 = 1 := by
    rw [← hω]
    exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hω
    omega
  have hτ : (ω : F) ^ 3 = 1 := by
    simpa using congrArg (fun u : Fˣ => (u : F)) hω3
  have hτ1 : (ω : F) ≠ 1 := fun h1 => hω1 (Units.ext h1)
  rcases frame_or_heis (K := F) h3F hτ hτ1 (pglImage H) (pglImage_comm hH)
    (pglImage_pow_three hH) (three_lt_card_pglImage hf hk h3 hH hcard) with
    ⟨b, hb, hdiag, -⟩ | ⟨y₁, y₂, hy₁, hy₂, ζ, hζ1, hrel⟩
  · obtain ⟨g, hg, -⟩ := exists_frame_gl hb
    have hframe : ∀ α ∈ H, ∃ c : Fin 3 → Fˣ,
        α = CatalogueBHigherLinearAction.slConjugation 3 F (g * frameDiag c * g⁻¹) := by
      intro α hα
      obtain ⟨A, hA⟩ := exists_gl_of_mem hf hk h3 hH hα
      obtain ⟨c, hc⟩ := frame_diag (A := A) hb hdiag hg (mem_pglImage.mpr (by rwa [hA]))
      exact ⟨c, by rw [← hA, hc]⟩
    refine ⟨frameU g, frameU_ne_bot g, frameU_isPGroup g, frameU_map hframe,
      frameY g ω hω3, frameY_not_central g ω hω3 hω1, orderOf_frameY hω3 hω1,
      frameY_mem_normalizer g ω hω3, frameY_fixed hω3 hframe, ?_⟩
    by_contra hcon
    have hInner : ∀ α ∈ H, orderOf α = 3 →
        ∃ k : Matrix.SpecialLinearGroup (Fin 3) F, ∀ z, α z = k * z * k⁻¹ := by
      intro α hα hord
      by_contra hnot
      exact hcon ⟨α, hα, hord, hnot⟩
    exact false_of_all_inner h9 hH hcard hframe hInner
  · exact (false_of_heisenberg hSnorm hSbot hS2 (mem_pglImage.mp hy₁)
      (mem_pglImage.mp hy₂) hζ1 hrel).elim
