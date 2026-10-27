module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsInnerProd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt
open scoped IsMulCommutative

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {τ : K →+* K}
variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
variable {H : Subgroup (GL ι K)} {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K}

section Invol

variable {Aε : Subgroup (GL ι K)} [IsMulCommutative Aε] [Finite K]

theorem glEquiv_involGL (hA : ∀ a : ↥Aε, a ^ p = 1) (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (I : Finset (Hyperplane ↥Aε p)) :
    glEquiv (glEquiv.symm (invol (glRep Aε) hp hA hpK I)) = invol (glRep Aε) hp hA hpK I :=
  MulEquiv.apply_symm_apply _ _

theorem involGL_mem_isomGL (hA : ∀ a : ↥Aε, a ^ p = 1) (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (hAεβ : Aε ≤ isomGL β) (I : Finset (Hyperplane ↥Aε p)) :
    glEquiv.symm (invol (glRep Aε) hp hA hpK I) ∈ isomGL β := by
  rw [mem_isomGL]
  intro x y
  rw [← glEquiv_apply, ← glEquiv_apply, glEquiv_involGL]
  exact invol_isometry (glRep Aε) hp hA hpK β (isIsomRep_glRep hAεβ) I x y

theorem involGL_apply_wtU (hA : ∀ a : ↥Aε, a ^ p = 1) (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (I : Finset (Hyperplane ↥Aε p)) :
    ∀ u ∈ wtU Aε I, glEquiv (glEquiv.symm (invol (glRep Aε) hp hA hpK I)) u = (1 : K) • u := by
  intro u hu
  rw [glEquiv_involGL, invol_apply, one_smul, show projI (glRep Aε) I u = 0 from hu, smul_zero,
    sub_zero]

theorem involGL_apply_wtW (hA : ∀ a : ↥Aε, a ^ p = 1) (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (I : Finset (Hyperplane ↥Aε p)) :
    ∀ w ∈ wtW Aε I,
      glEquiv (glEquiv.symm (invol (glRep Aε) hp hA hpK I)) w = (-(1 : K)) • w := by
  rintro _ ⟨v, rfl⟩
  rw [glEquiv_involGL, invol_apply, projI_projI (glRep Aε) hp hA hpK, neg_one_smul]
  module

theorem det_involGL (hA : ∀ a : ↥Aε, a ^ p = 1) (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (I : Finset (Hyperplane ↥Aε p)) :
    ((glEquiv.symm (invol (glRep Aε) hp hA hpK I) : GL ι K) : Matrix ι ι K).det =
      (-1) ^ ∑ H' ∈ I, Module.finrank K (weightSpace (glRep Aε) H'.1) := by
  rw [det_matrix_eq_det_glEquiv, glEquiv_involGL, LinearEquiv.coe_det,
    det_invol (glRep Aε) hp hA hpK I]

end Invol

theorem good_wtU_lu [Finite K] (hp : p.Prime) (hpK : (p : K) ≠ 0) (hβ : β = 0 ∨ β.SeparatingLeft)
    {Aε : Subgroup (GL ι K)} [IsMulCommutative Aε] (hA : ∀ a : ↥Aε, a ^ p = 1)
    (hAεβ : Aε ≤ isomGL β) {𝒮 : Set ((ι → K) →+ (ι → K))}
    (hmax : IsMaxElem β (glRep Aε) p 𝒮)
    (h𝒮 : ∀ s ∈ 𝒮, ∀ a v, s (glRep Aε a v) = glRep Aε a (s v))
    (h𝒮W : ∀ s ∈ 𝒮, ∀ i, ∀ v ∈ weightFamily (p := p) (glRep Aε) i,
      s v ∈ weightFamily (p := p) (glRep Aε) i)
    {Qbig QF : Prop}
    (hQscal : (∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧ Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β) →
      Qbig ∧ QF)
    (hQdim2 : ∀ (M N : Submodule K (ι → K)) (x : GL ι K), Module.finrank K M = 2 →
      (β = 0 ∨ ∀ m ∈ M, (∀ m' ∈ M, β m m' = 0) → m = 0) →
      x ∈ blkSub β M N → x ^ p = 1 → (∃ m ∈ M, glEquiv x m ≠ m) → Qbig ∧ QF)
    [DecidableEq (Hyperplane ↥Aε p)] (I : Finset (Hyperplane ↥Aε p)) {H₀ : Hyperplane ↥Aε p}
    (hH₀I : H₀ ∉ I) (hH₀ : weightSpace (glRep Aε) H₀.1 ≠ ⊥)
    (h2U : 2 ≤ Module.finrank K (wtU Aε I)) :
    (3 ≤ Module.finrank K (wtU Aε I) ∨ (Module.finrank K (wtU Aε I) = 2 ∧ Qbig)) ∧
      (3 ≤ Module.finrank K (wtU Aε I) ∨ (Module.finrank K (wtU Aε I) = 2 ∧ QF)) := by
  by_cases h3 : 3 ≤ Module.finrank K (wtU Aε I)
  · exact ⟨Or.inl h3, Or.inl h3⟩
  have h2' : Module.finrank K (wtU Aε I) = 2 := by omega
  suffices hQ : Qbig ∧ QF from ⟨Or.inr ⟨h2', hQ.1⟩, Or.inr ⟨h2', hQ.2⟩⟩
  by_cases hsc : ∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧ Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β
  · exact hQscal hsc
  have hd2 := two_le_finrank_weightSpace_of_not_scalar hp hβ hA hpK hAεβ hsc hH₀
  have hle' : Module.finrank K (weightSpace (glRep Aε) H₀.1) ≤ Module.finrank K (wtU Aε I) :=
    Submodule.finrank_mono (weightSpace_le_ker_projI hp hA hpK hH₀I)
  have hdH : Module.finrank K (weightSpace (glRep Aε) H₀.1) = 2 := by omega
  obtain ⟨x, hx, hx'⟩ := exists_supported_element β (glRep Aε) hp hA hpK (isIsomRep_glRep hAεβ)
    hmax h𝒮 h𝒮W {H₀} (fun H hH => by rw [Finset.mem_singleton.mp hH]; exact hH₀)
  refine hQdim2 (weightSpace (glRep Aε) H₀.1) (wtU Aε {H₀}) x hdH
    (hβ.imp id fun hsep m hm h => weightFamily_nondeg β (glRep Aε) (isIsomRep_glRep hAεβ) hp hA
      hpK hsep (some H₀) hm h)
    ⟨hAεβ x.2, fun v hv => ?_, fun w hw => ?_⟩ (congrArg Subtype.val (hA x)) ?_
  · rw [← glRep_apply_eq_glEquiv]
    exact apply_mem_weightSpace (glRep Aε) H₀.1 x hv
  · rw [← glRep_apply_eq_glEquiv]
    exact (apply_eq_self_iff_projI (glRep Aε) hp hA hpK hx hx' w).mpr hw
  · obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH₀
    refine ⟨m, hm, fun hfix => hm0 ?_⟩
    rw [← glRep_apply_eq_glEquiv] at hfix
    exact eq_zero_of_mem_weightSpace_of_fixed (glRep Aε) hp hA hpK
      (hx H₀ (Finset.mem_singleton_self _)) hm hfix

theorem layer_field_lu [Finite K] (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (hβ : β = 0 ∨ β.SeparatingLeft) (Dat : ClsInner p S B H β) {Aε : Subgroup (GL ι K)}
    [IsMulCommutative Aε] (hA : ∀ a : ↥Aε, a ^ p = 1) (hAεβ : Aε ≤ isomGL β)
    (hAε𝒮 : Aε ≤ centGL (fieldSet Dat)) (hmaxE : IsMaxElem β (glRep Aε) p (fieldSet Dat))
    {QbigF : (K ≃+* K) → Prop}
    (hF5a : ∀ U W : Submodule K (ι → K), IsCompl U W →
      (∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0) →
      (β = 0 ∨ ∀ u ∈ U, (∀ u' ∈ U, β u u' = 0) → u = 0) →
      ∀ (A : GL ι K) (σ : K ≃+* K), orderOf σ = p →
      (∀ u v, β (ModelGen.semiMap A σ u) (ModelGen.semiMap A σ v) = σ (β u v)) →
      (∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) → (∀ w ∈ W, ModelGen.semiMap A σ w ∈ W) →
      ∀ x ∈ blkSub β U W ⊓ centGL {(ModelGen.semiMap A σ).toAddMonoidHom}, orderOf x = p →
      (3 ≤ Module.finrank K U ∨ (Module.finrank K U = 2 ∧ QbigF σ)) →
      GLAPLayer p (blkI β U W ⊓ centGL {(ModelGen.semiMap A σ).toAddMonoidHom}) ≠ ⊥)
    (hF : FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ)
    (hform1 : ∀ u v, β (ModelGen.semiMap Dat.A Dat.σ u) (ModelGen.semiMap Dat.A Dat.σ v) =
      Dat.σ (β u v))
    [DecidableEq (Hyperplane ↥Aε p)] (H₁ : Hyperplane ↥Aε p) {H₀ : Hyperplane ↥Aε p}
    (hH₀ : weightSpace (glRep Aε) H₀.1 ≠ ⊥) (hne : H₀ ≠ H₁)
    (hgF : 3 ≤ Module.finrank K (wtU Aε {H₁}) ∨
      (Module.finrank K (wtU Aε {H₁}) = 2 ∧ QbigF Dat.σ)) :
    GLAPLayer p (blkI β (wtU Aε {H₁}) (wtW Aε {H₁}) ⊓
      centGL {(ModelGen.semiMap Dat.A Dat.σ).toAddMonoidHom}) ≠ ⊥ := by
  have hρ : IsIsomRep β (glRep Aε) := isIsomRep_glRep hAεβ
  have h𝒮 : ∀ s ∈ fieldSet Dat, ∀ a v, s (glRep Aε a v) = glRep Aε a (s v) := by
    intro s hs a v
    rw [glRep_apply_eq_glEquiv, glRep_apply_eq_glEquiv]
    exact ((mem_centGL.mp (hAε𝒮 a.2)) s hs v).symm
  have h𝒮W : ∀ s ∈ fieldSet Dat, ∀ i, ∀ v ∈ weightFamily (p := p) (glRep Aε) i,
      s v ∈ weightFamily (p := p) (glRep Aε) i := by
    rintro s ⟨hF', rfl⟩ i v hv
    exact preserves_weightFamily_of_semilinear (glRep Aε) (Dat.σ : K →+* K) _
      (fun c v => ModelGen.semiMap_smul Dat.A Dat.σ c v) (h𝒮 _ ⟨hF', rfl⟩) i hv
  obtain ⟨x, hx, hx'⟩ := exists_supported_element β (glRep Aε) hp hA hpK hρ hmaxE h𝒮 h𝒮W {H₀}
    (fun H hH => by rw [Finset.mem_singleton.mp hH]; exact hH₀)
  have hH₀I : H₀ ∉ ({H₁} : Finset (Hyperplane ↥Aε p)) := fun h => hne (Finset.mem_singleton.mp h)
  obtain ⟨hxB, hxp⟩ := supported_mem_blkSub hp hA hpK hAεβ {H₁} hH₀I hx hx'
  have hxC : (x : GL ι K) ∈ centGL {(ModelGen.semiMap Dat.A Dat.σ).toAddMonoidHom} := by
    rw [mem_centGL]
    rintro s hs v
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact (mem_centGL.mp (hAε𝒮 x.2)) _ ⟨hF, rfl⟩ v
  obtain ⟨hU, hW⟩ := preserves_wtU_wtW hp hA hpK {H₁} _ (h𝒮W _ ⟨hF, rfl⟩)
  exact hF5a _ _ (isCompl_ker_range_projI (glRep Aε) hp hA hpK _)
    (orth_ker_range_projI β (glRep Aε) hρ _)
    (hβ.imp id fun hsep => nondeg_ker_projI β (glRep Aε) hρ hp hA hpK hsep _) Dat.A Dat.σ
    hF.2.2.2.2.1.1 hform1 (fun u hu => hU u hu) (fun w hw => hW w hw) _ ⟨hxB, hxC⟩ hxp hgF

theorem concA_of_I_lu [Finite K] (hp : p.Prime) [hSn : S.Normal] (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (h2 : (2 : K) ≠ 0) (hpK : (p : K) ≠ 0) (Dat : ClsInner p S B H β) (hHβ : H ≤ isomGL β)
    (hβ : β = 0 ∨ β.SeparatingLeft) {Aε : Subgroup (GL ι K)} [IsMulCommutative Aε]
    (hA : ∀ a : ↥Aε, a ^ p = 1) (hle : liftGroup Dat ≤ Aε) (hAεβ : Aε ≤ isomGL β)
    (hAε𝒮 : Aε ≤ centGL (fieldSet Dat)) (hmaxE : IsMaxElem β (glRep Aε) p (fieldSet Dat))
    (hscalMax : ∀ c : Kˣ, c ^ p = 1 → Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β →
      Matrix.GeneralLinearGroup.scalar ι c ∈ Aε)
    (hdec : ∀ g ∈ Aε, ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ Aε ∧
      Matrix.GeneralLinearGroup.scalar ι c * g ∈ liftGroup Dat)
    {Qbig : Prop}
    (hblk : ∀ U W : Submodule K (ι → K), IsCompl U W →
      (∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0) →
      (β = 0 ∨ ∀ u ∈ U, (∀ u' ∈ U, β u u' = 0) → u = 0) →
      (3 ≤ Module.finrank K U ∨ (Module.finrank K U = 2 ∧ Qbig)) →
      blkI β U W ≤ H ∧ CFSG.Open.IsQuasisimple ↥(blkI β U W) ∧
      (∀ x ∈ blkSub β U W, orderOf x = p → p ∣ Nat.card ↥(blkI β U W)) ∧
      (∀ y : GL ι K, (∀ u ∈ U, glEquiv y u ∈ U) → (∀ j ∈ blkI β U W, y * j = j * y) →
        ∃ c : K, ∀ u ∈ U, glEquiv y u = c • u) ∧
      (∀ (A : GL ι K) (σ : K ≃+* K), orderOf σ = p → (∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) →
        ∀ y : GL ι K, (∀ u ∈ U, glEquiv y u ∈ U) → ∀ k : ℕ, 0 < k → k < p →
          ¬ ∀ j ∈ blkI β U W, y * (ModelGen.semiConj A σ ^ k) j * y⁻¹ = j))
    [DecidableEq (Hyperplane ↥Aε p)] (I : Finset (Hyperplane ↥Aε p))
    (hI : ∀ H' ∈ I, weightSpace (glRep Aε) H'.1 ≠ ⊥) (hI1 : 1 ≤ I.card)
    {H₀ : Hyperplane ↥Aε p} (hH₀ : H₀ ∉ I) (hW₀ : weightSpace (glRep Aε) H₀.1 ≠ ⊥)
    (hrank : p ^ (3 + I.card) ≤ Nat.card B)
    {z : GL ι K} (hzH : z ∈ H) {s : K} (hs : s * s = 1)
    (hzU : ∀ u ∈ wtU Aε I, glEquiv z u = s • u) (hzW : ∀ w ∈ wtW Aε I, glEquiv z w = (-s) • w)
    (hgood : 3 ≤ Module.finrank K (wtU Aε I) ∨ (Module.finrank K (wtU Aε I) = 2 ∧ Qbig))
    (hE : I.card = 1 →
      (∃ a ∈ Aε, (¬ ∃ c : K, ∀ u ∈ wtU Aε I, glEquiv a u = c • u) ∧
        GLAPLayer p (blkI β (wtU Aε I) (wtW Aε I) ⊓ Subgroup.centralizer {a}) ≠ ⊥) ∨
      (FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ ∧
        GLAPLayer p (blkI β (wtU Aε I) (wtW Aε I) ⊓
          centGL {(ModelGen.semiMap Dat.A Dat.σ).toAddMonoidHom}) ≠ ⊥)) :
    S267ConcA p S B := by
  classical
  have hρ : IsIsomRep β (glRep Aε) := isIsomRep_glRep hAεβ
  have hUW := isCompl_ker_range_projI (glRep Aε) hp hA hpK I
  have horth := orth_ker_range_projI β (glRep Aε) hρ I
  have hnd : β = 0 ∨ ∀ u ∈ wtU Aε I, (∀ u' ∈ wtU Aε I, β u u' = 0) → u = 0 :=
    hβ.imp id fun hsep => nondeg_ker_projI β (glRep Aε) hρ hp hA hpK hsep I
  obtain ⟨hIH, hIq, hdvd, hSchur, hF5b⟩ := hblk _ _ hUW horth hnd hgood
  have h𝒮 : ∀ s ∈ fieldSet Dat, ∀ a v, s (glRep Aε a v) = glRep Aε a (s v) := by
    intro s hs a v
    rw [glRep_apply_eq_glEquiv, glRep_apply_eq_glEquiv]
    exact ((mem_centGL.mp (hAε𝒮 a.2)) s hs v).symm
  have h𝒮W : ∀ s ∈ fieldSet Dat, ∀ i, ∀ v ∈ weightFamily (p := p) (glRep Aε) i,
      s v ∈ weightFamily (p := p) (glRep Aε) i := by
    rintro s ⟨hF, rfl⟩ i v hv
    exact preserves_weightFamily_of_semilinear (glRep Aε) (Dat.σ : K →+* K) _
      (fun c v => ModelGen.semiMap_smul Dat.A Dat.σ c v) (h𝒮 _ ⟨hF, rfl⟩) i hv
  obtain ⟨x₀, hx₀, hx₀'⟩ := exists_supported_element β (glRep Aε) hp hA hpK hρ hmaxE h𝒮 h𝒮W
    {H₀} (fun H hH => by rw [Finset.mem_singleton.mp hH]; exact hW₀)
  obtain ⟨hx₀B, hx₀p⟩ := supported_mem_blkSub hp hA hpK hAεβ I hH₀ hx₀ hx₀'
  have hpI := hdvd _ hx₀B hx₀p
  have hU0 : wtU Aε I ≠ ⊥ := fun h =>
    hW₀ (le_bot_iff.mp (h ▸ weightSpace_le_ker_projI hp hA hpK hH₀))
  have hscal := exists_scalar_of_smul_on hp hβ hA hpK hAεβ hscalMax I hU0
  have hfield : FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ →
      ∀ y : GL ι K, (∀ u ∈ wtU Aε I, glEquiv y u ∈ wtU Aε I) →
        (∀ w ∈ wtW Aε I, glEquiv y w ∈ wtW Aε I) → ∀ k : ℕ, 0 < k → k < p →
          ¬ ∀ j ∈ blkI β (wtU Aε I) (wtW Aε I),
            y * (ModelGen.semiConj Dat.A Dat.σ ^ k) j * y⁻¹ = j := by
    intro hF y hyU _ k hk0 hkp
    have hU := (preserves_wtU_wtW hp hA hpK I _ (h𝒮W _ ⟨hF, rfl⟩)).1
    exact hF5b Dat.A Dat.σ hF.2.2.2.2.1.1 (fun u hu => hU u hu) y hyU k hk0 hkp
  exact concA_of_weights_scal hp hB hBC hcore h2 hpK Dat hHβ hA hle hdec hAεβ hAε𝒮 hmaxE I hI
    hI1 hH₀ hW₀ hrank hzH hs hzU hzW hIH hIq hpI hSchur hfield hscal hE

theorem concA_of_pair_lu [Finite K] (hp : p.Prime) [hSn : S.Normal] (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (h2 : (2 : K) ≠ 0) (hpK : (p : K) ≠ 0) (Dat : ClsInner p S B H β) (hHβ : H ≤ isomGL β)
    (hβ : β = 0 ∨ β.SeparatingLeft)
    (hdetH : ∀ g ∈ isomGL β, (g : Matrix ι ι K).det = 1 → g ∈ H)
    {Aε : Subgroup (GL ι K)} [IsMulCommutative Aε]
    (hA : ∀ a : ↥Aε, a ^ p = 1) (hle : liftGroup Dat ≤ Aε) (hAεβ : Aε ≤ isomGL β)
    (hAε𝒮 : Aε ≤ centGL (fieldSet Dat)) (hmaxE : IsMaxElem β (glRep Aε) p (fieldSet Dat))
    (hscalMax : ∀ c : Kˣ, c ^ p = 1 → Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β →
      Matrix.GeneralLinearGroup.scalar ι c ∈ Aε)
    (hdec : ∀ g ∈ Aε, ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ Aε ∧
      Matrix.GeneralLinearGroup.scalar ι c * g ∈ liftGroup Dat)
    {Qbig : Prop}
    (hblk : ∀ U W : Submodule K (ι → K), IsCompl U W →
      (∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0) →
      (β = 0 ∨ ∀ u ∈ U, (∀ u' ∈ U, β u u' = 0) → u = 0) →
      (3 ≤ Module.finrank K U ∨ (Module.finrank K U = 2 ∧ Qbig)) →
      blkI β U W ≤ H ∧ CFSG.Open.IsQuasisimple ↥(blkI β U W) ∧
      (∀ x ∈ blkSub β U W, orderOf x = p → p ∣ Nat.card ↥(blkI β U W)) ∧
      (∀ y : GL ι K, (∀ u ∈ U, glEquiv y u ∈ U) → (∀ j ∈ blkI β U W, y * j = j * y) →
        ∃ c : K, ∀ u ∈ U, glEquiv y u = c • u) ∧
      (∀ (A : GL ι K) (σ : K ≃+* K), orderOf σ = p → (∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) →
        ∀ y : GL ι K, (∀ u ∈ U, glEquiv y u ∈ U) → ∀ k : ℕ, 0 < k → k < p →
          ¬ ∀ j ∈ blkI β U W, y * (ModelGen.semiConj A σ ^ k) j * y⁻¹ = j))
    [DecidableEq (Hyperplane ↥Aε p)] (T : Finset (Hyperplane ↥Aε p))
    (hT : ∀ H' : Hyperplane ↥Aε p, H' ∈ T ↔ weightSpace (glRep Aε) H'.1 ≠ ⊥) (h3 : 3 ≤ T.card)
    (h5 : p ^ 5 ≤ Nat.card B)
    (hgoodI : ∀ I ⊆ T, ∀ H₀ ∈ T, H₀ ∉ I → I.card = 2 →
      3 ≤ Module.finrank K (wtU Aε I) ∨ (Module.finrank K (wtU Aε I) = 2 ∧ Qbig)) :
    S267ConcA p S B := by
  obtain ⟨Ha, hHa, Hb, hHb, hab, he⟩ := exists_pair_even_finrank (glRep Aε) T h3
  obtain ⟨Hc, hHcT, hHcI⟩ : ∃ Hc ∈ T, Hc ∉ ({Ha, Hb} : Finset (Hyperplane ↥Aε p)) := by
    by_contra hcon
    push Not at hcon
    have h1 := Finset.card_le_card (show T ⊆ {Ha, Hb} from fun H hH => hcon H hH)
    rw [Finset.card_pair hab] at h1
    omega
  have hIT : ({Ha, Hb} : Finset (Hyperplane ↥Aε p)) ⊆ T := by
    intro H hH
    rcases Finset.mem_insert.mp hH with rfl | hH
    · exact hHa
    · rw [Finset.mem_singleton.mp hH]
      exact hHb
  have hIc : ({Ha, Hb} : Finset (Hyperplane ↥Aε p)).card = 2 := Finset.card_pair hab
  have hzH : glEquiv.symm (invol (glRep Aε) hp hA hpK {Ha, Hb}) ∈ H := by
    refine hdetH _ (involGL_mem_isomGL hA hp hpK hAεβ _) ?_
    rw [det_involGL hA hp hpK, Finset.sum_pair hab, he.neg_one_pow]
  exact concA_of_I_lu hp hB hBC hcore h2 hpK Dat hHβ hβ hA hle hAεβ hAε𝒮 hmaxE hscalMax hdec
    hblk {Ha, Hb} (fun H' hH' => (hT H').mp (hIT hH')) (by rw [hIc]; norm_num) hHcI
    ((hT Hc).mp hHcT) (by rw [hIc]; exact h5) hzH (s := 1) (by norm_num)
    (involGL_apply_wtU hA hp hpK _) (involGL_apply_wtW hA hp hpK _)
    (hgoodI _ hIT Hc hHcT hHcI hIc) (fun h => absurd h (by rw [hIc]; norm_num))


theorem concl_lu [Nonempty ι] [Finite K] (hp : p.Prime) [hSn : S.Normal]
    (hB : IsElemAbelian p B) (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) (h4 : p ^ 4 ≤ Nat.card B) (h2 : (2 : K) ≠ 0)
    (hpK : (p : K) ≠ 0) (Dat : ClsInner p S B H β) (hHβ : H ≤ isomGL β)
    (hβ : β = 0 ∨ β.SeparatingLeft)
    (hdetH : ∀ g ∈ isomGL β, (g : Matrix ι ι K).det = 1 → g ∈ H)
    (hG6 : ∀ g ∈ isomGL β, g ^ p = 1 → ∃ c : Kˣ, c ^ p = 1 ∧
      Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β ∧
      Matrix.GeneralLinearGroup.scalar ι c * g ∈ H)
    {Qbig : Prop} {QbigF : (K ≃+* K) → Prop}
    (hblk : ∀ U W : Submodule K (ι → K), IsCompl U W →
      (∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0) →
      (β = 0 ∨ ∀ u ∈ U, (∀ u' ∈ U, β u u' = 0) → u = 0) →
      (3 ≤ Module.finrank K U ∨ (Module.finrank K U = 2 ∧ Qbig)) →
      blkI β U W ≤ H ∧ CFSG.Open.IsQuasisimple ↥(blkI β U W) ∧
      (∀ x ∈ blkSub β U W, orderOf x = p → p ∣ Nat.card ↥(blkI β U W)) ∧
      (∀ y : GL ι K, (∀ u ∈ U, glEquiv y u ∈ U) → (∀ j ∈ blkI β U W, y * j = j * y) →
        ∃ c : K, ∀ u ∈ U, glEquiv y u = c • u) ∧
      (∀ (A : GL ι K) (σ : K ≃+* K), orderOf σ = p → (∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) →
        ∀ y : GL ι K, (∀ u ∈ U, glEquiv y u ∈ U) → ∀ k : ℕ, 0 < k → k < p →
          ¬ ∀ j ∈ blkI β U W, y * (ModelGen.semiConj A σ ^ k) j * y⁻¹ = j))
    (hF5a : ∀ U W : Submodule K (ι → K), IsCompl U W →
      (∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0) →
      (β = 0 ∨ ∀ u ∈ U, (∀ u' ∈ U, β u u' = 0) → u = 0) →
      ∀ (A : GL ι K) (σ : K ≃+* K), orderOf σ = p →
      (∀ u v, β (ModelGen.semiMap A σ u) (ModelGen.semiMap A σ v) = σ (β u v)) →
      (∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) → (∀ w ∈ W, ModelGen.semiMap A σ w ∈ W) →
      ∀ x ∈ blkSub β U W ⊓ centGL {(ModelGen.semiMap A σ).toAddMonoidHom}, orderOf x = p →
      (3 ≤ Module.finrank K U ∨ (Module.finrank K U = 2 ∧ QbigF σ)) →
      GLAPLayer p (blkI β U W ⊓ centGL {(ModelGen.semiMap A σ).toAddMonoidHom}) ≠ ⊥)
    (hform1 : FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ →
      ∀ u v, β (ModelGen.semiMap Dat.A Dat.σ u) (ModelGen.semiMap Dat.A Dat.σ v) =
        Dat.σ (β u v))
    (hQscal : (∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧ Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β) →
      Qbig ∧ (FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ → QbigF Dat.σ))
    (hQdim2 : ∀ (M N : Submodule K (ι → K)) (x : GL ι K), Module.finrank K M = 2 →
      (β = 0 ∨ ∀ m ∈ M, (∀ m' ∈ M, β m m' = 0) → m = 0) →
      x ∈ blkSub β M N → x ^ p = 1 → (∃ m ∈ M, glEquiv x m ≠ m) →
      Qbig ∧ (FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ → QbigF Dat.σ))
    (hD1 : ∀ (Aε : Subgroup (GL ι K)) [IsMulCommutative Aε], (∀ a : ↥Aε, a ^ p = 1) →
      Aε ≤ isomGL β → IsMaxElem β (glRep Aε) p ∅ →
      (∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧ Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β) →
      ∀ H' : Hyperplane ↥Aε p, weightSpace (glRep Aε) H'.1 ≠ ⊥ →
        Module.finrank K (weightSpace (glRep Aε) H'.1) = 1) :
    S267ConcA p S B ∨
      (Nat.card B = p ^ 4 ∧ (9 ≤ Fintype.card ι ∨
        (6 ≤ Fintype.card ι ∧ FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ))) ∨
      (Nat.card B = p ^ 4 ∧ Fintype.card ι = 4 ∧
        (∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧ Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β) ∧
        B = (B ⊓ centModSubgroup p S) ⊔ (B ⊓ S) ∧
        (B ⊓ centModSubgroup p S) ⊓ (B ⊓ S) = ⊥) := by
  classical
  obtain ⟨Aε, hAε, hle, hAεβ, hAε𝒮, hmax, hcap, hscalMax, hdec⟩ :=
    exists_engine_lu hp hB hrank hBC hcore hZ h4 h2 hpK Dat hHβ hdetH hG6
  haveI : IsMulCommutative ↥Aε := hAε.1
  have hA : ∀ a : ↥Aε, a ^ p = 1 := fun a => Subtype.ext (by simpa using hAε.2 a a.2)
  have hmaxE : IsMaxElem β (glRep Aε) p (fieldSet Dat) :=
    isMaxElem_of_maximal β (fieldSet Dat) Aε hAε hAεβ hAε𝒮 hmax
  haveI : Fintype (Hyperplane ↥Aε p) := Fintype.ofFinite _
  have hρ : IsIsomRep β (glRep Aε) := isIsomRep_glRep hAεβ
  have h𝒮 : ∀ s ∈ fieldSet Dat, ∀ a v, s (glRep Aε a v) = glRep Aε a (s v) := by
    intro s hs a v
    rw [glRep_apply_eq_glEquiv, glRep_apply_eq_glEquiv]
    exact ((mem_centGL.mp (hAε𝒮 a.2)) s hs v).symm
  have h𝒮W : ∀ s ∈ fieldSet Dat, ∀ i, ∀ v ∈ weightFamily (p := p) (glRep Aε) i,
      s v ∈ weightFamily (p := p) (glRep Aε) i := by
    rintro s ⟨hF, rfl⟩ i v hv
    exact preserves_weightFamily_of_semilinear (glRep Aε) (Dat.σ : K →+* K) _
      (fun c v => ModelGen.semiMap_smul Dat.A Dat.σ c v) (h𝒮 _ ⟨hF, rfl⟩) i hv
  set T : Finset (Hyperplane ↥Aε p) :=
    Finset.univ.filter fun H' => weightSpace (glRep Aε) H'.1 ≠ ⊥ with hTdef
  have hT : ∀ H' : Hyperplane ↥Aε p, H' ∈ T ↔ weightSpace (glRep Aε) H'.1 ≠ ⊥ := fun H' => by
    simp [hTdef]
  have hcardA : Nat.card ↥Aε = p ^ T.card :=
    card_eq_pow_support β (glRep Aε) hp hA hpK hρ hmaxE h𝒮 h𝒮W (glRep_injective Aε) T hT
  have hLscal : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ liftGroup Dat → c = 1 := by
    rintro c ⟨y, ⟨x, rfl⟩, hy⟩
    have hk : Dat.θ x ∈ Dat.φ.ker := by
      rw [Dat.ker_eq, Subgroup.mem_subgroupOf]
      exact ⟨c, hy.symm⟩
    have hθ1 : Dat.θ x = 1 := by
      have hmem : Dat.θ x ∈ Dat.θ.range ⊓ Dat.φ.ker := ⟨⟨x, rfl⟩, hk⟩
      rw [Dat.range_inf_ker, Subgroup.mem_bot] at hmem
      exact hmem
    apply scalarGL_injective (ι := ι)
    rw [← hy, map_one]
    show ((Dat.θ x : ↥H) : GL ι K) = 1
    rw [hθ1]
    rfl
  obtain ⟨hns_eq, hsc_card⟩ := card_engine_eq hp hAε hle hAεβ hLscal hscalMax hdec
  have hBcard := card_eq_lu hp hB hBC hcore Dat
  have hN : Module.finrank K (ι → K) = Fintype.card ι := Module.finrank_fintype_fun_eq_card K
  have hpos : ∀ H' ∈ T, 1 ≤ Module.finrank K (weightSpace (glRep Aε) H'.1) := fun H' hH' =>
    Nat.one_le_iff_ne_zero.mpr fun h => (hT H').mp hH' (Submodule.finrank_eq_zero.mp h)
  have hUW : ∀ I : Finset (Hyperplane ↥Aε p), IsCompl (wtU Aε I) (wtW Aε I) := fun I =>
    isCompl_ker_range_projI (glRep Aε) hp hA hpK I
  have horth : ∀ I : Finset (Hyperplane ↥Aε p), ∀ u ∈ wtU Aε I, ∀ w ∈ wtW Aε I,
      β u w = 0 ∧ β w u = 0 := fun I =>
    orth_ker_range_projI β (glRep Aε) hρ I
  have hnd : ∀ I : Finset (Hyperplane ↥Aε p),
      β = 0 ∨ ∀ u ∈ wtU Aε I, (∀ u' ∈ wtU Aε I, β u u' = 0) → u = 0 := fun I =>
    hβ.imp id fun hsep => nondeg_ker_projI β (glRep Aε) hρ hp hA hpK hsep I
  have hsupp : ∀ H' ∈ T, ∃ x : ↥Aε, (∀ H ∈ ({H'} : Finset _), x ∉ H.1) ∧
      ∀ H'' : Hyperplane ↥Aε p, H'' ∉ ({H'} : Finset _) →
        weightSpace (glRep Aε) H''.1 ≠ ⊥ → x ∈ H''.1 := fun H' hH' =>
    exists_supported_element β (glRep Aε) hp hA hpK hρ hmaxE h𝒮 h𝒮W {H'}
      (fun H hH => by rw [Finset.mem_singleton.mp hH]; exact (hT H').mp hH')
  have hgood : ∀ (I : Finset (Hyperplane ↥Aε p)) (H₀ : Hyperplane ↥Aε p), H₀ ∉ I → H₀ ∈ T →
      2 ≤ Module.finrank K (wtU Aε I) →
      (3 ≤ Module.finrank K (wtU Aε I) ∨ (Module.finrank K (wtU Aε I) = 2 ∧ Qbig)) ∧
      (3 ≤ Module.finrank K (wtU Aε I) ∨ (Module.finrank K (wtU Aε I) = 2 ∧
        (FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ → QbigF Dat.σ))) :=
    fun I H₀ hH₀I hH₀T h2U =>
      good_wtU_lu hp hpK hβ hA hAεβ hmaxE h𝒮 h𝒮W hQscal hQdim2 I hH₀I ((hT H₀).mp hH₀T) h2U
  have caseI : 3 ≤ T.card → p ^ 5 ≤ Nat.card B →
      (∀ I ⊆ T, ∀ H₀ ∈ T, H₀ ∉ I → I.card = 2 → 2 ≤ Module.finrank K (wtU Aε I)) →
      S267ConcA p S B := fun h3 h5 hU2 =>
    concA_of_pair_lu hp hB hBC hcore h2 hpK Dat hHβ hβ hdetH hA hle hAεβ hAε𝒮 hmaxE hscalMax
      hdec hblk T hT h3 h5 fun I hIT H₀ hH₀T hH₀I hIc =>
        (hgood I H₀ hH₀I hH₀T (hU2 I hIT H₀ hH₀T hH₀I hIc)).1
  have hEfield : ∀ H₁ H₀ : Hyperplane ↥Aε p, H₀ ∈ T → H₀ ≠ H₁ →
      FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ →
      (3 ≤ Module.finrank K (wtU Aε {H₁}) ∨
        (Module.finrank K (wtU Aε {H₁}) = 2 ∧
          (FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ → QbigF Dat.σ))) →
      GLAPLayer p (blkI β (wtU Aε {H₁}) (wtW Aε {H₁}) ⊓
        centGL {(ModelGen.semiMap Dat.A Dat.σ).toAddMonoidHom}) ≠ ⊥ :=
    fun H₁ H₀ hH₀T hne hF hgF =>
      layer_field_lu hp hpK hβ Dat hA hAεβ hAε𝒮 hmaxE hF5a hF (hform1 hF) H₁ ((hT H₀).mp hH₀T)
        hne (hgF.imp id fun h => ⟨h.1, h.2 hF⟩)
  have caseSingle : ∀ H₁ H₀ : Hyperplane ↥Aε p, H₁ ∈ T → H₀ ∈ T → H₀ ≠ H₁ →
      ∀ {z : GL ι K} {s : K}, z ∈ H → s * s = 1 →
      (∀ u ∈ wtU Aε {H₁}, glEquiv z u = s • u) → (∀ w ∈ wtW Aε {H₁}, glEquiv z w = (-s) • w) →
      2 ≤ Module.finrank K (wtU Aε {H₁}) →
      ((∃ a ∈ Aε, (¬ ∃ c : K, ∀ u ∈ wtU Aε {H₁}, glEquiv a u = c • u) ∧
        GLAPLayer p (blkI β (wtU Aε {H₁}) (wtW Aε {H₁}) ⊓ Subgroup.centralizer {a}) ≠ ⊥) ∨
        (FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ ∧
          GLAPLayer p (blkI β (wtU Aε {H₁}) (wtW Aε {H₁}) ⊓
            centGL {(ModelGen.semiMap Dat.A Dat.σ).toAddMonoidHom}) ≠ ⊥)) →
      S267ConcA p S B := by
    intro H₁ H₀ hH₁T hH₀T hne z s hzH hs hzU hzW h2U hE
    have hH₀I : H₀ ∉ ({H₁} : Finset (Hyperplane ↥Aε p)) := fun h => hne (Finset.mem_singleton.mp h)
    obtain ⟨hgoodU, -⟩ := hgood _ H₀ hH₀I hH₀T h2U
    exact concA_of_I_lu hp hB hBC hcore h2 hpK Dat hHβ hβ hA hle hAεβ hAε𝒮 hmaxE hscalMax hdec
      hblk {H₁} (fun H' hH' => by rw [Finset.mem_singleton.mp hH']; exact (hT H₁).mp hH₁T)
      (by rw [Finset.card_singleton]) hH₀I ((hT H₀).mp hH₀T)
      (by rw [Finset.card_singleton]; exact h4)
      hzH hs hzU hzW hgoodU fun _ => hE
  have hU2sum : ∀ (I J : Finset (Hyperplane ↥Aε p)), Disjoint I J → J ⊆ T → 2 ≤ J.card →
      2 ≤ Module.finrank K (wtU Aε I) := by
    intro I J hIJ hJT hJ2
    have h1 := sum_finrank_le_finrank_ker_projI (glRep Aε) hp hA hpK hIJ
    have h2' : J.card ≤ ∑ H' ∈ J, Module.finrank K (weightSpace (glRep Aε) H'.1) := by
      calc J.card = ∑ _H' ∈ J, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ _ := Finset.sum_le_sum fun H' hH' => hpos H' (hJT hH')
    exact hJ2.trans (h2'.trans h1)
  have hU2one : ∀ (I : Finset (Hyperplane ↥Aε p)) (H₀ : Hyperplane ↥Aε p), H₀ ∉ I →
      2 ≤ Module.finrank K (weightSpace (glRep Aε) H₀.1) → 2 ≤ Module.finrank K (wtU Aε I) :=
    fun I H₀ hH₀I hd => hd.trans (Submodule.finrank_mono (weightSpace_le_ker_projI hp hA hpK hH₀I))
  have hthree : ∀ (Ha : Hyperplane ↥Aε p), Ha ∈ T → T.card = 3 →
      ∃ Hb ∈ T, ∃ Hc ∈ T, Hb ≠ Ha ∧ Hc ≠ Ha ∧ Hb ≠ Hc := by
    intro Ha hHa ht
    have h2 : (T.erase Ha).card = 2 := by rw [Finset.card_erase_of_mem hHa, ht]
    obtain ⟨Hb, Hc, hbc, he⟩ := Finset.card_eq_two.mp h2
    have hb : Hb ∈ T.erase Ha := by rw [he]; exact Finset.mem_insert_self _ _
    have hc : Hc ∈ T.erase Ha := by
      rw [he]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact ⟨Hb, Finset.mem_of_mem_erase hb, Hc, Finset.mem_of_mem_erase hc,
      Finset.ne_of_mem_erase hb, Finset.ne_of_mem_erase hc, hbc⟩
  have hzeven : ∀ Ha : Hyperplane ↥Aε p,
      Even (Module.finrank K (weightSpace (glRep Aε) Ha.1)) →
      glEquiv.symm (invol (glRep Aε) hp hA hpK {Ha}) ∈ H := fun Ha hev =>
    hdetH _ (involGL_mem_isomGL hA hp hpK hAεβ _)
      (by rw [det_involGL hA hp hpK, Finset.sum_singleton, hev.neg_one_pow])
  have hsum3 : ∀ (Ha Hb Hc : Hyperplane ↥Aε p), Ha ∈ T → Hb ∈ T → Hc ∈ T → Ha ≠ Hb → Ha ≠ Hc →
      Hb ≠ Hc → T.card = 3 → ∀ f : Hyperplane ↥Aε p → ℕ, ∑ H' ∈ T, f H' = f Ha + f Hb + f Hc := by
    intro Ha Hb Hc hHa hHb hHc hab hac hbc ht f
    have hsub : ({Ha, Hb, Hc} : Finset (Hyperplane ↥Aε p)) ⊆ T := by
      intro H hH
      simp only [Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with rfl | rfl | rfl <;> assumption
    have hcard : ({Ha, Hb, Hc} : Finset (Hyperplane ↥Aε p)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [ht, hcard])
    rw [← heq, Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc, add_assoc]
  have hsum2 : ∀ (Ha Hb : Hyperplane ↥Aε p), Ha ∈ T → Hb ∈ T → Ha ≠ Hb → T.card = 2 →
      ∀ f : Hyperplane ↥Aε p → ℕ, ∑ H' ∈ T, f H' = f Ha + f Hb := by
    intro Ha Hb hHa hHb hab ht f
    have hsub : ({Ha, Hb} : Finset (Hyperplane ↥Aε p)) ⊆ T := by
      intro H hH
      rcases Finset.mem_insert.mp hH with rfl | hH
      · exact hHa
      · rw [Finset.mem_singleton.mp hH]
        exact hHb
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [ht, Finset.card_pair hab])
    rw [← heq, Finset.sum_pair hab]
  have hNle := sum_finrank_le_finrank (glRep Aε) hp hA hpK T
  rw [hN] at hNle
  by_cases hsc : ∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧ Matrix.GeneralLinearGroup.scalar ι c ∈ isomGL β
  ·
    have hcL := hsc_card hsc
    obtain ⟨c₀, hc₀1, hc₀p, hc₀β⟩ := hsc
    have hc₀A := hscalMax c₀ hc₀p hc₀β
    have hfix0 : fixedSpace (glRep Aε) ⊤ = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      have h1 : glRep Aε ⟨_, hc₀A⟩ v = v := hv _ (Subgroup.mem_top _)
      rw [glRep_apply_eq_glEquiv, glEquiv_scalar_apply] at h1
      rw [Submodule.mem_bot]
      have h1' : ((c₀ : K) - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      exact (smul_eq_zero.mp h1').resolve_left (sub_ne_zero.mpr fun h => hc₀1 (Units.ext h))
    have hNsum : Fintype.card ι = ∑ H' ∈ T, Module.finrank K (weightSpace (glRep Aε) H'.1) := by
      rw [← hN, finrank_eq_fixedSpace_add_sum_support (glRep Aε) hp hA hpK T hT, hfix0,
        finrank_bot, zero_add]
    have hU2s : ∀ I ⊆ T, ∀ H₀ ∈ T, H₀ ∉ I → I.card = 2 → 4 ≤ T.card →
        2 ≤ Module.finrank K (wtU Aε I) := fun I hIT _ _ _ hIc h4T =>
      hU2sum I (T \ I) Finset.disjoint_sdiff Finset.sdiff_subset
        (by rw [Finset.card_sdiff_of_subset hIT]; omega)
    rcases hBcard with ⟨hBB, hBc⟩ | ⟨hF, hBc⟩
    ·
      have hBt : Nat.card B = p ^ T.card := by rw [hBc, ← hcL, hcardA]
      by_cases h5 : 5 ≤ T.card
      · left
        exact caseI (by omega) (by rw [hBt]; exact Nat.pow_le_pow_right hp.pos h5)
          fun I hIT H₀ hH₀T hH₀I hIc => hU2s I hIT H₀ hH₀T hH₀I hIc (by omega)
      ·
        have ht : T.card = 4 := by
          have : 4 ≤ T.card := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hBt ▸ h4)
          omega
        right
        right
        have hnF : ¬ FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ := fun hF =>
          hF.2.1 (show Dat.b ∈ innerPart S B from hBB.symm ▸ hF.1).2
        have h𝒮0 : fieldSet Dat = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun s hs => hnF hs.1
        have hmax0 : IsMaxElem β (glRep Aε) p ∅ := h𝒮0 ▸ hmaxE
        have hd1 := hD1 Aε hA hAεβ hmax0 ⟨c₀, hc₀1, hc₀p, hc₀β⟩
        refine ⟨by rw [hBt, ht], ?_, ⟨c₀, hc₀1, hc₀p, hc₀β⟩, ?_⟩
        · rw [hNsum, Finset.sum_congr rfl fun H' hH' => hd1 H' ((hT H').mp hH'), Finset.sum_const,
            smul_eq_mul, mul_one, ht]
        ·
          obtain ⟨Ha, hHa⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
          have h3e : (T.erase Ha).card = 3 := by rw [Finset.card_erase_of_mem hHa, ht]
          obtain ⟨Hb, hHb', Hc, hHc', hbc⟩ : ∃ Hb ∈ T.erase Ha, ∃ Hc ∈ T.erase Ha, Hb ≠ Hc := by
            obtain ⟨Hb, hHb⟩ := Finset.card_pos.mp (by omega : 0 < (T.erase Ha).card)
            have h2e : ((T.erase Ha).erase Hb).card = 2 := by
              rw [Finset.card_erase_of_mem hHb, h3e]
            obtain ⟨Hc, hHc⟩ := Finset.card_pos.mp (by omega : 0 < ((T.erase Ha).erase Hb).card)
            exact ⟨Hb, hHb, Hc, Finset.mem_of_mem_erase hHc, (Finset.ne_of_mem_erase hHc).symm⟩
          have hba := Finset.ne_of_mem_erase hHb'
          have hca := Finset.ne_of_mem_erase hHc'
          have hHb := Finset.mem_of_mem_erase hHb'
          have hHc := Finset.mem_of_mem_erase hHc'
          set z := glEquiv.symm (invol (glRep Aε) hp hA hpK {Ha, Hb}) with hzdef
          have hzH : z ∈ H := by
            refine hdetH _ (involGL_mem_isomGL hA hp hpK hAεβ _) ?_
            rw [det_involGL hA hp hpK, Finset.sum_pair hba.symm, hd1 Ha ((hT Ha).mp hHa),
              hd1 Hb ((hT Hb).mp hHb)]
            norm_num
          have hz2 : z ^ 2 = 1 := by
            apply glEquiv.injective
            rw [map_pow, glEquiv_involGL hA hp hpK, map_one, pow_two]
            exact LinearEquiv.ext fun v => invol_invol (glRep Aε) hp hA hpK _ v
          have hz1 : Dat.φ ⟨z, hzH⟩ ≠ 1 := by
            intro h
            have hk : (⟨z, hzH⟩ : ↥H) ∈ Dat.φ.ker := h
            rw [Dat.ker_eq, Subgroup.mem_subgroupOf] at hk
            obtain ⟨c, hc'⟩ := hk
            have hc'' : Matrix.GeneralLinearGroup.scalar ι c = z := hc'
            have hHcI : Hc ∉ ({Ha, Hb} : Finset (Hyperplane ↥Aε p)) := by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hca, hbc.symm⟩
            refine invol_ne_smul (glRep Aε) hp hA hpK h2 (Finset.mem_insert_self Ha {Hb}) hHcI
              ((hT Ha).mp hHa) ((hT Hc).mp hHc) (c : K) fun v => ?_
            rw [← glEquiv_involGL hA hp hpK, ← hzdef, ← hc'', glEquiv_scalar_apply]
          have hzF : z ∈ centGL (fieldSet Dat) := by
            rw [h𝒮0, mem_centGL]
            intro s hs
            exact absurd hs (Set.notMem_empty s)
          have hzA : ∀ y ∈ liftGroup Dat, z * y = y * z := by
            intro y hy
            apply glEquiv.injective
            refine LinearEquiv.ext fun v => ?_
            rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
              glEquiv_involGL hA hp hpK]
            have := invol_comm (glRep Aε) hp hA hpK {Ha, Hb}
              (glRep Aε ⟨y, hle hy⟩).toAddMonoidHom (glRep_preserves_weightFamily _) v
            simpa only [LinearMap.toAddMonoidHom_coe, glRep_apply_eq_glEquiv] using this
          obtain ⟨h1, h2', -⟩ := innerPart_eq_sup_of_involution hp hcore hZ hB hrank Dat hzH hz2
            hz1 hzF hzA
          exact ⟨hBB.symm.trans h1, h2'⟩
    ·
      have hBt : Nat.card B = p ^ (T.card + 1) := by rw [hBc, ← hcL, hcardA, pow_succ]
      by_cases h4' : 4 ≤ T.card
      · left
        exact caseI (by omega) (by rw [hBt]; exact Nat.pow_le_pow_right hp.pos (by omega))
          fun I hIT H₀ hH₀T hH₀I hIc => hU2s I hIT H₀ hH₀T hH₀I hIc h4'
      ·
        have ht : T.card = 3 := by
          have : 4 ≤ T.card + 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hBt ▸ h4)
          omega
        left
        have hU2 : ∀ Ha ∈ T, 2 ≤ Module.finrank K (wtU Aε {Ha}) := fun Ha hHa =>
          hU2sum {Ha} (T.erase Ha) (by simp [Finset.disjoint_singleton_left])
            (Finset.erase_subset _ _) (by rw [Finset.card_erase_of_mem hHa, ht])
        by_cases hev : ∃ Ha ∈ T, Even (Module.finrank K (weightSpace (glRep Aε) Ha.1))
        · obtain ⟨Ha, hHaT, hev⟩ := hev
          obtain ⟨Hb, hHbT, -, -, hba, -, -⟩ := hthree Ha hHaT ht
          have hHbI : Hb ∉ ({Ha} : Finset (Hyperplane ↥Aε p)) := fun h =>
            hba (Finset.mem_singleton.mp h)
          have hzH : glEquiv.symm (invol (glRep Aε) hp hA hpK {Ha}) ∈ H :=
            hzeven Ha hev
          exact caseSingle Ha Hb hHaT hHbT hba hzH (by norm_num) (involGL_apply_wtU hA hp hpK _)
            (involGL_apply_wtW hA hp hpK _) (hU2 Ha hHaT)
            (Or.inr ⟨hF, hEfield Ha Hb hHbT hba hF
              (hgood {Ha} Hb hHbI hHbT (hU2 Ha hHaT)).2⟩)
        ·
          push Not at hev
          obtain ⟨H₁, hH₁T⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨H₂, hH₂T, H₃, hH₃T, h21, h31, h23⟩ := hthree H₁ hH₁T ht
          have hodd : Odd (Fintype.card ι) := by
            rw [hNsum, hsum3 H₁ H₂ H₃ hH₁T hH₂T hH₃T h21.symm h31.symm h23 ht]
            have o1 := Nat.not_even_iff_odd.mp (hev H₁ hH₁T)
            have o2 := Nat.not_even_iff_odd.mp (hev H₂ hH₂T)
            have o3 := Nat.not_even_iff_odd.mp (hev H₃ hH₃T)
            rw [Nat.odd_iff] at o1 o2 o3 ⊢
            omega
          have hH₂I : H₂ ∉ ({H₁} : Finset (Hyperplane ↥Aε p)) := fun h =>
            h21 (Finset.mem_singleton.mp h)
          set z : GL ι K := Matrix.GeneralLinearGroup.scalar ι (-1) *
            glEquiv.symm (invol (glRep Aε) hp hA hpK {H₁}) with hzdef
          have hglz : ∀ v, glEquiv z v = (-1 : K) • invol (glRep Aε) hp hA hpK {H₁} v := by
            intro v
            rw [hzdef, map_mul, LinearEquiv.mul_apply, glEquiv_involGL hA hp hpK,
              glEquiv_scalar_apply, Units.val_neg,
              Units.val_one]
          have hneg : Matrix.GeneralLinearGroup.scalar ι (-1 : Kˣ) ∈ isomGL β :=
            scalar_mem_isomGL_of_mul _
              (by rw [Units.val_neg, Units.val_one, map_neg, map_one]; ring)
          have hzH : z ∈ H := by
            refine hdetH _ ((isomGL β).mul_mem hneg (involGL_mem_isomGL hA hp hpK hAεβ _)) ?_
            rw [hzdef, Units.val_mul, Matrix.det_mul, det_involGL hA hp hpK, Finset.sum_singleton,
              Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
              Finset.prod_const, Finset.card_univ, Units.val_neg, Units.val_one, ← pow_add]
            exact (hodd.add_odd (Nat.not_even_iff_odd.mp (hev H₁ hH₁T))).neg_one_pow
          refine caseSingle H₁ H₂ hH₁T hH₂T h21 hzH (s := -1) (by norm_num) (fun u hu => ?_)
            (fun w hw => ?_) (hU2 H₁ hH₁T) (Or.inr ⟨hF, hEfield H₁ H₂ hH₂T h21 hF
              (hgood {H₁} H₂ hH₂I hH₂T (hU2 H₁ hH₁T)).2⟩)
          · rw [hglz, ← glEquiv_involGL hA hp hpK, involGL_apply_wtU hA hp hpK _ u hu, one_smul]
          · rw [hglz, ← glEquiv_involGL hA hp hpK, involGL_apply_wtW hA hp hpK _ w hw, smul_smul]
            norm_num
  ·
    have hAL := hns_eq hsc
    have hLcard : Nat.card ↥(liftGroup Dat) = p ^ T.card := by rw [← hAL, hcardA]
    have hd2 : ∀ H' ∈ T, 2 ≤ Module.finrank K (weightSpace (glRep Aε) H'.1) := fun H' hH' =>
      two_le_finrank_weightSpace_of_not_scalar hp hβ hA hpK hAεβ hsc ((hT H').mp hH')
    have hU2n : ∀ I ⊆ T, ∀ H₀ ∈ T, H₀ ∉ I → I.card = 2 → 2 ≤ Module.finrank K (wtU Aε I) :=
      fun I _ H₀ hH₀T hH₀I _ => hU2one I H₀ hH₀I (hd2 H₀ hH₀T)
    rcases hBcard with ⟨hBB, hBc⟩ | ⟨hF, hBc⟩
    · have hBt : Nat.card B = p ^ (T.card + 1) := by rw [hBc, hLcard, pow_succ, mul_comm]
      by_cases h4' : 4 ≤ T.card
      · left
        exact caseI (by omega) (by rw [hBt]; exact Nat.pow_le_pow_right hp.pos (by omega)) hU2n
      ·
        have ht : T.card = 3 := by
          have : 4 ≤ T.card + 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hBt ▸ h4)
          omega
        by_cases hev : ∃ Ha ∈ T, Even (Module.finrank K (weightSpace (glRep Aε) Ha.1))
        · left
          obtain ⟨Ha, hHaT, hev⟩ := hev
          obtain ⟨Hb, hHbT, Hc, hHcT, hba, hca, hbc⟩ := hthree Ha hHaT ht
          have hHbI : Hb ∉ ({Ha} : Finset (Hyperplane ↥Aε p)) := fun h =>
            hba (Finset.mem_singleton.mp h)
          have hHcI : Hc ∉ ({Ha} : Finset (Hyperplane ↥Aε p)) := fun h =>
            hca (Finset.mem_singleton.mp h)
          have hzH : glEquiv.symm (invol (glRep Aε) hp hA hpK {Ha}) ∈ H :=
            hzeven Ha hev
          obtain ⟨xb, hxb, hxb'⟩ := hsupp Hb hHbT
          have hHcI' : Hc ∉ insert Hb ({Ha} : Finset (Hyperplane ↥Aε p)) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hbc.symm, hca⟩
          have hgood' := (hgood (insert Hb {Ha}) Hc hHcI' hHcT
            (hU2one _ Hc hHcI' (hd2 Hc hHcT))).1
          obtain ⟨-, hq', hdvd', -, -⟩ := hblk _ _ (hUW _) (horth _) (hnd _) hgood'
          obtain ⟨xc, hxc, hxc'⟩ := hsupp Hc hHcT
          obtain ⟨hxcB, hxcp⟩ := supported_mem_blkSub hp hA hpK hAεβ (insert Hb {Ha}) hHcI' hxc
            hxc'
          have hlay := glaPLayer_ne_bot_of_subBlock hp hA hpK hAεβ {Ha} hHbI hxb hxb' hq'
            (hdvd' _ hxcB hxcp)
          have hnsc : ¬ ∃ c : K, ∀ u ∈ wtU Aε {Ha}, glEquiv (xb : GL ι K) u = c • u := by
            rintro ⟨c, hc⟩
            obtain ⟨vc, hvc, hvc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ((hT Hc).mp hHcT)
            obtain ⟨vb, hvb, hvb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ((hT Hb).mp hHbT)
            have h1 : glEquiv (xb : GL ι K) vc = vc := by
              rw [← glRep_apply_eq_glEquiv]
              exact apply_eq_of_mem_weightSpace (glRep Aε)
                (hxb' Hc (fun h => hbc (Finset.mem_singleton.mp h).symm) ((hT Hc).mp hHcT)) hvc
            have hc1 : c = 1 := by
              have h2' := hc vc (weightSpace_le_ker_projI hp hA hpK hHcI hvc)
              rw [h1] at h2'
              have h3 : (c - 1) • vc = 0 := by rw [sub_smul, ← h2', one_smul, sub_self]
              exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hvc0)
            have h3 := hc vb (weightSpace_le_ker_projI hp hA hpK hHbI hvb)
            rw [hc1, one_smul, ← glRep_apply_eq_glEquiv] at h3
            exact hvb0 (eq_zero_of_mem_weightSpace_of_fixed (glRep Aε) hp hA hpK
              (hxb Hb (Finset.mem_singleton_self _)) hvb h3)
          exact caseSingle Ha Hb hHaT hHbT hba hzH (by norm_num) (involGL_apply_wtU hA hp hpK _)
            (involGL_apply_wtW hA hp hpK _)
            (hU2one _ Hb hHbI (hd2 Hb hHbT)) (Or.inl ⟨xb, xb.2, hnsc, hlay⟩)
        ·
          right
          left
          push Not at hev
          refine ⟨by rw [hBt, ht], Or.inl ?_⟩
          obtain ⟨H₁, hH₁T⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨H₂, hH₂T, H₃, hH₃T, h21, h31, h23⟩ := hthree H₁ hH₁T ht
          rw [hsum3 H₁ H₂ H₃ hH₁T hH₂T hH₃T h21.symm h31.symm h23 ht] at hNle
          have e1 := hd2 H₁ hH₁T
          have e2 := hd2 H₂ hH₂T
          have e3 := hd2 H₃ hH₃T
          have o1 := Nat.not_even_iff_odd.mp (hev H₁ hH₁T)
          have o2 := Nat.not_even_iff_odd.mp (hev H₂ hH₂T)
          have o3 := Nat.not_even_iff_odd.mp (hev H₃ hH₃T)
          rw [Nat.odd_iff] at o1 o2 o3
          omega
    · have hBt : Nat.card B = p ^ (T.card + 2) := by rw [hBc, hLcard]; ring
      by_cases h3 : 3 ≤ T.card
      · left
        exact caseI h3 (by rw [hBt]; exact Nat.pow_le_pow_right hp.pos (by omega)) hU2n
      ·
        have ht : T.card = 2 := by
          have : 4 ≤ T.card + 2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hBt ▸ h4)
          omega
        have hother : ∀ Ha ∈ T, ∃ Hb ∈ T, Hb ≠ Ha := by
          intro Ha hHa
          obtain ⟨Hb, hHb⟩ := Finset.card_pos.mp
            (by rw [Finset.card_erase_of_mem hHa, ht]; norm_num : 0 < (T.erase Ha).card)
          exact ⟨Hb, Finset.mem_of_mem_erase hHb, Finset.ne_of_mem_erase hHb⟩
        by_cases hev : ∃ Ha ∈ T, Even (Module.finrank K (weightSpace (glRep Aε) Ha.1))
        · left
          obtain ⟨Ha, hHaT, hev⟩ := hev
          obtain ⟨Hb, hHbT, hba⟩ := hother Ha hHaT
          have hHbI : Hb ∉ ({Ha} : Finset (Hyperplane ↥Aε p)) := fun h =>
            hba (Finset.mem_singleton.mp h)
          have hzH : glEquiv.symm (invol (glRep Aε) hp hA hpK {Ha}) ∈ H :=
            hzeven Ha hev
          have h2U := hU2one _ Hb hHbI (hd2 Hb hHbT)
          exact caseSingle Ha Hb hHaT hHbT hba hzH (by norm_num) (involGL_apply_wtU hA hp hpK _)
            (involGL_apply_wtW hA hp hpK _) h2U
            (Or.inr ⟨hF, hEfield Ha Hb hHbT hba hF (hgood {Ha} Hb hHbI hHbT h2U).2⟩)
        ·
          right
          left
          push Not at hev
          refine ⟨by rw [hBt, ht], Or.inr ⟨?_, hF⟩⟩
          obtain ⟨H₁, hH₁T⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨H₂, hH₂T, h21⟩ := hother H₁ hH₁T
          rw [hsum2 H₁ H₂ hH₁T hH₂T h21.symm ht] at hNle
          have e1 := hd2 H₁ hH₁T
          have e2 := hd2 H₂ hH₂T
          have o1 := Nat.not_even_iff_odd.mp (hev H₁ hH₁T)
          have o2 := Nat.not_even_iff_odd.mp (hev H₂ hH₂T)
          rw [Nat.odd_iff] at o1 o2
          omega

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
