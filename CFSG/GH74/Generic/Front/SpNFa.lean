module

public import CFSG.GH74.Generic.Front.SpNFDefs

public section

namespace CFSG.GH74.Generic

open Module Matrix

section SpNFa

variable {F : Type} [Field F]

private theorem tensorNF_of_basis (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (p q : Fin 2 → Fin 2 ⊕ Fin 2 → F) (a G : Matrix (Fin 2) (Fin 2) F)
    (hG : IsUnit G.det) (hGs : ∀ i j, G j i = G i j)
    (hp : ∀ j, A *ᵥ p j = ∑ i, a i j • p i) (hq : ∀ j, A *ᵥ q j = ∑ i, a i j • q i)
    (hpp : ∀ i j, sp2Form (p i) (p j) = 0) (hqq : ∀ i j, sp2Form (q i) (q j) = 0)
    (hpq : ∀ i j, sp2Form (p i) (q j) = G i j) : TensorNF A := by
  classical
  have hqp : ∀ i j, sp2Form (q i) (p j) = -G i j := fun i j => by
    rw [sp2Form_comm, hpq, hGs]
  have hgram : (sp2ColMat p q)ᵀ * sp2Gram F * sp2ColMat p q = fromBlocks 0 G (-G) 0 := by
    ext x y
    rw [sp2_gram_apply]
    rcases x with i | i <;> rcases y with j | j
    · rw [sp2ColMat_mulVec_inl, sp2ColMat_mulVec_inl, hpp]
      simp
    · rw [sp2ColMat_mulVec_inl, sp2ColMat_mulVec_inr, hpq]
      simp
    · rw [sp2ColMat_mulVec_inr, sp2ColMat_mulVec_inl, hqp]
      simp
    · rw [sp2ColMat_mulVec_inr, sp2ColMat_mulVec_inr, hqq]
      simp
  refine ⟨sp2ColMat p q, a, G, ?_, ?_, hgram⟩
  · have hG2 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hG
    have hT : (fromBlocks 0 (-G⁻¹) G⁻¹ 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        fromBlocks 0 G (-G) 0 = 1 := by
      rw [fromBlocks_multiply]
      simp [hG2, ← fromBlocks_one]
    have hinv : ((fromBlocks 0 (-G⁻¹) G⁻¹ 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((sp2ColMat p q)ᵀ * sp2Gram F)) * sp2ColMat p q = 1 := by
      rw [Matrix.mul_assoc, hgram, hT]
    exact isUnit_det_of_left_inverse hinv
  · ext x y
    rcases y with j | j
    · have h := congrFun (hp j) x
      simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      simp [Matrix.mul_apply, Fintype.sum_sum_type, sp2ColMat, h, mul_comm]
    · have h := congrFun (hq j) x
      simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      simp [Matrix.mul_apply, Fintype.sum_sum_type, sp2ColMat, h, mul_comm]

private theorem sp2Form_mulVec_similitude {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} {μ : F}
    (hs : Aᵀ * sp2Gram F * A = μ • sp2Gram F) (a b : Fin 2 ⊕ Fin 2 → F) :
    sp2Form (A *ᵥ a) (A *ᵥ b) = μ * sp2Form a b := by
  have h1 : ∀ x : Fin 2 ⊕ Fin 2 → F, (A *ᵥ a) ⬝ᵥ x = a ⬝ᵥ (Aᵀ *ᵥ x) := by
    intro x
    rw [dotProduct_comm, dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  rw [sp2Form, h1, mulVec_mulVec, mulVec_mulVec, hs, smul_mulVec, dotProduct_smul, smul_eq_mul]

private theorem sp2Form_adj {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} {c μ : F}
    (hAA : A * A = c • 1) (hs : Aᵀ * sp2Gram F * A = μ • sp2Gram F) (u v : Fin 2 ⊕ Fin 2 → F) :
    c * sp2Form (A *ᵥ u) v = μ * sp2Form u (A *ᵥ v) := by
  have h := sp2Form_mulVec_similitude hs u (A *ᵥ v)
  rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec, sp2Form_smul_right] at h
  exact h

private theorem exists_dual_pair {W₁ W₂ : Submodule F (Fin 2 ⊕ Fin 2 → F)} (hc : IsCompl W₁ W₂)
    (h11 : ∀ u ∈ W₁, ∀ u' ∈ W₁, sp2Form u u' = 0) (h22 : ∀ w ∈ W₂, ∀ w' ∈ W₂, sp2Form w w' = 0) :
    ∃ e f : Fin 2 → Fin 2 ⊕ Fin 2 → F, (∀ i, e i ∈ W₁) ∧ (∀ i, f i ∈ W₂) ∧
      ∀ i j, sp2Form (e i) (f j) = if i = j then 1 else 0 := by
  classical
  let E : (Fin 2 ⊕ Fin 2 → F) →ₗ[F] (Fin 2 ⊕ Fin 2 → F) →ₗ[F] F :=
    LinearMap.mk₂ F sp2Form
      (fun x y v => by simp [sp2Form, add_dotProduct])
      (fun c x v => by simp [sp2Form, smul_dotProduct])
      sp2Form_add_right sp2Form_smul_right
  let E12 : W₁ →ₗ[F] W₂ →ₗ[F] F := E.compl₁₂ W₁.subtype W₂.subtype
  have hE12 : ∀ (u : W₁) (w : W₂),
      E12 u w = sp2Form (u : Fin 2 ⊕ Fin 2 → F) (w : Fin 2 ⊕ Fin 2 → F) := fun u w => rfl
  have hspan : ∀ v : Fin 2 ⊕ Fin 2 → F, ∃ x ∈ W₁, ∃ y ∈ W₂, x + y = v := fun v => by
    have hv : v ∈ W₁ ⊔ W₂ := by rw [hc.sup_eq_top]; trivial
    exact Submodule.mem_sup.1 hv
  have hinj1 : Function.Injective E12 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hu' : ∀ w : W₂, sp2Form (u : Fin 2 ⊕ Fin 2 → F) (w : Fin 2 ⊕ Fin 2 → F) = 0 := fun w => by
      rw [← hE12]; exact LinearMap.congr_fun hu w
    have h0 : (u : Fin 2 ⊕ Fin 2 → F) = 0 := by
      refine eq_zero_of_sp2Form_right fun v => ?_
      obtain ⟨x, hx, y, hy, rfl⟩ := hspan v
      rw [sp2Form_add_right, h11 _ u.2 x hx, hu' ⟨y, hy⟩, add_zero]
    exact Subtype.ext h0
  have hinj2 : Function.Injective E12.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hw' : ∀ u : W₁, sp2Form (u : Fin 2 ⊕ Fin 2 → F) (w : Fin 2 ⊕ Fin 2 → F) = 0 := fun u => by
      rw [← hE12]; exact LinearMap.congr_fun hw u
    have h0 : (w : Fin 2 ⊕ Fin 2 → F) = 0 := by
      refine eq_zero_of_sp2Form_right fun v => ?_
      obtain ⟨x, hx, y, hy, rfl⟩ := hspan v
      rw [sp2Form_add_right, sp2Form_comm x (w : Fin 2 ⊕ Fin 2 → F), hw' ⟨x, hx⟩, neg_zero,
        h22 _ w.2 y hy, add_zero]
    exact Subtype.ext h0
  have hfin : finrank F (Fin 2 ⊕ Fin 2 → F) = 4 := by simp
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have d12 : finrank F W₁ ≤ finrank F W₂ := by
    have := LinearMap.finrank_le_finrank_of_injective hinj1
    rwa [Subspace.dual_finrank_eq] at this
  have d21 : finrank F W₂ ≤ finrank F W₁ := by
    have := LinearMap.finrank_le_finrank_of_injective hinj2
    rwa [Subspace.dual_finrank_eq] at this
  have h1 : finrank F W₁ = 2 := by omega
  have h2' : finrank F W₂ = 2 := by omega
  let eb : Basis (Fin 2) F W₁ := Module.finBasisOfFinrankEq F W₁ h1
  have hsurj : Function.Surjective E12.flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Subspace.dual_finrank_eq, h1, h2'])).1 hinj2
  choose w hw using fun j => hsurj (eb.dualBasis j)
  refine ⟨fun i => (eb i : Fin 2 ⊕ Fin 2 → F), fun j => (w j : Fin 2 ⊕ Fin 2 → F),
    fun i => (eb i).2, fun j => (w j).2, fun i j => ?_⟩
  have h := LinearMap.congr_fun (hw j) (eb i)
  rw [LinearMap.flip_apply, hE12, Basis.dualBasis_apply_self] at h
  exact h

end SpNFa

theorem tensorNF_nonsplit_plus {F : Type} [Field F] (h2 : (2 : F) ≠ 0)
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (l : F) (hl : ¬ IsSquare l)
    (hAA : A * A = l • 1) (hAJ : Aᵀ * sp2Gram F * A = l • sp2Gram F) : TensorNF A := by
  classical
  have hl0 : l ≠ 0 := fun h => hl ⟨0, by rw [h, mul_zero]⟩
  have hadj : ∀ u v, sp2Form (A *ᵥ u) v = sp2Form u (A *ᵥ v) := fun u v =>
    mul_left_cancel₀ hl0 (sp2Form_adj hAA hAJ u v)
  have hAu : ∀ u, sp2Form u (A *ᵥ u) = 0 := fun u => by
    have h1 := hadj u u
    have h3 := sp2Form_comm u (A *ᵥ u)
    have : (2 : F) * sp2Form u (A *ᵥ u) = 0 := by linear_combination h3 - h1
    exact (mul_eq_zero.1 this).resolve_left h2
  have hA2 : ∀ v, A *ᵥ (A *ᵥ v) = l • v := fun v => by
    rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec]
  have hAA' : ∀ u v, sp2Form (A *ᵥ u) (A *ᵥ v) = l * sp2Form u v :=
    sp2Form_mulVec_similitude hAJ
  have hbasis : ∀ c d : Fin 2 ⊕ Fin 2, sp2Form (Pi.single c (1 : F)) (Pi.single d (1 : F)) =
      sp2Gram F c d := fun c d => by
    simp
  obtain ⟨e, f, hef⟩ : ∃ e f : Fin 2 ⊕ Fin 2 → F, sp2Form e f = 1 :=
    ⟨Pi.single (Sum.inl 0) 1, Pi.single (Sum.inr 0) 1, by rw [hbasis]; simp⟩
  have hpp : ∀ u : Fin 2 ⊕ Fin 2 → F, ∀ i j,
      sp2Form (![u, A *ᵥ u] i) (![u, A *ᵥ u] j) = 0 := by
    intro u i j
    fin_cases i <;> fin_cases j
    · exact sp2Form_self h2 u
    · exact hAu u
    · exact (hadj u u).trans (hAu u)
    · show sp2Form (A *ᵥ u) (A *ᵥ u) = 0
      rw [hAA', sp2Form_self h2, mul_zero]
  have hact : ∀ u : Fin 2 ⊕ Fin 2 → F, ∀ j, A *ᵥ (![u, A *ᵥ u] j) =
      ∑ i, (!![0, l; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j • ![u, A *ᵥ u] i := by
    intro u j
    fin_cases j
    · simp [Fin.sum_univ_two]
    · simp [Fin.sum_univ_two, hA2]
  refine tensorNF_of_basis A ![e, A *ᵥ e] ![f, A *ᵥ f] !![0, l; 1, 0]
    !![1, sp2Form e (A *ᵥ f); sp2Form e (A *ᵥ f), l] ?_ ?_ (hact e) (hact f) (hpp e) (hpp f) ?_
  · rw [Matrix.det_fin_two_of]
    exact isUnit_iff_ne_zero.2 fun h => hl ⟨sp2Form e (A *ᵥ f), by linear_combination h⟩
  · simp [Fin.forall_fin_two]
  · intro i j
    fin_cases i <;> fin_cases j
    · exact hef
    · rfl
    · exact hadj e f
    · show sp2Form (A *ᵥ e) (A *ᵥ f) = l
      rw [hAA', hef, mul_one]

theorem tensorNF_split_minus {F : Type} [Field F] (h2 : (2 : F) ≠ 0)
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (ν : F) (hν : ν ≠ 0)
    (hAA : A * A = (ν ^ 2) • 1) (hAJ : Aᵀ * sp2Gram F * A = (-(ν ^ 2)) • sp2Gram F) :
    TensorNF A := by
  classical
  have hν2 : ν ^ 2 ≠ 0 := pow_ne_zero 2 hν
  have hA2 : ∀ v, A *ᵥ (A *ᵥ v) = (ν ^ 2) • v := fun v => by
    rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec]
  have hAA' : ∀ u v, sp2Form (A *ᵥ u) (A *ᵥ v) = -(ν ^ 2) * sp2Form u v :=
    sp2Form_mulVec_similitude hAJ
  have hsl : ∀ (c : F) (u w : Fin 2 ⊕ Fin 2 → F), sp2Form (c • u) w = c * sp2Form u w :=
    fun c u w => by simp [sp2Form, smul_dotProduct]
  have hnr : ∀ u v : Fin 2 ⊕ Fin 2 → F, sp2Form u (-v) = -sp2Form u v :=
    fun u v => by rw [sp2Form, sp2Form, mulVec_neg, dotProduct_neg]
  let Wp : Submodule F (Fin 2 ⊕ Fin 2 → F) := Module.End.eigenspace (Matrix.toLin' A) ν
  let Wm : Submodule F (Fin 2 ⊕ Fin 2 → F) := Module.End.eigenspace (Matrix.toLin' A) (-ν)
  have hWp : ∀ u, u ∈ Wp ↔ A *ᵥ u = ν • u := fun u => by
    simp [Wp]
  have hWm : ∀ u, u ∈ Wm ↔ A *ᵥ u = (-ν) • u := fun u => by
    simp [Wm]
  have hc : IsCompl Wp Wm := by
    refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro u hup hum
      have h3 : (ν - -ν) • u = 0 := by
        rw [sub_smul, ← (hWp u).1 hup, ← (hWm u).1 hum, sub_self]
      exact (smul_eq_zero.1 h3).resolve_left fun h => mul_ne_zero h2 hν (by linear_combination h)
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have h1 : (ν • v + A *ᵥ v) ∈ Wp := (hWp _).2 (by
        rw [mulVec_add, mulVec_smul, hA2]; module)
      have h2' : (ν • v - A *ᵥ v) ∈ Wm := (hWm _).2 (by
        rw [mulVec_sub, mulVec_smul, hA2]; module)
      have hv : v = (2 * ν)⁻¹ • (ν • v + A *ᵥ v) + (2 * ν)⁻¹ • (ν • v - A *ᵥ v) := by
        rw [← smul_add]
        have : ν • v + A *ᵥ v + (ν • v - A *ᵥ v) = (2 * ν) • v := by module
        rw [this, smul_smul, inv_mul_cancel₀ (mul_ne_zero h2 hν), one_smul]
      rw [hv]
      exact Submodule.add_mem_sup (Wp.smul_mem _ h1) (Wm.smul_mem _ h2')
  have h11 : ∀ u ∈ Wp, ∀ u' ∈ Wp, sp2Form u u' = 0 := fun u hu u' hu' => by
    have h := hAA' u u'
    rw [(hWp u).1 hu, (hWp u').1 hu', hsl, sp2Form_smul_right] at h
    have : (2 * ν ^ 2) * sp2Form u u' = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 hν2)
  have h22 : ∀ w ∈ Wm, ∀ w' ∈ Wm, sp2Form w w' = 0 := fun u hu u' hu' => by
    have h := hAA' u u'
    rw [(hWm u).1 hu, (hWm u').1 hu', hsl, sp2Form_smul_right] at h
    have : (2 * ν ^ 2) * sp2Form u u' = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 hν2)
  obtain ⟨e, f, he, hf, hef⟩ := exists_dual_pair hc h11 h22
  have hAe : ∀ i, A *ᵥ e i = ν • e i := fun i => (hWp _).1 (he i)
  have hAf : ∀ i, A *ᵥ f i = (-ν) • f i := fun i => (hWm _).1 (hf i)
  have hee : ∀ i j, sp2Form (e i) (e j) = 0 := fun i j => h11 _ (he i) _ (he j)
  have hff : ∀ i j, sp2Form (f i) (f j) = 0 := fun i j => h22 _ (hf i) _ (hf j)
  have hfe : ∀ i j, sp2Form (f i) (e j) = -(if j = i then 1 else 0) := fun i j => by
    rw [sp2Form_comm, hef]
  refine tensorNF_of_basis A ![e 0, f 1] ![e 1, -f 0] !![ν, 0; 0, -ν] !![0, -1; -1, 0]
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Matrix.det_fin_two_of]
    exact isUnit_iff_ne_zero.2 (by simp)
  · simp [Fin.forall_fin_two]
  · intro j
    fin_cases j
    · simp [Fin.sum_univ_two, hAe]
    · simp [Fin.sum_univ_two, hAf]
  · intro j
    fin_cases j
    · simp [Fin.sum_univ_two, hAe]
    · simp [Fin.sum_univ_two, mulVec_neg, hAf]
  · intro i j
    fin_cases i <;> fin_cases j
    · exact hee 0 0
    · simpa using hef 0 1
    · simpa using hfe 1 0
    · exact hff 1 1
  · intro i j
    fin_cases i <;> fin_cases j
    · exact hee 1 1
    · show sp2Form (e 1) (-f 0) = 0
      rw [hnr, hef]; simp
    · show sp2Form (-f 0) (e 1) = 0
      rw [sp2Form_neg_left, hfe]; simp
    · show sp2Form (-f 0) (-f 0) = 0
      exact sp2Form_self h2 _
  · intro i j
    fin_cases i <;> fin_cases j
    · exact hee 0 1
    · show sp2Form (e 0) (-f 0) = -1
      rw [hnr, hef]; simp
    · show sp2Form (f 1) (e 1) = -1
      rw [hfe]; simp
    · show sp2Form (f 1) (-f 0) = 0
      rw [hnr, hff, neg_zero]

end CFSG.GH74.Generic
