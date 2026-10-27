module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4BurgDb
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLUnitary
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLField

public section

namespace CFSG.ComponentClassification.CatFactsL4U4.BurgD

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.TBLit
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem coe_slConj (A : GL (Fin 4) K) (g : SL(4, K)) :
    ((CatalogueBHigherLinearAction.slConjugation 4 K A g : SL(4, K)) :
        Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * (g : Matrix (Fin 4) (Fin 4) K) *
        ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
  CatalogueBHigherLinearAction.slConjugation_matrix 4 K A g

theorem orderOf_neg_one (h2 : (2 : K) ≠ 0) {g₀ : SL(4, K)}
    (hg₀ : (g₀ : Matrix (Fin 4) (Fin 4) K) = -1) : orderOf g₀ = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two]
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, hg₀, Matrix.SpecialLinearGroup.coe_one, neg_one_mul,
      neg_neg]
  · intro h
    have := congrArg (fun x : SL(4, K) => (x : Matrix (Fin 4) (Fin 4) K) 0 0) h
    simp only [hg₀, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply, one_apply_eq] at this
    exact h2 (by linear_combination -this)

theorem neg_one_comm {g₀ : SL(4, K)} (hg₀ : (g₀ : Matrix (Fin 4) (Fin 4) K) = -1)
    (g : SL(4, K)) : g₀ * g = g * g₀ := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg₀, neg_one_mul,
    mul_neg_one]

theorem sign_conj_mul_proj {J : Finset (Fin 4)} {P X : Matrix (Fin 4) (Fin 4) K} {ε : K}
    (hε : ε * ε = 1) (hSP : signMat K J * P = ε • P) (hXP : X * P = P * X) :
    signMat K J * X * signMat K J * P = X * P := by
  rw [Matrix.mul_assoc, hSP, Matrix.mul_smul, Matrix.mul_assoc, hXP, ← Matrix.mul_assoc, hSP,
    Matrix.smul_mul, smul_smul, hε, one_smul]

theorem inner_trivial {L : Type*} [Group L] [Finite L] (e : SL(4, K) ≃* L) (h2 : (2 : K) ≠ 0)
    {J : Finset (Fin 4)} (hJ : Odd J.card) {Q : Subgroup L} {F : Type*} [Field F]
    (h2F : (2 : F) ≠ 0) (e₁ : Q ⧸ pPrimeCore 2 Q ≃* SL(2, F)) {γ : L → L}
    (hγ : ∀ g, γ (e g) = e (CatalogueBHigherLinearAction.slConjugation 4 K (signGL K J) g))
    (hγQ : ∀ a ∈ Q, γ a ∈ Q) (B : GL (Fin 4) K)
    (hBS : (B : Matrix (Fin 4) (Fin 4) K) * signMat K J = signMat K J * B) {l : K}
    (hl : (B : Matrix (Fin 4) (Fin 4) K) * B = l • 1)
    (hns : ∀ c : K, (B : Matrix (Fin 4) (Fin 4) K) ≠ c • 1)
    (hQB : ∀ a ∈ Q, ((e.symm a : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) * B =
      B * ((e.symm a : SL(4, K)) : Matrix (Fin 4) (Fin 4) K))
    {g₀ : SL(4, K)} (hg₀ : (g₀ : Matrix (Fin 4) (Fin 4) K) = -1) (hcQ : e g₀ ∈ Q) :
    ∀ a ∈ Q, γ a * a⁻¹ ∈ (pPrimeCore 2 Q).map Q.subtype := by
  have hdet : IsUnit (B : Matrix (Fin 4) (Fin 4) K).det :=
    ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit)
  obtain ⟨P, ε, hP, hP0, hε, hSP, -, hcomm⟩ := exists_proj h2 hJ hBS hl hdet hns
  set ι : Q →* Matrix (Fin 4) (Fin 4) K :=
    ((Units.coeHom (Matrix (Fin 4) (Fin 4) K)).comp SpecialLinearGroup.toGL).comp
      (e.symm.toMonoidHom.comp Q.subtype) with hιdef
  have hιa : ∀ a : Q, ι a = ((e.symm a : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) := fun a => rfl
  have hι : ∀ a, ι a * P = P * ι a := fun a => by rw [hιa]; exact hcomm _ (hQB a a.2)
  refine mul_inv_mem_of_rep h2F e₁ hγQ (projHom ι hP hι) (fun a ha => ?_) hcQ ?_ ?_
  · rw [projHom_apply, projHom_apply, hιa, hιa]
    congr 1
    have h1 : e.symm (γ a) = CatalogueBHigherLinearAction.slConjugation 4 K (signGL K J)
        (e.symm a) := by
      rw [← e.apply_symm_apply a, hγ, e.symm_apply_apply, e.symm_apply_apply]
    change ((e.symm (γ a) : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) * P = _
    rw [h1, coe_slConj, signGL_inv, coe_signGL]
    exact sign_conj_mul_proj hε hSP (hcomm _ (hQB a ha))
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_neg_one h2 hg₀
  · rw [projHom_apply, hιa]
    change ((e.symm (e g₀) : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) * P + (1 - P) ≠ 1
    rw [e.symm_apply_apply, hg₀, neg_one_mul]
    intro h
    apply hP0
    have h' : (2 : K) • P = 0 := by
      rw [two_smul]
      have := congrArg (fun M => 1 - M) h
      simp only [sub_self] at this
      rw [← this]
      abel
    exact (smul_eq_zero.1 h').resolve_left h2

theorem sq_eq_sq_of_commute_dual [Finite K] (h2 : (2 : K) ≠ 0) {J : Finset (Fin 4)}
    (hJ : Odd J.card) (B : GL (Fin 4) K) (α β : Kˣ) (hαβ : (α : K) ≠ β)
    (h : conjAut 4 K B * dualAut 4 K * conjAut 4 K (blockScalarGL J α β) =
      conjAut 4 K (blockScalarGL J α β) * (conjAut 4 K B * dualAut 4 K)) :
    (α : K) * α = β * β := by
  set D := blockScalarGL (K := K) J α β with hD
  set D' := GeneralLinearGroup.inverseTranspose D with hD'
  have h1 : conjAut 4 K (B * D') * dualAut 4 K = conjAut 4 K (D * B) * dualAut 4 K := by
    rw [map_mul, mul_assoc, ← dualAut_mul_conjAut, ← mul_assoc, h, map_mul, mul_assoc]
  have h2' : conjAut 4 K (B * D') = conjAut 4 K (D * B) := mul_right_cancel h1
  have h3 : conjAut 4 K (B * D' * B⁻¹ * D⁻¹) * fieldAut 4 K 1 = 1 := by
    rw [map_one, mul_one, map_mul, map_mul, h2', ← map_mul, ← map_mul, mul_inv_cancel_right,
      mul_inv_cancel, map_one]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ 1 h3
  have h4 : B * D' * B⁻¹ = GeneralLinearGroup.scalar (Fin 4) c * D := by
    rw [hc, inv_mul_cancel_right]
  have hD'm : (D' : Matrix (Fin 4) (Fin 4) K) =
      diagonal fun i => if i ∈ J then (α : K)⁻¹ else (β : K)⁻¹ := by
    rw [hD', GeneralLinearGroup.coe_inverseTranspose]
    change (diagonal fun i => if i ∈ J then ((α⁻¹ : Kˣ) : K) else ((β⁻¹ : Kˣ) : K))ᵀ = _
    rw [diagonal_transpose]
    congr 1
    funext i
    split_ifs <;> simp
  have h5 : (B : Matrix (Fin 4) (Fin 4) K) *
      (diagonal fun i => if i ∈ J then (α : K)⁻¹ else (β : K)⁻¹) *
        ((B⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (c : K) • diagonal fun i => if i ∈ J then (α : K) else β := by
    have := congrArg (fun M : GL (Fin 4) K => (M : Matrix (Fin 4) (Fin 4) K)) h4
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [← hD'm, this, hD, coe_blockScalarGL, scalar_apply, ← smul_one_eq_diagonal,
      Matrix.smul_mul, Matrix.one_mul]
  have hinv : (α : K)⁻¹ ≠ (β : K)⁻¹ := fun h' => hαβ (inv_injective h')
  obtain ⟨ha, hb⟩ := spectral h2 hJ hinv hαβ B h5
  have hα0 : (α : K) ≠ 0 := α.ne_zero
  have hβ0 : (β : K) ≠ 0 := β.ne_zero
  have hca : (c : K) * α * α = 1 := by rw [ha, inv_mul_cancel₀ hα0]
  have hcb : (c : K) * β * β = 1 := by rw [hb, inv_mul_cancel₀ hβ0]
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  apply mul_left_cancel₀ hc0
  rw [← mul_assoc, ← mul_assoc, hca, hcb]

theorem false_of_two_involutions {L : Type*} [Group L] [Finite L] {Q : Subgroup L}
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (e₁ : Q ⧸ pPrimeCore 2 Q ≃* SL(2, F)) {a b : L}
    (ha : a ∈ Q) (hb : b ∈ Q) (hao : orderOf a = 2) (hbo : orderOf b = 2) (hab : a * b = b * a)
    (hne : a ≠ b) : False := by
  have := Burgoyne.C.eq_of_involutions h2 e₁ (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    (by rw [Subgroup.orderOf_mk]; exact hao) (by rw [Subgroup.orderOf_mk]; exact hbo)
    (Subtype.ext hab)
  exact hne (congrArg Subtype.val this)

theorem pair01 : (({0, 1} : Finset (Fin 4)).card) = 2 := by decide

theorem conj_signSL_ne (h2 : (2 : K) ≠ 0) (H : GL (Fin 4) K) {g₀ : SL(4, K)}
    (hg₀ : (g₀ : Matrix (Fin 4) (Fin 4) K) = -1) :
    CatalogueBHigherLinearAction.slConjugation 4 K H
      (signSL K {0, 1} (by rw [pair01]; exact even_two)) ≠ g₀ := by
  intro h
  have h1 : signSL K {0, 1} (by rw [pair01]; exact even_two) =
      CatalogueBHigherLinearAction.slConjugation 4 K H⁻¹ g₀ := by
    rw [← h, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  have h2' : CatalogueBHigherLinearAction.slConjugation 4 K H⁻¹ g₀ = g₀ := by
    apply Subtype.ext
    rw [coe_slConj, hg₀, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, ← Units.val_mul,
      inv_inv, inv_mul_cancel, Units.val_one]
  rw [h2'] at h1
  have := congrArg (fun x : SL(4, K) => (x : Matrix (Fin 4) (Fin 4) K) 2 2) h1
  simp only [coe_signSL, signMat, diagonal_apply_eq, hg₀, Matrix.neg_apply, one_apply_eq] at this
  norm_num at this
  exact h2 (by linear_combination this)

theorem autFixed_eq_map {L : Type*} [Group L] (e : SL(4, K) ≃* L) {s : MulAut L}
    {H : GL (Fin 4) K} {σ : MulAut SL(4, K)} {C : Subgroup SL(4, K)}
    (hC : ∀ g, σ g = g ↔ g ∈ C)
    (hs : ∀ g, s (e g) = e ((CatalogueBHigherLinearAction.slConjugation 4 K H * σ *
      (CatalogueBHigherLinearAction.slConjugation 4 K H)⁻¹) g)) :
    autFixed s = C.map ((e.toMonoidHom).comp
      (CatalogueBHigherLinearAction.slConjugation 4 K H).toMonoidHom) := by
  set c := CatalogueBHigherLinearAction.slConjugation 4 K H with hc
  ext x
  change s x = x ↔ _
  constructor
  · intro hx
    refine ⟨c.symm (e.symm x), (hC _).1 ?_, ?_⟩
    · have h1 := hs (e.symm x)
      rw [e.apply_symm_apply, hx] at h1
      have h2 : e.symm x = (c * σ * c⁻¹) (e.symm x) := by
        have := congrArg e.symm h1
        rwa [e.symm_apply_apply] at this
      change e.symm x = c (σ (c.symm (e.symm x))) at h2
      have h3 := congrArg c.symm h2
      rw [c.symm_apply_apply] at h3
      exact h3.symm
    · change e (c (c.symm (e.symm x))) = x
      rw [c.apply_symm_apply, e.apply_symm_apply]
  · rintro ⟨g, hg, rfl⟩
    change s (e (c g)) = e (c g)
    rw [hs]
    change e (c (σ (c.symm (c g)))) = e (c g)
    rw [c.symm_apply_apply, (hC g).2 hg]

theorem false_of_quasisimple_fixed {L : Type*} [Group L] [Finite L] [Finite K]
    (e : SL(4, K) ≃* L) (h2 : (2 : K) ≠ 0) {s : MulAut L} {H : GL (Fin 4) K}
    {σ : MulAut SL(4, K)} {C : Subgroup SL(4, K)} (hC : ∀ g, σ g = g ↔ g ∈ C)
    (hCq : IsQuasisimple C) (hsign : signSL K {0, 1} (by rw [pair01]; exact even_two) ∈ C)
    (hs : ∀ g, s (e g) = e ((CatalogueBHigherLinearAction.slConjugation 4 K H * σ *
      (CatalogueBHigherLinearAction.slConjugation 4 K H)⁻¹) g))
    {Q : Subgroup L} (hQs : Q ≤ autFixed s) (hQc : IsPComponent 2 (Q.subgroupOf (autFixed s)))
    {F : Type*} [Field F] (h2F : (2 : F) ≠ 0) (e₁ : Q ⧸ pPrimeCore 2 Q ≃* SL(2, F))
    {g₀ : SL(4, K)} (hg₀ : (g₀ : Matrix (Fin 4) (Fin 4) K) = -1) (hcQ : e g₀ ∈ Q) : False := by
  set c := CatalogueBHigherLinearAction.slConjugation 4 K H with hc
  set f : SL(4, K) →* L := (e.toMonoidHom).comp c.toMonoidHom with hf
  have hfi : Function.Injective f := e.injective.comp c.injective
  have hN := autFixed_eq_map e hC hs
  have hNq : IsQuasisimple (autFixed s) := by
    rw [hN]
    exact LocalCores.isQuasisimple_of_mulEquiv (C.equivMapOfInjective f hfi) hCq
  have hQN : Q = autFixed s := Burgoyne.C.eq_of_le_of_isQuasisimple hQs le_rfl hQc hNq
  set g₁ := signSL K {0, 1} (by rw [pair01]; exact even_two) with hg₁
  have hbN : f g₁ ∈ autFixed s := by
    rw [hN]
    exact ⟨g₁, hsign, rfl⟩
  have hg₁2 : orderOf g₁ = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, hg₁, signSL_mul_self]
    · intro h
      have := congrArg (fun x : SL(4, K) => (x : Matrix (Fin 4) (Fin 4) K) 0 0) h
      simp only [hg₁, coe_signSL, signMat, diagonal_apply_eq, Matrix.SpecialLinearGroup.coe_one,
        one_apply_eq] at this
      norm_num at this
      exact h2 (by linear_combination -this)
  refine false_of_two_involutions h2F e₁ hcQ (hQN ▸ hbN) ?_ ?_ ?_ ?_
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_neg_one h2 hg₀
  · change orderOf (e (c g₁)) = 2
    rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq]
    exact hg₁2
  · change e g₀ * e (c g₁) = e (c g₁) * e g₀
    rw [← map_mul, ← map_mul, neg_one_comm hg₀]
  · intro h
    exact conj_signSL_ne h2 H hg₀ (e.injective h).symm

theorem false_of_field {L : Type*} [Group L] [Finite L] [Finite K] (e : SL(4, K) ≃* L)
    (h2 : (2 : K) ≠ 0) {s : MulAut L} {H : GL (Fin 4) K} (τ : K ≃+* K)
    (hs : ∀ g, s (e g) = e ((CatalogueBHigherLinearAction.slConjugation 4 K H *
      CatalogueBHigherLinearField.slFieldAut (Fin 4) K τ *
        (CatalogueBHigherLinearAction.slConjugation 4 K H)⁻¹) g))
    {Q : Subgroup L} (hQs : Q ≤ autFixed s) (hQc : IsPComponent 2 (Q.subgroupOf (autFixed s)))
    {F : Type*} [Field F] (h2F : (2 : F) ≠ 0) (e₁ : Q ⧸ pPrimeCore 2 Q ≃* SL(2, F))
    {g₀ : SL(4, K)} (hg₀ : (g₀ : Matrix (Fin 4) (Fin 4) K) = -1) (hcQ : e g₀ ∈ Q) : False := by
  have hCq : IsQuasisimple (fieldFixedSL 4 τ) := by
    rw [← range_map_fixField]
    exact LocalCores.isQuasisimple_of_mulEquiv
      (MonoidHom.ofInjective (map_fixField_injective (n := 4) τ))
      (CatalogueBGeneralLinear.specialLinear_quasisimple 4 (fixField τ) (by norm_num)
        (Or.inl (by norm_num)) (Or.inl (by norm_num)))
  have hsign : signSL K {0, 1} (by rw [pair01]; exact even_two) ∈ fieldFixedSL 4 τ := by
    rw [mem_fieldFixedSL]
    intro i j
    simp only [coe_signSL, signMat, diagonal_apply]
    split_ifs <;> simp
  exact false_of_quasisimple_fixed e h2 (σ := CatalogueBHigherLinearField.slFieldAut (Fin 4) K τ)
    (fun g => Iff.rfl) hCq hsign hs hQs hQc h2F e₁ hg₀ hcQ

theorem false_of_graphField {L : Type*} [Group L] [Finite L] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) (hKf : Nat.card K = (p ^ f) ^ 2)
    (e : SL(4, K) ≃* L) {s : MulAut L} {H : GL (Fin 4) K}
    (hs : ∀ g, s (e g) = e ((CatalogueBHigherLinearAction.slConjugation 4 K H *
      (CatalogueBHigherLinearField.slFieldAut (Fin 4) K
          (LieType.BorelTits.unitaryInvolution K p f) *
        CatalogueBGraphForm.slGraphAut 4 K) *
        (CatalogueBHigherLinearAction.slConjugation 4 K H)⁻¹) g))
    {Q : Subgroup L} (hQs : Q ≤ autFixed s) (hQc : IsPComponent 2 (Q.subgroupOf (autFixed s)))
    {F : Type*} [Field F] (h2F : (2 : F) ≠ 0) (e₁ : Q ⧸ pPrimeCore 2 Q ≃* SL(2, F))
    {g₀ : SL(4, K)} (hg₀ : (g₀ : Matrix (Fin 4) (Fin 4) K) = -1) (hcQ : e g₀ ∈ Q) : False := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K p 2).1 (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 this)
  set σ := LieType.BorelTits.unitaryInvolution K p f with hσ
  have hσσ : ∀ x, σ (σ x) = x := LieType.BorelTits.unitaryInvolution_involutive hKf
  exact false_of_quasisimple_fixed e h2
    (σ := CatalogueBHigherLinearField.slFieldAut (Fin 4) K σ * CatalogueBGraphForm.slGraphAut 4 K)
    (C := unitarySL 4 σ) (fun g => gfLift_eq_iff hσσ g)
    (isQuasisimple_unitarySL hp2 hKf (by norm_num)) (signSL_mem_unitarySL σ (by decide)) hs hQs
    hQc h2F e₁ hg₀ hcQ

end CFSG.ComponentClassification.CatFactsL4U4.BurgD
