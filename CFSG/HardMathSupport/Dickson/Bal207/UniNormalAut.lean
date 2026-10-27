module

public import CFSG.HardMathSupport.Dickson.Bal207.UniModel
public import CFSG.HardMathSupport.Dickson.Bal207.UniNormal
public import CFSG.HardMathSupport.Dickson.Bal207.UniLift

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Uni

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

theorem uni_conj_inl_left {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}
    (x : N ⋊[φ] G) (m : N) :
    (x * SemidirectProduct.inl m * x⁻¹).left = x.left * φ x.right m * x.left⁻¹ := by
  rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.inv_left,
    SemidirectProduct.mul_right, SemidirectProduct.left_inl, SemidirectProduct.right_inl, mul_one,
    ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem uni_conj_inl_eq {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}
    (x : N ⋊[φ] G) (m : N) :
    x * SemidirectProduct.inl m * x⁻¹ =
      SemidirectProduct.inl (x * SemidirectProduct.inl m * x⁻¹).left := by
  ext
  · rfl
  · simp

section Trans

variable {X : Type} [Group X] {K : Subgroup X} {S : Type} [Group S]

theorem uniAut_trans (e : (↥K ⧸ Subgroup.center ↥K) ≃* S) (β : MulAut S)
    (g : ↥(Subgroup.normalizer (K : Set X))) : uniAut (e.trans β) g = β * uniAut e g * β⁻¹ :=
  MulEquiv.ext fun _ => rfl

end Trans

section Gamma

variable {f n : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

theorem uni_isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) F) :=
  CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one

theorem uni_det_glAut (σ : F ≃+* F) (g : GL (Fin n) F) :
    ((glAut σ g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det =
      σ ((g : Matrix (Fin n) (Fin n) F).det) := by
  rw [coe_glAut, show (g : Matrix (Fin n) (Fin n) F).map σ =
    (σ : F →+* F).mapMatrix (g : Matrix (Fin n) (Fin n) F) from rfl, ← RingHom.map_det]
  rfl

@[expose] def uniGammaSU (n : ℕ) : Subgroup (UniGamma h n) where
  carrier := {x | ((x.left : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1}
  mul_mem' {x y} hx hy := by
    have hx' : ((x.left : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := hx
    have hy' : ((y.left : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := hy
    show (((x * y).left : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1
    rw [SemidirectProduct.mul_left, Subgroup.coe_mul, Units.val_mul, det_mul, hx', one_mul,
      coe_primeFormFieldU, uni_det_glAut, hy', map_one]
  one_mem' := by
    show (((1 : UniGamma h n).left : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1
    rw [SemidirectProduct.one_left, Subgroup.coe_one, Units.val_one, det_one]
  inv_mem' {x} hx := by
    have hx' : ((x.left : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := hx
    have hinv : (((x.left⁻¹ : primeFormUnitary h _) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F).det = 1 := by
      have e := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F).det)
        (mul_inv_cancel (x.left : GL (Fin n) F))
      simp only [Units.val_mul, det_mul, hx', one_mul, Units.val_one, det_one] at e
      rwa [Subgroup.coe_inv]
    show (((x⁻¹).left : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1
    rw [SemidirectProduct.inv_left, coe_primeFormFieldU, uni_det_glAut, hinv, map_one]

theorem uni_psi_inl (A : primeFormUnitary h (oneGram F n)) :
    primeFormPsi h uni_isPrimeFormGram_one (SemidirectProduct.inl A) =
      primeFormConjHom h (oneGram F n) A := by
  rw [show (SemidirectProduct.inl A : UniGamma h n) = ⟨A, 1⟩ from rfl, primeFormPsi_apply,
    map_one, mul_one]

variable {h}

theorem uni_psi_eq_one (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n) {x : UniGamma h n}
    (hx : x ∈ uniGammaSU h n) (h1 : primeFormPsi h uni_isPrimeFormGram_one x = 1) : x = 1 := by
  obtain ⟨hr, c, hcN, hc⟩ := (primeFormPsi_eq_one_iff h uni_isPrimeFormGram_one hn x).1 h1
  have hdet : ((x.left : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := hx
  have hcn : (c : F) ^ n = 1 := by
    have e := congrArg Units.val (GeneralLinearGroup.det_scalar (n := Fin n) c)
    rw [Units.val_pow_eq_pow_val, Fintype.card_fin] at e
    rw [← e, ← hdet, hc]
    rfl
  have hc1 := uni_units_eq_one h hf h3 hcn hcN
  refine SemidirectProduct.ext (Subtype.ext ?_) hr
  rw [hc, hc1, map_one]
  rfl

theorem uni_psi_injOn (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n) {x y : UniGamma h n}
    (hx : x ∈ uniGammaSU h n) (hy : y ∈ uniGammaSU h n)
    (hxy : primeFormPsi h uni_isPrimeFormGram_one x = primeFormPsi h uni_isPrimeFormGram_one y) :
    x = y := by
  have h1 := uni_psi_eq_one hf hn h3 (mul_mem (inv_mem hx) hy)
    (by rw [map_mul, map_inv, hxy, inv_mul_cancel])
  exact inv_mul_eq_one.1 h1

theorem uni_exists_lift (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n)
    (α : MulAut (primeFormP h (oneGram F n))) :
    ∃ x ∈ uniGammaSU h n, primeFormPsi h uni_isPrimeFormGram_one x = α := by
  obtain ⟨⟨A, σ⟩, hx⟩ := primeFormPsi_surjective h uni_isPrimeFormGram_one hn (uni_ne_three h3) α
  obtain ⟨s, hs⟩ := uni_exists_conjHom_eq h hf hn h3 A
  refine ⟨⟨⟨s, s.2.1⟩, σ⟩, s.2.2, ?_⟩
  rw [primeFormPsi_apply, ← hs, ← primeFormPsi_apply, hx]

variable (h)

@[expose] noncomputable def uniGammaEquiv (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n) :
    ↥(uniGammaSU h n) ≃* MulAut (primeFormP h (oneGram F n)) :=
  MulEquiv.ofBijective ((primeFormPsi h uni_isPrimeFormGram_one).comp (uniGammaSU h n).subtype)
    ⟨fun x y hxy => Subtype.ext (uni_psi_injOn hf hn h3 x.2 y.2 hxy), fun α => by
      obtain ⟨x, hx, hxα⟩ := uni_exists_lift hf hn h3 α
      exact ⟨⟨x, hx⟩, hxα⟩⟩

@[expose] noncomputable def uniLift (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n) :
    MulAut (primeFormP h (oneGram F n)) →* UniGamma h n :=
  (uniGammaSU h n).subtype.comp (uniGammaEquiv h hf hn h3).symm.toMonoidHom

theorem psi_uniLift (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n)
    (α : MulAut (primeFormP h (oneGram F n))) :
    primeFormPsi h uni_isPrimeFormGram_one (uniLift h hf hn h3 α) = α :=
  (uniGammaEquiv h hf hn h3).apply_symm_apply α

theorem uni_aut_normal_form (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n)
    (Ω : Set (MulAut (primeFormP h (oneGram F n))))
    (hΩc : ∀ α ∈ Ω, ∀ β ∈ Ω, α * β = β * α) (hΩ3 : ∀ α ∈ Ω, α ^ 3 = 1) :
    ∃ (P : primeFormUnitary h (oneGram F n)) (σ : F ≃+* F), σ ^ 3 = 1 ∧ ∀ α ∈ Ω,
      ∃ D : primeFormUnitary h (oneGram F n),
        ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag ∧ D ^ 3 = 1 ∧ ∃ k : ℕ,
          (primeFormConjHom h (oneGram F n) P)⁻¹ * α * primeFormConjHom h (oneGram F n) P =
            primeFormPsi h uni_isPrimeFormGram_one
              (SemidirectProduct.inl D * SemidirectProduct.inr (σ ^ k)) := by
  obtain ⟨P, σ, hσ, hP⟩ := uni_normal_form_mat h (uni_three_dvd hf) (uniLift h hf hn h3 '' Ω)
    (by
      rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
      rw [← map_mul, ← map_mul, hΩc α hα β hβ])
    (by
      rintro _ ⟨α, hα, rfl⟩
      rw [← map_pow, hΩ3 α hα, map_one])
  refine ⟨P, σ, hσ, fun α hα => ?_⟩
  obtain ⟨D, hD, hD3, k, hk⟩ := hP _ ⟨α, hα, rfl⟩
  refine ⟨D, hD, hD3, k, ?_⟩
  have e := congrArg (primeFormPsi h uni_isPrimeFormGram_one) hk
  rwa [map_mul, map_mul, map_inv, psi_uniLift, uni_psi_inl] at e

theorem uni_frame {X : Type} [Group X] {K B : Subgroup X} (hB : IsSCp 3 ⊤ B)
    (hBK : B ≤ Subgroup.normalizer (K : Set X)) (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n)
    (h3 : ¬ 3 ∣ n) (e : (↥K ⧸ Subgroup.center ↥K) ≃* primeFormP h (oneGram F n)) :
    ∃ (e' : (↥K ⧸ Subgroup.center ↥K) ≃* primeFormP h (oneGram F n)) (σ : F ≃+* F), σ ^ 3 = 1 ∧
      ∀ (b : X) (hb : b ∈ B), ∃ D : primeFormUnitary h (oneGram F n),
        ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag ∧ D ^ 3 = 1 ∧ ∃ k : ℕ,
          uniAut e' ⟨b, hBK hb⟩ = primeFormPsi h uni_isPrimeFormGram_one
            (SemidirectProduct.inl D * SemidirectProduct.inr (σ ^ k)) := by
  have hc : ∀ α ∈ Set.range fun b : ↥B => uniAut e ⟨b, hBK b.2⟩,
      ∀ β ∈ Set.range fun b : ↥B => uniAut e ⟨b, hBK b.2⟩, α * β = β * α := by
    rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have hbc : (b : X) * c = c * b := congrArg Subtype.val (hB.2.1.1.is_comm.comm b c)
    exact Subtype.ext hbc
  have h3' : ∀ α ∈ Set.range fun b : ↥B => uniAut e ⟨b, hBK b.2⟩, α ^ 3 = 1 := by
    rintro _ ⟨b, rfl⟩
    have h1 : (⟨(b : X), hBK b.2⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hB.2.1.2 b b.2)
    rw [← map_pow, h1, map_one]
  obtain ⟨P, σ, hσ, hP⟩ := uni_aut_normal_form h hf hn h3 _ hc h3'
  refine ⟨e.trans (primeFormConjHom h (oneGram F n) P)⁻¹, σ, hσ, fun b hb => ?_⟩
  obtain ⟨D, hD, hD3, k, hk⟩ := hP _ ⟨⟨b, hb⟩, rfl⟩
  refine ⟨D, hD, hD3, k, ?_⟩
  rw [uniAut_trans, inv_inv]
  exact hk

end Gamma

section Theta

variable {f n : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

theorem uni_conj_injective (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n) :
    Function.Injective (MulAut.conj : primeFormP h (oneGram F n) →*
      MulAut (primeFormP h (oneGram F n))) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  have hc : s ∈ Subgroup.center (primeFormP h (oneGram F n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have e := congrArg (fun φ : MulAut (primeFormP h (oneGram F n)) => φ g) hs
    simp only [MulAut.conj_apply, MulAut.one_apply] at e
    calc g * s = s * g * s⁻¹ * s := by rw [e]
      _ = s * g := by group
  rw [uni_center_eq_bot h hn h3] at hc
  exact Subgroup.mem_bot.1 hc

theorem uni_conjHom_mem_range (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n)
    (A : primeFormUnitary h (oneGram F n)) :
    primeFormConjHom h (oneGram F n) A ∈
      (MulAut.conj : primeFormP h (oneGram F n) →* MulAut (primeFormP h (oneGram F n))).range := by
  obtain ⟨s, hs⟩ := uni_exists_conjHom_eq h hf hn h3 A
  exact ⟨(s : primeFormP h (oneGram F n)), by rw [hs, primeFormConjHom_eq_conj]⟩

@[expose] noncomputable def uniTheta (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n) :
    primeFormUnitary h (oneGram F n) →* primeFormP h (oneGram F n) :=
  (MonoidHom.ofInjective (uni_conj_injective h hn h3)).symm.toMonoidHom.comp
    ((primeFormConjHom h (oneGram F n)).codRestrict _ (uni_conjHom_mem_range h hf hn h3))

variable (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n)

theorem conj_uniTheta (A : primeFormUnitary h (oneGram F n)) :
    MulAut.conj (uniTheta h hf hn h3 A) = primeFormConjHom h (oneGram F n) A := by
  have e := MonoidHom.ofInjective_apply (uni_conj_injective h hn h3)
    (x := (MonoidHom.ofInjective (uni_conj_injective h hn h3)).symm
      ⟨primeFormConjHom h (oneGram F n) A, uni_conjHom_mem_range h hf hn h3 A⟩)
  rw [MulEquiv.apply_symm_apply] at e
  exact e.symm

theorem uniTheta_eq_of_conj {A : primeFormUnitary h (oneGram F n)}
    {s : primeFormP h (oneGram F n)} (hs : MulAut.conj s = primeFormConjHom h (oneGram F n) A) :
    uniTheta h hf hn h3 A = s :=
  uni_conj_injective h hn h3 (by rw [conj_uniTheta, hs])

theorem uniTheta_gramSU (g : gramSU h (oneGram F n)) :
    uniTheta h hf hn h3 ⟨g, g.2.1⟩ = (g : primeFormP h (oneGram F n)) :=
  uniTheta_eq_of_conj h hf hn h3 (primeFormConjHom_eq_conj h _ g).symm

theorem uniTheta_psi (x : UniGamma h n) (A : primeFormUnitary h (oneGram F n)) :
    primeFormPsi h uni_isPrimeFormGram_one x (uniTheta h hf hn h3 A) =
      uniTheta h hf hn h3 (x * SemidirectProduct.inl A * x⁻¹).left := by
  symm
  apply uniTheta_eq_of_conj
  have e1 : MulAut.conj (primeFormPsi h uni_isPrimeFormGram_one x (uniTheta h hf hn h3 A)) =
      primeFormPsi h uni_isPrimeFormGram_one x * MulAut.conj (uniTheta h hf hn h3 A) *
        (primeFormPsi h uni_isPrimeFormGram_one x)⁻¹ := by
    ext g
    simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
      MulEquiv.apply_symm_apply]
  have e2 : primeFormPsi h uni_isPrimeFormGram_one x * primeFormConjHom h (oneGram F n) A *
      (primeFormPsi h uni_isPrimeFormGram_one x)⁻¹ =
        primeFormPsi h uni_isPrimeFormGram_one (x * SemidirectProduct.inl A * x⁻¹) := by
    rw [map_mul, map_mul, map_inv, uni_psi_inl]
  rw [e1, conj_uniTheta, e2]
  conv_lhs => rw [uni_conj_inl_eq x A]
  rw [uni_psi_inl]

end Theta

end CFSG.HardMathSupport.Dickson.Bal207.Uni

end
