module

public import CFSG.LargeExtraspecial.OutSix

public section

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups Pointwise

section InvTranspose

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

theorem sl_transpose_mul (A B : Matrix.SpecialLinearGroup ι R) :
    (A * B).transpose = B.transpose * A.transpose :=
  Subtype.ext (Matrix.transpose_mul A.1 B.1)

theorem sl_transpose_one : (1 : Matrix.SpecialLinearGroup ι R).transpose = 1 :=
  Subtype.ext Matrix.transpose_one

theorem sl_transpose_transpose (A : Matrix.SpecialLinearGroup ι R) :
    A.transpose.transpose = A :=
  Subtype.ext (Matrix.transpose_transpose A.1)

theorem sl_transpose_inv (A : Matrix.SpecialLinearGroup ι R) :
    A⁻¹.transpose = A.transpose⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← sl_transpose_mul, mul_inv_cancel, sl_transpose_one]

theorem sl_transpose_inv_transpose_inv (A : Matrix.SpecialLinearGroup ι R) :
    (A.transpose⁻¹).transpose⁻¹ = A := by
  rw [sl_transpose_inv, sl_transpose_transpose, inv_inv]

@[expose] def invTranspose : MulAut (Matrix.SpecialLinearGroup ι R) where
  toFun A := A.transpose⁻¹
  invFun A := A.transpose⁻¹
  left_inv := sl_transpose_inv_transpose_inv
  right_inv := sl_transpose_inv_transpose_inv
  map_mul' A B := by rw [sl_transpose_mul, mul_inv_rev]

theorem invTranspose_apply (A : Matrix.SpecialLinearGroup ι R) :
    invTranspose A = A.transpose⁻¹ := rfl

theorem invTranspose_mul_self :
    (invTranspose : MulAut (Matrix.SpecialLinearGroup ι R)) * invTranspose = 1 :=
  MulEquiv.ext fun A => sl_transpose_inv_transpose_inv A

theorem trace_coe_conj (P A : Matrix.SpecialLinearGroup ι R) :
    Matrix.trace ((P * A * P⁻¹ : Matrix.SpecialLinearGroup ι R) : Matrix ι ι R) =
      Matrix.trace (A : Matrix ι ι R) := by
  have h : ((P⁻¹ : Matrix.SpecialLinearGroup ι R) : Matrix ι ι R) * (P : Matrix ι ι R) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem trace_coe_inv_eq_of_conj_eq_invTranspose {P : Matrix.SpecialLinearGroup ι R}
    (hP : MulAut.conj P = invTranspose) (A : Matrix.SpecialLinearGroup ι R) :
    Matrix.trace ((A⁻¹ : Matrix.SpecialLinearGroup ι R) : Matrix ι ι R) =
      Matrix.trace (A : Matrix ι ι R) := by
  have h : P * A * P⁻¹ = A.transpose⁻¹ := by
    have := congrArg (fun φ : MulAut (Matrix.SpecialLinearGroup ι R) => φ A) hP
    simpa only [MulAut.conj_apply, invTranspose_apply] using this
  have h2 : Matrix.trace ((P * A * P⁻¹ : Matrix.SpecialLinearGroup ι R) : Matrix ι ι R) =
      Matrix.trace ((A.transpose⁻¹ : Matrix.SpecialLinearGroup ι R) : Matrix ι ι R) := by
    rw [h]
  rw [trace_coe_conj, ← sl_transpose_inv, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.trace_transpose] at h2
  exact h2.symm

end InvTranspose

private def testMat : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 1, 0, 0, 0;
     1, 0, 1, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

private def testMatInv : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

private theorem testMat_mul_testMatInv : testMat * testMatInv = 1 := by
  decide +kernel

private theorem trace_testMat : Matrix.trace testMat = 1 := by
  decide +kernel

private theorem trace_testMatInv : Matrix.trace testMatInv = 0 := by
  decide +kernel

private theorem zmod_two_eq_one_of_mul_eq_one {a b : ZMod 2} (h : a * b = 1) : a = 1 := by
  revert a b
  decide

private theorem zmod_two_eq_one_of_pow_six {r : ZMod 2} (h : r ^ 6 = 1) : r = 1 := by
  revert r
  decide

private theorem det_testMat : testMat.det = 1 := by
  have h := congrArg Matrix.det testMat_mul_testMatInv
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact zmod_two_eq_one_of_mul_eq_one h

private theorem det_testMatInv : testMatInv.det = 1 := by
  have h := congrArg Matrix.det testMat_mul_testMatInv
  rw [Matrix.det_mul, Matrix.det_one, mul_comm] at h
  exact zmod_two_eq_one_of_mul_eq_one h

private def testSL : SL(6, ZMod 2) := ⟨testMat, det_testMat⟩

private def testSLInv : SL(6, ZMod 2) := ⟨testMatInv, det_testMatInv⟩

private theorem testSL_inv : testSL⁻¹ = testSLInv :=
  inv_eq_of_mul_eq_one_right (Subtype.ext testMat_mul_testMatInv)

theorem invTranspose_not_mem_inner_six :
    (invTranspose : MulAut (SL(6, ZMod 2))) ∉ inner (SL(6, ZMod 2)) := by
  rintro ⟨P, hP⟩
  have h := trace_coe_inv_eq_of_conj_eq_invTranspose hP testSL
  rw [testSL_inv] at h
  change Matrix.trace testMatInv = Matrix.trace testMat at h
  rw [trace_testMat, trace_testMatInv] at h
  exact absurd h (by decide)

theorem sl_six_eq_one_of_central (A : SL(6, ZMod 2)) (h : ∀ B : SL(6, ZMod 2), B * A = A * B) :
    A = 1 := by
  obtain ⟨r, hr, hrA⟩ :=
    Matrix.SpecialLinearGroup.mem_center_iff.mp (Subgroup.mem_center_iff.mpr h)
  have hr1 : r = 1 := zmod_two_eq_one_of_pow_six (by rwa [Fintype.card_fin] at hr)
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

theorem center_sl_six_eq_bot : Subgroup.center (SL(6, ZMod 2)) = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun A hA =>
    sl_six_eq_one_of_central A (Subgroup.mem_center_iff.mp hA)

noncomputable def pslSixEquivSL : PSL(6, ZMod 2) ≃* SL(6, ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq center_sl_six_eq_bot).trans QuotientGroup.quotientBot

private theorem center_eq_bot_of_mulEquiv {G H : Type*} [Group G] [Group H] (f : G ≃* H)
    (h : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  apply f.injective
  rw [map_one]
  have hf : f g ∈ Subgroup.center H := by
    rw [← center_map_equiv f]
    exact Subgroup.mem_map_of_mem f.toMonoidHom hg
  rw [h, Subgroup.mem_bot] at hf
  exact hf

theorem center_psl_six_eq_bot : Subgroup.center (PSL(6, ZMod 2)) = ⊥ :=
  center_eq_bot_of_mulEquiv pslSixEquivSL center_sl_six_eq_bot

theorem exists_involutory_outer_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : ∃ γ : MulAut H, γ * γ = 1 ∧ γ ∉ inner H) :
    ∃ γ : MulAut G, γ * γ = 1 ∧ γ ∉ inner G := by
  obtain ⟨γ, hγ, hγi⟩ := h
  refine ⟨MulAut.congr e.symm γ, ?_, fun hmem => hγi ?_⟩
  · rw [← map_mul, hγ, map_one]
  · rw [← inner_map_congr e.symm] at hmem
    exact (Subgroup.mem_map_iff_mem (MulAut.congr e.symm).injective).mp hmem

private theorem eq_of_mem_zpowers_of_orderOf_eq_two {G : Type*} [Group G] {a b : G}
    (ha : orderOf a = 2) (hb : b ∈ zpowers a) (hb1 : b ≠ 1) : b = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← zpow_mod_orderOf, ha] at hb1 ⊢
  have hk : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hk with hk | hk
  · rw [hk, zpow_zero] at hb1
    exact absurd rfl hb1
  · rw [hk, zpow_one]

theorem exists_conj_eq_of_orderOf_eq_two {G : Type*} [Group G] [Finite G]
    (h4 : ¬ 4 ∣ Nat.card G) {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2) :
    ∃ c : G, c * a * c⁻¹ = b := by
  have hN0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have h2 : 2 ∣ Nat.card G := ha ▸ orderOf_dvd_natCard a
  have hfact : (Nat.card G).factorization 2 = 1 := by
    have h1le : 1 ≤ (Nat.card G).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN0).mp (by simpa using h2)
    have hlt : ¬ 2 ≤ (Nat.card G).factorization 2 := fun h =>
      h4 (by simpa using (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN0).mpr h)
    omega
  obtain ⟨P, hP⟩ : ∃ P : Sylow 2 G, (P : Subgroup G) = zpowers a :=
    ⟨Sylow.ofCard (zpowers a) (by rw [Nat.card_zpowers, ha, hfact, pow_one]),
      Sylow.coe_ofCard _ _⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 2 G, (Q : Subgroup G) = zpowers b :=
    ⟨Sylow.ofCard (zpowers b) (by rw [Nat.card_zpowers, hb, hfact, pow_one]),
      Sylow.coe_ofCard _ _⟩
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨c, eq_of_mem_zpowers_of_orderOf_eq_two hb ?_ ?_⟩
  · have h1 : MulAut.conj c • a ∈ MulAut.conj c • (P : Subgroup G) :=
      Subgroup.smul_mem_pointwise_smul a (MulAut.conj c) _ (by rw [hP]; exact mem_zpowers a)
    rw [← Sylow.coe_subgroup_smul, hc, hQ] at h1
    simpa [MulAut.smul_def, MulAut.conj_apply] using h1
  · intro h
    have ha1 : a = 1 := by simpa using h
    rw [ha1, orderOf_one] at ha
    omega

theorem exists_sigma_of_conjOuter_eq {X : Type*} [Group X] (X₀ : Subgroup X) [X₀.Normal]
    (hC : centralizer (X₀ : Set X) ≤ X₀) (hZ : Subgroup.center X₀ = ⊥) (hidx : X₀.index = 2)
    {x : X} (hx : x ∉ X₀) {γ : MulAut X₀} (hγ : γ * γ = 1)
    (hxγ : conjOuter X₀ x = (QuotientGroup.mk γ : Outer X₀)) :
    ∃ σ : X, σ * σ = 1 ∧ X₀ ⊔ zpowers σ = ⊤ := by
  obtain ⟨g, hg⟩ := QuotientGroup.eq.mp hxγ
  set σ : X := x * (g : X) with hσdef
  have hσ : (MulAut.conjNormal σ : MulAut X₀) = γ := by
    rw [hσdef, map_mul, MulAut.conjNormal_val, hg, mul_inv_cancel_left]
  have hcent : σ * σ ∈ centralizer (X₀ : Set X) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h1 : (MulAut.conjNormal (σ * σ) : MulAut X₀) = 1 := by rw [map_mul, hσ, hγ]
    have h2 : ((MulAut.conjNormal (σ * σ) ⟨y, hy⟩ : X₀) : X) = y := by rw [h1]; rfl
    rw [MulAut.conjNormal_apply] at h2
    calc y * (σ * σ) = (σ * σ * y * (σ * σ)⁻¹) * (σ * σ) := by rw [h2]
      _ = σ * σ * y := by group
  have hsq : σ * σ = 1 := by
    have hz : (⟨σ * σ, hC hcent⟩ : X₀) ∈ Subgroup.center X₀ :=
      Subgroup.mem_center_iff.mpr fun y => Subtype.ext (mem_centralizer_iff.mp hcent y y.2)
    rw [hZ, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  have hσX₀ : σ ∉ X₀ := fun hmem => hx ((Subgroup.mul_mem_cancel_right X₀ g.2).mp hmem)
  refine ⟨σ, hsq, ?_⟩
  have hle : X₀ ≤ X₀ ⊔ zpowers σ := le_sup_left
  have hσK : σ ∈ X₀ ⊔ zpowers σ := Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)
  have hdvd : (X₀ ⊔ zpowers σ).index ∣ X₀.index := Subgroup.index_dvd_of_le hle
  rw [hidx] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hK1 | hK2
  · exact Subgroup.index_eq_one.mp hK1
  · exfalso
    have hrel := Subgroup.relIndex_mul_index hle
    rw [hK2, hidx] at hrel
    have hone : X₀.relIndex (X₀ ⊔ zpowers σ) = 1 := by omega
    exact hσX₀ (Subgroup.relIndex_eq_one.mp hone hσK)

theorem exists_sigma_of_outer_involution {X Y : Type*} [Group X] [Group Y]
    (X₀ : Subgroup X) [X₀.Normal] (e : X₀ ≃* Y) (hC : centralizer (X₀ : Set X) ≤ X₀)
    (hZ : Subgroup.center Y = ⊥) (hOut : ¬ 4 ∣ Nat.card (Outer Y))
    (τ : MulAut Y) (hτ : τ * τ = 1) (hτi : τ ∉ inner Y) (hidx : X₀.index ∣ 2) :
    ∃ σ : X, σ * σ = 1 ∧ X₀ ⊔ zpowers σ = ⊤ := by
  rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h1 | h2
  · refine ⟨1, mul_one 1, ?_⟩
    rw [Subgroup.index_eq_one.mp h1, top_sup_eq]
  have hZ' : Subgroup.center X₀ = ⊥ := center_eq_bot_of_mulEquiv e hZ
  obtain ⟨τ', hτ', hτi'⟩ := exists_involutory_outer_of_mulEquiv e ⟨τ, hτ, hτi⟩
  rw [← Nat.card_congr (equivalence e).toEquiv] at hOut
  have hfin : Finite (Outer X₀) :=
    Nat.finite_of_card_ne_zero fun h => hOut (h ▸ dvd_zero 4)
  obtain ⟨x, hx⟩ : ∃ x : X, x ∉ X₀ := by
    by_contra hcon
    rw [not_exists] at hcon
    have htop : X₀ = ⊤ := (Subgroup.eq_top_iff' X₀).mpr fun a => not_not.mp (hcon a)
    rw [htop, Subgroup.index_top] at h2
    omega
  have hxx : x * x ∈ X₀ := by
    have := Subgroup.pow_index_mem X₀ x
    rwa [h2, pow_two] at this
  have hx1 : conjOuter X₀ x ≠ 1 := by
    intro h
    have hmem : x ∈ (conjOuter X₀).ker := MonoidHom.mem_ker.mpr h
    rw [ker_conjOuter X₀ hC] at hmem
    exact hx hmem
  have hxsq : conjOuter X₀ x * conjOuter X₀ x = 1 := by
    rw [← map_mul]
    apply MonoidHom.mem_ker.mp
    rw [ker_conjOuter X₀ hC]
    exact hxx
  have hq1 : (QuotientGroup.mk τ' : Outer X₀) ≠ 1 := fun h =>
    hτi' ((QuotientGroup.eq_one_iff τ').mp h)
  have hqsq : (QuotientGroup.mk τ' : Outer X₀) * QuotientGroup.mk τ' = 1 := by
    rw [← QuotientGroup.mk_mul, hτ']
    rfl
  obtain ⟨c, hc⟩ := exists_conj_eq_of_orderOf_eq_two hOut
    (orderOf_eq_prime (by rwa [pow_two]) hq1) (orderOf_eq_prime (by rwa [pow_two]) hx1)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
  refine exists_sigma_of_conjOuter_eq X₀ hC hZ' h2 hx (γ := a * τ' * a⁻¹) ?_ ?_
  · calc a * τ' * a⁻¹ * (a * τ' * a⁻¹) = a * (τ' * τ') * a⁻¹ := by group
      _ = 1 := by rw [hτ', mul_one, mul_inv_cancel]
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hc.symm

theorem exists_sigma_of_psl_six {X : Type*} [Group X] [Finite X] (X₀ : Subgroup X) [X₀.Normal]
    (e : X₀ ≃* PSL(6, ZMod 2)) (hC : centralizer (X₀ : Set X) ≤ X₀) :
    ∃ σ : X, σ * σ = 1 ∧ X₀ ⊔ Subgroup.zpowers σ = ⊤ := by
  obtain ⟨τ, hτ, hτi⟩ := exists_involutory_outer_of_mulEquiv pslSixEquivSL
    ⟨invTranspose, invTranspose_mul_self, invTranspose_not_mem_inner_six⟩
  have hOut : Nat.card (Outer PSL(6, ZMod 2)) ∣ 2 := card_outer_psl_two_dvd (by norm_num)
  exact exists_sigma_of_outer_involution X₀ e hC center_psl_six_eq_bot
    (fun h => absurd (h.trans hOut) (by norm_num)) τ hτ hτi
    (index_dvd_two_of_mulEquiv_psl (by norm_num) X₀ e hC)

end CFSG.LargeExtraspecial.S14
