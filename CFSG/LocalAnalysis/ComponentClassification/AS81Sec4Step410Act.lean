module

public import CFSG.GH74.KGroups.Cover
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveOddCore
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter
open Matrix

section Act

variable {G : Type} [Group G] {A : Subgroup G} {P : Type*} [Group P]

@[expose] noncomputable def quotCenterEquiv (φ : ↥A →* P) (hφ : Function.Surjective φ)
    (hker : φ.ker = center ↥A) : ↥A ⧸ center ↥A ≃* P :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

theorem quotCenterEquiv_mk (φ : ↥A →* P) (hφ : Function.Surjective φ)
    (hker : φ.ker = center ↥A) (a : ↥A) :
    quotCenterEquiv φ hφ hker (QuotientGroup.mk a) = φ a :=
  rfl

@[expose] noncomputable def quotCenterAct (φ : ↥A →* P) (hφ : Function.Surjective φ)
    (hker : φ.ker = center ↥A) : ↥(normalizer (A : Set G)) →* MulAut P :=
  (MulAut.congr (quotCenterEquiv φ hφ hker)).toMonoidHom.comp
    (GH74.KGroups.inducedHom.comp (RankTwoAltFive.conjActHom le_rfl))

theorem quotCenterAct_apply (φ : ↥A →* P) (hφ : Function.Surjective φ) (hker : φ.ker = center ↥A)
    (n : ↥(normalizer (A : Set G))) (a : ↥A) :
    quotCenterAct φ hφ hker n (φ a) =
      φ ⟨n * a * (n : G)⁻¹, (mem_normalizer_iff.mp n.2 a).mp a.2⟩ := by
  have h1 : (quotCenterEquiv φ hφ hker).symm (φ a) = QuotientGroup.mk a := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [quotCenterAct, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply]
  rw [h1, GH74.KGroups.inducedHom_mk, quotCenterEquiv_mk]
  congr 1

theorem quotCenterAct_eq_one_iff (φ : ↥A →* P) (hφ : Function.Surjective φ)
    (hker : φ.ker = center ↥A) (hA : commutator ↥A = ⊤) (n : ↥(normalizer (A : Set G))) :
    quotCenterAct φ hφ hker n = 1 ↔ (n : G) ∈ centralizer (A : Set G) := by
  have hperf : Group.IsPerfect ↥A := ⟨hA⟩
  constructor
  · intro h
    have h1 : GH74.KGroups.inducedHom (RankTwoAltFive.conjActHom le_rfl n) = 1 :=
      (MulAut.congr (quotCenterEquiv φ hφ hker)).injective (by rw [map_one]; exact h)
    have h2 : RankTwoAltFive.conjActHom le_rfl n = 1 :=
      GH74.KGroups.inducedHom_injective hperf (by rw [h1, map_one])
    have h3 : n ∈ (RankTwoAltFive.conjActHom (le_refl (normalizer (A : Set G)))).ker := h2
    rwa [RankTwoAltFive.ker_conjActHom, mem_subgroupOf] at h3
  · intro h
    have h3 : n ∈ (RankTwoAltFive.conjActHom (le_refl (normalizer (A : Set G)))).ker := by
      rw [RankTwoAltFive.ker_conjActHom, mem_subgroupOf]
      exact h
    have h2 : RankTwoAltFive.conjActHom le_rfl n = 1 := h3
    simp only [quotCenterAct, MonoidHom.comp_apply, h2, map_one]

theorem quotCenterAct_of_mem (φ : ↥A →* P) (hφ : Function.Surjective φ) (hker : φ.ker = center ↥A)
    (a : ↥A) : quotCenterAct φ hφ hker ⟨a, le_normalizer a.2⟩ = MulAut.conj (φ a) := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨b, rfl⟩ := hφ x
  rw [quotCenterAct_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

end Act

namespace L34Out

theorem oneOne_mul_self :
    ((Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 2)) :
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) *
        (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1) = 1 := by
  decide

theorem eq_one_of_pow_coprime {M : Type*} [Monoid M] {x : M} {m n : ℕ}
    (h : Nat.Coprime m n) (hm : x ^ m = 1) (hn : x ^ n = 1) : x = 1 := by
  have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one hn)
  rw [h.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

section L34

variable {k : Type*} [Field k] {σ : k ≃+* k}

abbrev OutL34 (k : Type*) [Field k] : Type _ :=
  kˣ ⋊[inversionAction kˣ] (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))

variable {Ψ : MulAut (projectiveSL 3 k) →* OutL34 k}

theorem psi_beta (hΨ : ∀ (A : GL (Fin 3) k) (a b : ZMod 2), Ψ (nf σ A a b) =
      ⟨GeneralLinearGroup.det A, (Multiplicative.ofAdd a, Multiplicative.ofAdd b)⟩) :
    Ψ (fieldAut 3 k σ * dualAut 3 k) =
      ⟨1, (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 2))⟩ := by
  have e : fieldAut 3 k σ * dualAut 3 k = nf σ 1 1 1 := by simp [nf, val_one_two]
  rw [e, hΨ, map_one]

theorem psi_diag (hΨ : ∀ (A : GL (Fin 3) k) (a b : ZMod 2), Ψ (nf σ A a b) =
      ⟨GeneralLinearGroup.det A, (Multiplicative.ofAdd a, Multiplicative.ofAdd b)⟩) (μ : kˣ) :
    Ψ (conjAut 3 k (diagGL μ)) = ⟨μ, 1⟩ := by
  rw [← nf_zero_zero σ, hΨ, det_diagGL]
  rfl

theorem conjAut_diagGL_mul_beta (hσ : ∀ a, σ a = a ^ 2) (hk : Nat.card k = 4) (μ : kˣ) :
    conjAut 3 k (diagGL μ) * (fieldAut 3 k σ * dualAut 3 k) =
      (fieldAut 3 k σ * dualAut 3 k) * conjAut 3 k (diagGL μ) := by
  have hff := fieldAut_sigma_mul_self hσ hk
  have e1 : fieldAut 3 k σ * dualAut 3 k = nf σ 1 1 1 := by simp [nf, val_one_two]
  rw [e1, ← nf_zero_zero σ, nf_mul σ hff, nf_mul σ hff]
  simp [twistF, twistD, inverseTranspose_diagGL, map_sigma_diagGL hσ hk]

theorem exists_psi_eq_beta (hk : Nat.card k = 4)
    (hΨ : ∀ (A : GL (Fin 3) k) (a b : ZMod 2), Ψ (nf σ A a b) =
      ⟨GeneralLinearGroup.det A, (Multiplicative.ofAdd a, Multiplicative.ofAdd b)⟩)
    {W : Type*} [Group W] [Finite W] (hW : IsPGroup 2 W) (f : W →* MulAut (projectiveSL 3 k))
    (hcard : 4 * Nat.card (Ψ.comp f).ker ≤ Nat.card W) :
    ∃ w : W, Ψ (f w) = Ψ (fieldAut 3 k σ * dualAut 3 k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  set g := Ψ.comp f with hg
  set ρ := (SemidirectProduct.rightHom :
    OutL34 k →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) with hρ
  have hker : (ρ.comp g).ker = g.ker := by
    refine le_antisymm (fun w hw => ?_) (fun w hw => by
      rw [MonoidHom.mem_ker] at hw ⊢
      rw [MonoidHom.comp_apply, hw, map_one])
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hw
    rw [MonoidHom.mem_ker]
    obtain ⟨n, hn⟩ := hW w
    have hgw : g w = SemidirectProduct.inl (g w).left := by
      refine SemidirectProduct.ext rfl ?_
      rw [SemidirectProduct.right_inl]
      exact hw
    have h1 : (g w).left ^ 2 ^ n = 1 := by
      have h2 : g w ^ 2 ^ n = 1 := by rw [← map_pow, hn, map_one]
      rw [hgw, ← map_pow, ← map_one SemidirectProduct.inl] at h2
      exact SemidirectProduct.inl_injective h2
    have h3 : (g w).left ^ 3 = 1 := units_pow_three hk _
    have h4 : (g w).left = 1 := by
      have hco : Nat.Coprime (2 ^ n) 3 := Nat.Coprime.pow_left _ (by norm_num)
      exact eq_one_of_pow_coprime hco h1 h3
    rw [hgw, h4, map_one]
  have hrange : (ρ.comp g).range = ⊤ := by
    have h1 := card_eq_card_quotient_mul_card_subgroup (ρ.comp g).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (ρ.comp g)).toEquiv, hker] at h1
    have h2 : 4 ≤ Nat.card (ρ.comp g).range := by
      have hk0 : 0 < Nat.card g.ker := Nat.card_pos
      rw [h1] at hcard
      exact Nat.le_of_mul_le_mul_right (by linarith) hk0
    have h3 : Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = 4 := by
      rw [Nat.card_prod]
      simp [Nat.card_eq_fintype_card]
    exact Subgroup.eq_top_of_le_card _ (by rw [h3]; exact h2)
  obtain ⟨w, hw⟩ := (MonoidHom.range_eq_top.mp hrange)
    (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 2))
  refine ⟨w, ?_⟩
  rw [psi_beta hΨ]
  obtain ⟨n, hn⟩ := hW w
  have hn' : g w ^ 2 ^ n = 1 := by rw [← map_pow, hn, map_one]
  have hgw : g w = ⟨(g w).left,
      (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 2))⟩ :=
    SemidirectProduct.ext rfl hw
  have hsq : g w * g w = SemidirectProduct.inl ((g w).left * (g w).left) := by
    rw [hgw]
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.mul_left, SemidirectProduct.left_inl, inversionAction_apply]
      simp [show (1 + 1 : ZMod 2) = 0 from rfl]
    · rw [SemidirectProduct.mul_right, SemidirectProduct.right_inl]
      exact oneOne_mul_self
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, pow_one, hgw] at hn'
    have h2 := congrArg (fun x : OutL34 k => Multiplicative.toAdd x.right.1) hn'
    simp at h2
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have h1 : ((g w).left * (g w).left) ^ 2 ^ m = 1 := by
    rw [pow_succ', pow_mul, sq, hsq, ← map_pow, ← map_one SemidirectProduct.inl] at hn'
    exact SemidirectProduct.inl_injective hn'
  have h3 : ((g w).left * (g w).left) ^ 3 = 1 := units_pow_three hk _
  have h4 : (g w).left * (g w).left = 1 := by
    have hco : Nat.Coprime (2 ^ m) 3 := Nat.Coprime.pow_left _ (by norm_num)
    exact eq_one_of_pow_coprime hco h1 h3
  have h5 : (g w).left = 1 := by
    have h6 := units_pow_three hk (g w).left
    calc (g w).left = (g w).left ^ 3 * ((g w).left * (g w).left)⁻¹ := by group
      _ = 1 := by rw [h6, h4]; group
  change g w = _
  rw [hgw, h5]

theorem exists_eq_conj_mul_diag (hσ : ∀ a, σ a = a ^ 2) (hk : Nat.card k = 4)
    (hΨ : ∀ (A : GL (Fin 3) k) (a b : ZMod 2), Ψ (nf σ A a b) =
      ⟨GeneralLinearGroup.det A, (Multiplicative.ofAdd a, Multiplicative.ofAdd b)⟩)
    {γ : MulAut (projectiveSL 3 k)} {j : ℕ} (hγ : γ ^ 3 ^ j = 1) :
    ∃ (a : projectiveSL 3 k) (μ : kˣ), γ = MulAut.conj a * conjAut 3 k (diagGL μ) := by
  have hright : (Ψ γ).right = 1 := by
    have h1 : (Ψ γ).right ^ 3 ^ j = 1 := by
      rw [← SemidirectProduct.rightHom_eq_right, ← map_pow, ← map_pow, hγ, map_one, map_one]
    have h2 : (Ψ γ).right ^ 2 = 1 := by
      obtain ⟨⟨x⟩, ⟨y⟩⟩ := (Ψ γ).right
      refine Prod.ext ?_ ?_ <;> show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0 <;>
        congr 1 <;> revert x y <;> decide
    have hco : Nat.Coprime (3 ^ j) 2 := Nat.Coprime.pow_left _ (by norm_num)
    exact eq_one_of_pow_coprime hco h1 h2
  refine ⟨?_, (Ψ γ).left, ?_⟩
  · exact Classical.choose (show γ * (conjAut 3 k (diagGL (Ψ γ).left))⁻¹ ∈
        (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range by
      rw [← ker_eq_range_conj hσ hk hΨ, MonoidHom.mem_ker, map_mul, map_inv, psi_diag hΨ,
        mul_inv_eq_one]
      exact SemidirectProduct.ext rfl hright)
  · have h := Classical.choose_spec (show γ * (conjAut 3 k (diagGL (Ψ γ).left))⁻¹ ∈
        (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range by
      rw [← ker_eq_range_conj hσ hk hΨ, MonoidHom.mem_ker, map_mul, map_inv, psi_diag hΨ,
        mul_inv_eq_one]
      exact SemidirectProduct.ext rfl hright)
    rw [h, inv_mul_cancel_right]

theorem beta_ne_conj (hσ : ∀ a, σ a = a ^ 2) (hk : Nat.card k = 4)
    (hΨ : ∀ (A : GL (Fin 3) k) (a b : ZMod 2), Ψ (nf σ A a b) =
      ⟨GeneralLinearGroup.det A, (Multiplicative.ofAdd a, Multiplicative.ofAdd b)⟩)
    (a : projectiveSL 3 k) : MulAut.conj a ≠ fieldAut 3 k σ * dualAut 3 k := by
  intro h
  have h1 : fieldAut 3 k σ * dualAut 3 k ∈ Ψ.ker := by
    rw [ker_eq_range_conj hσ hk hΨ]
    exact ⟨a, h⟩
  rw [MonoidHom.mem_ker, psi_beta hΨ] at h1
  have h2 := congrArg (fun x : OutL34 k => Multiplicative.toAdd x.right.1) h1
  simp at h2

end L34

end L34Out

end CFSG.ComponentClassification.AS81
