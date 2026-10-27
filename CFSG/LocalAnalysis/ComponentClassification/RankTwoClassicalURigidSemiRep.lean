module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidAutInv
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidSemi

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {K : Type} [Field K] [CharP K 2] {ε f : ℕ} (h : UnitaryFieldData 2 f K)
  {R : Matrix (Fin (2 * 1 + ε)) (HypIndex 1 ε) K} (hR : IsHypTransport h R)

omit [CharP K 2] in
theorem exists_semi_of_psiU (hε : 2 ≤ ε)
    {α : MulAut (StatedProj (StatedSU (2 + ε) (2 ^ f) K))} {δ : MulAut (stabE (ε := ε) h)}
    (hαδ : ∀ g, psiU h hR (δ g) = α (psiU h hR g)) :
    ∃ (τ : K ≃+* K) (Z Z' : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K), Z * Z' = 1 ∧ Z' * Z = 1 ∧
      ∀ g, ∃ c : Kˣ, smat h (δ g) = (c : K) • (Z * (smat h g).map τ * Z') := by
  obtain ⟨τ, A₁, -, hA₁⟩ := exists_unitary_semilinear_statedProj h (n := 2 + ε) (by omega)
    (fun h' => absurd h'.1 (by omega)) α
  have hRR : R * transportInv h R = 1 := mul_transportInv hR
  have hRR' : transportInv h R * R = 1 := transportInv_mul hR
  have hτRR : R.map τ * (transportInv h R).map τ = 1 := by
    rw [← Matrix.map_mul, hRR, Matrix.map_one _ (map_zero τ) (map_one τ)]
  have hτRR' : (transportInv h R).map τ * R.map τ = 1 := by
    rw [← Matrix.map_mul, hRR', Matrix.map_one _ (map_zero τ) (map_one τ)]
  refine ⟨τ, transportInv h R * A₁.val * R.map τ,
    (transportInv h R).map τ * (A₁⁻¹ : GL (Fin (2 + ε)) K).val * R, ?_, ?_, fun g => ?_⟩
  · calc transportInv h R * A₁.val * R.map τ *
          ((transportInv h R).map τ * (A₁⁻¹ : GL (Fin (2 + ε)) K).val * R) =
        transportInv h R * A₁.val * (R.map τ * (transportInv h R).map τ) *
          (A₁⁻¹ : GL (Fin (2 + ε)) K).val * R := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hτRR, Matrix.mul_one, Matrix.mul_assoc (transportInv h R), ← Units.val_mul,
          mul_inv_cancel, Units.val_one, Matrix.mul_one, hRR']
  · calc (transportInv h R).map τ * (A₁⁻¹ : GL (Fin (2 + ε)) K).val * R *
          (transportInv h R * A₁.val * R.map τ) =
        (transportInv h R).map τ * (A₁⁻¹ : GL (Fin (2 + ε)) K).val * (R * transportInv h R) *
          A₁.val * R.map τ := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hRR, Matrix.mul_one, Matrix.mul_assoc ((transportInv h R).map τ), ← Units.val_mul,
          inv_mul_cancel, Units.val_one, Matrix.mul_one, hτRR']
  · obtain ⟨hg, hαg⟩ := hA₁ (hypTransport h hR g)
    have h1 : uProj K (2 + ε) f (hypTransport h hR (δ g)) =
        uProj K (2 + ε) f ⟨_, hg⟩ := by
      rw [← psiU_apply, hαδ, psiU_apply]
      exact hαg
    obtain ⟨c, hc⟩ := uProj_eq_uProj_iff.mp h1
    refine ⟨c⁻¹, ?_⟩
    have h2 := congrArg Units.val hc
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_glAut, scalar_apply] at h2
    rw [← smul_eq_diagonal_mul] at h2
    have h3 : R * smat h (δ g) * transportInv h R = ((c⁻¹ : Kˣ) : K) •
        (A₁.val * (R * smat h g * transportInv h R).map τ *
          (A₁⁻¹ : GL (Fin (2 + ε)) K).val) := by
      have e1 : ((hypTransport h hR (δ g) : StatedSU (2 + ε) (2 ^ f) K) :
          GL (Fin (2 + ε)) K).val = R * smat h (δ g) * transportInv h R := rfl
      have e2 : ((hypTransport h hR g : StatedSU (2 + ε) (2 ^ f) K) :
          GL (Fin (2 + ε)) K).val = R * smat h g * transportInv h R := rfl
      rw [e2] at h2
      rw [← e1, h2, smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero c),
        one_smul]
    calc smat h (δ g) = transportInv h R * (R * smat h (δ g) * transportInv h R) * R :=
          (transportInv_transport hR _).symm
      _ = _ := by
        rw [h3, Matrix.map_mul, Matrix.map_mul, Matrix.mul_smul, Matrix.smul_mul]
        congr 1
        simp only [Matrix.mul_assoc]

omit [CharP K 2] in
theorem map_single_eq (τ : K ≃+* K) :
    (Matrix.single hE hF (1 : K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K).map τ =
      Matrix.single hE hF 1 := by
  ext i j
  simp [Matrix.single_apply]

section Scalar

variable {δ : MulAut (stabE (ε := ε) h)} {τ : K ≃+* K}
  {Z Z' : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K} (hZZ : Z * Z' = 1) (hZZ' : Z' * Z = 1)
  (hδ : ∀ g, ∃ c : Kˣ, smat h (δ g) = (c : K) • (Z * (smat h g).map τ * Z'))
include hZZ hZZ' hδ

theorem semi_eq_of_tvSub (hT : (tvSub h).map δ.toMonoidHom = tvSub h) :
    (∀ g, smat h (δ g) = Z * (smat h g).map τ * Z') ∧ (∀ k, Z (.inr (.inl k)) hE = 0) ∧
      (∀ l, Z hF (.inr (.inl l)) = 0) ∧ Z hF hF ≠ 0 := by
  set E : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K := Matrix.single hE hF 1 with hEdef
  have hEv : ∀ v : HypIndex 1 ε → K, E *ᵥ v = v hF • Pi.single hE 1 := fun v => by
    rw [hEdef, single_mulVec_eq, one_mul]
  have hEE : E * E = 0 := by
    ext i j
    simp [hEdef, Matrix.mul_apply, Matrix.single_apply]
  have hc1 : h.bar 1 = 1 := map_one h.bar
  set t : stabE (ε := ε) h := ⟨tz h hc1, tz_mem_stabE h hc1⟩ with ht
  have hts : smat h t = 1 + E := by
    rw [smat, ht, coe_tz, one_smul]
  have htT : t ∈ tvSub h := by
    refine ⟨(mem_ker_zBlockHom h _).mpr (eich_mem_eichSub h (valid_zero h hc1)), ?_⟩
    funext k
    simp [avec, hts, hEdef, one_apply]
  have hδt : δ t ∈ tvSub h := by
    rw [← hT]
    exact ⟨t, htT, rfl⟩
  obtain ⟨c', hc'⟩ := exists_eichM_zero_of_avec h hδt.1 hδt.2
  rw [eichM_zero_left] at hc'
  obtain ⟨l, hl⟩ := hδ t
  rw [hts, Matrix.map_add _ (map_add τ), Matrix.map_one _ (map_zero τ) (map_one τ), hEdef,
    map_single_eq, ← hEdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hZZ] at hl
  have hl1 : (l : K) = 1 := by
    have htt : t * t = 1 := Subtype.ext (tz_mul_tz h hc1)
    have h1 : smat h (δ t) * smat h (δ t) = 1 := by
      rw [← smat_mul, ← map_mul, htt, map_one]
      rfl
    rw [hl, smul_mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_one, show Z * E * Z' * (Z * E * Z') = Z * (E * (Z' * Z) * E) * Z'
        by simp only [Matrix.mul_assoc], hZZ', Matrix.mul_one, hEE, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, add_assoc, ← two_smul K (Z * E * Z'), CharTwo.two_eq_zero,
      zero_smul, add_zero] at h1
    have h2 := congrFun (congrFun h1 hE) hE
    simp only [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at h2
    have h3 : ((l : K) - 1) * ((l : K) - 1) = 0 := by
      have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h2 + (1 - (l : K)) * h2'
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  rw [hl1, one_smul] at hl
  have hEZ : c' • (E * Z) = Z * E := by
    have h1 : c' • E = Z * E * Z' := by
      have := hc'.symm.trans hl
      exact add_left_cancel this
    calc c' • (E * Z) = (c' • E) * Z := (Matrix.smul_mul _ _ _).symm
      _ = Z * E * (Z' * Z) := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = Z * E := by rw [hZZ', Matrix.mul_one]
  have hrow : ∀ v : HypIndex 1 ε → K, (c' * (Z *ᵥ v) hF) • Pi.single hE (1 : K) =
      v hF • (Z *ᵥ Pi.single hE 1) := by
    intro v
    have h1 := congrArg (· *ᵥ v) hEZ
    simp only [smul_mulVec, ← mulVec_mulVec, hEv, mulVec_smul] at h1
    rw [smul_smul] at h1
    exact h1
  have hc'0 : c' ≠ 0 := by
    rintro rfl
    have h1 : smat h (δ t) = 1 := by rw [hc', zero_smul, add_zero]
    have h2 : δ t = 1 := Subtype.ext (Subtype.ext (Units.ext h1))
    have h3 : t = 1 := δ.injective (h2.trans δ.map_one.symm)
    have h4 := congrArg (fun x : stabE (ε := ε) h => smat h x hE hF) h3
    simp [hts, hEdef, smat] at h4
  have hZe : Z *ᵥ Pi.single hE 1 = (c' * (Z *ᵥ Pi.single hF 1) hF) • Pi.single hE 1 := by
    have h1 := hrow (Pi.single hF 1)
    rw [Pi.single_eq_same, one_smul] at h1
    exact h1.symm
  set μ := c' * (Z *ᵥ Pi.single hF 1) hF with hμ
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hZe
    have h1 := congrArg (Z' *ᵥ ·) hZe
    simp only [mulVec_mulVec, hZZ', one_mulVec, mulVec_zero] at h1
    have := congrFun h1 hE
    simp at this
  have hZ'e : Z' *ᵥ Pi.single hE 1 = μ⁻¹ • Pi.single hE 1 := by
    have h1 := congrArg (Z' *ᵥ ·) hZe
    simp only [mulVec_mulVec, hZZ', one_mulVec, mulVec_smul] at h1
    conv_rhs => rw [h1]
    rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  refine ⟨fun g => ?_, fun k => ?_, fun l' => ?_, ?_⟩
  · obtain ⟨cg, hcg⟩ := hδ g
    have he1 : smat h (δ g) *ᵥ Pi.single hE 1 = Pi.single hE 1 := (mem_stabE h).mp (δ g).2
    have hge : (smat h g).map τ *ᵥ Pi.single hE (1 : K) = Pi.single hE 1 := by
      have h0 : smat h g *ᵥ Pi.single hE 1 = Pi.single hE 1 := (mem_stabE h).mp g.2
      funext a
      have h2 := congrFun h0 a
      rw [mulVec_single_one, col_apply] at h2 ⊢
      rw [map_apply, h2]
      by_cases ha : a = hE
      · subst ha
        simp
      · simp [Pi.single_eq_of_ne ha]
    have hcg1 : (cg : K) = 1 := by
      rw [hcg, smul_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hZ'e, mulVec_smul, mulVec_smul,
        hge, hZe, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hμ0, mul_one] at he1
      have := congrFun he1 hE
      simpa using this
    rw [hcg, hcg1, one_smul]
  · have := congrFun hZe (.inr (.inl k))
    rw [mulVec_single_one, col_apply] at this
    simpa using this
  · have h1 := hrow (Pi.single (.inr (.inl l')) 1)
    rw [Pi.single_eq_of_ne (by simp), zero_smul, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hc'0
      · rw [mulVec_single_one, col_apply] at h2
        exact h2
    · have := congrFun h1 hE
      simp at this
  · intro h0
    have h1 := hrow (Pi.single hF 1)
    rw [Pi.single_eq_same, one_smul, mulVec_single_one, col_apply, h0, mul_zero, zero_smul] at h1
    have h2 := congrArg (Z' *ᵥ ·) h1.symm
    simp only [mulVec_mulVec, hZZ', one_mulVec, mulVec_zero] at h2
    have := congrFun h2 hE
    simp at this

end Scalar

section Hinj

variable {δ : MulAut (stabE (ε := ε) h)} {τ : K ≃+* K}
  {Z Z' : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K}

theorem semi_hinj [Finite K] (hf : 2 ≤ f) (hε : 2 ≤ ε) (hZZ' : Z' * Z = 1)
    (hδg : ∀ g, smat h (δ g) = Z * (smat h g).map τ * Z')
    (hZe : ∀ k, Z (.inr (.inl k)) hE = 0) (hZf0 : Z hF hF ≠ 0)
    (hfix : ∀ x ∈ (zBlockHom (ε := ε) h).ker, avec h (δ x) = avec h x → avec h x = 0) :
    ∀ a : Fin ε → K, Z hF hF • a = zBlock Z *ᵥ (τ ∘ a) → a = 0 := by
  intro a ha
  obtain ⟨x, hx, hxa⟩ := exists_mem_ker_avec_eq h a
  have hcomm : Z * (smat h x).map τ = smat h (δ x) * Z := by
    rw [hδg x, Matrix.mul_assoc _ Z', hZZ', Matrix.mul_one]
  have h1 := fcol_of_semi_commute h hZe hcomm
  have hδx : δ x ∈ (zBlockHom (ε := ε) h).ker := by
    rw [← map_ker_zBlockHom h hf hε δ]
    exact ⟨x, hx, rfl⟩
  have hρ : rmat h (δ x) = 1 := by
    rw [rmat, MonoidHom.mem_ker.mp hδx]
    rfl
  rw [hρ, one_mulVec, hxa, ← ha, add_comm] at h1
  have h2 : Z hF hF • a = Z hF hF • avec h (δ x) := add_left_cancel h1
  have h3 : a = avec h (δ x) := smul_right_injective _ hZf0 h2
  rw [← hxa]
  exact hfix x hx (by rw [← h3, hxa])

theorem avec_mul_inv_of_mem_ker {y z : stabE (ε := ε) h}
    (hy : y ∈ (zBlockHom (ε := ε) h).ker) (hz : z ∈ (zBlockHom (ε := ε) h).ker) :
    avec h (y * z⁻¹) = avec h y - avec h z := by
  have hy1 : rmat h y = 1 := by
    rw [rmat, MonoidHom.mem_ker.mp hy]
    rfl
  have hz1 : rmat h z⁻¹ = 1 := by
    rw [rmat, MonoidHom.mem_ker.mp (inv_mem hz)]
    rfl
  rw [avec_mul, hy1, one_mulVec, avec_inv, hz1, one_mulVec, sub_eq_add_neg]

theorem fixfree_conj [Finite K] (hf : 2 ≤ f) (hε : 2 ≤ ε) (β δ₀ : MulAut (stabE (ε := ε) h))
    (hδ₀ : ∀ x ∈ (zBlockHom (ε := ε) h).ker, avec h (δ₀ x) = avec h x → avec h x = 0) :
    ∀ x ∈ (zBlockHom (ε := ε) h).ker, avec h (β (δ₀ (β.symm x))) = avec h x →
      avec h x = 0 := by
  intro x hx hfx
  have hker : ∀ (γ : MulAut (stabE (ε := ε) h)) {y}, y ∈ (zBlockHom (ε := ε) h).ker →
      γ y ∈ (zBlockHom (ε := ε) h).ker := fun γ y hy => by
    rw [← map_ker_zBlockHom h hf hε γ]
    exact ⟨y, hy, rfl⟩
  have hT : ∀ (γ : MulAut (stabE (ε := ε) h)) {y}, y ∈ tvSub h → γ y ∈ tvSub h :=
    fun γ y hy => by
      rw [← map_tvSub h hf hε γ]
      exact ⟨y, hy, rfl⟩
  set x' := β.symm x
  have hx' : x' ∈ (zBlockHom (ε := ε) h).ker := hker β.symm hx
  have hδx' : δ₀ x' ∈ (zBlockHom (ε := ε) h).ker := hker δ₀ hx'
  have h1 : β (δ₀ x') * x⁻¹ ∈ tvSub h :=
    ⟨mul_mem (hker β hδx') (inv_mem hx), by
      rw [avec_mul_inv_of_mem_ker h (hker β hδx') hx, hfx, sub_self]⟩
  have h2 : δ₀ x' * x'⁻¹ ∈ tvSub h := by
    have := hT β.symm h1
    rwa [map_mul, map_inv, MulEquiv.symm_apply_apply] at this
  have h3 : avec h (δ₀ x') = avec h x' := by
    have := h2.2
    rw [avec_mul_inv_of_mem_ker h hδx' hx'] at this
    exact sub_eq_zero.mp this
  have h4 : x' ∈ tvSub h := ⟨hx', hδ₀ x' hx' h3⟩
  have h5 := hT β h4
  rw [MulEquiv.apply_symm_apply] at h5
  exact h5.2

end Hinj

end CFSG.ComponentClassification.RankTwoClassical.URigid
