module

public import CFSG.LargeExtraspecial.AS35QThGamPsi

public section

namespace CFSG.LargeExtraspecial.AS35QTh

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)

theorem π_uLin (d : Fin 3 → K) (β : K) (y : Fin (3 + 2) → K) :
    π 3 (uLin d β y) = π 3 y + herm frob (v₀ 3) y • d := by
  rw [uLin_apply, map_add, map_add, map_smul, map_smul, π_v₀, π_ι, smul_zero, add_zero]

theorem uLin_u₀ (d : Fin 3 → K) (β : K) : uLin d β (u₀ 3) = u₀ 3 + β • v₀ 3 + ι 3 d := by
  rw [uLin_apply, herm_v₀_u₀, herm_ι_u₀, mul_one, add_zero, one_smul]

theorem PsiS_smul_v₀ (x : Model) : PsiS x • v₀ 3 = (gm x.2.2).det • v₀ 3 := by
  rw [PsiS, mul_smul, Lsu_smul_v₀, smul_comm, Usu_smul_v₀]

theorem π_PsiS_smul_ι (x : Model) (z : Fin 3 → K) :
    π 3 (PsiS x • ι 3 z) = (gm x.2.2).det • gv x.2.2 z := by
  rw [PsiS, mul_smul, Lsu_smul_ι, smul_comm, Usu_smul, map_smul, π_uLin, herm_v₀_ι, zero_smul,
    add_zero, π_ι]

theorem gm_injective : Function.Injective gm := by
  intro A B h
  exact Subtype.ext (Units.ext h)

theorem psiS_injective : Function.Injective PsiS := by
  rintro ⟨ε, a, A⟩ ⟨ε', a', A'⟩ h
  have h1 : (gm A).det • v₀ 3 = (gm A').det • v₀ 3 := by
    have := congrArg (· • v₀ 3) h
    simp only [PsiS_smul_v₀] at this
    exact this
  have hdet : (gm A).det = (gm A').det := smul_left_injective K v₀_ne_zero h1
  have hA : A = A' := by
    refine gm_injective (Matrix.ext_of_mulVec_single fun j => ?_)
    have h2 := π_PsiS_smul_ι (ε, a, A) (Pi.single j 1)
    rw [h, π_PsiS_smul_ι] at h2
    simp only at h2
    rw [hdet] at h2
    exact (smul_right_injective _ (det_gm_ne_zero A') h2).symm
  subst hA
  have h3 : Usu a (betaG ε a) (betaG_valid ε a) = Usu a' (betaG ε' a') (betaG_valid ε' a') :=
    mul_right_cancel h
  have h4 : u₀ 3 + betaG ε a • v₀ 3 + ι 3 a = u₀ 3 + betaG ε' a' • v₀ 3 + ι 3 a' := by
    have := congrArg (· • u₀ 3) h3
    simp only [Usu_smul, uLin_u₀] at this
    exact this
  have ha : a = a' := by
    have := congrArg (π 3) h4
    simpa only [map_add, map_smul, π_u₀, π_v₀, π_ι, smul_zero, zero_add] using this
  subst ha
  have hb : betaG ε a = betaG ε' a := by
    have := congrArg (herm frob (u₀ 3)) h4
    simpa only [herm_add_right, herm_smul_right, herm_u₀_u₀, herm_u₀_v₀, herm_u₀_ι, mul_one,
      zero_add, add_zero] using this
  have he : ε = ε' := toK_injective (by rw [betaG, betaG] at hb; exact add_left_cancel hb)
  rw [he]

theorem psiC_injective : Function.Injective psiC := by
  intro x y h
  apply psiS_injective
  apply mk_injective_PG5
  exact congrArg Subtype.val h

@[expose] noncomputable def bMat (g : SUid frob (3 + 2)) : Matrix (Fin 3) (Fin 3) K :=
  LinearMap.toMatrix'
    ((π 3).comp ((Matrix.toLin' ((g : GL (Fin (3 + 2)) K) : Matrix _ _ K)).comp (ι 3)))

theorem bMat_mulVec (g : SUid frob (3 + 2)) (z : Fin 3 → K) :
    bMat g *ᵥ z = π 3 (g • ι 3 z) := by
  rw [bMat, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, LinearMap.comp_apply,
    Matrix.toLin'_apply, smul_def]

theorem herm_v₀_smul_ι {g : SUid frob (3 + 2)} {c : K} (hc : c ≠ 0)
    (hg : g • v₀ 3 = c • v₀ 3) (z : Fin 3 → K) : herm frob (v₀ 3) (g • ι 3 z) = 0 := by
  have h := herm_smul_smul frob g (v₀ 3) (ι 3 z)
  rw [hg, herm_smul_left, herm_v₀_ι] at h
  exact (mul_eq_zero.mp h).resolve_left (frob_ne_zero hc)

theorem herm_bMat {g : SUid frob (3 + 2)} {c : K} (hc : c ≠ 0) (hg : g • v₀ 3 = c • v₀ 3)
    (z z' : Fin 3 → K) : herm frob (bMat g *ᵥ z) (bMat g *ᵥ z') = herm frob z z' := by
  rw [bMat_mulVec, bMat_mulVec, ← herm_ι_ι z z', ← herm_smul_smul frob g (ι 3 z) (ι 3 z'),
    herm_eq_coords (g • ι 3 z) (g • ι 3 z'), herm_v₀_smul_ι hc hg, herm_v₀_smul_ι hc hg,
    map_zero, mul_zero, zero_mul, zero_add, zero_add]

theorem conjTr_bMat {g : SUid frob (3 + 2)} {c : K} (hc : c ≠ 0) (hg : g • v₀ 3 = c • v₀ 3) :
    conjTr frob (bMat g) * bMat g = 1 :=
  conjTr_mul_self_of_isometry frob (herm_bMat hc hg)

@[expose] noncomputable def toGU3 (B : Matrix (Fin 3) (Fin 3) K) (hB : conjTr frob B * B = 1) :
    GU3 :=
  ⟨⟨B, conjTr frob B, conjTr_mul_self_comm hB, hB⟩, hB⟩

theorem conjTr_smul (c : K) (B : Matrix (Fin 3) (Fin 3) K) :
    conjTr frob (c • B) = frob c • conjTr frob B := by
  ext i j
  simp [conjTr, Matrix.transpose_apply, Matrix.map_apply]

theorem unitary_smul {B : Matrix (Fin 3) (Fin 3) K} (hB : conjTr frob B * B = 1) {c : K}
    (hc : frob c * c = 1) : conjTr frob (c • B) * (c • B) = 1 := by
  rw [conjTr_smul, Matrix.smul_mul, Matrix.mul_smul, hB, smul_smul, hc, one_smul]

theorem det_gm_inv (A : GU3) : (gm A⁻¹).det = ((gm A).det)⁻¹ := by
  have h : (gm A).det * (gm A⁻¹).det = 1 := by
    rw [← Matrix.det_mul, ← gm_mul, mul_inv_cancel]
    simp only [gm, OneMemClass.coe_one, Units.val_one, Matrix.det_one]
  exact eq_inv_of_mul_eq_one_right h

theorem exists_PsiS_eq {g : SUid frob (3 + 2)} {c : K} (hc : c ≠ 0)
    (hg : g • v₀ 3 = c • v₀ 3) : ∃ x : Model, PsiS x = g := by
  set B := bMat g with hBdef
  have hB : conjTr frob B * B = 1 := conjTr_bMat hc hg
  set δ := B.det with hδ
  have hδ0 : δ ≠ 0 := by
    have h := congrArg Matrix.det hB
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact right_ne_zero_of_mul_eq_one h
  have hfδ : frob δ⁻¹ * δ⁻¹ = 1 := frob_mul_self (inv_ne_zero hδ0)
  set A : GU3 := toGU3 (δ⁻¹ • B) (unitary_smul hB hfδ) with hAdef
  have hgmA : gm A = δ⁻¹ • B := rfl
  have hdetA : (gm A).det = δ := by
    rw [hgmA, Matrix.det_smul, Fintype.card_fin, inv_pow, pow_three_K hδ0, inv_one, one_mul]
  set g₁ := g * Lsu A⁻¹ with hg₁
  set c₁ := δ⁻¹ * c with hc₁
  have hc₁0 : c₁ ≠ 0 := mul_ne_zero (inv_ne_zero hδ0) hc
  have hg₁v : g₁ • v₀ 3 = c₁ • v₀ 3 := by
    rw [hg₁, mul_smul, Lsu_smul_v₀, det_gm_inv, hdetA, smul_comm, hg, smul_smul]
  have hg₁π : ∀ z, π 3 (g₁ • ι 3 z) = z := by
    intro z
    rw [hg₁, mul_smul, Lsu_smul_ι, det_gm_inv, hdetA, smul_comm, map_smul, ← bMat_mulVec,
      ← hBdef]
    have hB' : B = δ • gm A := by rw [hgmA, smul_smul, mul_inv_cancel₀ hδ0, one_smul]
    rw [hB', Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ hδ0, one_smul, ← gv, gv_gv_inv]
  set G₁ := ((g₁ : GL (Fin (3 + 2)) K) : Matrix (Fin (3 + 2)) (Fin (3 + 2)) K) with hG₁
  have hiso₁ : ∀ x y, herm frob (G₁ *ᵥ x) (G₁ *ᵥ y) = herm frob x y := fun x y => by
    rw [hG₁, ← smul_def, ← smul_def, herm_smul_smul]
  have hfc : frob c₁⁻¹ * c₁⁻¹ = 1 := frob_mul_self (inv_ne_zero hc₁0)
  have hMiso : ∀ x y, herm frob ((Dmat c₁⁻¹ * G₁) *ᵥ x) ((Dmat c₁⁻¹ * G₁) *ᵥ y) =
      herm frob x y := fun x y => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, herm_Dmat hfc, hiso₁]
  have hMv : (Dmat c₁⁻¹ * G₁) *ᵥ v₀ 3 = v₀ 3 := by
    rw [← Matrix.mulVec_mulVec, hG₁, ← smul_def, hg₁v, Matrix.mulVec_smul, Dmat_mulVec_v₀,
      smul_smul, mul_inv_cancel₀ hc₁0, one_smul]
  have hMπ : ∀ z, π 3 ((Dmat c₁⁻¹ * G₁) *ᵥ ι 3 z) = z := fun z => by
    rw [← Matrix.mulVec_mulVec, π_Dmat, hG₁, ← smul_def, hg₁π]
  have hdetM := det_eq_one_of_fix hMiso hMv hMπ
  rw [Matrix.det_mul, det_Dmat, hG₁, ((mem_SUid_iff frob).mp g₁.2).1, mul_one] at hdetM
  have hc₁1 : c₁ = 1 := by
    have := eq_one_of_sq_K hdetM
    rw [inv_eq_one] at this
    exact this
  rw [hc₁1, one_smul] at hg₁v
  have hG₁v : G₁ *ᵥ v₀ 3 = v₀ 3 := by rw [hG₁, ← smul_def, hg₁v]
  have hG₁π : ∀ z, π 3 (G₁ *ᵥ ι 3 z) = z := fun z => by rw [hG₁, ← smul_def, hg₁π]
  have hU := eq_Umat_of_fix hiso₁ hG₁v hG₁π
  set d := π 3 (G₁ *ᵥ u₀ 3) with hd
  set β := herm frob (u₀ 3) (G₁ *ᵥ u₀ 3) with hβ
  have hval : β + frob β = herm frob d d := by
    have h0 := hiso₁ (u₀ 3) (u₀ 3)
    rw [hU, Umat_mulVec, uLin_u₀, herm_u₀_u₀] at h0
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, herm_u₀_u₀,
      herm_u₀_v₀, herm_v₀_u₀, herm_v₀_v₀, herm_u₀_ι, herm_v₀_ι, herm_ι_u₀, herm_ι_v₀,
      herm_ι_ι, mul_zero, mul_one, zero_add, add_zero] at h0
    linear_combination h0 - herm frob d d * two_eq_zero
  have hg₁U : g₁ = Usu d β hval := by
    refine Subtype.ext (Units.ext ?_)
    rw [coe_Usu, ← hU]
  set s := β + frob ω * herm frob d d with hs
  have hs2 : s + frob s = 0 := by
    rw [hs, map_add, map_mul, frob_frob, herm_self_fixed frob frob_frob d]
    linear_combination hval + herm frob d d * omega_add_frob +
      herm frob d d * two_eq_zero
  obtain ⟨ε, hε⟩ : ∃ ε : ZMod 2, toK ε = s := by
    rcases (add_frob_eq_zero_iff s).1 hs2 with h0 | h1
    · exact ⟨0, by rw [map_zero, h0]⟩
    · exact ⟨1, by rw [map_one, h1]⟩
  refine ⟨(ε, d, A), ?_⟩
  have hβε : betaG ε d = β := by
    rw [betaG, hε, hs]
    linear_combination frob ω * herm frob d d * two_eq_zero
  have hgeq : g = g₁ * Lsu A := by rw [hg₁, mul_assoc, ← Lsu_inv, inv_mul_cancel, mul_one]
  simp only [PsiS]
  rw [hgeq, hg₁U, Usu_congr hβε _ hval]

theorem psiC_surjective : Function.Surjective psiC := by
  rintro ⟨γ, hγ⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  rw [Subgroup.mem_centralizer_singleton_iff] at hγ
  have h1 : g * tvU (v₀ 3) = tvU (v₀ 3) * g := by
    apply mk_injective_PG5
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact hγ
  have h2 : tvU (g • v₀ 3) = tvU (v₀ 3) := by
    rw [← conj_tvU g herm_v₀_v₀, h1, mul_inv_cancel_right]
  have hgv0 : g • v₀ 3 ≠ 0 := (smul_ne_zero_iff_ne g).mpr v₀_ne_zero
  have hiso : herm frob (g • v₀ 3) (g • v₀ 3) = 0 := by rw [herm_smul_smul, herm_v₀_v₀]
  obtain ⟨c, hc⟩ := (tvU_eq_tvU_iff v₀_ne_zero herm_v₀_v₀ hgv0 hiso).1 h2.symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hgv0 hc
  obtain ⟨x, hx⟩ := exists_PsiS_eq hc0 hc
  refine ⟨x, Subtype.ext ?_⟩
  change (QuotientGroup.mk (PsiS x) : PG 5) = QuotientGroup.mk g
  rw [hx]

theorem psiC_bijective : Function.Bijective psiC := ⟨psiC_injective, psiC_surjective⟩

end CFSG.LargeExtraspecial.AS35QTh
