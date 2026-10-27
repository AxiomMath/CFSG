module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6CentPGU
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KU6Fix

open CFSG.Fischer CFSG.LocalAnalysis.GLTheoremA.KU6Cent Module Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (mem_primeFormUnitary)
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo (hF4 hF4_bar bar bar_bar)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

noncomputable abbrev hf : (Fin 6 → F4) →ₛₗ[hF4.bar] (Fin 6 → F4) →ₗ[F4] F4 := stdHermForm hF4 6

theorem hf_apply (x y : Fin 6 → F4) : hf x y = ∑ i, bar (x i) * y i := by
  rw [hf, stdHermForm_apply, hF4_bar]

theorem hf_mulVec (g : Gu) (x y : Fin 6 → F4) :
    hf (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ x)
      (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ y) = hf x y := by
  have hg := g.2
  rw [mem_primeFormUnitary] at hg
  rw [hf, stdHermForm_eq_gramForm]
  refine (gramForm_isometry_iff hF4 1 _).2 ?_ x y
  simpa [idGram] using hg

noncomputable abbrev hperp (W : Submodule F4 (Fin 6 → F4)) : Submodule F4 (Fin 6 → F4) :=
  W.orthogonalBilin hf

theorem mem_hperp {W : Submodule F4 (Fin 6 → F4)} {y : Fin 6 → F4} :
    y ∈ hperp W ↔ ∀ w ∈ W, hf w y = 0 :=
  Submodule.mem_orthogonalBilin

private noncomputable def barE : F4 ≃+* F4 where
  toFun := bar
  invFun := bar
  left_inv := bar_bar
  right_inv := bar_bar
  map_mul' := map_mul bar
  map_add' := map_add bar

private theorem barE_apply (x : F4) : barE x = bar x := rfl

private theorem barE_symm_apply (x : F4) : barE.symm x = bar x := rfl

private theorem hperp_eq (W : Submodule F4 (Fin 6 → F4)) :
    hperp W = LinearFlag.dotOrth (LinearFlag.coordImage barE W) := by
  ext y
  rw [mem_hperp, LinearFlag.mem_dotOrth]
  constructor
  · intro h u hu
    have h1 := h _ (LinearFlag.mem_coordImage.1 hu)
    rw [hf_apply] at h1
    simp only [barE_symm_apply, bar_bar] at h1
    rw [dotProduct]
    rw [← h1]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · intro h w hw
    have h1 := h _ (LinearFlag.coord_mem_coordImage (σ := barE) hw)
    rw [dotProduct] at h1
    simp only [barE_apply] at h1
    rw [hf_apply, ← h1]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem finrank_coordImage (W : Submodule F4 (Fin 6 → F4)) :
    finrank F4 (LinearFlag.coordImage barE W) = finrank F4 W := by
  let j : W ≃+ LinearFlag.coordImage barE W :=
    { toFun := fun w => ⟨fun i => barE (w.1 i), LinearFlag.coord_mem_coordImage w.2⟩
      invFun := fun v => ⟨fun i => barE.symm (v.1 i), v.2⟩
      left_inv := fun w => by ext i; simp
      right_inv := fun v => by ext i; simp
      map_add' := fun v w => by ext i; simp }
  have h := rank_eq_of_equiv_equiv (barE : F4 → F4) j barE.bijective
    (fun r w => by ext i; simp [j])
  rw [Module.finrank, Module.finrank, h]

theorem finrank_hperp (W : Submodule F4 (Fin 6 → F4)) :
    finrank F4 (hperp W) = 6 - finrank F4 W := by
  rw [hperp_eq, LinearFlag.finrank_dotOrth, finrank_coordImage]

theorem finrank_le_three {W : Submodule F4 (Fin 6 → F4)} (hW : W ≤ hperp W) :
    finrank F4 W ≤ 3 := by
  have h1 := Submodule.finrank_mono hW
  rw [finrank_hperp] at h1
  have h2 := Submodule.finrank_le W
  rw [Module.finrank_fin_fun] at h2
  omega

theorem eq_one_of_fix (g : Gu) (hg : g ^ 9 = 1) {W : Submodule F4 (Fin 6 → F4)}
    (hW : W ≤ hperp W) (h3 : finrank F4 W = 3)
    (hfix : ∀ w ∈ W, ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ w = w) : g = 1 := by
  set M := ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) with hM
  have hWW : hperp W = W := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq hW
    rw [finrank_hperp, h3]
  have hmem : ∀ x, M *ᵥ x - x ∈ W := by
    intro x
    rw [← hWW, mem_hperp]
    intro w hw
    have h1 : hf w (M *ᵥ x) = hf w x := by
      conv_lhs => rw [← hfix w hw]
      exact hf_mulVec g w x
    rw [map_sub, h1, sub_self]
  have h2 : ∀ x, M *ᵥ (M *ᵥ x) = x := by
    intro x
    have h := hfix _ (hmem x)
    rw [Matrix.mulVec_sub] at h
    funext i
    have hi := congrFun h i
    simp only [Pi.sub_apply] at hi
    linear_combination hi + ((M *ᵥ x) i - x i) * F4.two_eq_zero
  have hg2 : g ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Subgroup.coe_pow, Units.val_pow_eq_pow_val, pow_two,
      ← Matrix.mulVec_mulVec, ← hM, h2, OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]
  calc g = g ^ 9 * ((g ^ 2) ^ 4)⁻¹ := by group
    _ = 1 := by rw [hg, hg2, one_pow, inv_one, one_mul]

private theorem circ_code : ∀ i j k l : Fin 4, (⟨i⟩ : F4) ≠ 0 → (⟨i⟩ : F4) ≠ 1 →
    (⟨j⟩ : F4) ^ 3 + (⟨i⟩ : F4) * (⟨k⟩ : F4) ^ 3 + (⟨i⟩ : F4) ^ 2 * (⟨l⟩ : F4) ^ 3 -
      3 * ((⟨i⟩ : F4) * (⟨j⟩ : F4) * (⟨k⟩ : F4) * (⟨l⟩ : F4)) = 0 →
    (⟨j⟩ : F4) = 0 ∧ (⟨k⟩ : F4) = 0 ∧ (⟨l⟩ : F4) = 0 := by
  decide

private theorem circ_eq_zero (c a b d : F4) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (h : a ^ 3 + c * b ^ 3 + c ^ 2 * d ^ 3 - 3 * (c * a * b * d) = 0) : a = 0 ∧ b = 0 ∧ d = 0 :=
  circ_code c.code a.code b.code d.code hc0 hc1 h

theorem linearIndependent_cyc {B : GL (Fin 6) F4} {c : F4ˣ} (hc : c ≠ 1)
    (hB : B ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c) {v : Fin 6 → F4} (hv : v ≠ 0) :
    LinearIndependent F4 ![v, (B : Matrix (Fin 6) (Fin 6) F4) *ᵥ v,
      (B : Matrix (Fin 6) (Fin 6) F4) *ᵥ ((B : Matrix (Fin 6) (Fin 6) F4) *ᵥ v)] := by
  set M := (B : Matrix (Fin 6) (Fin 6) F4) with hM
  have hM3 : ∀ x i, (M *ᵥ (M *ᵥ (M *ᵥ x))) i = (c : F4) * x i := by
    intro x i
    have h : ((B ^ 3 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ x =
        ((Matrix.GeneralLinearGroup.scalar (Fin 6) c : GL (Fin 6) F4) :
          Matrix (Fin 6) (Fin 6) F4) *ᵥ x := by rw [hB]
    rw [pow_succ, pow_succ, pow_one, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h
    rw [← hM] at h
    rw [h, Matrix.mulVec_diagonal]
  have hc0 : (c : F4) ≠ 0 := c.ne_zero
  have hc1 : (c : F4) ≠ 1 := fun h => hc (Units.val_eq_one.1 h)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons] at hg
  have e1 := congrArg (M *ᵥ ·) hg
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_zero] at e1
  have e2 := congrArg (M *ᵥ ·) e1
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_zero] at e2
  by_contra hne
  push Not at hne
  obtain ⟨k, hk⟩ := hne
  apply hv
  funext i
  have h0 := congrFun hg i
  have h1 := congrFun e1 i
  have h2 := congrFun e2 i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0 h1 h2
  rw [hM3 v i] at h1
  rw [hM3 v i, hM3 (M *ᵥ v) i] at h2
  have hΔ : (g 0 ^ 3 + (c : F4) * g 1 ^ 3 + (c : F4) ^ 2 * g 2 ^ 3 -
      3 * ((c : F4) * g 0 * g 1 * g 2)) * v i = 0 := by
    linear_combination (g 0 ^ 2 - g 1 * (c : F4) * g 2) * h0 +
      ((c : F4) * g 2 ^ 2 - g 0 * g 1) * h1 + (g 1 ^ 2 - g 0 * g 2) * h2
  rcases mul_eq_zero.1 hΔ with hd | hd
  · obtain ⟨ha, hb, hd'⟩ := circ_eq_zero _ _ _ _ hc0 hc1 hd
    exfalso
    apply hk
    fin_cases k
    · exact ha
    · exact hb
    · exact hd'
  · exact hd

noncomputable abbrev cyc (M : Matrix (Fin 6) (Fin 6) F4) (v : Fin 6 → F4) : Submodule F4 (Fin 6 → F4) :=
  Submodule.span F4 (Set.range ![v, M *ᵥ v, M *ᵥ (M *ᵥ v)])

theorem finrank_cyc {B : GL (Fin 6) F4} {c : F4ˣ} (hc : c ≠ 1)
    (hB : B ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c) {v : Fin 6 → F4} (hv : v ≠ 0) :
    finrank F4 (cyc (B : Matrix (Fin 6) (Fin 6) F4) v) = 3 := by
  rw [cyc, finrank_span_eq_card (linearIndependent_cyc hc hB hv), Fintype.card_fin]

theorem cyc_le {M : Matrix (Fin 6) (Fin 6) F4} {W : Submodule F4 (Fin 6 → F4)}
    (hW : ∀ w ∈ W, M *ᵥ w ∈ W) {v : Fin 6 → F4} (hv : v ∈ W) : cyc M v ≤ W := by
  rw [cyc, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  fin_cases k
  · exact hv
  · exact hW v hv
  · exact hW _ (hW v hv)

theorem fix_cyc {M N : Matrix (Fin 6) (Fin 6) F4} (hMN : N * M = M * N) {v : Fin 6 → F4}
    (hv : N *ᵥ v = v) : ∀ w ∈ cyc M v, N *ᵥ w = w := by
  have hcomm : ∀ x, N *ᵥ (M *ᵥ x) = M *ᵥ (N *ᵥ x) := fun x => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMN]
  let F : Submodule F4 (Fin 6 → F4) := LinearMap.ker (Matrix.mulVecLin N - LinearMap.id)
  have hF : ∀ x, x ∈ F ↔ N *ᵥ x = x := fun x => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply, LinearMap.id_apply,
      sub_eq_zero]
  have hle : cyc M v ≤ F := by
    rw [cyc, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, hF]
    fin_cases k
    · exact hv
    · change N *ᵥ (M *ᵥ v) = M *ᵥ v
      rw [hcomm, hv]
    · change N *ᵥ (M *ᵥ (M *ᵥ v)) = M *ᵥ (M *ᵥ v)
      rw [hcomm, hcomm, hv]
  exact fun w hw => (hF w).1 (hle hw)

end CFSG.LocalAnalysis.GLTheoremA.KU6Fix

end
