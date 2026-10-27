module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48LayerY
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma25
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Fix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
open CFSG.Assembly
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K ζ9 ζ9_pow_nine ζ9_pow_three_ne_one)
open CFSG.Open.StatedSUFieldChange (statedProjSUEquiv statedSUEquiv statedSUEquiv_coe glEquiv_coe)
open CFSG.ClassicalInvolution.Phan (blockEmb blockEmb_injective coe_coe_blockEmb blockMat blockMat_apply
  blockIdx blockMat_apply_blockIdx)

noncomputable section

theorem pattern_of_charpoly {d : Fin 4 → K} {t : K} (ht : t ≠ 1)
    (h : ∏ i, (Polynomial.X - Polynomial.C (d i)) =
      ∏ i : Fin 4, (Polynomial.X - Polynomial.C (if i = 3 then (1 : K) else t))) :
    ∃ k : Fin 4, d k = 1 ∧ ∀ j, j ≠ k → d j = t := by
  classical
  have key : ∀ f : Fin 4 → K, ∏ i, (Polynomial.X - Polynomial.C (f i)) =
      ((Finset.univ.val.map f).map fun a => Polynomial.X - Polynomial.C a).prod := by
    intro f
    rw [Multiset.map_map]
    rfl
  have hm : (Finset.univ.val.map d) =
      Finset.univ.val.map (fun i : Fin 4 => if i = 3 then (1 : K) else t) := by
    have h1 := congrArg Polynomial.roots h
    rw [key, key, Polynomial.roots_multiset_prod_X_sub_C,
      Polynomial.roots_multiset_prod_X_sub_C] at h1
    exact h1
  rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at hm
  have hm' : ([d 0, d 1, d 2, d 3] : List K).Perm [t, t, t, 1] := by
    simpa [List.ofFn_succ, ht] using hm
  have hmem : ∀ j : Fin 4, d j = t ∨ d j = 1 := by
    intro j
    have h1 : d j ∈ ([d 0, d 1, d 2, d 3] : List K) := by fin_cases j <;> simp
    have h2 := hm'.mem_iff.1 h1
    simpa using h2
  rcases hmem 0 with h0 | h0 <;> rcases hmem 1 with h1 | h1 <;>
    rcases hmem 2 with h2 | h2 <;> rcases hmem 3 with h3 | h3
  all_goals first
    | (exfalso
       have hc := hm'.count_eq 1
       rw [h0, h1, h2, h3] at hc
       simp [List.count_cons, ht] at hc
       done)
    | exact ⟨0, h0, fun j hj => by fin_cases j <;> first | exact absurd rfl hj | assumption⟩
    | exact ⟨1, h1, fun j hj => by fin_cases j <;> first | exact absurd rfl hj | assumption⟩
    | exact ⟨2, h2, fun j hj => by fin_cases j <;> first | exact absurd rfl hj | assumption⟩
    | exact ⟨3, h3, fun j hj => by fin_cases j <;> first | exact absurd rfl hj | assumption⟩

theorem permMatrix_map_fix (σ : Equiv.Perm (Fin 4)) (f : K →+* K) :
    (σ.permMatrix K).map f = σ.permMatrix K := by
  ext i j
  simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, apply_ite f,
    map_one, map_zero]

theorem permMatrix_transpose_mul_self (σ : Equiv.Perm (Fin 4)) :
    (σ.permMatrix K)ᵀ * σ.permMatrix K = 1 := by
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

theorem nf_model {γ : MulAut SU4} (hγ3 : γ ^ 3 = 1) (hγ1 : fieldFactor4 γ ≠ 1)
    {h : SU4} (hh : ∀ x : SU4, γ (h * x * h⁻¹) = h * fieldSU4 (fieldFactor4 γ) x * h⁻¹)
    {Y g₀ : SU4} (hY : γ Y = Y) {t : μ3} (ht : (t : Kˣ) ≠ 1) (hg₀ : g₀ * Y * g₀⁻¹ = yStd t) :
    ∃ k : SU4, (∀ z : SU4, k * γ (k⁻¹ * z * k) * k⁻¹ = fieldSU4 (fieldFactor4 γ) z) ∧
      k * Y * k⁻¹ = yStd t := by
  classical
  set φ : K ≃+* K := fieldFactor4 γ with hφdef
  have hφ3 : φ ^ 3 = 1 := by rw [hφdef, ← map_pow, hγ3, map_one]
  have hφ1 : φ ≠ 1 := hγ1
  obtain ⟨p0, hp0⟩ : ∃ p0 : SU4, p0 = h⁻¹ * Y * h := ⟨_, rfl⟩
  have hFp0 : fieldSU4 φ p0 = p0 := by
    have h1 := hh p0
    have h2 : h * p0 * h⁻¹ = Y := by rw [hp0]; group
    rw [h2, hY] at h1
    calc fieldSU4 φ p0 = h⁻¹ * (h * fieldSU4 φ p0 * h⁻¹) * h := by group
      _ = h⁻¹ * Y * h := by rw [h1]
      _ = p0 := hp0.symm
  obtain ⟨c, hc⟩ : ∃ c : SU4, c = (g₀ * h)⁻¹ := ⟨_, rfl⟩
  have hp0c : p0 = c * yStd t * c⁻¹ := by
    have hY' : Y = g₀⁻¹ * yStd t * g₀ := by rw [← hg₀]; group
    rw [hp0, hY', hc]; group
  have hp03 : p0 ^ 3 = 1 := by rw [hp0c, conj_pow, yStd_pow_three]; group
  have hpu : ((((p0 : SU4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map hK.bar)ᵀ *
      ((p0 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := unitary_of_mem_SU4 p0
  have hpm3 : ((p0 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ^ 3 = 1 := by
    have := congrArg (fun x : SU4 => ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hp03
    simpa [Units.val_pow_eq_pow_val] using this
  have hpmF : ((p0 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ =
      ((p0 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    have := congrArg (fun x : SU4 => ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hFp0
    simpa [coe_fieldSU4, coe_glAut] using this
  obtain ⟨H, hH, hHF, d, -, hpH⟩ := exists_fixed_orthonormal_eigenbasis (g₀ := 1)
    (by simp) hφ3 hφ1 (by simp) hpu hpm3 (by simpa using hpmF)
  set Hu : GL (Fin 4) K := ⟨H, (H.map hK.bar)ᵀ, mul_eq_one_comm.mp hH, hH⟩ with hHu_def
  have hHu : ((Hu : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = H := rfl
  have hHu_inv : ((Hu⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (H.map hK.bar)ᵀ := rfl
  have hdiag : ((Hu⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((p0 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (Hu : Matrix (Fin 4) (Fin 4) K) =
      diagonal d := by
    rw [hHu_inv, hHu]
    calc (H.map hK.bar)ᵀ * ((p0 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * H
        = (H.map hK.bar)ᵀ * (((p0 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * H) := by
          rw [mul_assoc]
      _ = (H.map hK.bar)ᵀ * (H * diagonal d) := by rw [hpH]
      _ = ((H.map hK.bar)ᵀ * H) * diagonal d := by rw [mul_assoc]
      _ = diagonal d := by rw [hH, one_mul]
  have hcp1 : (diagonal d).charpoly =
      ((p0 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).charpoly := by
    rw [← hdiag, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj' Hu _
  have hpGL : (p0 : GL (Fin 4) K) = (c : GL (Fin 4) K) * (yStd t : GL (Fin 4) K) *
      (c : GL (Fin 4) K)⁻¹ := by
    rw [hp0c]; simp
  have hcp2 : ((p0 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).charpoly =
      ((yStd t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).charpoly := by
    have hpM : ((p0 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((c : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((yStd t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((c : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)⁻¹ := by
      rw [hpGL]
      simp only [Units.val_mul, Matrix.coe_units_inv]
    rw [hpM]
    exact Matrix.charpoly_units_conj (c : GL (Fin 4) K) _
  have hyd : ((yStd t : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal (fun k : Fin 4 => if k = 3 then (1 : K) else ((t : Kˣ) : K)) :=
    coe_yStd t
  have hcharp : (diagonal d).charpoly = (diagonal
      (fun k : Fin 4 => if k = 3 then (1 : K) else ((t : Kˣ) : K))).charpoly := by
    rw [hcp1, hcp2, hyd]
  rw [Matrix.charpoly_diagonal, Matrix.charpoly_diagonal] at hcharp
  have ht' : ((t : Kˣ) : K) ≠ 1 := fun h1 => ht (Units.val_eq_one.1 h1)
  obtain ⟨k, hk1, hkt⟩ := pattern_of_charpoly ht' hcharp
  set τ : Equiv.Perm (Fin 4) := Equiv.swap k 3 with hτdef
  have hd_tau : ∀ i : Fin 4, d (τ i) = if i = 3 then (1 : K) else ((t : Kˣ) : K) := by
    intro i
    by_cases hi3 : i = 3
    · subst hi3
      rw [hτdef, Equiv.swap_apply_right, hk1, if_pos rfl]
    · by_cases hik : i = k
      · subst hik
        have h3i : (3 : Fin 4) ≠ i := fun h => hi3 h.symm
        rw [hτdef, Equiv.swap_apply_left, hkt 3 h3i, if_neg hi3]
      · rw [hτdef, Equiv.swap_apply_of_ne_of_ne hik hi3, hkt i hik, if_neg hi3]
  obtain ⟨P, hPdef⟩ : ∃ P : GL (Fin 4) K, P = TauCeti.permutationGL (k := K) τ := ⟨_, rfl⟩
  have hPval : ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = τ⁻¹.permMatrix K := by
    rw [hPdef, TauCeti.permutationGL_coe]
  have hPT : ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *
      ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [hPval]
    exact permMatrix_transpose_mul_self τ⁻¹
  have hPbar : ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map hK.bar =
      ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [hPval]; exact permMatrix_map_fix τ⁻¹ hK.bar
  have hPφ : ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ =
      ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [hPval]; exact permMatrix_map_fix τ⁻¹ φ
  obtain ⟨H', hH'def⟩ : ∃ H' : GL (Fin 4) K, H' = Hu * P := ⟨_, rfl⟩
  have hH'val : ((H' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      H * ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [hH'def]; rfl
  have hH'mem : H' ∈ primeFormUnitary hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one, hH'val, Matrix.map_mul, hPbar,
      Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc ((H.map hK.bar)ᵀ) H, hH, one_mul]
    exact hPT
  have hHφ : H.map φ = H := by
    have := hHF
    rwa [Matrix.one_mul] at this
  have hH'φ : ((H' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ =
      ((H' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [hH'val, Matrix.map_mul, hHφ, hPφ]
  have hglH : glAut φ H' = H' := Units.ext (by rw [coe_glAut]; exact hH'φ)
  have hXd : ((Hu⁻¹ * (p0 : GL (Fin 4) K) * Hu : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal d := by
    rw [Units.val_mul, Units.val_mul]; exact hdiag
  have hPconj : ((P⁻¹ * (Hu⁻¹ * (p0 : GL (Fin 4) K) * Hu) * P : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = diagonal (fun i => d (τ i)) := by
    rw [hPdef]
    ext i j
    rw [TauCeti.coe_permutationGL_inv_mul_mul_permutationGL_apply, hXd, Matrix.diagonal_apply,
      Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hne : τ i ≠ τ j := fun h => hij (τ.injective h)
      simp [hij, hne]
  have hH'p : H'⁻¹ * (p0 : GL (Fin 4) K) * H' = (yStd t : GL (Fin 4) K) := by
    have e2 : H'⁻¹ * (p0 : GL (Fin 4) K) * H' =
        P⁻¹ * (Hu⁻¹ * (p0 : GL (Fin 4) K) * Hu) * P := by
      rw [hH'def]; group
    apply Units.ext
    rw [e2, hPconj, hyd]
    congr 1
    funext i
    exact hd_tau i
  have hH'inv : H'⁻¹ ∈ primeFormUnitary hK ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
    inv_mem hH'mem
  obtain ⟨g₁, hg₁⟩ := exists_SU4_conj_eq hH'inv
  simp only [inv_inv] at hg₁
  refine ⟨g₁ * h⁻¹, ?_, ?_⟩
  · intro z
    have hu : (g₁ * h⁻¹)⁻¹ * z * (g₁ * h⁻¹) = h * (g₁⁻¹ * z * g₁) * h⁻¹ := by group
    rw [hu, hh]
    have hk : g₁ * h⁻¹ * (h * fieldSU4 φ (g₁⁻¹ * z * g₁) * h⁻¹) * (g₁ * h⁻¹)⁻¹ =
        g₁ * fieldSU4 φ (g₁⁻¹ * z * g₁) * g₁⁻¹ := by group
    rw [hk]
    apply Subtype.ext
    have E1 : ∀ x : GL (Fin 4) K, (g₁ : GL (Fin 4) K) * x * (g₁ : GL (Fin 4) K)⁻¹ =
        H'⁻¹ * x * H' := fun x => (hg₁ x).symm
    have E2 : H'⁻¹ * ((g₁ : GL (Fin 4) K)⁻¹ * (z : GL (Fin 4) K) * (g₁ : GL (Fin 4) K)) * H' =
        (z : GL (Fin 4) K) := by
      rw [← E1]; group
    have E3 : glAut φ (z : GL (Fin 4) K) =
        H'⁻¹ * glAut φ ((g₁ : GL (Fin 4) K)⁻¹ * (z : GL (Fin 4) K) * (g₁ : GL (Fin 4) K)) * H' := by
      calc glAut φ (z : GL (Fin 4) K)
          = glAut φ (H'⁻¹ * ((g₁ : GL (Fin 4) K)⁻¹ * (z : GL (Fin 4) K) * (g₁ : GL (Fin 4) K)) * H') := by
            rw [E2]
        _ = H'⁻¹ * glAut φ ((g₁ : GL (Fin 4) K)⁻¹ * (z : GL (Fin 4) K) * (g₁ : GL (Fin 4) K)) * H' := by
            rw [map_mul, map_mul, map_inv, hglH]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_fieldSU4]
    rw [E1, E3]
  · apply Subtype.ext
    have hYp : g₁ * h⁻¹ * Y * (g₁ * h⁻¹)⁻¹ = g₁ * p0 * g₁⁻¹ := by rw [hp0]; group
    rw [hYp]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hg₁ (p0 : GL (Fin 4) K), hH'p]


theorem kerEquiv_spec {t : μ3} (ht : (t : Kˣ) ≠ 1) (s : ↥(rho ht).ker) :
    (blockEmb K 2 3 4 3 0 (by norm_num) (kerEquiv ht s) : SU4) = s.1.1 := by
  have hf := blockEmb_injective (K := K) (p := 2) (f := 3) (by norm_num : 0 + 3 ≤ 4)
  have h1 : kerEquiv ht s = (MonoidHom.ofInjective hf).symm
      ((MulEquiv.subgroupCongr (map_ker_rho ht))
        ((Subgroup.equivMapOfInjective (rho ht).ker (Cstd t).subtype (Cstd t).subtype_injective) s)) :=
    rfl
  have h2 := congrArg Subtype.val (show (MonoidHom.ofInjective hf) (kerEquiv ht s) =
      (MulEquiv.subgroupCongr (map_ker_rho ht))
        ((Subgroup.equivMapOfInjective (rho ht).ker (Cstd t).subtype (Cstd t).subtype_injective) s) by
    rw [h1, MulEquiv.apply_symm_apply])
  exact h2

theorem blockMat_map_fix (A : Matrix (Fin 3) (Fin 3) K) (f : K ≃+* K) :
    (blockMat 4 0 A).map f = blockMat 4 0 (A.map f) := by
  ext a b
  rw [Matrix.map_apply, blockMat_apply, blockMat_apply]
  split_ifs
  · simp
  · simp [Matrix.one_apply, apply_ite f]

theorem blockMat_inj_zero {A B : Matrix (Fin 3) (Fin 3) K} (h : blockMat 4 0 A = blockMat 4 0 B) :
    A = B := by
  ext x y
  have := congrFun (congrFun h (blockIdx 0 (by norm_num) x)) (blockIdx 0 (by norm_num) y)
  rwa [blockMat_apply_blockIdx, blockMat_apply_blockIdx] at this

theorem normalizer_cx_of_comm {G : Type} [Group G] {g y : G} (hgy : g * y = y * g) :
    g ∈ Subgroup.normalizer ((cx y : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  change h ∈ Subgroup.centralizer ({y} : Set G) ↔ g * h * g⁻¹ ∈ Subgroup.centralizer ({y} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hgi : g⁻¹ * y = y * g⁻¹ := by
    have e : g⁻¹ * y = g⁻¹ * (y * g) * g⁻¹ := by group
    rw [e, hgy.symm]
    group
  have e1 : g * h * g⁻¹ * y = g * (h * y) * g⁻¹ := by
    calc g * h * g⁻¹ * y = g * h * (g⁻¹ * y) := by group
      _ = g * h * (y * g⁻¹) := by rw [hgi]
      _ = g * (h * y) * g⁻¹ := by group
  have e2 : y * (g * h * g⁻¹) = g * (y * h) * g⁻¹ := by
    calc y * (g * h * g⁻¹) = (y * g) * h * g⁻¹ := by group
      _ = (g * y) * h * g⁻¹ := by rw [hgy.symm]
      _ = g * (y * h) * g⁻¹ := by group
  rw [e1, e2]
  constructor
  · intro hc
    rw [hc]
  · intro hc
    exact mul_left_cancel (mul_right_cancel hc)

theorem exists_noncomm_of_commutator_top {G : Type*} [Group G] [Nontrivial G]
    (h : commutator G = ⊤) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have h1 : (⊤ : Subgroup G) ≤ Subgroup.centralizer (⊤ : Subgroup G) := fun x _ =>
    Subgroup.mem_centralizer_iff.2 fun b _ => hc b x
  have h2 : commutator G = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 h1
  rw [h] at h2
  exact top_ne_bot h2


theorem statedSU3_diag_mem {ζ : K} (hζ9 : ζ ^ 9 = 1) (hζ0 : ζ ≠ 0) :
    ∃ a : ↥(StatedSU 3 (2 ^ 3) K), ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![1, ζ, ζ⁻¹] := by
  have hu1 : diagonal ![(1 : K), ζ, ζ⁻¹] * diagonal ![(1 : K), ζ⁻¹, ζ] = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hζ0]
  have hu2 : diagonal ![(1 : K), ζ⁻¹, ζ] * diagonal ![(1 : K), ζ, ζ⁻¹] = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hζ0]
  have hdet : (diagonal ![(1 : K), ζ, ζ⁻¹]).det = 1 := by
    rw [det_diagonal, Fin.prod_univ_three]
    simp [mul_inv_cancel₀ hζ0]
  have hunit : ((diagonal ![(1 : K), ζ, ζ⁻¹]).map (· ^ (2 ^ 3)))ᵀ * diagonal ![(1 : K), ζ, ζ⁻¹] = 1 := by
    rw [diagonal_map (by simp), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have h8 : ζ ^ 8 * ζ = 1 := by rw [← pow_succ]; exact hζ9
    have h8' : (ζ ^ 8)⁻¹ * ζ⁻¹ = 1 := by rw [← mul_inv, h8, inv_one]
    fin_cases i <;> simp [h8, h8']
  let u : GL (Fin 3) K := ⟨diagonal ![(1 : K), ζ, ζ⁻¹], diagonal ![(1 : K), ζ⁻¹, ζ], hu1, hu2⟩
  refine ⟨⟨u, Subgroup.subset_closure ⟨hdet, hunit⟩⟩, rfl⟩

theorem statedProj_field_ne_one {φ' : K ≃+* K} (hφ'3 : φ' ^ 3 = 1) (hφ'1 : φ' ≠ 1) :
    statedProjSUEquiv φ' 3 (2 ^ 3) ≠ 1 := by
  intro h1
  have hord : orderOf φ' = 3 := orderOf_eq_prime hφ'3 hφ'1
  set ζ : K := ((ζ9 : Kˣ) : K) with hζdef
  have hζ9 : ζ ^ 9 = 1 := by rw [hζdef, ← Units.val_pow_eq_pow_val, ζ9_pow_nine, Units.val_one]
  have hζ0 : ζ ≠ 0 := (ζ9 : Kˣ).ne_zero
  have hζ3 : ζ ^ 3 ≠ 1 := fun h => ζ9_pow_three_ne_one (Units.ext (by simpa [hζdef] using h))
  have hζfix : φ' ζ ≠ ζ := by
    intro hfix
    have hmem : ζ ∈ fixField φ' := mem_fixField.2 hfix
    haveI : Fintype (fixField φ') := Fintype.ofFinite _
    have h4 : Fintype.card (fixField φ') = 4 := by
      rw [Fintype.card_eq_nat_card, card_fixField hord]
    have hpow := FiniteField.pow_card (⟨ζ, hmem⟩ : fixField φ')
    rw [h4] at hpow
    have hz4 : ζ ^ 4 = ζ := by simpa using congrArg Subtype.val hpow
    apply hζ3
    have : ζ * ζ ^ 3 = ζ * 1 := by rw [mul_one, ← pow_succ', hz4]
    exact mul_left_cancel₀ hζ0 this
  obtain ⟨a, ha⟩ := statedSU3_diag_mem hζ9 hζ0
  have hq : (QuotientGroup.mk (statedSUEquiv φ' 3 (2 ^ 3) a) : StatedProj (StatedSU 3 (2 ^ 3) K)) =
      QuotientGroup.mk a := by
    have := congrArg (fun F => F (QuotientGroup.mk a : StatedProj (StatedSU 3 (2 ^ 3) K))) h1
    rw [MulAut.one_apply] at this
    exact this
  rw [QuotientGroup.eq] at hq
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 (show ((statedSUEquiv φ' 3 (2 ^ 3) a :
      GL (Fin 3) K))⁻¹ * (a : GL (Fin 3) K) ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3)).range from
    Subgroup.mem_subgroupOf.1 hq)
  have hab : (a : GL (Fin 3) K) = (statedSUEquiv φ' 3 (2 ^ 3) a : GL (Fin 3) K) *
      Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    rw [hc]; group
  have hb : ((statedSUEquiv φ' 3 8 a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ' := by
    rw [statedSUEquiv_coe, glEquiv_coe]
  have hm := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) hab
  have e00 := congrFun (congrFun hm 0) 0
  have e11 := congrFun (congrFun hm 1) 1
  simp [ha, hb, Matrix.mul_diagonal, Matrix.map_apply, Matrix.diagonal_apply] at e00 e11
  apply hζfix
  have hc1 : ((c : Kˣ) : K) = 1 := by
    first
    | exact e00.symm
    | exact e00
    | simpa using e00.symm
  rw [hc1, mul_one] at e11
  exact e11.symm


theorem statedProj_field_pow_three {φ' : K ≃+* K} (hφ'3 : φ' ^ 3 = 1) :
    statedProjSUEquiv φ' 3 (2 ^ 3) ^ 3 = 1 := by
  have hcube : ∀ x : K, φ' (φ' (φ' x)) = x := fun x => by
    have := congrArg (fun e : K ≃+* K => e x) hφ'3
    simpa [pow_succ] using this
  apply MulEquiv.ext
  intro x
  have hpow : ∀ y, (statedProjSUEquiv φ' 3 (2 ^ 3) ^ 3) y =
      statedProjSUEquiv φ' 3 (2 ^ 3) (statedProjSUEquiv φ' 3 (2 ^ 3)
        (statedProjSUEquiv φ' 3 (2 ^ 3) y)) := fun y => by
    simp [pow_succ, MulAut.mul_apply]
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
  rw [hpow, MulAut.one_apply]
  show QuotientGroup.mk (statedSUEquiv φ' 3 8 (statedSUEquiv φ' 3 8 (statedSUEquiv φ' 3 8 b))) =
    QuotientGroup.mk b
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp only [statedSUEquiv_coe, glEquiv_coe]
  ext i j
  simp [Matrix.map_apply, hcube]

theorem field_mem_F {φ' : K ≃+* K} :
    statedProjSUEquiv φ' 3 (2 ^ 3) ∈ LargeEvenMatFieldImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin (2 + 1)) K (2 ^ 3))) := by
  refine ⟨φ', fun h h' hrel => ?_⟩
  have hrel' : ((h' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ' := hrel
  let h₁ : ↥(StatedSU 3 (2 ^ 3) K) := ⟨h.1, h.2⟩
  let h₂ : ↥(StatedSU 3 (2 ^ 3) K) := ⟨h'.1, h'.2⟩
  change QuotientGroup.mk (statedSUEquiv φ' 3 (2 ^ 3) h₁) = QuotientGroup.mk h₂
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [statedSUEquiv_coe, glEquiv_coe]
  exact hrel'.symm

theorem one_mem_conjImage :
    (1 : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (2 + 1)) K (2 ^ 3)))) ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (2 + 1)) K (2 ^ 3)))
        (LargeEvenGUSet (Fin (2 + 1)) K (2 ^ 3)) := by
  refine ⟨1, ⟨1, one_ne_zero, by simp, by simp⟩, fun h h' hrel => ?_⟩
  rw [MulAut.one_apply]
  congr 1
  apply Subtype.ext
  simpa using hrel.symm


noncomputable def cqSU3 :
    CFSG.ClassicalInvolution.Phan.Su K 2 3 3 ⧸
        Subgroup.center (CFSG.ClassicalInvolution.Phan.Su K 2 3 3) ≃*
      StatedProj (StatedSU 3 (2 ^ 3) K) :=
  (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU card_K 3))
    (CFSG.LieType.Universal.Unitary.map_center_mulEquiv _)).trans
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card card_K (le_refl 3)
        (by decide)).2)

theorem cqSU3_mk (y : CFSG.ClassicalInvolution.Phan.Su K 2 3 3) :
    cqSU3 (QuotientGroup.mk y) = QuotientGroup.mk (MulEquiv.subgroupCongr
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU card_K 3) y) :=
  (congrArg (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card card_K (le_refl 3)
        (by decide)).2)
    (QuotientGroup.congr_mk _ _ (MulEquiv.subgroupCongr
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU card_K 3))
      (CFSG.LieType.Universal.Unitary.map_center_mulEquiv _) y)).trans
    (QuotientGroup.quotientMulEquivOfEq_mk _ _)

theorem fieldOn_layer_model {G : Type} [Group G] [Finite G] {M : Subgroup G} {g y : G}
    (hgM : g ∈ Subgroup.normalizer (M : Set G)) (hgy : g * y = y * g)
    (φ : ↥M →* SU4) (hφs : Function.Surjective φ) (hker : ¬ 3 ∣ Nat.card φ.ker)
    {t : μ3} (ht : (t : Kˣ) ≠ 1) (hyM : y ∈ M) (hy3 : y ^ 3 = 1)
    (hφy : φ ⟨y, hyM⟩ = yStd t) {φ' : K ≃+* K} (hφ'3 : φ' ^ 3 = 1) (hφ'1 : φ' ≠ 1)
    (hφg : ∀ x : ↥M, φ (conjL M g hgM x) = fieldSU4 φ' (φ x)) :
    FieldOn 3 g (GLAPLayer 3 (M ⊓ cx y)) := by
  classical
  obtain ⟨J, hJ, hJl, himg, -⟩ := layerY φ hφs hker ht hyM hy3 hφy
  rw [hJl]
  have hJle : J ≤ M ⊓ cx y := hJ.1
  have hJM : J ≤ M := hJle.trans inf_le_left
  have hgX : g ∈ Subgroup.normalizer ((M ⊓ cx y : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 := Subgroup.mem_normalizer_iff.1 hgM h
    have h2 := Subgroup.mem_normalizer_iff.1 (normalizer_cx_of_comm hgy) h
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    rw [h1, h2]
  have hgJ : g ∈ Subgroup.normalizer (J : Set G) := by
    apply mem_normalizer_iff_gLBConj_eq.2
    rw [← hJl, ← CFSG.HardMathSupport.Solomon.LocalBalance.Lemma25Ns.glaPLayer_gLBConj,
      mem_normalizer_iff_gLBConj_eq.1 hgX]
  refine ⟨hgJ, ?_⟩
  have hπker := restrictCent_ker φ hker hyM hφy
  have hJmem : ∀ j : ↥J, restrictCent φ hyM hφy (Subgroup.inclusion hJle j) ∈ (rho ht).ker := by
    intro j
    have hj : φ ⟨j.1, hJM j.2⟩ ∈ Jblk := by
      rw [← himg]
      exact ⟨⟨j.1, hJM j.2⟩, Subgroup.mem_subgroupOf.2 j.2, rfl⟩
    rw [← map_ker_rho ht] at hj
    obtain ⟨s, hs, hsj⟩ := hj
    have hs' : restrictCent φ hyM hφy (Subgroup.inclusion hJle j) = s := Subtype.ext hsj.symm
    rw [hs']
    exact hs
  have hsurj : ∀ s ∈ (rho ht).ker, ∃ j : ↥J,
      restrictCent φ hyM hφy (Subgroup.inclusion hJle j) = s := by
    intro s hs
    have hs' : (Cstd t).subtype s ∈ Jblk := by
      rw [← map_ker_rho ht]
      exact ⟨s, hs, rfl⟩
    rw [← himg] at hs'
    obtain ⟨x, hx, hxs⟩ := hs'
    exact ⟨⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩, Subtype.ext hxs⟩
  have hSc : GLAPPrimeCore 3 ↥(rho ht).ker = ⊥ := pPrimeCore_normal_eq_bot (pPrimeCore_Cstd ht) _
  let ε₁ := pquotEquivOfSurj (restrictTo (restrictCent φ hyM hφy) (rho ht).ker hJle hJmem)
    (restrictTo_surjective _ _ hJle hJmem hsurj) (restrictTo_ker _ _ hJle hJmem hπker) hSc
  let ε : PQuot 3 J ≃* CFSG.ClassicalInvolution.Phan.Su K 2 3 3 := ε₁.trans (kerEquiv ht)
  have hεspec : ∀ x : ↥J, (blockEmb K 2 3 4 3 0 (by norm_num) (ε (QuotientGroup.mk x)) : SU4) =
      φ ⟨x.1, hJM x.2⟩ :=
    fun x => kerEquiv_spec ht _
  let θ : PQuot 3 J ⧸ Subgroup.center (PQuot 3 J) ≃* StatedProj (StatedSU 3 (2 ^ 3) K) :=
    (QuotientGroup.congr _ _ ε (CFSG.LieType.Universal.Unitary.map_center_mulEquiv ε)).trans cqSU3
  have hcore : ∀ a : ↥J, statedProjSUEquiv φ' 3 (2 ^ 3) (θ (QuotientGroup.mk (QuotientGroup.mk a))) =
      θ (QuotientGroup.mk (QuotientGroup.mk (conjL J g hgJ a))) := by
    intro a
    have hSU : (blockEmb K 2 3 4 3 0 (by norm_num) (ε (QuotientGroup.mk (conjL J g hgJ a))) : SU4) =
        fieldSU4 φ' (blockEmb K 2 3 4 3 0 (by norm_num) (ε (QuotientGroup.mk a)) : SU4) := by
      rw [hεspec, hεspec]
      have e : (⟨(conjL J g hgJ a : G), hJM (conjL J g hgJ a).2⟩ : ↥M) =
          conjL M g hgM ⟨a.1, hJM a.2⟩ := Subtype.ext (by rw [conjL_apply, conjL_apply])
      rw [e]
      exact hφg ⟨a.1, hJM a.2⟩
    have hF : (((blockEmb K 2 3 4 3 0 (by norm_num) (ε (QuotientGroup.mk a)) : SU4) :
        GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ' =
        (((fieldSU4 φ' (blockEmb K 2 3 4 3 0 (by norm_num) (ε (QuotientGroup.mk a)) : SU4) :
          SU4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      rw [coe_fieldSU4, coe_glAut]
    have hmat : ((ε (QuotientGroup.mk (conjL J g hgJ a)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((ε (QuotientGroup.mk a) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ' := by
      apply blockMat_inj_zero
      rw [← coe_coe_blockEmb (K := K) (p := 2) (f := 3) (m := 4) (k := 3) (i := 0) (by norm_num),
        ← blockMat_map_fix,
        ← coe_coe_blockEmb (K := K) (p := 2) (f := 3) (m := 4) (k := 3) (i := 0) (by norm_num)]
      rw [hF, hSU]
    have hθmk : ∀ x : ↥J, θ (QuotientGroup.mk (QuotientGroup.mk x)) =
        QuotientGroup.mk (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU card_K 3)
          (ε (QuotientGroup.mk x))) := fun x =>
      (congrArg cqSU3 (QuotientGroup.congr_mk _ _ ε
        (CFSG.LieType.Universal.Unitary.map_center_mulEquiv ε) (QuotientGroup.mk x))).trans
        (cqSU3_mk _)
    have hfmk : ∀ y : ↥(StatedSU 3 (2 ^ 3) K), statedProjSUEquiv φ' 3 (2 ^ 3) (QuotientGroup.mk y) =
        QuotientGroup.mk (statedSUEquiv φ' 3 (2 ^ 3) y) := fun y => rfl
    rw [hθmk, hθmk, hfmk]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [statedSUEquiv_coe, glEquiv_coe]
    exact hmat.symm
  have hQ := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
  have hsimple : IsSimpleGroup (StatedProj (StatedSU 3 (2 ^ 3) K)) := by
    haveI := hQ.2
    exact θ.symm.isSimpleGroup
  have hcomm : commutator (PQuot 3 J ⧸ Subgroup.center (PQuot 3 J)) = ⊤ := by
    let f := QuotientGroup.mk' (Subgroup.center (PQuot 3 J))
    have htop : Subgroup.map f ⊤ = ⊤ := by
      rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
      exact QuotientGroup.mk'_surjective _
    have hc : ⁅(⊤ : Subgroup (PQuot 3 J)), ⊤⁆ = ⊤ := hQ.1
    have key : Subgroup.map f ⁅(⊤ : Subgroup (PQuot 3 J)), ⊤⁆ =
        ⁅Subgroup.map f ⊤, Subgroup.map f ⊤⁆ := Subgroup.map_commutator (⊤ : Subgroup (PQuot 3 J)) (⊤ : Subgroup (PQuot 3 J)) f
    rw [hc, htop] at key
    exact key.symm
  have hnon : ∃ a b : StatedProj (StatedSU 3 (2 ^ 3) K), a * b ≠ b * a := by
    haveI := hQ.2
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_commutator_top hcomm
    exact ⟨θ a, θ b, fun h => hab (θ.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hord : orderOf (statedProjSUEquiv φ' 3 (2 ^ 3)) = 3 :=
    orderOf_eq_prime (statedProj_field_pow_three hφ'3) (statedProj_field_ne_one hφ'3 hφ'1)
  refine ⟨hQ.1, ⟨.twA, 2, 3⟩, by norm_num [LargeEvenInLambda2], ?_⟩
  dsimp only [LargeEvenRawDatum]
  unfold LargeEvenRecipeUnitary
  refine ⟨K, inferInstance, inferInstance, by rw [card_K], ?_⟩
  refine ⟨hsimple, hnon, θ, Or.inl (by decide), statedProjSUEquiv φ' 3 (2 ^ 3), field_mem_F, 1,
    one_mem_conjImage, hord, ?_⟩
  intro l l' hrel
  obtain ⟨a, b, rfl, rfl, hab⟩ := hrel
  have hb : b = conjL J g hgJ a := Subtype.ext (by rw [conjL_apply]; exact hab)
  simp only [one_mul, mul_one, inv_one]
  rw [hb]
  exact hcore a

end

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48

end
