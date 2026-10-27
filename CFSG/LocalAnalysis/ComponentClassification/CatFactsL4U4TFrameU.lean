module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TFrameL
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4NoPSpUGraph

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace TBlocks

open Matrix HBlocks

variable {F : Type} [Field F]

theorem eigen_data (h2 : (2 : F) ≠ 0) {X : Matrix (Fin 4) (Fin 4) F} (hXX : X * X = 1)
    (hdet : X.det = 1) (h1 : X ≠ 1) (hm1 : X ≠ -1) :
    IsCompl (LinearMap.ker (Matrix.toLin' X - 1)) (LinearMap.ker (Matrix.toLin' X + 1)) ∧
      Module.finrank F (LinearMap.ker (Matrix.toLin' X - 1)) = 2 ∧
      Module.finrank F (LinearMap.ker (Matrix.toLin' X + 1)) = 2 := by
  classical
  set T := Matrix.toLin' X with hT
  have hTT : ∀ v, T (T v) = v := fun v => by
    rw [hT, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hXX,
      Matrix.one_mulVec]
  have hc := isCompl_ker_of_sq h2 hTT
  refine ⟨hc, ?_⟩
  obtain ⟨Vp, hVp⟩ : ∃ V : Submodule F (Fin 4 → F), V = LinearMap.ker (T - 1) := ⟨_, rfl⟩
  obtain ⟨Vm, hVm⟩ : ∃ V : Submodule F (Fin 4 → F), V = LinearMap.ker (T + 1) := ⟨_, rfl⟩
  rw [← hVp, ← hVm] at hc ⊢
  have hTp : ∀ v ∈ Vp, T v = (1 : F) • v := fun v hv => by
    rw [hVp, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    rw [one_smul, hv]
  have hTm : ∀ v ∈ Vm, T v = (-1 : F) • v := fun v hv => by
    rw [hVm, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
      add_eq_zero_iff_eq_neg] at hv
    rw [neg_one_smul, hv]
  have hdetT := CatFactsL4U4.det_eq_of_isCompl_smul hc hTp hTm
  have hdX : LinearMap.det T = 1 := by rw [hT, LinearMap.det_toLin', hdet]
  rw [hdX, one_pow, one_mul] at hdetT
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  rw [Module.finrank_fin_fun] at hsum
  have hXv : ∀ v, X *ᵥ v = T v := fun v => by rw [hT, Matrix.toLin'_apply]
  have hdp : Module.finrank F Vp ≠ 0 := by
    intro h0
    apply hm1
    have hbot : Vp = ⊥ := Submodule.finrank_eq_zero.1 h0
    have htop : Vm = ⊤ := by
      have := hc.sup_eq_top
      rwa [hbot, bot_sup_eq] at this
    have hall : ∀ v, X *ᵥ v = -v := fun v => by
      rw [hXv, hTm v (by rw [htop]; exact Submodule.mem_top), neg_one_smul]
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at this
    simpa [Matrix.neg_apply, Matrix.one_apply, Pi.single_apply, eq_comm] using this
  have hdm : Module.finrank F Vm ≠ 0 := by
    intro h0
    apply h1
    have hbot : Vm = ⊥ := Submodule.finrank_eq_zero.1 h0
    have htop : Vp = ⊤ := by
      have := hc.sup_eq_top
      rwa [hbot, sup_bot_eq] at this
    have hall : ∀ v, X *ᵥ v = v := fun v => by
      rw [hXv, hTp v (by rw [htop]; exact Submodule.mem_top), one_smul]
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at this
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this
  have hm2 : Module.finrank F Vm = 2 := by
    rcases Nat.even_or_odd (Module.finrank F Vm) with he | ho
    · obtain ⟨k, hk⟩ := he
      omega
    · exfalso
      rw [ho.neg_one_pow] at hdetT
      apply h2
      linear_combination hdetT
  exact ⟨by omega, hm2⟩

end TBlocks

namespace StabU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank TBlocks
  CFSG.LinearGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem stdHermForm_mulVec {M : Matrix (Fin 4) (Fin 4) K} (hM : (M.map h.bar)ᵀ * M = 1)
    (v w : Fin 4 → K) : stdHermForm h 4 (M *ᵥ v) (M *ᵥ w) = stdHermForm h 4 v w := by
  have e1 : ∀ x y : Fin 4 → K, stdHermForm h 4 x y = (fun i => h.bar (x i)) ⬝ᵥ y := fun x y => by
    rw [stdHermForm_apply]
    rfl
  have hM' : Mᵀ * M.map h.bar = 1 := by
    have := congrArg Matrix.transpose hM
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  rw [e1, e1, bar_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec, hM', Matrix.one_mulVec]

include h in
theorem exists_orthonormal_eigenframe (hp2 : p ≠ 2) (X : unitarySU p f K 4)
    (hXX : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (X : GL (Fin 4) K) = 1)
    (h1 : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ 1)
    (hm1 : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ -1) :
    ∃ Q : Matrix (Fin 4) (Fin 4) K, uStar h Q * Q = 1 ∧
      ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Q = Q * X1 (1 : K) := by
  classical
  have : Finite K := h.finite
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  set M := ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hM
  obtain ⟨hdet, hU⟩ := (mem_unitarySU_iff h).1 X.2
  obtain ⟨hc, hdp, hdm⟩ := eigen_data h2K hXX hdet h1 hm1
  set T := Matrix.toLin' M with hT
  obtain ⟨Vp, hVp⟩ : ∃ V : Submodule K (Fin 4 → K), V = LinearMap.ker (T - 1) := ⟨_, rfl⟩
  obtain ⟨Vm, hVm⟩ : ∃ V : Submodule K (Fin 4 → K), V = LinearMap.ker (T + 1) := ⟨_, rfl⟩
  rw [← hVp, ← hVm] at hc
  rw [← hVp] at hdp
  rw [← hVm] at hdm
  have hMp : ∀ v ∈ Vp, M *ᵥ v = v := fun v hv => by
    rw [hVp, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, hT,
      Matrix.toLin'_apply] at hv
    exact hv
  have hMm : ∀ v ∈ Vm, M *ᵥ v = -v := fun v hv => by
    rw [hVm, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
      add_eq_zero_iff_eq_neg, hT, Matrix.toLin'_apply] at hv
    exact hv
  have hsym : ∀ v w, stdHermForm h 4 v w = 0 → stdHermForm h 4 w v = 0 := by
    intro v w hvw
    rw [← (stdHermForm_isSymm h 4).eq, hvw, map_zero]
  have horth : ∀ v ∈ Vp, ∀ w ∈ Vm, stdHermForm h 4 v w = 0 := by
    intro v hv w hw
    have := stdHermForm_mulVec h hU v w
    rw [hMp v hv, hMm w hw, map_neg] at this
    have h2 : (2 : K) * stdHermForm h 4 v w = 0 := by linear_combination -this
    exact (mul_eq_zero.1 h2).resolve_left h2K
  have hsep : ∀ V W : Submodule K (Fin 4 → K), IsCompl V W →
      (∀ v ∈ V, ∀ w ∈ W, stdHermForm h 4 v w = 0) →
      ((stdHermForm h 4).domRestrict₁₂ V V).SeparatingLeft := by
    intro V W hVW horth' x hx
    apply Subtype.ext
    apply stdHermForm_separatingLeft h 4
    intro y
    have hy : y ∈ V ⊔ W := by rw [hVW.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    have e1 := hx ⟨y₁, hy₁⟩
    rw [LinearMap.domRestrict₁₂_apply] at e1
    rw [map_add, e1, horth' x x.2 y₂ hy₂, add_zero]
  obtain ⟨ep, hep⟩ := h.exists_orthonormal_basis ((stdHermForm_isSymm h 4).domRestrict Vp)
    (hsep Vp Vm hc horth)
  obtain ⟨em, hem⟩ := h.exists_orthonormal_basis ((stdHermForm_isSymm h 4).domRestrict Vm)
    (hsep Vm Vp hc.symm fun w hw v hv => hsym _ _ (horth v hv w hw))
  have i0 : 0 < Module.finrank K Vp := by omega
  have i1 : 1 < Module.finrank K Vp := by omega
  have j0 : 0 < Module.finrank K Vm := by omega
  have j1 : 1 < Module.finrank K Vm := by omega
  set e0 := ep ⟨0, i0⟩ with he0
  set e1 := ep ⟨1, i1⟩ with he1
  set f0 := em ⟨0, j0⟩ with hf0
  set f1 := em ⟨1, j1⟩ with hf1
  have g : ∀ (u v : Fin (Module.finrank K Vp)),
      stdHermForm h 4 (ep u) (ep v) = if u = v then 1 else 0 :=
    fun u v => by rw [← hep u v, LinearMap.domRestrict₁₂_apply]
  have g' : ∀ (u v : Fin (Module.finrank K Vm)),
      stdHermForm h 4 (em u) (em v) = if u = v then 1 else 0 :=
    fun u v => by rw [← hem u v, LinearMap.domRestrict₁₂_apply]
  have hne : (⟨0, i0⟩ : Fin (Module.finrank K Vp)) ≠ ⟨1, i1⟩ := by simp
  have hne' : (⟨0, j0⟩ : Fin (Module.finrank K Vm)) ≠ ⟨1, j1⟩ := by simp
  have g00 : stdHermForm h 4 e0 e0 = 1 := by rw [g]; simp
  have g01 : stdHermForm h 4 e0 e1 = 0 := by rw [g, ite_eq_right hne]
  have g10 : stdHermForm h 4 e1 e0 = 0 := by rw [g, ite_eq_right hne.symm]
  have g11 : stdHermForm h 4 e1 e1 = 1 := by rw [g]; simp
  have k00 : stdHermForm h 4 f0 f0 = 1 := by rw [g']; simp
  have k01 : stdHermForm h 4 f0 f1 = 0 := by rw [g', ite_eq_right hne']
  have k10 : stdHermForm h 4 f1 f0 = 0 := by rw [g', ite_eq_right hne'.symm]
  have k11 : stdHermForm h 4 f1 f1 = 1 := by rw [g']; simp
  have o1 : ∀ (u : Vp) (w : Vm), stdHermForm h 4 u w = 0 := fun u w => horth u u.2 w w.2
  have o2 : ∀ (u : Vp) (w : Vm), stdHermForm h 4 w u = 0 := fun u w => hsym _ _ (o1 u w)
  set col : Fin 4 → Fin 4 → K := ![e0, e1, f0, f1] with hcol
  set Q : Matrix (Fin 4) (Fin 4) K := Matrix.of fun i j => col j i with hQ
  have hQcol : ∀ j, (fun k => Q k j) = col j := fun j => rfl
  refine ⟨Q, ?_, ?_⟩
  · ext a b
    rw [uStar_mul_apply, hQcol, hQcol]
    fin_cases a <;> fin_cases b <;>
      simp [hcol, g00, g01, g10, g11, k00, k01, k10, k11, o1, o2]
  · ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    change (M *ᵥ col j) i = _
    have p0 := hMp _ e0.2
    have p1 := hMp _ e1.2
    have m0 := hMm _ f0.2
    have m1 := hMm _ f1.2
    fin_cases j <;> simp [hcol, hQ, p0, p1, m0, m1, X1, Fin.sum_univ_four]

@[expose] noncomputable def dZero (t l : K) : Matrix (Fin 2) (Fin 2) K := !![1, t / 2; l, -(t / 2) * l]

theorem uStar_bd_dZero (h2 : (2 : K) ≠ 0) {t l : K} (hl : l ^ 2 = -1) (hbl : h.bar l = l)
    (ht : h.bar t = -t) :
    uStar h (bd (dZero t l) (dZero t l)) * bd (dZero t l) (dZero t l) = t • bJ 1 1 := by
  have h2' : h.bar 2 = 2 := map_ofNat h.bar 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uStar, bd, dZero, bJ, Matrix.mul_apply, Fin.sum_univ_four, map_div₀, hbl, ht, h2'] <;>
    field_simp
  all_goals first
    | linear_combination hl
    | linear_combination (-t) * hl
    | linear_combination (-t ^ 2) * hl
    | linear_combination t * hl

include h in
theorem exists_frame_t2_U4 (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) (X : unitarySU p f K 4)
    (hXX : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (X : GL (Fin 4) K) = 1)
    (h1 : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ 1)
    (hm1 : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ -1) :
    ∃ (R : GL (Fin 4) K) (t : K), t ≠ 0 ∧ h.bar t = -t ∧
      uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1 ∧
      ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
        (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K) := by
  classical
  have : Finite K := h.finite
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨Q, hQu, hXQ⟩ := exists_orthonormal_eigenframe h hp2 X hXX h1 hm1
  obtain ⟨l, hl⟩ : ∃ l : K, l ^ 2 = -1 := by
    let : Fintype K := Fintype.ofFinite K
    have hcK : Fintype.card K % 4 = 1 := by
      rw [Fintype.card_eq_nat_card, h.card, pow_mul, Nat.pow_mod]
      rw [show p ^ 2 % 4 = 1 by
        rcases Nat.even_or_odd p with he | ho
        · exfalso
          exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two h.prime).1
            (even_iff_two_dvd.1 he)).symm
        · obtain ⟨t, rfl⟩ := ho
          ring_nf
          omega]
      simp
    obtain ⟨r, hr⟩ := (FiniteField.isSquare_neg_one_iff (F := K)).2 (by omega)
    exact ⟨r, by rw [sq, ← hr]⟩
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hl
    exact one_ne_zero (by linear_combination hl : (1 : K) = 0)
  have hbl : h.bar l = l := by
    have hNl := norm_eq_neg_one_of_sq h hq hl
    rw [UnitaryFieldData.norm] at hNl
    have e : l * (h.bar l - l) = 0 := by linear_combination hNl - hl
    exact sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_left hl0)
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Kˣ)
  set t : K := (μ : K) - h.bar μ with htdef
  have ht : h.bar t = -t := by
    rw [htdef, map_sub, h.bar_bar]
    ring
  have ht0 : t ≠ 0 := sub_ne_zero.2 (Ne.symm (bar_ne_of_generator h hμ))
  set D := bd (dZero t l) (dZero t l) with hD
  have hDD := uStar_bd_dZero h h2K hl hbl ht
  have hR1 : uStar h (Q * D) * (Q * D) = t • bJ 1 1 := by
    rw [uStar_mul]
    calc uStar h D * uStar h Q * (Q * D) = uStar h D * (uStar h Q * Q) * D := by
          simp only [Matrix.mul_assoc]
      _ = t • bJ 1 1 := by rw [hQu, Matrix.mul_one, hDD]
  have hdet : (Q * D).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hR1
    rw [det_mul, h0, mul_zero, det_smul, det_bJ, Fintype.card_fin] at this
    simp at this
    exact ht0 (pow_eq_zero_iff (by norm_num) |>.1 this.symm)
  refine ⟨GeneralLinearGroup.mkOfDetNeZero (Q * D) hdet, t, ht0, ht, ?_, ?_⟩
  · rw [GeneralLinearGroup.val_mkOfDetNeZero]
    exact hR1
  · rw [GeneralLinearGroup.val_mkOfDetNeZero, ← Matrix.mul_assoc, hXQ, Matrix.mul_assoc,
      Matrix.mul_assoc, ← bd_comm_X1]

end StabU

end CFSG.ComponentClassification.CatFactsL4U4
