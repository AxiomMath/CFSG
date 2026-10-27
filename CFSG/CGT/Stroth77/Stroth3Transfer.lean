module

public import CFSG.CGT.Stroth77.Stroth3FormII
public import CFSG.CGT.Stroth77.TorusNormalForm

public section

namespace CFSG.CGT.Stroth77

section Matrices

variable {k : Fin 3 → ℕ}

theorem Type300.compat_const (m : ℕ) (M : IntMat) : Compat (StrothTypeIndex.t300 m).k M :=
  fun i j => ⟨M i j, by fin_cases i <;> fin_cases j <;> rfl⟩

theorem matAct_smul_one (d : ℤ) (hd : Compat k (d • (1 : IntMat))) (x : Torus k) :
    matAct k (d • (1 : IntMat)) hd x = d • x := by
  have h : matAct k (d • (1 : IntMat)) hd = DistribSMul.toAddMonoidHom (Torus k) d := by
    refine torus_hom_ext _ _ fun j z => ?_
    funext i
    rw [matAct_single, DistribSMul.toAddMonoidHom_apply, Pi.smul_apply]
    by_cases hij : i = j
    · subst hij
      simp [mul_comm]
    · simp [Matrix.one_apply_ne hij, Pi.single_eq_of_ne hij]
  rw [h, DistribSMul.toAddMonoidHom_apply]

theorem matAct_injective {M M' : IntMat} (hM : Compat k M) (hM' : Compat k M') {d : ℤ}
    (hd : Odd d) (h : MatEq k (M' * M) (d • (1 : IntMat))) :
    Function.Injective (matAct k M hM) := by
  intro x y hxy
  have hd1 : Compat k (d • (1 : IntMat)) := fun i j => by
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  have key := matAct_congr (hM'.mul hM) hd1 h
  rw [matAct_mul _ _ hM' hM] at key
  have hdx : d • x = d • y := by
    rw [← matAct_smul_one d hd1, ← matAct_smul_one d hd1, ← key, AddMonoidHom.comp_apply,
      AddMonoidHom.comp_apply, hxy]
  funext i
  have hi := congrFun hdx i
  simp only [Pi.smul_apply, zsmul_eq_mul] at hi
  exact (isUnit_intCast_of_odd hd).mul_left_cancel hi

@[expose] noncomputable def torusEquivOfMat (M M' : IntMat) (hM : Compat k M) (hM' : Compat k M')
    {d : ℤ} (hd : Odd d) (h : MatEq k (M' * M) (d • (1 : IntMat))) : Torus k ≃+ Torus k :=
  AddEquiv.ofBijective (matAct k M hM)
    ⟨matAct_injective hM hM' hd h, Finite.surjective_of_injective (matAct_injective hM hM' hd h)⟩

theorem matAct_intertwine {Ψ X X₀ : IntMat} (hΨ : Compat k Ψ) (hX : Compat k X)
    (hX₀ : Compat k X₀) (h : MatEq k (Ψ * X) (X₀ * Ψ)) (x : Torus k) :
    matAct k Ψ hΨ (matAct k X hX x) = matAct k X₀ hX₀ (matAct k Ψ hΨ x) := by
  have key := matAct_congr (hΨ.mul hX) (hX₀.mul hΨ) h
  rw [matAct_mul _ _ hΨ hX, matAct_mul _ _ hX₀ hΨ] at key
  exact DFunLike.congr_fun key x

theorem val_intCast_mod_two_of_one_le {e : ℕ} (he : 1 ≤ e) (X : ℤ) :
    (((X : ZMod (2 ^ e)).val % 2 : ℕ) : ℤ) = X % 2 := by
  rw [Int.natCast_mod, ZMod.val_intCast]
  push_cast
  exact Int.emod_emod_of_dvd X (dvd_pow_self 2 (by omega))

theorem matAct_val_zero_mod_two (hk0 : 1 ≤ k 0) (M : IntMat) (hM : Compat k M)
    (h0 : Odd (M 0 0)) (h1 : Even (M 0 1)) (h2 : Even (M 0 2)) (x : Torus k) :
    ((matAct k M hM x) 0).val % 2 = (x 0).val % 2 := by
  obtain ⟨v, rfl⟩ := Torus.exists_ofInt x
  rw [matAct_ofInt, Torus.ofInt_apply, Torus.ofInt_apply]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  obtain ⟨c, hc⟩ := h2
  have e : M 0 0 * v 0 + M 0 1 * v 1 + M 0 2 * v 2 =
      v 0 + 2 * (a * v 0 + b * v 1 + c * v 2) := by
    rw [ha, hb, hc]
    ring
  have h1' := val_intCast_mod_two_of_one_le hk0 (M 0 0 * v 0 + M 0 1 * v 1 + M 0 2 * v 2)
  have h2' := val_intCast_mod_two_of_one_le hk0 (v 0)
  rw [e] at h1'
  rw [e]
  omega

theorem matAct_apply_zero_eq_zero_iff (hk : ∀ i, k i = k 0) (M : IntMat) (hM : Compat k M)
    (h0 : Odd (M 0 0)) (h1 : Even (M 0 1)) (h2 : Even (M 0 2)) {x : Torus k} (hx : x + x = 0) :
    (matAct k M hM x) 0 = 0 ↔ x 0 = 0 := by
  obtain ⟨v, rfl⟩ := Torus.exists_ofInt x
  rw [← Torus.ofInt_add, Torus.ofInt_eq_zero_iff] at hx
  rw [matAct_ofInt, Torus.ofInt_apply, Torus.ofInt_apply, ZMod.intCast_zmod_eq_zero_iff_dvd,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  push_cast
  obtain ⟨b, hb⟩ := h1
  obtain ⟨c, hc⟩ := h2
  have hx1 : (2 : ℤ) ^ k 0 ∣ v 1 + v 1 := by
    have := hx 1
    rw [hk 1] at this
    exact this
  have hx2 : (2 : ℤ) ^ k 0 ∣ v 2 + v 2 := by
    have := hx 2
    rw [hk 2] at this
    exact this
  have hcop : IsCoprime ((2 : ℤ) ^ k 0) (M 0 0) := (Int.isCoprime_two_left.mpr h0).pow_left
  have e : M 0 0 * v 0 + M 0 1 * v 1 + M 0 2 * v 2 =
      M 0 0 * v 0 + (b * (v 1 + v 1) + c * (v 2 + v 2)) := by
    rw [hb, hc]
    ring
  rw [e, dvd_add_left (dvd_add (hx1.mul_left b) (hx2.mul_left c)), hcop.dvd_mul_left_iff]

end Matrices

section Transfer

variable {τ σ : StrothTypeIndex} (ψ : Torus τ.k ≃+ Torus σ.k)

theorem inW_equiv_iff (hW : ∀ x, x + x = 0 → ((ψ x) 0 = 0 ↔ x 0 = 0)) (x : Torus τ.k) :
    InW (ψ x) ↔ InW x := by
  have h2x : ψ x + ψ x = 0 ↔ x + x = 0 := by
    rw [← map_add]
    exact map_eq_zero_iff ψ ψ.injective
  constructor
  · rintro ⟨h0, h1⟩
    have hx := h2x.mp h1
    exact ⟨(hW x hx).mp h0, hx⟩
  · rintro ⟨h0, h1⟩
    exact ⟨(hW x h1).mpr h0, h2x.mpr h1⟩

theorem VFacts.of_equiv (hσ : VFacts σ)
    (huv : ∀ x, ψ (τ.action.φuv x) = σ.action.φuv (ψ x))
    (ht : ∀ x, ψ (τ.action.φt x) = σ.action.φt (ψ x))
    (hρ : ∀ x, ψ (τ.action.φρ x) = σ.action.φρ (ψ x))
    (hpar : ∀ x, ((ψ x) 0).val % 2 = (x 0).val % 2)
    (hW : ∀ x, x + x = 0 → ((ψ x) 0 = 0 ↔ x 0 = 0)) (h2 : 2 ≤ τ.k 0)
    (hpar_u : ∀ x : Torus τ.k, ((τ.action.φu x) 0).val % 2 = (x 0).val % 2)
    (hW_u : ∀ w : Torus τ.k, InW w → (τ.action.φu w) 0 = 0) : VFacts τ where
  two_le := h2
  classify := by
    intro δ hU hT h2' hinv
    have huv' : ∀ y, ψ.symm (σ.action.φuv y) = τ.action.φuv (ψ.symm y) := fun y => by
      rw [AddEquiv.symm_apply_eq, huv, AddEquiv.apply_symm_apply]
    have ht' : ∀ y, ψ.symm (σ.action.φt y) = τ.action.φt (ψ.symm y) := fun y => by
      rw [AddEquiv.symm_apply_eq, ht, AddEquiv.apply_symm_apply]
    let δ' : Torus σ.k →+ Torus σ.k := (ψ.toAddMonoidHom.comp δ).comp ψ.symm.toAddMonoidHom
    have hδ' : ∀ y, δ' y = ψ (δ (ψ.symm y)) := fun y => rfl
    obtain ⟨α, hα, w, hw, hδw⟩ := hσ.classify δ'
      (fun y => by rw [hδ', hδ', huv', hU, huv])
      (fun y => by rw [hδ', hδ', ht', hT, ht])
      (fun y hy => by
        rw [hδ', h2' (ψ.symm y) (by rw [← map_add, hy, map_zero]),
          AddEquiv.apply_symm_apply])
      (fun y => by rw [hδ', hδ', AddEquiv.symm_apply_apply, hinv, AddEquiv.apply_symm_apply])
    refine ⟨α, hα, ψ.symm w,
      (inW_equiv_iff ψ hW _).mp (by rwa [AddEquiv.apply_symm_apply]), fun x => ?_⟩
    have hx := hδw (ψ x)
    rw [hδ', AddEquiv.symm_apply_apply] at hx
    apply ψ.injective
    rw [hx, map_add, map_zsmul, map_nsmul, AddEquiv.apply_symm_apply]
    congr 1
    exact nsmul_eq_of_mod_two hw.2 (hpar x)
  even_uv r hr := by
    rw [← hpar r]
    exact hσ.even_uv (ψ r) (by rw [← huv, ← map_add, hr, map_zero])
  even_t r hr := by
    rw [← hpar r]
    exact hσ.even_t (ψ r) (by rw [← ht, ← map_add, hr, map_zero])
  fixed z hU hT := (inW_equiv_iff ψ hW z).mp (hσ.fixed (ψ z) (by rw [← huv, hU])
    (by rw [← ht, hT]))
  par_uv x := by
    have h1 := hpar (τ.action.φuv x)
    rw [huv] at h1
    rw [← h1, hσ.par_uv, hpar]
  par_t x := by
    have h1 := hpar (τ.action.φt x)
    rw [ht] at h1
    rw [← h1, hσ.par_t, hpar]
  par_u := hpar_u
  par_ρ x := by
    have h1 := hpar (τ.action.φρ x)
    rw [hρ] at h1
    rw [← h1, hσ.par_ρ, hpar]
  W_uv w hw := ψ.injective (by rw [huv, hσ.W_uv _ ((inW_equiv_iff ψ hW w).mpr hw)])
  W_t w hw := ψ.injective (by rw [ht, hσ.W_t _ ((inW_equiv_iff ψ hW w).mpr hw)])
  W_u := hW_u
  W_ρ w hw := by
    have hw' := (inW_equiv_iff ψ hW w).mpr hw
    have h1 : InW (ψ (τ.action.φρ w)) := by
      rw [hρ]
      exact ⟨hσ.W_ρ _ hw', by rw [← map_add, hw'.2, map_zero]⟩
    exact ((inW_equiv_iff ψ hW _).mp h1).1
  W_fpf w hw hfix := by
    have h1 := hσ.W_fpf (ψ w) ((inW_equiv_iff ψ hW w).mpr hw) (by rw [← hρ, hfix])
    exact (map_eq_zero_iff ψ ψ.injective).mp h1
  sq_W v hv2 hρv := by
    have h1 : ψ v + ψ v = 0 := by rw [← map_add, hv2, map_zero]
    have h2' := hσ.sq_W (ψ v) h1 (by rw [← hρ, ← hρ, hρv, map_add])
    exact (hW v hv2).mp h2'
  W_orbit v w hv hv0 hw := by
    have h1 := hσ.W_orbit (ψ v) (ψ w) ((inW_equiv_iff ψ hW v).mpr hv)
      (fun h => hv0 ((map_eq_zero_iff ψ ψ.injective).mp h)) ((inW_equiv_iff ψ hW w).mpr hw)
    rw [← hρ, ← map_add] at h1
    rcases h1 with h | h | h | h
    · exact Or.inl ((map_eq_zero_iff ψ ψ.injective).mp h)
    · exact Or.inr (Or.inl (ψ.injective h))
    · exact Or.inr (Or.inr (Or.inl (ψ.injective h)))
    · exact Or.inr (Or.inr (Or.inr (ψ.injective h)))

theorem KillFact.of_equiv (hσ : KillFact σ)
    (huv : ∀ x, ψ (τ.action.φuv x) = σ.action.φuv (ψ x))
    (ht : ∀ x, ψ (τ.action.φt x) = σ.action.φt (ψ x))
    (hρ : ∀ x, ψ (τ.action.φρ x) = σ.action.φρ (ψ x))
    (hW : ∀ x, x + x = 0 → ((ψ x) 0 = 0 ↔ x 0 = 0)) : KillFact τ := by
  intro ruv rt d0 h1 h2 h3 h4 h5
  obtain ⟨d, w1, w2⟩ := hσ (ψ ruv) (ψ rt) (ψ d0)
    (by rw [← huv, ← map_add, h1, map_zero])
    (by rw [← ht, ← map_add, h2, map_zero])
    (by rw [← huv, ← ht, ← map_add, ← map_add, h3])
    (by rw [← huv, ← huv, ← map_add, ← hρ, h4, map_add, map_sub])
    (by rw [← hρ, h5, ← ht, map_add, map_sub])
  refine ⟨ψ.symm d, (inW_equiv_iff ψ hW _).mp ?_, (inW_equiv_iff ψ hW _).mp ?_⟩
  · rw [map_add, map_sub, huv, AddEquiv.apply_symm_apply]
    exact w1
  · rw [map_add, map_sub, ht, AddEquiv.apply_symm_apply]
    exact w2

end Transfer

end CFSG.CGT.Stroth77
