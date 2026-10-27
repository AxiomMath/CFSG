module

public import CFSG.HardMathSupport.Solomon.Coordinator.L5Lin

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Timmesfeld.LocalTwo.Torus CFSG.HardMathSupport.Solomon.Proving
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (mem_semilinearAutGroup_of_odd)

section Galois

variable {K : Type*} [Field K] {n : ℕ} (φ : K →+* K)

theorem ringEquiv_apply_eq_of_isPrimitiveRoot_five {σ : K ≃+* K} (hσ : σ ^ 5 = 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) : σ ζ = ζ := by
  have h1 : (σ ζ) ^ 5 = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨m, hm, hmζ⟩ := hζ.eq_pow_of_pow_eq_one h1
  have hk : ∀ k : ℕ, (σ ^ k) ζ = ζ ^ (m ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', pow_succ', pow_mul]
      show σ ((σ ^ k) ζ) = _
      rw [ih, map_pow, ← hmζ]
  have h5 := hk 5
  rw [hσ] at h5
  change ζ = ζ ^ m ^ 5 at h5
  have ho : orderOf ζ = 5 := hζ.eq_orderOf.symm
  rw [← pow_mod_orderOf, ho] at h5
  have hinj := hζ.pow_inj (by norm_num : 1 < 5) (Nat.mod_lt _ (by norm_num))
    (by rw [pow_one]; exact h5)
  have hm1 : m = 1 := by
    interval_cases m <;> first | rfl | (norm_num at hinj)
  rw [← hmζ, hm1, pow_one]

theorem map_diagHom_eq {v : Fin n → Kˣ} (hv : ∀ i, φ (v i : K) = v i) :
    ((diagHom v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ = (diagHom v : GL (Fin n) K) := by
  rw [diagHom_apply, coe_diagGL, Matrix.diagonal_map (map_zero φ)]
  congr 1
  funext i
  exact hv i

theorem map_swap_eq (a b : Fin n) : (Matrix.swap K a b).map φ = Matrix.swap K a b := by
  have h1 : Matrix.swap K a b = (Equiv.swap a b).toPEquiv.toMatrix := rfl
  ext i j
  rw [Matrix.map_apply, h1, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem map_sgnSwap_eq (a b : Fin n) :
    ((sgnSwap a b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ = (sgnSwap a b : GL (Fin n) K) := by
  rw [sgnSwap, Units.val_mul, Matrix.map_mul, coe_swapGL, map_swap_eq, map_diagHom_eq]
  intro i
  simp only [signVec, Function.update_apply, Pi.one_apply]
  split_ifs <;> simp

theorem sl_map_eq_self {g : SpecialLinearGroup (Fin n) K}
    (h : (g : Matrix (Fin n) (Fin n) K).map φ = g) : SpecialLinearGroup.map φ g = g := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, h]

theorem starX_eq_commutator (ζ : Kˣ) (k : Fin 3) :
    (diagHom (tvec ζ (0 : Fin 5) 4) : GL (Fin 5) K) * sgnSwap 0 (![1, 2, 3] k) *
        (diagHom (tvec ζ 0 4))⁻¹ * (sgnSwap 0 (![1, 2, 3] k))⁻¹ =
      starX ζ (0 : Fin 5) ![1, 2, 3] k := by
  have e1 := sgnSwap_conj_diag (K := K) (0 : Fin 5) (![1, 2, 3] k) (tvec ζ 0 4)⁻¹
  calc (diagHom (tvec ζ (0 : Fin 5) 4) : GL (Fin 5) K) * sgnSwap 0 (![1, 2, 3] k) *
        (diagHom (tvec ζ 0 4))⁻¹ * (sgnSwap 0 (![1, 2, 3] k))⁻¹
      = diagHom (tvec ζ (0 : Fin 5) 4) * (sgnSwap 0 (![1, 2, 3] k) *
        diagHom (tvec ζ 0 4)⁻¹ * (sgnSwap 0 (![1, 2, 3] k))⁻¹) := by
        rw [map_inv]; group
    _ = diagHom (tvec ζ (0 : Fin 5) 4 * ((tvec ζ 0 4)⁻¹ ∘ Equiv.swap 0 (![1, 2, 3] k))) := by
        rw [e1, map_mul]
    _ = starX ζ (0 : Fin 5) ![1, 2, 3] k := by
        rw [starX]
        congr 1
        funext m
        fin_cases k <;> fin_cases m <;> simp [tvec, Equiv.swap_apply_def]

end Galois

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem conj_fieldAut_fix {n : ℕ} {b : MulAut (projectiveSL n F)} {A : GL (Fin n) F}
    {σ : F ≃+* F} (hb : b = conjAut n F A * fieldAut n F σ * (conjAut n F A)⁻¹)
    {g : SpecialLinearGroup (Fin n) F} (hg : SpecialLinearGroup.map σ.toRingHom g = g) :
    b (conjAut n F A (proj n F g)) = conjAut n F A (proj n F g) := by
  rw [hb, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, fieldAut_proj, hg]

section Five

variable {Lb : Type*} [Group Lb] [Finite Lb] {Γ : Lb →* projectiveSL 5 F}

section Data

variable (hΓ : Function.Surjective Γ) (hker : Γ.ker = Subgroup.center Lb)
  (hodd : Odd (Nat.card (Subgroup.center Lb))) {β : MulAut Lb} {b : MulAut (projectiveSL 5 F)}
  (hβ : ∀ x, Γ (β x) = b (Γ x)) {A : GL (Fin 5) F} {σ : F ≃+* F}
  (hbh : b = conjAut 5 F A * fieldAut 5 F σ * (conjAut 5 F A)⁻¹)
include hΓ hker hodd hβ hbh

omit [Finite F] in
theorem conj_proj_mem_fix_of_two {g : SpecialLinearGroup (Fin 5) F}
    (hg : (g : Matrix (Fin 5) (Fin 5) F).map σ.toRingHom = g) {e : ℕ} (he : g ^ 2 ^ e = 1) :
    conjAut 5 F A (proj 5 F g) ∈ (autFix β).map Γ := by
  have hodd' : Odd (Nat.card Γ.ker) := by rw [hker]; exact hodd
  exact mem_map_autFix_of_two hΓ hker.le hβ hodd' (conj_fieldAut_fix hbh (sl_map_eq_self _ hg))
    (e := e) (by rw [← map_pow, ← map_pow, he, map_one, map_one])

theorem exists_fixTorus_projectiveSL_five {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ 5)
    (hζσ : σ (ζ : F) = ζ) :
    ∃ D : TorusData (Fin 3) 5 ↥((autFix β).map Γ),
      Nat.card (Subgroup.closure (Set.range D.X)) = 5 ^ 3 ∧
      (∀ k, ∃ x : SpecialLinearGroup (Fin 5) F,
        SpecialLinearGroup.toGL x = starX ζ (0 : Fin 5) ![1, 2, 3] k ∧
        ((D.X k : ↥((autFix β).map Γ)) : projectiveSL 5 F) = conjAut 5 F A (proj 5 F x)) ∧
      (∀ k, ∃ s : SpecialLinearGroup (Fin 5) F,
        SpecialLinearGroup.toGL s = starSw (0 : Fin 5) ![1, 2, 3] k ∧
        ((D.Sw k : ↥((autFix β).map Γ)) : projectiveSL 5 F) = conjAut 5 F A (proj 5 F s)) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hζσ' : σ ((ζ⁻¹ : Fˣ) : F) = (ζ⁻¹ : Fˣ) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hζσ]
  set c := conjAut 5 F A with hc
  set Fix := (autFix β).map Γ with hFix
  have htvecσ : ∀ (i j m : Fin 5), σ ((tvec ζ i j m : Fˣ) : F) = tvec ζ i j m := by
    intro i j m
    simp only [tvec, Function.update_apply, Pi.one_apply]
    split_ifs
    · exact hζσ'
    · exact hζσ
    · simp
  have hfixSL : ∀ g : SpecialLinearGroup (Fin 5) F,
      (g : Matrix (Fin 5) (Fin 5) F).map σ.toRingHom = g → b (c (proj 5 F g)) = c (proj 5 F g) :=
    fun g hg => conj_fieldAut_fix hbh (sl_map_eq_self _ hg)
  have hmemC : ∀ g₁ g₂ : SpecialLinearGroup (Fin 5) F,
      (g₁ : Matrix (Fin 5) (Fin 5) F).map σ.toRingHom = g₁ →
      (g₂ : Matrix (Fin 5) (Fin 5) F).map σ.toRingHom = g₂ →
        c (proj 5 F (g₁ * g₂ * g₁⁻¹ * g₂⁻¹)) ∈ Fix := by
    intro g₁ g₂ h₁ h₂
    have := mem_map_autFix_of_commutator hΓ hker.le hβ (hfixSL g₁ h₁) (hfixSL g₂ h₂)
    simpa only [map_mul, map_inv] using this
  set M : Subgroup (SpecialLinearGroup (Fin 5) F) :=
    Fix.comap (c.toMonoidHom.comp (proj 5 F)) with hM
  have hmemM : ∀ g, g ∈ M ↔ c (proj 5 F g) ∈ Fix := fun g => Iff.rfl
  let ι : M →* GL (Fin 5) F := SpecialLinearGroup.toGL.comp M.subtype
  have hι : Function.Injective ι :=
    SpecialLinearGroup.toGL_injective.comp (Subgroup.subtype_injective _)
  let π : M →* Fix := (c.toMonoidHom.comp ((proj 5 F).comp M.subtype)).codRestrict Fix
    (fun g => g.2)
  have hπapply : ∀ g : M, ((π g : Fix) : projectiveSL 5 F) = c (proj 5 F g) := fun g => rfl
  have hπ1 : ∀ g : M, π g = 1 → proj 5 F (g : SpecialLinearGroup (Fin 5) F) = 1 := by
    intro g hg
    have h1 : c (proj 5 F (g : SpecialLinearGroup (Fin 5) F)) = 1 := by
      rw [← hπapply, hg]
      rfl
    rwa [map_eq_one_iff _ c.injective] at h1
  have hπ : ∀ g : M, π g = 1 → ∃ a : Fˣ, ι g = GeneralLinearGroup.scalar (Fin 5) a :=
    fun g hg => proj_ker_scalar _ (hπ1 g hg)
  have hdetT : ((diagHom (tvec ζ (0 : Fin 5) 4) : GL (Fin 5) F) :
      Matrix (Fin 5) (Fin 5) F).det = 1 := det_starX (r := 1) ζ (d := fun _ => 4) (by decide) 0
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 (mem_range_toGL_of_det hdetT)
  have hyσ : (y : Matrix (Fin 5) (Fin 5) F).map σ.toRingHom = y := by
    have := map_diagHom_eq σ.toRingHom (v := tvec ζ (0 : Fin 5) 4) (fun i => htvecσ 0 4 i)
    rw [← hy] at this
    exact this
  have hd : ∀ k : Fin 3, (0 : Fin 5) ≠ ![1, 2, 3] k := by decide
  have hsw : ∀ k : Fin 3, ∃ w : SpecialLinearGroup (Fin 5) F,
      SpecialLinearGroup.toGL w = starSw (0 : Fin 5) ![1, 2, 3] k ∧
        (w : Matrix (Fin 5) (Fin 5) F).map σ.toRingHom = w ∧ w ^ 2 ^ 2 = 1 := by
    intro k
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.1 (mem_range_toGL_of_det (F := F)
      (det_starSw (d := ![1, 2, 3]) hd k))
    refine ⟨w, hw, ?_, ?_⟩
    · have := map_sgnSwap_eq σ.toRingHom (K := F) (0 : Fin 5) (![1, 2, 3] k)
      rw [starSw] at hw
      rw [← hw] at this
      exact this
    · apply SpecialLinearGroup.toGL_injective
      rw [map_pow, hw, map_one, starSw]
      exact sgnSwap_pow_four _ _
  choose w hw hwσ hw4 using hsw
  have hcommX : ∀ k : Fin 3, SpecialLinearGroup.toGL (y * w k * y⁻¹ * (w k)⁻¹) =
      starX ζ (0 : Fin 5) ![1, 2, 3] k := by
    intro k
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy, hw k, starSw]
    exact starX_eq_commutator ζ k
  have hmemX : ∀ k, starX ζ (0 : Fin 5) ![1, 2, 3] k ∈ ι.range := by
    intro k
    refine ⟨⟨y * w k * y⁻¹ * (w k)⁻¹, (hmemM _).2 (hmemC y (w k) hyσ (hwσ k))⟩, ?_⟩
    exact hcommX k
  have hmemS : ∀ k, starSw (0 : Fin 5) ![1, 2, 3] k ∈ ι.range := by
    intro k
    exact ⟨⟨w k, (hmemM _).2 (conj_proj_mem_fix_of_two hΓ hker hodd hβ hbh (hwσ k) (hw4 k))⟩,
      hw k⟩
  obtain ⟨D, hcard, hX, hS⟩ := exists_torusData_star hζ ι hι π hπ 0 4 ![1, 2, 3] (by decide)
    hd (by decide) (by decide) hmemX hmemS
  refine ⟨D, hcard, fun k => ?_, fun k => ?_⟩
  · obtain ⟨x, hx, hxk⟩ := hX k
    exact ⟨(x : SpecialLinearGroup (Fin 5) F), hx, by rw [hxk]; exact hπapply x⟩
  · obtain ⟨s, hs, hsk⟩ := hS k
    exact ⟨(s : SpecialLinearGroup (Fin 5) F), hs, by rw [hsk]; exact hπapply s⟩

end Data

theorem exists_descent_projectiveSL_five {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) [CharP F ℓ]
    (hK : Nat.card F = ℓ ^ f) (h5 : 5 ∣ Nat.card F - 1) {b : MulAut (projectiveSL 5 F)}
    (hbD : b ∉ linearAutGroup 5 F) (hb5 : b ^ 5 = 1) :
    ∃ (A : GL (Fin 5) F) (σ : F ≃+* F) (ζ : Fˣ),
      b = conjAut 5 F A * fieldAut 5 F σ * (conjAut 5 F A)⁻¹ ∧ IsPrimitiveRoot ζ 5 ∧
        σ (ζ : F) = ζ ∧ σ ^ 5 = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hb1 : b ≠ 1 := fun h => hbD (h ▸ Subgroup.one_mem _)
  have hbo : orderOf b = 5 := orderOf_eq_prime hb5 hb1
  have hbE : b ∈ semilinearAutGroup 5 F :=
    mem_semilinearAutGroup_of_odd (by norm_num) (by rw [hbo]; decide)
  obtain ⟨-, σ, hσ, ⟨h, hh, hbh⟩, -⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.higher_linear_prime_semilinear_field_descent'
      hℓ hf (by norm_num) hK Nat.prime_five b hbE hbD hbo
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1 hh
  have hσ5 : σ ^ 5 = 1 := hσ ▸ pow_orderOf_eq_one σ
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_five_of_dvd h5
  exact ⟨A, σ, ζ, hbh, hζ,
    ringEquiv_apply_eq_of_isPrimitiveRoot_five hσ5 (IsPrimitiveRoot.coe_units_iff.2 hζ), hσ5⟩

theorem hasTorusFixed_three_projectiveSL_five (hΓ : Function.Surjective Γ)
    (hker : Γ.ker = Subgroup.center Lb) (hodd : Odd (Nat.card (Subgroup.center Lb)))
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) [CharP F ℓ] (hK : Nat.card F = ℓ ^ f)
    (h5 : 5 ∣ Nat.card F - 1) (h2 : ringChar F ≠ 2) {β : MulAut Lb}
    {b : MulAut (projectiveSL 5 F)} (hβ : ∀ x, Γ (β x) = b (Γ x))
    (hbD : b ∉ linearAutGroup 5 F) (hb5 : b ^ 5 = 1) : HasTorusFixed 5 3 Lb β := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨A, σ, ζ, hbh, hζ, hζσ, -⟩ := exists_descent_projectiveSL_five hℓ hf hK h5 hbD hb5
  have hneg : (-1 : F) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two h2
  obtain ⟨D, hcard, hX, hS⟩ := exists_fixTorus_projectiveSL_five hΓ hker hodd hβ hbh hζ hζσ
  have hdetN : ((diagHom (negFourVec (F := F)) : GL (Fin 5) F) :
      Matrix (Fin 5) (Fin 5) F).det = 1 := by
    rw [diagHom_apply, det_diagGL]
    simp [negFourVec, Fin.prod_univ_five]
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.1 (mem_range_toGL_of_det hdetN)
  have htσ : (t : Matrix (Fin 5) (Fin 5) F).map σ.toRingHom = t := by
    have := map_diagHom_eq σ.toRingHom (v := negFourVec (F := F)) (fun i => by
      fin_cases i <;> simp [negFourVec])
    rw [← ht] at this
    exact this
  have ht2 : t ^ 2 ^ 1 = 1 := by
    apply SpecialLinearGroup.toGL_injective
    rw [map_pow, ht, map_one, pow_one, ← map_pow]
    have : negFourVec (F := F) ^ 2 = 1 := by
      funext i
      fin_cases i <;> simp [negFourVec]
    rw [this, map_one]
  set T : ↥((autFix β).map Γ) :=
    ⟨conjAut 5 F A (proj 5 F t), conj_proj_mem_fix_of_two hΓ hker hodd hβ hbh htσ ht2⟩ with hT
  have hcommP : ∀ g : SpecialLinearGroup (Fin 5) F, Commute (SpecialLinearGroup.toGL t)
      (SpecialLinearGroup.toGL g) → ∀ y : ↥((autFix β).map Γ),
        (y : projectiveSL 5 F) = conjAut 5 F A (proj 5 F g) → Commute T y := by
    intro g hg y hy
    apply Subtype.ext
    show conjAut 5 F A (proj 5 F t) * (y : projectiveSL 5 F) =
      (y : projectiveSL 5 F) * conjAut 5 F A (proj 5 F t)
    rw [hy, ← map_mul, ← map_mul, ← map_mul, ← map_mul, (commute_of_toGL hg).eq]
  refine hasTorusFixed_of_fixData Nat.prime_five hker hodd β D hcard (T := T) ?_
    ⟨1, Subtype.ext (by
      show (conjAut 5 F A (proj 5 F t)) ^ 2 ^ 1 = 1
      rw [← map_pow, ← map_pow, ht2, map_one, map_one])⟩ ?_ ?_
  · intro h1
    have h1' : conjAut 5 F A (proj 5 F t) = 1 := congrArg Subtype.val h1
    rw [map_eq_one_iff _ (conjAut 5 F A).injective] at h1'
    obtain ⟨a, ha⟩ := proj_ker_scalar _ h1'
    rw [ht] at ha
    have h0 := congrArg (fun g : GL (Fin 5) F => (g : Matrix (Fin 5) (Fin 5) F) 0 0) ha
    have h4 := congrArg (fun g : GL (Fin 5) F => (g : Matrix (Fin 5) (Fin 5) F) 4 4) ha
    simp [diagHom_apply, coe_diagGL, negFourVec, GeneralLinearGroup.coe_scalar] at h0 h4
    exact hneg (h0.trans h4.symm)
  · intro k
    obtain ⟨x, hx, hxk⟩ := hX k
    refine hcommP x ?_ _ hxk
    rw [ht, hx, starX]
    exact (Commute.all _ _).map diagHom
  · intro k
    obtain ⟨s, hs, hsk⟩ := hS k
    refine hcommP s ?_ _ hsk
    rw [ht, hs, starSw]
    refine (commute_sgnSwap_diag (comp_swap_eq_of_eq ?_)).symm
    fin_cases k <;> simp [negFourVec]

end Five

end CFSG.HardMathSupport.Solomon.Coordinator
