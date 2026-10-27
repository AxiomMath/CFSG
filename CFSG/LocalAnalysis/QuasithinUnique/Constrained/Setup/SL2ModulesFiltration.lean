module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesSplit
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups

section Basic

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {V : Type*} [AddCommGroup V] [Module k V]

structure IsFrobFiltration (n : ℕ) (ρ : Representation k SL(2, F) V) (r : ℕ)
    (M : ℕ → Submodule k V) : Prop where
  zero : M 0 = ⊥
  top : M r = ⊤
  mono : ∀ j, M j ≤ M (j + 1)
  inv : ∀ j g, ∀ v ∈ M j, ρ g v ∈ M j
  factor : ∀ j < r, M j = M (j + 1) ∨ ∃ J : Finset ℕ, (∀ i ∈ J, i < n) ∧
    ∃ f : V →ₗ[k] ((J → Fin 2) → k), (∀ t, ∃ v ∈ M (j + 1), f v = t) ∧
      (∀ v ∈ M (j + 1), (f v = 0 ↔ v ∈ M j)) ∧
      ∀ g, ∀ v ∈ M (j + 1), f (ρ g v) = frobTensor F k J g (f v)

theorem IsFrobFiltration.map_equiv {V' : Type*} [AddCommGroup V'] [Module k V'] {n : ℕ}
    {ρ : Representation k SL(2, F) V} {ρ' : Representation k SL(2, F) V'} (Ψ : V ≃ₗ[k] V')
    (hΨ : ∀ g v, Ψ (ρ g v) = ρ' g (Ψ v)) {r : ℕ} {M : ℕ → Submodule k V}
    (h : IsFrobFiltration n ρ r M) :
    IsFrobFiltration n ρ' r (fun j => (M j).map (Ψ : V →ₗ[k] V')) := by
  have hmem : ∀ (p : Submodule k V) (v : V), Ψ v ∈ p.map (Ψ : V →ₗ[k] V') ↔ v ∈ p := fun p v => by
    constructor
    · rintro ⟨u, hu, huv⟩
      rwa [← Ψ.injective huv]
    · exact fun hv => ⟨v, hv, rfl⟩
  refine ⟨?_, ?_, fun j => Submodule.map_mono (h.mono j), ?_, ?_⟩
  · simp only [h.zero, Submodule.map_bot]
  · simp only [h.top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr Ψ.surjective
  · rintro j g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, h.inv j g v hv, hΨ g v⟩
  · intro j hj
    rcases h.factor j hj with heq | ⟨J, hJ, f, hsurj, hker, hequi⟩
    · exact Or.inl (by simp only [heq])
    · refine Or.inr ⟨J, hJ, f.comp (Ψ.symm : V' →ₗ[k] V), fun t => ?_, fun v' hv' => ?_,
        fun g v' hv' => ?_⟩
      · obtain ⟨v, hv, hfv⟩ := hsurj t
        refine ⟨Ψ v, ⟨v, hv, rfl⟩, ?_⟩
        simp [hfv]
      · obtain ⟨v, hv, rfl⟩ := hv'
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        have : Ψ v ∈ (M j).map (Ψ : V →ₗ[k] V') ↔ v ∈ M j := hmem (M j) v
        rw [hker v hv, ← this]
      · obtain ⟨v, hv, rfl⟩ := hv'
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        have h1 : ρ' g (Ψ v) = Ψ (ρ g v) := (hΨ g v).symm
        rw [h1, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
        exact hequi g v hv

theorem IsFrobFiltration.of_equiv {n : ℕ} {ρ : Representation k SL(2, F) V} {J : Finset ℕ}
    (hJ : ∀ i ∈ J, i < n) (Φ : V ≃ₗ[k] ((J → Fin 2) → k))
    (hΦ : ∀ g v, Φ (ρ g v) = frobTensor F k J g (Φ v)) :
    IsFrobFiltration n ρ 1 (fun j => if j = 0 then ⊥ else ⊤) := by
  refine ⟨by simp, by simp, fun j => ?_, fun j g v hv => ?_, fun j hj => ?_⟩
  · by_cases h : j = 0 <;> simp [h]
  · by_cases h : j = 0
    · simp only [h, ite_true, Submodule.mem_bot] at hv ⊢
      rw [hv, map_zero]
    · simp only [h, ite_false]
      trivial
  · have hj0 : j = 0 := by omega
    subst hj0
    refine Or.inr ⟨J, hJ, (Φ : V →ₗ[k] ((J → Fin 2) → k)), fun t => ⟨Φ.symm t, ?_, ?_⟩, fun v _ => ?_,
      fun g v _ => hΦ g v⟩
    · simp
    · simp
    · simp only [ite_true, Submodule.mem_bot]
      exact ⟨fun h => Φ.injective (by simpa using h), fun h => by rw [h, map_zero]⟩

end Basic

section Glue

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {V V₁ V₂ V₃ : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]

theorem IsFrobFiltration.glue3 {n : ℕ} {ρ : Representation k SL(2, F) V}
    {ρ₁ : Representation k SL(2, F) V₁} {ρ₂ : Representation k SL(2, F) V₂}
    {ρ₃ : Representation k SL(2, F) V₃}
    (Z : V₁ →ₗ[k] V) (pZ : V →ₗ[k] V₁) (S : V₂ →ₗ[k] V) (pS : V →ₗ[k] V₂) (P : V →ₗ[k] V₃)
    (hpZ : ∀ u, pZ (Z u) = u) (hpS : ∀ w, pS (S w) = w) (hpSZ : ∀ u, pS (Z u) = 0)
    (hZ : ∀ g u, ρ g (Z u) = Z (ρ₁ g u)) (hS : ∀ g w, ∃ u, ρ g (S w) = S (ρ₂ g w) + Z u)
    (hP : ∀ g v, P (ρ g v) = ρ₃ g (P v)) (hPs : Function.Surjective P)
    (hPZ : ∀ u, P (Z u) = 0) (hPS : ∀ w, P (S w) = 0)
    (hker : ∀ v, P v = 0 → ∃ u w, v = Z u + S w)
    {r₁ r₂ r₃ : ℕ} {C₁ : ℕ → Submodule k V₁} {C₂ : ℕ → Submodule k V₂}
    {C₃ : ℕ → Submodule k V₃}
    (h₁ : IsFrobFiltration n ρ₁ r₁ C₁) (h₂ : IsFrobFiltration n ρ₂ r₂ C₂)
    (h₃ : IsFrobFiltration n ρ₃ r₃ C₃) :
    ∃ M : ℕ → Submodule k V, IsFrobFiltration n ρ (r₁ + r₂ + r₃) M := by
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Submodule k V, ∀ j, A j = (C₁ j).map Z := ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → Submodule k V, ∀ j, B j = LinearMap.range Z ⊔ (C₂ j).map S :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ → Submodule k V, ∀ j, D j = (C₃ j).comap P := ⟨_, fun _ => rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ → Submodule k V, ∀ j, M j =
      if j ≤ r₁ then A j else if j ≤ r₁ + r₂ then B (j - r₁) else D (j - r₁ - r₂) :=
    ⟨_, fun _ => rfl⟩
  have hmemA : ∀ j v, v ∈ A j ↔ ∃ u ∈ C₁ j, Z u = v := fun j v => by
    rw [hA, Submodule.mem_map]
  have hmemB : ∀ j v, v ∈ B j ↔ ∃ u w, w ∈ C₂ j ∧ v = Z u + S w := fun j v => by
    rw [hB, Submodule.mem_sup]
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, _, ⟨w, hw, rfl⟩, hsum⟩
      exact ⟨u, w, hw, hsum.symm⟩
    · rintro ⟨u, w, hw, rfl⟩
      exact ⟨Z u, ⟨u, rfl⟩, S w, ⟨w, hw, rfl⟩, rfl⟩
  have hmemD : ∀ j v, v ∈ D j ↔ P v ∈ C₃ j := fun j v => by
    rw [hD, Submodule.mem_comap]
  have hpSv : ∀ u w, pS (Z u + S w) = w := fun u w => by
    rw [map_add, hpSZ, hpS, zero_add]
  have hA_r1 : A r₁ = LinearMap.range Z := by rw [hA, h₁.top, Submodule.map_top]
  have hB_0 : B 0 = LinearMap.range Z := by
    rw [hB, h₂.zero, Submodule.map_bot, sup_bot_eq]
  have hB_r2 : B r₂ = LinearMap.ker P := by
    ext v
    rw [hmemB]
    constructor
    · rintro ⟨u, w, -, rfl⟩
      rw [LinearMap.mem_ker, map_add, hPZ, hPS, add_zero]
    · intro hv
      obtain ⟨u, w, rfl⟩ := hker v (LinearMap.mem_ker.mp hv)
      exact ⟨u, w, by rw [h₂.top]; trivial, rfl⟩
  have hD_0 : D 0 = LinearMap.ker P := by rw [hD, h₃.zero, Submodule.comap_bot]
  have hD_top : D r₃ = ⊤ := by rw [hD, h₃.top, Submodule.comap_top]
  have hMA : ∀ j, j ≤ r₁ → M j = A j := fun j h => by rw [hM, ite_eq_left h]
  have hMB : ∀ j, r₁ ≤ j → j ≤ r₁ + r₂ → M j = B (j - r₁) := by
    intro j h1 h2
    by_cases h : j ≤ r₁
    · have : j = r₁ := le_antisymm h h1
      subst this
      rw [hM, ite_eq_left le_rfl, hA_r1, Nat.sub_self, hB_0]
    · rw [hM, ite_eq_right h, ite_eq_left h2]
  have hMD : ∀ j, r₁ + r₂ ≤ j → M j = D (j - r₁ - r₂) := by
    intro j h
    by_cases h1 : j ≤ r₁
    · have hr2 : r₂ = 0 := by omega
      have hj : j = r₁ := by omega
      subst hr2
      subst hj
      have e : j - j - 0 = 0 := by omega
      rw [hM, ite_eq_left le_rfl, hA_r1, e, hD_0, ← hB_r2, hB_0]
    · by_cases h2 : j ≤ r₁ + r₂
      · have e1 : j - r₁ = r₂ := by omega
        have e2 : j - r₁ - r₂ = 0 := by omega
        rw [hM, ite_eq_right h1, ite_eq_left h2, e2, e1, hB_r2, hD_0]
      · rw [hM, ite_eq_right h1, ite_eq_right h2]
  have hAinv : ∀ j g, ∀ v ∈ A j, ρ g v ∈ A j := by
    intro j g v hv
    rw [hmemA] at hv ⊢
    obtain ⟨u, hu, rfl⟩ := hv
    exact ⟨ρ₁ g u, h₁.inv j g u hu, (hZ g u).symm⟩
  have hBinv : ∀ j g, ∀ v ∈ B j, ρ g v ∈ B j := by
    intro j g v hv
    rw [hmemB] at hv ⊢
    obtain ⟨u, w, hw, rfl⟩ := hv
    obtain ⟨u', hu'⟩ := hS g w
    refine ⟨ρ₁ g u + u', ρ₂ g w, h₂.inv j g w hw, ?_⟩
    simp only [map_add, hZ g u, hu']
    abel
  have hDinv : ∀ j g, ∀ v ∈ D j, ρ g v ∈ D j := by
    intro j g v hv
    rw [hmemD] at hv ⊢
    rw [hP]
    exact h₃.inv j g _ hv
  refine ⟨M, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hMA 0 (Nat.zero_le _), hA, h₁.zero, Submodule.map_bot]
  · rw [hMD (r₁ + r₂ + r₃) (by omega), show r₁ + r₂ + r₃ - r₁ - r₂ = r₃ by omega, hD_top]
  · intro j
    by_cases hj1 : j + 1 ≤ r₁
    · rw [hMA j (by omega), hMA (j + 1) hj1, hA, hA]
      exact Submodule.map_mono (h₁.mono j)
    · have hr1 : r₁ ≤ j := by omega
      by_cases hj2 : j + 1 ≤ r₁ + r₂
      · rw [hMB j hr1 (by omega), hMB (j + 1) (by omega) hj2, hB, hB]
        have : j + 1 - r₁ = (j - r₁) + 1 := by omega
        rw [this]
        exact sup_le_sup_left (Submodule.map_mono (h₂.mono _)) _
      · have hr2 : r₁ + r₂ ≤ j := by omega
        rw [hMD j hr2, hMD (j + 1) (by omega), hD, hD]
        have : j + 1 - r₁ - r₂ = (j - r₁ - r₂) + 1 := by omega
        rw [this]
        exact Submodule.comap_mono (h₃.mono _)
  · intro j g v hv
    by_cases h1 : j ≤ r₁
    · rw [hMA j h1] at hv ⊢
      exact hAinv j g v hv
    · by_cases h2 : j ≤ r₁ + r₂
      · rw [hMB j (by omega) h2] at hv ⊢
        exact hBinv _ g v hv
      · rw [hMD j (by omega)] at hv ⊢
        exact hDinv _ g v hv
  · intro j hj
    by_cases hj1 : j + 1 ≤ r₁
    · rw [hMA j (by omega), hMA (j + 1) hj1]
      rcases h₁.factor j (by omega) with heq | ⟨J, hJ, f, hs, hk, he⟩
      · left
        rw [hA, hA, heq]
      · right
        refine ⟨J, hJ, f.comp pZ, ?_, ?_, ?_⟩
        · intro t
          obtain ⟨u, hu, hfu⟩ := hs t
          refine ⟨Z u, (hmemA _ _).mpr ⟨u, hu, rfl⟩, ?_⟩
          simp [hpZ, hfu]
        · intro v hv
          obtain ⟨u, hu, rfl⟩ := (hmemA _ _).mp hv
          simp only [LinearMap.comp_apply, hpZ]
          rw [hk u hu, hmemA]
          constructor
          · intro hu'
            exact ⟨u, hu', rfl⟩
          · rintro ⟨u', hu', hZu⟩
            have : u' = u := by simpa [hpZ] using congrArg pZ hZu
            rw [← this]
            exact hu'
        · intro g v hv
          obtain ⟨u, hu, rfl⟩ := (hmemA _ _).mp hv
          simp only [LinearMap.comp_apply, hZ, hpZ]
          exact he g u hu
    · have hr1 : r₁ ≤ j := by omega
      by_cases hj2 : j + 1 ≤ r₁ + r₂
      · rw [hMB j hr1 (by omega), hMB (j + 1) (by omega) hj2]
        have hidx : j + 1 - r₁ = (j - r₁) + 1 := by omega
        rw [hidx]
        rcases h₂.factor (j - r₁) (by omega) with heq | ⟨J, hJ, f, hs, hk, he⟩
        · left
          rw [hB, hB, heq]
        · right
          refine ⟨J, hJ, f.comp pS, ?_, ?_, ?_⟩
          · intro t
            obtain ⟨w, hw, hfw⟩ := hs t
            refine ⟨S w, (hmemB _ _).mpr ⟨0, w, hw, by rw [map_zero, zero_add]⟩, ?_⟩
            simp [hpS, hfw]
          · intro v hv
            obtain ⟨u, w, hw, rfl⟩ := (hmemB _ _).mp hv
            simp only [LinearMap.comp_apply, hpSv]
            rw [hk w hw, hmemB]
            constructor
            · intro hw'
              exact ⟨u, w, hw', rfl⟩
            · rintro ⟨u', w', hw', hsum⟩
              have : w = w' := by rw [← hpSv u w, hsum, hpSv]
              rw [this]
              exact hw'
          · intro g v hv
            obtain ⟨u, w, hw, rfl⟩ := (hmemB _ _).mp hv
            obtain ⟨u'', hu''⟩ := hS g w
            simp only [LinearMap.comp_apply]
            have : ρ g (Z u + S w) = Z (ρ₁ g u + u'') + S (ρ₂ g w) := by
              simp only [map_add, hZ g u, hu'']
              abel
            rw [this, hpSv, hpSv]
            exact he g w hw
      · have hr2 : r₁ + r₂ ≤ j := by omega
        rw [hMD j hr2, hMD (j + 1) (by omega)]
        have hidx : j + 1 - r₁ - r₂ = (j - r₁ - r₂) + 1 := by omega
        rw [hidx]
        rcases h₃.factor (j - r₁ - r₂) (by omega) with heq | ⟨J, hJ, f, hs, hk, he⟩
        · left
          rw [hD, hD, heq]
        · right
          refine ⟨J, hJ, f.comp P, ?_, ?_, ?_⟩
          · intro t
            obtain ⟨c, hc, hfc⟩ := hs t
            obtain ⟨v, hv⟩ := hPs c
            refine ⟨v, (hmemD _ _).mpr (by rw [hv]; exact hc), ?_⟩
            simp [hv, hfc]
          · intro v hv
            have hv' := (hmemD _ _).mp hv
            simp only [LinearMap.comp_apply]
            rw [hk _ hv', hmemD]
          · intro g v hv
            have hv' := (hmemD _ _).mp hv
            simp only [LinearMap.comp_apply, hP]
            exact he g _ hv'

end Glue

section Tensor

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {ι : Type*}

omit [Algebra F k] [CharP k 2] in
def projZ : ((Option (Option ι) → Fin 2) → k) →ₗ[k] ((ι → Fin 2) → k) where
  toFun v y := v (optCons 0 (optCons 1 y))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Algebra F k] [CharP k 2] in
def projS : ((Option (Option ι) → Fin 2) → k) →ₗ[k] ((Option ι → Fin 2) → k) where
  toFun v x := v (optCons (x none) (optCons (x none) (fun z => x (some z))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Algebra F k] [CharP k 2] in
theorem projZ_liftZ (u : (ι → Fin 2) → k) : projZ (liftZ u) = u := by
  funext y
  show liftZ u (optCons 0 (optCons 1 y)) = u y
  rw [liftZ_apply, ite_eq_left (by decide)]

omit [Algebra F k] [CharP k 2] in
theorem projS_liftS (w : (Option ι → Fin 2) → k) : projS (liftS w) = w := by
  funext x
  show liftS w (optCons (x none) (optCons (x none) (fun z => x (some z)))) = w x
  rw [liftS_apply, ite_eq_left rfl]
  congr 1
  funext o
  cases o <;> rfl

omit [Algebra F k] [CharP k 2] in
theorem projS_liftZ (u : (ι → Fin 2) → k) : projS (liftZ u) = 0 := by
  funext x
  show liftZ u (optCons (x none) (optCons (x none) (fun z => x (some z)))) = 0
  rw [liftZ_apply, ite_eq_right (fun h => h rfl)]

omit [Algebra F k] in
theorem projQ_liftZ (u : (ι → Fin 2) → k) : projQ (liftZ u) = 0 := by
  funext y
  rw [projQ_apply, liftZ_apply, liftZ_apply, ite_eq_left (by decide), ite_eq_left (by decide)]
  exact CharTwo.add_self_eq_zero (u y)

omit [Algebra F k] [CharP k 2] in
theorem projQ_liftS (w : (Option ι → Fin 2) → k) : projQ (liftS w) = 0 := by
  funext y
  rw [projQ_apply, liftS_apply, liftS_apply, ite_eq_right (by decide), ite_eq_right (by decide)]
  exact add_zero 0

theorem exists_equiv_of_injective_mod [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n)
    (hn : 0 < n) {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → ℕ)
    (hinj : Function.Injective (fun i => e i % n)) :
    ∃ (J : Finset ℕ) (_ : ∀ i ∈ J, i < n) (Φ : ((ι → Fin 2) → k) ≃ₗ[k] ((J → Fin 2) → k)),
      ∀ g v, Φ (tensorRep F k e g v) = frobTensor F k J g (Φ v) := by
  let e' : ι → ℕ := fun i => e i % n
  have htw : ∀ g, tensorRep F k e' g = tensorRep F k e g := by
    intro g
    simp only [tensorRep, MonoidHom.coe_mk, OneHom.coe_mk]
    congr 1
    ext x' x
    simp only [tmatE, e']
    exact Finset.prod_congr rfl fun i _ => by rw [twistMat_mod hF]
  let J : Finset ℕ := Finset.univ.image e'
  have hJn : ∀ i ∈ J, i < n := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    exact Nat.mod_lt _ hn
  let τ : ι ≃ J := Equiv.ofBijective
    (fun i => ⟨e' i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
    ⟨fun i j h => hinj (congrArg Subtype.val h), fun ⟨j, hj⟩ => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨i, rfl⟩⟩
  let Φ : (tensorRep F k e').Equiv (frobTensor F k J) :=
    reindexEquiv τ e' (fun j : J => (j : ℕ)) (fun i => rfl)
  refine ⟨J, hJn, Φ.toLinearEquiv, fun g v => ?_⟩
  rw [← htw g]
  exact equiv_apply Φ g v

theorem exists_filtration [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n) :
    ∀ (r : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = r → ∀ e : ι → ℕ,
      ∃ (s : ℕ) (M : ℕ → Submodule k ((ι → Fin 2) → k)),
        IsFrobFiltration n (tensorRep F k e) s M := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exfalso
      have := Fintype.one_lt_card (α := F)
      rw [hF] at this
      simp at this
    · exact h
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro ι _ _ hcard e
    by_cases hinj : Function.Injective (fun i => e i % n)
    · obtain ⟨J, hJn, Φ, hΦ⟩ := exists_equiv_of_injective_mod (k := k) hF hn e hinj
      exact ⟨1, _, IsFrobFiltration.of_equiv hJn Φ hΦ⟩
    · simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i, j, hne, hij⟩ := hinj
      obtain ⟨ι', _, _, σι, hσ1, hσ2, hc⟩ := exists_equiv_option_option hij
      let e'' : Option (Option ι') → ℕ := fun o => e (σι o)
      let Ψ : (tensorRep F k e'').Equiv (tensorRep F k e) :=
        reindexEquiv σι e'' e (fun o => rfl)
      have hcc : ∀ g : SL(2, F), twistMat k (e'' none) g = twistMat k (e'' (some none)) g := by
        intro g
        show twistMat k (e (σι none)) g = twistMat k (e (σι (some none))) g
        rw [hσ1, hσ2, ← twistMat_mod hF (e i) g, ← twistMat_mod hF (e j) g]
        rw [hne]
      obtain ⟨s₁, C₁, h₁⟩ := ih (Fintype.card ι') (by omega) ι' rfl
        (fun z => e'' (some (some z)))
      obtain ⟨s₂, C₂, h₂⟩ := ih (Fintype.card (Option ι')) (by rw [Fintype.card_option]; omega)
        (Option ι') rfl (succHead e'')
      obtain ⟨M'', hM''⟩ := IsFrobFiltration.glue3 (ρ := tensorRep F k e'')
        (ρ₁ := tensorRep F k (fun z => e'' (some (some z)))) (ρ₂ := tensorRep F k (succHead e''))
        (ρ₃ := tensorRep F k (fun z => e'' (some (some z))))
        liftZ projZ liftS projS projQ projZ_liftZ projS_liftS projS_liftZ
        (fun g u => tensorRep_liftZ e'' hcc g u)
        (fun g w => ⟨_, sub_eq_iff_eq_add'.mp (tensorRep_liftS e'' hcc g w)⟩)
        (fun g v => tensorRep_projQ e'' hcc g v) (fun v => ⟨sectT v, projQ_sectT v⟩)
        projQ_liftZ projQ_liftS
        (fun v hv => by
          obtain ⟨_, ⟨u, rfl⟩, _, ⟨w, rfl⟩, hsum⟩ := Submodule.mem_sup.mp (ker_projQ_le v hv)
          exact ⟨u, w, hsum.symm⟩)
        h₁ h₂ h₁
      exact ⟨s₁ + s₂ + s₁, _, hM''.map_equiv Ψ.toLinearEquiv (fun g v => equiv_apply Ψ g v)⟩

theorem tensorRep_filtration [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n) {ι : Type}
    [Fintype ι] [DecidableEq ι] (e : ι → ℕ) :
    ∃ (r : ℕ) (M : ℕ → Submodule k ((ι → Fin 2) → k)), IsFrobFiltration n (tensorRep F k e) r M :=
  exists_filtration hF _ ι rfl e

end Tensor

end CFSG.QuasithinUnique.Setup.SL2Modules
