module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.Collar2

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}

section Polarity

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj] {c : Γ.Coloring (Fin 2)}
variable {K : Type*} [Field K] [Fintype K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W}

@[expose] def IsPolarHomology (c : Γ.Coloring (Fin 2)) (ι : V → Submodule K W)
    (X : Submodule K W) (σ : W →ₗ[K] W) : Prop :=
  (∀ v ∈ polar c ι X, σ v = v) ∧ ∀ v, σ v - v ∈ X

private theorem isCompl_polar (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι ⊤) [FiniteDimensional K W] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι ⊤ ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K W = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1)
    (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X) :
    IsCompl X (polar c ι X) := by
  have htop : finrank K (⊤ : Submodule K W) = 5 := by rw [finrank_top, h5]
  have hπ4 : finrank K (polar c ι X) = 4 := by
    have h := finrank_polar_add_one hP hT c hdeg hι hsec hℓ htop hX1 le_top
    omega
  have hinf : X ⊓ polar c ι X = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    have hXeq : X = K ∙ v := eq_span_singleton_of_mem_of_finrank_eq_one hX1 hv.1 hv0
    have hle : X ≤ polar c ι X := hXeq ▸
      (Submodule.span_singleton_le_iff_mem v (polar c ι X)).mpr hv.2
    exact hXP ((le_polar_self_iff hP hT c hdeg hι hsec hℓ htop hX1 le_top).1 hle)
  have hsup : X ⊔ polar c ι X = ⊤ := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq X (polar c ι X)
    rw [hinf, finrank_bot, hX1, hπ4] at h
    exact Submodule.eq_of_le_of_finrank_eq le_top (by omega)
  exact isCompl_iff.mpr ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩

private theorem exists_isPolarHomology_scalar (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι ⊤) [FiniteDimensional K W] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι ⊤ ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K W = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1)
    (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X)
    {z₀ z₁ : V} (hz₀ : c z₀ = 0) (hz₁ : c z₁ = 0) (hne : z₀ ≠ z₁)
    (hz₀X : z₀ ∉ collar c ι X) (hz₁U : ι z₁ ≤ X ⊔ ι z₀) :
    ∃ (σ : W →ₗ[K] W) (lam : K), IsPolarHomology c ι X σ ∧ (ι z₀).map σ = ι z₁ ∧
      lam ≠ 0 ∧ lam ≠ 1 ∧ ∀ x ∈ X, σ x = lam • x := by
  classical
  have htop : finrank K (⊤ : Submodule K W) = 5 := by rw [finrank_top, h5]
  have hcompl := isCompl_polar hP hT c hdeg hι hsec hℓ h5 hX1 hXP
  have hZ₀ne : ι z₀ ≠ ⊥ := by
    intro hbot
    have h := hι.finrank_point z₀ hz₀
    rw [hbot, finrank_bot] at h
    omega
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ₀ne
  have hZ₀span : ι z₀ = K ∙ v₀ :=
    eq_span_singleton_of_mem_of_finrank_eq_one (hι.finrank_point z₀ hz₀) hv₀ hv₀0
  have hv₀sup : v₀ ∈ X ⊔ polar c ι X := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y, hyX, h, hhπ, hyh⟩ := Submodule.mem_sup.mp hv₀sup
  have hy0 : y ≠ 0 := by
    intro hy
    have hv₀π : v₀ ∈ polar c ι X := by rw [← hyh, hy, zero_add]; exact hhπ
    have hle : ι z₀ ≤ polar c ι X := by
      rw [hZ₀span]
      exact (Submodule.span_singleton_le_iff_mem v₀ (polar c ι X)).mpr hv₀π
    have hz₀sec : z₀ ∈ sectionPoints c ι (polar c ι X) := ⟨hz₀, hle⟩
    exact hz₀X (by
      rw [← sectionPoints_polar_eq_collar hP hT c hdeg hι hsec hℓ htop hX1 le_top]
      exact hz₀sec)
  have hXspan : X = K ∙ y := eq_span_singleton_of_mem_of_finrank_eq_one hX1 hyX hy0
  have hh0 : h ≠ 0 := by
    intro hh
    have hXeq : X = ι z₀ := by
      rw [hXspan, hZ₀span]
      congr 1
      rw [← hyh, hh, add_zero]
    exact hXP ⟨z₀, hz₀, hXeq.symm⟩
  have hZ₁ne : ι z₁ ≠ ⊥ := by
    intro hbot
    have h := hι.finrank_point z₁ hz₁
    rw [hbot, finrank_bot] at h
    omega
  obtain ⟨v₁, hv₁, hv₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ₁ne
  have hZ₁span : ι z₁ = K ∙ v₁ :=
    eq_span_singleton_of_mem_of_finrank_eq_one (hι.finrank_point z₁ hz₁) hv₁ hv₁0
  have hv₁le : v₁ ∈ X ⊔ ι z₀ := hz₁U hv₁
  rw [hXspan, hZ₀span] at hv₁le
  obtain ⟨b, hb, a, ha, hba⟩ := Submodule.mem_sup.mp hv₁le
  obtain ⟨β₀, hβ₀⟩ := Submodule.mem_span_singleton.mp hb
  obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp ha
  have hv₁eq : v₁ = (β₀ + γ) • y + γ • h := by
    rw [← hba, ← hβ₀, ← hγ, ← hyh, smul_add, add_smul]
    abel
  have hγ0 : γ ≠ 0 := by
    intro hγ0
    have hv₁X : ι z₁ ≤ X := by
      rw [hZ₁span]
      refine (Submodule.span_singleton_le_iff_mem v₁ X).mpr ?_
      have hmem : (β₀ + γ) • y ∈ X := by
        rw [hXspan]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)
      rw [hv₁eq, hγ0, zero_smul, add_zero]
      simpa [hγ0] using hmem
    have heq : ι z₁ = X :=
      Submodule.eq_of_le_of_finrank_eq hv₁X (by rw [hι.finrank_point z₁ hz₁, hX1])
    exact hXP ⟨z₁, hz₁, heq⟩
  let lam : K := γ⁻¹ * (β₀ + γ)
  let w : W := γ⁻¹ • v₁
  have hw_mem : w ∈ ι z₁ := Submodule.smul_mem _ γ⁻¹ hv₁
  have hw_eq : w = h + lam • y := by
    dsimp only [w, lam]
    rw [hv₁eq, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hγ0, one_smul, add_comm]
  have hw0 : w ≠ 0 := by
    intro hwzero
    have hhX : h ∈ X := by
      have hneg : h = -(lam • y) := by
        have hsum : h + lam • y = 0 := by rw [← hw_eq]; exact hwzero
        exact eq_neg_of_add_eq_zero_left hsum
      rw [hneg]
      exact X.neg_mem (X.smul_mem lam hyX)
    have hhbot : h ∈ (⊥ : Submodule K W) := by
      rw [← hcompl.inf_eq_bot]
      exact ⟨hhX, hhπ⟩
    exact hh0 (by simpa using hhbot)
  have hZ₁w : ι z₁ = K ∙ w :=
    eq_span_singleton_of_mem_of_finrank_eq_one (hι.finrank_point z₁ hz₁) hw_mem hw0
  have hlam0 : lam ≠ 0 := by
    intro hlam
    have hwπ : w ∈ polar c ι X := by rw [hw_eq, hlam, zero_smul, add_zero]; exact hhπ
    have hZ₁π : ι z₁ ≤ polar c ι X := by
      rw [hZ₁w]
      exact (Submodule.span_singleton_le_iff_mem w (polar c ι X)).mpr hwπ
    have hcol : z₁ ∈ collar c ι X := by
      have hz₁sec : z₁ ∈ sectionPoints c ι (polar c ι X) := ⟨hz₁, hZ₁π⟩
      rwa [sectionPoints_polar_eq_collar hP hT c hdeg hι hsec hℓ htop hX1 le_top] at hz₁sec
    exact (sectionPoints_sup_of_not_mem_collar hP hT hι hsec hX1 le_top hXP hz₀ hz₀X).2
      z₁ ⟨hz₁, hz₁U⟩ hcol
  have hlam1 : lam ≠ 1 := by
    intro hlam
    have hwv₀ : w = v₀ := by
      rw [hw_eq, hlam, one_smul, add_comm]
      exact hyh
    have heq : ι z₁ = ι z₀ := by rw [hZ₁w, hZ₀span, hwv₀]
    exact hne (hι.injective heq).symm
  let σ : W →ₗ[K] W :=
    LinearMap.id + (lam - 1) • X.projection (polar c ι X) hcompl
  have hfix : ∀ v ∈ polar c ι X, σ v = v := by
    intro v hv
    simp [σ, Submodule.projection_apply_of_mem_right hcompl hv]
  have hdisp : ∀ v, σ v - v ∈ X := by
    intro v
    have hform : σ v = v + (lam - 1) • (X.projection (polar c ι X) hcompl) v := by simp [σ]
    rw [hform]
    have hmem := Submodule.projection_apply_mem hcompl v
    have heq : v + (lam - 1) • (X.projection (polar c ι X) hcompl) v - v =
        (lam - 1) • (X.projection (polar c ι X) hcompl) v := by abel
    rw [heq]
    exact Submodule.smul_mem X (lam - 1) hmem
  have hσy : σ y = lam • y := by
    have hproj : (X.projection (polar c ι X) hcompl) y = y :=
      Submodule.projection_apply_of_mem_left hcompl hyX
    have hform : σ y = y + (lam - 1) • y := by simp [σ, hproj]
    rw [hform]
    calc
      y + (lam - 1) • y = (1 : K) • y + (lam - 1) • y := by rw [one_smul]
      _ = (1 + (lam - 1)) • y := by rw [add_smul]
      _ = lam • y := by rw [show 1 + (lam - 1) = lam by ring]
  have hσv₀ : σ v₀ = w := by
    have hv₀eq : v₀ = y + h := hyh.symm
    have hproj : (X.projection (polar c ι X) hcompl) v₀ = y := by
      rw [hv₀eq, map_add, Submodule.projection_apply_of_mem_left hcompl hyX,
        Submodule.projection_apply_of_mem_right hcompl hhπ, add_zero]
    have hform : σ v₀ = v₀ + (lam - 1) • (X.projection (polar c ι X) hcompl) v₀ := by simp [σ]
    rw [hform, hproj, hv₀eq]
    have h1 : (y + h) + (lam - 1) • y = h + (y + (lam - 1) • y) := by abel
    rw [h1]
    have h2 : y + (lam - 1) • y = lam • y := by
      calc
        y + (lam - 1) • y = (1 : K) • y + (lam - 1) • y := by rw [one_smul]
        _ = (1 + (lam - 1)) • y := by rw [add_smul]
        _ = lam • y := by rw [show 1 + (lam - 1) = lam by ring]
    rw [h2, hw_eq]
  refine ⟨σ, lam, ⟨hfix, hdisp⟩, ?_, hlam0, hlam1, ?_⟩
  · rw [hZ₀span, Submodule.map_span, Set.image_singleton, hσv₀]
    exact hZ₁w.symm
  · intro x hx
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp (hXspan ▸ hx)
    rw [← hμ, map_smul, hσy]
    simp only [smul_smul]
    rw [mul_comm]

private theorem map_le_sup_center {X : Submodule K W} {σ : W →ₗ[K] W}
    (hσ : IsPolarHomology c ι X σ) (z : V) : (ι z).map σ ≤ X ⊔ ι z := by
  refine (Submodule.map_le_iff_le_comap).mpr ?_
  intro v hv
  change σ v ∈ X ⊔ ι z
  have hdiff : σ v - v ∈ X := hσ.2 v
  have h : σ v = v + (σ v - v) := (add_sub_cancel v (σ v)).symm
  rw [h, sup_comm]
  exact Submodule.add_mem_sup hv hdiff

private theorem exists_scalar_ne_zero_of_isPolarHomology
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι ⊤) [FiniteDimensional K W] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι ⊤ ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K W = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1)
    (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X)
    {σ : W →ₗ[K] W} (hσ : IsPolarHomology c ι X σ)
    {z₀ z₁ : V} (hz₀ : c z₀ = 0) (hz₀X : z₀ ∉ collar c ι X) (hz₁ : c z₁ = 0)
    (h01 : (ι z₀).map σ = ι z₁) :
    ∃ lam : K, lam ≠ 0 ∧ ∀ x ∈ X, σ x = lam • x := by
  classical
  have htop : finrank K (⊤ : Submodule K W) = 5 := by rw [finrank_top, h5]
  have hcompl := isCompl_polar hP hT c hdeg hι hsec hℓ h5 hX1 hXP
  have hXne : X ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hX1
    omega
  obtain ⟨x₀, hx₀X, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hXne
  have hXspan : X = K ∙ x₀ := eq_span_singleton_of_mem_of_finrank_eq_one hX1 hx₀X hx₀0
  have hdiff : σ x₀ - x₀ ∈ K ∙ x₀ := by rw [← hXspan]; exact hσ.2 x₀
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hdiff
  let lam : K := 1 + a
  have hlamx : σ x₀ = lam • x₀ := by
    have h1 : σ x₀ = x₀ + a • x₀ := by rw [ha]; abel
    rw [h1]
    dsimp only [lam]
    rw [add_smul, one_smul]
  have hscalar : ∀ x ∈ X, σ x = lam • x := by
    intro x hx
    obtain ⟨mu, hmu⟩ := Submodule.mem_span_singleton.mp (hXspan ▸ hx)
    rw [← hmu, map_smul, hlamx]
    simp only [smul_smul]
    rw [mul_comm]
  refine ⟨lam, ?_, hscalar⟩
  intro hlam0
  have hZ₀ne : ι z₀ ≠ ⊥ := by
    intro hbot
    have h := hι.finrank_point z₀ hz₀
    rw [hbot, finrank_bot] at h
    omega
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ₀ne
  have hZ₀span : ι z₀ = K ∙ v₀ :=
    eq_span_singleton_of_mem_of_finrank_eq_one (hι.finrank_point z₀ hz₀) hv₀ hv₀0
  have hv₀sup : v₀ ∈ X ⊔ polar c ι X := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y, hyX, h, hhπ, hyh⟩ := Submodule.mem_sup.mp hv₀sup
  have hσv₀ : σ v₀ = h := by
    rw [← hyh, map_add, hscalar y hyX, hσ.1 h hhπ, hlam0, zero_smul, zero_add]
  have hmap_le : (ι z₀).map σ ≤ polar c ι X := by
    rw [hZ₀span, Submodule.map_span, Set.image_singleton, hσv₀]
    exact (Submodule.span_singleton_le_iff_mem h (polar c ι X)).mpr hhπ
  have hZ₁π : ι z₁ ≤ polar c ι X := by rw [← h01]; exact hmap_le
  have hcol : z₁ ∈ collar c ι X := by
    have hz₁sec : z₁ ∈ sectionPoints c ι (polar c ι X) := ⟨hz₁, hZ₁π⟩
    rwa [sectionPoints_polar_eq_collar hP hT c hdeg hι hsec hℓ htop hX1 le_top] at hz₁sec
  have hZ₁le : ι z₁ ≤ X ⊔ ι z₀ := by rw [← h01]; exact map_le_sup_center hσ z₀
  exact (sectionPoints_sup_of_not_mem_collar hP hT hι hsec hX1 le_top hXP hz₀ hz₀X).2
    z₁ ⟨hz₁, hZ₁le⟩ hcol

private theorem injective_of_isPolarHomology
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι ⊤) [FiniteDimensional K W] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι ⊤ ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K W = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1)
    (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X)
    {σ : W →ₗ[K] W} (hσ : IsPolarHomology c ι X σ)
    {z₀ z₁ : V} (hz₀ : c z₀ = 0) (hz₀X : z₀ ∉ collar c ι X) (hz₁ : c z₁ = 0)
    (h01 : (ι z₀).map σ = ι z₁) :
    Function.Injective σ := by
  obtain ⟨lam, hlam0, hscalar⟩ :=
    exists_scalar_ne_zero_of_isPolarHomology hP hT c hdeg hι hsec hℓ h5 hX1 hXP hσ hz₀ hz₀X
      hz₁ h01
  have hcompl := isCompl_polar hP hT c hdeg hι hsec hℓ h5 hX1 hXP
  intro u v huv
  have hw : σ (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hsup : u - v ∈ X ⊔ polar c ι X := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨x, hxX, h, hhπ, hxh⟩ := Submodule.mem_sup.mp hsup
  have hform : σ (u - v) = h + lam • x := by
    rw [← hxh, map_add, hσ.1 h hhπ, hscalar x hxX, add_comm]
  have hsum : h + lam • x = 0 := by rw [← hform]; exact hw
  have hhX : h ∈ X := by
    have hneg : h = -(lam • x) := eq_neg_of_add_eq_zero_left hsum
    rw [hneg]
    exact X.neg_mem (X.smul_mem lam hxX)
  have hhbot : h = 0 := by
    have hmem : h ∈ X ⊓ polar c ι X := ⟨hhX, hhπ⟩
    rw [hcompl.inf_eq_bot] at hmem
    simpa using hmem
  have hlamx : lam • x = 0 := by
    have := hsum
    rw [hhbot, zero_add] at this
    exact this
  have hx0 : x = 0 := (smul_eq_zero.mp hlamx).resolve_left hlam0
  have hzero : u - v = 0 := by rw [← hxh, hx0, hhbot, add_zero]
  exact sub_eq_zero.mp hzero

private theorem mem_polar_of_map_mem_polar
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι ⊤) [FiniteDimensional K W] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι ⊤ ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K W = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1)
    (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X)
    {σ : W →ₗ[K] W} (hσ : IsPolarHomology c ι X σ)
    {z₀ z₁ : V} (hz₀ : c z₀ = 0) (hz₀X : z₀ ∉ collar c ι X) (hz₁ : c z₁ = 0)
    (h01 : (ι z₀).map σ = ι z₁) {v : W} (hv : σ v ∈ polar c ι X) :
    v ∈ polar c ι X := by
  obtain ⟨lam, hlam0, hscalar⟩ :=
    exists_scalar_ne_zero_of_isPolarHomology hP hT c hdeg hι hsec hℓ h5 hX1 hXP hσ hz₀ hz₀X
      hz₁ h01
  have hcompl := isCompl_polar hP hT c hdeg hι hsec hℓ h5 hX1 hXP
  have hvsup : v ∈ X ⊔ polar c ι X := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨x, hxX, h, hhπ, hxh⟩ := Submodule.mem_sup.mp hvsup
  have hform : σ v = h + lam • x := by
    rw [← hxh, map_add, hσ.1 h hhπ, hscalar x hxX, add_comm]
  have hlamx : lam • x ∈ polar c ι X := by
    have := hv
    rw [hform] at this
    simpa using (polar c ι X).sub_mem this hhπ
  have hx0 : x = 0 := by
    have hmem : lam • x ∈ X ⊓ polar c ι X := ⟨X.smul_mem lam hxX, hlamx⟩
    rw [hcompl.inf_eq_bot] at hmem
    exact (smul_eq_zero.mp (by simpa using hmem)).resolve_left hlam0
  rw [← hxh, hx0, zero_add]
  exact hhπ

private theorem map_eq_self_of_le_polar {X U : Submodule K W} {σ : W →ₗ[K] W}
    (hσ : IsPolarHomology c ι X σ) (hU : U ≤ polar c ι X) : U.map σ = U := by
  refine le_antisymm ?_ ?_
  · rintro v ⟨u, hu, rfl⟩
    rw [hσ.1 u (hU hu)]
    exact hu
  · intro v hv
    exact Submodule.mem_map.mpr ⟨v, hv, hσ.1 v (hU hv)⟩

private theorem good_line_step
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι ⊤) [FiniteDimensional K W] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι ⊤ ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K W = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1)
    (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X)
    {σ : W →ₗ[K] W} (hσ : IsPolarHomology c ι X σ)
    {z z' N : V} (hz : c z = 0) (hz' : c z' = 0) (hzX : z ∉ collar c ι X)
    (hzz' : (ι z).map σ = ι z') (hzN : Γ.Adj z N) :
    ∃ N', c N' = 1 ∧ Γ.Adj z' N' ∧ (ι N).map σ = ι N' ∧
      ∀ a, Γ.Adj N a → ∃ a', c a' = 0 ∧ (ι a).map σ = ι a' := by
  classical
  have htop : finrank K (⊤ : Submodule K W) = 5 := by rw [finrank_top, h5]
  have hinj :=
    injective_of_isPolarHomology hP hT c hdeg hι hsec hℓ h5 hX1 hXP hσ hz hzX hz' hzz'
  have hN1 : c N = 1 := color_eq_one_of_adj_of_color_eq_zero hz hzN
  obtain ⟨y, hyN, hycol⟩ := exists_adj_mem_collar hP hT hι hX1 le_top hN1
  have hy0 : c y = 0 := hycol.1
  have hyz : y ≠ z := fun h => hzX (h ▸ hycol)
  have hz'le : ι z' ≤ perpSpan c ι y := by
    rw [← hzz']
    refine (map_le_sup_center hσ z).trans (sup_le hycol.2 ?_)
    exact submodule_le_perpSpan ⟨hz, by
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact le_of_eq (dist_eq_two_of_adj_of_adj_of_ne hP hzN hyN (Ne.symm hyz))⟩
  have hz'y : z' ≠ y := by
    intro hzy
    have hz'π : ι z' ≤ polar c ι X := by rw [hzy]; exact le_polar_of_mem_collar hycol
    have hzle : ι z ≤ polar c ι X := by
      intro v hv
      refine mem_polar_of_map_mem_polar hP hT c hdeg hι hsec hℓ h5 hX1 hXP hσ hz hzX
        hz' hzz' ?_
      have hvmap : σ v ∈ (ι z).map σ := Submodule.mem_map.mpr ⟨v, hv, rfl⟩
      rw [hzz'] at hvmap
      exact hz'π hvmap
    have hzcol : z ∈ collar c ι X := by
      have hzsec : z ∈ sectionPoints c ι (polar c ι X) := ⟨hz, hzle⟩
      rwa [sectionPoints_polar_eq_collar hP hT c hdeg hι hsec hℓ htop hX1 le_top] at hzsec
    exact hzX hzcol
  have hz'perp : z' ∈ ptPerp Γ c {y} := by
    rw [← sectionPoints_perpSpan hP hT hι hy0]
    exact ⟨hz', hz'le⟩
  have hz'y2 : Γ.dist z' y = 2 :=
    dist_eq_two_of_le_two_of_ne hP hz' hy0 hz'y (hz'perp.2 y rfl)
  let N' : V := commonNeighbor hP hz'y2
  have hz'N' : Γ.Adj z' N' := commonNeighbor_adj_left hP hz'y2
  have hyN' : Γ.Adj y N' := commonNeighbor_adj_right hP hz'y2
  have hN'1 : c N' = 1 := color_eq_one_of_adj_of_color_eq_zero hz' hz'N'
  have hline : ι N = ι y ⊔ ι z :=
    line_eq_sup_of_two_adjacent_points hι hy0 hz hyz hyN.symm hzN
  have hlineN' : ι N' = ι y ⊔ ι z' :=
    line_eq_sup_of_two_adjacent_points hι hy0 hz' (Ne.symm hz'y) hyN' hz'N'
  have hmapN : (ι N).map σ = ι N' := by
    rw [hline, Submodule.map_sup, hlineN',
      map_eq_self_of_le_polar hσ (le_polar_of_mem_collar hycol), hzz']
  refine ⟨N', hN'1, hz'N', hmapN, ?_⟩
  intro a haN
  have ha0 : c a = 0 := color_eq_zero_of_adj_of_color_eq_one hN1 haN
  have hale : ι a ≤ ι N := (hι.adj_iff a N ha0 hN1).1 haN.symm
  have hmapsub : (ι a).map σ ≤ ι N' := by
    rw [← hmapN]
    exact Submodule.map_mono hale
  have ha1 : finrank K ((ι a).map σ) = 1 := by
    rw [← (Submodule.equivMapOfInjective σ hinj (ι a)).finrank_eq]
    exact hι.finrank_point a ha0
  obtain ⟨a', hN'a', ha'eq⟩ := hι.full N' hN'1 ((ι a).map σ) ha1 hmapsub
  exact ⟨a', color_eq_zero_of_adj_of_color_eq_one hN'1 hN'a', ha'eq.symm⟩

theorem IsPolarHomology.map_point (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι ⊤) [FiniteDimensional K W] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι ⊤ ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K W = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1) (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X)
    {σ : W →ₗ[K] W} (hσ : IsPolarHomology c ι X σ) {z₀ z₁ : V} (hz₀ : c z₀ = 0)
    (hz₀X : z₀ ∉ collar c ι X) (hz₁ : c z₁ = 0) (h01 : (ι z₀).map σ = ι z₁)
    {x : V} (hx : c x = 0) :
    ∃ x', c x' = 0 ∧ (ι x).map σ = ι x' := by
  classical
  let Good : V → Prop := fun z => ∃ z', c z' = 0 ∧ (ι z).map σ = ι z'
  have hz₀good : Good z₀ := ⟨z₁, hz₁, h01⟩
  have hstep : ∀ z w, c z = 0 → z ∉ collar c ι X → c w = 0 → w ∉ collar c ι X →
      Γ.dist z w = 2 → Good z → Good w := by
    intro z w hz hzX hw hwX hzw hgood
    obtain ⟨z', hz', hzz'⟩ := hgood
    obtain ⟨N, ⟨hzN, hwN⟩, -⟩ := existsUnique_commonNeighbor hP hzw
    obtain ⟨N', -, -, -, hN'good⟩ :=
      good_line_step hP hT c hdeg hι hsec hℓ h5 hX1 hXP hσ hz hz' hzX hzz' hzN
    exact hN'good w hwN.symm
  by_cases hxcol : x ∈ collar c ι X
  · exact ⟨x, hx, map_eq_self_of_le_polar hσ (le_polar_of_mem_collar hxcol)⟩
  · exact collar_compl_induction hP hT hι hX1 le_top (Q := Good) hz₀ hz₀X hz₀good hstep hx hxcol

private theorem exists_line_map
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι ⊤) [FiniteDimensional K W] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι ⊤ ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K W = 5)
    {σ : W →ₗ[K] W} (hinj : Function.Injective σ)
    (φ : {y : V // c y = 0} → {y : V // c y = 0})
    (hφ : ∀ y, (ι y.1).map σ = ι (φ y).1)
    {N : V} (hN : c N = 1) :
    ∃ N', c N' = 1 ∧ (ι N).map σ = ι N' := by
  classical
  have htop : finrank K (⊤ : Submodule K W) = 5 := by rw [finrank_top, h5]
  let U : Submodule K W := (ι N).map σ
  have hUle : U ≤ ⊤ := le_top
  have hU2 : finrank K U = 2 := by
    change finrank K ((ι N).map σ) = 2
    rw [← (Submodule.equivMapOfInjective σ hinj (ι N)).finrank_eq]
    exact hι.finrank_line N hN
  let F : V → V := fun y => if hy : c y = 0 then (φ ⟨y, hy⟩).1 else y
  have hF : ∀ y (hy : c y = 0), F y = (φ ⟨y, hy⟩).1 := fun y hy => dif_pos hy
  have hmem : ∀ y ∈ Γ.neighborSet N, F y ∈ sectionPoints c ι U := by
    intro y hy
    have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hN hy
    have hyle : ι y ≤ ι N := (hι.adj_iff y N hy0 hN).1 hy.symm
    refine ⟨?_, ?_⟩
    · rw [hF y hy0]
      exact (φ ⟨y, hy0⟩).2
    · rw [hF y hy0, ← hφ ⟨y, hy0⟩]
      exact Submodule.map_mono hyle
  have hinjOn : Set.InjOn F (Γ.neighborSet N) := by
    intro y hy y' hy' heq
    have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hN hy
    have hy'0 : c y' = 0 := color_eq_zero_of_adj_of_color_eq_one hN hy'
    have hsub : φ ⟨y, hy0⟩ = φ ⟨y', hy'0⟩ := by
      apply Subtype.ext
      simpa [hF y hy0, hF y' hy'0] using heq
    have hmap : (ι y).map σ = (ι y').map σ := by
      rw [hφ ⟨y, hy0⟩, hφ ⟨y', hy'0⟩, hsub]
    exact hι.injective (Submodule.map_injective_of_injective hinj hmap)
  have hcard : (Γ.neighborSet N).ncard ≤ (sectionPoints c ι U).ncard :=
    Set.ncard_le_ncard_of_injOn F hmem hinjOn
  have hdegN : Γ.degree N = s + 1 := by rw [hdeg N, if_neg (by rw [hN]; decide)]
  rw [ncard_neighborSet, hdegN] at hcard
  by_cases hline : ∃ L, c L = 1 ∧ ι L = U
  · obtain ⟨L, hL1, hLU⟩ := hline
    exact ⟨L, hL1, hLU.symm⟩
  · push Not at hline
    have hge : 2 ≤ (sectionPoints c ι U).ncard := by
      have hs2 : 2 ≤ s := two_le_s hP hT c hdeg
      omega
    have hcount := hsec.ncard_eq hUle hU2 hline hge
    have hsq : ℓ ^ 2 ≤ s := sq_le_of_hasConstantSecants hP hT c hdeg hι hsec htop
    nlinarith

private theorem map_perpSpan
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι ⊤) [FiniteDimensional K W] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι ⊤ ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K W = 5)
    {σ : W →ₗ[K] W} (hinj : Function.Injective σ)
    (φ : {y : V // c y = 0} → {y : V // c y = 0})
    (hφ : ∀ y, (ι y.1).map σ = ι (φ y).1)
    {y : V} (hy : c y = 0) :
    (perpSpan c ι y).map σ = perpSpan c ι (φ ⟨y, hy⟩).1 := by
  classical
  have htop : finrank K (⊤ : Submodule K W) = 5 := by rw [finrank_top, h5]
  have hφy0 : c (φ ⟨y, hy⟩).1 = 0 := (φ ⟨y, hy⟩).2
  have hmap_le : (perpSpan c ι y).map σ ≤ perpSpan c ι (φ ⟨y, hy⟩).1 := by
    rw [perpSpan_eq_iSup_neighborFinset hP hT hι hy,
      perpSpan_eq_iSup_neighborFinset hP hT hι hφy0]
    simp only [Submodule.map_iSup]
    refine iSup_le fun L => iSup_le fun hL => ?_
    rw [mem_neighborFinset] at hL
    have hL1 : c L = 1 := color_eq_one_of_adj_of_color_eq_zero hy hL
    obtain ⟨N', hN'1, hN'eq⟩ :=
      exists_line_map hP hT c hdeg hι hsec hℓ h5 hinj φ hφ hL1
    rw [hN'eq]
    have hyL : ι y ≤ ι L := (hι.adj_iff y L hy hL1).1 hL
    have hle : ι (φ ⟨y, hy⟩).1 ≤ ι N' := by
      rw [← hφ ⟨y, hy⟩, ← hN'eq]
      exact Submodule.map_mono hyL
    exact le_iSup_of_le N' (le_iSup_of_le
      (by simpa using (hι.adj_iff (φ ⟨y, hy⟩).1 N' hφy0 hN'1).2 hle) le_rfl)
  have h4y : finrank K (perpSpan c ι y) = 4 := by
    have h := finrank_perpSpan_add_one hP hT hι hy
    omega
  have h4φy : finrank K (perpSpan c ι (φ ⟨y, hy⟩).1) = 4 := by
    have h := finrank_perpSpan_add_one hP hT hι hφy0
    omega
  refine Submodule.eq_of_le_of_finrank_eq hmap_le ?_
  rw [← (Submodule.equivMapOfInjective σ hinj (perpSpan c ι y)).finrank_eq, h4y, h4φy]

theorem IsPolarHomology.map_polar (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι ⊤) [FiniteDimensional K W] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι ⊤ ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K W = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1) (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X)
    {σ : W →ₗ[K] W} (hσ : IsPolarHomology c ι X σ) {z₀ z₁ : V} (hz₀ : c z₀ = 0)
    (hz₀X : z₀ ∉ collar c ι X) (hz₁ : c z₁ = 0) (h01 : (ι z₀).map σ = ι z₁)
    {Y : Submodule K W} (hσY : Y.map σ = Y) :
    (polar c ι Y).map σ = polar c ι Y := by
  classical
  have hinj :=
    injective_of_isPolarHomology hP hT c hdeg hι hsec hℓ h5 hX1 hXP hσ hz₀ hz₀X hz₁ h01
  let mp : ∀ y : {y : V // c y = 0}, ∃ y' : {y' : V // c y' = 0}, (ι y.1).map σ = ι y'.1 :=
    fun y => by
      obtain ⟨y', hy', hmap⟩ :=
        IsPolarHomology.map_point hP hT c hdeg hι hsec hℓ h5 hX1 hXP hσ hz₀ hz₀X hz₁ h01 y.2
      exact ⟨⟨y', hy'⟩, hmap⟩
  let φ : {y : V // c y = 0} → {y : V // c y = 0} := fun y => (mp y).choose
  have hφ : ∀ y, (ι y.1).map σ = ι (φ y).1 := fun y => (mp y).choose_spec
  have hφinj : Function.Injective φ := by
    intro y y' hyy
    have hmap : (ι y.1).map σ = (ι y'.1).map σ := by rw [hφ y, hφ y', hyy]
    exact Subtype.ext (hι.injective (Submodule.map_injective_of_injective hinj hmap))
  have hH : ∀ y : {y : V // c y = 0},
      (perpSpan c ι y.1).map σ = perpSpan c ι (φ y).1 := fun y =>
    map_perpSpan hP hT c hdeg hι hsec hℓ h5 hinj φ hφ y.2
  have hcollar : ∀ y : {y : V // c y = 0},
      y.1 ∈ collar c ι Y ↔ (φ y).1 ∈ collar c ι Y := by
    intro y
    have hiff : Y ≤ perpSpan c ι y.1 ↔ Y ≤ perpSpan c ι (φ y).1 := by
      rw [← (LinearMap.map_le_map_iff' (f := σ) (LinearMap.ker_eq_bot.mpr hinj))]
      rw [hσY, hH y]
    exact ⟨fun hy' => ⟨(φ y).2, hiff.mp hy'.2⟩, fun hy' => ⟨y.2, hiff.mpr hy'.2⟩⟩
  have himage : φ '' {y : {y : V // c y = 0} | y.1 ∈ collar c ι Y} =
      {y : {y : V // c y = 0} | y.1 ∈ collar c ι Y} := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact (hcollar y).mp hy
    · rw [Set.ncard_image_of_injective _ hφinj]
  change (⨆ y : {y : V // y ∈ collar c ι Y}, ι y.1).map σ =
    ⨆ y : {y : V // y ∈ collar c ι Y}, ι y.1
  rw [Submodule.map_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun y => ?_
    rw [hφ ⟨y.1, y.2.1⟩]
    exact le_iSup (fun z : {z : V // z ∈ collar c ι Y} => ι z.1)
      ⟨(φ ⟨y.1, y.2.1⟩).1, (hcollar ⟨y.1, y.2.1⟩).mp y.2⟩
  · refine iSup_le fun z => ?_
    have hz : (⟨z.1, z.2.1⟩ : {y : V // c y = 0}) ∈
        φ '' {y : {y : V // c y = 0} | y.1 ∈ collar c ι Y} := by
      rw [himage]
      exact z.2
    obtain ⟨y, hy, hyz⟩ := hz
    have hzy : (ι y.1).map σ = ι z.1 := by rw [hφ y, hyz]
    rw [← hzy]
    exact le_iSup (fun y' : {y : V // y ∈ collar c ι Y} => (ι y'.1).map σ) ⟨y.1, hy⟩

private theorem eq_polar_of_map_eq_of_not_le
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι ⊤) [FiniteDimensional K W] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι ⊤ ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K W = 5)
    {X : Submodule K W} (hX1 : finrank K X = 1)
    (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X)
    {σ : W →ₗ[K] W} (hσ : IsPolarHomology c ι X σ)
    {lam : K} (hlam1 : lam ≠ 1) (hscalar : ∀ x ∈ X, σ x = lam • x)
    {H : Submodule K W} (hH : H.map σ = H)
    (hHhyper : finrank K H + 1 = finrank K (⊤ : Submodule K W)) (hXH : ¬ X ≤ H) :
    H = polar c ι X := by
  have htop : finrank K (⊤ : Submodule K W) = 5 := by rw [finrank_top, h5]
  have hcompl := isCompl_polar hP hT c hdeg hι hsec hℓ h5 hX1 hXP
  have hHle : H ≤ polar c ι X := by
    intro v hv
    have hvsup : v ∈ X ⊔ polar c ι X := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨x, hxX, h, hhπ, hxh⟩ := Submodule.mem_sup.mp hvsup
    have hσvH : σ v ∈ H := by
      rw [← hH]
      exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
    have hdiff : σ v - v ∈ H := H.sub_mem hσvH hv
    have hform : σ v - v = (lam - 1) • x := by
      rw [← hxh, map_add, hσ.1 h hhπ, hscalar x hxX, sub_smul, one_smul]
      abel
    have hsmul : (lam - 1) • x ∈ H := by rw [← hform]; exact hdiff
    have hxH : x ∈ H := by
      have hinv : (lam - 1)⁻¹ • ((lam - 1) • x) ∈ H := H.smul_mem _ hsmul
      rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hlam1), one_smul] at hinv
    have hx0 : x = 0 := by
      by_contra hx0
      have hXeq : X = K ∙ x := eq_span_singleton_of_mem_of_finrank_eq_one hX1 hxX hx0
      exact hXH (hXeq ▸ (Submodule.span_singleton_le_iff_mem x H).mpr hxH)
    rw [← hxh, hx0, zero_add]
    exact hhπ
  have hH4 : finrank K H = 4 := by omega
  have hπ4 : finrank K (polar c ι X) = 4 := by
    have h := finrank_polar_add_one hP hT c hdeg hι hsec hℓ htop hX1 le_top
    omega
  exact Submodule.eq_of_le_of_finrank_eq hHle (by rw [hH4, hπ4])

theorem le_polar_comm (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hι : IsProjGQ c ι ⊤) [FiniteDimensional K W] {ℓ : ℕ}
    (hsec : HasConstantSecants c ι ⊤ ℓ) (hℓ : 2 ≤ ℓ) (h5 : finrank K W = 5)
    {X Y : Submodule K W} (hX1 : finrank K X = 1) (hXP : ¬ ∃ v, c v = 0 ∧ ι v = X)
    (hY1 : finrank K Y = 1) (hYP : ¬ ∃ v, c v = 0 ∧ ι v = Y) (hYX : Y ≤ polar c ι X) :
    X ≤ polar c ι Y := by
  classical
  have htop : finrank K (⊤ : Submodule K W) = 5 := by rw [finrank_top, h5]
  obtain ⟨z₀, hz₀, hz₀X⟩ :=
    exists_not_mem_collar hP hT c hdeg hι hsec hℓ htop hX1 le_top hXP
  have hdata := sectionPoints_sup_of_not_mem_collar hP hT hι hsec hX1 le_top hXP hz₀ hz₀X
  have hge : 1 < (sectionPoints c ι (X ⊔ ι z₀)).ncard := by
    rw [hdata.1]
    omega
  obtain ⟨z₁, hz₁sec, hz₁ne⟩ := Set.exists_ne_of_one_lt_ncard hge z₀
  have hz₁ : c z₁ = 0 := hz₁sec.1
  obtain ⟨σ, lam, hσ, hσ01, -, hlam1, hscalar⟩ :=
    exists_isPolarHomology_scalar hP hT c hdeg hι hsec hℓ h5 hX1 hXP hz₀ hz₁
      (Ne.symm hz₁ne) hz₀X hz₁sec.2
  have hYfix : Y.map σ = Y := map_eq_self_of_le_polar hσ hYX
  have hπY : (polar c ι Y).map σ = polar c ι Y :=
    IsPolarHomology.map_polar hP hT c hdeg hι hsec hℓ h5 hX1 hXP hσ hz₀ hz₀X hz₁ hσ01 hYfix
  have hHhyper : finrank K (polar c ι Y) + 1 = finrank K (⊤ : Submodule K W) :=
    finrank_polar_add_one hP hT c hdeg hι hsec hℓ htop hY1 le_top
  by_cases hXY : X ≤ polar c ι Y
  · exact hXY
  · exfalso
    have heq : polar c ι Y = polar c ι X :=
      eq_polar_of_map_eq_of_not_le hP hT c hdeg hι hsec hℓ h5 hX1 hXP hσ hlam1 hscalar hπY
        hHhyper hXY
    have hXYeq : X = Y :=
      eq_of_polar_eq hP hT c hdeg hι hsec hℓ htop hX1 le_top hXP hY1 le_top hYP heq.symm
    have hself : Y ≤ polar c ι Y := by rw [heq]; exact hYX
    exact hYP ((le_polar_self_iff hP hT c hdeg hι hsec hℓ htop hY1 le_top).1 hself)

end Polarity

end CFSG.Geometry.GeneralizedQuadrangles

end
