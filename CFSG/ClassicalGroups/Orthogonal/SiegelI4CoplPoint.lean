module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4CoplAxis

public section

namespace CFSG.ClassicalGroups.Alternating

open Module

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}

theorem isLine_span_pair (hBN : BN.IsAlt) {a c : N} (hac : BN a c = 0)
    (hind : LinearIndependent K ![a, c]) : IsLine BN (Submodule.span K {a, c}) :=
  ⟨isotropic_span_pair hBN hac, by
    rw [← Matrix.range_cons_cons_empty a c ![], finrank_span_eq_card hind, Fintype.card_fin]⟩

theorem IsLine.exists_pair_of_mem {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) {a : N} (ha : a ∈ ℓ)
    (ha0 : a ≠ 0) : ∃ c ∈ ℓ, LinearIndependent K ![a, c] ∧ ℓ = Submodule.span K {a, c} := by
  obtain ⟨c, hcℓ, hind⟩ := exists_mem_linearIndependent_pair hℓ.2.ge ha ha0
  refine ⟨c, hcℓ, hind, ?_⟩
  have hle : Submodule.span K {a, c} ≤ ℓ := by
    rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact ha
    · exact hcℓ
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [hℓ.2, ← Matrix.range_cons_cons_empty a c ![], finrank_span_eq_card hind,
    Fintype.card_fin]

theorem linearIndependent_triple_of_notMem {a b c : N} (hab : LinearIndependent K ![a, b])
    (hc : c ∉ Submodule.span K {a, b}) : LinearIndependent K ![a, b, c] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hg
  have hg2 : g 2 = 0 := by
    by_contra h2
    apply hc
    have : c = (-(g 0 / g 2)) • a + (-(g 1 / g 2)) • b := by
      have h3 : g 2 • c = -(g 0 • a + g 1 • b) := by
        rw [eq_neg_iff_add_eq_zero, ← hg]
        abel
      have := congrArg (fun v => (g 2)⁻¹ • v) h3
      simp only [smul_smul, inv_mul_cancel₀ h2, one_smul, smul_neg] at this
      rw [this]
      simp only [smul_add, smul_smul, div_eq_inv_mul, neg_mul, neg_smul, mul_comm]
      abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  rw [hg2, zero_smul, add_zero] at hg
  have hg' : g 0 • a + g 1 • b = 0 := by simpa using hg
  obtain ⟨h0, h1⟩ := LinearIndependent.pair_iff.mp hab (g 0) (g 1) hg'
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact hg2

theorem linearIndependent_pair_of_triple₀₂ {a b c : N} (h : LinearIndependent K ![a, b, c]) :
    LinearIndependent K ![a, c] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Fintype.linearIndependent_iff] at h
  have := h ![s, 0, t] (by simpa [Fin.sum_univ_three] using hst)
  exact ⟨by simpa using this 0, by simpa using this 2⟩

theorem linearIndependent_pair_of_triple₁₂ {a b c : N} (h : LinearIndependent K ![a, b, c]) :
    LinearIndependent K ![b, c] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Fintype.linearIndependent_iff] at h
  have := h ![0, s, t] (by simpa [Fin.sum_univ_three] using hst)
  exact ⟨by simpa using this 1, by simpa using this 2⟩

theorem exists_notMem_span_pair {π : Submodule K N} (hπ : IsPlane BN π) {a b : N}
    (hab : LinearIndependent K ![a, b]) : ∃ c ∈ π, c ∉ Submodule.span K {a, b} := by
  by_contra hcon
  push Not at hcon
  have hle : π ≤ Submodule.span K {a, b} := hcon
  have := Submodule.finrank_mono hle
  rw [hπ.2, ← Matrix.range_cons_cons_empty a b ![], finrank_span_eq_card hab,
    Fintype.card_fin] at this
  omega

theorem lineElt_self_smul [CharP K 2] (hBN : BN.IsAlt) (a : N) (l : K) :
    lineElt hBN a (l • a) = 1 := by
  have hac : BN a (l • a) = 0 := by rw [map_smul, hBN.self_eq_zero, smul_zero]
  refine Gsp.ext' fun x => ?_
  rw [lineElt_app hBN hac, Gsp.app_one]
  simp only [map_smul, smul_eq_mul, smul_smul]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (norm := module) (BN x a * l) • (h2 • a)


theorem Gsp.map_lin_map_lin_inv (g : Gsp BN) (S : Submodule K N) :
    (S.map g⁻¹.lin).map g.lin = S := by
  ext x
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    simpa [Gsp.lin_apply, Gsp.app_app_inv] using hz
  · intro hx
    exact ⟨g⁻¹.app x, ⟨x, hx, rfl⟩, by simp [Gsp.lin_apply, Gsp.app_app_inv]⟩

theorem exists_planeFrame_of_linearIndependent (hBNnd : BN.Nondegenerate) {π : Submodule K N}
    (hπ : IsPlane BN π) {a b c : N} (ha : a ∈ π) (hb : b ∈ π) (hc : c ∈ π)
    (hind : LinearIndependent K ![a, b, c]) :
    ∃ F : PlaneFrame BN π, F.e 0 = a ∧ F.e 1 = b ∧ F.e 2 = c := by
  have hmem : ∀ i, ![a, b, c] i ∈ π := by
    intro i
    fin_cases i <;> simp [ha, hb, hc]
  have hspan : Submodule.span K (Set.range ![a, b, c]) = π := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hmem i
    · rw [finrank_span_eq_card hind, hπ.2, Fintype.card_fin]
  have hf : ∀ i : Fin 3, ∃ x : N, ∀ j : Fin 3,
      BN x (![a, b, c] j) = if i = j then 1 else 0 :=
    fun i => exists_apply_eq_of_linearIndependent hBNnd hind (fun j => if i = j then 1 else 0)
  choose f hf using hf
  refine ⟨⟨![a, b, c], f, hmem, fun w hw => ?_, hf⟩, rfl, rfl, rfl⟩
  have hw' : w ∈ Submodule.span K (Set.range ![a, b, c]) := by
    rw [hspan]
    exact hw
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hw'
  refine ⟨t 0, t 1, t 2, ?_⟩
  rw [← ht, Fin.sum_univ_three]

theorem exists_eq_mul_lineElt_of_mem_planeGroup [CharP K 2] (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) {π : Submodule K N} (hπ : IsPlane BN π) {a b c : N} (ha : a ∈ π)
    (hb : b ∈ π) (hc : c ∈ π)
    (hind : LinearIndependent K ![a, b, c]) {g : Gsp BN} (hg : g ∈ planeGroup hBN π) :
    ∃ α β γ : K,
      g = lineElt hBN a (α • b) * lineElt hBN a (β • c) * lineElt hBN b (γ • c) := by
  obtain ⟨F, h0, h1, h2⟩ := exists_planeFrame_of_linearIndependent hBNnd hπ ha hb hc hind
  obtain ⟨x, y, z, hxyz⟩ := F.exists_phi_eq hBN hπ.1 (planeGroup_le_planeSub hBN hπ.1 hg)
  refine ⟨x, y, z, ?_⟩
  rw [hxyz, PlaneFrame.phi, h0, h1, h2,
    lineElt_mul_right hBN hπ.1 ha (π.smul_mem x hb) (π.smul_mem y hc)]

end CFSG.ClassicalGroups.Alternating

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

@[expose] noncomputable def planePt (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V))
    (π : Submodule K N) (a : N) : Submodule K V :=
  ⨅ (ℓ : Submodule K N) (_ : IsLine BN ℓ ∧ a ∈ ℓ ∧ ℓ ≤ π), famSpace hBN ρ ℓ

theorem mem_planePt_iff (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V)) {π : Submodule K N}
    {a : N} {x : V} :
    x ∈ planePt hBN ρ π a ↔ ∀ ℓ : Submodule K N, IsLine BN ℓ → a ∈ ℓ → ℓ ≤ π →
      x ∈ famSpace hBN ρ ℓ := by
  simp only [planePt, Submodule.mem_iInf, and_imp]

theorem planePt_le (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V)) {π ℓ : Submodule K N} {a : N}
    (hℓ : IsLine BN ℓ) (ha : a ∈ ℓ) (hℓπ : ℓ ≤ π) : planePt hBN ρ π a ≤ famSpace hBN ρ ℓ :=
  fun _ hx => (mem_planePt_iff hBN ρ).mp hx ℓ hℓ ha hℓπ

theorem planePt_smul (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V)) (π : Submodule K N) {c : K}
    (hc : c ≠ 0) (a : N) : planePt hBN ρ π (c • a) = planePt hBN ρ π a := by
  ext x
  simp only [mem_planePt_iff, Submodule.smul_mem_iff _ hc]

theorem planePt_map (hBN : BN.IsAlt) (ρ : Gsp BN →* (V ≃ₗ[K] V)) (g : Gsp BN)
    (π : Submodule K N) (a : N) :
    planePt hBN ρ (π.map g.lin) (g.app a) = (planePt hBN ρ π a).map (ρ g : V →ₗ[K] V) := by
  ext x
  rw [Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨(ρ g)⁻¹ x, ?_, by simp⟩
    rw [mem_planePt_iff]
    intro ℓ hℓ ha hℓπ
    have h1 := (mem_planePt_iff hBN ρ).mp hx (ℓ.map g.lin) (hℓ.map g) ⟨a, ha, rfl⟩
      (Submodule.map_mono hℓπ)
    rw [famSpace_map, Submodule.mem_map] at h1
    obtain ⟨z, hz, hzx⟩ := h1
    have : (ρ g)⁻¹ x = z := by rw [← hzx]; simp
    rw [this]
    exact hz
  · rintro ⟨y, hy, rfl⟩
    rw [mem_planePt_iff]
    intro ℓ' hℓ' ha hℓπ
    have hℓ : IsLine BN (ℓ'.map g⁻¹.lin) := hℓ'.map g⁻¹
    have h1 := (mem_planePt_iff hBN ρ).mp hy (ℓ'.map g⁻¹.lin) hℓ ⟨g.app a, ha, by
        simp [Gsp.lin_apply, Gsp.app_inv_app]⟩ (by
        calc ℓ'.map g⁻¹.lin ≤ (π.map g.lin).map g⁻¹.lin := Submodule.map_mono hℓπ
          _ = π := by
            have := Gsp.map_lin_map_lin_inv g⁻¹ π
            simpa using this)
    have h2 := Gsp.map_lin_map_lin_inv g ℓ'
    have : famSpace hBN ρ ℓ' = (famSpace hBN ρ (ℓ'.map g⁻¹.lin)).map (ρ g : V →ₗ[K] V) := by
      rw [← famSpace_map, h2]
    rw [this]
    exact Submodule.mem_map_of_mem h1

section Point

variable {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}
  (hs : I4Setting hBN Qf ρ) (hcopl : ∀ π, IsPlane BN π → Copl (planeFamily hBN ρ π))

include hs hcopl

theorem map_mem_piGroup_of_isLine {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) {P W : Submodule K V}
    (hP : P ≤ famSpace hBN ρ ℓ) (hW : famSpace hBN ρ ℓ ≤ W) {g : Gsp BN}
    (hg : g ∈ planeGroup hBN ℓ) : ρ g ∈ piGroup Qf P W := by
  by_cases hg1 : g = 1
  · rw [hg1, map_one]
    exact one_mem _
  · have hax := movedSpace_eq_famSpace_of_isLine hs hcopl hℓ hg hg1
    exact isLongRootElement_mem_piGroup (hs.isLongRootElement_map_of_isLine hℓ hg hg1)
      (hax ▸ hP) (hax ▸ hW)

omit hcopl in
theorem map_lineElt_ne_one {a c : N} (hac : BN a c = 0) (hind : LinearIndependent K ![a, c]) :
    ρ (lineElt hBN a c) ≠ 1 := fun h =>
  lineElt_ne_one hBN hs.nondegN hac hind (hs.inj (by rw [h, map_one]))

theorem famSpace_mem_axes {ℓ π : Submodule K N} (hℓ : IsLine BN ℓ) (hℓπ : ℓ ≤ π) :
    famSpace hBN ρ ℓ ∈ axes (planeFamily hBN ρ π) := by
  obtain ⟨g, hg, hg1⟩ := exists_ne_one_mem_planeGroup hBN hs.nondegN hℓ
  exact ⟨ρ g, ⟨g, planeGroup_mono hBN hℓπ hg, rfl⟩,
    fun h => hg1 (hs.inj (by rw [h, map_one])),
    (movedSpace_eq_famSpace_of_isLine hs hcopl hℓ hg hg1).symm⟩

theorem finrank_planePt {π : Submodule K N} (hπ : IsPlane BN π) {a : N} (ha : a ∈ π)
    (ha0 : a ≠ 0) : finrank K (planePt hBN ρ π a) = 1 := by
  have h2 : 2 ≤ finrank K π := by rw [hπ.2]; norm_num
  obtain ⟨c₁, hc₁, hind₁⟩ := exists_mem_linearIndependent_pair h2 ha ha0
  obtain ⟨c₂, hc₂, hnot⟩ := exists_notMem_span_pair hπ hind₁
  have hind₃ := linearIndependent_triple_of_notMem hind₁ hnot
  have hind₂ := linearIndependent_pair_of_triple₀₂ hind₃
  obtain ⟨F, hF0, hF1, hF2⟩ :=
    exists_planeFrame_of_linearIndependent hs.nondegN hπ ha hc₁ hc₂ hind₃
  have hac₁ : BN a c₁ = 0 := hπ.1 a ha c₁ hc₁
  have hac₂ : BN a c₂ = 0 := hπ.1 a ha c₂ hc₂
  have hℓ₁ : IsLine BN (Submodule.span K {a, c₁}) := isLine_span_pair hBN hac₁ hind₁
  have hℓ₂ : IsLine BN (Submodule.span K {a, c₂}) := isLine_span_pair hBN hac₂ hind₂
  have hspan : ∀ {x y : N}, x ∈ π → y ∈ π → Submodule.span K {x, y} ≤ π := by
    intro x y hx hy
    rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact hx
    · exact hy
  have hℓ₁π := hspan ha hc₁
  have hℓ₂π := hspan ha hc₂
  have haℓ₁ : a ∈ Submodule.span K {a, c₁} := Submodule.subset_span (by simp)
  have haℓ₂ : a ∈ Submodule.span K {a, c₂} := Submodule.subset_span (by simp)
  have hne : Submodule.span K {a, c₁} ≠ Submodule.span K {a, c₂} := by
    intro h
    apply hnot
    rw [h]
    exact Submodule.subset_span (by simp)
  have hA : famSpace hBN ρ (Submodule.span K {a, c₁}) ≠ famSpace hBN ρ (Submodule.span K {a, c₂}) :=
    fun h => hne (famSpace_injective_of_isLine hs hcopl hℓ₁ hℓ₂ h)
  have hE := hs.isSiegelFamily_planeFamily hπ
  obtain ⟨hP1, -, hW3, hWs⟩ := hE.pair hs.nondeg (famSpace_mem_axes hs hcopl hℓ₁ hℓ₁π)
    (famSpace_mem_axes hs hcopl hℓ₂ hℓ₂π) hA
  set P := famSpace hBN ρ (Submodule.span K {a, c₁}) ⊓ famSpace hBN ρ (Submodule.span K {a, c₂})
    with hPdef
  set W := famSpace hBN ρ (Submodule.span K {a, c₁}) ⊔ famSpace hBN ρ (Submodule.span K {a, c₂})
    with hWdef
  have hPW : P ≤ W := inf_le_left.trans le_sup_left
  have hpi : ∀ c ∈ π, ρ (lineElt hBN a c) ∈ piGroup Qf P W := by
    intro c hc
    obtain ⟨x₀, x₁, x₂, hcx⟩ := F.span c hc
    rw [hF0, hF1, hF2] at hcx
    have hx₀ : x₀ • a ∈ π := π.smul_mem _ ha
    have hx₁ : x₁ • c₁ ∈ π := π.smul_mem _ hc₁
    have hx₂ : x₂ • c₂ ∈ π := π.smul_mem _ hc₂
    have : lineElt hBN a c = lineElt hBN a (x₁ • c₁) * lineElt hBN a (x₂ • c₂) := by
      rw [hcx, ← lineElt_mul_right hBN hπ.1 ha (π.add_mem hx₀ hx₁) hx₂,
        ← lineElt_mul_right hBN hπ.1 ha hx₀ hx₁, lineElt_self_smul hBN a x₀, one_mul]
    rw [this, map_mul]
    refine mul_mem (map_mem_piGroup_of_isLine hs hcopl hℓ₁ inf_le_left le_sup_left ?_)
      (map_mem_piGroup_of_isLine hs hcopl hℓ₂ inf_le_right le_sup_right ?_)
    · exact lineElt_mem_planeGroup hBN haℓ₁
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · exact lineElt_mem_planeGroup hBN haℓ₂
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hPle : P ≤ planePt hBN ρ π a := by
    intro x hx
    rw [mem_planePt_iff]
    intro ℓ hℓ haℓ hℓπ
    revert hx
    suffices h : P ≤ famSpace hBN ρ ℓ from fun hx => h hx
    obtain ⟨c, hcℓ, hindc, hℓeq⟩ := hℓ.exists_pair_of_mem haℓ ha0
    have hc : c ∈ π := hℓπ hcℓ
    have hac : BN a c = 0 := hπ.1 a ha c hc
    have hg1 : lineElt hBN a c ≠ 1 := lineElt_ne_one hBN hs.nondegN hac hindc
    have hg : lineElt hBN a c ∈ planeGroup hBN ℓ := by
      rw [hℓeq]
      exact lineElt_mem_planeGroup hBN (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp))
    have hmem := (mem_piGroup_iff_of_ne_one hs.nondeg hWs hP1 hPW
      (map_lineElt_ne_one hs hac hindc)).mp (hpi c hc)
    rw [← movedSpace_eq_famSpace_of_isLine hs hcopl hℓ hg hg1]
    exact hmem.2.1
  have hle : planePt hBN ρ π a ≤ P :=
    le_inf (planePt_le hBN ρ hℓ₁ haℓ₁ hℓ₁π) (planePt_le hBN ρ hℓ₂ haℓ₂ hℓ₂π)
  rw [le_antisymm hle hPle]
  exact hP1

theorem planePt_le_famSpace {π : Submodule K N} (hπ : IsPlane BN π) {a : N} (ha : a ∈ π)
    (ha0 : a ≠ 0) : planePt hBN ρ π a ≤ famSpace hBN ρ π := by
  obtain ⟨c, hcπ, hind⟩ := exists_mem_linearIndependent_pair (by rw [hπ.2]; norm_num) ha ha0
  have hℓ := isLine_span_pair hBN (hπ.1 a ha c hcπ) hind
  have hℓπ : Submodule.span K {a, c} ≤ π := by
    rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact ha
    · exact hcπ
  exact (planePt_le hBN ρ hℓ (Submodule.subset_span (by simp)) hℓπ).trans
    (famSpace_mono hBN ρ hℓπ)

theorem planePt_ne {π : Submodule K N} (hπ : IsPlane BN π) {a b : N} (ha : a ∈ π) (hb : b ∈ π)
    (hab : LinearIndependent K ![a, b]) : planePt hBN ρ π a ≠ planePt hBN ρ π b := by
  intro heq
  have ha0 : a ≠ 0 := by simpa using hab.ne_zero (0 : Fin 2)
  have hb0 : b ≠ 0 := by simpa using hab.ne_zero (1 : Fin 2)
  obtain ⟨c, hc, hnot⟩ := exists_notMem_span_pair hπ hab
  have hind₃ := linearIndependent_triple_of_notMem hab hnot
  have hac_ind := linearIndependent_pair_of_triple₀₂ hind₃
  have hbc_ind := linearIndependent_pair_of_triple₁₂ hind₃
  have hspan : ∀ {x y : N}, x ∈ π → y ∈ π → Submodule.span K {x, y} ≤ π := by
    intro x y hx hy
    rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact hx
    · exact hy
  have hℓab := isLine_span_pair hBN (hπ.1 a ha b hb) hab
  have hℓac := isLine_span_pair hBN (hπ.1 a ha c hc) hac_ind
  have hℓbc := isLine_span_pair hBN (hπ.1 b hb c hc) hbc_ind
  set Q := planePt hBN ρ π a with hQdef
  have hQ1 : finrank K Q = 1 := finrank_planePt hs hcopl hπ ha ha0
  have hQW : Q ≤ famSpace hBN ρ π := planePt_le_famSpace hs hcopl hπ ha ha0
  have hWs := qf_eq_zero_of_mem_famSpace_isPlane hs hcopl hπ
  have hpi : planeFamily hBN ρ π ≤ piGroup Qf Q (famSpace hBN ρ π) := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨α, β, γ, rfl⟩ := exists_eq_mul_lineElt_of_mem_planeGroup hBN hs.nondegN hπ ha hb hc
      hind₃ hg
    rw [map_mul, map_mul]
    refine mul_mem (mul_mem ?_ ?_) ?_
    · refine map_mem_piGroup_of_isLine hs hcopl hℓab
        (planePt_le hBN ρ hℓab (Submodule.subset_span (by simp)) (hspan ha hb))
        (famSpace_mono hBN ρ (hspan ha hb)) ?_
      exact lineElt_mem_planeGroup hBN (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · refine map_mem_piGroup_of_isLine hs hcopl hℓac
        (planePt_le hBN ρ hℓac (Submodule.subset_span (by simp)) (hspan ha hc))
        (famSpace_mono hBN ρ (hspan ha hc)) ?_
      exact lineElt_mem_planeGroup hBN (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · refine map_mem_piGroup_of_isLine hs hcopl hℓbc
        (heq ▸ planePt_le hBN ρ hℓbc (Submodule.subset_span (by simp)) (hspan hb hc))
        (famSpace_mono hBN ρ (hspan hb hc)) ?_
      exact lineElt_mem_planeGroup hBN (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hcard := natCard_piGroup hs.nondeg hWs hQ1 hQW
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hfin : Finite (piGroup Qf Q (famSpace hBN ρ π)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
  have hle := Subgroup.card_le_of_le hpi
  rw [(hs.isSiegelFamily_planeFamily hπ).card, hcard,
    finrank_famSpace_of_isPlane hs hcopl hπ] at hle
  have := (pow_le_pow_iff_right₀ hq).mp hle
  omega

theorem famSpace_eq_sup_planePt {π ℓ : Submodule K N} (hπ : IsPlane BN π) (hℓ : IsLine BN ℓ)
    (hℓπ : ℓ ≤ π) {a b : N} (ha : a ∈ ℓ) (hb : b ∈ ℓ) (hab : LinearIndependent K ![a, b]) :
    famSpace hBN ρ ℓ = planePt hBN ρ π a ⊔ planePt hBN ρ π b := by
  have ha0 : a ≠ 0 := by simpa using hab.ne_zero (0 : Fin 2)
  have hb0 : b ≠ 0 := by simpa using hab.ne_zero (1 : Fin 2)
  have hA := finrank_famSpace_of_isLine hs hcopl hℓ
  have hP₁ := finrank_planePt hs hcopl hπ (hℓπ ha) ha0
  have hP₂ := finrank_planePt hs hcopl hπ (hℓπ hb) hb0
  have hne := planePt_ne hs hcopl hπ (hℓπ ha) (hℓπ hb) hab
  have hle : planePt hBN ρ π a ⊔ planePt hBN ρ π b ≤ famSpace hBN ρ ℓ :=
    sup_le (planePt_le hBN ρ hℓ ha hℓπ) (planePt_le hBN ρ hℓ hb hℓπ)
  have hge : 2 ≤ finrank K ↥(planePt hBN ρ π a ⊔ planePt hBN ρ π b) := by
    by_contra hlt
    push Not at hlt
    have h1 : planePt hBN ρ π a = planePt hBN ρ π a ⊔ planePt hBN ρ π b :=
      Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    have h2 : planePt hBN ρ π b = planePt hBN ρ π a ⊔ planePt hBN ρ π b :=
      Submodule.eq_of_le_of_finrank_le le_sup_right (by omega)
    exact hne (h1.trans h2.symm)
  exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm

end Point

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
