module

public import CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.FixedTranslate

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CoxeterSystem

section Datum

variable {G : Type*} [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*} [Group W]
  {cs : CoxeterSystem M W} {p : ℕ} (D : CurtisDatum G cs p)

theorem nW_mul (a b : W) : ∃ h ∈ D.H, D.nW a * D.nW b = D.nW (a * b) * h := by
  obtain ⟨h₀, hh₀, e₀⟩ := nW_inv_mul D (a⁻¹) 1
  obtain ⟨h₁, hh₁, e₁⟩ := nW_inv_mul D (a⁻¹) b
  simp only [D.nW_one, mul_one, inv_inv] at e₀ e₁
  refine ⟨h₁ * ((D.nW b)⁻¹ * h₀⁻¹ * D.nW b), mul_mem hh₁ (D.nW_normH b (inv_mem hh₀)), ?_⟩
  have ha : D.nW a = (D.nW (a⁻¹))⁻¹ * h₀⁻¹ := by rw [e₀]; group
  rw [ha]
  calc (D.nW (a⁻¹))⁻¹ * h₀⁻¹ * D.nW b
      = (D.nW (a⁻¹))⁻¹ * (D.nW b * ((D.nW b)⁻¹ * h₀⁻¹ * D.nW b)) := by group
    _ = ((D.nW (a⁻¹))⁻¹ * D.nW b) * ((D.nW b)⁻¹ * h₀⁻¹ * D.nW b) := by group
    _ = (D.nW (a * b) * h₁) * ((D.nW b)⁻¹ * h₀⁻¹ * D.nW b) := by rw [e₁]
    _ = D.nW (a * b) * (h₁ * ((D.nW b)⁻¹ * h₀⁻¹ * D.nW b)) := by group

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {ρ : Representation k G V}
  [Finite G]

theorem linearIndependent_sub_one_translates [Fact p.Prime] [CharP k p] (hρ : IsSimpleRep ρ)
    {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ) (x : W) {m : ℕ}
    (b : Fin m → W)
    (hsep : ∀ i j, i ≠ j → ∀ ω : List B, cs.IsReduced ω → cs.wordProd ω = (b i)⁻¹ * b j →
      ∃ s ∈ ω, μ s = D.dScalar χ s)
    (hmove : ∀ i j, ∀ ω : List B, cs.IsReduced ω → cs.wordProd ω = (b i)⁻¹ * (x * b j) →
      ∃ s ∈ ω, μ s = D.dScalar χ s) :
    LinearIndependent k fun j => (ρ (D.nW x) - 1) (ρ (D.nW (b j)) y) := by
  obtain ⟨f, hf, hfy⟩ := D.exists_form hρ ht.1 ht.2.1
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have key : ∀ j, f (ρ ((D.nW (b i))⁻¹) ((ρ (D.nW x) - 1) (ρ (D.nW (b j)) y)))
      = -(if j = i then 1 else 0) := by
    intro j
    have hz : ρ ((D.nW (b i))⁻¹) ((ρ (D.nW x) - 1) (ρ (D.nW (b j)) y))
        = ρ ((D.nW (b i))⁻¹ * (D.nW x * D.nW (b j))) y
          - ρ ((D.nW (b i))⁻¹ * D.nW (b j)) y := by
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, act_mul]
    rw [hz, map_sub]
    have hfirst : f (ρ ((D.nW (b i))⁻¹ * (D.nW x * D.nW (b j))) y) = 0 := by
      obtain ⟨h₁, hh₁, e₁⟩ := nW_mul D x (b j)
      obtain ⟨h₂, hh₂, e₂⟩ := nW_inv_mul D (b i) (x * b j)
      obtain ⟨ω, hω, hωe⟩ := cs.exists_isReduced ((b i)⁻¹ * (x * b j))
      rw [e₁, ← mul_assoc, e₂, mul_assoc, hωe]
      rw [form_nW_mul D ρ ht hf hfy hω (mul_mem hh₂ hh₁)]
      have hco : D.coinvScalar χ μ ω = 0 := by
        obtain ⟨s, hs, hμs⟩ := hmove i j ω hω hωe.symm
        exact List.prod_eq_zero (List.mem_map.mpr ⟨s, hs, sub_eq_zero.mpr hμs⟩)
      rw [hco, mul_zero]
    have hsecond : f (ρ ((D.nW (b i))⁻¹ * D.nW (b j)) y) = if j = i then 1 else 0 := by
      by_cases hji : j = i
      · subst hji
        rw [inv_mul_cancel, map_one, Module.End.one_apply, hfy]
        simp
      · rw [if_neg hji]
        obtain ⟨h, hh, e⟩ := nW_inv_mul D (b i) (b j)
        obtain ⟨ω, hω, hωe⟩ := cs.exists_isReduced ((b i)⁻¹ * b j)
        rw [e, hωe]
        rw [form_nW_mul D ρ ht hf hfy hω hh]
        have hco : D.coinvScalar χ μ ω = 0 := by
          obtain ⟨s, hs, hμs⟩ := hsep i j (Ne.symm hji) ω hω hωe.symm
          exact List.prod_eq_zero (List.mem_map.mpr ⟨s, hs, sub_eq_zero.mpr hμs⟩)
        rw [hco, mul_zero]
    rw [hfirst, hsecond, zero_sub]
  have h2 := congrArg (fun z => f (ρ ((D.nW (b i))⁻¹) z)) hc
  simp only [map_sum, map_smul, map_zero] at h2
  simp only [key, smul_eq_mul, mul_neg, mul_ite, mul_one, mul_zero, Finset.sum_neg_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h2
  exact neg_eq_zero.mp h2

theorem le_finrank_range_sub_one [Fact p.Prime] [CharP k p] [Module.Finite k V]
    (hρ : IsSimpleRep ρ) {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ) (x : W)
    {m : ℕ} (b : Fin m → W)
    (hsep : ∀ i j, i ≠ j → ∀ ω : List B, cs.IsReduced ω → cs.wordProd ω = (b i)⁻¹ * b j →
      ∃ s ∈ ω, μ s = D.dScalar χ s)
    (hmove : ∀ i j, ∀ ω : List B, cs.IsReduced ω → cs.wordProd ω = (b i)⁻¹ * (x * b j) →
      ∃ s ∈ ω, μ s = D.dScalar χ s) :
    m ≤ Module.finrank k (LinearMap.range (ρ (D.nW x) - 1)) := by
  have hli := linearIndependent_sub_one_translates D hρ ht x b hsep hmove
  let T : V →ₗ[k] V := ρ (D.nW x) - 1
  let w : Fin m → LinearMap.range T :=
    fun j => ⟨T (ρ (D.nW (b j)) y), ρ (D.nW (b j)) y, rfl⟩
  have hw : LinearIndependent k w := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro c hc
    refine hli c ?_
    have h := congrArg (fun z => (LinearMap.range T).subtype z) hc
    simpa [T, w, map_sum, map_smul] using h
  simpa [T] using hw.fintype_card_le_finrank

end Datum

section Chev

open CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ} [CharP K p]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}

theorem le_finrank_range_sub_one_of_isChevType [Fact p.Prime] {k V : Type*} [Field k]
    [Algebra K k] [AddCommGroup V] [Module k V] [CharP k p] [Module.Finite k V]
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)} (ht : IsChevType τ K p hw ρ y χ J)
    {v : Fin τ.rank → ℤ} (hv : ∀ j ∈ J, reflect τ j v = v) (x : WeylGroup τ) {m : ℕ}
    (b : Fin m → WeylGroup τ) (hinj : ∀ i j, i ≠ j → b i • v ≠ b j • v)
    (hmove : ∀ i j, b i • v ≠ (x * b j) • v) :
    m ≤ Module.finrank k (LinearMap.range (ρ ((chevDatum τ K p hw).nW x) - 1)) := by
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
  refine le_finrank_range_sub_one (chevDatum τ K p hw) hρ hμ x b ?_ ?_
  · intro i j hij ω hω hωe
    obtain ⟨s, hsω, hsJ⟩ :=
      CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.exists_letter_notMem_of_smul_ne hv
        (l := ω) fun h => hinj i j hij (by
          rw [hωe, mul_smul] at h
          have := congrArg (fun z => b i • z) h
          simpa [smul_smul] using this.symm)
    exact ⟨s, hsω, mu_eq_dScalar_of_notMem ht hμ hsJ⟩
  · intro i j ω hω hωe
    obtain ⟨s, hsω, hsJ⟩ :=
      CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.exists_letter_notMem_of_smul_ne hv
        (l := ω) fun h => hmove i j (by
          rw [hωe, mul_smul] at h
          have := congrArg (fun z => b i • z) h
          simpa [smul_smul] using this.symm)
    exact ⟨s, hsω, mu_eq_dScalar_of_notMem ht hμ hsJ⟩

end Chev

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
