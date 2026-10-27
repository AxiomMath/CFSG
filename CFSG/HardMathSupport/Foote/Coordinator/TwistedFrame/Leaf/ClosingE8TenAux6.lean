module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux4
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenData

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

set_option linter.unusedSectionVars false

variable {K L : Type} [Field K] [Field L] [Algebra K L]


section Extract

variable {U : Submodule L (Fn L)}

theorem Eop_sq_zero {γ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ lxRoots) {u : Fn L}
    (hu : ∀ ν, ν ∉ deg1Roots → u ν = 0) : Eop aE8 γ (Eop aE8 γ u) = 0 := by
  obtain ⟨hγr, hγ0, -⟩ := lxRoots_data γ hγ
  funext ν
  rw [Eop_apply, Eop_apply]
  show ((aE8 γ (ν - γ) : ℤ) : L) * (((aE8 γ (ν - γ - γ) : ℤ) : L) * u (ν - γ - γ)) = (0 : Fn L) ν
  by_cases h1 : u (ν - γ - γ) = 0
  · rw [h1]
    simp
  have hμ : ν - γ - γ ∈ deg1Roots := by
    by_contra hn
    exact h1 (hu _ hn)
  by_cases h2 : aE8 γ (ν - γ - γ) = 0
  · rw [h2]
    simp
  have hr1 : ν - γ ∈ rootFinset Tag.E8 := by
    by_contra hn
    refine h2 ((adm_aE8 γ hγr hγ0 _ hμ).2 ?_)
    rw [show γ + (ν - γ - γ) = ν - γ by abel]
    exact hn
  have hμ' : ν - γ ∈ deg1Roots := by
    rw [mem_deg1Roots]
    refine ⟨mem_rootFinset.1 hr1, ?_⟩
    have h7 := (mem_deg1Roots.1 hμ).2
    have : (ν - γ) 7 = (ν - γ - γ) 7 + γ 7 := by simp
    rw [this, h7, hγ0]
    norm_num
  by_cases h3 : aE8 γ (ν - γ) = 0
  · rw [h3]
    simp
  exfalso
  have hr2 : ν ∈ rootFinset Tag.E8 := by
    by_contra hn
    refine h3 ((adm_aE8 γ hγr hγ0 _ hμ').2 ?_)
    rw [show γ + (ν - γ) = ν by abel]
    exact hn
  refine no_string (ν - γ - γ) hμ γ hγ ?_ ?_
  · rw [sub_add_cancel]
    exact hr1
  · rw [show ν - γ - γ + γ + γ = ν by abel]
    exact hr2

theorem inv_of_actOp {γ : Fin Tag.E8.rank → ℤ} {t : L} (ht : t ≠ 0)
    (h : ∀ u ∈ U, actOp aE8 γ t u ∈ U) : ∀ u ∈ U, Eop aE8 γ u ∈ U := by
  intro u hu
  have h1 := h u hu
  have : Eop aE8 γ u = t⁻¹ • (actOp aE8 γ t u - u) := by
    rw [actOp_apply, actFun_eq, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]
  rw [this]
  exact U.smul_mem _ (U.sub_mem h1 hu)

theorem inv_of_pair {γ₁ γ₂ : Fin Tag.E8.rank → ℤ} {q : ℕ} (hq : 2 ≤ q) (C : Finset L)
    (hC : q ^ 2 ≤ C.card) {ε : L} (hε : ε ≠ 0)
    (h : ∀ c ∈ C, ∀ u ∈ U, actOp aE8 γ₁ c (actOp aE8 γ₂ (ε * c ^ q) u) ∈ U) :
    (∀ u ∈ U, Eop aE8 γ₁ u ∈ U) ∧ (∀ u ∈ U, Eop aE8 γ₂ u ∈ U) := by
  have key : ∀ u ∈ U, Eop aE8 γ₁ u ∈ U ∧ Eop aE8 γ₂ u ∈ U := by
    intro u hu
    have he : Function.Injective (![0, 1, q, q + 1] : Fin 4 → ℕ) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
    have hlt : ∀ i, (![0, 1, q, q + 1] : Fin 4 → ℕ) i < C.card := by
      intro i
      have h2 : q + 1 < q ^ 2 := by nlinarith
      fin_cases i
      · show (0 : ℕ) < C.card
        omega
      · show (1 : ℕ) < C.card
        omega
      · show q < C.card
        omega
      · show q + 1 < C.card
        omega
    have hsum : ∀ c ∈ C, ∑ i, c ^ (![0, 1, q, q + 1] : Fin 4 → ℕ) i •
        (![u, Eop aE8 γ₁ u, ε • Eop aE8 γ₂ u, ε • Eop aE8 γ₁ (Eop aE8 γ₂ u)] : Fin 4 → Fn L) i
        ∈ U := by
      intro c hc
      have hh := h c hc u hu
      have eq : ∑ i, c ^ (![0, 1, q, q + 1] : Fin 4 → ℕ) i •
          (![u, Eop aE8 γ₁ u, ε • Eop aE8 γ₂ u, ε • Eop aE8 γ₁ (Eop aE8 γ₂ u)] : Fin 4 → Fn L) i
          = actOp aE8 γ₁ c (actOp aE8 γ₂ (ε * c ^ q) u) := by
        simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
          actOp, LinearMap.add_apply,
          LinearMap.smul_apply, LinearMap.id_apply, map_add, map_smul]
        module
      rw [eq]
      exact hh
    have hext := poly_extract U C _ he hlt _ hsum
    refine ⟨hext 1, ?_⟩
    have h2 := hext 2
    have h3 : Eop aE8 γ₂ u = ε⁻¹ • (ε • Eop aE8 γ₂ u) := by
      rw [smul_smul, inv_mul_cancel₀ hε, one_smul]
    rw [h3]
    exact U.smul_mem _ h2
  exact ⟨fun u hu => (key u hu).1, fun u hu => (key u hu).2⟩

theorem strip_middle (hsupp : ∀ u ∈ U, ∀ ν, ν ∉ deg1Roots → u ν = 0)
    {γ₃ : Fin Tag.E8.rank → ℤ} (hγ₃ : γ₃ ∈ lxRoots) (hE : ∀ u ∈ U, Eop aE8 γ₃ u ∈ U)
    (N : Fn L →ₗ[L] Fn L) (z : L) (hN : ∀ u ∈ U, N (actOp aE8 γ₃ z u) ∈ U) :
    ∀ u ∈ U, N u ∈ U := by
  intro u hu
  have hE' : Eop aE8 γ₃ u ∈ U := hE u hu
  have hsq : Eop aE8 γ₃ (Eop aE8 γ₃ u) = 0 := Eop_sq_zero hγ₃ (hsupp u hu)
  have hu' : u - z • Eop aE8 γ₃ u ∈ U := U.sub_mem hu (U.smul_mem _ hE')
  have hh := hN _ hu'
  have e : actOp aE8 γ₃ z (u - z • Eop aE8 γ₃ u) = u := by
    simp only [actOp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
      map_smul, hsq, smul_zero, sub_zero]
    module
  rwa [e] at hh

end Extract

section Rational

variable [Finite K]

theorem ratop_of_sfixed (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hbij : Function.Bijective Fr) {h n : ModGL Tag.E8 L} (hh : h ∈ adjointGroup Tag.E8 L)
    (hlang : Frob Fr h = h * n) {H : Subgroup (ModGL Tag.E8 K)} {Xbar : Subgroup (ModGL Tag.E8 L)}
    (hX : ∀ l₀ ∈ adjointGroup Tag.E8 K,
      h⁻¹ * baseChangeGL (algebraMap K L) l₀ * h ∈ Xbar → l₀ ∈ H)
    {x : ModGL Tag.E8 L} (hxA : x ∈ adjointGroup Tag.E8 L) (hxX : x ∈ Xbar)
    (hxσ : n * Frob Fr x * n⁻¹ = x) :
    ∃ l₀ ∈ H, baseChangeGL (algebraMap K L) l₀ = h * x * h⁻¹ := by
  have hy : h * x * h⁻¹ ∈ adjointGroup Tag.E8 L := mul_mem (mul_mem hh hxA) (inv_mem hh)
  have hF : Frob Fr (h * x * h⁻¹) = h * x * h⁻¹ := by
    rw [map_mul, map_mul, map_inv, hlang]
    calc h * n * Frob Fr x * (h * n)⁻¹ = h * (n * Frob Fr x * n⁻¹) * h⁻¹ := by group
      _ = h * x * h⁻¹ := by rw [hxσ]
  obtain ⟨l₀, hl₀A, hl₀⟩ := descent_E8 Fr hFr hbij hy hF
  refine ⟨l₀, hX l₀ hl₀A ?_, hl₀⟩
  rw [hl₀]
  have : h⁻¹ * (h * x * h⁻¹) * h = x := by group
  rw [this]
  exact hxX

theorem natCast_card_eq_zero : ((Nat.card K : ℕ) : L) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  have h0 : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
  calc ((Fintype.card K : ℕ) : L) = algebraMap K L (Fintype.card K : ℕ) := (map_natCast _ _).symm
    _ = 0 := by rw [h0, map_zero]

theorem exists_finset_pow [IsAlgClosed L] (r : ℕ) (hr : 2 ≤ r) (hr0 : (r : L) = 0) {κ : L}
    (hκ : κ ≠ 0) : ∃ C : Finset L, C.card = r ∧ ∀ c ∈ C, c ^ r = κ * c := by
  classical
  set P : Polynomial L := Polynomial.X ^ r - Polynomial.C κ * Polynomial.X with hP
  have hdeg : P.natDegree = r := by
    rw [hP, Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · rw [Polynomial.natDegree_X_pow]
      refine lt_of_le_of_lt ((Polynomial.natDegree_C_mul_le κ Polynomial.X).trans
        Polynomial.natDegree_X.le) ?_
      omega
  have hP0 : P ≠ 0 := by
    intro h0
    rw [h0] at hdeg
    simp at hdeg
    omega
  have hsep : P.Separable := by
    rw [Polynomial.separable_def]
    have hder : Polynomial.derivative P = Polynomial.C (-κ) := by
      rw [hP, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C_mul_X]
      have : ((r : L)) = 0 := hr0
      simp [this]
    rw [hder]
    refine ⟨0, Polynomial.C (-κ)⁻¹, ?_⟩
    rw [zero_mul, zero_add, ← Polynomial.C_mul, inv_mul_cancel₀ (neg_ne_zero.2 hκ), Polynomial.C_1]
  refine ⟨P.roots.toFinset, ?_, ?_⟩
  · rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep), ← hdeg]
    exact Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits P)
  · intro c hc
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def] at hc
    simp only [hP, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_C] at hc
    exact sub_eq_zero.1 hc

end Rational

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
