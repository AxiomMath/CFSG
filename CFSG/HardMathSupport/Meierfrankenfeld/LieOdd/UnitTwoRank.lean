module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitTwoRankAbs
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] (h : UnitaryFieldData 3 1 K)

noncomputable def lin1 : Subgroup (GL (HypIndex 2 0) K) :=
  (semilinearSimilitudes h 2 0).comap SemidirectProduct.inl

noncomputable def Θ : lin1 h →* MulAut (hypPSU h 2 0) :=
  (semilinearAutHom h (by norm_num : 1 ≤ 2) (Nat.zero_le 1)).comp
    (MonoidHom.codRestrict (SemidirectProduct.inl.comp (lin1 h).subtype)
      (semilinearSimilitudes h 2 0) (fun A => A.2))

theorem Θ_eq_one_iff (a : lin1 h) :
    Θ h a = 1 ↔ ∃ c : Kˣ, (a : GL (HypIndex 2 0) K) = GeneralLinearGroup.scalar _ c := by
  have := semilinearAutHom_eq_one_iff h (by norm_num : 1 ≤ 2) (Nat.zero_le 1) (by norm_num)
    ⟨SemidirectProduct.inl (a : GL (HypIndex 2 0) K), a.2⟩
  exact this.trans ⟨fun ⟨_, c, hc⟩ => ⟨c, hc⟩, fun ⟨c, hc⟩ => ⟨rfl, c, hc⟩⟩

instance finite_hypPSU : Finite (hypPSU h 2 0) := by
  haveI := h.finite
  infer_instance

instance finite_mulAut_hypPSU : Finite (MulAut (hypPSU h 2 0)) :=
  Finite.of_injective (fun f : MulAut (hypPSU h 2 0) => (f : hypPSU h 2 0 → hypPSU h 2 0))
    DFunLike.coe_injective

theorem scalar_mul_eq {ι : Type} [Fintype ι] [DecidableEq ι] (c : K) (M : Matrix ι ι K) :
    Matrix.scalar ι c * M = c • M := by
  rw [scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]

theorem norm_eq_one_of_sq {A : GL (HypIndex 2 0) K} (hA : A ∈ hypUnitary h 2 0) {c : K}
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      = Matrix.scalar (HypIndex 2 0) c) :
    h.norm c = 1 := by
  have hU := mul_mem hA hA
  rw [mem_hypUnitary, Units.val_mul, hAA, scalar_gram] at hU
  have h2 := congrFun (congrFun hU (.inl ⟨0, by norm_num⟩)) (hypPartner (.inl ⟨0, by norm_num⟩))
  simpa [hypGram_apply] using h2

variable (B : Subgroup (MulAut (hypPSU h 2 0)))

noncomputable def Hs : Subgroup (lin1 h) :=
  B.comap (Θ h) ⊓ (hypUnitary h 2 0).comap (lin1 h).subtype

noncomputable def hlin : Subgroup (GL (HypIndex 2 0) K) := (Hs h B).map (lin1 h).subtype

noncomputable def Rr : Subgroup (MulAut (hypPSU h 2 0)) := (Hs h B).map (Θ h)

theorem mem_Hs {a : lin1 h} : a ∈ Hs h B ↔
    Θ h a ∈ B ∧ (a : GL (HypIndex 2 0) K) ∈ hypUnitary h 2 0 := Iff.rfl

theorem hlin_sq (hB : ∀ x ∈ B, x * x = 1) {A : GL (HypIndex 2 0) K} (hA : A ∈ hlin h B) :
    ∃ l : K, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = (l ^ 2) • 1 := by
  obtain ⟨a, ha, rfl⟩ := hA
  obtain ⟨haB, haU⟩ := (mem_Hs h B).1 ha
  have h1 : Θ h (a * a) = 1 := by rw [map_mul]; exact hB _ haB
  obtain ⟨c, hc⟩ := (Θ_eq_one_iff h _).1 h1
  have hAA : ((a : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      ((a : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
        Matrix.scalar (HypIndex 2 0) (c : K) := by
    have := congrArg (fun g : GL (HypIndex 2 0) K => (g : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) hc
    simpa [GeneralLinearGroup.coe_scalar] using this
  have hN := norm_eq_one_of_sq h haU hAA
  obtain ⟨l, hl0, hl2⟩ := exists_sq_eq_of_norm_eq_one h (by norm_num : (3 : ℕ) ≠ 2) hN
  refine ⟨l, ?_⟩
  change ((a : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
    ((a : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = _
  rw [hAA, hl2, scalar_apply, smul_one_eq_diagonal]

theorem hlin_comm (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) {A A' : GL (HypIndex 2 0) K}
    (hA : A ∈ hlin h B) (hA' : A' ∈ hlin h B) :
    ∃ ε : K, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * (A' : Matrix _ _ K) =
      ε • ((A' : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * (A : Matrix _ _ K)) := by
  obtain ⟨a, ha, rfl⟩ := hA
  obtain ⟨a', ha', rfl⟩ := hA'
  obtain ⟨haB, -⟩ := (mem_Hs h B).1 ha
  obtain ⟨haB', -⟩ := (mem_Hs h B).1 ha'
  have h1 : Θ h (a * a' * (a' * a)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, hc _ haB _ haB', mul_inv_cancel]
  obtain ⟨c, hc'⟩ := (Θ_eq_one_iff h _).1 h1
  have hGL : ((a : GL (HypIndex 2 0) K)) * (a' : GL (HypIndex 2 0) K) =
      GeneralLinearGroup.scalar _ c * ((a' : GL (HypIndex 2 0) K) * (a : GL (HypIndex 2 0) K)) := by
    rw [← hc']
    change _ = ((a * a' * (a' * a)⁻¹ : lin1 h) : GL (HypIndex 2 0) K) * _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  refine ⟨(c : K), ?_⟩
  have := congrArg (fun g : GL (HypIndex 2 0) K => (g : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) hGL
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at this
  rw [scalar_mul_eq] at this
  simpa using this

theorem card_Rr_le (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hs : ∀ x ∈ B, x * x = 1) :
    Nat.card (Rr h B) ≤ 16 := by
  classical
  haveI := h.finite
  haveI : Fintype (Rr h B) := Fintype.ofFinite _
  haveI : Nonempty (HypIndex 2 0) := ⟨Sum.inl 0⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h (by norm_num : (3 : ℕ) ≠ 2)
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hcard4 : Fintype.card (HypIndex 2 0) = 4 := by
    simpa using card_hypIndex (r := 2) (ε := 0)
  have hex : ∀ β : Rr h B, ∃ a : lin1 h, a ∈ Hs h B ∧ Θ h a = β := fun β => by
    obtain ⟨a, ha, he⟩ := β.2
    exact ⟨a, ha, he⟩
  choose rep hrepH hrepΘ using hex
  let mat : Rr h B → Matrix (HypIndex 2 0) (HypIndex 2 0) K :=
    fun β => ((rep β : lin1 h) : GL (HypIndex 2 0) K)
  have hmat_inj : Function.Injective mat := by
    intro β β' hββ'
    have e1 : ((rep β : lin1 h) : GL (HypIndex 2 0) K) = (rep β' : lin1 h) := Units.ext hββ'
    have e2 : rep β = rep β' := Subtype.ext e1
    exact Subtype.ext (by rw [← hrepΘ β, ← hrepΘ β', e2])
  have hcard : (Finset.univ.image mat).card = Nat.card (Rr h B) := by
    rw [Finset.card_image_of_injective _ hmat_inj, Finset.card_univ, Nat.card_eq_fintype_card]
  rw [← hcard]
  refine card_le_sixteen (ι := HypIndex 2 0) h2 h4 hcard4 (hlin h B)
    (fun g hg => hlin_sq h B hs hg) (fun g hg g' hg' => hlin_comm h B hc hg hg')
    (Finset.univ.image mat) ?_ ?_
  · intro t ht
    obtain ⟨β, -, rfl⟩ := Finset.mem_image.1 ht
    exact ⟨_, ⟨rep β, hrepH β, rfl⟩, rfl⟩
  · intro t ht t' ht' hne c hct
    obtain ⟨β, -, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨β', -, rfl⟩ := Finset.mem_image.1 ht'
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact Units.ne_zero (rep β : GL (HypIndex 2 0) K) (by simpa [mat] using hct)
    have hy : Θ h (rep β * (rep β')⁻¹) = 1 := by
      refine (Θ_eq_one_iff h _).2 ⟨Units.mk0 c hc0, ?_⟩
      refine Units.ext ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, GeneralLinearGroup.coe_scalar,
        Units.val_mk0]
      have e : (((rep β : lin1 h) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
          (c • (((rep β' : lin1 h) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) : Matrix _ _ K) := hct
      rw [e, Matrix.smul_mul]
      rw [show (((rep β' : lin1 h) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (((rep β' : lin1 h) : GL (HypIndex 2 0) K)⁻¹ : GL (HypIndex 2 0) K) = 1 from by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]]
      rw [scalar_apply, smul_one_eq_diagonal]
    rw [map_mul, map_inv, mul_inv_eq_one, hrepΘ, hrepΘ] at hy
    exact hne (by rw [Subtype.ext hy])

theorem rep_unitary (β : MulAut (hypPSU h 2 0)) :
    ∃ x : semilinearSimilitudes h 2 0,
      semilinearAutHom h (by norm_num : 1 ≤ 2) (Nat.zero_le 1) x = β ∧
      (x : SemiGL (HypIndex 2 0) K).left ∈ hypUnitary h 2 0 := by
  obtain ⟨x₀, hx₀⟩ := semilinearAutHom_surjective h (by norm_num : 1 ≤ 2) (Nat.zero_le 1)
    (by norm_num : (3 : ℕ) ≠ 2) (by norm_num) β
  obtain ⟨x, hΦ, -, hU⟩ := exists_unitary_rep h (by norm_num : 1 ≤ 2) (Nat.zero_le 1)
    (by norm_num) x₀
  exact ⟨x, hΦ.trans hx₀, hU⟩

theorem mem_Rr_of_linear {x : semilinearSimilitudes h 2 0}
    (hr : (x : SemiGL (HypIndex 2 0) K).right = RingEquiv.refl K)
    (hU : (x : SemiGL (HypIndex 2 0) K).left ∈ hypUnitary h 2 0)
    (hB : semilinearAutHom h (by norm_num : 1 ≤ 2) (Nat.zero_le 1) x ∈ B) :
    semilinearAutHom h (by norm_num : 1 ≤ 2) (Nat.zero_le 1) x ∈ Rr h B := by
  obtain ⟨⟨A, σ⟩, hx⟩ := x
  change σ = RingEquiv.refl K at hr
  subst hr
  exact ⟨⟨A, hx⟩, ⟨hB, hU⟩, rfl⟩

theorem right_bar_of_not_Rr (hs : ∀ x ∈ B, x * x = 1) {β : MulAut (hypPSU h 2 0)} (hβ : β ∈ B)
    (hnot : β ∉ Rr h B) {x : semilinearSimilitudes h 2 0}
    (hx : semilinearAutHom h (by norm_num : 1 ≤ 2) (Nat.zero_le 1) x = β)
    (hU : (x : SemiGL (HypIndex 2 0) K).left ∈ hypUnitary h 2 0) :
    ∀ c, (x : SemiGL (HypIndex 2 0) K).right c = h.bar c := by
  have h1 : semilinearAutHom h (by norm_num : 1 ≤ 2) (Nat.zero_le 1) (x * x) = 1 := by
    rw [map_mul, hx]; exact hs _ hβ
  obtain ⟨hσσ, -⟩ := (semilinearAutHom_eq_one_iff h (by norm_num : 1 ≤ 2) (Nat.zero_le 1)
    (by norm_num) _).1 h1
  change (x : SemiGL (HypIndex 2 0) K).right * (x : SemiGL (HypIndex 2 0) K).right =
    RingEquiv.refl K at hσσ
  rcases ringEquiv_eq_refl_or_bar h hσσ with hr | hr
  · exact absurd (hx ▸ mem_Rr_of_linear h B hr hU (hx ▸ hβ)) hnot
  · exact hr

theorem mul_mem_Rr (hs : ∀ x ∈ B, x * x = 1) {β β' : MulAut (hypPSU h 2 0)} (hβ : β ∈ B)
    (hβ' : β' ∈ B) (n1 : β ∉ Rr h B) (n2 : β' ∉ Rr h B) : β * β' ∈ Rr h B := by
  obtain ⟨x, hx, hU⟩ := rep_unitary h β
  obtain ⟨x', hx', hU'⟩ := rep_unitary h β'
  have b1 := right_bar_of_not_Rr h B hs hβ n1 hx hU
  have b2 := right_bar_of_not_Rr h B hs hβ' n2 hx' hU'
  have hz : ((x * x' : semilinearSimilitudes h 2 0) : SemiGL (HypIndex 2 0) K).right =
      RingEquiv.refl K := by
    ext c
    change (x : SemiGL (HypIndex 2 0) K).right ((x' : SemiGL (HypIndex 2 0) K).right c) = c
    rw [b2, b1, h.bar_bar]
  obtain ⟨y, hy, hyr, hyU⟩ := exists_unitary_rep h (by norm_num : 1 ≤ 2) (Nat.zero_le 1)
    (by norm_num) (x * x')
  rw [map_mul, hx, hx'] at hy
  rw [← hy]
  exact mem_Rr_of_linear h B (hyr.trans hz) hyU (hy ▸ B.mul_mem hβ hβ')

theorem Rr_le (B : Subgroup (MulAut (hypPSU h 2 0))) : Rr h B ≤ B := by
  rintro _ ⟨a, ha, rfl⟩
  exact ((mem_Hs h B).1 ha).1

theorem card_le_two_mul_Rr (hs : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 * Nat.card (Rr h B) := by
  classical
  by_cases hall : ∀ β ∈ B, β ∈ Rr h B
  · have : B ≤ Rr h B := hall
    have := Subgroup.card_le_of_le this
    omega
  · push_neg at hall
    obtain ⟨β₀, hβ₀, hβ₀R⟩ := hall
    have key : ∀ β : B, β.1 ∉ Rr h B → β₀ * β.1 ∈ Rr h B := fun β hβ =>
      mul_mem_Rr h B hs hβ₀ β.2 hβ₀R hβ
    let f : B → Rr h B ⊕ Rr h B := fun β =>
      if hβ : β.1 ∈ Rr h B then Sum.inl ⟨β.1, hβ⟩ else Sum.inr ⟨β₀ * β.1, key β hβ⟩
    have hf : Function.Injective f := by
      intro β β' hββ'
      by_cases h1 : β.1 ∈ Rr h B <;> by_cases h2 : β'.1 ∈ Rr h B <;>
        simp only [f, h1, h2, dite_true, dite_false] at hββ'
      · have e := Subtype.mk.inj (Sum.inl.inj hββ')
        exact Subtype.ext e
      · exact absurd hββ' (by simp)
      · exact absurd hββ' (by simp)
      · have e := Subtype.mk.inj (Sum.inr.inj hββ')
        exact Subtype.ext (mul_left_cancel e)
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_sum] at this
    omega

theorem two_rank_hypPSU_le (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hs : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 ^ 5 := by
  have h1 := card_le_two_mul_Rr h B hs
  have h2 := card_Rr_le h B hc hs
  omega

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
