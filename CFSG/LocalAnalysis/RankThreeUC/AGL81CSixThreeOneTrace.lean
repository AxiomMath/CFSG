module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open Matrix

variable {F : Type*} [Field F] {σ : Type*} [Fintype σ] [DecidableEq σ]

private theorem neg_one_ne_one_GL (hF : (2 : F) ≠ 0) (hσF : (Fintype.card σ : F) ≠ 0) :
    (-1 : GL σ F) ≠ 1 := by
  intro h
  have hmat : (-1 : Matrix σ σ F) = 1 := by
    have := congrArg (fun u : GL σ F => (u : Matrix σ σ F)) h
    simpa only [Units.val_neg, GeneralLinearGroup.coe_one] using this
  have htrace : -((Fintype.card σ : F)) = (Fintype.card σ : F) := by
    have := congrArg Matrix.trace hmat
    simpa only [trace_neg, trace_one] using this
  have h2 : (2 : F) * (Fintype.card σ : F) = 0 := by
    rw [two_mul]
    nth_rewrite 1 [← htrace]
    exact neg_add_cancel _
  exact hσF ((mul_eq_zero.mp h2).resolve_left hF)

private theorem zpowers_neg_one_le_center {Q : Subgroup (GL σ F)} (hneg : -1 ∈ Q) :
    Subgroup.zpowers (⟨-1, hneg⟩ : ↥Q) ≤ Subgroup.center ↥Q := by
  rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
  intro x
  exact Subtype.ext (by
    show (x : GL σ F) * (-1) = (-1) * (x : GL σ F)
    rw [mul_neg_one, neg_one_mul])

private theorem card_zpowers_neg_one (hF : (2 : F) ≠ 0) (hσF : (Fintype.card σ : F) ≠ 0)
    {Q : Subgroup (GL σ F)} (hneg : -1 ∈ Q) :
    Nat.card (Subgroup.zpowers (⟨-1, hneg⟩ : ↥Q)) = 2 := by
  have hz2 : (⟨-1, hneg⟩ : ↥Q) ^ 2 = 1 := by
    apply Subtype.ext
    show ((-1 : GL σ F)) ^ 2 = 1
    rw [sq, neg_one_mul, neg_neg]
  have hz1 : (⟨-1, hneg⟩ : ↥Q) ≠ 1 := by
    intro h
    apply neg_one_ne_one_GL hF hσF
    have := congrArg (fun u : ↥Q => (u : GL σ F)) h
    simpa using this
  have hzord : orderOf (⟨-1, hneg⟩ : ↥Q) = 2 := orderOf_eq_prime hz2 hz1
  rw [Nat.card_zpowers, hzord]

private theorem conj_eq_neg_of_commutator_eq_neg_one {g h : GL σ F}
    (hc : g * h * g⁻¹ * h⁻¹ = -1) : h * g * h⁻¹ = -g := by
  have hc1 : g * h = (-1 : GL σ F) * (h * g) := by
    calc g * h = (g * h * g⁻¹ * h⁻¹) * (h * g) := by group
      _ = (-1 : GL σ F) * (h * g) := by rw [hc]
  have hneg_sq : (-1 : GL σ F) * (-1 : GL σ F) = 1 := by rw [neg_one_mul, neg_neg]
  have hswap : h * g = (-1 : GL σ F) * (g * h) := by
    have h2 : ((-1 : GL σ F) * ((-1 : GL σ F) * (h * g))) = h * g := by
      rw [← mul_assoc, hneg_sq, one_mul]
    rw [← h2, ← hc1]
  calc h * g * h⁻¹ = ((-1 : GL σ F) * (g * h)) * h⁻¹ := by rw [hswap]
    _ = (-1 : GL σ F) * g := by group
    _ = -g := neg_one_mul g

theorem trace_eq_zero_of_conj_eq_neg (hF : (2 : F) ≠ 0) {g h : GL σ F}
    (hconj : h * g * h⁻¹ = -g) :
    Matrix.trace ((g : GL σ F) : Matrix σ σ F) = 0 := by
  have htr_conj : Matrix.trace (((h * g * h⁻¹ : GL σ F) : Matrix σ σ F)) =
      Matrix.trace ((g : GL σ F) : Matrix σ σ F) := by
    simpa only [Units.val_mul] using Matrix.trace_units_conj h ((g : GL σ F) : Matrix σ σ F)
  have htr_neg : Matrix.trace (((-g : GL σ F) : Matrix σ σ F)) =
      -Matrix.trace ((g : GL σ F) : Matrix σ σ F) := by
    rw [show (-g : GL σ F) = (-1 : GL σ F) * g from (neg_one_mul g).symm]
    rw [Units.val_mul, Units.val_neg, Units.val_one, neg_mul, one_mul, trace_neg]
  have ht : Matrix.trace ((g : GL σ F) : Matrix σ σ F) =
      -Matrix.trace ((g : GL σ F) : Matrix σ σ F) := by
    calc Matrix.trace ((g : GL σ F) : Matrix σ σ F)
        = Matrix.trace (((h * g * h⁻¹ : GL σ F) : Matrix σ σ F)) := htr_conj.symm
      _ = Matrix.trace (((-g : GL σ F) : Matrix σ σ F)) := by rw [hconj]
      _ = -Matrix.trace ((g : GL σ F) : Matrix σ σ F) := htr_neg
  have h2 : (2 : F) * Matrix.trace ((g : GL σ F) : Matrix σ σ F) = 0 := by
    rw [two_mul]
    nth_rewrite 1 [ht]
    exact neg_add_cancel _
  exact (mul_eq_zero.mp h2).resolve_left hF

private theorem trace_eq_zero_of_ne_one_ne_neg_one (hF : (2 : F) ≠ 0) {Q : Subgroup (GL σ F)}
    (hneg : -1 ∈ Q)
    (hZ : ∀ g ∈ Q, (∀ h ∈ Q, g * h = h * g) → g = 1 ∨ g = -1)
    (hcomm : ∀ g ∈ Q, ∀ h ∈ Q, g * h * g⁻¹ * h⁻¹ = 1 ∨ g * h * g⁻¹ * h⁻¹ = -1)
    {g : ↥Q} (hg1 : g ≠ 1) (hgm : g ≠ ⟨-1, hneg⟩) :
    Matrix.trace ((g : GL σ F) : Matrix σ σ F) = 0 := by
  have hg1' : (g : GL σ F) ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hgm' : (g : GL σ F) ≠ -1 := fun h => hgm (Subtype.ext h)
  have hnc : ∃ h : ↥Q, (g : GL σ F) * (h : GL σ F) ≠ (h : GL σ F) * (g : GL σ F) := by
    by_contra hcon
    push Not at hcon
    rcases hZ (g : GL σ F) g.2 (fun h hh => hcon ⟨h, hh⟩) with h | h
    · exact hg1' h
    · exact hgm' h
  obtain ⟨h, hgh⟩ := hnc
  have hc' : (g : GL σ F) * (h : GL σ F) * (g : GL σ F)⁻¹ * (h : GL σ F)⁻¹ = -1 := by
    rcases hcomm (g : GL σ F) g.2 (h : GL σ F) h.2 with hc | hc
    · exact absurd (by
        calc (g : GL σ F) * (h : GL σ F)
            = ((g : GL σ F) * (h : GL σ F) * (g : GL σ F)⁻¹ * (h : GL σ F)⁻¹) *
                ((h : GL σ F) * (g : GL σ F)) := by group
          _ = (h : GL σ F) * (g : GL σ F) := by rw [hc, one_mul]) hgh
    · exact hc
  exact trace_eq_zero_of_conj_eq_neg hF (conj_eq_neg_of_commutator_eq_neg_one hc')

private theorem trace_cosetRep_mul_inv_eq_zero (hF : (2 : F) ≠ 0) {Q : Subgroup (GL σ F)}
    (hneg : -1 ∈ Q)
    (hZ : ∀ g ∈ Q, (∀ h ∈ Q, g * h = h * g) → g = 1 ∨ g = -1)
    (hcomm : ∀ g ∈ Q, ∀ h ∈ Q, g * h * g⁻¹ * h⁻¹ = 1 ∨ g * h * g⁻¹ * h⁻¹ = -1)
    {a b : ↥Q ⧸ Subgroup.zpowers (⟨-1, hneg⟩ : ↥Q)} (hab : a ≠ b) :
    Matrix.trace ((((Quotient.out a : ↥Q) : GL σ F) : Matrix σ σ F) *
      ((((Quotient.out b : ↥Q)⁻¹ : ↥Q) : GL σ F) : Matrix σ σ F)) = 0 := by
  classical
  let z : ↥Q := ⟨-1, hneg⟩
  let Z : Subgroup ↥Q := Subgroup.zpowers z
  haveI : Z.Normal := Subgroup.normal_of_le_center (zpowers_neg_one_le_center hneg)
  have hs : ∀ a : ↥Q ⧸ Z, ((Quotient.out a : ↥Q) : ↥Q ⧸ Z) = a := fun a => Quotient.out_eq' a
  have hxZ : (Quotient.out a : ↥Q) * (Quotient.out b : ↥Q)⁻¹ ∉ Z := by
    intro hmem
    have h1 : (((Quotient.out a : ↥Q) * (Quotient.out b : ↥Q)⁻¹ : ↥Q) : ↥Q ⧸ Z) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hs, hs] at h1
    exact hab (mul_inv_eq_one.mp h1)
  have hx1 : (Quotient.out a : ↥Q) * (Quotient.out b : ↥Q)⁻¹ ≠ 1 :=
    fun h => hxZ (by rw [h]; exact one_mem Z)
  have hxz : (Quotient.out a : ↥Q) * (Quotient.out b : ↥Q)⁻¹ ≠ z :=
    fun h => hxZ (by rw [h]; exact Subgroup.mem_zpowers z)
  have htrx := trace_eq_zero_of_ne_one_ne_neg_one hF hneg hZ hcomm hx1 (by simpa [z] using hxz)
  have hfw : ((((Quotient.out a : ↥Q) : GL σ F) : Matrix σ σ F) *
      ((((Quotient.out b : ↥Q)⁻¹ : ↥Q) : GL σ F) : Matrix σ σ F)) =
      ((((Quotient.out a : ↥Q) * (Quotient.out b : ↥Q)⁻¹ : ↥Q) : GL σ F) : Matrix σ σ F) := by
    simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hfw, htrx]

theorem linearIndependent_cosetReps (hF : (2 : F) ≠ 0)
    (hσF : (Fintype.card σ : F) ≠ 0) {Q : Subgroup (GL σ F)} [Finite ↥Q]
    (hneg : -1 ∈ Q)
    (hZ : ∀ g ∈ Q, (∀ h ∈ Q, g * h = h * g) → g = 1 ∨ g = -1)
    (hcomm : ∀ g ∈ Q, ∀ h ∈ Q, g * h * g⁻¹ * h⁻¹ = 1 ∨ g * h * g⁻¹ * h⁻¹ = -1) :
    LinearIndependent F (fun a : ↥Q ⧸ Subgroup.zpowers (⟨-1, hneg⟩ : ↥Q) =>
      (((Quotient.out a : ↥Q) : GL σ F) : Matrix σ σ F)) := by
  classical
  let z : ↥Q := ⟨-1, hneg⟩
  let Z : Subgroup ↥Q := Subgroup.zpowers z
  haveI : Z.Normal := Subgroup.normal_of_le_center (zpowers_neg_one_le_center hneg)
  haveI : Fintype ↥Q := Fintype.ofFinite _
  haveI : Fintype (↥Q ⧸ Z) := Fintype.ofFinite _
  let f : (↥Q ⧸ Z) → Matrix σ σ F := fun a =>
    (((Quotient.out a : ↥Q) : GL σ F) : Matrix σ σ F)
  let w : (↥Q ⧸ Z) → Matrix σ σ F := fun b =>
    ((((Quotient.out b : ↥Q)⁻¹ : ↥Q) : GL σ F) : Matrix σ σ F)
  have htr : ∀ a b : ↥Q ⧸ Z, a ≠ b → Matrix.trace (f a * w b) = 0 := by
    intro a b hab
    exact trace_cosetRep_mul_inv_eq_zero hF hneg hZ hcomm hab
  change LinearIndependent F f
  rw [linearIndependent_iff']
  intro s c hsum j hj
  have h1 := congrArg (fun M : Matrix σ σ F => Matrix.trace (M * w j)) hsum
  simp only [Finset.sum_mul, Matrix.zero_mul, trace_zero, Matrix.smul_mul] at h1
  rw [Matrix.trace_sum] at h1
  simp only [Matrix.trace_smul, smul_eq_mul] at h1
  have hjj : Matrix.trace (f j * w j) = (Fintype.card σ : F) := by
    have h1j : f j * w j = (1 : Matrix σ σ F) := by
      have h2 : f j * w j =
          ((((Quotient.out j : ↥Q) * (Quotient.out j : ↥Q)⁻¹ : ↥Q) : GL σ F) :
            Matrix σ σ F) := by
        simp only [f, w, Subgroup.coe_mul, Units.val_mul]
      rw [h2, mul_inv_cancel, Subgroup.coe_one, GeneralLinearGroup.coe_one]
    rw [h1j, Matrix.trace_one]
  rw [Finset.sum_eq_single_of_mem j hj] at h1
  · rw [hjj, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact h1
    · exact absurd h1 hσF
  · intro i _ hij
    rw [htr i j hij, mul_zero]

theorem card_le_of_symplecticType (hF : (2 : F) ≠ 0)
    (hσF : (Fintype.card σ : F) ≠ 0) {Q : Subgroup (GL σ F)} [Finite ↥Q]
    (hneg : -1 ∈ Q)
    (hZ : ∀ g ∈ Q, (∀ h ∈ Q, g * h = h * g) → g = 1 ∨ g = -1)
    (hcomm : ∀ g ∈ Q, ∀ h ∈ Q, g * h * g⁻¹ * h⁻¹ = 1 ∨ g * h * g⁻¹ * h⁻¹ = -1) :
    Nat.card ↥Q ≤ 2 * Fintype.card σ ^ 2 := by
  classical
  let Z : Subgroup ↥Q := Subgroup.zpowers (⟨-1, hneg⟩ : ↥Q)
  have hli := linearIndependent_cosetReps hF hσF hneg hZ hcomm
  haveI : Fintype ↥Q := Fintype.ofFinite _
  haveI : Fintype (↥Q ⧸ Z) := Fintype.ofFinite _
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_matrix, Module.finrank_self, mul_one] at hcard
  have hZcard : Nat.card Z = 2 := card_zpowers_neg_one hF hσF hneg
  have hQcard : Nat.card ↥Q = Nat.card (↥Q ⧸ Z) * Nat.card Z :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  rw [hZcard] at hQcard
  have hfin : Nat.card (↥Q ⧸ Z) = Fintype.card (↥Q ⧸ Z) := Nat.card_eq_fintype_card
  rw [hQcard, hfin]
  calc Fintype.card (↥Q ⧸ Z) * 2 = 2 * Fintype.card (↥Q ⧸ Z) := by ring
    _ ≤ 2 * (Fintype.card σ * Fintype.card σ) := Nat.mul_le_mul_left 2 hcard
    _ = 2 * Fintype.card σ ^ 2 := by ring

theorem eq_card_imp_scalar_of_symplecticType (hF : (2 : F) ≠ 0)
    (hσF : (Fintype.card σ : F) ≠ 0) {Q : Subgroup (GL σ F)} [Finite ↥Q]
    (hneg : -1 ∈ Q)
    (hZ : ∀ g ∈ Q, (∀ h ∈ Q, g * h = h * g) → g = 1 ∨ g = -1)
    (hcomm : ∀ g ∈ Q, ∀ h ∈ Q, g * h * g⁻¹ * h⁻¹ = 1 ∨ g * h * g⁻¹ * h⁻¹ = -1)
    (hQcard : Nat.card ↥Q = 2 * Fintype.card σ ^ 2) :
    ∀ M : Matrix σ σ F, (∀ g ∈ Q, (g : Matrix σ σ F) * M = M * g) →
      ∃ c : F, M = Matrix.scalar σ c := by
  classical
  let z : ↥Q := ⟨-1, hneg⟩
  let Z : Subgroup ↥Q := Subgroup.zpowers z
  have hZcard : Nat.card Z = 2 := card_zpowers_neg_one hF hσF hneg
  haveI : Z.Normal := Subgroup.normal_of_le_center (zpowers_neg_one_le_center hneg)
  have hli := linearIndependent_cosetReps hF hσF hneg hZ hcomm
  haveI : Fintype ↥Q := Fintype.ofFinite _
  haveI : Fintype (↥Q ⧸ Z) := Fintype.ofFinite _
  let f : (↥Q ⧸ Z) → Matrix σ σ F := fun a =>
    (((Quotient.out a : ↥Q) : GL σ F) : Matrix σ σ F)
  change LinearIndependent F f at hli
  have hquotcard : Nat.card (↥Q ⧸ Z) = Fintype.card σ ^ 2 := by
    have h1 : Nat.card (↥Q ⧸ Z) * 2 = 2 * Fintype.card σ ^ 2 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
      rw [hZcard] at h
      rw [← h, hQcard]
    rw [mul_comm 2 (Fintype.card σ ^ 2)] at h1
    exact Nat.mul_right_cancel (by norm_num) h1
  have h4 : Fintype.card (↥Q ⧸ Z) = Module.finrank F (Matrix σ σ F) := by
    have h3 : Fintype.card (↥Q ⧸ Z) = Fintype.card σ ^ 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact hquotcard
    rw [h3, Module.finrank_matrix, Module.finrank_self, mul_one, pow_two]
  have hspan : Submodule.span F (Set.range f) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' h4
  intro M hM
  have hcomm_span : ∀ N ∈ Submodule.span F (Set.range f), N * M = M * N := by
    intro N hN
    refine Submodule.span_induction (p := fun N _ => N * M = M * N) ?_ ?_ ?_ ?_ hN
    · rintro _ ⟨i, rfl⟩
      exact hM (Quotient.out i : ↥Q) (Quotient.out i).2
    · simp
    · intro x y hx hy hxM hyM
      rw [add_mul, mul_add, hxM, hyM]
    · intro a x hx hxM
      rw [smul_mul, Matrix.mul_smul, hxM]
  have hsingle : ∀ i j : σ, i ≠ j → Commute (Matrix.single i j (1 : F)) M := by
    intro i j hij
    have hmem : Matrix.single i j (1 : F) ∈ Submodule.span F (Set.range f) := by
      rw [hspan]
      exact Submodule.mem_top
    exact hcomm_span _ hmem
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single
    (fun i j hij => hsingle i j hij)
  exact ⟨c, hc.symm⟩

theorem card_le_and_scalar_of_symplecticType (hF : (2 : F) ≠ 0)
    (hσF : (Fintype.card σ : F) ≠ 0)
    {Q : Subgroup (GL σ F)} [Finite ↥Q] (hneg : -1 ∈ Q)
    (hZ : ∀ g ∈ Q, (∀ h ∈ Q, g * h = h * g) → g = 1 ∨ g = -1)
    (hcomm : ∀ g ∈ Q, ∀ h ∈ Q, g * h * g⁻¹ * h⁻¹ = 1 ∨ g * h * g⁻¹ * h⁻¹ = -1) :
    Nat.card ↥Q ≤ 2 * Fintype.card σ ^ 2 ∧
      (Nat.card ↥Q = 2 * Fintype.card σ ^ 2 → ∀ M : Matrix σ σ F,
        (∀ g ∈ Q, (g : Matrix σ σ F) * M = M * g) → ∃ c : F, M = Matrix.scalar σ c) :=
  ⟨card_le_of_symplecticType hF hσF hneg hZ hcomm,
    eq_card_imp_scalar_of_symplecticType hF hσF hneg hZ hcomm⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
