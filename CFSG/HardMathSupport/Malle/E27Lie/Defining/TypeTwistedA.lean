module

public import CFSG.HardMathSupport.Malle.E27Lie.Defining.AbelianKill
public import CFSG.HardMathSupport.Malle.E27Lie.Defining.Unitriangular
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Foote.E27 CFSG.Assembly.LowTwoRank TauCeti

theorem mul_apply_of_adjacent {ι F : Type*} [Fintype ι] [DecidableEq ι] [CommRing F]
    {pos : ι → ℕ} (hpos : Function.Injective pos) {M N : Matrix ι ι F}
    (hM : M.BlockTriangular pos) (hN : N.BlockTriangular pos) (hM1 : ∀ a, M a a = 1)
    (hN1 : ∀ a, N a a = 1) {a b : ι} (hab : pos b = pos a + 1) :
    (M * N) a b = M a b + N a b := by
  have hne : a ≠ b := fun h => by rw [h] at hab; omega
  rw [Matrix.mul_apply, Fintype.sum_eq_add a b hne]
  · rw [hM1, hN1, one_mul, mul_one, add_comm]
  · rintro c ⟨hca, hcb⟩
    by_cases h1 : pos c < pos a
    · rw [hM h1, zero_mul]
    · by_cases h2 : pos b < pos c
      · rw [hN h2, mul_zero]
      · exfalso
        rcases (by omega : pos c = pos a ∨ pos c = pos b) with h | h
        · exact hca (hpos h)
        · exact hcb (hpos h)

variable {p f : ℕ} {E : Type} [Field E] {r ε : ℕ}

@[expose] def psuCoord (hr : 1 ≤ r) (g : GL (HypIndex r ε) E) :
    (Fin (r - 1) → E) × (Fin ε → E) :=
  (fun i => (g : Matrix (HypIndex r ε) (HypIndex r ε) E) (.inl ⟨i, by omega⟩)
      (.inl ⟨i + 1, by omega⟩),
    fun k => (g : Matrix (HypIndex r ε) (HypIndex r ε) E) (.inl ⟨r - 1, by omega⟩) (.inr (.inl k)))

@[expose] noncomputable def unitriCoord (h : UnitaryFieldData p f E) (hr : 1 ≤ r) (hε : ε ≤ 1) :
    hypUnitriangular h r ε →* Multiplicative ((Fin (r - 1) → E) × (Fin ε → E)) where
  toFun g := Multiplicative.ofAdd (psuCoord hr ((g : hypSU h r ε) : GL (HypIndex r ε) E))
  map_one' := by
    show Multiplicative.ofAdd (psuCoord hr (1 : GL (HypIndex r ε) E)) = 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, toAdd_one]
    refine Prod.ext (funext fun i => ?_) (funext fun k => ?_)
    · simp only [psuCoord, Units.val_one, Prod.fst_zero, Pi.zero_apply]
      exact Matrix.one_apply_ne (by simp [Fin.ext_iff])
    · simp only [psuCoord, Units.val_one, Prod.snd_zero, Pi.zero_apply]
      exact Matrix.one_apply_ne (by simp)
  map_mul' g g' := by
    have hg := mem_hypUnitriangular.mp g.2
    have hg' := mem_hypUnitriangular.mp g'.2
    rw [← ofAdd_add]
    congr 1
    refine Prod.ext (funext fun i => ?_) (funext fun k => ?_)
    · simp only [psuCoord, Subgroup.coe_mul, Units.val_mul, Prod.fst_add, Pi.add_apply]
      exact mul_apply_of_adjacent fullPos_injective hg.1 hg'.1 hg.2 hg'.2 (by simp)
    · simp only [psuCoord, Subgroup.coe_mul, Units.val_mul, Prod.snd_add, Pi.add_apply]
      refine mul_apply_of_adjacent fullPos_injective hg.1 hg'.1 hg.2 hg'.2 ?_
      have hk : k.val = 0 := by have := k.2; omega
      simp only [fullPos_inr_inl, fullPos_inl, hk]
      omega

theorem unitri_of_superdiag (M₀ : strictUpper r E) :
    IsUnitriangular (1 + (M₀ : Matrix (Fin r) (Fin r) E)) := by
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · have hba' : b < a := hba
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hba'), M₀.2 a b hba'.le, add_zero]
  · rw [Matrix.add_apply, Matrix.one_apply_eq, M₀.2 a a le_rfl, add_zero]

theorem unitri_mul_apply_last' {m : Type*} {A : Matrix (Fin r) (Fin r) E}
    (hA : IsUnitriangular A) (hr : 1 ≤ r) (M : Matrix (Fin r) m E) (b : m) :
    (A * M) ⟨r - 1, by omega⟩ b = M ⟨r - 1, by omega⟩ b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨r - 1, by omega⟩]
  · rw [hA.2, one_mul]
  · intro a _ ha
    have hlt : a < ⟨r - 1, by omega⟩ := by
      rw [Fin.lt_def]
      have h1 := a.2
      have h2 : a.val ≠ r - 1 := fun h => ha (Fin.ext h)
      show a.val < r - 1
      omega
    rw [hA.1 hlt, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem unitriCoord_surjective_zero (h : UnitaryFieldData p f E) (hr : 1 ≤ r) :
    Function.Surjective (unitriCoord h hr (ε := 0) (Nat.zero_le 1)) := by
  intro x
  obtain ⟨M₀, hM₀⟩ := superdiag_surjective (n := r) (K := E) (Multiplicative.toAdd x).1
  have hC : (0 : Matrix (Fin r) (Fin r) E) + ((0 : Matrix (Fin r) (Fin r) E).map h.bar)ᵀ = 0 := by
    simp
  refine ⟨evenUnitriangularElt (h := h) (unitri_of_superdiag M₀) hC, ?_⟩
  apply Multiplicative.toAdd.injective
  show psuCoord hr _ = Multiplicative.toAdd x
  refine Prod.ext (funext fun i => ?_) (funext fun k => k.elim0)
  have hne : (⟨i, by omega⟩ : Fin r) ≠ ⟨i + 1, by omega⟩ := by simp [Fin.ext_iff]
  simp only [psuCoord]
  rw [coe_evenUnitriangularElt, evenMat, blk3_inl_inl, Matrix.add_apply, Matrix.one_apply_ne hne,
    zero_add, ← hM₀, superdiag_apply]

theorem unitriCoord_surjective_one (h : UnitaryFieldData p f E) (hp : p = 3) (hr : 1 ≤ r) :
    Function.Surjective (unitriCoord h hr (ε := 1) le_rfl) := by
  intro x
  have : CharP E p := h.charP
  have h2 : (2 : E) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff E p 2).mp (by exact_mod_cast h0)
    rw [hp] at this
    omega
  obtain ⟨M₀, hM₀⟩ := superdiag_surjective (n := r) (K := E) (Multiplicative.toAdd x).1
  set w := (Multiplicative.toAdd x).2 0
  set l : Fin r := ⟨r - 1, by omega⟩
  set c : E := -(w * h.bar w) / 2
  have hbc : h.bar c = c := by
    simp only [c, map_div₀, map_neg, map_mul, h.bar_bar, map_ofNat]
    ring
  set xv : Fin r → E := Pi.single l w
  have hC : Matrix.single l l c + ((Matrix.single l l c).map h.bar)ᵀ =
      -vecMulVec xv (fun j => h.bar (xv j)) := by
    ext i j
    by_cases hi : i = l <;> by_cases hj : j = l
    · subst hi; subst hj
      simp [xv, vecMulVec_apply, hbc, c]
      field_simp
      ring
    · subst hi
      simp [xv, vecMulVec_apply, Ne.symm hj, hj, Pi.single_apply]
    · subst hj
      simp [xv, vecMulVec_apply, Ne.symm hi, hi, Pi.single_apply]
    · simp [xv, vecMulVec_apply, Ne.symm hi, Ne.symm hj, hi, hj, Pi.single_apply]
  obtain ⟨g, hgU, hg⟩ := (exists_mem_hypUnitriangular_odd_iff (h := h)
    (oddDiag h (1 + (M₀ : Matrix (Fin r) (Fin r) E)) 1 * oddUni h xv (Matrix.single l l c))).mpr
    ⟨_, _, xv, unitri_of_superdiag M₀, hC, rfl⟩
  refine ⟨⟨g, hgU⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  show psuCoord hr _ = Multiplicative.toAdd x
  refine Prod.ext (funext fun i => ?_) (funext fun k => ?_)
  · have hne : (⟨i, by omega⟩ : Fin r) ≠ ⟨i + 1, by omega⟩ := by simp [Fin.ext_iff]
    simp only [psuCoord]
    rw [hg, oddDiag_mul_oddUni, blk3_inl_inl, Matrix.add_apply, Matrix.one_apply_ne hne,
      zero_add, ← hM₀, superdiag_apply]
  · have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    simp only [psuCoord]
    rw [hg, oddDiag_mul_oddUni, blk3_inl_inr_inl,
      unitri_mul_apply_last' (unitri_of_superdiag M₀) hr (replicateCol (Fin 1) xv) 0]
    simp [xv, l, w]

theorem false_of_psu_model_char_three {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K) {n f : ℕ}
    (hcl : StatedClassicalModel K .PSU n 3 f) (h3 : ¬ (n = 3 ∧ f = 1)) (h4 : ¬ (n = 4 ∧ f = 1)) :
    False := by
  obtain ⟨⟨hℓ, hm, hn3, -⟩, E, _, _, hE, ⟨e'⟩⟩ := hcl
  have hU : UnitaryFieldData 3 f E := ⟨hℓ, hm, by rw [hE, ← pow_mul, mul_comm]⟩
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ n = 2 * r + ε :=
    ⟨n / 2, n % 2, by omega, (Nat.div_add_mod n 2).symm⟩
  have hr : 1 ≤ r := by omega
  obtain ⟨R', hR'⟩ := exists_isHypTransport (r := r) (ε := ε) hU
  let ψ : ↥K ≃* hypPSU hU r ε := e'.trans (hypPSUEquivStatedProj hU hR' (by omega)).symm
  obtain ⟨-, -, -, ⟨eU, -⟩, ⟨P, hP⟩, -, -⟩ := unitary_order_and_Sylow hU hr hε
  have hPcard : Nat.card (hypProjUnitriangular hU r ε) =
      3 ^ (Nat.card (hypPSU hU r ε)).factorization 3 := by
    rw [← hP]
    exact P.card_eq_multiplicity
  have hsurj : Function.Surjective (unitriCoord hU hr hε) := by
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · exact unitriCoord_surjective_zero hU hr
    · exact unitriCoord_surjective_one hU rfl hr
  refine E27Config.false_of_sylow_hom_comm h hz ψ (hypProjUnitriangular hU r ε) hPcard
    ((unitriCoord hU hr hε).comp eU.symm.toMonoidHom) (hsurj.comp eU.symm.surjective) ?_
  have hcard : Nat.card (Multiplicative ((Fin (r - 1) → E) × (Fin ε → E))) =
      3 ^ (2 * f * (r - 1 + ε)) := by
    rw [show Nat.card (Multiplicative ((Fin (r - 1) → E) × (Fin ε → E))) =
        Nat.card ((Fin (r - 1) → E) × (Fin ε → E)) from rfl,
      Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin (r - 1)),
      Nat.card_eq_fintype_card (α := Fin ε), Fintype.card_fin, Fintype.card_fin, hU.card,
      ← pow_mul, ← pow_mul, ← pow_add, ← Nat.mul_add]
  rw [hcard]
  have hm2 : 2 ≤ f * (r - 1 + ε) := by
    rcases (by omega : 2 ≤ f ∨ f = 1) with hf | hf
    · calc 2 = 2 * 1 := by norm_num
        _ ≤ f * (r - 1 + ε) := Nat.mul_le_mul hf (by omega)
    · subst hf
      omega
  calc 81 = 3 ^ 4 := by norm_num
    _ ≤ 3 ^ (2 * f * (r - 1 + ε)) := Nat.pow_le_pow_right (by norm_num) (by
      rw [Nat.mul_assoc]
      omega)

theorem false_of_typeTwistedA_char_three {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K) (n : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA n q).Valid) (hp : q.p = 3) (h3 : ¬ (n = 2 ∧ q.exponent = 1))
    (h4 : ¬ (n = 3 ∧ q.exponent = 1)) (e : ↥K ≃* (CFSGIndex.lie ⟨.twistedA n q, hv⟩).Group) :
    False := by
  have hcl := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n q hv e
  rw [hp] at hcl
  exact false_of_psu_model_char_three h hz hcl (by omega) (by omega)

end CFSG.HardMathSupport.Malle.E27Lie
