module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharTailAlg
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharPlus
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  QuadraticMap Matrix Subgroup CFSG.Open

section Supp

variable {K : Type*} [Field K] {r : ℕ}

@[expose] def AltSupp {r : ℕ} {K : Type*} [Field K] (t : ℕ) (C : Matrix (Fin r) (Fin r) K) :
    Prop :=
  Cᵀ = -C ∧ (∀ i, C i i = 0) ∧ ∀ i j, C i j ≠ 0 → (i : ℕ) + j + t ≤ r

theorem AltSupp.zero (t : ℕ) : AltSupp t (0 : Matrix (Fin r) (Fin r) K) :=
  ⟨by simp, fun _ => rfl, fun i j h => absurd (Matrix.zero_apply i j) h⟩

theorem AltSupp.add {t : ℕ} {C C' : Matrix (Fin r) (Fin r) K} (h : AltSupp t C)
    (h' : AltSupp t C') : AltSupp t (C + C') := by
  refine ⟨by rw [Matrix.transpose_add, h.1, h'.1, neg_add], fun i => by
    rw [Matrix.add_apply, h.2.1 i, h'.2.1 i, add_zero], fun i j hij => ?_⟩
  by_contra hlt
  apply hij
  have h1 : C i j = 0 := by
    by_contra hne
    exact hlt (h.2.2 i j hne)
  have h2 : C' i j = 0 := by
    by_contra hne
    exact hlt (h'.2.2 i j hne)
  rw [Matrix.add_apply, h1, h2, add_zero]

theorem AltSupp.neg {t : ℕ} {C : Matrix (Fin r) (Fin r) K} (h : AltSupp t C) :
    AltSupp t (-C) := by
  refine ⟨by rw [Matrix.transpose_neg, h.1], fun i => by rw [Matrix.neg_apply, h.2.1 i, neg_zero],
    fun i j hij => h.2.2 i j fun h0 => hij ?_⟩
  rw [Matrix.neg_apply, h0, neg_zero]

theorem AltSupp.mono {t t' : ℕ} {C : Matrix (Fin r) (Fin r) K} (h : AltSupp t' C) (ht : t ≤ t') :
    AltSupp t C :=
  ⟨h.1, h.2.1, fun i j hij => by have := h.2.2 i j hij; omega⟩

theorem supp_mul_left {N C : Matrix (Fin r) (Fin r) K} {t : ℕ}
    (hN : ∀ i k, N i k ≠ 0 → (i : ℕ) < k) (hC : ∀ k j, C k j ≠ 0 → (k : ℕ) + j + t ≤ r) :
    ∀ i j, (N * C) i j ≠ 0 → (i : ℕ) + j + (t + 1) ≤ r := by
  intro i j h
  rw [Matrix.mul_apply] at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := hN i k (left_ne_zero_of_mul hk)
  have h2 := hC k j (right_ne_zero_of_mul hk)
  omega

theorem supp_mul_right {C N : Matrix (Fin r) (Fin r) K} {t : ℕ}
    (hN : ∀ i k, N i k ≠ 0 → (i : ℕ) < k) (hC : ∀ i k, C i k ≠ 0 → (i : ℕ) + k + t ≤ r) :
    ∀ i j, (C * Nᵀ) i j ≠ 0 → (i : ℕ) + j + (t + 1) ≤ r := by
  intro i j h
  rw [Matrix.mul_apply] at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := hC i k (left_ne_zero_of_mul hk)
  have h2 := hN j k (by simpa using right_ne_zero_of_mul hk)
  omega

theorem supp_conj_sub {D : Matrix (Fin r) (Fin r) K} (hD : D.IsUpperTriangular)
    (h1 : ∀ i, D i i = 1) {C : Matrix (Fin r) (Fin r) K} {t : ℕ}
    (hC : ∀ i j, C i j ≠ 0 → (i : ℕ) + j + t ≤ r) :
    ∀ i j, (D * C * Dᵀ - C) i j ≠ 0 → (i : ℕ) + j + (t + 1) ≤ r := by
  set N : Matrix (Fin r) (Fin r) K := D - 1 with hN
  have hNs : ∀ i k, N i k ≠ 0 → (i : ℕ) < k := by
    intro i k hik
    by_contra hge
    apply hik
    rw [hN, Matrix.sub_apply]
    by_cases hki : k = i
    · subst hki
      rw [h1 k, Matrix.one_apply_eq, sub_self]
    · have hlt : k < i := by
        rw [Fin.lt_def]
        have : (k : ℕ) ≠ i := fun h => hki (Fin.ext h)
        omega
      rw [hD hlt, Matrix.one_apply_ne (Ne.symm hki), sub_self]
  have hD' : D = 1 + N := by rw [hN]; abel
  have key : D * C * Dᵀ - C = N * C + C * Nᵀ + N * (C * Nᵀ) := by
    rw [hD', Matrix.transpose_add, Matrix.transpose_one]
    noncomm_ring
  intro i j h
  rw [key] at h
  have h1' := supp_mul_left hNs hC
  have h2' := supp_mul_right hNs hC
  have h3' := supp_mul_left hNs (supp_mul_right hNs hC)
  by_contra hlt
  apply h
  have e1 : (N * C) i j = 0 := by
    by_contra hne
    exact hlt (by have := h1' i j hne; omega)
  have e2 : (C * Nᵀ) i j = 0 := by
    by_contra hne
    exact hlt (by have := h2' i j hne; omega)
  have e3 : (N * (C * Nᵀ)) i j = 0 := by
    by_contra hne
    exact hlt (by have := h3' i j hne; omega)
  rw [Matrix.add_apply, Matrix.add_apply, e1, e2, e3]
  simp

theorem row0_mul_left {D F : Matrix (Fin r) (Fin r) K} (hD : D.IsUpperTriangular)
    (hF : ∀ k j, F k j ≠ 0 → (k : ℕ) = 0 ∨ (j : ℕ) = 0) :
    ∀ i j, (D * F) i j ≠ 0 → (i : ℕ) = 0 ∨ (j : ℕ) = 0 := by
  intro i j h
  rw [Matrix.mul_apply] at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hDi := left_ne_zero_of_mul hk
  have hFk := hF k j (right_ne_zero_of_mul hk)
  have hik : (i : ℕ) ≤ k := by
    by_contra hlt
    exact hDi (hD (show k < i from by rw [Fin.lt_def]; omega))
  omega

theorem row0_mul_right {D F : Matrix (Fin r) (Fin r) K} (hD : D.IsUpperTriangular)
    (hF : ∀ i k, F i k ≠ 0 → (i : ℕ) = 0 ∨ (k : ℕ) = 0) :
    ∀ i j, (F * Dᵀ) i j ≠ 0 → (i : ℕ) = 0 ∨ (j : ℕ) = 0 := by
  intro i j h
  rw [Matrix.mul_apply] at h
  obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hFl := hF i l (left_ne_zero_of_mul hl)
  have hDj : D j l ≠ 0 := by simpa using right_ne_zero_of_mul hl
  have hjl : (j : ℕ) ≤ l := by
    by_contra hlt
    exact hDj (hD (show l < j from by rw [Fin.lt_def]; omega))
  omega

theorem alt_conj {M : Matrix (Fin r) (Fin r) K} (hM : Mᵀ = -M) (hd : ∀ i, M i i = 0)
    (D : Matrix (Fin r) (Fin r) K) :
    (D * M * Dᵀ)ᵀ = -(D * M * Dᵀ) ∧ ∀ i, (D * M * Dᵀ) i i = 0 := by
  refine CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.alternating_of_mulVec_dotProduct_self
    fun y => ?_
  set z := Dᵀ *ᵥ y with hz
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose,
    dotProduct_comm]
  exact CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.mulVec_dotProduct_self_eq_zero hM hd z

theorem cross_sub_alt {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A]
    {qA : QuadraticForm K A} (L L' : Fin r → A) :
    (crossMat qA L L' - crossMat qA L' L)ᵀ = -(crossMat qA L L' - crossMat qA L' L) ∧
      ∀ i, (crossMat qA L L' - crossMat qA L' L) i i = 0 := by
  constructor
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.neg_apply, crossMat, of_apply]
    rw [polar_comm qA (L j) (L' i), polar_comm qA (L' j) (L i)]
    ring
  · intro i
    simp only [Matrix.sub_apply, crossMat, of_apply]
    rw [polar_comm qA (L i) (L' i)]
    ring

theorem cross_single_row0 {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A]
    {qA : QuadraticForm K A} (i₀ : Fin r) (v : A) (L' : Fin r → A) :
    ∀ i j, (crossMat qA (Pi.single i₀ v) L' - crossMat qA L' (Pi.single i₀ v)) i j ≠ 0 →
      i = i₀ ∨ j = i₀ := by
  intro i j h
  by_contra hcon
  push Not at hcon
  apply h
  simp [crossMat, Pi.single_apply, hcon.1, hcon.2]

end Supp

section Grp

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}

@[expose] def tailGrp (qA : QuadraticForm K A) (i₀ : Fin r) (W : AddSubgroup A) (t : ℕ) :
    Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) where
  carrier := {g | ∃ v ∈ W, ∃ C, AltSupp t C ∧ g = uMap qA (Pi.single i₀ v) C}
  one_mem' := ⟨0, W.zero_mem, 0, AltSupp.zero t, by rw [Pi.single_zero]; exact uMap_zero_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨v, hv, C, hC, rfl⟩ ⟨v', hv', C', hC', rfl⟩
    exact ⟨v + v', W.add_mem hv hv', C + C', hC.add hC', uMap_single_mul i₀ v v' C C'⟩
  inv_mem' := by
    rintro _ ⟨v, hv, C, hC, rfl⟩
    exact ⟨-v, W.neg_mem hv, -C, hC.neg, uMap_single_inv i₀ v C⟩

theorem tailGrp_le_tailUnipotent (qA : QuadraticForm K A) (i₀ : Fin r) (W : AddSubgroup A)
    (t : ℕ) : tailGrp qA i₀ W t ≤ tailUnipotent r qA := by
  rintro _ ⟨v, hv, C, hC, rfl⟩
  have h := dMap_mul_uMap_mem_tailUnipotent (D := (1 : GL (Fin r) K)) (qA := qA)
    (by simpa using (Matrix.blockTriangular_one : (1 : Matrix (Fin r) (Fin r) K).IsUpperTriangular))
    (fun i => by simp) (Pi.single i₀ v) hC.1 hC.2.1
  rwa [dMap_one_one, one_mul] at h

theorem tailGrp_mono {qA : QuadraticForm K A} {i₀ : Fin r} {W W' : AddSubgroup A} {t t' : ℕ}
    (hW : W ≤ W') (ht : t ≤ t') : tailGrp qA i₀ W t' ≤ tailGrp qA i₀ W' t := by
  rintro _ ⟨v, hv, C, hC, rfl⟩
  exact ⟨v, hW hv, C, hC.mono ht, rfl⟩

theorem tailGrp_comm {qA : QuadraticForm K A} {i₀ : Fin r} {W : AddSubgroup A} {t : ℕ}
    {g g' : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : g ∈ tailGrp qA i₀ W t) (hg' : g' ∈ tailGrp qA i₀ W t) : g * g' = g' * g := by
  obtain ⟨v, -, C, -, rfl⟩ := hg
  obtain ⟨v', -, C', -, rfl⟩ := hg'
  rw [uMap_single_mul, uMap_single_mul, add_comm v v', add_comm C C']

theorem tailGrp_pow {p : ℕ} [CharP K p] {qA : QuadraticForm K A} {i₀ : Fin r}
    {W : AddSubgroup A} {t : ℕ}
    {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : g ∈ tailGrp qA i₀ W t) : g ^ p = 1 := by
  obtain ⟨v, -, C, -, rfl⟩ := hg
  rw [uMap_single_pow]
  have h1 : p • v = 0 := by rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
  have h2 : p • C = 0 := by rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
  rw [h1, h2, Pi.single_zero]
  exact uMap_zero_zero

theorem commutator_mem_tailGrp [FiniteDimensional K A] {qA : QuadraticForm K A}
    (hani : qA.Anisotropic) {i₀ : Fin r} (hi₀ : (i₀ : ℕ) = 0)
    {u a : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hu : u ∈ tailUnipotent r qA) (ha : a ∈ tailGrp qA i₀ ⊤ 0) :
    u * a * u⁻¹ * a⁻¹ ∈ tailGrp qA i₀ ⊥ 1 := by
  obtain ⟨D, L', C', hD, h1, -, -, rfl⟩ := (mem_tailUnipotent_iff hani).1 hu
  obtain ⟨v, -, C, hC, rfl⟩ := ha
  rw [commutator_formula hD h1 hi₀ v C L' C']
  refine ⟨0, AddSubgroup.zero_mem _, _, ?_, by rw [Pi.single_zero]⟩
  set Dm : Matrix (Fin r) (Fin r) K := (D : Matrix (Fin r) (Fin r) K) with hDm
  set E : Matrix (Fin r) (Fin r) K :=
    crossMat qA (Pi.single i₀ v) L' - crossMat qA L' (Pi.single i₀ v) with hE
  obtain ⟨hE1, hE2⟩ : Eᵀ = -E ∧ ∀ i, E i i = 0 := cross_sub_alt (qA := qA) (Pi.single i₀ v) L'
  have hEC1 : (E + C)ᵀ = -(E + C) := by
    rw [Matrix.transpose_add, hE1, hC.1, neg_add]
  have hEC2 : ∀ i, (E + C) i i = 0 := fun i => by
    rw [Matrix.add_apply, hE2 i, hC.2.1 i, add_zero]
  obtain ⟨hX1, hX2⟩ := alt_conj hEC1 hEC2 Dm
  refine ⟨?_, fun i => ?_, fun i j hij => ?_⟩
  · rw [Matrix.transpose_sub, hX1, hC.1, neg_sub_left, neg_add_eq_sub, sub_eq_add_neg]
  · rw [Matrix.sub_apply, hX2 i, hC.2.1 i, sub_zero]
  · have hsplit : Dm * (E + C) * Dmᵀ - C = (Dm * C * Dmᵀ - C) + Dm * E * Dmᵀ := by
      rw [mul_add, add_mul]
      abel
    rw [hsplit] at hij
    by_contra hlt
    apply hij
    have e1 : (Dm * C * Dmᵀ - C) i j = 0 := by
      by_contra hne
      exact hlt (by have := supp_conj_sub hD h1 hC.2.2 i j hne; omega)
    have e2 : (Dm * E * Dmᵀ) i j = 0 := by
      by_contra hne
      have hrow := row0_mul_right hD (row0_mul_left hD (fun k j hkj => by
        rcases cross_single_row0 (qA := qA) i₀ v L' k j hkj with h | h
        · exact Or.inl (by rw [h, hi₀])
        · exact Or.inr (by rw [h, hi₀]))) i j hne
      have := i.isLt
      have := j.isLt
      omega
    rw [Matrix.add_apply, e1, e2, add_zero]

end Grp

section Main

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A]

theorem uMap_param_injective {qA : QuadraticForm K A} {r : ℕ} {L L' : Fin r → A}
    {C C' : Matrix (Fin r) (Fin r) K} (h : uMap qA L C = uMap qA L' C') : L = L' ∧ C = C' := by
  have := dMap_uMap_injective (D := (1 : GL (Fin r) K)) (D' := 1) (h := (1 : A ≃ₗ[K] A))
    (h' := 1) (L := L) (L' := L') (C := C) (C' := C')
    (by rw [dMap_one_one, one_mul, one_mul]; exact h)
  exact ⟨this.2.2.1, this.2.2.2⟩

theorem altE_altSupp {r : ℕ} {a b : Fin r} (hab : a ≠ b) {t : ℕ} (hle : (a : ℕ) + b + t ≤ r) :
    AltSupp t (altE a b : Matrix (Fin r) (Fin r) K) := by
  refine ⟨altE_transpose a b, altE_diag hab, fun i j hij => ?_⟩
  by_cases h1 : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h1
    exact hle
  · by_cases h2 : b = i ∧ a = j
    · obtain ⟨rfl, rfl⟩ := h2
      omega
    · exact absurd (altE_apply_of_ne h1 h2) hij

theorem tail_independent {p : ℕ} [CharP K p] {qA : QuadraticForm K A} {r : ℕ} {i₀ : Fin r}
    {v₀ : A} (hv₀ : v₀ ≠ 0) {a b : Fin r} (hab : a ≠ b) (hs : (a : ℕ) + b = r) (i j : ℕ)
    (h : uMap qA (Pi.single i₀ v₀) 0 ^ i * uMap qA (Pi.single i₀ 0) (altE a b) ^ j ∈
      tailGrp qA i₀ ⊥ 1) : p ∣ i ∧ p ∣ j := by
  rw [uMap_single_pow, uMap_single_pow, uMap_single_mul] at h
  obtain ⟨w, hw, C', hC', heq⟩ := h
  have hw0 : w = 0 := (AddSubgroup.mem_bot).1 hw
  obtain ⟨hL, hC⟩ := uMap_param_injective heq
  have hL' := congrFun hL i₀
  simp only [Pi.single_eq_same, hw0, smul_zero, add_zero] at hL'
  have hi : (i : K) = 0 := by
    have : (i : K) • v₀ = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact hL'
    exact (smul_eq_zero.1 this).resolve_right hv₀
  have hC1 := congrFun (congrFun hC a) b
  have hC0 : C' a b = 0 := by
    by_contra hne
    have := hC'.2.2 a b hne
    omega
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_zero, zero_add,
    altE_apply_self hab, hC0] at hC1
  simp only [nsmul_eq_mul, mul_one] at hC1
  exact ⟨(CharP.cast_eq_zero_iff K p i).1 hi, (CharP.cast_eq_zero_iff K p j).1 hC1⟩

theorem isElemAbelian_subgroupOf {G : Type*} [Group G] (p : ℕ) (E X : Subgroup G)
    (hcomm : ∀ g ∈ X, ∀ g' ∈ X, g * g' = g' * g) (hexp : ∀ g ∈ X, g ^ p = 1) :
    IsElemAbelian p (X.subgroupOf E) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · exact Subtype.ext (Subtype.ext (hcomm _ x.2 _ y.2))
  · exact Subtype.ext (hexp _ hx)

theorem rankThreeCent_of_tail {p : ℕ} [hp : Fact p.Prime] [Finite K] [CharP K p]
    [FiniteDimensional K A] {r : ℕ} (hr : 3 ≤ r) {qA : QuadraticForm K A}
    (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate)
    (hm : Module.finrank K A = 1 ∨ Module.finrank K A = 2) {S : Type} [Group S] [Finite S]
    (π : orthElementaryGroup (quadTail r qA) →* S) (hπ : Function.Surjective π)
    (hπinj : ∀ u ∈ (tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA)),
      π u = 1 → u = 1) : RankThreeCent p S := by
  haveI : Finite A := Module.finite_of_finite K
  haveI : Finite (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
    Finite.of_injective (β := ((Fin r ⊕ Fin r → K) × A) → ((Fin r ⊕ Fin r → K) × A))
      (fun e => ⇑e) fun a b h => LinearEquiv.ext (congrFun h)
  let E := orthElementaryGroup (quadTail r qA)
  have hpos : 0 < Module.finrank K A := by rcases hm with h | h <;> omega
  haveI : Nontrivial A := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : A)
  obtain ⟨i0, hi0⟩ : ∃ i : Fin r, (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, hi1⟩ : ∃ i : Fin r, (i : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨i2, hi2⟩ : ∃ i : Fin r, (i : ℕ) = r - 1 := ⟨⟨r - 1, by omega⟩, rfl⟩
  have h01 : i0 ≠ i1 := fun h' => by have := congrArg Fin.val h'; omega
  have h12 : i1 ≠ i2 := fun h' => by have := congrArg Fin.val h'; omega
  have hAU : tailGrp qA i0 ⊤ 0 ≤ tailUnipotent r qA := tailGrp_le_tailUnipotent qA i0 ⊤ 0
  have hBA : tailGrp qA i0 ⊥ 1 ≤ tailGrp qA i0 ⊤ 0 := tailGrp_mono bot_le (Nat.zero_le 1)
  have hUE : tailUnipotent r qA ≤ E := tailUnipotent_le
  have hmemA₁ : uMap qA (Pi.single i0 v₀) 0 ∈ tailGrp qA i0 ⊤ 0 :=
    ⟨v₀, AddSubgroup.mem_top _, 0, AltSupp.zero 0, rfl⟩
  have hmemA₂ : uMap qA (Pi.single i0 0) (altE i1 i2) ∈ tailGrp qA i0 ⊤ 0 :=
    ⟨0, AddSubgroup.mem_top _, _, altE_altSupp h12 (by omega), rfl⟩
  have hmemB : uMap qA (Pi.single i0 0) (altE i0 i1) ∈ tailGrp qA i0 ⊥ 1 :=
    ⟨0, AddSubgroup.zero_mem _, _, altE_altSupp h01 (by omega), rfl⟩
  let a₁ : ↥E := ⟨uMap qA (Pi.single i0 v₀) 0, hUE (hAU hmemA₁)⟩
  let a₂ : ↥E := ⟨uMap qA (Pi.single i0 0) (altE i1 i2), hUE (hAU hmemA₂)⟩
  let b₀ : ↥E := ⟨uMap qA (Pi.single i0 0) (altE i0 i1), hUE (hAU (hBA hmemB))⟩
  have hA : IsElemAbelian p ((tailGrp qA i0 ⊤ 0).subgroupOf E) :=
    isElemAbelian_subgroupOf p E _ (fun g hg g' hg' => tailGrp_comm hg hg')
      (fun g hg => tailGrp_pow hg)
  have hBA' : (tailGrp qA i0 ⊥ 1).subgroupOf E ≤ (tailGrp qA i0 ⊤ 0).subgroupOf E :=
    fun x hx => hBA hx
  have hind : ∀ i j : ℕ, a₁ ^ i * a₂ ^ j ∈ (tailGrp qA i0 ⊥ 1).subgroupOf E → p ∣ i ∧ p ∣ j := by
    intro i j h
    have h' : uMap qA (Pi.single i0 v₀) 0 ^ i * uMap qA (Pi.single i0 0) (altE i1 i2) ^ j ∈
        tailGrp qA i0 ⊥ 1 := h
    exact tail_independent hv₀ h12 (by omega) i j h'
  have hcard := card_mul_le_of_independent hA hBA' (a₁ := a₁) (a₂ := a₂) hmemA₁ hmemA₂ hind
  have hb₀1 : b₀ ≠ 1 := by
    intro h1
    have h2 : uMap qA (Pi.single i0 0) (altE i0 i1) = uMap qA (Pi.single i0 0) 0 := by
      have h3 : uMap qA (Pi.single i0 0) (altE i0 i1) = 1 := congrArg Subtype.val h1
      rw [h3, Pi.single_zero]
      exact uMap_zero_zero.symm
    have h3 := (uMap_param_injective h2).2
    have h4 := congrFun (congrFun h3 i0) i1
    rw [altE_apply_self h01, Matrix.zero_apply] at h4
    exact one_ne_zero h4
  have hb₀A : b₀ ∈ (tailGrp qA i0 ⊤ 0).subgroupOf E := hBA hmemB
  have hb₀p : orderOf b₀ = p := orderOf_eq_prime (hA.2 b₀ hb₀A) hb₀1
  have hBp : p ≤ Nat.card ((tailGrp qA i0 ⊥ 1).subgroupOf E) := by
    have := Subgroup.card_le_of_le (zpowers_le.mpr (show b₀ ∈ (tailGrp qA i0 ⊥ 1).subgroupOf E
      from hmemB))
    rwa [Nat.card_zpowers, hb₀p] at this
  have hbig : p ^ 3 ≤ Nat.card ((tailGrp qA i0 ⊤ 0).subgroupOf E) := by
    calc p ^ 3 = p * p ^ 2 := by ring
      _ ≤ Nat.card ((tailGrp qA i0 ⊥ 1).subgroupOf E) * p ^ 2 := Nat.mul_le_mul_right _ hBp
      _ ≤ _ := hcard
  exact rankThreeCent_of_witness_map π hπ (isPGroup_tailUnipotent (p := p) hani)
    (not_dvd_index_tailUnipotent hr hani hreg hm) (fun x hx => hAU hx) hBA' hA
    (fun u hu a ha => commutator_mem_tailGrp hani hi0 hu ha) hcard (Or.inl hbig) hπinj

end Main

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC
