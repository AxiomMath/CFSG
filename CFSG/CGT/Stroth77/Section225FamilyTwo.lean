module

public import CFSG.CGT.Stroth77.Section224CExtension

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {G : Type} [Group G] [Finite G] {X : StrothAmbient G}

@[expose] def thetaTwoM (m : ℕ) : IntMat :=
  Matrix.diagonal ![2, 2 + (2 : ℤ) ^ (m + 1), 2 + (2 : ℤ) ^ (m + 1)]

theorem thetaTwoM_compat (m : ℕ) : Compat (Type200.k m) (thetaTwoM m) := by
  refine Compat.of_witness (C := thetaTwoM m) ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [thetaTwoM, Type200.k, Matrix.diagonal]

@[expose] def thetaTwo (m : ℕ) : Torus (Type200.k m) →+ Torus (Type200.k m) :=
  matAct (Type200.k m) (thetaTwoM m) (thetaTwoM_compat m)

theorem thetaTwo_ofInt (m : ℕ) (v : Fin 3 → ℤ) :
    thetaTwo m (Torus.ofInt (Type200.k m) v) =
      Torus.ofInt (Type200.k m) (thetaTwoM m *ᵥ v) := by
  rw [thetaTwo, matAct_ofInt]

@[expose] def thetaTwoPreInt (m : ℕ) (W : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![W 0, (1 - (2 : ℤ) ^ m) * W 1, (1 - (2 : ℤ) ^ m) * W 2]

theorem thetaTwo_thetaPreInt (m : ℕ) (hm : 1 ≤ m) (W : Fin 3 → ℤ) :
    thetaTwo m (Torus.ofInt (Type200.k m) (thetaTwoPreInt m W)) =
      (2 : ℤ) • Torus.ofInt (Type200.k m) W := by
  rw [thetaTwo_ofInt, ← Torus.ofInt_zsmul]
  apply Torus.ofInt_eq_ofInt_iff.mpr
  intro i
  rw [thetaTwoM, Matrix.mulVec_diagonal]
  fin_cases i
  · change 2 * W 0 ≡ 2 * W 0 [ZMOD 2 ^ m]
    exact Int.ModEq.refl _
  · change (2 + (2 : ℤ) ^ (m + 1)) * ((1 - (2 : ℤ) ^ m) * W 1) ≡
      2 * W 1 [ZMOD 2 ^ (m + 2)]
    rw [Int.modEq_iff_dvd]
    have hcoef : (2 + (2 : ℤ) ^ (m + 1)) * (1 - (2 : ℤ) ^ m) =
        2 - (2 : ℤ) ^ (2 * m + 1) := by
      have h1 : (2 : ℤ) ^ (m + 1) = 2 * (2 : ℤ) ^ m := by
        rw [pow_succ]; ring
      have h2 : (2 : ℤ) ^ (m + 1) * (2 : ℤ) ^ m = (2 : ℤ) ^ (2 * m + 1) := by
        rw [← pow_add]; congr 1; omega
      rw [show (2 + (2 : ℤ) ^ (m + 1)) * (1 - (2 : ℤ) ^ m) =
          2 - (2 : ℤ) ^ (m + 1) * (2 : ℤ) ^ m by rw [h1]; ring, h2]
    refine ⟨(2 : ℤ) ^ (m - 1) * W 1, ?_⟩
    rw [← mul_assoc, hcoef]
    have hp : (2 : ℤ) ^ (2 * m + 1) = (2 : ℤ) ^ (m + 2) * (2 : ℤ) ^ (m - 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hp]; ring
  · change (2 + (2 : ℤ) ^ (m + 1)) * ((1 - (2 : ℤ) ^ m) * W 2) ≡
      2 * W 2 [ZMOD 2 ^ (m + 2)]
    rw [Int.modEq_iff_dvd]
    have hcoef : (2 + (2 : ℤ) ^ (m + 1)) * (1 - (2 : ℤ) ^ m) =
        2 - (2 : ℤ) ^ (2 * m + 1) := by
      have h1 : (2 : ℤ) ^ (m + 1) = 2 * (2 : ℤ) ^ m := by
        rw [pow_succ]; ring
      have h2 : (2 : ℤ) ^ (m + 1) * (2 : ℤ) ^ m = (2 : ℤ) ^ (2 * m + 1) := by
        rw [← pow_add]; congr 1; omega
      rw [show (2 + (2 : ℤ) ^ (m + 1)) * (1 - (2 : ℤ) ^ m) =
          2 - (2 : ℤ) ^ (m + 1) * (2 : ℤ) ^ m by rw [h1]; ring, h2]
    refine ⟨(2 : ℤ) ^ (m - 1) * W 2, ?_⟩
    rw [← mul_assoc, hcoef]
    have hp : (2 : ℤ) ^ (2 * m + 1) = (2 : ℤ) ^ (m + 2) * (2 : ℤ) ^ (m - 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hp]; ring

theorem thetaTwoM_mulVec_even (m : ℕ) (D : Fin 3 → ℤ) (i : Fin 3) :
    Even ((thetaTwoM m *ᵥ D) i) := by
  rw [thetaTwoM, Matrix.mulVec_diagonal]
  fin_cases i
  · change Even (2 * D 0)
    exact even_two_mul _
  · change Even ((2 + (2 : ℤ) ^ (m + 1)) * D 1)
    refine ⟨(1 + (2 : ℤ) ^ m) * D 1, ?_⟩
    have h : (2 : ℤ) ^ (m + 1) = 2 * (2 : ℤ) ^ m := by rw [pow_succ]; ring
    rw [h]; ring
  · change Even ((2 + (2 : ℤ) ^ (m + 1)) * D 2)
    refine ⟨(1 + (2 : ℤ) ^ m) * D 2, ?_⟩
    have h : (2 : ℤ) ^ (m + 1) = 2 * (2 : ℤ) ^ m := by rw [pow_succ]; ring
    rw [h]; ring

theorem thetaTwo_range_eq (m : ℕ) (hm : 1 ≤ m) :
    Set.range (thetaTwo m) = {v : Torus (Type200.k m) | ∃ w, (2 : ℤ) • w = v} := by
  ext v
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨D, hD⟩ := Torus.exists_ofInt d
    have hv : thetaTwo m d = Torus.ofInt (Type200.k m) (thetaTwoM m *ᵥ D) := by
      rw [← hD, thetaTwo_ofInt]
    refine ⟨Torus.ofInt (Type200.k m)
      (fun i => (thetaTwoM m *ᵥ D) i / 2), ?_⟩
    rw [hv, ← Torus.ofInt_zsmul]
    apply Torus.ofInt_eq_ofInt_iff.mpr
    intro i
    simp only [Pi.smul_apply, smul_eq_mul, Torus.ofInt_apply]
    rw [Int.two_mul_ediv_two_of_even (thetaTwoM_mulVec_even m D i)]
  · rintro ⟨w, rfl⟩
    obtain ⟨W, hW⟩ := Torus.exists_ofInt w
    exact ⟨Torus.ofInt (Type200.k m) (thetaTwoPreInt m W),
      by rw [thetaTwo_thetaPreInt m hm W, hW]⟩

theorem exists_thetaTwo_eq_of_two_zsmul (m : ℕ) (hm : 1 ≤ m)
    {v : Torus (Type200.k m)} (hv : ∃ w, (2 : ℤ) • w = v) :
    ∃ d, thetaTwo m d = v := by
  obtain ⟨w, hw⟩ := hv
  obtain ⟨W, hW⟩ := Torus.exists_ofInt w
  exact ⟨Torus.ofInt (Type200.k m) (thetaTwoPreInt m W),
    by rw [thetaTwo_thetaPreInt m hm W, hW, hw]⟩

theorem even_matVec_sub_of_thetaTwo_eq (m : ℕ) (hm : 1 ≤ m) (M : IntMat)
    (hM : Compat (Type200.k m) M) {q : Torus (Type200.k m)}
    (h : ∃ d, thetaTwo m d = matAct (Type200.k m) M hM q - q)
    (Q : Fin 3 → ℤ) (hQ : q = Torus.ofInt (Type200.k m) Q) (i : Fin 3) :
    Even ((M *ᵥ Q - Q) i) := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨D, hD⟩ := Torus.exists_ofInt d
  have htheta : thetaTwo m d = Torus.ofInt (Type200.k m) (thetaTwoM m *ᵥ D) := by
    rw [← hD, thetaTwo_ofInt]
  have hMq : matAct (Type200.k m) M hM q - q =
      Torus.ofInt (Type200.k m) (M *ᵥ Q - Q) := by
    rw [hQ, matAct_ofInt, Torus.ofInt_sub]
  have hEq : Torus.ofInt (Type200.k m) (M *ᵥ Q - Q) =
      Torus.ofInt (Type200.k m) (thetaTwoM m *ᵥ D) := by
    rw [← hMq, ← hd, htheta]
  have hcoord := congrFun hEq i
  have hmeven : Even ((thetaTwoM m *ᵥ D) i) := thetaTwoM_mulVec_even m D i
  have hk1 : 1 ≤ (Type200.k m) i := by
    fin_cases i <;> simp [Type200.k] <;> omega
  exact even_of_intCast_eq_even (n := (Type200.k m) i) hk1 hmeven hcoord

theorem thetaTwo_eq_iff_even (m : ℕ) (hm : 1 ≤ m) (M : IntMat)
    (hM : Compat (Type200.k m) M) {q : Torus (Type200.k m)} (Q : Fin 3 → ℤ)
    (hQ : q = Torus.ofInt (Type200.k m) Q) :
    (∃ d, thetaTwo m d = matAct (Type200.k m) M hM q - q) ↔
      ∀ i, Even ((M *ᵥ Q - Q) i) := by
  constructor
  · intro h i
    exact even_matVec_sub_of_thetaTwo_eq m hm M hM h Q hQ i
  · intro h
    let E : Fin 3 → ℤ := fun i => (M *ᵥ Q - Q) i / 2
    have hE : (2 : ℤ) • E = M *ᵥ Q - Q := by
      funext i
      simpa [E, Pi.smul_apply, smul_eq_mul] using Int.two_mul_ediv_two_of_even (h i)
    have hv : (2 : ℤ) • Torus.ofInt (Type200.k m) E =
        matAct (Type200.k m) M hM q - q := by
      rw [← Torus.ofInt_zsmul, hE, hQ, matAct_ofInt, Torus.ofInt_sub]
    exact exists_thetaTwo_eq_of_two_zsmul m hm ⟨Torus.ofInt (Type200.k m) E, hv⟩

theorem thetaTwo_matAct_iff_of_modEq_two (m : ℕ) (hm : 1 ≤ m) {M M' : IntMat}
    (hM : Compat (Type200.k m) M) (hM' : Compat (Type200.k m) M')
    (hmod : ∀ i j, M i j ≡ M' i j [ZMOD 2]) (q : Torus (Type200.k m)) :
    (∃ d, thetaTwo m d = matAct (Type200.k m) M hM q - q) ↔
      (∃ d, thetaTwo m d = matAct (Type200.k m) M' hM' q - q) := by
  obtain ⟨Q, hQ⟩ := Torus.exists_ofInt q
  rw [thetaTwo_eq_iff_even m hm M hM Q hQ.symm,
    thetaTwo_eq_iff_even m hm M' hM' Q hQ.symm]
  constructor
  · intro h i
    have hdiff : (M *ᵥ Q - Q) i ≡ (M' *ᵥ Q - Q) i [ZMOD 2] :=
      (mulVec_modEq_two hmod (fun _ => Int.ModEq.refl _) i).sub (Int.ModEq.refl (Q i))
    exact (even_iff_even_of_modEq_two hdiff).mp (h i)
  · intro h i
    have hdiff : (M *ᵥ Q - Q) i ≡ (M' *ᵥ Q - Q) i [ZMOD 2] :=
      (mulVec_modEq_two hmod (fun _ => Int.ModEq.refl _) i).sub (Int.ModEq.refl (Q i))
    exact (even_iff_even_of_modEq_two hdiff).mpr (h i)

theorem thetaTwo_c (m : ℕ) :
    thetaTwo m (Torus.c : Torus (Type200.k m)) = (2 : ℤ) • Torus.c := by
  have h : (Torus.c : Torus (Type200.k m)) = Torus.ofInt (Type200.k m) ![1, 0, 0] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    simp [Torus.c]
  rw [h, thetaTwo_ofInt]
  have h2 : thetaTwoM m *ᵥ (![1, 0, 0] : Fin 3 → ℤ) = ![2, 0, 0] := by
    funext i
    fin_cases i <;> simp [thetaTwoM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [h2, Torus.ofInt_eq_zsmul_gens]
  rw [← h]
  simp

theorem thetaTwo_a (m : ℕ) :
    thetaTwo m (Torus.a : Torus (Type200.k m)) =
      (2 + (2 : ℤ) ^ (m + 1)) • Torus.a := by
  have h : (Torus.a : Torus (Type200.k m)) = Torus.ofInt (Type200.k m) ![0, 1, 0] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    simp [Torus.a]
  rw [h, thetaTwo_ofInt]
  have h2 : thetaTwoM m *ᵥ (![0, 1, 0] : Fin 3 → ℤ) = ![0, 2 + (2 : ℤ) ^ (m + 1), 0] := by
    funext i
    fin_cases i <;> simp [thetaTwoM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [h2, Torus.ofInt_eq_zsmul_gens]
  rw [← h]
  simp

theorem thetaTwo_b (m : ℕ) :
    thetaTwo m (Torus.b : Torus (Type200.k m)) =
      (2 + (2 : ℤ) ^ (m + 1)) • Torus.b := by
  have h : (Torus.b : Torus (Type200.k m)) = Torus.ofInt (Type200.k m) ![0, 0, 1] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    simp [Torus.b]
  rw [h, thetaTwo_ofInt]
  have h2 : thetaTwoM m *ᵥ (![0, 0, 1] : Fin 3 → ℤ) = ![0, 0, 2 + (2 : ℤ) ^ (m + 1)] := by
    funext i
    fin_cases i <;> simp [thetaTwoM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [h2, Torus.ofInt_eq_zsmul_gens]
  rw [← h]
  simp

@[expose] def thetaTwoType : (τ : StrothTypeIndex) → Torus τ.k →+ Torus τ.k
  | StrothTypeIndex.t200 m => thetaTwo m
  | StrothTypeIndex.t201 m => thetaTwo m
  | _ => 0

theorem type200_uM_mulVec (Q : Fin 3 → ℤ) :
    Type200.uM *ᵥ Q = ![Q 0, Q 2, Q 1] := by
  funext i
  fin_cases i <;>
    simp [Type200.uM, uMat, ofCols, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem type200_rhoM_mulVec (Q : Fin 3 → ℤ) :
    Type200.ρM *ᵥ Q = ![Q 0 - Q 2, -Q 2, Q 1 - Q 2] := by
  funext i
  fin_cases i <;>
    simp [Type200.ρM, ofCols, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem type200_c_eq_ofInt (m : ℕ) :
    (Torus.c : Torus (Type200.k m)) = Torus.ofInt (Type200.k m) ![1, 0, 0] := by
  rw [Torus.ofInt_eq_zsmul_gens]
  simp [Torus.c]

theorem square_class_dichotomy_familyTwo (m : ℕ) (hm : 2 ≤ m)
    (q : Torus (Type200.k m))
    (hu : ∃ d, thetaTwo m d = matAct (Type200.k m) Type200.uM
      (Type200.compat_u m) q - q)
    (hr : ∃ d, thetaTwo m d = matAct (Type200.k m) Type200.ρM
      (Type200.compat_rho m) q - q) :
    (∃ d, thetaTwo m d = q) ∨ (∃ d, thetaTwo m d = q - Torus.c) := by
  obtain ⟨Q, hQ⟩ := Torus.exists_ofInt q
  have hQ' : q = Torus.ofInt (Type200.k m) Q := hQ.symm
  have hu1 : Even ((Type200.uM *ᵥ Q - Q) 1) :=
    even_matVec_sub_of_thetaTwo_eq m (by omega) Type200.uM (Type200.compat_u m) hu Q hQ' 1
  have hr0 : Even ((Type200.ρM *ᵥ Q - Q) 0) :=
    even_matVec_sub_of_thetaTwo_eq m (by omega) Type200.ρM (Type200.compat_rho m) hr Q hQ' 0
  have hu1' : Even (Q 2 - Q 1) := by
    have hEq : (Type200.uM *ᵥ Q - Q) 1 = Q 2 - Q 1 := by
      rw [type200_uM_mulVec]
      simp [Fin.isValue]
    rwa [hEq] at hu1
  have hr0' : Even (Q 0 - Q 2 - Q 0) := by
    have hEq : (Type200.ρM *ᵥ Q - Q) 0 = Q 0 - Q 2 - Q 0 := by
      rw [type200_rhoM_mulVec]
      simp [Fin.isValue]
    rwa [hEq] at hr0
  have hQ2 : Even (Q 2) := by
    have h : Even (-(Q 2)) := by
      have h' : Q 0 - Q 2 - Q 0 = -(Q 2) := by ring
      rwa [h'] at hr0'
    exact even_neg.mp h
  have hQ1 : Even (Q 1) := by
    have h := hQ2.sub hu1'
    have h' : Q 2 - (Q 2 - Q 1) = Q 1 := by ring
    rwa [h'] at h
  rcases Int.even_or_odd (Q 0) with hQ0 | hQ0
  · obtain ⟨e0, he0⟩ := even_iff_exists_two_mul.mp hQ0
    obtain ⟨e1, he1⟩ := even_iff_exists_two_mul.mp hQ1
    obtain ⟨e2, he2⟩ := even_iff_exists_two_mul.mp hQ2
    let E : Fin 3 → ℤ := ![e0, e1, e2]
    have hE : (2 : ℤ) • E = Q := by
      funext i
      fin_cases i <;> simp [E, he0, he1, he2]
    have hq2 : (2 : ℤ) • Torus.ofInt (Type200.k m) E = q := by
      rw [← Torus.ofInt_zsmul, hE, ← hQ']
    obtain ⟨d, hd⟩ := exists_thetaTwo_eq_of_two_zsmul m (by omega) ⟨_, hq2⟩
    exact Or.inl ⟨d, hd⟩
  · obtain ⟨e0, he0⟩ := hQ0
    obtain ⟨e1, he1⟩ := even_iff_exists_two_mul.mp hQ1
    obtain ⟨e2, he2⟩ := even_iff_exists_two_mul.mp hQ2
    let E : Fin 3 → ℤ := ![e0, e1, e2]
    have hE : (2 : ℤ) • E = Q - ![1, 0, 0] := by
      funext i
      fin_cases i <;> simp [E, he0, he1, he2] <;> omega
    have hq2 : (2 : ℤ) • Torus.ofInt (Type200.k m) E = q - Torus.c := by
      rw [← Torus.ofInt_zsmul, hE, Torus.ofInt_sub, ← hQ', type200_c_eq_ofInt]
    obtain ⟨d, hd⟩ := exists_thetaTwo_eq_of_two_zsmul m (by omega) ⟨_, hq2⟩
    exact Or.inr ⟨d, hd⟩

theorem square_class_dichotomy_t200 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) {m : ℕ} (hτ : Z.τ = StrothTypeIndex.t200 m)
    (q : Torus Z.τ.k)
    (huv : ∃ d, thetaTwoType Z.τ d =
      matAct Z.τ.k Z.τ.action.uv Z.τ.action.compat_uv q - q)
    (ht : ∃ d, thetaTwoType Z.τ d =
      matAct Z.τ.k Z.τ.action.t Z.τ.action.compat_t q - q)
    (hu : ∃ d, thetaTwoType Z.τ d =
      matAct Z.τ.k Z.τ.action.u Z.τ.action.compat_u q - q)
    (hρ : ∃ d, thetaTwoType Z.τ d =
      matAct Z.τ.k Z.τ.action.ρ Z.τ.action.compat_ρ q - q) :
    (∃ d, thetaTwoType Z.τ d = q) ∨
      (∃ d, thetaTwoType Z.τ d = q - gen Z.τ.k 0) := by
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  have hm2 : 2 ≤ m := by simpa [StrothTypeIndex.k, Type200.k] using hk 0
  exact square_class_dichotomy_familyTwo m hm2 q hu hρ

theorem square_class_dichotomy_t201 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) {m : ℕ} (hτ : Z.τ = StrothTypeIndex.t201 m)
    (q : Torus Z.τ.k)
    (huv : ∃ d, thetaTwoType Z.τ d =
      matAct Z.τ.k Z.τ.action.uv Z.τ.action.compat_uv q - q)
    (ht : ∃ d, thetaTwoType Z.τ d =
      matAct Z.τ.k Z.τ.action.t Z.τ.action.compat_t q - q)
    (hu : ∃ d, thetaTwoType Z.τ d =
      matAct Z.τ.k Z.τ.action.u Z.τ.action.compat_u q - q)
    (hρ : ∃ d, thetaTwoType Z.τ d =
      matAct Z.τ.k Z.τ.action.ρ Z.τ.action.compat_ρ q - q) :
    (∃ d, thetaTwoType Z.τ d = q) ∨
      (∃ d, thetaTwoType Z.τ d = q - gen Z.τ.k 0) := by
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  have hm2 : 2 ≤ m := by simpa [StrothTypeIndex.k, Type201.k] using hk 0
  exact square_class_dichotomy_familyTwo m hm2 q hu hρ

theorem square_class_dichotomy_familyTwo_type (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i)
    (hτ : (∃ m : ℕ, Z.τ = StrothTypeIndex.t200 m) ∨
      (∃ m : ℕ, Z.τ = StrothTypeIndex.t201 m))
    (q : Torus Z.τ.k)
    (huv : ∃ d, thetaTwoType Z.τ d =
      matAct Z.τ.k Z.τ.action.uv Z.τ.action.compat_uv q - q)
    (ht : ∃ d, thetaTwoType Z.τ d =
      matAct Z.τ.k Z.τ.action.t Z.τ.action.compat_t q - q)
    (hu : ∃ d, thetaTwoType Z.τ d =
      matAct Z.τ.k Z.τ.action.u Z.τ.action.compat_u q - q)
    (hρ : ∃ d, thetaTwoType Z.τ d =
      matAct Z.τ.k Z.τ.action.ρ Z.τ.action.compat_ρ q - q) :
    (∃ d, thetaTwoType Z.τ d = q) ∨
      (∃ d, thetaTwoType Z.τ d = q - gen Z.τ.k 0) := by
  rcases hτ with ⟨m, h⟩ | ⟨m, h⟩
  · exact square_class_dichotomy_t200 Z hk h q huv ht hu hρ
  · exact square_class_dichotomy_t201 Z hk h q huv ht hu hρ

theorem dvd_two_pow_of_four_mul_dvd {m : ℕ} {j : ℤ}
    (h : (2 : ℤ) ^ (m + 2) ∣ 4 * j) : (2 : ℤ) ^ m ∣ j := by
  have hpow : (2 : ℤ) ^ (m + 2) = 4 * (2 : ℤ) ^ m := by
    rw [show m + 2 = 2 + m by omega, pow_add]
    norm_num
  rw [hpow] at h
  exact Int.dvd_of_mul_dvd_mul_left (a := 4) (by norm_num) (by simpa [mul_comm] using h)

theorem two_torsion_solution_familyTwo (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n)
    (w w' : Torus Z.τ.k) (hw2 : (2 : ℤ) • w = 0) (hw2' : (2 : ℤ) • w' = 0)
    (hU00 : Z.τ.action.u 0 0 = 1) (hU01 : Z.τ.action.u 0 1 = 0)
    (hU02 : Z.τ.action.u 0 2 = 0)
    (hU10 : Z.τ.action.u 1 0 = 0) (hU11 : Z.τ.action.u 1 1 = 0)
    (hU12 : Z.τ.action.u 1 2 = 1)
    (hU20 : Z.τ.action.u 2 0 = 0) (hU21 : Z.τ.action.u 2 1 = 1)
    (hU22 : Z.τ.action.u 2 2 = 0)
    (hR20 : Z.τ.action.ρ 2 0 = 0)
    (hR21 : Z.τ.action.ρ 2 1 = 1) (hR22 : Z.τ.action.ρ 2 2 = -1)
    (hV10 : Z.τ.action.uv 1 0 = -4)
    (hV11 : Z.τ.action.uv 1 1 = 1)
    (hUeq : w' = matAct Z.τ.k Z.τ.action.u Z.τ.action.compat_u w)
    (hReq : w' = matAct Z.τ.k Z.τ.action.ρ Z.τ.action.compat_ρ w)
    (hVeq : matAct Z.τ.k Z.τ.action.uv Z.τ.action.compat_uv w = w)
    (hne : w ≠ 0) :
    w = (2 : ℤ) ^ (Z.τ.m + 1) • (Torus.a : Torus Z.τ.k) ∧
      w' = (2 : ℤ) ^ (Z.τ.m + 1) • (Torus.b : Torus Z.τ.k) := by
  classical
  have hm2 : 2 ≤ Z.τ.m := by simpa [StrothTypeIndex.m] using hk 0
  have hm1 : 1 ≤ Z.τ.m := by omega
  have hk1all : ∀ i, 1 ≤ Z.τ.k i := fun i => by have := hk i; omega
  obtain ⟨ε, hε, hwε0⟩ := (Torus.two_zsmul_eq_zero_iff hk1all w).mp hw2
  obtain ⟨ε', hε', hw'ε0⟩ := (Torus.two_zsmul_eq_zero_iff hk1all w').mp hw2'
  set v : Fin 3 → ℤ := fun i => ε i * 2 ^ (Z.τ.k i - 1) with hv
  set v' : Fin 3 → ℤ := fun i => ε' i * 2 ^ (Z.τ.k i - 1) with hv'
  have hwε : w = Torus.ofInt Z.τ.k v := by simpa [v] using hwε0
  have hw'ε : w' = Torus.ofInt Z.τ.k v' := by simpa [v'] using hw'ε0
  have hk0 : Z.τ.k 0 = Z.τ.m := rfl
  have hk1 : Z.τ.k 1 = Z.τ.m + 2 := by
    rw [StrothTypeIndex.k_eq]; simp [hrel]
  have hk2 : Z.τ.k 2 = Z.τ.m + 2 := by
    rw [StrothTypeIndex.k_two, hrel]
  have hu_int : Torus.ofInt Z.τ.k v' = Torus.ofInt Z.τ.k (Z.τ.action.u *ᵥ v) := by
    rw [← matAct_ofInt, ← hw'ε, ← hwε]
    exact hUeq
  have hu0 : ε' 0 = ε 0 := by
    have h := (Torus.ofInt_eq_ofInt_iff.mp hu_int) 0
    have h' : ε' 0 * 2 ^ (Z.τ.m - 1) ≡ ε 0 * 2 ^ (Z.τ.m - 1) [ZMOD 2 ^ Z.τ.m] := by
      simpa [v, v', hk0, hU00, hU01, hU02, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three] using h
    exact int_eq_of_modEq_two (hε' 0) (hε 0)
      (int_modEq_two_of_mul_two_pow_pred_modEq hm1 h')
  have hu1 : ε' 1 = ε 2 := by
    have h := (Torus.ofInt_eq_ofInt_iff.mp hu_int) 1
    have h' : ε' 1 * 2 ^ (Z.τ.m + 1) ≡ ε 2 * 2 ^ (Z.τ.m + 1)
        [ZMOD 2 ^ (Z.τ.m + 2)] := by
      simpa [v, v', hk1, hk2, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        hU10, hU11, hU12, Nat.add_sub_cancel] using h
    exact int_eq_of_modEq_two (hε' 1) (hε 2) (int_modEq_two_of_mul_two_pow_modEq h')
  have hu2 : ε' 2 = ε 1 := by
    have h := (Torus.ofInt_eq_ofInt_iff.mp hu_int) 2
    have h' : ε' 2 * 2 ^ (Z.τ.m + 1) ≡ ε 1 * 2 ^ (Z.τ.m + 1)
        [ZMOD 2 ^ (Z.τ.m + 2)] := by
      simpa [v, v', hk1, hk2, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        hU20, hU21, hU22, Nat.add_sub_cancel] using h
    exact int_eq_of_modEq_two (hε' 2) (hε 1) (int_modEq_two_of_mul_two_pow_modEq h')
  have hr_int : Torus.ofInt Z.τ.k v' = Torus.ofInt Z.τ.k (Z.τ.action.ρ *ᵥ v) := by
    rw [← matAct_ofInt, ← hw'ε, ← hwε]
    exact hReq
  have hr2 : ε' 2 ≡ ε 1 - ε 2 [ZMOD 2] := by
    have h := (Torus.ofInt_eq_ofInt_iff.mp hr_int) 2
    have h' : ε' 2 * 2 ^ (Z.τ.m + 1) ≡
        ε 1 * 2 ^ (Z.τ.m + 1) + -(ε 2 * 2 ^ (Z.τ.m + 1))
          [ZMOD 2 ^ (Z.τ.m + 2)] := by
      simpa [v, v', hk1, hk2, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        hR20, hR21, hR22, Nat.add_sub_cancel] using h
    have h'' : ε' 2 * 2 ^ (Z.τ.m + 1) ≡ (ε 1 - ε 2) * 2 ^ (Z.τ.m + 1)
        [ZMOD 2 ^ (Z.τ.m + 2)] := by
      rwa [show ε 1 * 2 ^ (Z.τ.m + 1) + -(ε 2 * 2 ^ (Z.τ.m + 1)) =
        (ε 1 - ε 2) * 2 ^ (Z.τ.m + 1) by ring] at h'
    exact int_modEq_two_of_mul_two_pow_modEq h''
  have hε2 : ε 2 = 0 := by
    have h' : ε 1 ≡ ε 1 - ε 2 [ZMOD 2] := by simpa [hu2] using hr2
    have hdvd : (2 : ℤ) ∣ 0 - ε 2 := by
      have := Int.modEq_iff_dvd.mp h'
      simpa using this
    exact int_eq_zero_of_modEq_two (hε 2) (Int.modEq_iff_dvd.mpr hdvd)
  have hv_int : Torus.ofInt Z.τ.k v = Torus.ofInt Z.τ.k (Z.τ.action.uv *ᵥ v) := by
    rw [← matAct_ofInt, ← hwε]
    exact hVeq.symm
  have hε0 : ε 0 = 0 := by
    have h := (Torus.ofInt_eq_ofInt_iff.mp hv_int) 1
    have h' : ε 1 * 2 ^ (Z.τ.m + 1) ≡
        (-4) * (ε 0 * 2 ^ (Z.τ.m - 1)) + (1) * (ε 1 * 2 ^ (Z.τ.m + 1))
          [ZMOD 2 ^ (Z.τ.m + 2)] := by
      simpa [v, hk0, hk1, hk2, hε2, hV10, hV11, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Nat.add_sub_cancel] using h
    have h'' : ε 1 * 2 ^ (Z.τ.m + 1) ≡ (ε 1 - ε 0) * 2 ^ (Z.τ.m + 1)
        [ZMOD 2 ^ (Z.τ.m + 2)] := by
      have h3 : (-4) * (ε 0 * 2 ^ (Z.τ.m - 1)) + (1) * (ε 1 * 2 ^ (Z.τ.m + 1)) =
          (ε 1 - ε 0) * 2 ^ (Z.τ.m + 1) := by
        have hp : (2 : ℤ) ^ (Z.τ.m + 1) = 4 * 2 ^ (Z.τ.m - 1) := by
          rw [show Z.τ.m + 1 = (Z.τ.m - 1) + 2 by omega, pow_add]; ring
        rw [hp]; ring
      rwa [h3] at h'
    have hmod : ε 1 ≡ ε 1 - ε 0 [ZMOD 2] :=
      int_modEq_two_of_mul_two_pow_modEq h''
    have hdvd : (2 : ℤ) ∣ ε 0 := by
      have := Int.modEq_iff_dvd.mp hmod
      simpa using this
    exact int_eq_zero_of_modEq_two (hε 0) (Int.modEq_zero_iff_dvd.mpr hdvd)
  have hε'0 : ε' 0 = 0 := by rw [hu0, hε0]
  have hε1 : ε 1 = 1 := by
    rcases hε 1 with h0 | h1
    · exfalso
      apply hne
      rw [hwε]
      have hvec : v = 0 := by
        funext i
        fin_cases i <;> simp [v, hε0, h0, hε2]
      rw [hvec]
      simp
    · exact h1
  have ha_ofInt : (Torus.a : Torus Z.τ.k) = Torus.ofInt Z.τ.k ![0, 1, 0] := by
    funext i
    fin_cases i <;> simp [Torus.a, gen, Torus.ofInt_apply, Fin.isValue]
  have hb_ofInt : (Torus.b : Torus Z.τ.k) = Torus.ofInt Z.τ.k ![0, 0, 1] := by
    funext i
    fin_cases i <;> simp [Torus.b, gen, Torus.ofInt_apply, Fin.isValue]
  have hv_eq : v = (2 : ℤ) ^ (Z.τ.m + 1) • (![0, 1, 0] : Fin 3 → ℤ) := by
    funext i
    fin_cases i <;>
      simp [v, hk1, hk2, hε0, hε1, hε2, Nat.add_sub_cancel]
  have hv'_eq : v' = (2 : ℤ) ^ (Z.τ.m + 1) • (![0, 0, 1] : Fin 3 → ℤ) := by
    funext i
    fin_cases i <;>
      simp [v', hk1, hk2, hε'0, hu1, hu2, hε2, hε1, Nat.add_sub_cancel]
  constructor
  · calc w = Torus.ofInt Z.τ.k v := hwε
      _ = Torus.ofInt Z.τ.k ((2 : ℤ) ^ (Z.τ.m + 1) • (![0, 1, 0] : Fin 3 → ℤ)) := by
          rw [hv_eq]
      _ = (2 : ℤ) ^ (Z.τ.m + 1) • Torus.ofInt Z.τ.k (![0, 1, 0] : Fin 3 → ℤ) :=
          Torus.ofInt_zsmul _ _
      _ = (2 : ℤ) ^ (Z.τ.m + 1) • (Torus.a : Torus Z.τ.k) := by rw [← ha_ofInt]
  · calc w' = Torus.ofInt Z.τ.k v' := hw'ε
      _ = Torus.ofInt Z.τ.k ((2 : ℤ) ^ (Z.τ.m + 1) • (![0, 0, 1] : Fin 3 → ℤ)) := by
          rw [hv'_eq]
      _ = (2 : ℤ) ^ (Z.τ.m + 1) • Torus.ofInt Z.τ.k (![0, 0, 1] : Fin 3 → ℤ) :=
          Torus.ofInt_zsmul _ _
      _ = (2 : ℤ) ^ (Z.τ.m + 1) • (Torus.b : Torus Z.τ.k) := by rw [← hb_ofInt]

theorem commute_of_deviationTorus_eq_zero (Z : StrothDatum X) {s x : G}
    (hs : s ∈ Z.centralizerInMho) (hx : x ∈ Z.D)
    (h : deviationTorus Z s hs (Additive.ofMul ⟨x, hx⟩) = 0) : x * s = s * x := by
  rw [deviationTorus_apply] at h
  have h1 : ((deviation Z s hs (Additive.ofMul ⟨x, hx⟩)).toMul : G) = 1 := by
    have h' : Z.dataD.e (Additive.ofMul ⟨((deviation Z s hs
        (Additive.ofMul ⟨x, hx⟩)).toMul : G), omegaIn_le 1 Z.D
          (deviation Z s hs (Additive.ofMul ⟨x, hx⟩)).toMul.2⟩) =
        Z.dataD.e (Additive.ofMul (1 : Z.D)) := by
      rw [h]
      simp
    have hx' := Additive.ofMul.injective (Z.dataD.e.injective h')
    simpa using congrArg Subtype.val hx'
  have h2 : s * x * s⁻¹ * x⁻¹ = 1 := by
    simpa [deviation_apply] using h1
  have h3 : s * x * s⁻¹ = x := by
    have := congrArg (· * x) h2
    simpa [mul_assoc] using this
  have h4 : s * x = x * s := by
    have := congrArg (· * s) h3
    simpa [mul_assoc] using this
  exact h4.symm

theorem deviation_form_diag_familyTwo (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D)
    (hU00 : Z.τ.action.u 0 0 = 1) (hU01 : Z.τ.action.u 0 1 = 0)
    (hU02 : Z.τ.action.u 0 2 = 0)
    (hU10 : Z.τ.action.u 1 0 = 0) (hU11 : Z.τ.action.u 1 1 = 0)
    (hU12 : Z.τ.action.u 1 2 = 1)
    (hU20 : Z.τ.action.u 2 0 = 0) (hU21 : Z.τ.action.u 2 1 = 1)
    (hU22 : Z.τ.action.u 2 2 = 0)
    (hR01 : Z.τ.action.ρ 0 1 = 0) (hR11 : Z.τ.action.ρ 1 1 = 0)
    (hR20 : Z.τ.action.ρ 2 0 = 0)
    (hR21 : Z.τ.action.ρ 2 1 = 1) (hR22 : Z.τ.action.ρ 2 2 = -1)
    (hV10 : Z.τ.action.uv 1 0 = -4)
    (hV11 : Z.τ.action.uv 1 1 = 1)
    (huv2 : Even (Z.τ.action.uv 2 1)) :
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1 ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)) ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1)) ∧
    (∀ d : Z.D, ((deviation Z s (hF hsF) (Additive.ofMul (d * d))).toMul : G) = 1) := by
  classical
  have hm2 : 2 ≤ Z.τ.m := by simpa [StrothTypeIndex.m] using hk 0
  have hs : s ∈ Z.centralizerInMho := hF hsF
  have hc_mem : (Z.dataD.c : G) ∈ omegaIn (Z.τ.n - 2) Z.D := by
    refine mem_omegaIn_of_pow_eq_one Z.dataD.c.2 ?_
    have hn : Z.τ.n - 2 = Z.τ.m := by omega
    rw [hn, ← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_coe, Z.dataD.orderOf_c]
  have hcs : s * (Z.dataD.c : G) = (Z.dataD.c : G) * s :=
    (Subgroup.mem_centralizer_iff.mp (hcent hsF) _ hc_mem).symm
  have hφc : ((deviation Z s (hF hsF)
      (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1 := by
    rw [deviation_apply]
    calc s * (Z.dataD.c : G) * s⁻¹ * (Z.dataD.c : G)⁻¹
        = (Z.dataD.c : G) * s * s⁻¹ * (Z.dataD.c : G)⁻¹ := by rw [hcs]
      _ = 1 := by group
  have hΦc0 : deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩) = 0 := by
    rw [deviationTorus_apply]
    have h1 : (⟨((deviation Z s hs (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G),
        omegaIn_le 1 Z.D (deviation Z s hs
          (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul.2⟩ : Z.D) = 1 :=
      Subtype.ext hφc
    rw [h1]
    simp
  have huL : Z.dataD.u ∈ X.L := Z.hL ▸ Z.dataD.u_mem_L
  have huvL : Z.dataD.uv ∈ X.L := Z.hL ▸ Z.dataD.uv_mem_L
  have hρL : Z.dataD.ρ ∈ X.L := Z.hL ▸ Z.dataD.ρ_mem_L
  obtain ⟨du, hduD, hdu⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z F hF hN hidx hsF hsD huL
  obtain ⟨duv, hduvD, hduv⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z F hF hN hidx hsF hsD huvL
  obtain ⟨dr, hdrD, hdr⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z F hF hN hidx hsF hsD
      (X.L.inv_mem hρL)
  have huinv : (Z.dataD.u)⁻¹ = Z.dataD.u := inv_eq_of_mul_eq_one_right Z.dataD.u_sq
  have huvinv : (Z.dataD.uv)⁻¹ = Z.dataD.uv :=
    inv_eq_of_mul_eq_one_right Z.dataD.uv_sq
  have hdu' : Z.dataD.u * s * (Z.dataD.u)⁻¹ = s * du := by
    simpa [huinv] using hdu
  have hduv' : Z.dataD.uv * s * (Z.dataD.uv)⁻¹ = s * duv := by
    simpa [huvinv] using hduv
  have hdr' : Z.dataD.ρ * s * (Z.dataD.ρ)⁻¹ = s * dr := by
    simpa using hdr
  have hcolU : matAct Z.τ.k Z.τ.action.u Z.τ.action.compat_u
      (Torus.a : Torus Z.τ.k) =
      (Z.τ.action.u 0 1) • (Torus.c : Torus Z.τ.k) +
        (Z.τ.action.u 1 1) • (Torus.a : Torus Z.τ.k) +
          (Z.τ.action.u 2 1) • (Torus.b : Torus Z.τ.k) := by
    rw [show (Torus.a : Torus Z.τ.k) = gen Z.τ.k 1 from rfl, matAct_gen_eq]
  have hcolR : matAct Z.τ.k Z.τ.action.ρ Z.τ.action.compat_ρ
      (Torus.a : Torus Z.τ.k) =
      (Z.τ.action.ρ 0 1) • (Torus.c : Torus Z.τ.k) +
        (Z.τ.action.ρ 1 1) • (Torus.a : Torus Z.τ.k) +
          (Z.τ.action.ρ 2 1) • (Torus.b : Torus Z.τ.k) := by
    rw [show (Torus.a : Torus Z.τ.k) = gen Z.τ.k 1 from rfl, matAct_gen_eq]
  have hcolV : matAct Z.τ.k Z.τ.action.uv Z.τ.action.compat_uv
      (Torus.a : Torus Z.τ.k) =
      (Z.τ.action.uv 0 1) • (Torus.c : Torus Z.τ.k) +
        (Z.τ.action.uv 1 1) • (Torus.a : Torus Z.τ.k) +
          (Z.τ.action.uv 2 1) • (Torus.b : Torus Z.τ.k) := by
    rw [show (Torus.a : Torus Z.τ.k) = gen Z.τ.k 1 from rfl, matAct_gen_eq]
  have hua : conjBy Z.dataD.u_mem (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) =
      ⟨Z.dataD.b, Z.dataD.b.2⟩ := by
    have h := Z.dataD.u_conj (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D)
    rw [Z.dataD.e_a] at h
    rw [show Z.τ.action.φu (Torus.a : Torus Z.τ.k) =
        (Z.τ.action.u 0 1) • Torus.c + (Z.τ.action.u 1 1) • Torus.a +
          (Z.τ.action.u 2 1) • Torus.b from hcolU] at h
    rw [hU01, hU11, hU21] at h
    simp only [zero_zsmul, zero_add, one_zsmul] at h
    rw [← Z.dataD.e_b] at h
    exact Additive.ofMul.injective (Z.dataD.e.injective h)
  have hρa : conjBy Z.dataD.ρ_mem (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) =
      ⟨Z.dataD.b, Z.dataD.b.2⟩ := by
    have h := Z.dataD.ρ_conj (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D)
    rw [Z.dataD.e_a] at h
    rw [show Z.τ.action.φρ (Torus.a : Torus Z.τ.k) =
        (Z.τ.action.ρ 0 1) • Torus.c + (Z.τ.action.ρ 1 1) • Torus.a +
          (Z.τ.action.ρ 2 1) • Torus.b from hcolR] at h
    rw [hR01, hR11, hR21] at h
    simp only [zero_zsmul, zero_add, one_zsmul] at h
    rw [← Z.dataD.e_b] at h
    exact Additive.ofMul.injective (Z.dataD.e.injective h)
  have huva : conjBy Z.dataD.uv_mem (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) =
      (⟨Z.dataD.c, Z.dataD.c.2⟩ : Z.D) ^ (Z.τ.action.uv 0 1) *
        (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) ^ (Z.τ.action.uv 1 1) *
          (⟨Z.dataD.b, Z.dataD.b.2⟩ : Z.D) ^ (Z.τ.action.uv 2 1) := by
    have h := Z.dataD.uv_conj (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D)
    rw [Z.dataD.e_a] at h
    rw [show Z.τ.action.φuv (Torus.a : Torus Z.τ.k) =
        (Z.τ.action.uv 0 1) • Torus.c + (Z.τ.action.uv 1 1) • Torus.a +
          (Z.τ.action.uv 2 1) • Torus.b from hcolV] at h
    apply Additive.ofMul.injective
    apply Z.dataD.e.injective
    rw [h, ofMul_mul, ofMul_mul, ofMul_zpow, ofMul_zpow, ofMul_zpow,
      map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
      Z.dataD.e_c, Z.dataD.e_a, Z.dataD.e_b]
  have hdev_u : deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩) =
      matAct Z.τ.k Z.τ.action.u Z.τ.action.compat_u
        (deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)) := by
    have h := deviationTorus_conj_eq Z hs hduD Z.dataD.u_mem hdu'
      (M := Z.τ.action.u) (hM := Z.τ.action.compat_u) (hmat := Z.dataD.u_conj)
      (x := Z.dataD.a) Z.dataD.a.2
    rw [hua] at h
    exact h
  have hdev_r : deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩) =
      matAct Z.τ.k Z.τ.action.ρ Z.τ.action.compat_ρ
        (deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)) := by
    have h := deviationTorus_conj_eq Z hs hdrD Z.dataD.ρ_mem hdr'
      (M := Z.τ.action.ρ) (hM := Z.τ.action.compat_ρ) (hmat := Z.dataD.ρ_conj)
      (x := Z.dataD.a) Z.dataD.a.2
    rw [hρa] at h
    exact h
  have hdev_uv : matAct Z.τ.k Z.τ.action.uv Z.τ.action.compat_uv
      (deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)) =
      deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩) := by
    have h := deviationTorus_conj_eq Z hs hduvD Z.dataD.uv_mem hduv'
      (M := Z.τ.action.uv) (hM := Z.τ.action.compat_uv) (hmat := Z.dataD.uv_conj)
      (x := Z.dataD.a) Z.dataD.a.2
    rw [huva] at h
    have hcalc : deviationTorus Z s hs (Additive.ofMul
        ((⟨Z.dataD.c, Z.dataD.c.2⟩ : Z.D) ^ (Z.τ.action.uv 0 1) *
          (⟨Z.dataD.a, Z.dataD.a.2⟩ : Z.D) ^ (Z.τ.action.uv 1 1) *
            (⟨Z.dataD.b, Z.dataD.b.2⟩ : Z.D) ^ (Z.τ.action.uv 2 1))) =
        deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩) := by
      rw [ofMul_mul, ofMul_mul, ofMul_zpow, ofMul_zpow, ofMul_zpow,
        map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hΦc0, smul_zero, zero_add]
      have hw2 : (2 : ℤ) • deviationTorus Z s hs
          (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩) = 0 :=
        deviationTorus_two_zsmul Z s hs _
      have hw2' : (2 : ℤ) • deviationTorus Z s hs
          (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩) = 0 :=
        deviationTorus_two_zsmul Z s hs _
      have hodd : ∀ {z : ℤ}, Odd z → ∀ {x : Torus Z.τ.k}, (2 : ℤ) • x = 0 → z • x = x := by
        intro z hz x hx
        obtain ⟨r, rfl⟩ := hz
        rw [add_zsmul, mul_zsmul', hx, smul_zero, zero_add, one_zsmul]
      have heven : ∀ {z : ℤ}, Even z → ∀ {x : Torus Z.τ.k}, (2 : ℤ) • x = 0 → z • x = 0 := by
        intro z hz x hx
        obtain ⟨r, rfl⟩ := hz
        rw [show r + r = 2 * r by ring, mul_zsmul', hx, smul_zero]
      rw [hodd (by rw [hV11]; norm_num) hw2, heven huv2 hw2', add_zero]
    rw [hcalc] at h
    exact h.symm
  have hne : deviationTorus Z s hs
      (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩) ≠ 0 := by
    intro hw0
    apply hsD
    have hΦa0 : deviationTorus Z s hs
        (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩) = 0 := hw0
    have hΦb0 : deviationTorus Z s hs
        (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩) = 0 := by
      rw [hdev_u, hΦa0, map_zero]
    have hΦall : ∀ x : Z.D, deviationTorus Z s hs (Additive.ofMul x) = 0 := by
      intro x
      obtain ⟨W, hW⟩ := Torus.exists_ofInt (Z.dataD.e (Additive.ofMul x))
      have hdec : Additive.ofMul x =
          Z.dataD.e.symm (W 0 • (Torus.c : Torus Z.τ.k) +
            W 1 • (Torus.a : Torus Z.τ.k) + W 2 • (Torus.b : Torus Z.τ.k)) := by
        apply Z.dataD.e.injective
        rw [AddEquiv.apply_symm_apply, ← hW, Torus.ofInt_eq_zsmul_gens]
      have hc' : Z.dataD.e.symm (Torus.c : Torus Z.τ.k) =
          Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩ := by
        rw [← Z.dataD.e_c, AddEquiv.symm_apply_apply]
      have ha' : Z.dataD.e.symm (Torus.a : Torus Z.τ.k) =
          Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩ := by
        rw [← Z.dataD.e_a, AddEquiv.symm_apply_apply]
      have hb' : Z.dataD.e.symm (Torus.b : Torus Z.τ.k) =
          Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩ := by
        rw [← Z.dataD.e_b, AddEquiv.symm_apply_apply]
      rw [hdec]
      simp only [map_add, map_zsmul, hc', ha', hb', hΦc0, hΦa0, hΦb0, smul_zero, add_zero]
    apply Z.mem_of_mem_centralizer (hF hsF).1.1
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact commute_of_deviationTorus_eq_zero Z hs hx (hΦall ⟨x, hx⟩)
  have hw2a : (2 : ℤ) • deviationTorus Z s hs
      (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩) = 0 := deviationTorus_two_zsmul Z s hs _
  have hw2b : (2 : ℤ) • deviationTorus Z s hs
      (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩) = 0 := deviationTorus_two_zsmul Z s hs _
  obtain ⟨hwval, hw'val⟩ :=
    two_torsion_solution_familyTwo Z hk hrel _ _ hw2a hw2b
      hU00 hU01 hU02 hU10 hU11 hU12 hU20 hU21 hU22 hR20 hR21 hR22 hV10 hV11
      hdev_u hdev_r hdev_uv hne
  have hφa : ((deviation Z s (hF hsF)
      (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)) := by
    have h : deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩) =
        (2 : ℤ) ^ (Z.τ.m + 1) • (Torus.a : Torus Z.τ.k) := hwval
    rw [deviationTorus_apply] at h
    have h2 : Z.dataD.e (Additive.ofMul (Z.dataD.a ^ (2 ^ (Z.τ.m + 1)))) =
        ((2 : ℕ) ^ (Z.τ.m + 1)) • (Torus.a : Torus Z.τ.k) := by
      rw [Z.dataD.e_pow, Z.dataD.e_a]
    have h' : Z.dataD.e (Additive.ofMul ⟨((deviation Z s (hF hsF)
        (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G), omegaIn_le 1 Z.D
          (deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a,
            Z.dataD.a.2⟩)).toMul.2⟩) =
        Z.dataD.e (Additive.ofMul (Z.dataD.a ^ (2 ^ (Z.τ.m + 1)))) := by
      rw [h, h2, show (2 : ℤ) ^ (Z.τ.m + 1) = ((2 ^ (Z.τ.m + 1) : ℕ) : ℤ) by
        push_cast; ring, natCast_zsmul]
    have hx := Additive.ofMul.injective (Z.dataD.e.injective h')
    simpa using congrArg Subtype.val hx
  have hφb : ((deviation Z s (hF hsF)
      (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1)) := by
    have h : deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩) =
        (2 : ℤ) ^ (Z.τ.m + 1) • (Torus.b : Torus Z.τ.k) := hw'val
    rw [deviationTorus_apply] at h
    have h2 : Z.dataD.e (Additive.ofMul (Z.dataD.b ^ (2 ^ (Z.τ.m + 1)))) =
        ((2 : ℕ) ^ (Z.τ.m + 1)) • (Torus.b : Torus Z.τ.k) := by
      rw [Z.dataD.e_pow, Z.dataD.e_b]
    have h' : Z.dataD.e (Additive.ofMul ⟨((deviation Z s (hF hsF)
        (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G), omegaIn_le 1 Z.D
          (deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b,
            Z.dataD.b.2⟩)).toMul.2⟩) =
        Z.dataD.e (Additive.ofMul (Z.dataD.b ^ (2 ^ (Z.τ.m + 1)))) := by
      rw [h, h2, show (2 : ℤ) ^ (Z.τ.m + 1) = ((2 ^ (Z.τ.m + 1) : ℕ) : ℤ) by
        push_cast; ring, natCast_zsmul]
    have hx := Additive.ofMul.injective (Z.dataD.e.injective h')
    simpa using congrArg Subtype.val hx
  exact ⟨hφc, hφa, hφb, fun d => deviation_sq_mem Z s (hF hsF) d⟩

theorem deviationTorus_generators_eq_familyTwo (Z : StrothDatum X)
    (F : Subgroup G) (hF : F ≤ Z.centralizerInMho) {s : G} (hsF : s ∈ F)
    (hφc : ((deviation Z s (hF hsF)
      (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1)
    (hφa : ((deviation Z s (hF hsF)
      (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)))
    (hφb : ((deviation Z s (hF hsF)
      (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1))) :
    deviationTorus Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩) = 0 ∧
    deviationTorus Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩) =
      (2 : ℤ) ^ (Z.τ.m + 1) • (Torus.a : Torus Z.τ.k) ∧
    deviationTorus Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩) =
      (2 : ℤ) ^ (Z.τ.m + 1) • (Torus.b : Torus Z.τ.k) := by
  have hs : s ∈ Z.centralizerInMho := hF hsF
  refine ⟨?_, ?_, ?_⟩
  · rw [deviationTorus_apply]
    have h1 : (⟨((deviation Z s hs (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G),
        omegaIn_le 1 Z.D (deviation Z s hs
          (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul.2⟩ : Z.D) = 1 :=
      Subtype.ext hφc
    rw [h1]
    simp
  · rw [deviationTorus_apply]
    have h1 : (⟨((deviation Z s hs (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G),
        omegaIn_le 1 Z.D (deviation Z s hs
          (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul.2⟩ : Z.D) =
        Z.dataD.a ^ (2 ^ (Z.τ.m + 1)) := Subtype.ext hφa
    rw [h1, Z.dataD.e_pow, Z.dataD.e_a]
    rw [show ((2 : ℕ) ^ (Z.τ.m + 1)) • (Torus.a : Torus Z.τ.k) =
        ((2 : ℤ) ^ (Z.τ.m + 1)) • Torus.a from by
      rw [← natCast_zsmul]
      norm_num]
  · rw [deviationTorus_apply]
    have h1 : (⟨((deviation Z s hs (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G),
        omegaIn_le 1 Z.D (deviation Z s hs
          (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul.2⟩ : Z.D) =
        Z.dataD.b ^ (2 ^ (Z.τ.m + 1)) := Subtype.ext hφb
    rw [h1, Z.dataD.e_pow, Z.dataD.e_b]
    rw [show ((2 : ℕ) ^ (Z.τ.m + 1)) • (Torus.b : Torus Z.τ.k) =
        ((2 : ℤ) ^ (Z.τ.m + 1)) • Torus.b from by
      rw [← natCast_zsmul]
      norm_num]

theorem deviation_form_diag_familyTwo_t200 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) {m : ℕ}
    (hτ : Z.τ = StrothTypeIndex.t200 m)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1 ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)) ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1)) ∧
    (∀ d : Z.D, ((deviation Z s (hF hsF) (Additive.ofMul (d * d))).toMul : G) = 1) := by
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  set Z' : StrothDatum X :=
    ⟨D, hAD, hDS, StrothTypeIndex.t200 m, dataD, hL, hcentS⟩ with hZ'
  exact deviation_form_diag_familyTwo Z' hk hrel F hDF hF hN hidx hcent hsF hsD
    (by simp [Z', StrothTypeIndex.action, Type200.action, Type200.uM, Type200.uvM, Type200.uvA, Type200.tM, Type200.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type200.action, Type200.uM, Type200.uvM, Type200.uvA, Type200.tM, Type200.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type200.action, Type200.uM, Type200.uvM, Type200.uvA, Type200.tM, Type200.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type200.action, Type200.uM, Type200.uvM, Type200.uvA, Type200.tM, Type200.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type200.action, Type200.uM, Type200.uvM, Type200.uvA, Type200.tM, Type200.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type200.action, Type200.uM, Type200.uvM, Type200.uvA, Type200.tM, Type200.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type200.action, Type200.uM, Type200.uvM, Type200.uvA, Type200.tM, Type200.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type200.action, Type200.uM, Type200.uvM, Type200.uvA, Type200.tM, Type200.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type200.action, Type200.uM, Type200.uvM, Type200.uvA, Type200.tM, Type200.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type200.action, Type200.uM, Type200.uvM, Type200.uvA, Type200.tM, Type200.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type200.action, Type200.uM, Type200.uvM, Type200.uvA, Type200.tM, Type200.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type200.action, Type200.uM, Type200.uvM, Type200.uvA, Type200.tM, Type200.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type200.action, Type200.uM, Type200.uvM, Type200.uvA, Type200.tM, Type200.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type200.action, Type200.uM, Type200.uvM, Type200.uvA, Type200.tM, Type200.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type200.action, Type200.uM, Type200.uvM, Type200.uvA, Type200.tM, Type200.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type200.action, Type200.uM, Type200.uvM, Type200.uvA, Type200.tM, Type200.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by
      have h : Z'.τ.action.uv 2 1 = 2 := by
        simp [Z', StrothTypeIndex.action, Type200.action, SigmaFourAction.ofMatEq, Type200.uvM, Type200.uvA, ofCols_apply]
      rw [h]
      norm_num)

theorem deviation_form_diag_familyTwo_t201 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) {m : ℕ}
    (hτ : Z.τ = StrothTypeIndex.t201 m)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1 ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
      (Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)) ∧
    ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
      (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1)) ∧
    (∀ d : Z.D, ((deviation Z s (hF hsF) (Additive.ofMul (d * d))).toMul : G) = 1) := by
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  set Z' : StrothDatum X :=
    ⟨D, hAD, hDS, StrothTypeIndex.t201 m, dataD, hL, hcentS⟩ with hZ'
  exact deviation_form_diag_familyTwo Z' hk hrel F hDF hF hN hidx hcent hsF hsD
    (by simp [Z', StrothTypeIndex.action, Type201.action, Type201.uM, Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type201.action, Type201.uM, Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type201.action, Type201.uM, Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type201.action, Type201.uM, Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type201.action, Type201.uM, Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type201.action, Type201.uM, Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type201.action, Type201.uM, Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type201.action, Type201.uM, Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type201.action, Type201.uM, Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type201.action, Type201.uM, Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type201.action, Type201.uM, Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type201.action, Type201.uM, Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by simp [Z', StrothTypeIndex.action, Type201.action, Type201.uM, Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type201.action, Type201.uM, Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type201.action, Type201.uM, Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq]) (by simp [Z', StrothTypeIndex.action, Type201.action, Type201.uM, Type201.uvM, Type201.uvA, Type201.tM, Type201.ρM, uMat, ofCols_apply, SigmaFourAction.ofMatEq])
    (by
      have h : Z'.τ.action.uv 2 1 = 2 + 2 ^ (m + 1) := by
        simp [Z', StrothTypeIndex.action, Type201.action, SigmaFourAction.ofMatEq, Type201.uvM, Type201.uvA, ofCols_apply]
      rw [h]
      exact ⟨1 + 2 ^ m, by
        rw [show (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m by rw [pow_succ]; ring]
        ring⟩)

theorem thetaD_torus_eq_familyTwo_t200 (Z : StrothDatum X) {m : ℕ}
    (hτ : Z.τ = StrothTypeIndex.t200 m)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    ∀ d : Z.D,
      Z.dataD.e (Additive.ofMul (thetaD Z s (hF hsF) d)) =
        thetaTwoType Z.τ (Z.dataD.e (Additive.ofMul d)) := by
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  set Z' : StrothDatum X :=
    ⟨D, hAD, hDS, StrothTypeIndex.t200 m, dataD, hL, hcentS⟩ with hZ'
  obtain ⟨hφc, hφa, hφb, -⟩ :=
    deviation_form_diag_familyTwo_t200 Z' hk hrel (m := m) rfl F hDF hF hN hidx hcent hsF hsD
  have hs : s ∈ Z'.centralizerInMho := hF hsF
  obtain ⟨hΦc, hΦa, hΦb⟩ :=
    deviationTorus_generators_eq_familyTwo Z' F hF hsF hφc hφa hφb
  intro d
  obtain ⟨i, j, l, hd⟩ := ofMul_eq_gens_zsmul Z' d
  have hV : Z'.dataD.e (Additive.ofMul d) =
      i • (Torus.c : Torus Z'.τ.k) + j • (Torus.a : Torus Z'.τ.k) +
        l • (Torus.b : Torus Z'.τ.k) := by
    rw [hd, map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
      Z'.dataD.e_c, Z'.dataD.e_a, Z'.dataD.e_b]
  have hΦd : deviationTorus Z' s hs (Additive.ofMul d) =
      j • ((2 : ℤ) ^ (Z'.τ.m + 1) • (Torus.a : Torus Z'.τ.k)) +
        l • ((2 : ℤ) ^ (Z'.τ.m + 1) • (Torus.b : Torus Z'.τ.k)) := by
    rw [hd, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hΦc, hΦa, hΦb]
    simp
  have hLHS : Z'.dataD.e (Additive.ofMul (thetaD Z' s hs d)) =
      (2 : ℤ) • Z'.dataD.e (Additive.ofMul d) + deviationTorus Z' s hs (Additive.ofMul d) :=
    thetaD_additive_torus Z' s hs d
  rw [hLHS, hV, hΦd]
  have hRHS : thetaTwoType Z'.τ (i • (Torus.c : Torus Z'.τ.k) +
      j • (Torus.a : Torus Z'.τ.k) + l • (Torus.b : Torus Z'.τ.k)) =
      i • ((2 : ℤ) • (Torus.c : Torus Z'.τ.k)) +
        j • ((2 + (2 : ℤ) ^ (Z'.τ.m + 1)) • (Torus.a : Torus Z'.τ.k)) +
        l • ((2 + (2 : ℤ) ^ (Z'.τ.m + 1)) • (Torus.b : Torus Z'.τ.k)) := by
    have hc : thetaTwoType Z'.τ (Torus.c : Torus Z'.τ.k) = (2 : ℤ) • Torus.c :=
      thetaTwo_c m
    have ha : thetaTwoType Z'.τ (Torus.a : Torus Z'.τ.k) =
        (2 + (2 : ℤ) ^ (Z'.τ.m + 1)) • Torus.a :=
      thetaTwo_a m
    have hb : thetaTwoType Z'.τ (Torus.b : Torus Z'.τ.k) =
        (2 + (2 : ℤ) ^ (Z'.τ.m + 1)) • Torus.b :=
      thetaTwo_b m
    rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hc, ha, hb]
  rw [hRHS]
  module

theorem thetaD_torus_eq_familyTwo_t201 (Z : StrothDatum X) {m : ℕ}
    (hτ : Z.τ = StrothTypeIndex.t201 m)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G))
    {s : G} (hsF : s ∈ F) (hsD : s ∉ Z.D) :
    ∀ d : Z.D,
      Z.dataD.e (Additive.ofMul (thetaD Z s (hF hsF) d)) =
        thetaTwoType Z.τ (Z.dataD.e (Additive.ofMul d)) := by
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  set Z' : StrothDatum X :=
    ⟨D, hAD, hDS, StrothTypeIndex.t201 m, dataD, hL, hcentS⟩ with hZ'
  obtain ⟨hφc, hφa, hφb, -⟩ :=
    deviation_form_diag_familyTwo_t201 Z' hk hrel (m := m) rfl F hDF hF hN hidx hcent hsF hsD
  have hs : s ∈ Z'.centralizerInMho := hF hsF
  obtain ⟨hΦc, hΦa, hΦb⟩ :=
    deviationTorus_generators_eq_familyTwo Z' F hF hsF hφc hφa hφb
  intro d
  obtain ⟨i, j, l, hd⟩ := ofMul_eq_gens_zsmul Z' d
  have hV : Z'.dataD.e (Additive.ofMul d) =
      i • (Torus.c : Torus Z'.τ.k) + j • (Torus.a : Torus Z'.τ.k) +
        l • (Torus.b : Torus Z'.τ.k) := by
    rw [hd, map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
      Z'.dataD.e_c, Z'.dataD.e_a, Z'.dataD.e_b]
  have hΦd : deviationTorus Z' s hs (Additive.ofMul d) =
      j • ((2 : ℤ) ^ (Z'.τ.m + 1) • (Torus.a : Torus Z'.τ.k)) +
        l • ((2 : ℤ) ^ (Z'.τ.m + 1) • (Torus.b : Torus Z'.τ.k)) := by
    rw [hd, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hΦc, hΦa, hΦb]
    simp
  have hLHS : Z'.dataD.e (Additive.ofMul (thetaD Z' s hs d)) =
      (2 : ℤ) • Z'.dataD.e (Additive.ofMul d) + deviationTorus Z' s hs (Additive.ofMul d) :=
    thetaD_additive_torus Z' s hs d
  rw [hLHS, hV, hΦd]
  have hRHS : thetaTwoType Z'.τ (i • (Torus.c : Torus Z'.τ.k) +
      j • (Torus.a : Torus Z'.τ.k) + l • (Torus.b : Torus Z'.τ.k)) =
      i • ((2 : ℤ) • (Torus.c : Torus Z'.τ.k)) +
        j • ((2 + (2 : ℤ) ^ (Z'.τ.m + 1)) • (Torus.a : Torus Z'.τ.k)) +
        l • ((2 + (2 : ℤ) ^ (Z'.τ.m + 1)) • (Torus.b : Torus Z'.τ.k)) := by
    have hc : thetaTwoType Z'.τ (Torus.c : Torus Z'.τ.k) = (2 : ℤ) • Torus.c :=
      thetaTwo_c m
    have ha : thetaTwoType Z'.τ (Torus.a : Torus Z'.τ.k) =
        (2 + (2 : ℤ) ^ (Z'.τ.m + 1)) • Torus.a :=
      thetaTwo_a m
    have hb : thetaTwoType Z'.τ (Torus.b : Torus Z'.τ.k) =
        (2 + (2 : ℤ) ^ (Z'.τ.m + 1)) • Torus.b :=
      thetaTwo_b m
    rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hc, ha, hb]
  rw [hRHS]
  module

theorem theta_eq_matAct_sub_of_conj_familyTwo (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i)
    (e : Additive Z.D ≃+ Torus Z.τ.k) {s l : G}
    (hs : s ∈ Z.centralizerInMho) (hsqD : s * s ∈ Z.D)
    (hlN : l ∈ Subgroup.normalizer (Z.D : Set G))
    (M : IntMat) (hM : Compat Z.τ.k M)
    (hconj : ∀ d : Z.D, e (Additive.ofMul (conjBy hlN d)) =
      matAct Z.τ.k M hM (e (Additive.ofMul d)))
    (hform : ∀ d : Z.D, e (Additive.ofMul (thetaD Z s hs d)) =
      thetaTwoType Z.τ (e (Additive.ofMul d)))
    {d : Z.D} (h : l⁻¹ * s * l = s * (d : G)) :
    thetaTwoType Z.τ (e (Additive.ofMul d)) =
      matAct Z.τ.k M hM (e (Additive.ofMul ⟨s * s, hsqD⟩)) -
        e (Additive.ofMul ⟨s * s, hsqD⟩) := by
  let q : Z.D := ⟨s * s, hsqD⟩
  have hconjq : conjBy hlN q = q * thetaD Z s hs d := by
    apply Subtype.ext
    dsimp [conjBy, q]
    rw [show l⁻¹ * (s * s) * l = (l⁻¹ * s * l) * (l⁻¹ * s * l) by group]
    rw [h]
    exact sq_mul_eq_sq_mul_thetaD Z hk hs d.2
  have heq : matAct Z.τ.k M hM (e (Additive.ofMul q)) =
      e (Additive.ofMul q) + thetaTwoType Z.τ (e (Additive.ofMul d)) := by
    calc matAct Z.τ.k M hM (e (Additive.ofMul q))
        = e (Additive.ofMul (conjBy hlN q)) := (hconj q).symm
      _ = e (Additive.ofMul (q * thetaD Z s hs d)) := by rw [hconjq]
      _ = e (Additive.ofMul q) + e (Additive.ofMul (thetaD Z s hs d)) := by
        rw [ofMul_mul, map_add]
      _ = e (Additive.ofMul q) + thetaTwoType Z.τ (e (Additive.ofMul d)) := by rw [hform]
  rw [heq]
  abel

theorem deviation_kills_omegaIn_two_familyTwo (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n)
    {s : G} (hs : s ∈ Z.centralizerInMho)
    (hΦc : deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩) = 0)
    (hΦa : deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩) =
      (2 : ℤ) ^ (Z.τ.m + 1) • (Torus.a : Torus Z.τ.k))
    (hΦb : deviationTorus Z s hs (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩) =
      (2 : ℤ) ^ (Z.τ.m + 1) • (Torus.b : Torus Z.τ.k))
    {d : Z.D} (hd : (d : G) ∈ omegaIn 2 Z.D) :
    deviationTorus Z s hs (Additive.ofMul d) = 0 := by
  classical
  have hm1 : 1 ≤ Z.τ.m := by
    have h2 : 2 ≤ Z.τ.m := by simpa [StrothTypeIndex.m] using hk 0
    omega
  have hcomm : ∀ a ∈ Z.D, ∀ b ∈ Z.D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (Z.dataD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨-, hd4⟩ := (mem_omegaIn_iff_of_comm hcomm).mp hd
  have hd4' : d ^ (4 : ℕ) = 1 := by
    apply Subtype.ext
    simpa using hd4
  have he4 : (4 : ℤ) • Z.dataD.e (Additive.ofMul d) = 0 := by
    calc (4 : ℤ) • Z.dataD.e (Additive.ofMul d)
        = Z.dataD.e ((4 : ℤ) • Additive.ofMul d) := by rw [map_zsmul]
      _ = Z.dataD.e (Additive.ofMul (d ^ (4 : ℕ))) := by rw [ofMul_pow]; norm_num
      _ = 0 := by rw [hd4']; simp
  obtain ⟨i, j, l, hdrep⟩ := ofMul_eq_gens_zsmul Z d
  have hcoord : Z.dataD.e (Additive.ofMul d) =
      i • Torus.c + j • Torus.a + l • Torus.b := by
    rw [hdrep, map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
      Z.dataD.e_c, Z.dataD.e_a, Z.dataD.e_b]
  rw [hcoord] at he4
  have hk1 : Z.τ.k 1 = Z.τ.m + 2 := by
    rw [StrothTypeIndex.k_eq]; simp [hrel]
  have hk2 : Z.τ.k 2 = Z.τ.m + 2 := by
    rw [StrothTypeIndex.k_two, hrel]
  have hj : (2 : ℤ) ^ Z.τ.m ∣ j := by
    have h1 := congrFun he4 1
    have h1' : ((4 * j : ℤ) : ZMod (2 ^ Z.τ.k 1)) = 0 := by
      simpa [Torus.c, Torus.a, Torus.b, gen, Pi.single_apply, Pi.add_apply,
        Pi.smul_apply, zsmul_eq_mul, mul_assoc] using h1
    rw [hk1] at h1'
    have hdvd : (2 : ℤ) ^ (Z.τ.m + 2) ∣ 4 * j := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (4 * j) (2 ^ (Z.τ.m + 2))).mp h1'
      exact_mod_cast this
    exact dvd_two_pow_of_four_mul_dvd hdvd
  have hl : (2 : ℤ) ^ Z.τ.m ∣ l := by
    have h2 := congrFun he4 2
    have h2' : ((4 * l : ℤ) : ZMod (2 ^ Z.τ.k 2)) = 0 := by
      simpa [Torus.c, Torus.a, Torus.b, gen, Pi.single_apply, Pi.add_apply,
        Pi.smul_apply, zsmul_eq_mul, mul_assoc] using h2
    rw [hk2] at h2'
    have hdvd : (2 : ℤ) ^ (Z.τ.m + 2) ∣ 4 * l := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (4 * l) (2 ^ (Z.τ.m + 2))).mp h2'
      exact_mod_cast this
    exact dvd_two_pow_of_four_mul_dvd hdvd
  have hΦd : deviationTorus Z s hs (Additive.ofMul d) =
      j • ((2 : ℤ) ^ (Z.τ.m + 1) • (Torus.a : Torus Z.τ.k)) +
        l • ((2 : ℤ) ^ (Z.τ.m + 1) • (Torus.b : Torus Z.τ.k)) := by
    rw [hdrep, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hΦc, hΦa, hΦb]
    simp
  rw [hΦd]
  have hja : j • ((2 : ℤ) ^ (Z.τ.m + 1) • (Torus.a : Torus Z.τ.k)) = 0 := by
    rw [← mul_zsmul']
    rw [← addOrderOf_dvd_iff_zsmul_eq_zero, addOrderOf_a, hk1]
    have hp : (2 : ℤ) ^ (Z.τ.m + 2) ∣ j * 2 ^ (Z.τ.m + 1) := by
      obtain ⟨t, ht⟩ := hj
      refine ⟨(2 : ℤ) ^ (Z.τ.m - 1) * t, ?_⟩
      rw [ht]
      have h1 : (2 : ℤ) ^ Z.τ.m * (2 : ℤ) ^ (Z.τ.m + 1) = (2 : ℤ) ^ (2 * Z.τ.m + 1) := by
        rw [← pow_add]; congr 1; omega
      have h2 : (2 : ℤ) ^ (Z.τ.m + 2) * (2 : ℤ) ^ (Z.τ.m - 1) =
          (2 : ℤ) ^ (2 * Z.τ.m + 1) := by
        rw [← pow_add]; congr 1; omega
      calc (2 : ℤ) ^ Z.τ.m * t * 2 ^ (Z.τ.m + 1)
          = ((2 : ℤ) ^ Z.τ.m * 2 ^ (Z.τ.m + 1)) * t := by ring
        _ = (2 : ℤ) ^ (2 * Z.τ.m + 1) * t := by rw [h1]
        _ = ((2 : ℤ) ^ (Z.τ.m + 2) * (2 : ℤ) ^ (Z.τ.m - 1)) * t := by rw [h2]
        _ = (2 : ℤ) ^ (Z.τ.m + 2) * ((2 : ℤ) ^ (Z.τ.m - 1) * t) := by ring
    have hcast : ((2 ^ (Z.τ.m + 2) : ℕ) : ℤ) = (2 : ℤ) ^ (Z.τ.m + 2) := by
      push_cast; ring
    rw [hcast]
    simpa [mul_comm] using hp
  have hjb : l • ((2 : ℤ) ^ (Z.τ.m + 1) • (Torus.b : Torus Z.τ.k)) = 0 := by
    rw [← mul_zsmul']
    rw [← addOrderOf_dvd_iff_zsmul_eq_zero, addOrderOf_b, hk2]
    have hp : (2 : ℤ) ^ (Z.τ.m + 2) ∣ l * 2 ^ (Z.τ.m + 1) := by
      obtain ⟨t, ht⟩ := hl
      refine ⟨(2 : ℤ) ^ (Z.τ.m - 1) * t, ?_⟩
      rw [ht]
      have h1 : (2 : ℤ) ^ Z.τ.m * (2 : ℤ) ^ (Z.τ.m + 1) = (2 : ℤ) ^ (2 * Z.τ.m + 1) := by
        rw [← pow_add]; congr 1; omega
      have h2 : (2 : ℤ) ^ (Z.τ.m + 2) * (2 : ℤ) ^ (Z.τ.m - 1) =
          (2 : ℤ) ^ (2 * Z.τ.m + 1) := by
        rw [← pow_add]; congr 1; omega
      calc (2 : ℤ) ^ Z.τ.m * t * 2 ^ (Z.τ.m + 1)
          = ((2 : ℤ) ^ Z.τ.m * 2 ^ (Z.τ.m + 1)) * t := by ring
        _ = (2 : ℤ) ^ (2 * Z.τ.m + 1) * t := by rw [h1]
        _ = ((2 : ℤ) ^ (Z.τ.m + 2) * (2 : ℤ) ^ (Z.τ.m - 1)) * t := by rw [h2]
        _ = (2 : ℤ) ^ (Z.τ.m + 2) * ((2 : ℤ) ^ (Z.τ.m - 1) * t) := by ring
    have hcast : ((2 ^ (Z.τ.m + 2) : ℕ) : ℤ) = (2 : ℤ) ^ (Z.τ.m + 2) := by
      push_cast; ring
    rw [hcast]
    simpa [mul_comm] using hp
  rw [hja, hjb]
  simp


theorem exists_sq_eq_c_of_index_two_of_centOmega_familyTwo_t200 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) {m : ℕ}
    (hτ : Z.τ = StrothTypeIndex.t200 m)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G)) :
    ∃ s ∈ F, s ∉ Z.D ∧ s * s = (Z.dataD.c : G) := by
  classical
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  set Z' : StrothDatum X :=
    ⟨D, hAD, hDS, StrothTypeIndex.t200 m, dataD, hL, hcentS⟩ with hZ'
  obtain ⟨s0, hs0F, hs0D, hs0sqD⟩ := exists_sq_mem_D_of_index_two Z' hk F hF hidx
  have hs : s0 ∈ Z'.centralizerInMho := hF hs0F
  have hform := thetaD_torus_eq_familyTwo_t200 Z' (m := m) rfl hk hrel F hDF hF hN hidx
    hcent hs0F hs0D
  have hφ := deviation_form_diag_familyTwo_t200 Z' hk hrel (m := m) rfl F hDF hF hN hidx
    hcent hs0F hs0D
  obtain ⟨hΦc, hΦa, hΦb⟩ :=
    deviationTorus_generators_eq_familyTwo Z' F hF hs0F hφ.1 hφ.2.1 hφ.2.2.1
  have hAkill : ∀ (x : G) (hx : x ∈ X.A),
      deviationTorus Z' s0 hs (Additive.ofMul ⟨x, Z'.hAD hx⟩) = 0 := by
    intro x hx
    exact deviation_kills_omegaIn_two_familyTwo Z' hk hrel hs hΦc hΦa hΦb
      (A_le_omegaIn_two Z' hx)
  have huL : Z'.dataD.u ∈ X.L := hL ▸ Z'.dataD.u_mem_L
  have htL : Z'.dataD.t ∈ X.L := hL ▸ Z'.dataD.t_mem_L
  have huvL : Z'.dataD.uv ∈ X.L := hL ▸ Z'.dataD.uv_mem_L
  have hρL : Z'.dataD.ρ ∈ X.L := hL ▸ Z'.dataD.ρ_mem_L
  obtain ⟨du, hduD, hdu⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z' F hF hN hidx hs0F hs0D huL
  obtain ⟨dt, hdtD, hdt⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z' F hF hN hidx hs0F hs0D htL
  obtain ⟨duv, hduvD, hduv⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z' F hF hN hidx hs0F hs0D huvL
  obtain ⟨dρ, hdρD, hdρ⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z' F hF hN hidx hs0F hs0D hρL
  have hcond_uv : ∃ d : Torus Z'.τ.k,
      thetaTwoType Z'.τ d = matAct Z'.τ.k Z'.τ.action.uv Z'.τ.action.compat_uv
        (Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) -
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) :=
    ⟨Z'.dataD.e (Additive.ofMul ⟨duv, hduvD⟩),
      theta_eq_matAct_sub_of_conj_familyTwo Z' hk Z'.dataD.e hs hs0sqD Z'.dataD.uv_mem
        Z'.τ.action.uv Z'.τ.action.compat_uv Z'.dataD.uv_conj hform
        (d := ⟨duv, hduvD⟩) (by simpa using hduv)⟩
  have hcond_t : ∃ d : Torus Z'.τ.k,
      thetaTwoType Z'.τ d = matAct Z'.τ.k Z'.τ.action.t Z'.τ.action.compat_t
        (Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) -
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) :=
    ⟨Z'.dataD.e (Additive.ofMul ⟨dt, hdtD⟩),
      theta_eq_matAct_sub_of_conj_familyTwo Z' hk Z'.dataD.e hs hs0sqD Z'.dataD.t_mem
        Z'.τ.action.t Z'.τ.action.compat_t Z'.dataD.t_conj hform
        (d := ⟨dt, hdtD⟩) (by simpa using hdt)⟩
  have hcond_u : ∃ d : Torus Z'.τ.k,
      thetaTwoType Z'.τ d = matAct Z'.τ.k Z'.τ.action.u Z'.τ.action.compat_u
        (Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) -
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) :=
    ⟨Z'.dataD.e (Additive.ofMul ⟨du, hduD⟩),
      theta_eq_matAct_sub_of_conj_familyTwo Z' hk Z'.dataD.e hs hs0sqD Z'.dataD.u_mem
        Z'.τ.action.u Z'.τ.action.compat_u Z'.dataD.u_conj hform
        (d := ⟨du, hduD⟩) (by simpa using hdu)⟩
  have hcond_ρ : ∃ d : Torus Z'.τ.k,
      thetaTwoType Z'.τ d = matAct Z'.τ.k Z'.τ.action.ρ Z'.τ.action.compat_ρ
        (Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) -
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) :=
    ⟨Z'.dataD.e (Additive.ofMul ⟨dρ, hdρD⟩),
      theta_eq_matAct_sub_of_conj_familyTwo Z' hk Z'.dataD.e hs hs0sqD Z'.dataD.ρ_mem
        Z'.τ.action.ρ Z'.τ.action.compat_ρ Z'.dataD.ρ_conj hform
        (d := ⟨dρ, hdρD⟩) (by simpa using hdρ)⟩
  have hdich := square_class_dichotomy_t200 Z' hk rfl
    (Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) hcond_uv hcond_t hcond_u hcond_ρ
  rcases hdich with ⟨v, hv⟩ | ⟨v, hv⟩
  ·
    exfalso
    obtain ⟨y, hy⟩ := Z'.dataD.e.surjective v
    set d : Z'.D := Additive.toMul y with hd
    have hed : Z'.dataD.e (Additive.ofMul d) = v := by
      rw [hd, ofMul_toMul]
      exact hy
    have hθd : Z'.dataD.e (Additive.ofMul (thetaD Z' s0 hs d)) =
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) := by
      rw [hform d, hed]
      exact hv
    set d' : Z'.D := ⟨s0 * s0, hs0sqD⟩ * thetaD Z' s0 hs d⁻¹ with hd'
    have hsq : (d' : G) = (s0 * (d : G)⁻¹) * (s0 * (d : G)⁻¹) := by
      rw [hd']
      exact (sq_mul_eq_sq_mul_thetaD Z' hk hs (by exact Z'.D.inv_mem d.2)).symm
    have he : Z'.dataD.e (Additive.ofMul d') = 0 := by
      rw [hd', ofMul_mul, map_add, thetaD_inv, ofMul_inv, map_neg, hθd, add_neg_cancel]
    have hz2 : (s0 * (d : G)⁻¹) * (s0 * (d : G)⁻¹) = 1 := by
      have h1 : d' = 1 := by
        apply Additive.ofMul.injective
        apply Z'.dataD.e.injective
        rw [he]
        simp
      rw [← hsq, h1]
      rfl
    have hzS : s0 * (d : G)⁻¹ ∈ (X.S : Subgroup G) :=
      X.S.mul_mem (hF hs0F).1.1 (X.S.inv_mem (hDS d.2))
    have hzA : s0 * (d : G)⁻¹ ∈ Subgroup.centralizer (X.A : Set G) := by
      refine Subgroup.mul_mem _ ?_ ?_
      · rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact commute_of_deviationTorus_eq_zero Z' hs (Z'.hAD ha) (hAkill a ha)
      · refine Subgroup.mem_centralizer_iff.mpr (fun a ha => ?_)
        have haD : a ∈ Z'.D := Z'.hAD ha
        have hcomm : a * (d : G) = (d : G) * a :=
          congrArg Subtype.val (Z'.dataD.isMulCommutative.is_comm.comm ⟨a, haD⟩ ⟨d, d.2⟩)
        exact (show Commute a (d : G) from hcomm).inv_right.eq
    have hzA' : s0 * (d : G)⁻¹ ∈ X.A := X.hH _ hzS hz2 hzA
    have hzD : s0 * (d : G)⁻¹ ∈ Z'.D := Z'.hAD hzA'
    exact hs0D (by
      have : s0 = (s0 * (d : G)⁻¹) * (d : G) := by group
      rw [this]
      exact Z'.D.mul_mem hzD d.2)
  ·
    obtain ⟨y, hy⟩ := Z'.dataD.e.surjective v
    set d : Z'.D := Additive.toMul y with hd
    have hed : Z'.dataD.e (Additive.ofMul d) = v := by
      rw [hd, ofMul_toMul]
      exact hy
    have hθd : Z'.dataD.e (Additive.ofMul (thetaD Z' s0 hs d)) =
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) - Torus.c := by
      rw [hform d, hed]
      exact hv
    set d' : Z'.D := ⟨s0 * s0, hs0sqD⟩ * thetaD Z' s0 hs d⁻¹ with hd'
    have hsq : (d' : G) = (s0 * (d : G)⁻¹) * (s0 * (d : G)⁻¹) := by
      rw [hd']
      exact (sq_mul_eq_sq_mul_thetaD Z' hk hs (by exact Z'.D.inv_mem d.2)).symm
    have he : Z'.dataD.e (Additive.ofMul d') =
        Z'.dataD.e (Additive.ofMul ⟨Z'.dataD.c, Z'.dataD.c.2⟩) := by
      rw [hd', ofMul_mul, map_add, thetaD_inv, ofMul_inv, map_neg, hθd,
        Z'.dataD.e_c]
      abel
    have hsqc : (s0 * (d : G)⁻¹) * (s0 * (d : G)⁻¹) = (Z'.dataD.c : G) := by
      have h1 : d' = ⟨Z'.dataD.c, Z'.dataD.c.2⟩ := by
        apply Additive.ofMul.injective
        apply Z'.dataD.e.injective
        rw [he]
      rw [← hsq, h1]
    refine ⟨s0 * (d : G)⁻¹, F.mul_mem hs0F (F.inv_mem (hDF d.2)), ?_, hsqc⟩
    intro hmem
    apply hs0D
    have : s0 = (s0 * (d : G)⁻¹) * (d : G) := by group
    rw [this]
    exact Z'.D.mul_mem hmem d.2

theorem exists_sq_eq_c_and_deviation_form_familyTwo_t200 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) {m : ℕ}
    (hτ : Z.τ = StrothTypeIndex.t200 m)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G)) :
    ∃ s : G, ∃ hsF : s ∈ F, s ∉ Z.D ∧ s * s = (Z.dataD.c : G) ∧
      ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1 ∧
      ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
        (Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)) ∧
      ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
        (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1)) ∧
      (∀ d : Z.D, ((deviation Z s (hF hsF)
        (Additive.ofMul (d * d))).toMul : G) = 1) := by
  obtain ⟨s, hsF, hsD, hsq⟩ :=
    exists_sq_eq_c_of_index_two_of_centOmega_familyTwo_t200 Z hk hrel hτ F hDF hF hN hidx hcent
  obtain ⟨hφc, hφa, hφb, hφsq⟩ :=
    deviation_form_diag_familyTwo_t200 Z hk hrel hτ F hDF hF hN hidx hcent hsF hsD
  exact ⟨s, hsF, hsD, hsq, hφc, hφa, hφb, hφsq⟩

theorem exists_sq_eq_c_of_index_two_of_centOmega_familyTwo_t201 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) {m : ℕ}
    (hτ : Z.τ = StrothTypeIndex.t201 m)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G)) :
    ∃ s ∈ F, s ∉ Z.D ∧ s * s = (Z.dataD.c : G) := by
  classical
  obtain ⟨D, hAD, hDS, τ, dataD, hL, hcentS⟩ := Z
  subst hτ
  set Z' : StrothDatum X :=
    ⟨D, hAD, hDS, StrothTypeIndex.t201 m, dataD, hL, hcentS⟩ with hZ'
  obtain ⟨s0, hs0F, hs0D, hs0sqD⟩ := exists_sq_mem_D_of_index_two Z' hk F hF hidx
  have hs : s0 ∈ Z'.centralizerInMho := hF hs0F
  have hform := thetaD_torus_eq_familyTwo_t201 Z' (m := m) rfl hk hrel F hDF hF hN hidx
    hcent hs0F hs0D
  have hφ := deviation_form_diag_familyTwo_t201 Z' hk hrel (m := m) rfl F hDF hF hN hidx
    hcent hs0F hs0D
  obtain ⟨hΦc, hΦa, hΦb⟩ :=
    deviationTorus_generators_eq_familyTwo Z' F hF hs0F hφ.1 hφ.2.1 hφ.2.2.1
  have hAkill : ∀ (x : G) (hx : x ∈ X.A),
      deviationTorus Z' s0 hs (Additive.ofMul ⟨x, Z'.hAD hx⟩) = 0 := by
    intro x hx
    exact deviation_kills_omegaIn_two_familyTwo Z' hk hrel hs hΦc hΦa hΦb
      (A_le_omegaIn_two Z' hx)
  have huL : Z'.dataD.u ∈ X.L := hL ▸ Z'.dataD.u_mem_L
  have htL : Z'.dataD.t ∈ X.L := hL ▸ Z'.dataD.t_mem_L
  have huvL : Z'.dataD.uv ∈ X.L := hL ▸ Z'.dataD.uv_mem_L
  have hρL : Z'.dataD.ρ ∈ X.L := hL ▸ Z'.dataD.ρ_mem_L
  obtain ⟨du, hduD, hdu⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z' F hF hN hidx hs0F hs0D huL
  obtain ⟨dt, hdtD, hdt⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z' F hF hN hidx hs0F hs0D htL
  obtain ⟨duv, hduvD, hduv⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z' F hF hN hidx hs0F hs0D huvL
  obtain ⟨dρ, hdρD, hdρ⟩ :=
    exists_mul_eq_of_mem_normalizer_of_index_two Z' F hF hN hidx hs0F hs0D hρL
  have hcond_uv : ∃ d : Torus Z'.τ.k,
      thetaTwoType Z'.τ d = matAct Z'.τ.k Z'.τ.action.uv Z'.τ.action.compat_uv
        (Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) -
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) :=
    ⟨Z'.dataD.e (Additive.ofMul ⟨duv, hduvD⟩),
      theta_eq_matAct_sub_of_conj_familyTwo Z' hk Z'.dataD.e hs hs0sqD Z'.dataD.uv_mem
        Z'.τ.action.uv Z'.τ.action.compat_uv Z'.dataD.uv_conj hform
        (d := ⟨duv, hduvD⟩) (by simpa using hduv)⟩
  have hcond_t : ∃ d : Torus Z'.τ.k,
      thetaTwoType Z'.τ d = matAct Z'.τ.k Z'.τ.action.t Z'.τ.action.compat_t
        (Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) -
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) :=
    ⟨Z'.dataD.e (Additive.ofMul ⟨dt, hdtD⟩),
      theta_eq_matAct_sub_of_conj_familyTwo Z' hk Z'.dataD.e hs hs0sqD Z'.dataD.t_mem
        Z'.τ.action.t Z'.τ.action.compat_t Z'.dataD.t_conj hform
        (d := ⟨dt, hdtD⟩) (by simpa using hdt)⟩
  have hcond_u : ∃ d : Torus Z'.τ.k,
      thetaTwoType Z'.τ d = matAct Z'.τ.k Z'.τ.action.u Z'.τ.action.compat_u
        (Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) -
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) :=
    ⟨Z'.dataD.e (Additive.ofMul ⟨du, hduD⟩),
      theta_eq_matAct_sub_of_conj_familyTwo Z' hk Z'.dataD.e hs hs0sqD Z'.dataD.u_mem
        Z'.τ.action.u Z'.τ.action.compat_u Z'.dataD.u_conj hform
        (d := ⟨du, hduD⟩) (by simpa using hdu)⟩
  have hcond_ρ : ∃ d : Torus Z'.τ.k,
      thetaTwoType Z'.τ d = matAct Z'.τ.k Z'.τ.action.ρ Z'.τ.action.compat_ρ
        (Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) -
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) :=
    ⟨Z'.dataD.e (Additive.ofMul ⟨dρ, hdρD⟩),
      theta_eq_matAct_sub_of_conj_familyTwo Z' hk Z'.dataD.e hs hs0sqD Z'.dataD.ρ_mem
        Z'.τ.action.ρ Z'.τ.action.compat_ρ Z'.dataD.ρ_conj hform
        (d := ⟨dρ, hdρD⟩) (by simpa using hdρ)⟩
  have hdich := square_class_dichotomy_t201 Z' hk rfl
    (Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩)) hcond_uv hcond_t hcond_u hcond_ρ
  rcases hdich with ⟨v, hv⟩ | ⟨v, hv⟩
  ·
    exfalso
    obtain ⟨y, hy⟩ := Z'.dataD.e.surjective v
    set d : Z'.D := Additive.toMul y with hd
    have hed : Z'.dataD.e (Additive.ofMul d) = v := by
      rw [hd, ofMul_toMul]
      exact hy
    have hθd : Z'.dataD.e (Additive.ofMul (thetaD Z' s0 hs d)) =
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) := by
      rw [hform d, hed]
      exact hv
    set d' : Z'.D := ⟨s0 * s0, hs0sqD⟩ * thetaD Z' s0 hs d⁻¹ with hd'
    have hsq : (d' : G) = (s0 * (d : G)⁻¹) * (s0 * (d : G)⁻¹) := by
      rw [hd']
      exact (sq_mul_eq_sq_mul_thetaD Z' hk hs (by exact Z'.D.inv_mem d.2)).symm
    have he : Z'.dataD.e (Additive.ofMul d') = 0 := by
      rw [hd', ofMul_mul, map_add, thetaD_inv, ofMul_inv, map_neg, hθd, add_neg_cancel]
    have hz2 : (s0 * (d : G)⁻¹) * (s0 * (d : G)⁻¹) = 1 := by
      have h1 : d' = 1 := by
        apply Additive.ofMul.injective
        apply Z'.dataD.e.injective
        rw [he]
        simp
      rw [← hsq, h1]
      rfl
    have hzS : s0 * (d : G)⁻¹ ∈ (X.S : Subgroup G) :=
      X.S.mul_mem (hF hs0F).1.1 (X.S.inv_mem (hDS d.2))
    have hzA : s0 * (d : G)⁻¹ ∈ Subgroup.centralizer (X.A : Set G) := by
      refine Subgroup.mul_mem _ ?_ ?_
      · rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact commute_of_deviationTorus_eq_zero Z' hs (Z'.hAD ha) (hAkill a ha)
      · refine Subgroup.mem_centralizer_iff.mpr (fun a ha => ?_)
        have haD : a ∈ Z'.D := Z'.hAD ha
        have hcomm : a * (d : G) = (d : G) * a :=
          congrArg Subtype.val (Z'.dataD.isMulCommutative.is_comm.comm ⟨a, haD⟩ ⟨d, d.2⟩)
        exact (show Commute a (d : G) from hcomm).inv_right.eq
    have hzA' : s0 * (d : G)⁻¹ ∈ X.A := X.hH _ hzS hz2 hzA
    have hzD : s0 * (d : G)⁻¹ ∈ Z'.D := Z'.hAD hzA'
    exact hs0D (by
      have : s0 = (s0 * (d : G)⁻¹) * (d : G) := by group
      rw [this]
      exact Z'.D.mul_mem hzD d.2)
  ·
    obtain ⟨y, hy⟩ := Z'.dataD.e.surjective v
    set d : Z'.D := Additive.toMul y with hd
    have hed : Z'.dataD.e (Additive.ofMul d) = v := by
      rw [hd, ofMul_toMul]
      exact hy
    have hθd : Z'.dataD.e (Additive.ofMul (thetaD Z' s0 hs d)) =
        Z'.dataD.e (Additive.ofMul ⟨s0 * s0, hs0sqD⟩) - Torus.c := by
      rw [hform d, hed]
      exact hv
    set d' : Z'.D := ⟨s0 * s0, hs0sqD⟩ * thetaD Z' s0 hs d⁻¹ with hd'
    have hsq : (d' : G) = (s0 * (d : G)⁻¹) * (s0 * (d : G)⁻¹) := by
      rw [hd']
      exact (sq_mul_eq_sq_mul_thetaD Z' hk hs (by exact Z'.D.inv_mem d.2)).symm
    have he : Z'.dataD.e (Additive.ofMul d') =
        Z'.dataD.e (Additive.ofMul ⟨Z'.dataD.c, Z'.dataD.c.2⟩) := by
      rw [hd', ofMul_mul, map_add, thetaD_inv, ofMul_inv, map_neg, hθd,
        Z'.dataD.e_c]
      abel
    have hsqc : (s0 * (d : G)⁻¹) * (s0 * (d : G)⁻¹) = (Z'.dataD.c : G) := by
      have h1 : d' = ⟨Z'.dataD.c, Z'.dataD.c.2⟩ := by
        apply Additive.ofMul.injective
        apply Z'.dataD.e.injective
        rw [he]
      rw [← hsq, h1]
    refine ⟨s0 * (d : G)⁻¹, F.mul_mem hs0F (F.inv_mem (hDF d.2)), ?_, hsqc⟩
    intro hmem
    apply hs0D
    have : s0 = (s0 * (d : G)⁻¹) * (d : G) := by group
    rw [this]
    exact Z'.D.mul_mem hmem d.2

theorem exists_sq_eq_c_and_deviation_form_familyTwo_t201 (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) (hrel : Z.τ.m + 2 = Z.τ.n) {m : ℕ}
    (hτ : Z.τ = StrothTypeIndex.t201 m)
    (F : Subgroup G) (hDF : Z.D ≤ F) (hF : F ≤ Z.centralizerInMho)
    (hN : X.L ≤ Subgroup.normalizer (F : Set G))
    (hidx : (Z.D.subgroupOf F).index = 2)
    (hcent : F ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G)) :
    ∃ s : G, ∃ hsF : s ∈ F, s ∉ Z.D ∧ s * s = (Z.dataD.c : G) ∧
      ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.c, Z.dataD.c.2⟩)).toMul : G) = 1 ∧
      ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.a, Z.dataD.a.2⟩)).toMul : G) =
        (Z.dataD.a : G) ^ (2 ^ (Z.τ.m + 1)) ∧
      ((deviation Z s (hF hsF) (Additive.ofMul ⟨Z.dataD.b, Z.dataD.b.2⟩)).toMul : G) =
        (Z.dataD.b : G) ^ (2 ^ (Z.τ.m + 1)) ∧
      (∀ d : Z.D, ((deviation Z s (hF hsF)
        (Additive.ofMul (d * d))).toMul : G) = 1) := by
  obtain ⟨s, hsF, hsD, hsq⟩ :=
    exists_sq_eq_c_of_index_two_of_centOmega_familyTwo_t201 Z hk hrel hτ F hDF hF hN hidx hcent
  obtain ⟨hφc, hφa, hφb, hφsq⟩ :=
    deviation_form_diag_familyTwo_t201 Z hk hrel hτ F hDF hF hN hidx hcent hsF hsD
  exact ⟨s, hsF, hsD, hsq, hφc, hφa, hφb, hφsq⟩

end CFSG.CGT.Stroth77

end
