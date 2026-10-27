module

public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.CharacterTheory.Semidihedral.ProjectiveNonsquareInvolutions
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.Foundations.Basic

public section

namespace CFSG.LinearGroups

noncomputable section

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter Matrix
open CFSG.Semidihedral.MatrixCoverData CFSG.Semidihedral.ProjectiveNonsquareInvolutions

universe u

variable {K : Type u} [Field K]

theorem eq_of_anticommute_J {M : Matrix (Fin 2) (Fin 2) K}
    (hJ : !![0, -1; 1, 0] * M = -(M * !![0, -1; 1, 0])) (hM : M * M = -1) :
    M = !![M 0 0, M 0 1; M 0 1, -M 0 0] ∧ M 0 0 ^ 2 + M 0 1 ^ 2 = -1 := by
  have e00 := congrFun (congrFun hJ 0) 0
  have e01 := congrFun (congrFun hJ 0) 1
  have s00 := congrFun (congrFun hM 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 s00
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [e00]
    linear_combination -e01
  · rw [e00] at s00
    linear_combination s00

theorem exists_conj_commute_J (h2 : (2 : K) ≠ 0) {x y x' y' : K} (h : x ^ 2 + y ^ 2 = -1)
    (h' : x' ^ 2 + y' ^ 2 = -1) :
    ∃ Q : GL (Fin 2) K, Q * J K 1 = J K 1 * Q ∧
      (Q : Matrix (Fin 2) (Fin 2) K) * !![x, y; y, -x] = !![x', y'; y', -x'] * Q := by
  have key (s t : K) (hst : s ^ 2 + t ^ 2 ≠ 0) (e1 : s * (x - x') = t * (y + y'))
      (e2 : s * (y - y') = -(t * (x + x'))) :
      ∃ Q : GL (Fin 2) K, Q * J K 1 = J K 1 * Q ∧
        (Q : Matrix (Fin 2) (Fin 2) K) * !![x, y; y, -x] = !![x', y'; y', -x'] * Q := by
    have hdet : (!![s, -t; t, s] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
      rw [det_fin_two_of]
      convert hst using 1
      ring
    refine ⟨GeneralLinearGroup.mkOfDetNeZero !![s, -t; t, s] hdet, Units.ext ?_, ?_⟩
    · change !![s, -t; t, s] * (J K 1 : Matrix (Fin 2) (Fin 2) K) =
        (J K 1 : Matrix (Fin 2) (Fin 2) K) * !![s, -t; t, s]
      rw [J_matrix]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · change !![s, -t; t, s] * !![x, y; y, -x] = !![x', y'; y', -x'] * !![s, -t; t, s]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first
          | linear_combination e1
          | linear_combination -e1
          | linear_combination e2
  by_cases hN : (y + y') ^ 2 + (x - x') ^ 2 = 0
  · refine key (x + x') (y' - y) (fun h0 => h2 ?_) (by linear_combination h - h') (by ring)
    have h4 : (2 : K) * 2 = 0 := by
      linear_combination (-1 : K) * hN + (-1 : K) * h0 + 2 * h + 2 * h'
    exact mul_self_eq_zero.mp h4
  · exact key (y + y') (x - x') hN (by ring) (by linear_combination h - h')

theorem exists_conj_normal_form {A B : GL (Fin 2) K}
    (hAt : trace (A : Matrix (Fin 2) (Fin 2) K) = 0) (hAd : GeneralLinearGroup.det A = 1)
    (hAn : ∀ c : Kˣ, A ≠ GeneralLinearGroup.scalar (Fin 2) c)
    (hB : (B : Matrix (Fin 2) (Fin 2) K) * B = -1)
    (hAB : (A : Matrix (Fin 2) (Fin 2) K) * B = -((B : Matrix (Fin 2) (Fin 2) K) * A)) :
    ∃ P : GL (Fin 2) K, ∃ x y : K, x ^ 2 + y ^ 2 = -1 ∧ P⁻¹ * A * P = J K 1 ∧
      ((P⁻¹ * B * P : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![x, y; y, -x] := by
  obtain ⟨P, hP⟩ := companion_conjugator K A 1 hAt hAd hAn
  have hqp : ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * P = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hpq : (P : Matrix (Fin 2) (Fin 2) K) * ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hJ : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K) =
      ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A * P := by
    rw [← Units.val_mul, ← Units.val_mul, hP, J_matrix, Units.val_one]
  have hM : ((P⁻¹ * B * P : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * B * P := by
    rw [Units.val_mul, Units.val_mul]
  have h1 : ((P⁻¹ * B * P : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((P⁻¹ * B * P : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = -1 := by
    rw [hM]
    calc ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * B * P *
          (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * B * P) =
        ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * B *
          ((P : Matrix (Fin 2) (Fin 2) K) * ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
            B * P := by
          simp only [Matrix.mul_assoc]
      _ = ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (B * B) * P := by
          rw [hpq, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = -1 := by
          rw [hB, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hqp]
  have h2 : !![0, -1; 1, 0] * ((P⁻¹ * B * P : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      -(((P⁻¹ * B * P : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * !![0, -1; 1, 0]) := by
    rw [hM, hJ]
    calc ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A * P *
          (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * B * P) =
        ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (A * B) * P := by
          simp only [← Matrix.mul_assoc]
          rw [Matrix.mul_assoc _ (P : Matrix (Fin 2) (Fin 2) K), hpq, Matrix.mul_one]
      _ = -(((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (B * A) * P) := by
          rw [hAB, Matrix.mul_neg, Matrix.neg_mul]
      _ = -(((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * B * P *
          (((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A * P)) := by
          simp only [← Matrix.mul_assoc]
          rw [Matrix.mul_assoc _ (P : Matrix (Fin 2) (Fin 2) K), hpq, Matrix.mul_one]
  obtain ⟨hMe, hxy⟩ := eq_of_anticommute_J h2 h1
  exact ⟨P, _, _, hxy, hP, hMe⟩

theorem exists_conj_of_normal_forms (h2 : (2 : K) ≠ 0) {A B A' B' P P' : GL (Fin 2) K}
    {x y x' y' : K} (hxy : x ^ 2 + y ^ 2 = -1) (hP : P⁻¹ * A * P = J K 1)
    (hPB : ((P⁻¹ * B * P : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![x, y; y, -x])
    (hxy' : x' ^ 2 + y' ^ 2 = -1) (hP' : P'⁻¹ * A' * P' = J K 1)
    (hPB' : ((P'⁻¹ * B' * P' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![x', y'; y', -x']) :
    ∃ X : GL (Fin 2) K, X * A * X⁻¹ = A' ∧ X * B * X⁻¹ = B' := by
  obtain ⟨Q, hQJ, hQB⟩ := exists_conj_commute_J h2 hxy hxy'
  have hQB' : Q * (P⁻¹ * B * P) = (P'⁻¹ * B' * P') * Q := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul (P'⁻¹ * B' * P'), hPB, hPB']
    exact hQB
  refine ⟨P' * Q * P⁻¹, ?_, ?_⟩
  · calc P' * Q * P⁻¹ * A * (P' * Q * P⁻¹)⁻¹ = P' * (Q * (P⁻¹ * A * P)) * Q⁻¹ * P'⁻¹ := by
          group
      _ = P' * (P'⁻¹ * A' * P') * P'⁻¹ := by rw [hP, hQJ, ← hP']; group
      _ = A' := by group
  · calc P' * Q * P⁻¹ * B * (P' * Q * P⁻¹)⁻¹ = P' * (Q * (P⁻¹ * B * P)) * Q⁻¹ * P'⁻¹ := by
          group
      _ = B' := by rw [hQB']; group

theorem coordinateGLAction_eq_one_iff [Finite K] (g : GL (Fin 2) K) :
    coordinateGLAction K g = 1 ↔ g ∈ Subgroup.center (GL (Fin 2) K) := by
  rw [← ProjGenLinGroup.mk_eq_one]
  exact map_eq_one_iff _ (coordinatePGLAction_injective K)

theorem coordinateGLAction_eq_iff [Finite K] {g h : GL (Fin 2) K} :
    coordinateGLAction K g = coordinateGLAction K h ↔
      ∃ u : Kˣ, g * GeneralLinearGroup.scalar (Fin 2) u = h := by
  rw [← ProjGenLinGroup.mk_eq_mk_iff]
  exact (coordinatePGLAction_injective K).eq_iff

theorem exists_det_eq_one_of_mem_coordinateG {v : Equiv.Perm (Omega K)}
    (hv : v ∈ coordinateG K) :
    ∃ A : GL (Fin 2) K, GeneralLinearGroup.det A = 1 ∧ coordinateGLAction K A = v := by
  rw [← coordinatePSLAction_range_eq_G] at hv
  obtain ⟨a, rfl⟩ := hv
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective a
  refine ⟨SpecialLinearGroup.toGL A, Units.ext ?_, (coordinatePSLAction_mk A).symm⟩
  simp

theorem trace_eq_zero_of_proj_involution [Finite K] {A : GL (Fin 2) K}
    (hAd : GeneralLinearGroup.det A = 1) (h1 : coordinateGLAction K A ≠ 1)
    (h2 : coordinateGLAction K A ^ 2 = 1) :
    trace (A : Matrix (Fin 2) (Fin 2) K) = 0 ∧ (A : Matrix (Fin 2) (Fin 2) K) * A = -1 ∧
      ∀ c : Kˣ, A ≠ GeneralLinearGroup.scalar (Fin 2) c := by
  have hord : orderOf (glProjective K A) = 2 := by
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => h1 ?_
    · rw [Subgroup.coe_pow, glProjective_coe]
      exact h2
    · have h' := congrArg Subtype.val h
      rw [glProjective_coe] at h'
      exact h'
  have ht := trace_zero_of_projective_involution K A hord
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simpa using congrArg Units.val hAd
  have hch := cayley_hamilton_two K (A : Matrix (Fin 2) (Fin 2) K)
  rw [ht, zero_smul, sub_zero, hdet, map_one, ← eq_neg_iff_add_eq_zero, pow_two] at hch
  refine ⟨ht, hch, fun c hc => h1 ?_⟩
  rw [hc]
  change coordinatePGLAction K (ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 2) c)) = 1
  rw [ProjGenLinGroup.mk_scalar, map_one]

theorem anticommute_of_proj_commute [Finite K] (h2 : (2 : K) ≠ 0) {A B : GL (Fin 2) K}
    (hAd : GeneralLinearGroup.det A = 1) (hBd : GeneralLinearGroup.det B = 1)
    (hA1 : coordinateGLAction K A ≠ 1) (hA2 : coordinateGLAction K A ^ 2 = 1)
    (hB1 : coordinateGLAction K B ≠ 1) (hB2 : coordinateGLAction K B ^ 2 = 1)
    (hne : coordinateGLAction K A ≠ coordinateGLAction K B)
    (hc : coordinateGLAction K A * coordinateGLAction K B =
      coordinateGLAction K B * coordinateGLAction K A) :
    (A : Matrix (Fin 2) (Fin 2) K) * B = -((B : Matrix (Fin 2) (Fin 2) K) * A) := by
  rw [← map_mul, ← map_mul, coordinateGLAction_eq_iff] at hc
  obtain ⟨u, hu⟩ := hc
  have hu2 : u ^ 2 = 1 := by
    have h := congrArg GeneralLinearGroup.det hu
    rw [map_mul, map_mul, map_mul, GeneralLinearGroup.det_scalar, hAd, hBd] at h
    simpa using h
  have hu2' : (u : K) ^ 2 = 1 := by
    simpa using congrArg Units.val hu2
  have hm := congrArg Units.val hu
  rw [Units.val_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at hm
  rcases sq_eq_one_iff.mp hu2' with h | h
  · exfalso
    rw [h, map_one, Matrix.mul_one] at hm
    have hAA := (trace_eq_zero_of_proj_involution hAd hA1 hA2).2.1
    have hBB := (trace_eq_zero_of_proj_involution hBd hB1 hB2).2.1
    have hCd : GeneralLinearGroup.det (A * B) = 1 := by rw [map_mul, hAd, hBd, mul_one]
    have hC1 : coordinateGLAction K (A * B) ≠ 1 := by
      rw [map_mul]
      intro h1
      apply hne
      rw [mul_eq_one_iff_eq_inv.mp h1]
      exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, hB2])
    have hAB' : A * B = B * A := Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hm)
    have hcomm : Commute (coordinateGLAction K A) (coordinateGLAction K B) := by
      change _ * _ = _ * _
      rw [← map_mul, ← map_mul, hAB']
    have hC2 : coordinateGLAction K (A * B) ^ 2 = 1 := by
      rw [map_mul, hcomm.mul_pow, hA2, hB2, one_mul]
    have hCC := (trace_eq_zero_of_proj_involution hCd hC1 hC2).2.1
    rw [Units.val_mul] at hCC
    have h11 : (1 : Matrix (Fin 2) (Fin 2) K) = -1 := by
      calc (1 : Matrix (Fin 2) (Fin 2) K) = (A * A : Matrix (Fin 2) (Fin 2) K) * (B * B) := by
            rw [hAA, hBB, neg_mul_neg, Matrix.mul_one]
        _ = (A : Matrix (Fin 2) (Fin 2) K) * ((A * B : Matrix (Fin 2) (Fin 2) K) * B) := by
            simp only [Matrix.mul_assoc]
        _ = (A : Matrix (Fin 2) (Fin 2) K) * ((B * A : Matrix (Fin 2) (Fin 2) K) * B) := by
            rw [hm]
        _ = -1 := by
            rw [← hCC]
            simp only [Matrix.mul_assoc]
    have h00 := congrFun (congrFun h11 0) 0
    simp only [one_apply_eq, Matrix.neg_apply] at h00
    apply h2
    linear_combination h00
  · rw [h, map_neg, map_one, Matrix.mul_neg, Matrix.mul_one] at hm
    rw [← hm, neg_neg]

theorem isKleinFour_of_card_eq_four {H : Type*} [Group H] (h4 : Nat.card H = 4)
    (hsq : ∀ x : H, x ^ 2 = 1) : IsKleinFour H := by
  refine ⟨h4, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton H := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : H)
    omega
  · exact h

theorem exists_pair_ne_of_isKleinFour {H : Type*} [Group H] [IsKleinFour H] :
    ∃ x y : H, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [IsKleinFour.card_four]; norm_num)
  have : Nontrivial H :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [IsKleinFour.card_four]; norm_num)
  obtain ⟨x, hx⟩ := exists_ne (1 : H)
  obtain ⟨y, hy⟩ : ∃ y : H, y ∉ Subgroup.zpowers x := by
    by_contra h
    exact IsKleinFour.not_isCyclic
      ⟨⟨x, fun y => Subgroup.mem_zpowers_iff.mp (not_not.mp (not_exists.mp h y))⟩⟩
  exact ⟨x, y, hx, fun h => hy (h ▸ Subgroup.one_mem _), fun h => hy (h ▸ Subgroup.mem_zpowers x)⟩

theorem exists_normal_form_of_four_group [Finite K] (h2 : (2 : K) ≠ 0)
    {V : Subgroup (Equiv.Perm (Omega K))} (hVG : V ≤ coordinateG K) [IsKleinFour V] :
    ∃ A B : GL (Fin 2) K, coordinateGLAction K A ∈ V ∧ coordinateGLAction K B ∈ V ∧
      coordinateGLAction K A ≠ 1 ∧ coordinateGLAction K B ≠ 1 ∧
      coordinateGLAction K A ≠ coordinateGLAction K B ∧
      ∃ P : GL (Fin 2) K, ∃ x y : K, x ^ 2 + y ^ 2 = -1 ∧ P⁻¹ * A * P = J K 1 ∧
        ((P⁻¹ * B * P : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![x, y; y, -x] := by
  obtain ⟨v₁, v₂, h₁, h₂, h₁₂⟩ := exists_pair_ne_of_isKleinFour (H := V)
  obtain ⟨A, hAd, hA⟩ := exists_det_eq_one_of_mem_coordinateG (hVG v₁.2)
  obtain ⟨B, hBd, hB⟩ := exists_det_eq_one_of_mem_coordinateG (hVG v₂.2)
  have hsq (v : V) : (v : Equiv.Perm (Omega K)) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, pow_two, IsKleinFour.mul_self, Subgroup.coe_one]
  have hA1 : coordinateGLAction K A ≠ 1 := by
    rw [hA]
    exact fun h => h₁ (Subtype.ext h)
  have hB1 : coordinateGLAction K B ≠ 1 := by
    rw [hB]
    exact fun h => h₂ (Subtype.ext h)
  have hne : coordinateGLAction K A ≠ coordinateGLAction K B := by
    rw [hA, hB]
    exact fun h => h₁₂ (Subtype.ext h)
  have hA2 : coordinateGLAction K A ^ 2 = 1 := hA ▸ hsq v₁
  have hB2 : coordinateGLAction K B ^ 2 = 1 := hB ▸ hsq v₂
  have hc : coordinateGLAction K A * coordinateGLAction K B =
      coordinateGLAction K B * coordinateGLAction K A := by
    rw [hA, hB]
    exact congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm v₁ v₂)
  obtain ⟨hAt, -, hAn⟩ := trace_eq_zero_of_proj_involution hAd hA1 hA2
  have hBB := (trace_eq_zero_of_proj_involution hBd hB1 hB2).2.1
  have hAB := anticommute_of_proj_commute h2 hAd hBd hA1 hA2 hB1 hB2 hne hc
  exact ⟨A, B, hA ▸ v₁.2, hB ▸ v₂.2, hA1, hB1, hne,
    exists_conj_normal_form hAt hAd hAn hBB hAB⟩

theorem exists_conj_of_four_groups [Finite K] (h2 : (2 : K) ≠ 0)
    {V W : Subgroup (Equiv.Perm (Omega K))} (hVG : V ≤ coordinateG K) (hWG : W ≤ coordinateG K)
    [IsKleinFour V] [IsKleinFour W] :
    ∃ d ∈ coordinateD K, W = V.map (MulAut.conj d).toMonoidHom := by
  obtain ⟨A, B, hAV, hBV, -, -, -, P, x, y, hxy, hP, hPB⟩ :=
    exists_normal_form_of_four_group h2 hVG
  obtain ⟨A', B', hAW, hBW, hA1, hB1, hne, P', x', y', hxy', hP', hPB'⟩ :=
    exists_normal_form_of_four_group h2 hWG
  obtain ⟨X, hXA, hXB⟩ := exists_conj_of_normal_forms h2 hxy hP hPB hxy' hP' hPB'
  have hD : coordinateGLAction K X ∈ coordinateD K := by
    rw [← coordinateGLAction_range_eq_D]
    exact ⟨X, rfl⟩
  refine ⟨coordinateGLAction K X, hD, ?_⟩
  have hconj (M M' : GL (Fin 2) K) (h : X * M * X⁻¹ = M') :
      MulAut.conj (coordinateGLAction K X) (coordinateGLAction K M) =
        coordinateGLAction K M' := by
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, h]
  have hA' : coordinateGLAction K A' ∈
      V.map (MulAut.conj (coordinateGLAction K X)).toMonoidHom :=
    ⟨_, hAV, hconj A A' hXA⟩
  have hB' : coordinateGLAction K B' ∈
      V.map (MulAut.conj (coordinateGLAction K X)).toMonoidHom :=
    ⟨_, hBV, hconj B B' hXB⟩
  have hle : W ≤ V.map (MulAut.conj (coordinateGLAction K X)).toMonoidHom := by
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact Subgroup.one_mem _
    by_cases hzA : z = coordinateGLAction K A'
    · rw [hzA]
      exact hA'
    by_cases hzB : z = coordinateGLAction K B'
    · rw [hzB]
      exact hB'
    have hz' := IsKleinFour.eq_mul_of_ne_all (x := (⟨_, hAW⟩ : W)) (y := ⟨_, hBW⟩)
      (z := ⟨z, hz⟩) (fun h => hA1 (congrArg Subtype.val h))
      (fun h => hB1 (congrArg Subtype.val h)) (fun h => hne (congrArg Subtype.val h))
      (fun h => hz1 (congrArg Subtype.val h)) (fun h => hzA (congrArg Subtype.val h))
      (fun h => hzB (congrArg Subtype.val h))
    rw [show z = coordinateGLAction K A' * coordinateGLAction K B' from congrArg Subtype.val hz']
    exact Subgroup.mul_mem _ hA' hB'
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, IsKleinFour.card_four,
    IsKleinFour.card_four]

theorem centralizer_inf_coordinateD_eq
    [Finite K] (hK : IsOddPrimePower (Nat.card K))
    {V : Subgroup (Equiv.Perm (Omega K))} (hVD : V ≤ coordinateD K) [IsKleinFour V] :
    Subgroup.centralizer (V : Set (Equiv.Perm (Omega K))) ⊓ coordinateD K = V := by
  have hf := coordinatePGLAction_injective K
  have hrange := coordinatePGLAction_range_eq_D K
  have hmap : (V.comap (coordinatePGLAction K)).map (coordinatePGLAction K) = V := by
    rw [Subgroup.map_comap_eq, hrange, inf_eq_right.mpr hVD]
  have hcard : Nat.card (V.comap (coordinatePGLAction K)) = 4 := by
    rw [← Subgroup.card_map_of_injective hf, hmap, IsKleinFour.card_four]
  have hsq (x : V.comap (coordinatePGLAction K)) : x ^ 2 = 1 := by
    apply Subtype.ext
    apply hf
    rw [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one, pow_two]
    exact congrArg Subtype.val (IsKleinFour.mul_self (⟨_, x.2⟩ : V))
  have hC := pgl2_kleinFour_centralizer_eq_self K hK _ (isKleinFour_of_card_eq_four hcard hsq)
  apply le_antisymm
  · rintro z ⟨hzC, hzD⟩
    rw [← hrange] at hzD
    obtain ⟨g, rfl⟩ := hzD
    have hg : g ∈ Subgroup.centralizer
        ((V.comap (coordinatePGLAction K) : Subgroup (PGL2 K)) : Set (PGL2 K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      apply hf
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp hzC _ hh
    rw [hC] at hg
    exact hg
  · intro z hz
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun y hy => ?_, hVD hz⟩
    exact congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm (⟨y, hy⟩ : V) ⟨z, hz⟩)

theorem card_le_four_of_isElementaryAbelian
    [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (E : Subgroup (coordinateD K)) [IsElementaryAbelian 2 E] : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (PGL2 K) := Finite.of_injective _ (pglEquivCoordinateD K).injective
  by_contra hlt
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (IsElementaryAbelian.isPGroup 2 E)
  have h4 : 2 ^ 2 ∣ Nat.card E := by
    rw [hn]
    refine pow_dvd_pow 2 ?_
    by_contra h
    rw [hn] at hlt
    interval_cases n <;> simp_all
  obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4
  let ψ : E →* PGL2 K := (pglEquivCoordinateD K).symm.toMonoidHom.comp E.subtype
  have hψ : Function.Injective ψ :=
    (pglEquivCoordinateD K).symm.injective.comp E.subtype_injective
  have hcard : Nat.card (W.map ψ) = 4 := by
    rw [Subgroup.card_map_of_injective hψ, hW]
    norm_num
  have hsq (x : W.map ψ) : x ^ 2 = 1 := by
    obtain ⟨w, -, hw⟩ := x.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hw, ← map_pow,
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E) w,
      map_one]
  have hC := pgl2_kleinFour_centralizer_eq_self K hK _ (isKleinFour_of_card_eq_four hcard hsq)
  have hle : ψ.range ≤ W.map ψ := by
    rw [← hC]
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, -, rfl⟩
    rw [← map_mul, ← map_mul, (inferInstance : IsMulCommutative E).is_comm.comm]
  have := Subgroup.card_le_of_le hle
  rw [hcard, ← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv] at this
  omega

theorem isOddPrimePower_card_of_ringChar_ne_two [Finite K] (hK : ringChar K ≠ 2) :
    IsOddPrimePower (Nat.card K) := by
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  exact ⟨ringChar K, n, hp, hp.odd_of_ne_two hK, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem odd_projective_linear_two_four_groups
    (K : Type u) [Field K] [Finite K]
    (hK : ringChar K ≠ 2) :
    ((coordinateG K).subgroupOf (coordinateD K)).Normal ∧
      (coordinateG K).relIndex (coordinateD K) = 2 ∧
      (∀ V : Subgroup (Equiv.Perm (Omega K)), V ≤ coordinateG K → IsElementaryAbelian 2 V →
        Nat.card V = 4 →
          Subgroup.centralizer (V : Set (Equiv.Perm (Omega K))) ⊓ coordinateD K = V) ∧
      (∀ V W : Subgroup (Equiv.Perm (Omega K)), V ≤ coordinateG K → IsElementaryAbelian 2 V →
        Nat.card V = 4 → W ≤ coordinateG K → IsElementaryAbelian 2 W → Nat.card W = 4 →
          ∃ d ∈ coordinateD K, W = V.map (MulAut.conj d).toMonoidHom) ∧
      CFSG.pRank 2 (coordinateD K) ≤ 2 := by
  have hodd := isOddPrimePower_card_of_ringChar_ne_two hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  refine ⟨coordinateG_normal_in_D K, ?_, fun V hVG hV hV4 => ?_,
    fun V W hVG hV hV4 hWG hW hW4 => ?_, ?_⟩
  · rw [Subgroup.relIndex, ← pglPSLRange_map_coordinateD,
      Subgroup.index_map_of_bijective (pglEquivCoordinateD K).bijective]
    exact pgl2_psl2Range_index_eq_two K hodd
  · have := isKleinFour_of_card_eq_four hV4 fun x =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 V) x
    exact centralizer_inf_coordinateD_eq hodd (hVG.trans (coordinateG_le_D K))
  · have := isKleinFour_of_card_eq_four hV4 fun x =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 V) x
    have := isKleinFour_of_card_eq_four hW4 fun x =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 W) x
    exact exists_conj_of_four_groups h2 hVG hWG
  · refine csSup_le' ?_
    rintro r ⟨E, hE, hcard⟩
    have := card_le_four_of_isElementaryAbelian hodd E
    rw [hcard] at this
    exact (Nat.pow_le_pow_iff_right one_lt_two).mp this

end

end CFSG.LinearGroups
