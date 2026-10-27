module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckP1
import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckWedge

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer Matrix Certificates.U52Yamada

theorem zSU_ne_one : zSU ≠ 1 := fun h => by
  have := congrArg mat h
  rw [mat_zSU, mat_one] at this
  exact absurd this (by decide)

theorem zSU_mul_self : zSU * zSU = 1 := ext_mat (by rw [mat_mul, mat_zSU, mat_one]; decide)

@[expose] def cvec (M : Matrix (Fin 5) (Fin 5) F4) : Fin 3 → F4 := fun i => M (ι3 i) 0

@[expose] def hnorm (c : Fin 3 → F4) : F4 := bar (c 0) * c 2 + bar (c 1) * c 1 + bar (c 2) * c 0

theorem cvec_one : cvec (1 : Matrix (Fin 5) (Fin 5) F4) = 0 := by
  funext i
  fin_cases i <;> rfl

theorem mul_eq_zero_of_isA₁Shape {N N' : Matrix (Fin 5) (Fin 5) F4} (hN : IsA₁Shape N)
    (hN' : IsA₁Shape N') {i j : Fin 5} (hij : ¬ (i = 4 ∧ j = 0)) : (N * N') i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h1 : (k = 0 ∧ i ≠ 0) ∨ (i = 4 ∧ k ≠ 4)
  · by_cases h2 : (j = 0 ∧ k ≠ 0) ∨ (k = 4 ∧ j ≠ 4)
    · exfalso
      rcases h1 with ⟨hk0, -⟩ | ⟨hi4, hk⟩ <;> rcases h2 with ⟨hj0, hk'⟩ | ⟨hk4, -⟩
      · exact hk' hk0
      · rw [hk0] at hk4
        exact absurd hk4 (by decide)
      · exact hij ⟨hi4, hj0⟩
      · exact hk hk4
    · rw [hN' k j h2, mul_zero]
  · rw [hN i k h1, zero_mul]

theorem isA₁Shape_mul_sub {M M' : Matrix (Fin 5) (Fin 5) F4} (hM : IsA₁Shape (M - 1))
    (hM' : IsA₁Shape (M' - 1)) :
    IsA₁Shape (M * M' - 1) ∧ cvec (M * M') = cvec M + cvec M' := by
  have e : M * M' - 1 = (M - 1) + (M' - 1) + (M - 1) * (M' - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  refine ⟨fun i j hij => ?_, ?_⟩
  · rw [e, Matrix.add_apply, Matrix.add_apply, hM i j hij, hM' i j hij,
      mul_eq_zero_of_isA₁Shape hM hM' (fun h => hij (Or.inl ⟨h.2, by rw [h.1]; decide⟩))]
    simp
  · have e' : M * M' = (M - 1) + (M' - 1) + (M - 1) * (M' - 1) + 1 := by
      rw [← e]
      abel
    funext i
    have h0 : ((M - 1) * (M' - 1)) (ι3 i) 0 = 0 :=
      mul_eq_zero_of_isA₁Shape hM hM' (by fin_cases i <;> decide)
    have h1i : (1 : Matrix (Fin 5) (Fin 5) F4) (ι3 i) 0 = 0 := by
      fin_cases i <;> rfl
    simp only [cvec, Pi.add_apply]
    rw [e', Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, h0, h1i, Matrix.sub_apply,
      Matrix.sub_apply, h1i]
    simp

theorem cvec_x₂ (a : F4) : cvec (x₂Mat a) = ![a, 0, 0] := by
  funext i
  fin_cases i <;> rfl

theorem cvec_x₃ (a : F4) : cvec (x₃Mat a) = ![0, 0, a] := by
  funext i
  fin_cases i <;> rfl

theorem cvec_x₄ (a b : F4) : cvec (x₄Mat a b) = ![0, a, 0] := by
  funext i
  fin_cases i <;> rfl

theorem exists_nf_of_mem_A₁sub {a : SU52} (ha : a ∈ A₁sub) :
    ∃ a₂ a₃ a₄ b₄ : F4, ValidPair a₄ b₄ ∧ mat a = x₂Mat a₂ * x₃Mat a₃ * x₄Mat a₄ b₄ := by
  obtain ⟨haS, h21, h31⟩ := mem_A₁sub.1 ha
  obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, g₁, g₂, g₃, g₄, e₁, e₂, e₃, e₄, rfl, -, k₁, l₁, -⟩ :=
    exists_eq_nf_coord haS
  rw [h21] at k₁
  rw [h31] at l₁
  rw [← k₁, ← l₁, x₁Mat_zero] at e₁
  refine ⟨a₂, a₃, a₄, b₄, x₄_coord_rel e₄, ?_⟩
  rw [mat_mul, mat_mul, mat_mul, e₁, e₂, e₃, e₄, Matrix.one_mul]

theorem isA₁Shape_of_mem_A₁sub {a : SU52} (ha : a ∈ A₁sub) : IsA₁Shape (mat a - 1) := by
  obtain ⟨a₂, a₃, a₄, b₄, -, e⟩ := exists_nf_of_mem_A₁sub ha
  rw [e]
  exact (isA₁Shape_mul_sub (isA₁Shape_mul_sub (isA₁Shape_x₂ a₂) (isA₁Shape_x₃ a₃)).1
    (isA₁Shape_x₄ a₄ b₄)).1

theorem cvec_mul {a a' : SU52} (ha : a ∈ A₁sub) (ha' : a' ∈ A₁sub) :
    cvec (mat (a * a')) = cvec (mat a) + cvec (mat a') :=
  (isA₁Shape_mul_sub (isA₁Shape_of_mem_A₁sub ha) (isA₁Shape_of_mem_A₁sub ha')).2

theorem cvec_nf (a₂ a₃ a₄ b₄ : F4) :
    cvec (x₂Mat a₂ * x₃Mat a₃ * x₄Mat a₄ b₄) = ![a₂, a₄, a₃] := by
  rw [(isA₁Shape_mul_sub (isA₁Shape_mul_sub (isA₁Shape_x₂ a₂) (isA₁Shape_x₃ a₃)).1
    (isA₁Shape_x₄ a₄ b₄)).2, (isA₁Shape_mul_sub (isA₁Shape_x₂ a₂) (isA₁Shape_x₃ a₃)).2,
    cvec_x₂, cvec_x₃, cvec_x₄]
  funext i
  fin_cases i <;> simp

theorem mem_ZX₄sub_of_cvec_eq_zero {a : SU52} (ha : a ∈ A₁sub) (h : cvec (mat a) = 0) :
    a ∈ ZX₄sub := by
  obtain ⟨a₂, a₃, a₄, b₄, -, e⟩ := exists_nf_of_mem_A₁sub ha
  rw [e, cvec_nf] at h
  have h2 : a₂ = 0 := congrFun h 0
  have h4 : a₄ = 0 := congrFun h 1
  have h3 : a₃ = 0 := congrFun h 2
  subst h2 h3 h4
  refine mem_x₄Sub.2 ⟨0, b₄, rfl, ?_⟩
  rw [e, x₂Mat_zero, x₃Mat_zero, Matrix.one_mul, Matrix.one_mul]

theorem cvec_of_mem_ZX₄sub {a : SU52} (ha : a ∈ ZX₄sub) : cvec (mat a) = 0 := by
  obtain ⟨α, β, hα, hm⟩ := mem_x₄Sub.1 ha
  subst hα
  rw [hm, cvec_x₄]
  funext i
  fin_cases i <;> rfl

theorem inv_mul_mem_ZX₄sub_iff {a a' : SU52} (ha : a ∈ A₁sub) (ha' : a' ∈ A₁sub) :
    a⁻¹ * a' ∈ ZX₄sub ↔ cvec (mat a) = cvec (mat a') := by
  have hai : a⁻¹ ∈ A₁sub := inv_mem ha
  have hinv : cvec (mat a⁻¹) + cvec (mat a) = 0 := by
    rw [← cvec_mul hai ha, inv_mul_cancel, mat_one]
    funext i
    fin_cases i <;> rfl
  have hneg : cvec (mat a⁻¹) = cvec (mat a) := by
    funext i
    have := congrFun hinv i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    exact (eq_neg_of_add_eq_zero_left this).trans (CharTwo.neg_eq _)
  constructor
  · intro h
    have := cvec_of_mem_ZX₄sub h
    rw [cvec_mul hai ha', hneg] at this
    funext i
    have hi := congrFun this i
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    exact (eq_neg_of_add_eq_zero_left hi).trans (CharTwo.neg_eq _)
  · intro h
    refine mem_ZX₄sub_of_cvec_eq_zero (mul_mem hai ha') ?_
    rw [cvec_mul hai ha', hneg, h]
    funext i
    simp [CharTwo.add_self_eq_zero]

theorem nf_sq_iff : ∀ a₂ a₃ a₄ b₄ : F4, a₄ * bar a₄ = b₄ + bar b₄ →
    (x₂Mat a₂ * x₃Mat a₃ * x₄Mat a₄ b₄ * (x₂Mat a₂ * x₃Mat a₃ * x₄Mat a₄ b₄) = 1 ↔
      hnorm ![a₂, a₄, a₃] = 0) := by
  unfold hnorm
  decide +kernel

theorem mul_self_eq_one_iff {a : SU52} (ha : a ∈ A₁sub) :
    a * a = 1 ↔ hnorm (cvec (mat a)) = 0 := by
  obtain ⟨a₂, a₃, a₄, b₄, hv, e⟩ := exists_nf_of_mem_A₁sub ha
  rw [e, cvec_nf, ← nf_sq_iff a₂ a₃ a₄ b₄ hv, ← e, ← mat_mul, ← mat_one]
  exact ⟨fun h => by rw [h], fun h => ext_mat h⟩

@[expose] def b₀SU : SU52 := x₃SU 1 * zSU

theorem mat_b₀SU : mat b₀SU = x₃Mat 1 * x₄Mat 0 1 := rfl

theorem b₀SU_mem_A₁sub : b₀SU ∈ A₁sub :=
  mul_mem (X₃sub_le_A₁sub (x₃SU_mem 1)) (X₄sub_le_A₁sub' (ZX₄sub_le_X₄sub zSU_mem))

theorem b₀SU_mem_Fsub : b₀SU ∈ Fsub :=
  mul_mem (mem_sup_left (mem_sup_right (x₃SU_mem 1))) (mem_sup_right zSU_mem)

theorem b₀SU_eq : b₀SU = conjX₁ 0 * conjX₁ 1 :=
  ext_mat (by rw [mat_mul, mat_conjX₁, mat_conjX₁, mat_b₀SU]; decide)

@[expose] def orbW : Fin 27 → List (Fin 10) :=
  ![[], [2], [2, 2], [0], [6, 0], [7, 0], [7, 6, 0], [3, 7, 0], [3, 7, 6, 0], [3, 3, 7, 0],
    [0, 7, 2, 2, 0], [2, 0], [6, 2, 0], [0, 7, 0], [6, 0, 7, 0], [7, 6, 2, 0], [7, 2, 0],
    [3, 7, 6, 2, 0], [3, 7, 2, 0], [2, 2, 0], [6, 2, 2, 0], [0, 7, 6, 0], [6, 0, 7, 6, 0],
    [6, 0, 7, 2, 0], [0, 7, 2, 0], [7, 2, 2, 0], [7, 6, 2, 2, 0]]

@[expose] def orbV : Fin 27 → Fin 3 → F4 :=
  ![![0, 0, 1], ![0, 0, F4.ω], ![0, 0, F4.ω + 1], ![1, 0, 0], ![1, 0, 1], ![1, 1, F4.ω],
    ![1, 1, F4.ω + 1], ![1, F4.ω, F4.ω], ![1, F4.ω, F4.ω + 1], ![1, F4.ω + 1, F4.ω],
    ![1, F4.ω + 1, F4.ω + 1], ![F4.ω, 0, 0], ![F4.ω, 0, F4.ω], ![F4.ω, 1, 1],
    ![F4.ω, 1, F4.ω + 1], ![F4.ω, F4.ω, 1], ![F4.ω, F4.ω, F4.ω + 1], ![F4.ω, F4.ω + 1, 1],
    ![F4.ω, F4.ω + 1, F4.ω + 1], ![F4.ω + 1, 0, 0], ![F4.ω + 1, 0, F4.ω + 1],
    ![F4.ω + 1, 1, 1], ![F4.ω + 1, 1, F4.ω], ![F4.ω + 1, F4.ω, 1], ![F4.ω + 1, F4.ω, F4.ω],
    ![F4.ω + 1, F4.ω + 1, 1], ![F4.ω + 1, F4.ω + 1, F4.ω]]

@[expose] def orbSU (k : Fin 27) : SU52 := wordSU (orbW k)

theorem cvec_orb_check : ∀ k : Fin 27, (fun i : Fin 3 => (wordMat (orbW k) *
    (x₃Mat 1 * x₄Mat 0 1) * invMat (wordMat (orbW k))) (![1, 2, 3] i) 0) = orbV k := by
  decide +kernel

theorem cvec_orb (k : Fin 27) : cvec (mat (orbSU k * b₀SU * (orbSU k)⁻¹)) = orbV k := by
  rw [← cvec_orb_check k, orbSU, mat_mul, mat_mul, mat_inv_eq_invMat, mat_wordSU, mat_b₀SU]
  rfl

theorem orbV_injective : Function.Injective orbV := by
  unfold orbV
  decide +kernel

theorem orbV_ne_zero (k : Fin 27) : orbV k ≠ 0 := by
  revert k
  unfold orbV
  decide +kernel

theorem orbV_complete : ∀ c : Fin 3 → F4, hnorm c = 0 → c ≠ 0 → ∃ k, orbV k = c := by
  unfold hnorm orbV
  decide +kernel

theorem genSU_comm_zSU (i : Fin 10) (hi : i ∈ ([0, 2, 3, 6, 7] : List (Fin 10))) :
    genSU i * zSU = zSU * genSU i := by
  refine ext_mat ?_
  rw [mat_mul, mat_mul, mat_genSU, mat_zSU]
  have key : ∀ i ∈ ([0, 2, 3, 6, 7] : List (Fin 10)),
      genMat i * x₄Mat 0 1 = x₄Mat 0 1 * genMat i := by
    decide +kernel
  exact key i hi

theorem orbSU_mem_CzSub (k : Fin 27) : orbSU k ∈ CzSub := by
  have hw : ∀ i ∈ orbW k, i ∈ ([0, 2, 3, 6, 7] : List (Fin 10)) := by
    revert k
    unfold orbW
    decide +kernel
  rw [orbSU, wordSU]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact mem_centralizer_singleton_iff.2 (genSU_comm_zSU i (hw i hi))

theorem e₂SU_mem_CzSub : e₂SU ∈ CzSub :=
  mem_centralizer_singleton_iff.2 (genSU_comm_zSU 3 (by decide))

theorem cvec_e₂_b₀SU : cvec (mat (e₂SU * b₀SU * e₂SU⁻¹)) = cvec (mat b₀SU) := by
  rw [mat_mul, mat_mul, mat_inv_eq_invMat, mat_e₂SU, mat_b₀SU]
  funext i
  fin_cases i <;> decide

theorem cvec_e₂_orb : cvec (mat (e₂SU * (orbSU 5 * b₀SU * (orbSU 5)⁻¹) * e₂SU⁻¹)) ≠ orbV 5 := by
  rw [orbSU, mat_mul, mat_mul, mat_inv_eq_invMat, mat_e₂SU, mat_mul, mat_mul,
    mat_inv_eq_invMat, mat_wordSU, mat_b₀SU]
  intro h
  have := congrFun h 1
  revert this
  decide

theorem fMat_comm_x₂_check : ∀ a b c : F4, ValidPair 0 a →
    (∃ β, fMat (a, b, c) * x₂Mat 1 * invMat (fMat (a, b, c)) * x₂Mat 1 = x₄Mat 0 β) →
    (∃ β, fMat (a, b, c) * x₂Mat F4.ω * invMat (fMat (a, b, c)) * x₂Mat F4.ω = x₄Mat 0 β) →
    a = 0 := by
  intro a b c
  rw [fMat_eq]
  revert a b c
  decide +kernel

theorem mem_A₁sub_of_comm_x₂ {f : SU52} (hf : f ∈ Fsub)
    (h1 : f * x₂SU 1 * f⁻¹ * (x₂SU 1)⁻¹ ∈ ZX₄sub)
    (hω : f * x₂SU F4.ω * f⁻¹ * (x₂SU F4.ω)⁻¹ ∈ ZX₄sub) : f ∈ A₁sub := by
  obtain ⟨⟨a, b, c⟩, ha, -, hp⟩ := exists_fMat_of_mem_Fsub hf
  have hinv : ∀ e : F4, mat (x₂SU e)⁻¹ = x₂Mat e := fun e => mat_inv_of_x₂ (mat_x₂SU e)
  have k : ∀ e : F4, f * x₂SU e * f⁻¹ * (x₂SU e)⁻¹ ∈ ZX₄sub →
      ∃ β, fMat (a, b, c) * x₂Mat e * invMat (fMat (a, b, c)) * x₂Mat e = x₄Mat 0 β := by
    intro e he
    obtain ⟨α, β, hα, hm⟩ := mem_x₄Sub.1 he
    subst hα
    refine ⟨β, ?_⟩
    rw [← hm, mat_mul, mat_mul, mat_mul, mat_inv_eq_invMat, hp, mat_x₂SU, hinv]
  have ha0 : a = 0 := fMat_comm_x₂_check a b c ha (k 1 h1) (k _ hω)
  subst ha0
  refine mem_A₁sub_of_shape fun i j hij => ?_
  rw [hp, fMat_eq]
  fin_cases i <;> fin_cases j <;> simp at hij ⊢

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
