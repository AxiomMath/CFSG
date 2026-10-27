module

public import CFSG.ClassicalInvolution.Generic.LineModel
public import CFSG.ClassicalInvolution.Phan.TorusAgree

public section

namespace CFSG.ClassicalInvolution.Generic

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary

section Matrices

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]

@[expose] noncomputable def omU12 : Su K p f 3 :=
  embSUid (unitaryInvolution K p f) 2 (rotSU _)

@[expose] noncomputable def omU23 : Su K p f 3 :=
  embSUid (unitaryInvolution K p f) 0 (rotSU _)⁻¹

variable {K p f}

theorem omU12_mem : omU12 K p f ∈ B12 K p f := ⟨rotSU _, rfl⟩

theorem omU23_mem : omU23 K p f ∈ B23 K p f := ⟨(rotSU _)⁻¹, rfl⟩

theorem coe_omU12 : (((omU12 K p f : Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
  rw [omU12, coe_embSUid]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embPair, rotSU, rotMat]

theorem coe_omU12_inv :
    ((((omU12 K p f)⁻¹ : Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
  rw [omU12, ← map_inv, coe_embSUid]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embPair, rotSU, rotMatInv]

theorem coe_omU23 : (((omU23 K p f : Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    !![1, 0, 0; 0, 0, 1; 0, -1, 0] := by
  rw [omU23, coe_embSUid]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embPair, rotSU, rotMatInv]

theorem coe_omU23_inv :
    ((((omU23 K p f)⁻¹ : Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, 0; 0, 0, -1; 0, 1, 0] := by
  rw [omU23, ← map_inv, inv_inv, coe_embSUid]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embPair, rotSU, rotMat]

theorem omU12_mul_omU23_pow_three : (omU12 K p f * omU23 K p f) ^ 3 = 1 := by
  refine Subtype.ext (Units.ext ?_)
  simp only [pow_succ, pow_zero, one_mul, Subgroup.coe_mul, Units.val_mul, coe_omU12, coe_omU23,
    Subgroup.coe_one, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem omU12_mul_embSUid_zero_mul_inv (A : Su K p f 2) :
    omU12 K p f * embSUid (unitaryInvolution K p f) 0 A * (omU12 K p f)⁻¹ =
      omU23 K p f * embSUid (unitaryInvolution K p f) 2 A * (omU23 K p f)⁻¹ := by
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, coe_omU12, coe_omU12_inv, coe_omU23, coe_omU23_inv,
    coe_embSUid, embPair]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem conjSub_omU12_B23 : conjSub (omU12 K p f) (B23 K p f) = conjSub (omU23 K p f) (B12 K p f) := by
  ext y
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨embSUid (unitaryInvolution K p f) 2 A, ⟨A, rfl⟩,
      (omU12_mul_embSUid_zero_mul_inv A).symm⟩
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨embSUid (unitaryInvolution K p f) 0 A, ⟨A, rfl⟩, omU12_mul_embSUid_zero_mul_inv A⟩

theorem rotSU_mul_torusTwo_mul_inv (s : normOne (unitaryInvolution K p f)) :
    rotSU (unitaryInvolution K p f) * torusTwo (unitaryInvolution K p f) s *
        (rotSU (unitaryInvolution K p f))⁻¹ = torusTwo (unitaryInvolution K p f) s⁻¹ := by
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, coe_torusTwo]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [rotSU, rotMat, rotMatInv]

theorem rotSU_inv_mul_torusTwo_mul (s : normOne (unitaryInvolution K p f)) :
    (rotSU (unitaryInvolution K p f))⁻¹ * torusTwo (unitaryInvolution K p f) s *
        rotSU (unitaryInvolution K p f) = torusTwo (unitaryInvolution K p f) s⁻¹ := by
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, coe_torusTwo]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [rotSU, rotMat, rotMatInv]

theorem omU12_conj_D12 {d : Su K p f 3} (hd : d ∈ D12 K p f) :
    omU12 K p f * d * (omU12 K p f)⁻¹ ∈ D12 K p f := by
  obtain ⟨u, rfl⟩ := mem_D12_iff.mp hd
  refine mem_D12_iff.mpr ⟨u⁻¹, ?_⟩
  rw [omU12, ← map_inv, ← map_mul, ← map_mul, rotSU_mul_torusTwo_mul_inv]

theorem omU12_inv_conj_D12 {d : Su K p f 3} (hd : d ∈ D12 K p f) :
    (omU12 K p f)⁻¹ * d * omU12 K p f ∈ D12 K p f := by
  obtain ⟨u, rfl⟩ := mem_D12_iff.mp hd
  refine mem_D12_iff.mpr ⟨u⁻¹, ?_⟩
  rw [omU12, ← map_inv, ← map_mul, ← map_mul, rotSU_inv_mul_torusTwo_mul]

theorem omU23_conj_D23 {d : Su K p f 3} (hd : d ∈ D23 K p f) :
    omU23 K p f * d * (omU23 K p f)⁻¹ ∈ D23 K p f := by
  obtain ⟨u, rfl⟩ := mem_D23_iff.mp hd
  refine mem_D23_iff.mpr ⟨u⁻¹, ?_⟩
  rw [omU23, ← map_inv, ← map_mul, ← map_mul, inv_inv, rotSU_inv_mul_torusTwo_mul]

theorem omU23_inv_conj_D23 {d : Su K p f 3} (hd : d ∈ D23 K p f) :
    (omU23 K p f)⁻¹ * d * omU23 K p f ∈ D23 K p f := by
  obtain ⟨u, rfl⟩ := mem_D23_iff.mp hd
  refine mem_D23_iff.mpr ⟨u⁻¹, ?_⟩
  rw [omU23, ← map_inv, ← map_mul, ← map_mul, inv_inv, rotSU_mul_torusTwo_mul_inv]

theorem omU12_not_mem_D12 : omU12 K p f ∉ D12 K p f := by
  intro h
  obtain ⟨u, hu⟩ := mem_D12_iff.mp h
  have h1 : torusTwo (unitaryInvolution K p f) u = rotSU (unitaryInvolution K p f) :=
    embSUid_injective _ 2 hu
  have h2 := congrFun (congrFun (congrArg
    (fun g : Su K p f 2 => ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h1) 0) 1
  simp [coe_torusTwo, rotSU, rotMat] at h2

theorem omU23_not_mem_D23 : omU23 K p f ∉ D23 K p f := by
  intro h
  obtain ⟨u, hu⟩ := mem_D23_iff.mp h
  have h1 : torusTwo (unitaryInvolution K p f) u = (rotSU (unitaryInvolution K p f))⁻¹ :=
    embSUid_injective _ 0 hu
  have h2 := congrFun (congrFun (congrArg
    (fun g : Su K p f 2 => ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h1) 0) 1
  simp [coe_torusTwo, rotSU, rotMatInv] at h2

end Matrices

section Line

@[expose] def UnitaryA2Pair (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]
    {G : Type} [Group G] (E P Q : Subgroup G) : Prop :=
  ∃ θ : Su K p f 3 →* G, θ.ker ≤ Subgroup.center (Su K p f 3) ∧ (B12 K p f).map θ = P ∧
    (B23 K p f).map θ = Q ∧ centPart P E = (D12 K p f).map θ ∧
    centPart Q E = (D23 K p f).map θ

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {F : Type} [Field F] {G : Type} [Group G]

theorem UnitaryA2Pair.unitaryBlockStandardPair {E P Q : Subgroup G}
    (h : UnitaryA2Pair K p f E P Q) :
    ∃ W : Subgroup G, UnitaryBlockStandardPair K p f W P Q := by
  obtain ⟨θ, hker, hP, hQ, -, -⟩ := h
  have e : ∀ B : Subgroup (Su K p f 3),
      B.map (MulAut.conj (1 : Su K p f 3)⁻¹).toMonoidHom = B := fun B => by
    rw [inv_one]
    exact conjSub_one B
  refine ⟨θ.range, θ, 1, rfl, hker, Or.inl ⟨?_, ?_⟩⟩
  · rw [e, hP]
  · rw [e, hQ]

theorem UnitaryA2Pair.isLine [Finite F] (hK : Nat.card K = (p ^ f) ^ 2) {E P Q : Subgroup G}
    (h : UnitaryA2Pair K p f E P Q) (hP : InSigma F E P) (hQ : InSigma F E Q)
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) : IsLine E P Q ∧ IsLine E Q P := by
  obtain ⟨θ, hker, hPB, hQB, hHP, hHQ⟩ := h
  refine isLine_of_model hP hQ hodd h5 hker ?_ ?_ D12_le_B12 D23_le_B23 hPB hQB hHP hHQ
    (fun d hd m hm => D12_conj_mem_B23 hK hd hm) (fun d hd m hm => D23_conj_mem_B12 hK hd hm)
    omU12_mem omU23_mem (fun d hd => omU12_conj_D12 hd) (fun d hd => omU12_inv_conj_D12 hd)
    (fun d hd => omU23_conj_D23 hd) (fun d hd => omU23_inv_conj_D23 hd) omU12_not_mem_D12
    omU23_not_mem_D23 conjSub_omU12_B23 omU12_mul_omU23_pow_three
  · intro b hb hz
    obtain ⟨A, rfl⟩ := hb
    rw [eq_one_of_embSUid_mem_center hK 2 hz, map_one]
  · intro b hb hz
    obtain ⟨A, rfl⟩ := hb
    rw [eq_one_of_embSUid_mem_center hK 0 hz, map_one]

theorem a2Dichotomy_of_unitary {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}
    [Finite F] (Fr : ToralFrame F Ω E S) (hK : Nat.card K = (p ^ f) ^ 2)
    (h : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q →
      Commutes P Q ∨ UnitaryA2Pair K p f E P Q ∨ UnitaryA2Pair K p f E Q P) :
    A2Dichotomy E S := by
  intro P hP Q hQ hPQ
  rcases h P hP Q hQ hPQ with hc | hp | hp
  · exact Or.inl hc
  · exact Or.inr (hp.isLine hK (Fr.inSigma hP) (Fr.inSigma hQ) Fr.odd Fr.five).1
  · exact Or.inr (hp.isLine hK (Fr.inSigma hQ) (Fr.inSigma hP) Fr.odd Fr.five).2

end Line

section DiagU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] noncomputable def diagU2 (σ : K ≃+* K) (a b : normOne σ) : GL (Fin 2) K :=
  diagGL ![(a : Kˣ), (b : Kˣ)]

@[expose] noncomputable def diagU3 (σ : K ≃+* K) (a b : normOne σ) : GL (Fin 3) K :=
  diagGL ![(a : Kˣ), (b : Kˣ), 1]

omit [Finite K] in
theorem conjTr_diagU2 (σ : K ≃+* K) (a b : normOne σ) :
    conjTr σ ((diagU2 σ a b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((diagU2 σ a b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [diagU2, coe_diagGL, conjTr_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simpa using (mem_normOne σ).mp a.2
  · simpa using (mem_normOne σ).mp b.2

omit [Finite K] in
theorem conjTr_diagU3 (σ : K ≃+* K) (a b : normOne σ) :
    conjTr σ ((diagU3 σ a b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((diagU3 σ a b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [diagU3, coe_diagGL, conjTr_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simpa using (mem_normOne σ).mp a.2
  · simpa using (mem_normOne σ).mp b.2
  · simp

@[expose] noncomputable def diagConj2U (hK : Nat.card K = (p ^ f) ^ 2)
    (a b : normOne (unitaryInvolution K p f)) (A : Su K p f 2) : Su K p f 2 :=
  ⟨diagU2 _ a b * A * (diagU2 _ a b)⁻¹,
    conj_mem_SUid (unitaryInvolution_involutive hK) (conjTr_diagU2 _ a b) A.2⟩

@[expose] noncomputable def diagConj3U (hK : Nat.card K = (p ^ f) ^ 2)
    (a b : normOne (unitaryInvolution K p f)) (A : Su K p f 3) : Su K p f 3 :=
  ⟨diagU3 _ a b * A * (diagU3 _ a b)⁻¹,
    conj_mem_SUid (unitaryInvolution_involutive hK) (conjTr_diagU3 _ a b) A.2⟩

theorem diagConj3U_embSUid_two (hK : Nat.card K = (p ^ f) ^ 2)
    (a b : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    diagConj3U hK a b (embSUid (unitaryInvolution K p f) 2 A) =
      embSUid (unitaryInvolution K p f) 2 (diagConj2U hK a b A) := by
  refine Subtype.ext (Units.ext ?_)
  simp only [diagConj3U, diagConj2U, Units.val_mul, coe_embSUid, diagU3, diagU2,
    coe_diagGL, coe_diagGL_inv, embPair]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]

theorem diagConj3U_embSUid_zero (hK : Nat.card K = (p ^ f) ^ 2)
    (a b : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    diagConj3U hK a b (embSUid (unitaryInvolution K p f) 0 A) =
      embSUid (unitaryInvolution K p f) 0 (diagConj2U hK b 1 A) := by
  refine Subtype.ext (Units.ext ?_)
  simp only [diagConj3U, diagConj2U, Units.val_mul, coe_embSUid, diagU3, diagU2,
    coe_diagGL, coe_diagGL_inv, embPair]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]

theorem diagConj2U_self (hK : Nat.card K = (p ^ f) ^ 2) (a : normOne (unitaryInvolution K p f))
    (A : Su K p f 2) : diagConj2U hK a a A = A := by
  refine Subtype.ext (Units.ext ?_)
  simp only [diagConj2U, diagU2, Units.val_mul, coe_diagGL, coe_diagGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply] <;> field_simp

theorem diagConj2U_torusTwo (hK : Nat.card K = (p ^ f) ^ 2)
    (a b s : normOne (unitaryInvolution K p f)) :
    diagConj2U hK a b (torusTwo (unitaryInvolution K p f) s) =
      torusTwo (unitaryInvolution K p f) s := by
  refine Subtype.ext (Units.ext ?_)
  simp only [diagConj2U, diagU2, Units.val_mul, coe_diagGL, coe_diagGL_inv,
    coe_torusTwo]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply] <;> field_simp

theorem mem_range_torusTwo_of_diagConj2U_eq (hK : Nat.card K = (p ^ f) ^ 2)
    {a b : normOne (unitaryInvolution K p f)} (hab : a ≠ b) {A : Su K p f 2}
    (h : diagConj2U hK a b A = A) : A ∈ (torusTwo (unitaryInvolution K p f)).range := by
  have h' := congrArg (fun g : Su K p f 2 => ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h
  simp only [diagConj2U, diagU2, Units.val_mul, coe_diagGL, coe_diagGL_inv]
    at h'
  have h01 := congrFun (congrFun h' 0) 1
  have h10 := congrFun (congrFun h' 1) 0
  simp [Matrix.mul_apply, Matrix.diagonal_apply] at h01 h10
  have hb : ((b : Kˣ) : K) * ((b : Kˣ) : K)⁻¹ = 1 := mul_inv_cancel₀ (Units.ne_zero _)
  have ha : ((a : Kˣ) : K) * ((a : Kˣ) : K)⁻¹ = 1 := mul_inv_cancel₀ (Units.ne_zero _)
  have hne : ((a : Kˣ) : K) - ((b : Kˣ) : K) ≠ 0 :=
    sub_ne_zero.mpr (fun h => hab (Subtype.ext (Units.ext h)))
  have hne' : ((b : Kˣ) : K) - ((a : Kˣ) : K) ≠ 0 :=
    sub_ne_zero.mpr (fun h => hab (Subtype.ext (Units.ext h.symm)))
  have e01 : (((a : Kˣ) : K) - ((b : Kˣ) : K)) *
      ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    linear_combination (((b : Kˣ) : K)) * h01 -
      (((a : Kˣ) : K) * ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1) * hb
  have e10 : (((b : Kˣ) : K) - ((a : Kˣ) : K)) *
      ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    linear_combination (((a : Kˣ) : K)) * h10 -
      (((b : Kˣ) : K) * ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0) * ha
  exact mem_range_torusTwo_of_offDiag A ((mul_eq_zero.mp e01).resolve_left hne)
    ((mul_eq_zero.mp e10).resolve_left hne')

@[expose] def DiagActionU {G : Type} [Group G] (hK : Nat.card K = (p ^ f) ^ 2)
    (θ : Su K p f 3 →* G) (E : Subgroup G) : Prop :=
  ∀ e ∈ E, ∃ a b : normOne (unitaryInvolution K p f), ∀ x : Su K p f 3,
    e * θ x * e⁻¹ = θ (diagConj3U hK a b x)

end DiagU

section DiagUPair

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {F : Type} [Field F] {G : Type} [Group G]

theorem unitaryA2Pair_of_diagAction (hK : Nat.card K = (p ^ f) ^ 2) {E P Q : Subgroup G}
    {θ : Su K p f 3 →* G} (hker : θ.ker ≤ Subgroup.center (Su K p f 3))
    (hPB : (B12 K p f).map θ = P) (hQB : (B23 K p f).map θ = Q)
    (hdiag : DiagActionU hK θ E) (hPS : InSigma F E P) (hQS : InSigma F E Q) :
    UnitaryA2Pair K p f E P Q := by
  refine ⟨θ, hker, hPB, hQB, ?_, ?_⟩
  · have hinj := comp_embSUid_injective hK hker 2
    obtain ⟨e₀, he₀, he₀'⟩ := hPS.exists_mem_not_mem_axis
    obtain ⟨a₀, b₀, h₀⟩ := hdiag e₀ he₀
    have hab : a₀ ≠ b₀ := by
      rintro rfl
      apply he₀'
      rw [mem_axisSub_iff]
      refine ⟨he₀, fun k hk => ?_⟩
      rw [← hPB] at hk
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hk
      have h1 := h₀ (embSUid (unitaryInvolution K p f) 2 A)
      rw [diagConj3U_embSUid_two, diagConj2U_self] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    ext c
    constructor
    · intro hc
      rw [mem_centPart_iff] at hc
      obtain ⟨hcP, hcE⟩ := hc
      rw [← hPB] at hcP
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hcP
      have h1 := h₀ (embSUid (unitaryInvolution K p f) 2 A)
      rw [diagConj3U_embSUid_two, mul_inv_eq_iff_eq_mul.mpr (hcE e₀ he₀)] at h1
      have h2 : diagConj2U hK a₀ b₀ A = A := hinj h1.symm
      exact ⟨embSUid (unitaryInvolution K p f) 2 A,
        ⟨A, mem_range_torusTwo_of_diagConj2U_eq hK hab h2, rfl⟩, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      rw [mem_centPart_iff, ← hPB]
      refine ⟨⟨d, D12_le_B12 hd, rfl⟩, fun e he => ?_⟩
      obtain ⟨a, b, h⟩ := hdiag e he
      obtain ⟨A, hA, rfl⟩ := hd
      have h1 := h (embSUid (unitaryInvolution K p f) 2 A)
      rw [diagConj3U_embSUid_two] at h1
      obtain ⟨u, rfl⟩ := mem_diagTorus2_iff.mp hA
      rw [diagConj2U_torusTwo] at h1
      exact mul_inv_eq_iff_eq_mul.mp h1
  · have hinj := comp_embSUid_injective hK hker 0
    obtain ⟨e₀, he₀, he₀'⟩ := hQS.exists_mem_not_mem_axis
    obtain ⟨a₀, b₀, h₀⟩ := hdiag e₀ he₀
    have hab : b₀ ≠ 1 := by
      rintro rfl
      apply he₀'
      rw [mem_axisSub_iff]
      refine ⟨he₀, fun k hk => ?_⟩
      rw [← hQB] at hk
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hk
      have h1 := h₀ (embSUid (unitaryInvolution K p f) 0 A)
      rw [diagConj3U_embSUid_zero, diagConj2U_self] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    ext c
    constructor
    · intro hc
      rw [mem_centPart_iff] at hc
      obtain ⟨hcQ, hcE⟩ := hc
      rw [← hQB] at hcQ
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hcQ
      have h1 := h₀ (embSUid (unitaryInvolution K p f) 0 A)
      rw [diagConj3U_embSUid_zero, mul_inv_eq_iff_eq_mul.mpr (hcE e₀ he₀)] at h1
      have h2 : diagConj2U hK b₀ 1 A = A := hinj h1.symm
      exact ⟨embSUid (unitaryInvolution K p f) 0 A,
        ⟨A, mem_range_torusTwo_of_diagConj2U_eq hK hab h2, rfl⟩, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      rw [mem_centPart_iff, ← hQB]
      refine ⟨⟨d, D23_le_B23 hd, rfl⟩, fun e he => ?_⟩
      obtain ⟨a, b, h⟩ := hdiag e he
      obtain ⟨A, hA, rfl⟩ := hd
      have h1 := h (embSUid (unitaryInvolution K p f) 0 A)
      rw [diagConj3U_embSUid_zero] at h1
      obtain ⟨u, rfl⟩ := mem_diagTorus2_iff.mp hA
      rw [diagConj2U_torusTwo] at h1
      exact mul_inv_eq_iff_eq_mul.mp h1

end DiagUPair

end CFSG.ClassicalInvolution.Generic
