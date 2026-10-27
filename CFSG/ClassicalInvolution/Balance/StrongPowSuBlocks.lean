module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinearBlocks
public import CFSG.ClassicalInvolution.Models.LinearPairs.Frame

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear (compIndicator blockOn blockOn_one
  blockOn_mul det_blockOn blockOn_apply_mem blockOn_apply_not_mem coordSet mem_coordSet
  compIndicator_mul_apply mul_compIndicator_apply compIndicator_apply)

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def blockOnHom (J : Finset (Fin n)) :
    Matrix (Fin J.card) (Fin J.card) K →* Matrix (Fin n) (Fin n) K where
  toFun := blockOn K J
  map_one' := blockOn_one J
  map_mul' := blockOn_mul J

@[expose] noncomputable def blockGLOn (J : Finset (Fin n)) : GL (Fin J.card) K →* GL (Fin n) K :=
  Units.map (blockOnHom J)

theorem coe_blockGLOn (J : Finset (Fin n)) (g : GL (Fin J.card) K) :
    ((blockGLOn J g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      blockOn K J (g : Matrix (Fin J.card) (Fin J.card) K) := rfl


theorem blockOn_injective (J : Finset (Fin n)) {X Y : Matrix (Fin J.card) (Fin J.card) K}
    (h : blockOn K J X = blockOn K J Y) : X = Y := by
  ext a b
  have h2 := congrFun (congrFun h (J.equivFin.symm a)) (J.equivFin.symm b)
  rw [blockOn_apply_mem J _ (J.equivFin.symm a).2 (J.equivFin.symm b).2,
    blockOn_apply_mem J _ (J.equivFin.symm a).2 (J.equivFin.symm b).2] at h2
  simpa using h2

section Unitary

variable [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem conjTr_blockOn (J : Finset (Fin n)) (X : Matrix (Fin J.card) (Fin J.card) K) :
    conjTr (unitaryInvolution K p f) (blockOn K J X) =
      blockOn K J (conjTr (unitaryInvolution K p f) X) := by
  ext i j
  simp only [conjTr, transpose_apply, map_apply]
  by_cases hij : i ∈ J ∧ j ∈ J
  · rw [blockOn_apply_mem J _ hij.2 hij.1, blockOn_apply_mem J _ hij.1 hij.2]
    simp
  · have h1 : j ∉ J ∨ i ∉ J := by tauto
    have h2 : i ∉ J ∨ j ∉ J := by tauto
    rw [blockOn_apply_not_mem J _ h1, blockOn_apply_not_mem J _ h2]
    by_cases h : i = j <;> simp [h, eq_comm]

theorem blockGLOn_mem_SUid (J : Finset (Fin n)) {g : GL (Fin J.card) K}
    (hg : g ∈ SUid (unitaryInvolution K p f) J.card) :
    blockGLOn J g ∈ SUid (unitaryInvolution K p f) n := by
  obtain ⟨hdet, hiso⟩ := hg
  refine ⟨by rw [coe_blockGLOn, det_blockOn, hdet], ?_⟩
  rw [coe_blockGLOn, conjTr_blockOn, ← blockOn_mul, hiso, blockOn_one]

variable (K p f) in
@[expose] noncomputable def blockSUOn (J : Finset (Fin n)) : Su K p f J.card →* Su K p f n :=
  ((blockGLOn J).comp (SUid (unitaryInvolution K p f) J.card).subtype).codRestrict _
    fun g => blockGLOn_mem_SUid J g.2

theorem coe_coe_blockSUOn (J : Finset (Fin n)) (X : Su K p f J.card) :
    (((blockSUOn K p f J X : Su K p f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      blockOn K J (((X : Su K p f J.card) : GL (Fin J.card) K) :
        Matrix (Fin J.card) (Fin J.card) K) :=
  rfl

theorem blockSUOn_injective (J : Finset (Fin n)) : Function.Injective (blockSUOn K p f J) := by
  intro X Y h
  have h1 := congrArg (fun g : Su K p f n => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h
  simp only [coe_coe_blockSUOn] at h1
  exact Subtype.ext (Units.ext (blockOn_injective J h1))

variable (K p f) in
@[expose] noncomputable def coordBlockSU (J : Finset (Fin n)) : Subgroup (Su K p f n) :=
  (blockSUOn K p f J).range


theorem mem_coordBlockSU_iff {J : Finset (Fin n)} {g : Su K p f n} :
    g ∈ coordBlockSU K p f J ↔ ∀ i j, (i ∉ J ∨ j ∉ J) →
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = if i = j then 1 else 0 := by
  constructor
  · rintro ⟨X, rfl⟩ i j hij
    rw [coe_coe_blockSUOn, blockOn_apply_not_mem J _ hij]
  · intro h
    set G : Matrix (Fin n) (Fin n) K := ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hG
    set X : Matrix (Fin J.card) (Fin J.card) K :=
      Matrix.of fun a b => G (J.equivFin.symm a) (J.equivFin.symm b) with hX
    have hXg : blockOn K J X = G := by
      ext i j
      by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
      · rw [blockOn_apply_mem J X hi hj, hX, of_apply, Equiv.symm_apply_apply,
          Equiv.symm_apply_apply]
      · rw [blockOn_apply_not_mem J X (Or.inr hj), h i j (Or.inr hj)]
      · rw [blockOn_apply_not_mem J X (Or.inl hi), h i j (Or.inl hi)]
      · rw [blockOn_apply_not_mem J X (Or.inl hi), h i j (Or.inl hi)]
    have hdet : X.det = 1 := by
      rw [← det_blockOn J X, hXg]
      exact g.2.1
    have hunit : conjTr (unitaryInvolution K p f) X * X = 1 := by
      apply blockOn_injective J
      rw [blockOn_mul, ← conjTr_blockOn, hXg, blockOn_one]
      exact g.2.2
    refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero X (by rw [hdet]; exact one_ne_zero),
      hdet, hunit⟩, ?_⟩
    exact Subtype.ext (Units.ext hXg)

theorem mem_coordBlockSU_iff_indicator {J : Finset (Fin n)} {g : Su K p f n} :
    g ∈ coordBlockSU K p f J ↔
      compIndicator K J * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = compIndicator K J ∧
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compIndicator K J =
          compIndicator K J := by
  rw [mem_coordBlockSU_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · ext i j
      rw [compIndicator_mul_apply, compIndicator_apply]
      by_cases hi : i ∈ J
      · simp [hi]
      · simp only [hi, ite_false, not_false_eq_true, true_and]
        exact h i j (Or.inl hi)
    · ext i j
      rw [mul_compIndicator_apply, compIndicator_apply]
      by_cases hj : j ∈ J
      · by_cases hij : i = j
        · subst hij
          simp [hj]
        · simp [hj, hij]
      · simp only [hj, ite_false]
        rw [h i j (Or.inr hj)]
        by_cases hij : i = j
        · subst hij
          simp [hj]
        · simp [hij]
  · rintro ⟨h1, h2⟩ i j hij
    rcases hij with hi | hj
    · have := congrFun (congrFun h1 i) j
      simp only [compIndicator_mul_apply, compIndicator_apply, hi, not_false_eq_true, true_and,
        ite_false] at this
      rw [this]
    · have := congrFun (congrFun h2 i) j
      simp only [mul_compIndicator_apply, compIndicator_apply, hj, ite_false] at this
      rw [this]
      by_cases hij : i = j
      · subst hij
        simp [hj]
      · simp [hij]

theorem diagonal_mul_comm_of_mem_coordBlockSU {J : Finset (Fin n)} {g : Su K p f n}
    (hg : g ∈ coordBlockSU K p f J) {v : Fin n → K} (hv : ∀ i ∈ J, ∀ j ∈ J, v i = v j) :
    diagonal v * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * diagonal v := by
  rw [mem_coordBlockSU_iff] at hg
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases hij : i ∈ J ∧ j ∈ J
  · rw [hv i hij.1 j hij.2, mul_comm]
  · rw [hg i j (by tauto)]
    split_ifs with h
    · subst h
      rw [mul_one, one_mul]
    · rw [mul_zero, zero_mul]

theorem isQuasisimple_su_of_two_le (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {m : ℕ}
    (hm : 2 ≤ m) : CFSG.IsQuasisimple (Su K p f m) := by
  by_cases h2 : m = 2
  · subst h2
    obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
    obtain ⟨P, hP⟩ := exists_wittMatrix hK 2
    have hsl : CFSG.Open.IsQuasisimple
        (Matrix.SpecialLinearGroup (Fin 2) (CFSG.LieType.Steinberg.fixedSubfield K p f)) :=
      CFSG.ClassicalInvolution.Balance.StrongBalance.Linear.isQuasisimple_SL_of_two_le le_rfl
        (by rw [CFSG.LieType.Steinberg.card_fixedSubfield hK]; omega)
    exact isQuasisimple_of_mulEquiv
      ((CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).trans (conjEquiv P hP))
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hsl)
  · have hm3 : 3 ≤ m := by omega
    have hdq : (m, p ^ f) ≠ (3, 2) := fun h => by
      have := congrArg Prod.snd h
      simp only at this
      omega
    exact isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr (SUid_eq_statedSU hK m)).symm
      (isQuasisimple_statedSU_of_card hK hm3 hdq).1

theorem isQuasisimple_coordBlockSU (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    {J : Finset (Fin n)} (hJ : 2 ≤ J.card) : CFSG.Open.IsQuasisimple (coordBlockSU K p f J) :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
    (isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (blockSUOn_injective (K := K) (p := p)
      (f := f) J)) (isQuasisimple_su_of_two_le hK hq hJ))


theorem conj_mem_coordBlockSU {J : Finset (Fin n)} {y g : Su K p f n}
    (hyP : compIndicator K J * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compIndicator K J)
    (hg : g ∈ coordBlockSU K p f J) : y * g * y⁻¹ ∈ coordBlockSU K p f J := by
  rw [mem_coordBlockSU_iff_indicator] at hg ⊢
  obtain ⟨hg1, hg2⟩ := hg
  set P := compIndicator K J with hP
  set Y : Matrix (Fin n) (Fin n) K := ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hY
  set G : Matrix (Fin n) (Fin n) K := ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hG
  set Yi : Matrix (Fin n) (Fin n) K :=
    (((y⁻¹ : Su K p f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hYi
  have h1 : Y * Yi = 1 := by
    have := congrArg (fun z : Su K p f n => ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (mul_inv_cancel y)
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] at this
    exact this
  have h2 : Yi * Y = 1 := by
    have := congrArg (fun z : Su K p f n => ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (inv_mul_cancel y)
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] at this
    exact this
  have hYiP : P * Yi = Yi * P := by
    calc P * Yi = Yi * Y * P * Yi := by rw [h2, Matrix.one_mul]
      _ = Yi * (Y * P) * Yi := by simp only [Matrix.mul_assoc]
      _ = Yi * (P * Y) * Yi := by rw [hyP]
      _ = Yi * P * (Y * Yi) := by simp only [Matrix.mul_assoc]
      _ = Yi * P := by rw [h1, Matrix.mul_one]
  have hcoe : ((y * g * y⁻¹ : Su K p f n) : GL (Fin n) K) = ((y : GL (Fin n) K) * g * y⁻¹ :
      GL (Fin n) K) := rfl
  have hM : (((y * g * y⁻¹ : Su K p f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Y * G * Yi := by
    rw [hcoe]
    simp [hY, hG, hYi]
  rw [hM]
  refine ⟨?_, ?_⟩
  · calc P * (Y * G * Yi) = Y * (P * G) * Yi := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hyP]; simp only [Matrix.mul_assoc]
      _ = Y * (P * Yi) := by rw [hg1, Matrix.mul_assoc]
      _ = Y * (Yi * P) := by rw [hYiP]
      _ = P := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  · calc (Y * G * Yi) * P = Y * (G * P) * Yi := by
          rw [Matrix.mul_assoc, ← hYiP]; simp only [Matrix.mul_assoc]
      _ = (Y * P) * Yi := by rw [hg2]
      _ = (P * Y) * Yi := by rw [hyP]
      _ = P := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

section Sign

open CFSG.ClassicalInvolution.Models (signOf)

omit [Finite K] in
theorem signOf_true' : signOf K true = (1 : K) := by simp [signOf]

omit [Finite K] in
theorem signOf_false' : signOf K false = (-1 : K) := by simp [signOf]

theorem entry_eq_zero_of_comm_sign (h2 : (2 : K) ≠ 0) {σ : Fin n → Bool} {D y : Su K p f n}
    (hD : ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal fun i => signOf K (σ i))
    (hy : D * y = y * D) {i j : Fin n} (hij : σ i ≠ σ j) :
    ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0 := by
  have h := congrArg (fun z : Su K p f n => ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) hy
  simp only [Subgroup.coe_mul, Units.val_mul, hD, diagonal_mul, mul_diagonal] at h
  have h2' : (2 : K) * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0 := by
    cases hi : σ i <;> cases hj : σ j
    · exact absurd (hi.trans hj.symm) hij
    · rw [hi, hj, signOf_true', signOf_false'] at h
      linear_combination (-1 : K) * h
    · rw [hi, hj, signOf_true', signOf_false'] at h
      linear_combination h
    · exact absurd (hi.trans hj.symm) hij
  exact (mul_eq_zero.mp h2').resolve_left h2

theorem compIndicator_comm_of_comm_sign (h2 : (2 : K) ≠ 0) {σ : Fin n → Bool} {D y : Su K p f n}
    (hD : ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal fun i => signOf K (σ i))
    (hy : D * y = y * D) (b : Bool) :
    compIndicator K (coordSet σ b) * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compIndicator K (coordSet σ b) := by
  ext i j
  rw [compIndicator_mul_apply, mul_compIndicator_apply]
  by_cases hij : σ i = σ j
  · have : (i ∈ coordSet σ b) ↔ (j ∈ coordSet σ b) := by
      rw [mem_coordSet, mem_coordSet, hij]
    by_cases hi : i ∈ coordSet σ b
    · simp [hi, this.mp hi]
    · simp [hi, mt this.mpr hi]
  · rw [entry_eq_zero_of_comm_sign h2 hD hy hij]
    simp

theorem comm_of_mem_coordBlockSU {σ : Fin n → Bool} {D s : Su K p f n}
    (hD : ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal fun i => signOf K (σ i))
    (b : Bool) (hs : s ∈ coordBlockSU K p f (coordSet σ b)) : D * s = s * D := by
  apply Subtype.ext
  apply Units.ext
  rw [mem_coordBlockSU_iff] at hs
  simp only [Subgroup.coe_mul, Units.val_mul, hD]
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases hij : i ∈ coordSet σ b ∧ j ∈ coordSet σ b
  · rw [mem_coordSet, mem_coordSet] at hij
    rw [hij.1, ← hij.2]
    ring
  · have hor : i ∉ coordSet σ b ∨ j ∉ coordSet σ b := by tauto
    rw [hs i j hor]
    by_cases h : i = j
    · subst h
      simp
    · simp [h]

theorem isComponentOf_block_centralizer_su (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (h2 : (2 : K) ≠ 0) {X : Type} [Group X] (Ψ : Su K p f n →* X)
    (hker : Ψ.ker ≤ Subgroup.center (Su K p f n)) (e : X) (σ : Fin n → Bool) (D : Su K p f n)
    (hD : ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal fun i => signOf K (σ i))
    (hf : ∀ y, e * Ψ y * e⁻¹ = Ψ (D * y * D⁻¹)) (b : Bool) (hcard : 2 ≤ (coordSet σ b).card) :
    CFSG.Open.IsComponentOf ((coordBlockSU K p f (coordSet σ b)).map Ψ)
      (Ψ.range ⊓ Subgroup.centralizer ({e} : Set X)) := by
  have hQ : CFSG.Open.IsComponentOf (coordBlockSU K p f (coordSet σ b))
      (CFSG.ClassicalInvolution.Balance.fixedGroup (MulAut.conj D)) := by
    have hle : coordBlockSU K p f (coordSet σ b) ≤
        CFSG.ClassicalInvolution.Balance.fixedGroup (MulAut.conj D) := by
      intro s hs
      rw [CFSG.ClassicalInvolution.Balance.mem_fixedGroup, MulAut.conj_apply,
        mul_inv_eq_iff_eq_mul]
      exact comm_of_mem_coordBlockSU hD b hs
    refine ⟨hle, CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hle ?_,
      isQuasisimple_coordBlockSU hK hq hcard⟩
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro s y hs hy
    have hyD : D * y = y * D := by
      have := CFSG.ClassicalInvolution.Balance.mem_fixedGroup.mp hy
      rwa [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at this
    exact conj_mem_coordBlockSU (compIndicator_comm_of_comm_sign h2 hD hyD b) hs
  have hmain := CFSG.ClassicalInvolution.Balance.isComponentOf_map_centralizer hker 1 e
    (MulAut.conj D) (fun y => by simpa [MulAut.conj_apply] using hf y) hQ
  have e1 : (MulAut.conj (1 : Su K p f n)).toMonoidHom = MonoidHom.id _ := by
    ext; simp
  rwa [e1, MonoidHom.comp_id] at hmain

end Sign

end Unitary

end CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
