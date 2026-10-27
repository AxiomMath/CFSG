module

public import CFSG.RankThree.SteinbergR3ESL3RootPermutingFixed

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG.RankThree.Classical2 CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

theorem mnSyl_exists_subfield {Ω : Type} [Field Ω] [IsAlgClosed Ω] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP Ω ℓ] (hf : 1 ≤ f) :
    ∃ K : Subfield Ω, Nat.card K = (ℓ ^ f) ^ 2 ∧ ∀ c : Ω, c ∈ K ↔ c ^ (ℓ ^ f) ^ 2 = c := by
  set K : Subfield Ω := (iterateFrobenius Ω ℓ (f * 2)).eqLocusField (RingHom.id Ω) with hKdef
  have hmem : ∀ c : Ω, c ∈ K ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [hKdef, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply, pow_mul]
  refine ⟨K, ?_, hmem⟩
  have hq : 1 < (ℓ ^ f) ^ 2 :=
    Nat.one_lt_pow two_ne_zero (Nat.one_lt_pow (by omega) (Fact.out : ℓ.Prime).one_lt)
  set P : Polynomial Ω := Polynomial.X ^ ((ℓ ^ f) ^ 2) - Polynomial.X with hPdef
  have hP : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero Ω hq
  have hset : (K : Set Ω) = P.rootSet Ω := by
    ext c
    rw [SetLike.mem_coe, hmem, Polynomial.mem_rootSet]
    constructor
    · intro h
      exact ⟨hP, by simp [hPdef, h]⟩
    · rintro ⟨-, h⟩
      simpa [hPdef, sub_eq_zero] using h
  have h1 : Nat.card K = Nat.card (P.rootSet Ω) := Nat.card_congr (Set.equivOfEq hset)
  have hdvd : ℓ ∣ (ℓ ^ f) ^ 2 := dvd_pow (dvd_pow_self ℓ (by omega)) two_ne_zero
  rw [h1, Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree (galois_poly_separable ℓ _ hdvd) (IsAlgClosed.splits _),
    FiniteField.X_pow_card_sub_X_natDegree_eq Ω hq]

theorem mnSyl_image_SUid {F Ω : Type} [Field F] [Finite F] [Field Ω] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP F ℓ] (ι : F →+* Ω) (hrange : ∀ c : Ω, c ∈ Set.range ι ↔ c ^ (ℓ ^ f) ^ 2 = c)
    (n : ℕ) :
    GeneralLinearGroup.map ι '' (SUid (unitaryInvolution F ℓ f) n : Set (GL (Fin n) F)) =
      unitarySet (ℓ ^ f) n := by
  have hmap : ∀ B : GL (Fin n) F,
      ((GeneralLinearGroup.map ι B : GL (Fin n) Ω) : Matrix (Fin n) (Fin n) Ω) =
        (B : Matrix (Fin n) (Fin n) F).map ι := fun B => rfl
  have hσ : ∀ c : F, ι (unitaryInvolution F ℓ f c) = ι c ^ ℓ ^ f := fun c => by
    rw [unitaryInvolution_apply, map_pow]
  have hconj : ∀ A : Matrix (Fin n) (Fin n) F, (conjTr (unitaryInvolution F ℓ f) A).map ι =
      ((A.map ι).map (· ^ ℓ ^ f))ᵀ := fun A => by
    ext i j
    simp only [conjTr, Matrix.map_apply, Matrix.transpose_apply]
    exact hσ _
  ext X
  constructor
  · rintro ⟨B, hB, rfl⟩
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · rw [hmap, Matrix.map_apply]
      exact (hrange _).mp ⟨_, rfl⟩
    · rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hB.1, map_one]
    · rw [hmap, ← hconj]
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => M.map ι) hB.2
      simpa [Matrix.map_mul] using h
  · rintro ⟨h1, h2, h3⟩
    have hX : ∀ i j, ∃ b : F, ι b = (X : Matrix (Fin n) (Fin n) Ω) i j := fun i j =>
      (hrange _).mpr (h1 i j)
    choose B₁ hB₁ using hX
    obtain ⟨B₀, hB₀map⟩ : ∃ B₀ : Matrix (Fin n) (Fin n) F,
        B₀.map ι = (X : Matrix (Fin n) (Fin n) Ω) :=
      ⟨Matrix.of B₁, by
        ext i j
        exact hB₁ i j⟩
    have hdet : B₀.det = 1 := by
      apply ι.injective
      rw [map_one, RingHom.map_det, RingHom.mapMatrix_apply, hB₀map, h2]
    have hne : B₀.det ≠ 0 := by
      rw [hdet]
      exact one_ne_zero
    refine ⟨GeneralLinearGroup.mkOfDetNeZero B₀ hne, ⟨?_, ?_⟩, ?_⟩
    · rw [GeneralLinearGroup.val_mkOfDetNeZero]
      exact hdet
    · rw [GeneralLinearGroup.val_mkOfDetNeZero]
      apply Matrix.map_injective ι.injective
      simp only [Matrix.map_mul, hconj, hB₀map, Matrix.map_one ι (map_zero ι) (map_one ι)]
      exact h3
    · apply Units.ext
      rw [hmap, GeneralLinearGroup.val_mkOfDetNeZero]
      exact hB₀map

theorem mnSyl_card_unitarySet_three {Ω : Type} [Field Ω] [IsAlgClosed Ω] {ℓ f : ℕ}
    [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f) :
    Nat.card (unitarySet (ℓ ^ f) 3 : Set (GL (Fin 3) Ω)) =
      (ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) := by
  obtain ⟨K, hKcard, hKmem⟩ := mnSyl_exists_subfield (Ω := Ω) (ℓ := ℓ) hf
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hKcard]
    exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero))
  have hrange : ∀ c : Ω, c ∈ Set.range K.subtype ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [← hKmem]
    exact ⟨fun ⟨b, hb⟩ => hb ▸ b.2, fun h => ⟨⟨c, h⟩, rfl⟩⟩
  have hinj : Function.Injective
      (GeneralLinearGroup.map K.subtype : GL (Fin 3) K →* GL (Fin 3) Ω) :=
    fun A B h => Units.ext (Matrix.map_injective K.subtype_injective (congrArg Units.val h))
  rw [← mnSyl_image_SUid K.subtype hrange 3 (ℓ := ℓ) (f := f), Nat.card_image_of_injective hinj,
    SetLike.coe_sort_coe]
  obtain ⟨P₃, hP₃⟩ := exists_wittMatrix hKcard 3
  rw [← Nat.card_congr (conjEquiv P₃ hP₃).toEquiv, CFSG.LieType.Steinberg.card_SU_three hKcard]

theorem mnSyl_card_eq_of_conj {Ω : Type} [Field Ω] {n : ℕ} (S : Subgroup SL(n, Ω))
    (U : Set (GL (Fin n) Ω)) (hU : ∀ Y ∈ U, (Y : Matrix (Fin n) (Fin n) Ω).det = 1)
    (H : SL(n, Ω))
    (hH : ∀ X : SL(n, Ω), X ∈ S ↔ ∃ Y ∈ U, SpecialLinearGroup.toGL X =
      SpecialLinearGroup.toGL H * Y * (SpecialLinearGroup.toGL H)⁻¹) :
    Nat.card S = Nat.card U := by
  set c : S → GL (Fin n) Ω := fun X =>
    (SpecialLinearGroup.toGL H)⁻¹ * SpecialLinearGroup.toGL (X : SL(n, Ω)) *
      SpecialLinearGroup.toGL H with hc
  have hinj : Function.Injective c := by
    intro X Y h
    have h1 : SpecialLinearGroup.toGL (X : SL(n, Ω)) = SpecialLinearGroup.toGL (Y : SL(n, Ω)) :=
      mul_left_cancel (mul_right_cancel h)
    exact Subtype.ext (SpecialLinearGroup.toGL_injective h1)
  have hrange : Set.range c = U := by
    ext Y
    constructor
    · rintro ⟨X, rfl⟩
      obtain ⟨Z, hZ, hXZ⟩ := (hH X).mp X.2
      have : c X = Z := by
        rw [hc]
        simp only
        rw [hXZ]
        group
      rw [this]
      exact hZ
    · intro hY
      set Z : GL (Fin n) Ω := SpecialLinearGroup.toGL H * Y * (SpecialLinearGroup.toGL H)⁻¹
        with hZdef
      have hdet : (Z : Matrix (Fin n) (Fin n) Ω).det = 1 := by
        have h1 : GeneralLinearGroup.det Z = GeneralLinearGroup.det Y := by
          rw [hZdef, map_mul, map_mul, map_inv, SpecialLinearGroup.coeToGL_det, inv_one, mul_one,
            one_mul]
        have h2 := congrArg (fun u : Ωˣ => (u : Ω)) h1
        simp only [GeneralLinearGroup.val_det_apply] at h2
        rw [h2]
        exact hU Y hY
      set X : SL(n, Ω) := ⟨(Z : Matrix (Fin n) (Fin n) Ω), hdet⟩ with hXdef
      have hXZ : SpecialLinearGroup.toGL X = Z :=
        Units.ext (SpecialLinearGroup.coe_GL_coe_matrix X)
      refine ⟨⟨X, (hH X).mpr ⟨Y, hY, hXZ⟩⟩, ?_⟩
      change (SpecialLinearGroup.toGL H)⁻¹ * SpecialLinearGroup.toGL X *
        SpecialLinearGroup.toGL H = Y
      rw [hXZ, hZdef]
      group
  rw [← hrange, Nat.card_range_of_injective hinj]

theorem sl3_unitary_fixed_card_dvd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {k Ω : Type} [Field k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (hk : Nat.card k = ℓ ^ f) (_hq2 : 2 < ℓ ^ f)
    (π : Equiv.Perm (Fin 3)) (Φ : SL(3, Ω) ≃* SL(3, Ω)) (b : Fin 3 → Fin 3 → Ωˣ)
    (hΦ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, Ω)) :
        Matrix (Fin 3) (Fin 3) Ω) = 1 + Matrix.single (π j) (π i) ((b i j : Ω) * t ^ ℓ ^ f)) :
    ∃ U : Subgroup SL(3, Ω), U ≤ fixSubgroup Φ ∧ IsPGroup ℓ U ∧ Nat.card U = (ℓ ^ f) ^ 3 := by
  obtain ⟨-, ⟨H, hH⟩, -, hfin, -⟩ :=
    CFSG.RankThree.SL3RootPermuting.sl3_root_permuting_frobenius_fixed_unitary hℓ hf hk π Φ b hΦ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype k := Fintype.ofFinite k
  have : CharP k ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  have hcard : Nat.card (fixSubgroup Φ) =
      (ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) := by
    rw [mnSyl_card_eq_of_conj (fixSubgroup Φ) (unitarySet (ℓ ^ f) 3)
      (fun Y hY => hY.2.1) H hH, mnSyl_card_unitarySet_three hf]
  have h3 : ℓ ^ (3 * f) = (ℓ ^ f) ^ 3 := by rw [mul_comm, pow_mul]
  have := hfin
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := fixSubgroup Φ) ℓ (n := 3 * f) (by
    rw [hcard, h3]
    exact (dvd_mul_right _ _).mul_right _)
  have hKcard : Nat.card (K.map (fixSubgroup Φ).subtype) = (ℓ ^ f) ^ 3 := by
    rw [Subgroup.card_map_of_injective (fixSubgroup Φ).subtype_injective, hK, h3]
  exact ⟨K.map (fixSubgroup Φ).subtype, Subgroup.map_subtype_le K,
    IsPGroup.of_card (n := 3 * f) (by rw [hKcard, h3]), hKcard⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
