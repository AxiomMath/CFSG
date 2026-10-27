module

public import CFSG.HardMathSupport.Dickson.Bal207.UniBlock
public import CFSG.RankThree.PartOne.KC.UnitaryCoordBlocks

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Uni

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Dickson.Bal207.FirstClaim
  CFSG.RankThree.PartOne.KCUnitaryCoord CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

theorem uni_conj_mem_blockSU {m : ℕ} {x : blockGamma h m} {D : primeFormUnitary h (oneGram F m)}
    {φ : F ≃+* F}
    (hx : (SemidirectProduct.inl 1)⁻¹ * x * SemidirectProduct.inl 1 =
      SemidirectProduct.inl D * SemidirectProduct.inr φ)
    {g : primeFormUnitary h (oneGram F m)} (hg : g ∈ blockSU h m) :
    (x * SemidirectProduct.inl g * x⁻¹).left ∈ blockSU h m := by
  have hx' : x = SemidirectProduct.inl D * SemidirectProduct.inr φ := by
    rw [← hx, map_one, inv_one, one_mul, mul_one]
  rw [hx', uni_conj_inl_inr_left, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_primeFormFieldU]
  exact conj_mem_gramSU h _ D.2
    (glAut_mem_gramSU h uni_isPrimeFormGram_one φ (Subgroup.mem_subgroupOf.1 hg))

section Frame

variable {X : Type} [Group X] {K B : Subgroup X} {S : Type} [Group S]
  {e : (↥K ⧸ Subgroup.center ↥K) ≃* S} (hBK : B ≤ Subgroup.normalizer (K : Set X)) {m : ℕ}
  {ι : primeFormUnitary h (oneGram F m) →* S} {x : ↥B → blockGamma h m}

theorem uni_block_inv
    (hx : ∀ (b : ↥B) (g : primeFormUnitary h (oneGram F m)),
      uniAut e ⟨b, hBK b.2⟩ (ι g) = ι ((x b * SemidirectProduct.inl g * (x b)⁻¹).left))
    (hP : ∀ b : ↥B, ∃ D : primeFormUnitary h (oneGram F m),
      ((D : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).IsDiag ∧ ∃ φ : F ≃+* F,
        (∀ c : F, c ^ 3 = 1 → φ c = c) ∧
          (SemidirectProduct.inl 1)⁻¹ * x b * SemidirectProduct.inl 1 =
            SemidirectProduct.inl D * SemidirectProduct.inr φ)
    (b : X) (hb : b ∈ B) :
    ∀ s ∈ (blockSU h m).map ι, uniAut e ⟨b, hBK hb⟩ s ∈ (blockSU h m).map ι := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨D, -, φ, -, hPx⟩ := hP ⟨b, hb⟩
  have e1 : uniAut e ⟨b, hBK hb⟩ (ι g) =
      ι ((x ⟨b, hb⟩ * SemidirectProduct.inl g * (x ⟨b, hb⟩)⁻¹).left) := hx ⟨b, hb⟩ g
  rw [e1]
  exact ⟨_, uni_conj_mem_blockSU h hPx hg, rfl⟩

theorem uni_fixed_of_cubeDiag
    (hx : ∀ (b : ↥B) (g : primeFormUnitary h (oneGram F m)),
      uniAut e ⟨b, hBK b.2⟩ (ι g) = ι ((x b * SemidirectProduct.inl g * (x b)⁻¹).left))
    (hP : ∀ b : ↥B, ∃ D : primeFormUnitary h (oneGram F m),
      ((D : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).IsDiag ∧ ∃ φ : F ≃+* F,
        (∀ c : F, c ^ 3 = 1 → φ c = c) ∧
          (SemidirectProduct.inl 1)⁻¹ * x b * SemidirectProduct.inl 1 =
            SemidirectProduct.inl D * SemidirectProduct.inr φ)
    {t : primeFormUnitary h (oneGram F m)} (ht : (t : GL (Fin m) F) ∈ cubeDiag F m)
    (b : X) (hb : b ∈ B) : uniAut e ⟨b, hBK hb⟩ (ι t) = ι t := by
  obtain ⟨D, hD, φ, hφ, hPx⟩ := hP ⟨b, hb⟩
  have e1 : uniAut e ⟨b, hBK hb⟩ (ι t) =
      ι ((x ⟨b, hb⟩ * SemidirectProduct.inl t * (x ⟨b, hb⟩)⁻¹).left) := hx ⟨b, hb⟩ t
  have e2 := conj_inl_eq_of_frame h hD hφ ht hPx
  rw [one_mul, inv_one, mul_one] at e2
  rw [e1, e2, SemidirectProduct.left_inl]

end Frame

theorem uni_exists_cube_pair (hf : f = 1 ∨ f = 3) {m : ℕ} (hm : 2 ≤ m) :
    ∃ t g : primeFormUnitary h (oneGram F m), t ∈ blockSU h m ∧ g ∈ blockSU h m ∧
      (t : GL (Fin m) F) ∈ cubeDiag F m ∧ t * g ≠ g * t := by
  obtain ⟨ω, hω, hω1, hωb⟩ := exists_cube_root_bar h (uni_three_dvd hf)
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  obtain ⟨v, hv⟩ : ∃ v : Fˣ, (v : F) = ω := ⟨Units.mk0 ω hω0, rfl⟩
  have hvn : h.norm (v : F) = 1 := by
    show (v : F) * h.bar (v : F) = 1
    rw [hv, hωb, ← pow_succ', hω]
  set i : Fin m := ⟨0, by omega⟩ with hi
  set j : Fin m := ⟨1, by omega⟩ with hj
  have hij : i ≠ j := by
    rw [hi, hj, Ne, Fin.ext_iff]
    norm_num
  have hdet : ∀ Y : Matrix (Fin 2) (Fin 2) F, (coordEmbed F i j Y).det = Y.det := by
    intro Y
    rw [coordEmbed, Matrix.det_one_add_mul_comm, ← Matrix.mul_assoc, coordProj_mul_coordIncl hij,
      Matrix.one_mul]
    congr 1
    abel
  have hmem : ∀ Y : gramSU h (idGram F 2), coordSUHom h hij Y ∈ blockSU h m := by
    intro Y
    rw [Subgroup.mem_subgroupOf, mem_gramSU_iff_unitary]
    refine ⟨(coordSUHom h hij Y).2, ?_⟩
    show (coordEmbed F i j ((Y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).det = 1
    rw [hdet]
    exact ((mem_gramSU_iff_unitary h).1 Y.2).2
  have hd3 : ∀ k : Fin m,
      (if k = i then (v : F) else if k = j then ((v⁻¹ : Fˣ) : F) else 1) ^ 3 = 1 := by
    intro k
    split_ifs
    · rw [hv, hω]
    · rw [Units.val_inv_eq_inv_val, hv, inv_pow, hω, inv_one]
    · exact one_pow 3
  refine ⟨diagonalCoord h hij v hvn, swapCoord h hij, hmem _, hmem _, ⟨?_, ?_⟩, ?_⟩
  · rw [coe_diagonalCoord h hij v hvn]
    exact isDiag_diagonal _
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, coe_diagonalCoord h hij v hvn, diagonal_pow, Units.val_one,
      ← diagonal_one]
    congr 1
    funext k
    exact hd3 k
  · intro hc
    have e := congrArg (fun A : primeFormUnitary h (oneGram F m) =>
      ((A : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) i j) hc
    simp only [Subgroup.coe_mul, Units.val_mul, coe_diagonalCoord h hij v hvn, diagonal_mul,
      mul_diagonal, swapCoord_apply h hij, hij.symm, ↓reduceIte, mul_one, one_mul,
      Units.val_inv_eq_inv_val, hv] at e
    apply hω1
    have h2 : ω * ω = 1 := by
      have h1 := mul_inv_cancel₀ hω0
      rwa [← e] at h1
    calc ω = ω * (ω * ω) := by rw [h2, mul_one]
      _ = ω ^ 3 := by ring
      _ = 1 := hω

end CFSG.HardMathSupport.Dickson.Bal207.Uni

end
