module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSUDet
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUTransfer

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {p f n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def u42CommU (h : UnitaryFieldData p f K) (n : ℕ) (A : GL (Fin n) K) :
    Subgroup ↥(primeFormUnitary h (idGram K n)) :=
  (commutingUnitary (idForm h n)
    (semilinearMatrixMap h (A : Matrix (Fin n) (Fin n) K))).comap (toLinU h n)

theorem mem_u42CommU (h : UnitaryFieldData p f K) (A : GL (Fin n) K)
    (x : ↥(primeFormUnitary h (idGram K n))) :
    x ∈ u42CommU h n A ↔
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) =
        (A : Matrix (Fin n) (Fin n) K) * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar := by
  rw [← CFSG.ComponentClassification.CatLeafProof.OddInner.commute_semilinearMatrixMap_iff h]
  rw [u42CommU, Subgroup.mem_comap, mem_commutingUnitary]
  have key : ∀ (y : ↥(primeFormUnitary h (idGram K n))) (w : Fin n → K),
      ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        (Fin n → K) →ₗ[K] (Fin n → K)) w =
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w := fun y w => rfl
  refine ⟨fun hx v => ?_, fun hx => ⟨toLinU_mem x, fun v => ?_⟩⟩
  · have := hx.2 v
    rwa [key, key] at this
  · rw [key, key]
    exact hx v


theorem u42_mem_fixedSubgroup'' {G : Type} [Group G] {σ : MulAut G} {x : G} :
    x ∈ fixedSubgroup σ ↔ σ x = x := Iff.rfl

theorem u42_fixed_iff_bar (h : UnitaryFieldData p f K) (A : ↥(primeFormUnitary h (idGram K n)))
    (φ : K ≃+* K) (hφ : ∀ x, φ x = h.bar x) (x : ↥(gramSU h (idGram K n))) :
    x ∈ fixedSubgroup (primeFormConjSU h (idGram K n) A *
      primeFormFieldSU h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) φ :
        MulAut ↥(gramSU h (idGram K n))) ↔
      (⟨(x : GL (Fin n) K), x.2.1⟩ : ↥(primeFormUnitary h (idGram K n))) ∈ u42CommU h n A := by
  rw [mem_u42CommU, u42_mem_fixedSubgroup'', Subtype.ext_iff]
  have hmap : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ =
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar :=
    Matrix.ext fun i j => hφ _
  change (A : GL (Fin n) K) * glAut φ (x : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ = x ↔ _
  rw [mul_inv_eq_iff_eq_mul, ← Units.val_inj, Units.val_mul, Units.val_mul, coe_glAut, hmap]
  exact eq_comm


theorem u42_card_fixed_bar (h : UnitaryFieldData p f K) (A : ↥(primeFormUnitary h (idGram K n)))
    (φ : K ≃+* K) (hφ : ∀ x, φ x = h.bar x) :
    Nat.card ↥(fixedSubgroup (primeFormConjSU h (idGram K n) A *
      primeFormFieldSU h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) φ :
        MulAut ↥(gramSU h (idGram K n)))) =
      Nat.card ↥(u42DetOn h n (u42CommU h n (A : GL (Fin n) K))).ker := by
  have hker : ∀ y : ↥(primeFormUnitary h (idGram K n)),
      y ∈ u42CommU h n (A : GL (Fin n) K) → u42DetU h n y = 1 →
        (y : GL (Fin n) K) ∈ gramSU h (idGram K n) := by
    intro y hy hd
    refine ⟨y.2, ?_⟩
    have h1 := congrArg Units.val hd
    rw [u42DetU_apply, GeneralLinearGroup.val_det_apply, Units.val_one] at h1
    exact h1
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨⟨(x.1 : GL (Fin n) K), x.1.2.1⟩, (u42_fixed_iff_bar h A φ hφ x.1).1 x.2⟩, ?_⟩
      invFun := fun y => ⟨⟨(y.1.1 : GL (Fin n) K), hker y.1.1 y.1.2 y.2⟩,
        (u42_fixed_iff_bar h A φ hφ ⟨(y.1.1 : GL (Fin n) K), hker y.1.1 y.1.2 y.2⟩).2 y.1.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [MonoidHom.mem_ker]
  apply Units.ext
  change ((x.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1
  exact x.1.2.2

theorem u42_detU_sq (h : UnitaryFieldData p f K) (hn : 1 ≤ n) (A : GL (Fin n) K)
    (x : ↥(primeFormUnitary h (idGram K n))) (hx : x ∈ u42CommU h n A) :
    u42DetU h n x * u42DetU h n x = 1 := by
  obtain ⟨hmem, -⟩ := u42_N₁ h hn
  have hN : h.norm ((u42DetU h n x : Kˣ) : K) = 1 := by
    rw [← hmem, ← u42_unitaryDet_toLinU h x]
    exact ⟨_, rfl⟩
  have hc := (mem_u42CommU h A x).1 hx
  have hb : (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar).det =
      h.bar ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det := by
    rw [RingHom.map_det]
    rfl
  have hdet : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det *
      (A : Matrix (Fin n) (Fin n) K).det =
      (A : Matrix (Fin n) (Fin n) K).det * h.bar ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det := by
    rw [← Matrix.det_mul, hc, Matrix.det_mul, hb]
  have hA0 : (A : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact (GeneralLinearGroup.det A).ne_zero
  have hxb : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      h.bar ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det := by
    rw [mul_comm _ (A : Matrix (Fin n) (Fin n) K).det] at hdet
    exact mul_left_cancel₀ hA0 hdet
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  have hN' := hN
  rw [UnitaryFieldData.norm, u42DetU_apply, GeneralLinearGroup.val_det_apply] at hN'
  rw [u42DetU_apply, GeneralLinearGroup.val_det_apply]
  rw [← hxb] at hN'
  exact hN'

theorem u42_card_u42CommU (h : UnitaryFieldData p f K) (A : GL (Fin n) K) :
    Nat.card ↥(u42CommU h n A) =
      Nat.card ↥(commutingUnitary (idForm h n)
        (semilinearMatrixMap h (A : Matrix (Fin n) (Fin n) K))) := by
  refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨toLinU h n x.1, x.2⟩) ⟨?_, ?_⟩)
  · intro x y hxy
    have := congrArg (fun z => (z.1 : LinearMap.GeneralLinearGroup K (Fin n → K))) hxy
    exact Subtype.ext (toLinU_injective this)
  · rintro ⟨y, hy⟩
    obtain ⟨A', hA'⟩ := exists_toLinU hy.1
    refine ⟨⟨A', ?_⟩, Subtype.ext hA'⟩
    rw [u42CommU, Subgroup.mem_comap, hA']
    exact hy


theorem u42_psu_bar_eq (h : UnitaryFieldData p f K) (hn : 3 ≤ n)
    (A : ↥(primeFormUnitary h (idGram K n))) (φ : K ≃+* K) (hφ : ∀ x, φ x = h.bar x) :
    ∃ e ι : ℕ, e ∣ Nat.gcd n (p ^ f + 1) ∧ (ι = 1 ∨ ι = 2) ∧
      Nat.card ↥(fixedSubgroup (primeFormPsi h
        (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) ⟨A, φ⟩)) * e * ι =
        Nat.card ↥(commutingUnitary (idForm h n)
          (semilinearMatrixMap h ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) := by
  have : Finite K := h.finite
  obtain ⟨R, hRZ, -, hcount⟩ := u42_count_fixed (normOneScalars h (gramSU h (idGram K n)) n)
    (normOneScalars_le_center h _ n)
    (primeFormConjSU h (idGram K n) A *
      primeFormFieldSU h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) φ)
    (primeFormPsi h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) ⟨A, φ⟩)
    (fun g => CFSG.ComponentClassification.CatFC.psu_graph_hψ h A φ g)
  have hZcard : Nat.card (normOneScalars h (gramSU h (idGram K n)) n) = Nat.gcd n (p ^ f + 1) :=
    CFSG.RankThree.Classical.card_normOneScalars_one h (by omega)
  obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hRZ
  have hRpos : 0 < Nat.card R := Nat.card_pos
  rw [hj] at hcount
  have hFj : Nat.card ↥(fixedSubgroup (primeFormPsi h
      (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) ⟨A, φ⟩)) * j =
      Nat.card ↥(fixedSubgroup (primeFormConjSU h (idGram K n) A *
      primeFormFieldSU h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) φ :
        MulAut ↥(gramSU h (idGram K n)))) := by
    refine Nat.eq_of_mul_eq_mul_left hRpos ?_
    rw [← hcount]
    ring
  have hfix := u42_card_fixed_bar h A φ hφ
  have hCm := u42_card_eq_ker_mul_range (u42DetOn h n (u42CommU h n (A : GL (Fin n) K)))
  have hle : Nat.card (u42DetOn h n (u42CommU h n (A : GL (Fin n) K))).range ≤ 2 := by
    apply u42_card_subgroup_le_two
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have hx := u42_detU_sq h (by omega) _ x.1 x.2
    have hy := u42_detU_sq h (by omega) _ y.1 y.2
    have hx' : ((u42DetU h n x.1 : Kˣ) : K) * ((u42DetU h n x.1 : Kˣ) : K) = 1 := by
      simpa using congrArg Units.val hx
    have hy' : ((u42DetU h n y.1 : Kˣ) : K) * ((u42DetU h n y.1 : Kˣ) : K) = 1 := by
      simpa using congrArg Units.val hy
    rcases mul_self_eq_one_iff.mp hx' with h1 | h1
    · left
      exact Units.ext h1
    · rcases mul_self_eq_one_iff.mp hy' with h2 | h2
      · right
        left
        exact Units.ext h2
      · right
        right
        exact Units.ext (h1.trans h2.symm)
  have hpos : 0 < Nat.card (u42DetOn h n (u42CommU h n (A : GL (Fin n) K))).range := Nat.card_pos
  refine ⟨j, Nat.card (u42DetOn h n (u42CommU h n (A : GL (Fin n) K))).range,
    ⟨Nat.card R, by rw [← hZcard, hj]; ring⟩, by omega, ?_⟩
  rw [hFj, hfix, ← u42_card_u42CommU h (A : GL (Fin n) K), hCm]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
