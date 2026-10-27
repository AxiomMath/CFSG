module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical
public import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity
import all CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity
public import CFSG.RankThree.PartTwo.KFacts.AutPSU

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Assembly.LowTwoRank

theorem ringEquiv_eq_one_of_pow_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (φ : K ≃+* K) (h3 : φ ^ 3 = 1) : φ = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  have h3' : ∀ x, φ (φ (φ x)) = x := fun x => by
    have := congrArg (fun ψ : K ≃+* K => ψ x) h3
    simpa [pow_succ] using this
  ext x
  show φ x = x
  by_contra hx
  have h0 : x ≠ 0 := fun h => hx (by rw [h, map_zero])
  have h1 : x ≠ 1 := fun h => hx (by rw [h, map_one])
  have hy0 : φ x ≠ 0 := fun h => h0 (φ.injective (by rw [h, map_zero]))
  have hy1 : φ x ≠ 1 := fun h => h1 (φ.injective (by rw [h, map_one]))
  have hz0 : φ (φ x) ≠ 0 := fun h => hy0 (φ.injective (by rw [h, map_zero]))
  have hz1 : φ (φ x) ≠ 1 := fun h => hy1 (φ.injective (by rw [h, map_one]))
  have hcard : ({0, 1, x, φ x} : Finset K).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hx)]
    · simp [h1.symm, hy1.symm]
    · simp [zero_ne_one, h0.symm, hy0.symm]
  have huniv : ({0, 1, x, φ x} : Finset K) = Finset.univ :=
    Finset.eq_univ_of_card _ (hcard.trans hc.symm)
  have hmem : φ (φ x) ∈ ({0, 1, x, φ x} : Finset K) := huniv ▸ Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact hz0 h
  · exact hz1 h
  · apply hx
    have := h3' x
    rw [h] at this
    exact this
  · exact hx (φ.injective h)


section Descend

variable {Y : Type} [Group Y] {L : Subgroup Y}

@[expose] def conjL (u : Y) (hu : u ∈ Subgroup.normalizer (L : Set Y)) : MulAut ↥L where
  toFun x := ⟨u * x * u⁻¹, (Subgroup.mem_normalizer_iff.1 hu x).1 x.2⟩
  invFun x := ⟨u⁻¹ * x * u, by
    simpa using (Subgroup.mem_normalizer_iff.1 (inv_mem hu) (x : Y)).1 x.2⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

@[simp] theorem coe_conjL (u : Y) (hu : u ∈ Subgroup.normalizer (L : Set Y)) (x : ↥L) :
    ((conjL u hu x : ↥L) : Y) = u * x * u⁻¹ := rfl

@[expose] noncomputable def descendAut {P : Type} [Group P] (e : ↥L ⧸ Subgroup.center ↥L ≃* P)
    (u : Y) (hu : u ∈ Subgroup.normalizer (L : Set Y)) : MulAut P :=
  e.symm.trans ((CFSG.RankThree.PartTwo.KFacts.centerDescend L (conjL u hu)).trans e)

theorem descendAut_apply {P : Type} [Group P] (e : ↥L ⧸ Subgroup.center ↥L ≃* P) (u : Y)
    (hu : u ∈ Subgroup.normalizer (L : Set Y)) (ℓ : ↥L) :
    descendAut e u hu (e (QuotientGroup.mk ℓ)) = e (QuotientGroup.mk (conjL u hu ℓ)) := by
  simp [descendAut]
  rfl

theorem descendAut_pow_three {P : Type} [Group P] (e : ↥L ⧸ Subgroup.center ↥L ≃* P) {u : Y}
    (hu : u ∈ Subgroup.normalizer (L : Set Y)) (hu3 : u ^ 3 = 1) : descendAut e u hu ^ 3 = 1 := by
  ext p
  obtain ⟨q, rfl⟩ := e.surjective p
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
  have h3 : u * u * u = 1 := by simpa [pow_succ] using hu3
  simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, descendAut_apply, MulAut.one_apply]
  congr 2
  ext
  simp only [coe_conjL]
  calc u * (u * (u * ℓ * u⁻¹) * u⁻¹) * u⁻¹ = (u * u * u) * ℓ * (u * u * u)⁻¹ := by group
    _ = ℓ := by rw [h3]; simp

end Descend

open scoped commutatorElement in
theorem eq_of_inv_mul_mem_center {H G : Type*} [Group H] [Group G] [Group.IsPerfect H]
    (f₁ f₂ : H →* G) (hc : ∀ g, (f₁ g)⁻¹ * f₂ g ∈ Subgroup.center G) : f₁ = f₂ := by
  let δ : H →* G := MonoidHom.mk' (fun g => (f₁ g)⁻¹ * f₂ g) (fun a b => by
    have h := Subgroup.mem_center_iff.mp (hc a) (f₁ b)⁻¹
    simp only [map_mul, mul_inv_rev]
    calc (f₁ b)⁻¹ * (f₁ a)⁻¹ * (f₂ a * f₂ b)
        = ((f₁ b)⁻¹ * ((f₁ a)⁻¹ * f₂ a)) * f₂ b := by group
      _ = (f₁ a)⁻¹ * f₂ a * ((f₁ b)⁻¹ * f₂ b) := by rw [h]; group)
  have hker : ⁅(⊤ : Subgroup H), ⊤⁆ ≤ δ.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hc a) (δ b)).symm
  have htop : ⁅(⊤ : Subgroup H), ⊤⁆ = ⊤ := Group.isPerfect_def.mp inferInstance
  rw [htop] at hker
  ext g
  have := hker (Subgroup.mem_top g)
  rw [MonoidHom.mem_ker] at this
  exact inv_mul_eq_one.mp this

section Unitary

open Matrix CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K]

@[expose] noncomputable def conjSU (h : UnitaryFieldData 2 1 K) {n : ℕ} {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    unitarySU 2 1 K n →* unitarySU 2 1 K n :=
  MonoidHom.mk' (fun g => ⟨A * g * A⁻¹, (unitarySU_eq_gramSU h n).ge
    (conj_mem_gramSU h _ hA ((unitarySU_eq_gramSU h n).le g.2))⟩) (fun a b => by
    ext
    simp [mul_assoc])

@[simp] theorem coe_conjSU (h : UnitaryFieldData 2 1 K) {n : ℕ} {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (g : unitarySU 2 1 K n) : ((conjSU h hA g : unitarySU 2 1 K n) : GL (Fin n) K) = A * g * A⁻¹ :=
  rfl

theorem mem_primeFormUnitary_one_iff_isometry (h : UnitaryFieldData 2 1 K) {n : ℕ}
    (A : GL (Fin n) K) :
    A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ↔
      ∀ x y : Fin n → K, stdHermForm h n ((A : Matrix (Fin n) (Fin n) K) *ᵥ x)
        ((A : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y := by
  rw [stdHermForm_eq_gramForm, gramForm_isometry_iff]
  rfl

theorem exists_unitary_conj_of_normalizer {Y : Type} [Group Y] {L : Subgroup Y}
    {n : ℕ} (hn : 4 ≤ n) [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (ρ : StatedSU n 2 K →* ↥L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n 2 K))
    (hρe : ∀ g, e (QuotientGroup.mk (ρ g)) = (QuotientGroup.mk g : StatedProj (StatedSU n 2 K)))
    {u : Y} (hu : u ∈ Subgroup.normalizer (L : Set Y)) (hu3 : u ^ 3 = 1) :
    ∃ A : GL (Fin n) K,
      (∀ x y : Fin n → K, stdHermForm (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq
        hK le_rfl) n ((A : Matrix (Fin n) (Fin n) K) *ᵥ x) ((A : Matrix (Fin n) (Fin n) K) *ᵥ y) =
          stdHermForm (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl) n
            x y) ∧
      A ^ 3 ∈ StatedScalars (Fin n) K ∧
      ∀ g : StatedSU n 2 K, ∃ g' : StatedSU n 2 K,
        (g' : GL (Fin n) K) = A * (g : GL (Fin n) K) * A⁻¹ ∧
          u * (ρ g : Y) * u⁻¹ = (ρ g' : Y) := by
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ 1 = 2) := by omega
  have hnq : (n, 2 ^ 1) ≠ (3, 2) := fun h => by have := (Prod.mk.inj h).1; omega
  have hperf : Group.IsPerfect (StatedSU n (2 ^ 1) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK hn3 hnq
  set h := CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl with hh
  set β := descendAut e u hu
  let Θ : StatedProj (StatedSU n (2 ^ 1) K) ≃*
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (unitaryPSUEquiv h hn1).symm.trans (unitaryPSUEquivPrimeFormOne h n)
  have hΘ : ∀ g : unitarySU 2 1 K n, Θ (QuotientGroup.mk g) =
      (QuotientGroup.mk (⟨g, (unitarySU_eq_gramSU h n).le g.2⟩ : gramSU h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : primeFormP h _) := fun g => by
    have h1 : (unitaryPSUEquiv h hn1).symm (QuotientGroup.mk g) = unitaryProj h n g :=
      (MulEquiv.symm_apply_eq _).mpr (unitaryPSUEquiv_unitaryProj h hn1 g).symm
    simp only [Θ, MulEquiv.trans_apply, h1]
    rfl
  set β' := MulAut.congr Θ β with hβ'
  have hβ3 : β ^ 3 = 1 := descendAut_pow_three e hu hu3
  have hβ'3 : β' ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  obtain ⟨φ, ⟨A, hA⟩, -⟩ := existsUnique_primeFormFieldFactor h isPrimeFormGram_one hn3 hq β'
  have hφ : φ = 1 := by
    have h1 := primeFormFieldFactor_apply h isPrimeFormGram_one hn3 hq A φ
    rw [← hA] at h1
    refine ringEquiv_eq_one_of_pow_three (by rw [hK]; norm_num) φ ?_
    rw [← h1, ← map_pow, hβ'3, map_one]
  subst hφ
  rw [map_one, mul_one] at hA
  obtain ⟨c, -, hc⟩ := eq_scalar_of_primeFormConjHom_eq_one h isPrimeFormGram_one hn3
    (A := A ^ 3) (by rw [map_pow, ← hA, hβ'3])
  set cA := conjSU h A.2 with hcA
  have key : ∀ g : unitarySU 2 1 K n,
      e (QuotientGroup.mk (conjL u hu (ρ g))) = (QuotientGroup.mk (cA g) : StatedProj _) := by
    intro g
    have h1 : e (QuotientGroup.mk (conjL u hu (ρ g))) = β (QuotientGroup.mk g) := by
      rw [← descendAut_apply e u hu, hρe]
    have h2 : Θ (β (QuotientGroup.mk g)) = Θ (QuotientGroup.mk (cA g)) := by
      have h3 : β' (Θ (QuotientGroup.mk g)) = Θ (β (QuotientGroup.mk g)) := by
        rw [hβ', MulAut.congr_apply]
        simp
      rw [← h3, hA, hΘ, hΘ, primeFormConjHom_mk]
      rfl
    rw [h1]
    exact Θ.injective h2
  have hρ : ∀ g, conjL u hu (ρ g) = ρ (cA g) := by
    have := eq_of_inv_mul_mem_center (ρ.comp cA) ((conjL u hu).toMonoidHom.comp ρ) (fun g => by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        inv_mul_eq_one]
      apply e.injective
      change e (QuotientGroup.mk (ρ (cA g))) = e (QuotientGroup.mk (conjL u hu (ρ g)))
      rw [hρe, key]
      rfl)
    exact fun g => (DFunLike.congr_fun this g).symm
  refine ⟨A.1, (mem_primeFormUnitary_one_iff_isometry h A.1).mp A.2, ?_,
    fun g => ⟨cA g, rfl, ?_⟩⟩
  · obtain ⟨c', hc'⟩ : ∃ c' : Kˣ, GeneralLinearGroup.scalar (Fin n) c' = ((A ^ 3 : _) : GL (Fin n) K) :=
      ⟨c, hc.symm⟩
    exact ⟨c', by simpa using hc'⟩
  · exact congrArg Subtype.val (hρ g)

end Unitary

end CFSG.HardMathSupport.Curtis.UnitaryLevi
