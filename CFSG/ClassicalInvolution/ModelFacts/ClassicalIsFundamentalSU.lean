module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalInvolutions
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalStar
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSplit
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Chart
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLift
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Intrinsic

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ComponentClassification Module
open scoped MatrixGroups

section Star

variable {F : Type} [Field F] (σ : F ≃+* F) {n : ℕ}

@[expose] def conjTrAdd (σ : F ≃+* F) (n : ℕ) :
    Matrix (Fin n) (Fin n) F →+ Matrix (Fin n) (Fin n) F where
  toFun := conjTr σ
  map_zero' := by
    ext i j
    simp [conjTr]
  map_add' := conjTr_add σ

theorem conjTrAdd_apply (A : Matrix (Fin n) (Fin n) F) : conjTrAdd σ n A = conjTr σ A := rfl

theorem conjTr_smul_eq (c : F) (A : Matrix (Fin n) (Fin n) F) :
    conjTr σ (c • A) = σ c • conjTr σ A := by
  ext i j
  simp [conjTr]

theorem conjTr_eq_of_mul_self {D : Matrix (Fin n) (Fin n) F} (hD : D * D = 1)
    (hu : conjTr σ D * D = 1) : conjTr σ D = D := by
  calc conjTr σ D = conjTr σ D * (D * D) := by rw [hD, Matrix.mul_one]
    _ = (conjTr σ D * D) * D := (Matrix.mul_assoc _ _ _).symm
    _ = D := by rw [hu, Matrix.one_mul]

theorem map_inv_two (σ : F ≃+* F) : σ (2 : F)⁻¹ = (2 : F)⁻¹ := by
  rw [map_inv₀, map_ofNat]

theorem conjTr_eMinus {D : Matrix (Fin n) (Fin n) F} (h : conjTr σ D = D) :
    conjTr σ (eMinus D) = eMinus D := by
  unfold eMinus
  rw [conjTr_smul_eq, conjTr_sub, conjTr_one, h, map_inv_two]

theorem conjTr_ePlus {D : Matrix (Fin n) (Fin n) F} (h : conjTr σ D = D) :
    conjTr σ (ePlus D) = ePlus D := by
  unfold ePlus
  rw [conjTr_smul_eq, conjTr_add, conjTr_one, h, map_inv_two]

end Star

section Involution

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] {n : ℕ}
  {z : Su F p f n}

theorem suMat_mul_self_of_mul_self (hz : z * z = 1) : suMat z * suMat z = 1 := by
  rw [← suMat_mul, hz, suMat_one]

theorem conjTr_suMat_mul_suMat (x : Su F p f n) :
    conjTr (unitaryInvolution F p f) (suMat x) * suMat x = 1 := x.2.2

theorem conjTr_suMat_of_mul_self (hz : z * z = 1) :
    conjTr (unitaryInvolution F p f) (suMat z) = suMat z :=
  conjTr_eq_of_mul_self _ (suMat_mul_self_of_mul_self hz) (conjTr_suMat_mul_suMat z)

theorem conjTr_partOn_mul_partOn (h2 : (2 : F) ≠ 0) (hz : z * z = 1) {x : Su F p f n}
    (hx : suMat x * suMat z = suMat z * suMat x) :
    conjTr (unitaryInvolution F p f)
        (partOn (eMinus (suMat z)) (ePlus (suMat z)) (suMat x)) *
      partOn (eMinus (suMat z)) (ePlus (suMat z)) (suMat x) = 1 := by
  have hD := suMat_mul_self_of_mul_self hz
  have hu := conjTr_suMat_of_mul_self hz
  exact star_partOn_mul_partOn (conjTrAdd (unitaryInvolution F p f) n)
    (fun a b => conjTr_mul _ a b) (eMinus_add_ePlus h2) (eMinus_mul_ePlus hD)
    (ePlus_mul_eMinus hD) (conjTr_eMinus _ hu) (conjTr_ePlus _ hu) (commute_eMinus' hx)
    (conjTr_suMat_mul_suMat x)

theorem conjTr_partOn_mul_partOn' (h2 : (2 : F) ≠ 0) (hz : z * z = 1) {x : Su F p f n}
    (hx : suMat x * suMat z = suMat z * suMat x) :
    conjTr (unitaryInvolution F p f)
        (partOn (ePlus (suMat z)) (eMinus (suMat z)) (suMat x)) *
      partOn (ePlus (suMat z)) (eMinus (suMat z)) (suMat x) = 1 := by
  have hD := suMat_mul_self_of_mul_self hz
  have hu := conjTr_suMat_of_mul_self hz
  have hsum' : ePlus (suMat z) + eMinus (suMat z) = 1 :=
    (add_comm _ _).trans (eMinus_add_ePlus h2)
  exact star_partOn_mul_partOn (conjTrAdd (unitaryInvolution F p f) n)
    (fun a b => conjTr_mul _ a b) hsum' (ePlus_mul_eMinus hD) (eMinus_mul_ePlus hD)
    (conjTr_ePlus _ hu) (conjTr_eMinus _ hu) (commute_ePlus' hx) (conjTr_suMat_mul_suMat x)

end Involution

section Groups

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] {n : ℕ}

theorem det_partOn_eq_one_of_perfect (h2 : (2 : F) ≠ 0) {D : Matrix (Fin n) (Fin n) F}
    (hD : D * D = 1) {L : Subgroup (Su F p f n)} (hL : Group.IsPerfect ↥L)
    (hLD : ∀ x ∈ L, suMat x * D = D * suMat x) (x : Su F p f n) (hx : x ∈ L) :
    (partOn (eMinus D) (ePlus D) (suMat x)).det = 1 := by
  have hsum := eMinus_add_ePlus (D := D) h2
  have hef := eMinus_mul_ePlus hD
  have hfe := ePlus_mul_eMinus hD
  let δ₀ : ↥L →* F :=
    { toFun := fun x => (partOn (eMinus D) (ePlus D) (suMat (x : Su F p f n))).det
      map_one' := by
        show (partOn (eMinus D) (ePlus D) (suMat (1 : Su F p f n))).det = 1
        rw [suMat_one, partOn_one hsum hef, det_one]
      map_mul' := by
        intro x y
        have hx := hLD x x.2
        have hy := hLD y y.2
        show (partOn (eMinus D) (ePlus D) (suMat ((x : Su F p f n) * (y : Su F p f n)))).det = _ * _
        rw [suMat_mul, partOn_mul hsum hef hfe (commute_eMinus' hx) (commute_eMinus' hy)
            (commute_ePlus' hy), det_mul] }
  have hker : commutator ↥L ≤ (δ₀.toHomUnits).ker := Abelianization.commutator_subset_ker _
  rw [hL.commutator_eq_top] at hker
  have h1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top ⟨x, hx⟩))
  have h2' : ((δ₀.toHomUnits ⟨x, hx⟩ : Fˣ) : F) = 1 := by rw [h1]; rfl
  have h3 : δ₀ ⟨x, hx⟩ = 1 := by simpa using h2'
  exact h3

theorem exists_mul_of_perfect_su (h2 : (2 : F) ≠ 0) {z : Su F p f n} (hz : z * z = 1)
    {L : Subgroup (Su F p f n)} (hL : Group.IsPerfect ↥L) (hLz : ∀ x ∈ L, x * z = z * x)
    (x : Su F p f n) (hx : x ∈ L) :
    ∃ a ∈ longRootGroupSU F p f (suMat z), ∃ b ∈ longRootGroupSU F p f (-suMat z), x = a * b := by
  have hD := suMat_mul_self_of_mul_self hz
  have hsum := eMinus_add_ePlus (D := suMat z) h2
  have hsum' : ePlus (suMat z) + eMinus (suMat z) = 1 := (add_comm _ _).trans hsum
  have hef := eMinus_mul_ePlus hD
  have hfe := ePlus_mul_eMinus hD
  have hLD : ∀ y ∈ L, suMat y * suMat z = suMat z * suMat y := fun y hy => by
    rw [← suMat_mul, ← suMat_mul, hLz y hy]
  have hxD := hLD x hx
  have hdet : (partOn (eMinus (suMat z)) (ePlus (suMat z)) (suMat x)).det = 1 :=
    det_partOn_eq_one_of_perfect h2 hD hL hLD x hx
  have hprod := partOn_mul_partOn hsum hef hfe (commute_eMinus' hxD) (commute_ePlus' hxD)
  have hdetp : (partOn (ePlus (suMat z)) (eMinus (suMat z)) (suMat x)).det = 1 := by
    have := congrArg Matrix.det hprod
    rw [det_mul, hdet, one_mul] at this
    rw [this]
    exact det_suMat x
  have hunit₁ := conjTr_partOn_mul_partOn h2 hz hxD
  have hunit₂ := conjTr_partOn_mul_partOn' h2 hz hxD
  have hDe : suMat z = ePlus (suMat z) - eMinus (suMat z) := eq_ePlus_sub_eMinus h2
  have h1D : (1 : Matrix (Fin n) (Fin n) F) + suMat z = (2 : F) • ePlus (suMat z) :=
    one_add_eq_smul_ePlus h2
  have h1D' : (1 : Matrix (Fin n) (Fin n) F) + -suMat z = (2 : F) • eMinus (suMat z) := by
    rw [← sub_eq_add_neg]
    exact one_sub_eq_smul_eMinus h2
  refine ⟨mkSU F p f _ hdet hunit₁, ?_, mkSU F p f _ hdetp hunit₂, ?_, ?_⟩
  · rw [mem_longRootGroupSU, suMat_mkSU]
    refine ⟨?_, ?_⟩
    · have e1 := partOn_mul_sub hsum hef hfe (suMat x)
      have e2 := sub_mul_partOn hsum hef hfe (suMat x)
      rw [← hDe] at e1 e2
      rw [e1, e2]
    · rw [h1D, Matrix.mul_smul, partOn_mul_right hef hfe hsum]
  · rw [mem_longRootGroupSU, suMat_mkSU]
    refine ⟨?_, ?_⟩
    · have e1 := partOn_mul_sub hsum' hfe hef (suMat x)
      have e2 := sub_mul_partOn hsum' hfe hef (suMat x)
      have hDe' : -suMat z = eMinus (suMat z) - ePlus (suMat z) := by
        calc -suMat z = -(ePlus (suMat z) - eMinus (suMat z)) := by rw [← hDe]
          _ = eMinus (suMat z) - ePlus (suMat z) := neg_sub _ _
      rw [← hDe'] at e1 e2
      rw [e1, e2]
    · rw [h1D', Matrix.mul_smul, partOn_mul_right hfe hef hsum']
  · apply suMat_injective
    rw [suMat_mul, suMat_mkSU, suMat_mkSU]
    exact hprod.symm

theorem commute_of_mem_longRootGroupSU_neg (h2 : (2 : F) ≠ 0) {z : Su F p f n} (hz : z * z = 1)
    {x y : Su F p f n} (hx : x ∈ longRootGroupSU F p f (suMat z))
    (hy : y ∈ longRootGroupSU F p f (-suMat z)) : x * y = y * x := by
  apply suToSL_injective
  rw [map_mul, map_mul]
  exact commute_longRootGroup_neg h2 (suMat_mul_self_of_mul_self hz) hx hy

theorem comm_of_mem_longRootGroupSU {z : Su F p f n} {x : Su F p f n}
    (hx : x ∈ longRootGroupSU F p f (suMat z)) : x * z = z * x := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul]
  exact hx.1

theorem mem_longRootGroupSU_self {z : Su F p f n} (hz : z * z = 1) :
    z ∈ longRootGroupSU F p f (suMat z) := by
  have hD := suMat_mul_self_of_mul_self hz
  refine ⟨rfl, ?_⟩
  show suMat z * (1 + suMat z) = 1 + suMat z
  rw [Matrix.mul_add, Matrix.mul_one, hD, add_comm]

theorem not_mem_longRootGroupSU_neg_self (h2 : (2 : F) ≠ 0) {z : Su F p f n} (hz : z * z = 1)
    (hz1 : z ≠ 1) : z ∉ longRootGroupSU F p f (-suMat z) := by
  have hD := suMat_mul_self_of_mul_self hz
  intro hmem
  have h3 : suMat z * (1 + -suMat z) = 1 + -suMat z := hmem.2
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_neg, hD] at h3
  have h4 : suMat z + suMat z = 1 + 1 := by
    calc suMat z + suMat z = (suMat z + -1) + (suMat z + 1) := by abel
      _ = (1 + -suMat z) + (suMat z + 1) := by rw [h3]
      _ = 1 + 1 := by abel
  have h5 : suMat z = 1 := by
    have : (2 : F) • suMat z = (2 : F) • (1 : Matrix (Fin n) (Fin n) F) := by
      rw [two_smul, two_smul, h4]
    exact smul_right_injective _ h2 this
  exact hz1 (suMat_injective (by rw [h5, suMat_one]))

end Groups

section Frames

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] {n : ℕ}

omit [Finite F] [Fact p.Prime] [CharP F p] in
theorem negBlockK_zero_eq_diagonal (a : ℕ) :
    negBlockK F n 0 a = Matrix.diagonal (fun j : Fin n => if j.val < a then (-1 : F) else 1) := by
  rw [negBlockK_eq_diagonal]
  congr 1
  funext j
  simp

omit [Finite F] [Fact p.Prime] [CharP F p] in
theorem neg_negBlockK_zero (a : ℕ) : -negBlockK F n 0 a = negBlockK F n a (n - a) := by
  rw [negBlockK_zero_eq_diagonal, negBlockK_eq_diagonal, Matrix.diagonal_neg]
  congr 1
  funext j
  have := j.isLt
  by_cases h : j.val < a
  · simp [h]
  · have h' : a ≤ j.val := by omega
    simp [h, h', show j.val < a + (n - a) by omega]

theorem exists_su_conj_negBlock (hF : Nat.card F = (p ^ f) ^ 2) (h2 : (2 : F) ≠ 0) (hn : 0 < n)
    {z : Su F p f n} (hz : z * z = 1) :
    ∃ (a : ℕ) (_ : a ≤ n) (g : Su F p f n),
      suMat z * suMat g = suMat g * negBlockK F n 0 a := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  have hI := suMat_mul_self_of_mul_self hz
  have hcompl := isCompl_eigSpace h2 hI
  set V := eigSpace (suMat z) (-1) with hV
  set W := eigSpace (suMat z) 1 with hW'
  set a := Module.finrank F V with ha'
  have ha : a ≤ n := by
    have := Submodule.finrank_le V
    rw [Module.finrank_fin_fun] at this
    exact this
  have hW : Module.finrank F W = n - a := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [Module.finrank_fin_fun] at this
    omega
  let E : Bool → Submodule F (Fin n → F) := fun b => cond b W V
  let ε : Fin n → Bool := fun j => decide (a ≤ j.val)
  have hε : ∀ b, Nat.card {j // ε j = b} = Module.finrank F (E b) := by
    intro b
    cases b
    · change _ = Module.finrank F V
      rw [Nat.card_congr (Equiv.subtypeEquivRight (q := fun j : Fin n => j.val < a)
        (fun j => by simp only [ε, decide_eq_false_iff_not, not_le]))]
      exact card_fin_val_lt ha
    · change _ = Module.finrank F W
      rw [hW, Nat.card_congr (Equiv.subtypeEquivRight (q := fun j : Fin n => a ≤ j.val)
        (fun j => by simp only [ε, decide_eq_true_eq]))]
      exact card_fin_val_ge ha
  have hnd : ∀ b, Nondeg (unitaryInvolution F p f) (E b) := fun b => by
    cases b
    · exact nondeg_eigSpace_neg_one h2 z hI
    · exact nondeg_eigSpace_one hσ h2 z hI
  have horth : ∀ s t, s ≠ t → Orth (unitaryInvolution F p f) (E s) (E t) := by
    intro s t hst u hu v hv
    cases s <;> cases t
    · exact absurd rfl hst
    · exact orth_eigSpace_neg_one_one h2 z u hu v hv
    · exact herm_eq_zero_comm _ hσ.invol (orth_eigSpace_neg_one_one h2 z v hv u hu)
    · exact absurd rfl hst
  obtain ⟨g, hg⟩ := exists_su_adapted hσ hn E hnd horth ε hε
  refine ⟨a, ha, g, ?_⟩
  have hcol : ∀ j, (fun k => suMat g k j) ∈ E (ε j) := fun j => by
    have := hg j
    rwa [suMat_smul, Matrix.mulVec_single_one] at this
  ext i j
  rw [negBlockK_zero_eq_diagonal, Matrix.mul_diagonal]
  by_cases hj : j.val < a
  · have hmem : (fun k => suMat g k j) ∈ V := by
      simpa [E, ε, not_le.mpr hj] using hcol j
    have := congr_fun (mem_eigSpace_neg_one.mp hmem) i
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply] at this
    simp only [Matrix.mul_apply, hj, ite_true]
    rw [this]
    ring
  · have hmem : (fun k => suMat g k j) ∈ W := by
      simpa [E, ε, not_lt.mp hj] using hcol j
    have := congr_fun (mem_eigSpace_one.mp hmem) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, hj, ite_false]
    rw [this]
    ring

theorem range_blockEmb_eq_longRootGroupSU_gen (h2 : (2 : F) ≠ 0) {j k : ℕ} (hj : j + k ≤ n) :
    (blockEmb F p f n k j hj).range = longRootGroupSU F p f (negBlockK F n j k) := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    exact blockSL_mem_longRootGroupK hj (suToSL (unitaryInvolution F p f) k A)
  · intro hx
    obtain ⟨A, hA⟩ := exists_blockSL_of_mem_longRootGroupK h2 hj hx
    have hAm : blockMat n j (A : Matrix (Fin k) (Fin k) F) = suMat x :=
      congrArg (fun z : SL(n, F) => (z : Matrix (Fin n) (Fin n) F)) hA
    have hAu : conjTr (unitaryInvolution F p f) (A : Matrix (Fin k) (Fin k) F) *
        (A : Matrix (Fin k) (Fin k) F) = 1 := by
      have hx1 : conjTr (unitaryInvolution F p f) (suMat x) * suMat x = 1 := x.2.2
      rw [← hAm, conjTr_blockMat, ← blockMat_mul hj] at hx1
      exact blockMat_injective hj (by rw [hx1, blockMat_one])
    refine ⟨⟨Matrix.SpecialLinearGroup.toGL A, ⟨by simp, by simpa using hAu⟩⟩, ?_⟩
    exact suMat_injective (by rw [suMat_blockEmb]; simpa [suMat] using hAm)

theorem exists_longRootGroupSU_data (hF : Nat.card F = (p ^ f) ^ 2) (h2 : (2 : F) ≠ 0)
    (hn : 0 < n) {z : Su F p f n} (hz : z * z = 1) :
    ∃ (a : ℕ) (ha : a ≤ n) (g : Su F p f n),
      suMat z * suMat g = suMat g * negBlockK F n 0 a ∧
      longRootGroupSU F p f (suMat z) =
        ((blockEmb F p f n a 0 (by omega)).range).map (MulAut.conj g).toMonoidHom ∧
      longRootGroupSU F p f (-suMat z) =
        ((blockEmb F p f n (n - a) a (by omega)).range).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨a, ha, g, hg⟩ := exists_su_conj_negBlock hF h2 hn hz
  refine ⟨a, ha, g, hg, ?_, ?_⟩
  · rw [longRootGroupSU_eq_map_conj_of_mul_eq g hg,
      range_blockEmb_eq_longRootGroupSU_gen h2 (by omega : 0 + a ≤ n)]
  · have hg' : -suMat z * suMat g = suMat g * negBlockK F n a (n - a) := by
      rw [← neg_negBlockK_zero, Matrix.neg_mul, hg, Matrix.mul_neg]
    rw [longRootGroupSU_eq_map_conj_of_mul_eq g hg',
      range_blockEmb_eq_longRootGroupSU_gen h2 (by omega : a + (n - a) ≤ n)]

theorem nonempty_mulEquiv_map_blockEmb {j k : ℕ} (hj : j + k ≤ n) (g : Su F p f n) :
    Nonempty (Su F p f k ≃*
      ↥(((blockEmb F p f n k j hj).range).map (MulAut.conj g).toMonoidHom)) := by
  let φ : Su F p f k →* Su F p f n := (MulAut.conj g).toMonoidHom.comp (blockEmb F p f n k j hj)
  have hφ : Function.Injective φ := (MulAut.conj g).injective.comp (blockEmb_injective hj)
  exact ⟨(MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr (by
    rw [MonoidHom.range_comp]))⟩

end Frames

section Blocks

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem open_isQuasisimple_su (hF : Nat.card F = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {k : ℕ}
    (hk : 2 ≤ k) : CFSG.Open.IsQuasisimple (Su F p f k) := by
  rcases Nat.lt_or_ge k 3 with h | h
  · obtain rfl : k = 2 := by omega
    obtain ⟨e⟩ := nonempty_sl2_mulEquiv_su_two (K := F) (p := p) (f := f) hF
    exact Components.quasisimple_of_equiv e.symm
      (isQuasisimple_specialLinearGroup_two (by rw [card_fixedSubfield hF]; omega))
  · have hnq : (k, p ^ f) ≠ (3, 2) := fun h' => by
      have := congrArg Prod.snd h'
      simp only at this
      omega
    have hq' := isQuasisimple_statedSU_of_card hF h hnq
    let e : Su F p f k ≃* CFSG.Assembly.LowTwoRank.StatedSU k (p ^ f) F :=
      MulEquiv.subgroupCongr (SUid_eq_statedSU hF k)
    exact open_isQuasisimple (isQuasisimple_of_mulEquiv e.symm hq'.1)

theorem subsingleton_su_of_le_one {a : ℕ} (ha : a ≤ 1) : Subsingleton (Su F p f a) := by
  have := subsingleton_sl_of_le_one (F := F) ha
  exact (suToSL_injective (σ := unitaryInvolution F p f) (n := a)).subsingleton

theorem exists_two_commuting_involutions (h2 : (2 : F) ≠ 0) {a : ℕ} (ha : 3 ≤ a) :
    ∃ s t : Su F p f a, s * s = 1 ∧ t * t = 1 ∧ s ≠ 1 ∧ t ≠ 1 ∧ s * t = t * s ∧ s ≠ t := by
  let T₁ : Pair a := ⟨{⟨0, by omega⟩, ⟨1, by omega⟩},
    Finset.card_pair (by simp [Fin.ext_iff])⟩
  let T₂ : Pair a := ⟨{⟨1, by omega⟩, ⟨2, by omega⟩},
    Finset.card_pair (by simp [Fin.ext_iff])⟩
  have hne1 : ∀ T : Pair a, zEltU F p f T ≠ 1 := fun T hT => by
    have h1 : zMat F a T.1 = zMat F a (∅ : Finset (Fin a)) := by
      rw [zMat_empty, ← suMat_zEltU (K := F) (p := p) (f := f) T, hT, suMat_one]
    have := zMat_inj h2 h1
    have h3 := T.2
    rw [this] at h3
    simp at h3
  refine ⟨zEltU F p f T₁, zEltU F p f T₂, zEltU_mul_self T₁, zEltU_mul_self T₂, hne1 T₁, hne1 T₂,
    signGroupU_comm (zEltU_mem_signGroupU T₁) (zEltU_mem_signGroupU T₂), fun h => ?_⟩
  have h1 : zMat F a T₁.1 = zMat F a T₂.1 := by
    rw [← suMat_zEltU (K := F) (p := p) (f := f) T₁, ← suMat_zEltU (K := F) (p := p) (f := f) T₂,
      h]
  have := zMat_inj h2 h1
  have h0 : (⟨0, by omega⟩ : Fin a) ∈ T₁.1 := by simp [T₁]
  rw [this] at h0
  simp [T₂, Fin.ext_iff] at h0

end Blocks

section Main

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem isLongRootSU2_of_isClassicalMember (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 2 ≤ n) {L : Subgroup (Su F p f n)} {z : Su F p f n}
    (h : IsClassicalMember p f L z) : IsLongRootSU2 F p f hn L z := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : NeZero f := ⟨hf⟩
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [GaloisField.card p f hf]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, pow_two] at this
  have hz1 : z ≠ 1 := h.ne_one
  have hLz : ∀ x ∈ L, x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h.subnormal hx)
  obtain ⟨a, ha, g, hg, hAm, hAp⟩ := exists_longRootGroupSU_data hF h2 (by omega) hzz
  set Am : Subgroup (Su F p f n) := longRootGroupSU F p f (suMat z) with hAmdef
  set Ap : Subgroup (Su F p f n) := longRootGroupSU F p f (-suMat z) with hApdef
  have hLsup : L ≤ Am ⊔ Ap := fun x hx => by
    obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_of_perfect_su h2 hzz h.perfect hLz x hx
    exact Subgroup.mul_mem_sup ha' hb'
  have hcomm : ∀ x ∈ Am, ∀ y ∈ Ap, x * y = y * x := fun x hx y hy =>
    commute_of_mem_longRootGroupSU_neg h2 hzz hx hy
  have hzAm : z ∈ Am := mem_longRootGroupSU_self hzz
  have hzAp : z ∉ Ap := not_mem_longRootGroupSU_neg_self h2 hzz hz1
  have hAmC : Am ≤ Subgroup.centralizer ({z} : Set (Su F p f n)) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_longRootGroupSU hx)
  obtain ⟨eAm0⟩ := nonempty_mulEquiv_map_blockEmb (F := F) (p := p) (f := f)
    (by omega : 0 + a ≤ n) g
  obtain ⟨eAp0⟩ := nonempty_mulEquiv_map_blockEmb (F := F) (p := p) (f := f)
    (by omega : a + (n - a) ≤ n) g
  let eAm : Su F p f a ≃* ↥Am := eAm0.trans (MulEquiv.subgroupCongr hAm.symm)
  let eAp : Su F p f (n - a) ≃* ↥Ap := eAp0.trans (MulEquiv.subgroupCongr hAp.symm)
  have ha2 : 2 ≤ a := by
    by_contra hlt
    have hsub : Subsingleton (Su F p f a) := subsingleton_su_of_le_one (by omega)
    have : Subsingleton Am := eAm.surjective.subsingleton
    exact hz1 (congrArg Subtype.val (Subsingleton.elim (⟨z, hzAm⟩ : Am) 1))
  have hAmq : CFSG.Open.IsQuasisimple ↥Am :=
    Components.quasisimple_of_equiv eAm.symm (open_isQuasisimple_su hF hq ha2)
  have hBq : Ap = ⊥ ∨ CFSG.Open.IsQuasisimple ↥Ap := by
    by_cases hb2 : 2 ≤ n - a
    · exact Or.inr (Components.quasisimple_of_equiv eAp.symm (open_isQuasisimple_su hF hq hb2))
    · left
      have hsub : Subsingleton (Su F p f (n - a)) := subsingleton_su_of_le_one (by omega)
      have : Subsingleton Ap := eAp.surjective.subsingleton
      exact Subgroup.eq_bot_of_subsingleton Ap
  have hLeq : L = Am :=
    eq_of_le_sup_of_isClassicalMember (by omega) h hcomm hLsup hzAp hAmC hAmq hBq
  have ha3 : ¬ 3 ≤ a := by
    intro ha3
    obtain ⟨s, t, hs2, ht2, hs1, ht1, hst, hne⟩ :=
      exists_two_commuting_involutions (F := F) (p := p) (f := f) h2 ha3
    obtain ⟨e2⟩ := h.nonempty_equiv
    let φ : Su F p f a →* Su F p f n :=
      (MulAut.conj g).toMonoidHom.comp (blockEmb F p f n a 0 (by omega))
    have hφ : Function.Injective φ := (MulAut.conj g).injective.comp (blockEmb_injective _)
    have hmem : ∀ s : Su F p f a, φ s ∈ L := fun s => by
      rw [hLeq, hAm]
      exact ⟨blockEmb F p f n a 0 (by omega) s, ⟨s, rfl⟩, rfl⟩
    have hord : ∀ s : Su F p f a, s * s = 1 → s ≠ 1 → orderOf (φ s) = 2 := fun s hs hs1 => by
      rw [orderOf_injective φ hφ s]
      exact orderOf_eq_prime (by rw [pow_two]; exact hs) hs1
    refine false_of_two_commuting_involutions_sl2 hodd e2 (a := ⟨φ s, hmem s⟩) (b := ⟨φ t, hmem t⟩)
      (by rw [Subgroup.orderOf_mk]; exact hord s hs2 hs1)
      (by rw [Subgroup.orderOf_mk]; exact hord t ht2 ht1) ?_ ?_
    · apply Subtype.ext
      show φ s * φ t = φ t * φ s
      rw [← map_mul, ← map_mul, hst]
    · intro hab
      exact hne (hφ (congrArg Subtype.val hab))
  obtain rfl : a = 2 := by omega
  refine ⟨g, ?_, ?_⟩
  · rw [hLeq, hAm]
    rfl
  · apply suMat_injective
    rw [suMat_mul, suMat_mul, suMat_rootInvSU]
    calc suMat z = suMat z * (suMat g * suMat g⁻¹) := by
          rw [suMat_mul_suMat_inv, Matrix.mul_one]
      _ = (suMat z * suMat g) * suMat g⁻¹ := (Matrix.mul_assoc _ _ _).symm
      _ = suMat g * negBlock F n 0 * suMat g⁻¹ := by rw [hg]; rfl

end Main

end CFSG.ClassicalInvolution.ModelFacts
