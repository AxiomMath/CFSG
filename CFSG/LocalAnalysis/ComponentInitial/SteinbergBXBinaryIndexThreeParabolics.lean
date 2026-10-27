module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBorelOvergroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

namespace BinaryParabolic

open Matrix Subgroup

variable {n : ℕ}

theorem eq_one_of_ne_zero : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

theorem upperTriangular_eq_unitriangular :
    upperTriangular n (ZMod 2) = unitriangular n (ZMod 2) := by
  refine le_antisymm (fun A hA => ⟨hA, fun i => eq_one_of_ne_zero _ fun h0 => ?_⟩)
    (unitriangular_le_upperTriangular n _)
  have hdet : (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := A.2
  rw [det_of_isUpperTriangular (mem_upperTriangular_iff_isUpperTriangular.mp hA),
    Finset.prod_eq_zero (f := fun k => (A : Matrix (Fin n) (Fin n) (ZMod 2)) k k)
      (Finset.mem_univ i) h0] at hdet
  exact zero_ne_one hdet

theorem flagStabilizer_anti {K : Type*} [Field K] {I J : Set ℕ} (h : I ⊆ J) :
    flagStabilizer n K J ≤ flagStabilizer n K I := fun _ hg =>
  mem_flagStabilizer.mpr fun i hi => mem_flagStabilizer.mp hg i (h hi)

theorem mem_cuts {i j : ℕ} : i ∈ Set.Icc 1 (n - 1) \ {j} ↔ 1 ≤ i ∧ i ≤ n - 1 ∧ i ≠ j := by
  simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_singleton_iff, and_assoc]

theorem flagStabilizer_Icc :
    flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1)) = unitriangular n (ZMod 2) := by
  rw [(subflag_stabilizer_generation (K := ZMod 2) (n := n) (Set.Icc 1 (n - 1))).1,
    ← upperTriangular_eq_unitriangular]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g (hg | ⟨j, hj, hjn, hjI, rfl⟩)
    · exact hg
    · exact absurd ⟨hj, by omega⟩ hjI
  · intro g hg
    exact Subgroup.subset_closure (Or.inl hg)

theorem unitriangular_le_flagStabilizer (I : Set ℕ) :
    unitriangular n (ZMod 2) ≤ flagStabilizer n (ZMod 2) I :=
  (unitriangular_le_upperTriangular n _).trans (upperTriangular_le_flagStabilizer I)

variable {j : ℕ}

theorem reflection_mem_parabolic (hj : 1 ≤ j) (hjn : j < n) :
    reflection n (ZMod 2) j hj hjn ∈ flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}) :=
  ((subflag_stabilizer_generation _).2.2 j hj hjn).mpr fun h => h.2 (Set.mem_singleton j)

theorem reflection_notMem_unitriangular (hj : 1 ≤ j) (hjn : j < n) :
    reflection n (ZMod 2) j hj hjn ∉ unitriangular n (ZMod 2) := by
  rw [← flagStabilizer_Icc]
  exact fun h => ((subflag_stabilizer_generation _).2.2 j hj hjn).mp h ⟨hj, by omega⟩

theorem eq_of_reflection_mem_parabolic {k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (h : reflection n (ZMod 2) k hk hkn ∈ flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})) :
    k = j := by
  by_contra hkj
  exact ((subflag_stabilizer_generation _).2.2 k hk hkn).mp h (mem_cuts.2 ⟨hk, by omega, hkj⟩)

theorem mem_unitriangular_of_mem_parabolic {g : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : g ∈ flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}))
    (hgj : g ∈ stabilizer (flagSpace n (ZMod 2) j)) : g ∈ unitriangular n (ZMod 2) := by
  rw [← flagStabilizer_Icc, mem_flagStabilizer]
  intro i hi
  by_cases hij : i = j
  · rw [hij]
    exact hgj
  · exact mem_flagStabilizer.mp hg i ⟨hi, hij⟩

theorem mulVec_mem_of_mem_flagStabilizer {K : Type*} [Field K] {I : Set ℕ}
    {g : SpecialLinearGroup (Fin n) K} (hg : g ∈ flagStabilizer n K I) {i : ℕ} (hi : i ∈ I)
    {v : Fin n → K} (hv : v ∈ flagSpace n K i) :
    (g : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ flagSpace n K i := by
  rw [← mem_stabilizer.mp (mem_flagStabilizer.mp hg i hi)]
  exact ⟨v, hv, rfl⟩

theorem single_mem_flagSpace {K : Type*} [Field K] {c : Fin n} {i : ℕ} (h : (c : ℕ) < i) :
    (Pi.single c 1 : Fin n → K) ∈ flagSpace n K i :=
  Submodule.subset_span ⟨c, h, rfl⟩

theorem mulVec_mem_flagSpace_pred (hjn : j < n) {g : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : g ∈ flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})) {v : Fin n → ZMod 2}
    (hv : v ∈ flagSpace n (ZMod 2) (j - 1)) :
    (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v ∈ flagSpace n (ZMod 2) (j - 1) := by
  rcases Nat.eq_zero_or_pos (j - 1) with h0 | h0
  · rw [h0, flagSpace_zero, Submodule.mem_bot] at hv ⊢
    rw [hv, mulVec_zero]
  · exact mulVec_mem_of_mem_flagStabilizer hg (mem_cuts.2 ⟨h0, by omega, by omega⟩) hv

theorem mulVec_mem_flagSpace_succ {g : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : g ∈ flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})) {v : Fin n → ZMod 2}
    (hv : v ∈ flagSpace n (ZMod 2) (j + 1)) :
    (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v ∈ flagSpace n (ZMod 2) (j + 1) := by
  by_cases h : j + 1 < n
  · exact mulVec_mem_of_mem_flagStabilizer hg (mem_cuts.2 ⟨by omega, by omega, by omega⟩) hv
  · rw [mem_flagSpace]
    intro c hc
    exact absurd c.isLt (by omega)

theorem mul_unitriangular_apply (hjn : j < n) {g u : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : g ∈ flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}))
    (hu : u ∈ unitriangular n (ZMod 2)) (c : Fin n) (hc : j - 1 ≤ (c : ℕ)) :
    ((g * u : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) c
        ⟨j - 1, by omega⟩ =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) c ⟨j - 1, by omega⟩ := by
  set a : Fin n := ⟨j - 1, by omega⟩ with ha
  have hw : (u : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single a 1 - Pi.single a 1 ∈
      flagSpace n (ZMod 2) (j - 1) := by
    rw [mem_flagSpace]
    intro d hd
    rw [Pi.sub_apply, mulVec_single_one, col_apply]
    rcases eq_or_lt_of_le hd with h | h
    · have hda : d = a := Fin.ext h.symm
      rw [hda, hu.2 a, Pi.single_eq_same, sub_self]
    · have hda : a < d := h
      rw [hu.1 d a hda, Pi.single_eq_of_ne (ne_of_gt hda), sub_self]
  have h1 := (mem_flagSpace.mp (mulVec_mem_flagSpace_pred hjn hg hw)) c hc
  rw [mulVec_sub, Pi.sub_apply, sub_eq_zero, mulVec_mulVec, mulVec_single_one,
    mulVec_single_one, col_apply, col_apply] at h1
  rw [SpecialLinearGroup.coe_mul]
  exact h1

theorem col_mem_flagSpace_succ (hj : 1 ≤ j) (hjn : j < n)
    {g : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : g ∈ flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})) :
    (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single ⟨j - 1, by omega⟩ 1 ∈
      flagSpace n (ZMod 2) (j + 1) :=
  mulVec_mem_flagSpace_succ hg (single_mem_flagSpace (by change j - 1 < j + 1; omega))

theorem inv_mul_mem_unitriangular (hj : 1 ≤ j) (hjn : j < n)
    {g h : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : g ∈ flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}))
    (hh : h ∈ flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}))
    (h1 : (g : Matrix (Fin n) (Fin n) (ZMod 2)) ⟨j - 1, by omega⟩ ⟨j - 1, by omega⟩ =
      (h : Matrix (Fin n) (Fin n) (ZMod 2)) ⟨j - 1, by omega⟩ ⟨j - 1, by omega⟩)
    (h2 : (g : Matrix (Fin n) (Fin n) (ZMod 2)) ⟨j, hjn⟩ ⟨j - 1, by omega⟩ =
      (h : Matrix (Fin n) (Fin n) (ZMod 2)) ⟨j, hjn⟩ ⟨j - 1, by omega⟩) :
    h⁻¹ * g ∈ unitriangular n (ZMod 2) := by
  set a : Fin n := ⟨j - 1, by omega⟩ with ha
  have hx : h⁻¹ * g ∈ flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}) :=
    mul_mem (inv_mem hh) hg
  have hhinv : h⁻¹ ∈ flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}) := inv_mem hh
  have hd : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single a 1 -
      (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single a 1 ∈ flagSpace n (ZMod 2) (j - 1) := by
    have hg1 := mem_flagSpace.mp (col_mem_flagSpace_succ hj hjn hg)
    have hh1 := mem_flagSpace.mp (col_mem_flagSpace_succ hj hjn hh)
    rw [mem_flagSpace]
    intro c hc
    rw [Pi.sub_apply, sub_eq_zero]
    rcases lt_or_ge (c : ℕ) (j + 1) with hcj | hcj
    · rcases (show (c : ℕ) = j - 1 ∨ (c : ℕ) = j by omega) with hc' | hc'
      · rw [show c = a from Fin.ext hc', mulVec_single_one, mulVec_single_one, col_apply,
          col_apply]
        exact h1
      · rw [show c = ⟨j, hjn⟩ from Fin.ext hc', mulVec_single_one, mulVec_single_one, col_apply,
          col_apply]
        exact h2
    · rw [hg1 c hcj, hh1 c hcj]
  refine mem_unitriangular_of_mem_parabolic hx (mem_stabilizer_of_map_le ?_)
  rw [flagSpace, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  change ((h⁻¹ * g : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
    Pi.single c 1 ∈ flagSpace n (ZMod 2) j
  have hc' : (c : ℕ) < j := hc
  rcases (show (c : ℕ) < j - 1 ∨ (c : ℕ) = j - 1 by omega) with hcj | hcj
  · exact flagSpace_mono (by omega)
      (mulVec_mem_flagSpace_pred hjn hx (single_mem_flagSpace hcj))
  · rw [show c = a from Fin.ext hcj, SpecialLinearGroup.coe_mul, ← mulVec_mulVec,
      show (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single a 1 =
        (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single a 1 +
          ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single a 1 -
            (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single a 1) by abel,
      mulVec_add, mulVec_mulVec, coe_inv_mul_coe, one_mulVec]
    exact Submodule.add_mem _ (single_mem_flagSpace (by simp [ha]; omega))
      (flagSpace_mono (by omega) (mulVec_mem_flagSpace_pred hjn hhinv hd))

theorem colPair_ne_zero (hj : 1 ≤ j) (hjn : j < n) {g : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : g ∈ flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})) :
    ((g : Matrix (Fin n) (Fin n) (ZMod 2)) ⟨j - 1, by omega⟩ ⟨j - 1, by omega⟩,
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) ⟨j, hjn⟩ ⟨j - 1, by omega⟩) ≠ 0 := by
  set a : Fin n := ⟨j - 1, by omega⟩ with ha
  intro h0
  have h1 : (g : Matrix (Fin n) (Fin n) (ZMod 2)) a a = 0 := congrArg Prod.fst h0
  have h2 : (g : Matrix (Fin n) (Fin n) (ZMod 2)) ⟨j, hjn⟩ a = 0 := congrArg Prod.snd h0
  have hcol : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single a 1 ∈
      flagSpace n (ZMod 2) (j - 1) := by
    have hg1 := mem_flagSpace.mp (col_mem_flagSpace_succ hj hjn hg)
    rw [mem_flagSpace]
    intro c hc
    rcases lt_or_ge (c : ℕ) (j + 1) with hcj | hcj
    · rcases (show (c : ℕ) = j - 1 ∨ (c : ℕ) = j by omega) with hc' | hc'
      · rw [show c = a from Fin.ext hc', mulVec_single_one, col_apply]
        exact h1
      · rw [show c = ⟨j, hjn⟩ from Fin.ext hc', mulVec_single_one, col_apply]
        exact h2
    · exact hg1 c hcj
  have hback := mem_flagSpace.mp (mulVec_mem_flagSpace_pred hjn (inv_mem hg) hcol) a le_rfl
  rw [mulVec_mulVec, coe_inv_mul_coe, one_mulVec, Pi.single_eq_same] at hback
  exact one_ne_zero hback

theorem relIndex_parabolic_le (hj : 1 ≤ j) (hjn : j < n) :
    (unitriangular n (ZMod 2)).relIndex (flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})) ≤
      3 := by
  set M := flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}) with hM
  set a : Fin n := ⟨j - 1, by omega⟩ with ha
  set b : Fin n := ⟨j, hjn⟩ with hb
  let φ : M → {x : ZMod 2 × ZMod 2 // x ≠ 0} := fun g =>
    ⟨(((g : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) a a,
      ((g : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) b a),
      colPair_ne_zero hj hjn g.2⟩
  have hφ : ∀ g h : M, g⁻¹ * h ∈ (unitriangular n (ZMod 2)).subgroupOf M → φ g = φ h := by
    intro g h hgh
    rw [mem_subgroupOf] at hgh
    have e : (h : SpecialLinearGroup (Fin n) (ZMod 2)) =
        (g : SpecialLinearGroup (Fin n) (ZMod 2)) * ((g⁻¹ * h : M) : _) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    apply Subtype.ext
    change (_, _) = (_, _)
    rw [e, mul_unitriangular_apply hjn g.2 hgh a le_rfl,
      mul_unitriangular_apply hjn g.2 hgh b (by simp [hb])]
  let ψ : M ⧸ (unitriangular n (ZMod 2)).subgroupOf M → {x : ZMod 2 × ZMod 2 // x ≠ 0} :=
    Quotient.lift φ fun g h hgh => hφ g h (QuotientGroup.leftRel_apply.mp hgh)
  have hψ : Function.Injective ψ := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H g => ?_
    induction y using QuotientGroup.induction_on with | H h => ?_
    have hgh : φ g = φ h := hxy
    have h1 := congrArg (fun x => (x.1 : ZMod 2 × ZMod 2).1) hgh
    have h2 := congrArg (fun x => (x.1 : ZMod 2 × ZMod 2).2) hgh
    have hu := inv_mul_mem_unitriangular hj hjn h.2 g.2 h1.symm h2.symm
    refine QuotientGroup.eq.mpr ?_
    rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hu
  rw [Subgroup.relIndex, Subgroup.index]
  calc Nat.card (M ⧸ (unitriangular n (ZMod 2)).subgroupOf M)
      ≤ Nat.card {x : ZMod 2 × ZMod 2 // x ≠ 0} := Nat.card_le_card_of_injective ψ hψ
    _ = 3 := by rw [Nat.card_eq_fintype_card]; decide

theorem relIndex_parabolic (hj : 1 ≤ j) (hjn : j < n) :
    (unitriangular n (ZMod 2)).relIndex (flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})) =
      3 := by
  have hle := relIndex_parabolic_le hj hjn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := n) (by omega)
  have hodd : ¬ 2 ∣ (unitriangular n (ZMod 2)).relIndex
      (flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})) := fun h2 => by
    have h := T.not_dvd_index
    rw [hT] at h
    exact h (h2.trans (relIndex_dvd_index_of_le (unitriangular_le_flagStabilizer _)))
  have hne1 : (unitriangular n (ZMod 2)).relIndex
      (flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})) ≠ 1 := fun h1 =>
    reflection_notMem_unitriangular hj hjn
      (relIndex_eq_one.mp h1 (reflection_mem_parabolic hj hjn))
  omega

theorem parabolic_eq_closure (hj : 1 ≤ j) (hjn : j < n) :
    flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}) =
      Subgroup.closure ((unitriangular n (ZMod 2) : Set (SpecialLinearGroup (Fin n) (ZMod 2))) ∪
        {reflection n (ZMod 2) j hj hjn}) := by
  rw [(subflag_stabilizer_generation _).1, subflagGenerators, upperTriangular_eq_unitriangular]
  congr 2
  ext g
  constructor
  · rintro ⟨k, hk, hkn, hkI, rfl⟩
    obtain rfl : k = j := by
      by_contra hkj
      exact hkI (mem_cuts.2 ⟨hk, by omega, hkj⟩)
    rfl
  · rintro rfl
    exact ⟨j, hj, hjn, fun h => h.2 (Set.mem_singleton j), rfl⟩

theorem reflection_eq_permMatrix (hj : 1 ≤ j) (hjn : j < n) :
    (reflection n (ZMod 2) j hj hjn : Matrix (Fin n) (Fin n) (ZMod 2)) =
      permMatrix n (ZMod 2) (Equiv.swap ⟨j - 1, by omega⟩ ⟨j, hjn⟩) := by
  rw [coe_reflection, reflectionMatrix_eq j hj hjn,
    show (-1 : ZMod 2) = 1 by decide]
  simp only [ite_self, diagonal_one, mul_one]

theorem permMatrix_mul_permMatrix {K : Type*} [Field K] (σ τ : Equiv.Perm (Fin n)) :
    permMatrix n K σ * permMatrix n K τ = permMatrix n K (σ * τ) := by
  rw [permMatrix_eq, permMatrix_eq, permMatrix_eq, ← Matrix.permMatrix_mul, _root_.mul_inv_rev]

theorem permMatrix_one' {K : Type*} [Field K] : permMatrix n K 1 = 1 := by
  rw [permMatrix_eq, inv_one, Matrix.permMatrix_one]

theorem transpose_permMatrix' {K : Type*} [Field K] (σ : Equiv.Perm (Fin n)) :
    (permMatrix n K σ)ᵀ = permMatrix n K σ⁻¹ := by
  rw [permMatrix_eq, permMatrix_eq, Matrix.transpose_permMatrix, inv_inv]

theorem permMatrix_submatrix_rev {K : Type*} [Field K] (σ : Equiv.Perm (Fin n)) :
    (permMatrix n K σ).submatrix Fin.revPerm Fin.revPerm =
      permMatrix n K (Fin.revPerm * σ * Fin.revPerm) := by
  ext x y
  simp only [submatrix_apply, permMatrix_apply, Equiv.Perm.mul_apply, Fin.revPerm_apply,
    Fin.rev_eq_iff]

theorem revMatrix_mul_mul {K : Type*} [Field K] (X : Matrix (Fin n) (Fin n) K) :
    permMatrix n K Fin.revPerm * X * permMatrix n K Fin.revPerm = X.submatrix Fin.rev Fin.rev := by
  rw [permMatrix_eq, Equiv.Perm.inv_def, Fin.revPerm_symm, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix,
    Fin.revPerm_symm]
  rfl

theorem revMatrix_inv {K : Type*} [Field K] :
    (permMatrix n K Fin.revPerm)⁻¹ = permMatrix n K Fin.revPerm := by
  refine Matrix.inv_eq_left_inv ?_
  rw [permMatrix_mul_permMatrix, show (Fin.revPerm : Equiv.Perm (Fin n)) * Fin.revPerm = 1 from
    Equiv.ext fun x => Fin.rev_rev x, permMatrix_one']

@[expose] noncomputable def graphFun (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    SpecialLinearGroup (Fin n) (ZMod 2) :=
  ⟨(((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ).submatrix
      Fin.revPerm Fin.revPerm, by
    rw [det_submatrix_equiv_self, det_transpose]
    exact (g⁻¹).2⟩

theorem coe_graphFun (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    (graphFun g : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ).submatrix
        Fin.revPerm Fin.revPerm :=
  rfl

theorem graphFun_mul (g h : SpecialLinearGroup (Fin n) (ZMod 2)) :
    graphFun (g * h) = graphFun g * graphFun h := by
  apply Subtype.ext
  change (((g * h)⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2))ᵀ.submatrix Fin.revPerm Fin.revPerm =
    (graphFun g : Matrix (Fin n) (Fin n) (ZMod 2)) * graphFun h
  rw [coe_graphFun, coe_graphFun, _root_.mul_inv_rev, SpecialLinearGroup.coe_mul, transpose_mul,
    submatrix_mul_equiv]

theorem graphFun_one : graphFun (1 : SpecialLinearGroup (Fin n) (ZMod 2)) = 1 := by
  apply Subtype.ext
  rw [coe_graphFun, inv_one, SpecialLinearGroup.coe_one, transpose_one, submatrix_one_equiv]

theorem graphFun_inv (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    graphFun g⁻¹ = (graphFun g)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← graphFun_mul, inv_mul_cancel, graphFun_one]

theorem graphFun_graphFun (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    graphFun (graphFun g) = g := by
  apply Subtype.ext
  rw [coe_graphFun, ← graphFun_inv, coe_graphFun, inv_inv, transpose_submatrix,
    transpose_transpose, submatrix_submatrix]
  ext a b
  simp

@[expose] noncomputable def graphAut (n : ℕ) : MulAut (SpecialLinearGroup (Fin n) (ZMod 2)) where
  toFun := graphFun
  invFun := graphFun
  left_inv := graphFun_graphFun
  right_inv := graphFun_graphFun
  map_mul' := graphFun_mul

theorem graphAut_apply (g : SpecialLinearGroup (Fin n) (ZMod 2)) : graphAut n g = graphFun g :=
  rfl

theorem coe_graphAut (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    ((graphAut n g : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      permMatrix n (ZMod 2) Fin.revPerm *
        ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *
          (permMatrix n (ZMod 2) Fin.revPerm)⁻¹ := by
  rw [revMatrix_inv, revMatrix_mul_mul]
  rfl

theorem graphFun_mem_unitriangular {u : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hu : u ∈ unitriangular n (ZMod 2)) : graphFun u ∈ unitriangular n (ZMod 2) := by
  have hu' := inv_mem hu
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [coe_graphFun, submatrix_apply, transpose_apply]
    exact hu'.1 _ _ (Fin.rev_lt_rev.mpr hab)
  · rw [coe_graphFun, submatrix_apply, transpose_apply]
    exact hu'.2 _

theorem map_graphAut_unitriangular :
    (unitriangular n (ZMod 2)).map (graphAut n).toMonoidHom = unitriangular n (ZMod 2) := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact graphFun_mem_unitriangular hu
  · intro u hu
    exact ⟨graphFun u, graphFun_mem_unitriangular hu, graphFun_graphFun u⟩

theorem graphFun_reflection (hj : 1 ≤ j) (hjn : j < n) :
    graphFun (reflection n (ZMod 2) j hj hjn) =
      reflection n (ZMod 2) (n - j) (by omega) (by omega) := by
  have hsq : reflection n (ZMod 2) j hj hjn * reflection n (ZMod 2) j hj hjn = 1 := by
    apply Subtype.ext
    rw [SpecialLinearGroup.coe_mul, reflection_eq_permMatrix, permMatrix_mul_permMatrix,
      Equiv.swap_mul_self, permMatrix_one', SpecialLinearGroup.coe_one]
  have hinv : (reflection n (ZMod 2) j hj hjn)⁻¹ = reflection n (ZMod 2) j hj hjn :=
    inv_eq_of_mul_eq_one_right hsq
  have key : Fin.revPerm * Equiv.swap (⟨j - 1, by omega⟩ : Fin n) ⟨j, hjn⟩ * Fin.revPerm =
      Equiv.swap (⟨n - j - 1, by omega⟩ : Fin n) ⟨n - j, by omega⟩ := by
    have h := Equiv.swap_apply_apply (Fin.revPerm : Equiv.Perm (Fin n))
      (⟨j - 1, by omega⟩ : Fin n) ⟨j, hjn⟩
    rw [show (Fin.revPerm : Equiv.Perm (Fin n))⁻¹ = Fin.revPerm by
      rw [Equiv.Perm.inv_def, Fin.revPerm_symm]] at h
    rw [← h, Equiv.swap_comm]
    congr 1
    exact Fin.ext (by simp; omega)
  apply Subtype.ext
  rw [coe_graphFun, hinv, reflection_eq_permMatrix, reflection_eq_permMatrix, transpose_permMatrix',
    Equiv.swap_inv, permMatrix_submatrix_rev, key]

theorem map_graphAut_parabolic (hj : 1 ≤ j) (hjn : j < n) :
    (flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})).map (graphAut n).toMonoidHom =
      flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {n - j}) := by
  rw [parabolic_eq_closure hj hjn, parabolic_eq_closure (j := n - j) (by omega) (by omega),
    MonoidHom.map_closure, Set.image_union, Set.image_singleton, ← Subgroup.coe_map,
    map_graphAut_unitriangular]
  congr 3
  exact graphFun_reflection hj hjn

abbrev OutsidePlane : Type := {v : Fin 3 → ZMod 2 // v 2 = 1}

theorem card_outsidePlane : Fintype.card OutsidePlane = 4 := by decide

theorem mulVec_outsidePlane {g : SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hg : g ∈ flagStabilizer 3 (ZMod 2) (Set.Icc 1 (3 - 1) \ {1})) (v : Fin 3 → ZMod 2)
    (hv : v 2 = 1) : ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) 2 = 1 := by
  have h2 : (2 : ℕ) ∈ Set.Icc 1 (3 - 1) \ {1} := mem_cuts.2 ⟨by norm_num, by norm_num, by norm_num⟩
  have hc0 := mem_flagSpace.mp (mulVec_mem_of_mem_flagStabilizer hg h2
    (single_mem_flagSpace (c := (0 : Fin 3)) (by decide))) 2 (by decide)
  have hc1 := mem_flagSpace.mp (mulVec_mem_of_mem_flagStabilizer hg h2
    (single_mem_flagSpace (c := (1 : Fin 3)) (by decide))) 2 (by decide)
  rw [mulVec_single_one, col_apply] at hc0 hc1
  have hg22 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 2 = 1 := by
    apply eq_one_of_ne_zero
    intro h0
    have hrow : ∀ c, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 c = 0 := by
      intro c
      fin_cases c
      · exact hc0
      · exact hc1
      · exact h0
    have hdet := det_eq_zero_of_row_eq_zero 2 hrow
    rw [g.2] at hdet
    exact one_ne_zero hdet
  simp only [mulVec, dotProduct, Fin.sum_univ_three]
  rw [hc0, hc1, hg22, hv]
  simp

@[expose] noncomputable def parabolicOnePerm
    (g : flagStabilizer 3 (ZMod 2) (Set.Icc 1 (3 - 1) \ {1})) : Equiv.Perm OutsidePlane where
  toFun v := ⟨((g : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
    v.1, mulVec_outsidePlane g.2 v.1 v.2⟩
  invFun v := ⟨(((g⁻¹ : flagStabilizer 3 (ZMod 2) (Set.Icc 1 (3 - 1) \ {1})) :
    SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v.1,
    mulVec_outsidePlane (g⁻¹).2 v.1 v.2⟩
  left_inv v := Subtype.ext (by
    change (((g⁻¹ : flagStabilizer 3 (ZMod 2) (Set.Icc 1 (3 - 1) \ {1})) :
      SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        (((g : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v.1) =
          v.1
    rw [mulVec_mulVec, Subgroup.coe_inv, coe_inv_mul_coe, one_mulVec])
  right_inv v := Subtype.ext (by
    change ((g : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
      ((((g⁻¹ : flagStabilizer 3 (ZMod 2) (Set.Icc 1 (3 - 1) \ {1})) :
        SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v.1) = v.1
    rw [mulVec_mulVec, Subgroup.coe_inv, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
      SpecialLinearGroup.coe_one, one_mulVec])

@[expose] noncomputable def parabolicOneAction :
    flagStabilizer 3 (ZMod 2) (Set.Icc 1 (3 - 1) \ {1}) →* Equiv.Perm OutsidePlane where
  toFun := parabolicOnePerm
  map_one' := Equiv.ext fun v => Subtype.ext (one_mulVec v.1)
  map_mul' _ _ := Equiv.ext fun v => Subtype.ext (mulVec_mulVec v.1 _ _).symm

theorem parabolicOneAction_injective : Function.Injective parabolicOneAction := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix : ∀ v : OutsidePlane,
      ((g : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v.1 =
        v.1 := fun v => congrArg Subtype.val (Equiv.ext_iff.mp hg v)
  have h0 := hfix ⟨![0, 0, 1], rfl⟩
  have h1 := hfix ⟨![1, 0, 1], rfl⟩
  have h2 := hfix ⟨![0, 1, 1], rfl⟩
  have hmat : ((g : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      1 := by
    refine ext_of_mulVec_single fun k => ?_
    rw [one_mulVec]
    fin_cases k
    · change ((g : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        Pi.single (0 : Fin 3) 1 = Pi.single (0 : Fin 3) 1
      rw [show (Pi.single (0 : Fin 3) 1 : Fin 3 → ZMod 2) = ![1, 0, 1] - ![0, 0, 1] by
        ext i; fin_cases i <;> rfl, mulVec_sub]
      exact congrArg₂ _ h1 h0
    · change ((g : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        Pi.single (1 : Fin 3) 1 = Pi.single (1 : Fin 3) 1
      rw [show (Pi.single (1 : Fin 3) 1 : Fin 3 → ZMod 2) = ![0, 1, 1] - ![0, 0, 1] by
        ext i; fin_cases i <;> rfl, mulVec_sub]
      exact congrArg₂ _ h2 h0
    · change ((g : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        Pi.single (2 : Fin 3) 1 = Pi.single (2 : Fin 3) 1
      rw [show (Pi.single (2 : Fin 3) 1 : Fin 3 → ZMod 2) = ![0, 0, 1] by
        ext i; fin_cases i <;> rfl]
      exact h0
  exact Subtype.ext (SpecialLinearGroup.ext _ _ fun i k => by
    rw [hmat, Subgroup.coe_one, SpecialLinearGroup.coe_one])

theorem card_parabolic_three {j : ℕ} (hj : 1 ≤ j) (hjn : j < 3) :
    Nat.card (flagStabilizer 3 (ZMod 2) (Set.Icc 1 (3 - 1) \ {j})) = 24 := by
  have h := ((unitriangular 3 (ZMod 2)).subgroupOf
    (flagStabilizer 3 (ZMod 2) (Set.Icc 1 (3 - 1) \ {j}))).card_mul_index
  have hU : Nat.card ((unitriangular 3 (ZMod 2)).subgroupOf
      (flagStabilizer 3 (ZMod 2) (Set.Icc 1 (3 - 1) \ {j}))) = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (unitriangular_le_flagStabilizer _)).toEquiv,
      card_unitriangular, Nat.card_zmod]
    norm_num
  rw [hU, ← Subgroup.relIndex, relIndex_parabolic hj hjn] at h
  omega

theorem parabolic_one_equiv :
    Nonempty (flagStabilizer 3 (ZMod 2) (Set.Icc 1 (3 - 1) \ {1}) ≃* Equiv.Perm (Fin 4)) := by
  have hbij : Function.Bijective parabolicOneAction :=
    parabolicOneAction_injective.bijective_of_nat_card_le (by
      rw [Nat.card_perm, Nat.card_eq_fintype_card (α := OutsidePlane), card_outsidePlane,
        card_parabolic_three le_rfl (by norm_num)]
      decide)
  exact ⟨(MulEquiv.ofBijective parabolicOneAction hbij).trans
    (Fintype.equivFinOfCardEq card_outsidePlane).permCongrHom⟩

theorem parabolic_two_equiv :
    Nonempty (flagStabilizer 3 (ZMod 2) (Set.Icc 1 (3 - 1) \ {2}) ≃* Equiv.Perm (Fin 4)) := by
  obtain ⟨e⟩ := parabolic_one_equiv
  have hmap : (flagStabilizer 3 (ZMod 2) (Set.Icc 1 (3 - 1) \ {1})).map (graphAut 3).toMonoidHom =
      flagStabilizer 3 (ZMod 2) (Set.Icc 1 (3 - 1) \ {2}) :=
    map_graphAut_parabolic (n := 3) (j := 1) le_rfl (by norm_num)
  exact ⟨((MulEquiv.subgroupCongr hmap).symm.trans
    ((graphAut 3).subgroupMap _).symm).trans e⟩

theorem parabolics_three_ne_and_sup :
    flagStabilizer 3 (ZMod 2) (Set.Icc 1 (3 - 1) \ {1}) ≠
        flagStabilizer 3 (ZMod 2) (Set.Icc 1 (3 - 1) \ {2}) ∧
      flagStabilizer 3 (ZMod 2) (Set.Icc 1 (3 - 1) \ {1}) ⊔
        flagStabilizer 3 (ZMod 2) (Set.Icc 1 (3 - 1) \ {2}) = ⊤ := by
  refine ⟨fun h => ?_, ?_⟩
  · have hr := reflection_mem_parabolic (n := 3) (j := 1) le_rfl (by norm_num)
    rw [h] at hr
    exact absurd (eq_of_reflection_mem_parabolic (j := 2) le_rfl (by norm_num) hr) (by norm_num)
  · rw [eq_top_iff, ← flagStabilizer_empty 3 (ZMod 2),
      (subflag_stabilizer_generation (K := ZMod 2) (n := 3) ∅).1, Subgroup.closure_le]
    rintro g (hg | ⟨k, hk, hkn, -, rfl⟩)
    · rw [upperTriangular_eq_unitriangular] at hg
      exact Subgroup.mem_sup_left (unitriangular_le_flagStabilizer _ hg)
    · interval_cases k
      · exact Subgroup.mem_sup_left (reflection_mem_parabolic hk hkn)
      · exact Subgroup.mem_sup_right (reflection_mem_parabolic hk hkn)

theorem eq_or_eq_parabolic {A : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hUA : unitriangular n (ZMod 2) ≤ A) (h3 : (unitriangular n (ZMod 2)).relIndex A ≤ 3) :
    A = unitriangular n (ZMod 2) ∨
      ∃! j : ℕ, 1 ≤ j ∧ j < n ∧ A = flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}) := by
  obtain ⟨hAI, -⟩ := borel_overgroups A (upperTriangular_eq_unitriangular ▸ hUA)
  by_cases hex : ∃ j, 1 ≤ j ∧ j < n ∧ j ∉ borelOvergroupCuts A
  · obtain ⟨j, hj, hjn, hjI⟩ := hex
    have hMA : flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}) ≤ A := by
      rw [hAI]
      refine flagStabilizer_anti fun i hi => ?_
      obtain ⟨hi1, hin, hr⟩ := hi
      exact mem_cuts.2 ⟨hi1, by omega, fun hij => hjI (by subst hij; exact ⟨hi1, hin, hr⟩)⟩
    have hmul := relIndex_mul_relIndex _ _ _ (unitriangular_le_flagStabilizer _) hMA
    rw [relIndex_parabolic hj hjn] at hmul
    have hne : (flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})).relIndex A ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    have h1 : (flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})).relIndex A = 1 := by omega
    have hAM : A = flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}) :=
      le_antisymm (relIndex_eq_one.mp h1) hMA
    refine Or.inr ⟨j, ⟨hj, hjn, hAM⟩, fun k ⟨hk, hkn, hAk⟩ => ?_⟩
    have hr : reflection n (ZMod 2) k hk hkn ∈
        flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}) := by
      rw [← hAM, hAk]
      exact reflection_mem_parabolic hk hkn
    exact eq_of_reflection_mem_parabolic hk hkn hr
  · left
    push Not at hex
    have hI : borelOvergroupCuts A = Set.Icc 1 (n - 1) := by
      ext i
      constructor
      · rintro ⟨hi, hin, -⟩
        exact ⟨hi, by omega⟩
      · rintro ⟨hi, hin⟩
        exact hex i hi (by omega)
    rw [hAI, hI, flagStabilizer_Icc]

end BinaryParabolic

open BinaryParabolic Matrix Subgroup

theorem binary_linear_index_three_sylow_overgroups_are_single_root_parabolics {n : ℕ}
    (hn : 3 ≤ n) :
    (∀ g : GeneralLinearGroup (Fin n) (ZMod 2), (g : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1) ∧
    (∀ (j : ℕ) (hj : 1 ≤ j) (hjn : j < n),
      (reflection n (ZMod 2) j hj hjn : Matrix (Fin n) (Fin n) (ZMod 2)) =
        permMatrix n (ZMod 2) (Equiv.swap ⟨j - 1, by omega⟩ ⟨j, hjn⟩)) ∧
    (∀ A : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2)), unitriangular n (ZMod 2) ≤ A →
      (unitriangular n (ZMod 2)).relIndex A ≤ 3 →
      A = unitriangular n (ZMod 2) ∨
        ∃! j : ℕ, 1 ≤ j ∧ j < n ∧ A = flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})) ∧
    (∀ (j : ℕ) (hj : 1 ≤ j) (hjn : j < n),
      flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}) =
          Subgroup.closure ((unitriangular n (ZMod 2) :
            Set (SpecialLinearGroup (Fin n) (ZMod 2))) ∪ {reflection n (ZMod 2) j hj hjn}) ∧
        (unitriangular n (ZMod 2)).relIndex
          (flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})) = 3) ∧
    (n = 3 →
      Nonempty (flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {1}) ≃* Equiv.Perm (Fin 4)) ∧
      Nonempty (flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {2}) ≃* Equiv.Perm (Fin 4)) ∧
      flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {1}) ≠
        flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {2}) ∧
      flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {1}) ⊔
        flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {2}) = ⊤) ∧
    normalizer (unitriangular n (ZMod 2) : Set (SpecialLinearGroup (Fin n) (ZMod 2))) =
      unitriangular n (ZMod 2) ∧
    ∃ γ : MulAut (SpecialLinearGroup (Fin n) (ZMod 2)),
      (∀ g, ((γ g : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
        permMatrix n (ZMod 2) Fin.revPerm *
          ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *
            (permMatrix n (ZMod 2) Fin.revPerm)⁻¹) ∧
      (unitriangular n (ZMod 2)).map γ.toMonoidHom = unitriangular n (ZMod 2) ∧
      ∀ j : ℕ, 1 ≤ j → j < n →
        (flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})).map γ.toMonoidHom =
          flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {n - j}) := by
  refine ⟨fun g => eq_one_of_ne_zero _ ((isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero,
    fun j hj hjn => reflection_eq_permMatrix hj hjn, fun A hUA h3 => eq_or_eq_parabolic hUA h3,
    fun j hj hjn => ⟨parabolic_eq_closure hj hjn, relIndex_parabolic hj hjn⟩, fun h3 => ?_,
    by rw [normalizer_unitriangular, upperTriangular_eq_unitriangular],
    ⟨graphAut n, coe_graphAut, map_graphAut_unitriangular,
      fun j hj hjn => map_graphAut_parabolic hj hjn⟩⟩
  subst h3
  exact ⟨parabolic_one_equiv, parabolic_two_equiv, parabolics_three_ne_and_sup.1,
    parabolics_three_ne_and_sup.2⟩

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
