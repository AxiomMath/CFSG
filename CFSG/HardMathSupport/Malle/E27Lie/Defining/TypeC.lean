module

public import CFSG.HardMathSupport.Malle.E27Lie.Defining.AbelianKill
public import CFSG.HardMathSupport.Malle.E27Lie.Defining.Unitriangular
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.HardMathSupport.Foote.E27 CFSG.Assembly.LowTwoRank TauCeti

variable {r : ℕ} {F : Type} [Field F]

theorem unitri_apply_last {A : Matrix (Fin r) (Fin r) F} (hA : IsUnitriangular A)
    (hr : 1 ≤ r) (a : Fin r) :
    A ⟨r - 1, by omega⟩ a = if a = ⟨r - 1, by omega⟩ then 1 else 0 := by
  split_ifs with ha
  · rw [ha, hA.2]
  · have hlt : a < ⟨r - 1, by omega⟩ := by
      rw [Fin.lt_def]
      have h1 := a.2
      have h2 : a.val ≠ r - 1 := fun h => ha (Fin.ext h)
      show a.val < r - 1
      omega
    exact hA.1 hlt

theorem unitri_mul_apply_last {A : Matrix (Fin r) (Fin r) F} (hA : IsUnitriangular A)
    (hr : 1 ≤ r) (C : Matrix (Fin r) (Fin r) F) (b : Fin r) :
    (A * C) ⟨r - 1, by omega⟩ b = C ⟨r - 1, by omega⟩ b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨r - 1, by omega⟩]
  · simp [unitri_apply_last hA hr]
  · intro a _ ha
    simp [unitri_apply_last hA hr, ha]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem unitri_conj_apply_last {D : Matrix (Fin r) (Fin r) F} (hD : IsUnitriangular D)
    (hr : 1 ≤ r) (C : Matrix (Fin r) (Fin r) F) :
    (D * C * Dᵀ) ⟨r - 1, by omega⟩ ⟨r - 1, by omega⟩ =
      C ⟨r - 1, by omega⟩ ⟨r - 1, by omega⟩ := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨r - 1, by omega⟩]
  · rw [unitri_mul_apply_last hD hr, Matrix.transpose_apply, hD.2, mul_one]
  · intro b _ hb
    simp [unitri_apply_last hD hr, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem unitri_sub_one_mem {A : Matrix (Fin r) (Fin r) F}
    (hA : IsUnitriangular A) : A - 1 ∈ strictUpper r F := fun a b hba => by
  rcases hba.lt_or_eq with h | rfl
  · rw [Matrix.sub_apply, hA.1 h, Matrix.one_apply_ne (ne_of_gt h), sub_zero]
  · rw [Matrix.sub_apply, hA.2, Matrix.one_apply_eq, sub_self]

theorem unitri_mul_apply_succ {A D : Matrix (Fin r) (Fin r) F} (hA : IsUnitriangular A)
    (hD : IsUnitriangular D) (i : Fin (r - 1)) :
    (A * D) ⟨i, by omega⟩ ⟨i + 1, by omega⟩ =
      A ⟨i, by omega⟩ ⟨i + 1, by omega⟩ + D ⟨i, by omega⟩ ⟨i + 1, by omega⟩ := by
  have h0 := mul_superdiag_eq_zero (unitri_sub_one_mem hA) (unitri_sub_one_mem hD) i
  have hAD : A * D = 1 + (A - 1) + (D - 1) + (A - 1) * (D - 1) := by noncomm_ring
  have hne : (⟨i, by omega⟩ : Fin r) ≠ ⟨i + 1, by omega⟩ := by simp [Fin.ext_iff]
  rw [hAD, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, h0, Matrix.one_apply_ne hne,
    Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply_ne hne]
  ring

@[expose] def spCoord (hr : 1 ≤ r) (g : StatedSp r F) : (Fin (r - 1) → F) × F :=
  (fun i => ((g : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)
      (Sum.inl ⟨i, by omega⟩) (Sum.inl ⟨i + 1, by omega⟩),
    ((g : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)
      (Sum.inl ⟨r - 1, by omega⟩) (Sum.inr ⟨r - 1, by omega⟩))

theorem spCoord_of_blockMat (hr : 1 ≤ r) {g : StatedSp r F} {A C : Matrix (Fin r) (Fin r) F}
    (hA : IsUnitriangular A)
    (hg : ((g : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
      blockMat A C) :
    spCoord hr g = (fun i : Fin (r - 1) => A ⟨i, by omega⟩ ⟨i + 1, by omega⟩,
      C ⟨r - 1, by omega⟩ ⟨r - 1, by omega⟩) := by
  simp only [spCoord, hg, blockMat, fromBlocks_apply₁₁, fromBlocks_apply₁₂]
  rw [unitri_mul_apply_last hA hr]

@[expose] noncomputable def unipotentCoord (hr : 1 ≤ r) :
    unipotent r F →* Multiplicative ((Fin (r - 1) → F) × F) where
  toFun g := Multiplicative.ofAdd (spCoord hr (g : StatedSp r F))
  map_one' := by
    have h1 : (((1 : StatedSp r F) : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = blockMat 1 0 := by
      rw [blockMat_one]
      rfl
    show Multiplicative.ofAdd (spCoord hr (1 : StatedSp r F)) = 1
    rw [spCoord_of_blockMat hr isUnitriangular_one h1]
    have hne : ∀ i : Fin (r - 1), (⟨i, by omega⟩ : Fin r) ≠ ⟨i + 1, by omega⟩ := fun i => by
      simp [Fin.ext_iff]
    simp only [Matrix.one_apply_ne (hne _), Matrix.zero_apply]
    rfl
  map_mul' g h := by
    obtain ⟨A, C, hA, -, hg⟩ := g.2
    obtain ⟨D, E, hD, -, hh⟩ := h.2
    have hgh : ((((g * h : unipotent r F) : StatedSp r F) : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = blockMat (A * D) (E + D⁻¹ * C * D⁻¹ᵀ) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, hg, hh, blockMat_mul hD.isUnit_det]
    rw [← ofAdd_add, spCoord_of_blockMat hr (hA.mul hD) hgh, spCoord_of_blockMat hr hA hg,
      spCoord_of_blockMat hr hD hh]
    congr 1
    refine Prod.ext (funext fun i => ?_) ?_
    · simp only [Prod.fst_add, Pi.add_apply]
      exact unitri_mul_apply_succ hA hD i
    · simp only [Prod.snd_add, Matrix.add_apply]
      rw [unitri_conj_apply_last hD.inv hr]
      ring

theorem unipotentCoord_surjective (hr : 1 ≤ r) :
    Function.Surjective (unipotentCoord (F := F) hr) := by
  intro x
  obtain ⟨M₀, hM₀⟩ := superdiag_surjective (n := r) (K := F) (Multiplicative.toAdd x).1
  have hA : IsUnitriangular (1 + (M₀ : Matrix (Fin r) (Fin r) F)) := by
    refine ⟨fun a b hba => ?_, fun a => ?_⟩
    · have hba' : b < a := hba
      rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hba'), M₀.2 a b hba'.le, add_zero]
    · rw [Matrix.add_apply, Matrix.one_apply_eq, M₀.2 a a le_rfl, add_zero]
  set c := (Multiplicative.toAdd x).2
  have hC : (Matrix.single (⟨r - 1, by omega⟩ : Fin r) (⟨r - 1, by omega⟩ : Fin r) c)ᵀ =
      Matrix.single (⟨r - 1, by omega⟩ : Fin r) (⟨r - 1, by omega⟩ : Fin r) c := by
    rw [Matrix.transpose_single]
  obtain ⟨g, hgU, hg⟩ := exists_mem_unipotent hA hC
  refine ⟨⟨g, hgU⟩, ?_⟩
  show Multiplicative.ofAdd (spCoord hr g) = x
  rw [spCoord_of_blockMat hr hA hg]
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd]
  refine Prod.ext (funext fun i => ?_) ?_
  · have hne : (⟨i, by omega⟩ : Fin r) ≠ ⟨i + 1, by omega⟩ := by simp [Fin.ext_iff]
    dsimp only
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, ← hM₀, superdiag_apply]
  · simp [c]

@[expose] noncomputable def unipotentEquivProj (hr : 1 ≤ r) :
    unipotent r F ≃* projUnipotent r F :=
  MulEquiv.ofBijective ((proj r F).subgroupMap (unipotent r F))
    ⟨fun x y h => Subtype.ext (proj_injOn_unipotent hr x.2 y.2 (congrArg Subtype.val h)),
      (proj r F).subgroupMap_surjective _⟩

theorem false_of_psp_model_char_three {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K) {r f : ℕ}
    (hcl : StatedClassicalModel K .PSp r 3 f) (hr : 1 ≤ r) (hfr : 4 ≤ f * r) : False := by
  obtain ⟨-, F, _, _, hFcard, ⟨e⟩⟩ := hcl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 3 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hFcard])
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := F) 3 hr
  have hPcard : Nat.card (projUnipotent r F) =
      3 ^ (Nat.card (StatedProj (StatedSp r F))).factorization 3 := by
    rw [← hP]
    exact P.card_eq_multiplicity
  refine E27Config.false_of_sylow_hom_comm h hz e (projUnipotent r F) hPcard
    ((unipotentCoord hr).comp (unipotentEquivProj hr).symm.toMonoidHom)
    ((unipotentCoord_surjective hr).comp (unipotentEquivProj hr).symm.surjective) ?_
  have hcard : Nat.card (Multiplicative ((Fin (r - 1) → F) × F)) = 3 ^ (f * r) := by
    rw [show Nat.card (Multiplicative ((Fin (r - 1) → F) × F)) = Nat.card ((Fin (r - 1) → F) × F)
      from rfl, Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin (r - 1)),
      Fintype.card_fin, hFcard, ← pow_mul, ← pow_add]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [hcard]
  calc 81 = 3 ^ 4 := by norm_num
    _ ≤ 3 ^ (f * r) := Nat.pow_le_pow_right (by norm_num) hfr

theorem false_of_typeC_char_three {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.C r q).Valid) (hp : q.p = 3) (hfr : 4 ≤ q.exponent * r)
    (e : ↥K ≃* (CFSGIndex.lie ⟨.C r q, hv⟩).Group) : False := by
  have hcl := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e
  rw [hp] at hcl
  have hr : 1 ≤ r := by
    have := q.exponent_pos
    by_contra h0
    push Not at h0
    interval_cases r
    omega
  exact false_of_psp_model_char_three h hz hcl hr hfr

theorem false_of_typeB2_char_three {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid)
    (hp : q.p = 3) (e : ↥K ≃* (CFSGIndex.lie ⟨.B 2 q, hv⟩).Group) : False := by
  have hcl := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
  rw [hp] at hcl
  have hv' := hv
  rw [LieTypeIndex.valid_iff, LieTypeIndex.isDuplicateRepresentative_iff] at hv'
  have hf : 2 ≤ q.exponent := by
    by_contra h1
    push Not at h1
    have hf1 : q.exponent = 1 := by have := q.exponent_pos; omega
    exact hv'.2 ⟨rfl, by rw [PrimePower.card_def, hp, hf1]; norm_num⟩
  exact false_of_psp_model_char_three h hz hcl (by norm_num) (by omega)

end CFSG.HardMathSupport.Malle.E27Lie
