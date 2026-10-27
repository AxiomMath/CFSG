module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizerBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect derivedSeriesOf
  derivedSeriesOf_zero derivedSeriesOf_succ le_derivedSeriesOf_of_perfect)

namespace InvPlacement

variable {n k : ℕ} (P : InvPlacement n k) {K : Type*} [Field K]

@[expose] def outer : Finset (Fin n) :=
  Finset.univ.image P.supp

theorem mem_outer {i : Fin n} : i ∈ P.outer ↔ ∃ s, P.supp s = i := by
  simp [outer]

theorem u_mem_outer (a : Fin k) : P.u a ∈ P.outer :=
  P.mem_outer.2 ⟨Sum.inl a, rfl⟩

theorem w_mem_outer (a : Fin k) : P.w a ∈ P.outer :=
  P.mem_outer.2 ⟨Sum.inr a, rfl⟩

theorem disjoint_outer_free : Disjoint P.outer P.free := by
  rw [free_eq_compl]
  exact disjoint_compl_right

theorem not_mem_free_of_mem_outer {i : Fin n} (h : i ∈ P.outer) : i ∉ P.free :=
  Finset.disjoint_left.1 P.disjoint_outer_free h

theorem mem_outer_of_not_mem_free {i : Fin n} (h : i ∉ P.free) : i ∈ P.outer := by
  rw [free_eq_compl, Finset.mem_compl, not_not] at h
  exact h

theorem u_not_mem_free (a : Fin k) : P.u a ∉ P.free :=
  P.not_mem_free_of_mem_outer (P.u_mem_outer a)

theorem w_not_mem_free (a : Fin k) : P.w a ∉ P.free :=
  P.not_mem_free_of_mem_outer (P.w_mem_outer a)

@[expose] noncomputable def outerEquiv : Fin k ⊕ Fin k ≃ P.outer :=
  (Equiv.ofInjective P.supp P.supp_injective).trans
    (Equiv.subtypeEquivRight fun i => by rw [Set.mem_range, mem_outer])

theorem coe_outerEquiv (s : Fin k ⊕ Fin k) : (P.outerEquiv s : Fin n) = P.supp s :=
  rfl

theorem outerEquiv_symm_supp (s : Fin k ⊕ Fin k) (h : P.supp s ∈ P.outer) :
    P.outerEquiv.symm ⟨P.supp s, h⟩ = s := by
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext rfl

theorem one_apply_of_injective {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {e : ι → κ}
    (he : Function.Injective e) (x y : ι) :
    (1 : Matrix κ κ K) (e x) (e y) = (1 : Matrix ι ι K) x y :=
  congrFun (congrFun (submatrix_one e he) x) y

theorem coe_reindexSpecialLinear_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (A : SpecialLinearGroup ι K) (x y : κ) :
    (reindexSpecialLinear e A : Matrix κ κ K) x y = (A : Matrix ι ι K) (e.symm x) (e.symm y) :=
  rfl

variable (K) in
@[expose] def diagSL : SpecialLinearGroup (Fin k) K →* SpecialLinearGroup (Fin k ⊕ Fin k) K where
  toFun a := ⟨fromBlocks (a : Matrix (Fin k) (Fin k) K) 0 0 a, by
    rw [det_fromBlocks_zero₂₁, a.2, mul_one]⟩
  map_one' := by
    apply Subtype.ext
    show fromBlocks ((1 : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) 0 0
      ((1 : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, fromBlocks_one]
  map_mul' a b := by
    apply Subtype.ext
    show fromBlocks ((a * b : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) 0 0
      ((a * b : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) =
      fromBlocks (a : Matrix (Fin k) (Fin k) K) 0 0 a *
        fromBlocks (b : Matrix (Fin k) (Fin k) K) 0 0 b
    rw [fromBlocks_multiply, Matrix.SpecialLinearGroup.coe_mul]
    simp

theorem coe_diagSL_apply (a : SpecialLinearGroup (Fin k) K) (s t : Fin k ⊕ Fin k) :
    (diagSL K a : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) K) s t =
      fromBlocks (a : Matrix (Fin k) (Fin k) K) 0 0 a s t :=
  rfl

variable (K) in
@[expose] noncomputable def leviOneHom :
    SpecialLinearGroup (Fin k) K →* SpecialLinearGroup (Fin n) K :=
  (blockEmbed P.outer).comp ((reindexSpecialLinear P.outerEquiv).toMonoidHom.comp (diagSL K))

theorem leviOneHom_apply_supp (a : SpecialLinearGroup (Fin k) K) (s t : Fin k ⊕ Fin k) :
    (P.leviOneHom K a : Matrix (Fin n) (Fin n) K) (P.supp s) (P.supp t) =
      fromBlocks (a : Matrix (Fin k) (Fin k) K) 0 0 a s t := by
  rw [leviOneHom, MonoidHom.comp_apply, MonoidHom.comp_apply, coe_blockEmbed, blockMatrix_apply,
    dite_eq_left ⟨P.mem_outer.2 ⟨s, rfl⟩, P.mem_outer.2 ⟨t, rfl⟩⟩, MulEquiv.coe_toMonoidHom,
    coe_reindexSpecialLinear_apply, P.outerEquiv_symm_supp, P.outerEquiv_symm_supp,
    coe_diagSL_apply]

theorem leviOneHom_apply_u_u (a : SpecialLinearGroup (Fin k) K) (x y : Fin k) :
    (P.leviOneHom K a : Matrix (Fin n) (Fin n) K) (P.u x) (P.u y) = a x y :=
  P.leviOneHom_apply_supp a (Sum.inl x) (Sum.inl y)

theorem leviOneHom_apply_w_w (a : SpecialLinearGroup (Fin k) K) (x y : Fin k) :
    (P.leviOneHom K a : Matrix (Fin n) (Fin n) K) (P.w x) (P.w y) = a x y :=
  P.leviOneHom_apply_supp a (Sum.inr x) (Sum.inr y)

theorem leviOneHom_apply_u_w (a : SpecialLinearGroup (Fin k) K) (x y : Fin k) :
    (P.leviOneHom K a : Matrix (Fin n) (Fin n) K) (P.u x) (P.w y) = 0 :=
  P.leviOneHom_apply_supp a (Sum.inl x) (Sum.inr y)

theorem leviOneHom_apply_w_u (a : SpecialLinearGroup (Fin k) K) (x y : Fin k) :
    (P.leviOneHom K a : Matrix (Fin n) (Fin n) K) (P.w x) (P.u y) = 0 :=
  P.leviOneHom_apply_supp a (Sum.inr x) (Sum.inl y)

theorem leviOneHom_apply_of_not_mem_outer (a : SpecialLinearGroup (Fin k) K) {i j : Fin n}
    (h : i ∉ P.outer ∨ j ∉ P.outer) :
    (P.leviOneHom K a : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j := by
  rw [leviOneHom, MonoidHom.comp_apply, coe_blockEmbed, blockMatrix_apply, dite_eq_right]
  rintro ⟨hi, hj⟩
  rcases h with h | h
  · exact h hi
  · exact h hj

theorem leviOneHom_mem_blockSpecialLinear (a : SpecialLinearGroup (Fin k) K) :
    P.leviOneHom K a ∈ blockSpecialLinear P.outer := by
  rw [← range_blockEmbed]
  exact ⟨_, rfl⟩

theorem leviOneHom_injective : Function.Injective (P.leviOneHom K) := by
  intro a b h
  ext x y
  rw [← P.leviOneHom_apply_u_u a, ← P.leviOneHom_apply_u_u b, h]

variable (K) in
@[expose] noncomputable def leviOne : Subgroup (SpecialLinearGroup (Fin n) K) :=
  (P.leviOneHom K).range

theorem leviOne_le_blockSpecialLinear : P.leviOne K ≤ blockSpecialLinear P.outer := by
  rintro _ ⟨a, rfl⟩
  exact P.leviOneHom_mem_blockSpecialLinear a

theorem blockEmbed_free_mem (d : SpecialLinearGroup P.free K) :
    blockEmbed P.free d ∈ blockSpecialLinear P.free := by
  rw [← range_blockEmbed]
  exact ⟨d, rfl⟩

theorem commute_leviOne_free {x y : SpecialLinearGroup (Fin n) K} (hx : x ∈ P.leviOne K)
    (hy : y ∈ blockSpecialLinear P.free) : Commute x y :=
  commute_blockSpecialLinear_of_disjoint P.disjoint_outer_free
    (P.leviOne_le_blockSpecialLinear hx) hy

theorem leviOneHom_mem_blockDiag (a : SpecialLinearGroup (Fin k) K) :
    P.leviOneHom K a ∈ P.blockDiag K := by
  intro i j hij
  by_cases h : i ∈ P.outer ∧ j ∈ P.outer
  · obtain ⟨s, rfl⟩ := P.mem_outer.1 h.1
    obtain ⟨t, rfl⟩ := P.mem_outer.1 h.2
    rw [leviOneHom_apply_supp]
    rcases s with x | x <;> rcases t with y | y
    · exact absurd (by simp [supp, level_u]) hij
    · rfl
    · rfl
    · exact absurd (by simp [supp, level_w]) hij
  · rw [P.leviOneHom_apply_of_not_mem_outer a (not_and_or.1 h), one_apply_ne]
    rintro rfl
    exact hij rfl

theorem blockSpecialLinear_free_le_blockDiag :
    blockSpecialLinear (K := K) P.free ≤ P.blockDiag K := by
  intro B hB i j hij
  have : i ∉ P.free ∨ j ∉ P.free := by
    by_contra h
    push Not at h
    exact hij ((P.mem_free.1 h.1).trans (P.mem_free.1 h.2).symm)
  rw [hB i j this, one_apply_ne]
  rintro rfl
  exact hij rfl

theorem leviOne_le_blockDiag : P.leviOne K ≤ P.blockDiag K := by
  rintro _ ⟨a, rfl⟩
  exact P.leviOneHom_mem_blockDiag a

theorem leviOne_le_centralizer : P.leviOne K ≤ Subgroup.centralizer {P.mat K} := by
  rintro _ ⟨a, rfl⟩
  rw [mem_centralizer_mat_iff]
  refine ⟨P.blockDiag_le_parabolic (P.leviOneHom_mem_blockDiag a), fun x y => ?_⟩
  rw [leviOneHom_apply_w_w, leviOneHom_apply_u_u]

theorem blockSpecialLinear_free_le_centralizer :
    blockSpecialLinear (K := K) P.free ≤ Subgroup.centralizer {P.mat K} := by
  intro B hB
  rw [mem_centralizer_mat_iff]
  refine ⟨P.blockDiag_le_parabolic (P.blockSpecialLinear_free_le_blockDiag hB), fun x y => ?_⟩
  rw [hB _ _ (Or.inl (P.w_not_mem_free x)), hB _ _ (Or.inl (P.u_not_mem_free x))]
  simp only [one_apply, P.w_injective.eq_iff, P.u_injective.eq_iff]

theorem submatrix_u_leviOneHom (a : SpecialLinearGroup (Fin k) K) :
    (P.leviOneHom K a : Matrix (Fin n) (Fin n) K).submatrix P.u P.u = a := by
  ext x y
  exact P.leviOneHom_apply_u_u a x y

theorem submatrix_w_leviOneHom (a : SpecialLinearGroup (Fin k) K) :
    (P.leviOneHom K a : Matrix (Fin n) (Fin n) K).submatrix P.w P.w = a := by
  ext x y
  exact P.leviOneHom_apply_w_w a x y

theorem submatrix_free_leviOneHom (a : SpecialLinearGroup (Fin k) K) :
    (P.leviOneHom K a : Matrix (Fin n) (Fin n) K).submatrix (Subtype.val : P.free → Fin n)
      (Subtype.val : P.free → Fin n) = 1 := by
  ext x y
  rw [submatrix_apply, P.leviOneHom_apply_of_not_mem_outer a
    (Or.inl (fun h => P.not_mem_free_of_mem_outer h x.2)),
    one_apply_of_injective Subtype.val_injective]

theorem submatrix_u_blockEmbed_free (d : SpecialLinearGroup P.free K) :
    (blockEmbed P.free d : Matrix (Fin n) (Fin n) K).submatrix P.u P.u = 1 := by
  ext x y
  rw [submatrix_apply, (P.blockEmbed_free_mem d) _ _ (Or.inl (P.u_not_mem_free x)),
    one_apply_of_injective P.u_injective]

theorem submatrix_w_blockEmbed_free (d : SpecialLinearGroup P.free K) :
    (blockEmbed P.free d : Matrix (Fin n) (Fin n) K).submatrix P.w P.w = 1 := by
  ext x y
  rw [submatrix_apply, (P.blockEmbed_free_mem d) _ _ (Or.inl (P.w_not_mem_free x)),
    one_apply_of_injective P.w_injective]

theorem submatrix_free_blockEmbed_free (d : SpecialLinearGroup P.free K) :
    (blockEmbed P.free d : Matrix (Fin n) (Fin n) K).submatrix (Subtype.val : P.free → Fin n)
      (Subtype.val : P.free → Fin n) = d := by
  ext x y
  rw [submatrix_apply, coe_blockEmbed, blockMatrix_apply, dite_eq_left ⟨x.2, y.2⟩]

variable (K) in
@[expose] noncomputable def detU : P.parabolic K →* K where
  toFun B :=
    ((B : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix P.u P.u |>.det
  map_one' := by
    show (((1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix P.u P.u).det = 1
    rw [Matrix.SpecialLinearGroup.coe_one, submatrix_one _ P.u_injective, det_one]
  map_mul' B B' := by
    show ((((B : SpecialLinearGroup (Fin n) K) * B' : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K).submatrix P.u P.u).det = _
    rw [Matrix.SpecialLinearGroup.coe_mul,
      P.submatrix_mul_u (P.mem_parabolic.1 B.2) (P.mem_parabolic.1 B'.2), det_mul]

variable (K) in
@[expose] noncomputable def detFree : P.parabolic K →* K where
  toFun B := ((B : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix
    (Subtype.val : P.free → Fin n) (Subtype.val : P.free → Fin n) |>.det
  map_one' := by
    show (((1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix
      (Subtype.val : P.free → Fin n) (Subtype.val : P.free → Fin n)).det = 1
    rw [Matrix.SpecialLinearGroup.coe_one, submatrix_one _ Subtype.val_injective, det_one]
  map_mul' B B' := by
    show ((((B : SpecialLinearGroup (Fin n) K) * B' : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K).submatrix (Subtype.val : P.free → Fin n)
        (Subtype.val : P.free → Fin n)).det = _
    rw [Matrix.SpecialLinearGroup.coe_mul,
      P.submatrix_mul_free (P.mem_parabolic.1 B.2) (P.mem_parabolic.1 B'.2), det_mul]

theorem map_commutatorElement_eq_one {G M : Type*} [Group G] [CommMonoid M] (f : G →* M)
    (x y : G) : f ⁅x, y⁆ = 1 := by
  have h1 : f.toHomUnits ⁅x, y⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  have h2 := congrArg Units.val h1
  rwa [MonoidHom.coe_toHomUnits, Units.val_one] at h2

variable (K) in
@[expose] noncomputable def core : Subgroup (SpecialLinearGroup (Fin n) K) :=
  P.radical K ⊔ (P.leviOne K ⊔ blockSpecialLinear P.free)

theorem core_le_centralizer : P.core K ≤ Subgroup.centralizer {P.mat K} :=
  sup_le P.radical_le_centralizer (sup_le P.leviOne_le_centralizer
    P.blockSpecialLinear_free_le_centralizer)

theorem mem_core_of_det {B : SpecialLinearGroup (Fin n) K}
    (hB : B ∈ Subgroup.centralizer {P.mat K})
    (h0 : ((B : Matrix (Fin n) (Fin n) K).submatrix P.u P.u).det = 1)
    (h1 : ((B : Matrix (Fin n) (Fin n) K).submatrix (Subtype.val : P.free → Fin n)
      (Subtype.val : P.free → Fin n)).det = 1) : B ∈ P.core K := by
  obtain ⟨hBT, hBuw⟩ := P.mem_centralizer_mat_iff.1 hB
  set a : SpecialLinearGroup (Fin k) K := ⟨_, h0⟩
  set d : SpecialLinearGroup P.free K := ⟨_, h1⟩
  set m := P.leviOneHom K a * blockEmbed P.free d with hm
  have hmT : (m : Matrix (Fin n) (Fin n) K).BlockTriangular P.level :=
    P.blockDiag_le_parabolic (mul_mem (P.leviOneHom_mem_blockDiag a)
      (P.blockSpecialLinear_free_le_blockDiag (P.blockEmbed_free_mem d)))
  have hLT := P.mem_parabolic.1 (P.blockDiag_le_parabolic (P.leviOneHom_mem_blockDiag a))
  have hDT := P.mem_parabolic.1 (P.blockDiag_le_parabolic
    (P.blockSpecialLinear_free_le_blockDiag (P.blockEmbed_free_mem d)))
  have hmu : (m : Matrix (Fin n) (Fin n) K).submatrix P.u P.u =
      (B : Matrix _ _ K).submatrix P.u P.u := by
    rw [hm, Matrix.SpecialLinearGroup.coe_mul, P.submatrix_mul_u hLT hDT, submatrix_u_leviOneHom,
      submatrix_u_blockEmbed_free, Matrix.mul_one]
  have hmw : (m : Matrix (Fin n) (Fin n) K).submatrix P.w P.w =
      (B : Matrix _ _ K).submatrix P.w P.w := by
    rw [hm, Matrix.SpecialLinearGroup.coe_mul, P.submatrix_mul_w hLT hDT, submatrix_w_leviOneHom,
      submatrix_w_blockEmbed_free, Matrix.mul_one]
    ext x y
    exact (hBuw x y).symm
  have hmf : (m : Matrix (Fin n) (Fin n) K).submatrix (Subtype.val : P.free → Fin n)
      (Subtype.val : P.free → Fin n) = (B : Matrix _ _ K).submatrix (Subtype.val : P.free → Fin n)
      (Subtype.val : P.free → Fin n) := by
    rw [hm, Matrix.SpecialLinearGroup.coe_mul, P.submatrix_mul_free hLT hDT,
      submatrix_free_leviOneHom, submatrix_free_blockEmbed_free, Matrix.one_mul]
  set r := B * m⁻¹ with hr
  have hrT : (r : Matrix (Fin n) (Fin n) K).BlockTriangular P.level :=
    P.mem_parabolic.1 (mul_mem (P.centralizer_le_parabolic hB) (inv_mem (P.mem_parabolic.2 hmT)))
  have hrm : r * m = B := by rw [hr, inv_mul_cancel_right]
  have key : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → Fin n), Function.Injective e →
      ∀ c : ℕ, (∀ i, P.level i = c ↔ ∃ x, e x = i) →
      (m : Matrix (Fin n) (Fin n) K).submatrix e e = (B : Matrix _ _ K).submatrix e e →
      IsUnit ((B : Matrix (Fin n) (Fin n) K).submatrix e e).det →
      (r : Matrix (Fin n) (Fin n) K).submatrix e e = 1 := by
    intro ι _ _ e he c hec hme hdet
    have h := P.submatrix_mul_of_level hrT hmT e he c hec
    rw [← Matrix.SpecialLinearGroup.coe_mul, hrm, hme] at h
    have h' := congrArg (· * ((B : Matrix (Fin n) (Fin n) K).submatrix e e)⁻¹) h
    rwa [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
      Matrix.mul_one, eq_comm] at h'
  have hru := key P.u P.u_injective 0 P.level_eq_zero_iff' hmu (by rw [h0]; exact isUnit_one)
  have hrw := key P.w P.w_injective 2 P.level_eq_two_iff' hmw (by
    have : (B : Matrix (Fin n) (Fin n) K).submatrix P.w P.w =
        (B : Matrix (Fin n) (Fin n) K).submatrix P.u P.u := by
      ext x y
      exact hBuw x y
    rw [this, h0]
    exact isUnit_one)
  have hrf := key Subtype.val Subtype.val_injective 1 P.level_eq_one_iff_free hmf
    (by rw [h1]; exact isUnit_one)
  have hrR : r ∈ P.radical K := by
    intro i j hij
    rcases lt_or_eq_of_le hij with h | h
    · rw [hrT h, one_apply_ne]
      rintro rfl
      exact lt_irrefl _ h
    · have hi2 := P.level_le_two i
      rcases (by omega : P.level i = 0 ∨ P.level i = 1 ∨ P.level i = 2) with h0' | h1' | h2'
      · obtain ⟨x, rfl⟩ := P.level_eq_zero_iff.1 h0'
        obtain ⟨y, rfl⟩ := P.level_eq_zero_iff.1 (h.trans h0')
        have := congrFun (congrFun hru x) y
        rw [submatrix_apply] at this
        rw [this]
        exact (one_apply_of_injective P.u_injective x y).symm
      · obtain ⟨x, rfl⟩ := (P.level_eq_one_iff_free i).1 h1'
        obtain ⟨y, rfl⟩ := (P.level_eq_one_iff_free j).1 (h.trans h1')
        have := congrFun (congrFun hrf x) y
        rw [submatrix_apply] at this
        rw [this]
        exact (one_apply_of_injective Subtype.val_injective x y).symm
      · obtain ⟨x, rfl⟩ := P.level_eq_two_iff.1 h2'
        obtain ⟨y, rfl⟩ := P.level_eq_two_iff.1 (h.trans h2')
        have := congrFun (congrFun hrw x) y
        rw [submatrix_apply] at this
        rw [this]
        exact (one_apply_of_injective P.w_injective x y).symm
  rw [← hrm]
  exact mul_mem (Subgroup.mem_sup_left hrR) (Subgroup.mem_sup_right (mul_mem
    (Subgroup.mem_sup_left ⟨a, rfl⟩)
    (Subgroup.mem_sup_right (P.blockEmbed_free_mem d))))

theorem commutator_centralizer_le_core :
    ⁅Subgroup.centralizer {P.mat K}, Subgroup.centralizer {P.mat K}⁆ ≤ P.core K := by
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  set p₁ : P.parabolic K := ⟨g₁, P.centralizer_le_parabolic h₁⟩
  set p₂ : P.parabolic K := ⟨g₂, P.centralizer_le_parabolic h₂⟩
  have hc : ((⁅p₁, p₂⁆ : P.parabolic K) : SpecialLinearGroup (Fin n) K) = ⁅g₁, g₂⁆ := rfl
  have hmem : ⁅g₁, g₂⁆ ∈ Subgroup.centralizer {P.mat K} := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  refine P.mem_core_of_det hmem ?_ ?_
  · rw [← hc]
    exact map_commutatorElement_eq_one (P.detU K) p₁ p₂
  · rw [← hc]
    exact map_commutatorElement_eq_one (P.detFree K) p₁ p₂

theorem radical_le_core : P.radical K ≤ P.core K :=
  le_sup_left

theorem leviOne_le_core : P.leviOne K ≤ P.core K :=
  le_sup_left.trans le_sup_right

theorem free_le_core : blockSpecialLinear (K := K) P.free ≤ P.core K :=
  le_sup_right.trans le_sup_right

theorem exists_free_ne {i j : Fin n} (hij : P.level i < P.level j) (hJ : 2 ≤ P.free.card) :
    ∃ l ∈ P.free, l ≠ i ∧ l ≠ j := by
  obtain ⟨l₁, hl₁, l₂, hl₂, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < P.free.card)
  by_cases hi : i ∈ P.free
  · have hj : j ∉ P.free := fun hj => by
      rw [P.mem_free.1 hi, P.mem_free.1 hj] at hij
      exact lt_irrefl _ hij
    by_cases h1 : l₁ = i
    · exact ⟨l₂, hl₂, fun h => hne (h1.trans h.symm), fun h => hj (h ▸ hl₂)⟩
    · exact ⟨l₁, hl₁, h1, fun h => hj (h ▸ hl₁)⟩
  · by_cases h1 : l₁ = j
    · exact ⟨l₂, hl₂, fun h => hi (h ▸ hl₂), fun h => hne (h1.trans h.symm)⟩
    · exact ⟨l₁, hl₁, fun h => hi (h ▸ hl₁), h1⟩

theorem transvection_mem_core {i j : Fin n} (hij : i ≠ j)
    (h : P.level i < P.level j ∨ (i ∈ P.free ∧ j ∈ P.free)) (c : K) :
    SpecialLinearGroup.transvection hij c ∈ P.core K := by
  rcases h with h | ⟨hi, hj⟩
  · exact P.radical_le_core (P.transvection_mem_radical hij h c)
  · exact P.free_le_core (transvection_mem_blockSpecialLinear hij hi hj c)

theorem radicalRootSet_subset_commutator (hJ : 2 ≤ P.free.card) :
    ∀ g ∈ P.radicalRootSet (K := K), g ∈ ⁅P.core K, P.core K⁆ := by
  rintro _ ⟨i, j, hij, c, h, rfl⟩
  obtain ⟨l, hl, hli, hlj⟩ := P.exists_free_ne h hJ
  have hl1 := P.mem_free.1 hl
  have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection hli.symm hlj hij c (1 : K)
  rw [mul_one] at hcomm
  rw [← hcomm]
  have hj2 := P.level_le_two j
  apply Subgroup.commutator_mem_commutator
  · apply P.transvection_mem_core
    by_cases hi0 : P.level i = 0
    · exact Or.inl (by omega)
    · exact Or.inr ⟨P.mem_free.2 (by omega), hl⟩
  · apply P.transvection_mem_core
    by_cases hj1 : P.level j = 1
    · exact Or.inr ⟨hl, P.mem_free.2 hj1⟩
    · exact Or.inl (by omega)

theorem radical_le_commutator_core (hJ : 2 ≤ P.free.card) :
    P.radical K ≤ ⁅P.core K, P.core K⁆ :=
  P.radical_le_closure.trans ((Subgroup.closure_le _).2 fun g hg =>
    P.radicalRootSet_subset_commutator hJ g hg)

theorem commutator_self_le' {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem commutator_core [Group.IsPerfect (SpecialLinearGroup (Fin k) K)]
    [Group.IsPerfect (SpecialLinearGroup P.free K)] (hJ : 2 ≤ P.free.card) :
    ⁅P.core K, P.core K⁆ = P.core K := by
  refine le_antisymm (commutator_self_le' _) ?_
  refine sup_le (P.radical_le_commutator_core hJ) (sup_le ?_ ?_)
  · have : Group.IsPerfect (P.leviOne K) := Group.IsPerfect.range _
    calc P.leviOne K = ⁅P.leviOne K, P.leviOne K⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅P.core K, P.core K⁆ := Subgroup.commutator_mono P.leviOne_le_core P.leviOne_le_core
  · have : Group.IsPerfect (blockSpecialLinear (K := K) P.free) := by
      rw [← range_blockEmbed]
      exact Group.IsPerfect.range _
    calc blockSpecialLinear (K := K) P.free =
          ⁅blockSpecialLinear (K := K) P.free, blockSpecialLinear (K := K) P.free⁆ :=
          Subgroup.commutator_eq_self.symm
      _ ≤ ⁅P.core K, P.core K⁆ := Subgroup.commutator_mono P.free_le_core P.free_le_core

theorem perfectCore_eq_of_perfect_of_commutator_le {G : Type*} [Group G] {C H : Subgroup G}
    (hHC : H ≤ C) (hH : ⁅H, H⁆ = H) (hC : ⁅C, C⁆ ≤ H) : perfectCore C = H := by
  refine le_antisymm ?_ (le_perfectCore_of_perfect hHC hH)
  calc perfectCore C ≤ derivedSeriesOf C 1 := CFSG.Quasithin.perfectCore_le_derivedSeriesOf C 1
    _ = ⁅C, C⁆ := by rw [derivedSeriesOf_succ, derivedSeriesOf_zero]
    _ ≤ H := hC

theorem perfectCore_centralizer_mat [Group.IsPerfect (SpecialLinearGroup (Fin k) K)]
    [Group.IsPerfect (SpecialLinearGroup P.free K)] (hJ : 2 ≤ P.free.card) :
    perfectCore (Subgroup.centralizer {P.mat K}) = P.core K :=
  perfectCore_eq_of_perfect_of_commutator_le P.core_le_centralizer (P.commutator_core hJ)
    P.commutator_centralizer_le_core

end InvPlacement

end CFSG.SeitzReduction.LinearPilot
