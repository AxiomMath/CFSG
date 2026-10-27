module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3FormModel
import CFSG.ClassicalGroups.Symplectic.Model
import CFSG.LieType.Universal.Symplectic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3.Sp

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremA.S267.P3
open CFSG.LocalAnalysis.GLTheoremA.S267.P3.Lin CFSG.LocalAnalysis.GLTheoremA.S267.P3.Form

variable {F : Type} [Field F]

@[expose] def spOn {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι F) :
    Subgroup (SpecialLinearGroup ι F) where
  carrier := {g : SpecialLinearGroup ι F | (g : Matrix ι ι F)ᵀ * J * (g : Matrix ι ι F) = J}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_mul] at hg hh ⊢
    calc ((g : Matrix ι ι F) * (h : Matrix ι ι F))ᵀ * J * ((g : Matrix ι ι F) * (h : Matrix ι ι F))
        = (h : Matrix ι ι F)ᵀ * ((g : Matrix ι ι F)ᵀ * J * (g : Matrix ι ι F)) *
            (h : Matrix ι ι F) := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = J := by rw [hg, hh]
  one_mem' := by
    simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one,
      Matrix.one_mul, Matrix.mul_one]
  inv_mem' {g} hg := by
    simp only [Set.mem_setOf_eq] at hg ⊢
    have hgi : (g : Matrix ι ι F) * ((g⁻¹ : SpecialLinearGroup ι F) : Matrix ι ι F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc ((g⁻¹ : SpecialLinearGroup ι F) : Matrix ι ι F)ᵀ * J *
          ((g⁻¹ : SpecialLinearGroup ι F) : Matrix ι ι F)
        = ((g⁻¹ : SpecialLinearGroup ι F) : Matrix ι ι F)ᵀ *
            ((g : Matrix ι ι F)ᵀ * J * (g : Matrix ι ι F)) *
              ((g⁻¹ : SpecialLinearGroup ι F) : Matrix ι ι F) := by rw [hg]
      _ = ((g : Matrix ι ι F) * ((g⁻¹ : SpecialLinearGroup ι F) : Matrix ι ι F))ᵀ * J *
            ((g : Matrix ι ι F) * ((g⁻¹ : SpecialLinearGroup ι F) : Matrix ι ι F)) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = J := by rw [hgi, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem mem_spOn {ι : Type} [Fintype ι] [DecidableEq ι] {J : Matrix ι ι F}
    {g : SpecialLinearGroup ι F} : g ∈ spOn J ↔ (g : Matrix ι ι F)ᵀ * J * (g : Matrix ι ι F) = J :=
  Iff.rfl

theorem blk_mem_spOn_iff {ι : Type} [Fintype ι] [DecidableEq ι] {J₂ : Matrix (Fin 2) (Fin 2) F}
    {J : Matrix ι ι F} (P : SpecialLinearGroup (Fin 2) F) (Y : SpecialLinearGroup ι F) :
    blk ι (P, Y) ∈ spOn (fromBlocks J₂ 0 0 J) ↔ P ∈ spOn J₂ ∧ Y ∈ spOn J := by
  rw [mem_spOn, mem_spOn, mem_spOn, coe_blk, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  constructor
  · intro h
    obtain ⟨h1, -, -, h4⟩ := Matrix.fromBlocks_inj.1 h
    exact ⟨h1, h4⟩
  · rintro ⟨h1, h4⟩
    rw [h1, h4]

@[expose] def ω₂ : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]

theorem mem_spOn_ω₂ (P : SpecialLinearGroup (Fin 2) F) : P ∈ spOn (ω₂ (F := F)) := by
  rw [mem_spOn]
  have hdet := P.2
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ω₂, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination hdet | linear_combination -hdet

theorem c3_rel : ((c3 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
    (c3 : SpecialLinearGroup (Fin 2) F) + (c3 : SpecialLinearGroup (Fin 2) F) + 1 = 0 := by
  rw [coe_c3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c3Mat, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

abbrev stdJ (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := fromBlocks 0 1 (-1) 0

@[expose] def stepFun {ι : Type} {n : ℕ} (e : ι ≃ Fin n ⊕ Fin n) :
    Fin 2 ⊕ ι → Fin (n + 1) ⊕ Fin (n + 1)
  | .inl i => if i = 0 then .inl 0 else .inr 0
  | .inr x => Sum.map Fin.succ Fin.succ (e x)

@[expose] def stepInv {ι : Type} {n : ℕ} (e : ι ≃ Fin n ⊕ Fin n) :
    Fin (n + 1) ⊕ Fin (n + 1) → Fin 2 ⊕ ι
  | .inl a => Fin.cases (.inl 0) (fun b => .inr (e.symm (.inl b))) a
  | .inr a => Fin.cases (.inl 1) (fun b => .inr (e.symm (.inr b))) a

@[expose] def stepEquiv {ι : Type} {n : ℕ} (e : ι ≃ Fin n ⊕ Fin n) :
    Fin 2 ⊕ ι ≃ Fin (n + 1) ⊕ Fin (n + 1) where
  toFun := stepFun e
  invFun := stepInv e
  left_inv x := by
    rcases x with i | x
    · fin_cases i <;> simp [stepFun, stepInv]
    · rcases h : e x with a | a <;> simp [stepFun, stepInv, h, Equiv.symm_apply_eq]
  right_inv y := by
    rcases y with a | a <;> refine Fin.cases ?_ (fun b => ?_) a <;> simp [stepFun, stepInv]

theorem stepEquiv_symm_apply {ι : Type} {n : ℕ} (e : ι ≃ Fin n ⊕ Fin n)
    (y : Fin (n + 1) ⊕ Fin (n + 1)) : (stepEquiv e).symm y = stepInv e y := rfl

theorem reindex_step {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n ⊕ Fin n)
    {J : Matrix ι ι F} (hJ : reindex e e J = stdJ n) :
    reindex (stepEquiv e) (stepEquiv e) (fromBlocks ω₂ 0 0 J) = stdJ (n + 1) := by
  have hJ' : ∀ x y, J (e.symm x) (e.symm y) = stdJ n x y := fun x y => by
    rw [← hJ]
    rfl
  have hz : ∀ k : Fin n, (0 : Fin (n + 1)) ≠ k.succ := fun k => (Fin.succ_ne_zero k).symm
  ext i j
  rw [reindex_apply, submatrix_apply, stepEquiv_symm_apply, stepEquiv_symm_apply]
  rcases i with a | a <;> rcases j with b | b <;> refine Fin.cases ?_ (fun a' => ?_) a <;>
    refine Fin.cases ?_ (fun b' => ?_) b <;>
    simp only [stepInv, Fin.cases_zero, Fin.cases_succ, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, hJ', Matrix.zero_apply, Matrix.one_apply,
      Matrix.neg_apply,
      Fin.succ_inj, hz, Fin.succ_ne_zero, if_false, if_true] <;>
    simp [ω₂]

@[expose] noncomputable def toGLRe {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) : SpecialLinearGroup ι F →* GL κ F :=
  Matrix.SpecialLinearGroup.toGL.comp (slReindex (F := F) e).toMonoidHom

theorem coe_toGLRe {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (g : SpecialLinearGroup ι F) :
    ((toGLRe e g : GL κ F) : Matrix κ κ F) = reindex e e (g : Matrix ι ι F) := rfl

theorem toGLRe_injective {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) : Function.Injective (toGLRe (F := F) e) := fun g h hgh =>
  Subtype.ext ((reindex e e).injective (by rw [← coe_toGLRe, ← coe_toGLRe, hgh]))

theorem reindex_isometry {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A J : Matrix ι ι F) :
    (reindex e e A)ᵀ * reindex e e J * reindex e e A = reindex e e (Aᵀ * J * A) := by
  simp only [reindex_apply, transpose_submatrix, submatrix_mul_equiv]

theorem det_eq_one_of_mem {n : ℕ} {A : GL (Fin n ⊕ Fin n) F} (hA : A ∈ StatedSp n F) :
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).det = 1 := by
  have hsp := TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.1
    ((Subgroup.ext_iff.1 CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic _).1 hA)
  exact SymplecticGroup.det_eq_one hsp

theorem map_spOn {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n ⊕ Fin n)
    {J : Matrix ι ι F} (hJ : reindex e e J = stdJ n) :
    (spOn J).map (toGLRe e) = StatedSp n F := by
  have hJ' : J = reindex e.symm e.symm (stdJ n) := by
    rw [← hJ, ← reindex_symm, Equiv.symm_apply_apply]
  ext B
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [CFSG.Open.StatedAPI.mem_statedSp_iff, coe_toGLRe]
    change _ * stdJ n * _ = stdJ n
    rw [← hJ, reindex_isometry, mem_spOn.1 hg]
  · intro hB
    have hu := CFSG.Open.StatedAPI.mem_statedSp_iff.1 hB
    set g : SpecialLinearGroup ι F := ⟨reindex e.symm e.symm (B : Matrix _ _ F), by
      rw [det_reindex_self]
      exact det_eq_one_of_mem hB⟩
    refine ⟨g, ?_, Units.ext ?_⟩
    · rw [SetLike.mem_coe, mem_spOn]
      change (reindex e.symm e.symm (B : Matrix _ _ F))ᵀ * J *
        reindex e.symm e.symm (B : Matrix _ _ F) = J
      rw [hJ', reindex_isometry, hu]
    · rw [coe_toGLRe]
      change reindex e e (reindex e.symm e.symm (B : Matrix _ _ F)) = _
      simp

@[expose] noncomputable def spOnEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (e : ι ≃ Fin n ⊕ Fin n) {J : Matrix ι ι F} (hJ : reindex e e J = stdJ n) :
    ↥(spOn J) ≃* ↥(StatedSp n F) :=
  ((spOn J).equivMapOfInjective _ (toGLRe_injective e)).trans
    (MulEquiv.subgroupCongr (map_spOn e hJ))

theorem coe_spOnEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n ⊕ Fin n)
    {J : Matrix ι ι F} (hJ : reindex e e J = stdJ n) (g : ↥(spOn J)) :
    (((spOnEquiv e hJ g : ↥(StatedSp n F)) : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      reindex e e ((g : SpecialLinearGroup ι F) : Matrix ι ι F) := rfl

theorem map_center_of_reindex {ι κ : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) {G : Subgroup (SpecialLinearGroup ι F)} {H : Subgroup (GL κ F)}
    (E : ↥G ≃* ↥H)
    (hE : ∀ x : ↥G, (((E x : ↥H) : GL κ F) : Matrix κ κ F) =
      reindex e e ((x : SpecialLinearGroup ι F) : Matrix ι ι F)) :
    ((Subgroup.center (SpecialLinearGroup ι F)).subgroupOf G).map (E : ↥G →* ↥H) =
      (StatedScalars κ F).subgroupOf H := by
  have key : ∀ x : ↥G, E x ∈ (StatedScalars κ F).subgroupOf H ↔
      x ∈ (Subgroup.center (SpecialLinearGroup ι F)).subgroupOf G := by
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range,
      Matrix.SpecialLinearGroup.mem_center_iff]
    constructor
    · rintro ⟨u, hu⟩
      have hu' : Matrix.scalar κ (u : F) =
          reindex e e ((x : SpecialLinearGroup ι F) : Matrix ι ι F) := by
        rw [← hE, ← hu]
        rfl
      have hx : ((x : SpecialLinearGroup ι F) : Matrix ι ι F) = Matrix.scalar ι (u : F) := by
        have h1 : ((x : SpecialLinearGroup ι F) : Matrix ι ι F) =
            (reindex e e).symm (Matrix.scalar κ (u : F)) := by
          rw [hu', Equiv.symm_apply_apply]
        rw [h1, reindex_symm]
        ext i j
        simp [Matrix.scalar_apply, Matrix.diagonal_apply]
      refine ⟨u, ?_, hx.symm⟩
      have hdet := (x : SpecialLinearGroup ι F).2
      rw [hx] at hdet
      simpa [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]
        using hdet
    · rintro ⟨r, hr, hrx⟩
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [zero_pow Fintype.card_ne_zero] at hr
        exact zero_ne_one hr
      refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
      rw [Matrix.GeneralLinearGroup.coe_scalar, hE, ← hrx]
      ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (key x).2 hx
  · intro hy
    refine ⟨E.symm y, (key _).1 (by rwa [MulEquiv.apply_symm_apply]), ?_⟩
    exact MulEquiv.apply_symm_apply E y

abbrev ν₀ : Type := Fin 0

@[expose] def Jl : Matrix (Lam ν₀) (Lam ν₀) F := fromBlocks ω₂ 0 0 0

@[expose] def Jk : Matrix (Kap ν₀) (Kap ν₀) F := fromBlocks ω₂ 0 0 Jl

@[expose] def Jt : Matrix (Lin.Top ν₀) (Lin.Top ν₀) F := fromBlocks ω₂ 0 0 Jk

@[expose] def e₀ : ν₀ ≃ Fin 0 ⊕ Fin 0 := Equiv.equivOfIsEmpty _ _

@[expose] def el : Lam ν₀ ≃ Fin 1 ⊕ Fin 1 := stepEquiv e₀

@[expose] def ek : Kap ν₀ ≃ Fin 2 ⊕ Fin 2 := stepEquiv el

@[expose] def et : Lin.Top ν₀ ≃ Fin 3 ⊕ Fin 3 := stepEquiv ek

theorem reindex_Jl : reindex el el (Jl (F := F)) = stdJ 1 :=
  reindex_step e₀ (by ext i; rcases i with i | i <;> exact i.elim0)

theorem reindex_Jk : reindex ek ek (Jk (F := F)) = stdJ 2 := reindex_step el reindex_Jl

theorem reindex_Jt : reindex et et (Jt (F := F)) = stdJ 3 := reindex_step ek reindex_Jk

@[expose] noncomputable def spData : FormData F ν₀ where
  G2 := spOn ω₂
  Gl := spOn Jl
  Gk := spOn Jk
  Gt := spOn Jt
  blk_top P hP Y hY := (blk_mem_spOn_iff P Y).2 ⟨hP, hY⟩
  blk_kap P hP R hR := (blk_mem_spOn_iff P R).2 ⟨hP, hR⟩
  blk_lam P hP := (blk_mem_spOn_iff P 1).2 ⟨hP, one_mem _⟩
  top_inv Y h := ((blk_mem_spOn_iff 1 Y).1 h).2
  kap_inv R h := ((blk_mem_spOn_iff 1 R).1 h).2
  c := c3
  c_mem := mem_spOn_ω₂ _
  c_rel := c3_rel
  w := w2
  w_mem := mem_spOn_ω₂ _
  c_mul_w := c3_mul_w2_ne
  negOne_mem := mem_spOn_ω₂ _

theorem isQuasisimple_spOn {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (hn : 1 ≤ n)
    (h4 : 4 ≤ Nat.card F) (e : ι ≃ Fin n ⊕ Fin n) {J : Matrix ι ι F}
    (hJ : reindex e e J = stdJ n) : CFSG.Open.IsQuasisimple ↥(spOn J) := by
  have h := CFSG.LieType.Universal.Symplectic.isQuasisimple n F hn (Or.inl (Or.inr h4))
  have h' : CFSG.Open.IsQuasisimple ↥(StatedSp n F) := ⟨Group.isPerfect_def.1 h.1, h.2.1⟩
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv (spOnEquiv e hJ) h'

theorem noThree_spData : ∀ z ∈ (spData (F := F)).Zt, z ^ 3 = 1 → z = 1 := by
  intro z hz hz3
  have hc := Subgroup.mem_subgroupOf.1 hz
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  have hu := mem_spOn.1 z.2
  have hzr : (((z : SpecialLinearGroup (Lin.Top ν₀) F)) : Matrix (Lin.Top ν₀) (Lin.Top ν₀) F) =
      Matrix.scalar (Lin.Top ν₀) r := hr.symm
  rw [hzr] at hu
  have hsq : r * r = 1 := by
    have := congrFun (congrFun hu (Sum.inl 0)) (Sum.inl 1)
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.mul_apply, Jt, ω₂] using this
  have hr3 : r ^ 3 = 1 := by
    have h1 : (((z : SpecialLinearGroup (Lin.Top ν₀) F)) : Matrix (Lin.Top ν₀) (Lin.Top ν₀) F) ^ 3 =
        1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, ← Subgroup.coe_pow, hz3]
      rfl
    rw [hzr, ← map_pow] at h1
    have := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 0)
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply] using this
  have hr1 : r = 1 := by
    have : r ^ 3 = r * r * r := by ring
    rw [hr3, hsq, one_mul] at this
    exact this.symm
  apply Subtype.ext
  apply Subtype.ext
  rw [hzr, hr1, map_one]
  rfl

@[expose] noncomputable def spProjEquiv : (spData (F := F)).XD ≃* StatedProj (StatedSp 3 F) :=
  QuotientGroup.congr _ _ (spOnEquiv et reindex_Jt)
    (map_center_of_reindex et (spOnEquiv et reindex_Jt) (coe_spOnEquiv et reindex_Jt))

end CFSG.LocalAnalysis.GLTheoremA.S267.P3.Sp

end
