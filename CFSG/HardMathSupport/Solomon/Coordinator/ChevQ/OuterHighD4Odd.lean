module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Three4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2RecStruct
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Split
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Main
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusCent
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.LieType.Steinberg.TwistedD4.Local
public import CFSG.HardMathSupport.Seitz.Proving.OrderThreeSLConj

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Odd

open Matrix CFSG.RankThree.PartTwo
open scoped MatrixGroups

section Conj

variable {F : Type} [Field F]

theorem gl_mul_inv (g : GL (Fin 3) F) :
    (g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem gl_inv_mul (g : GL (Fin 3) F) :
    ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

@[expose] def conjSL (g : GL (Fin 3) F) : SL(3, F) →* SL(3, F) where
  toFun h := ⟨(g : Matrix (Fin 3) (Fin 3) F) * (h : Matrix (Fin 3) (Fin 3) F) *
      ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), by
    rw [Matrix.det_mul, Matrix.det_mul, h.2, mul_one, ← Matrix.det_mul, gl_mul_inv,
      Matrix.det_one]⟩
  map_one' := by
    apply Subtype.ext
    change (g : Matrix (Fin 3) (Fin 3) F) * 1 *
      ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1
    rw [Matrix.mul_one, gl_mul_inv]
  map_mul' a b := by
    apply Subtype.ext
    change (g : Matrix (Fin 3) (Fin 3) F) * ((a : Matrix (Fin 3) (Fin 3) F) *
        (b : Matrix (Fin 3) (Fin 3) F)) * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((g : Matrix (Fin 3) (Fin 3) F) * (a : Matrix (Fin 3) (Fin 3) F) *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *
      ((g : Matrix (Fin 3) (Fin 3) F) * (b : Matrix (Fin 3) (Fin 3) F) *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    have h1 := gl_inv_mul g
    calc (g : Matrix (Fin 3) (Fin 3) F) * ((a : Matrix (Fin 3) (Fin 3) F) *
          (b : Matrix (Fin 3) (Fin 3) F)) * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (g : Matrix (Fin 3) (Fin 3) F) * (a : Matrix (Fin 3) (Fin 3) F) *
          (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)) *
          (b : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
          rw [h1, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem coe_conjSL (g : GL (Fin 3) F) (h : SL(3, F)) :
    ((conjSL g h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * (h : Matrix (Fin 3) (Fin 3) F) *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
  rfl

theorem conjSL_one (h : SL(3, F)) : conjSL 1 h = h := by
  apply Subtype.ext
  rw [coe_conjSL, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]

theorem conjSL_mul (g g' : GL (Fin 3) F) (h : SL(3, F)) :
    conjSL (g * g') h = conjSL g (conjSL g' h) := by
  apply Subtype.ext
  rw [coe_conjSL, coe_conjSL, coe_conjSL, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

theorem conjSL_toGL (h' h : SL(3, F)) :
    conjSL (Matrix.SpecialLinearGroup.toGL h') h = h' * h * h'⁻¹ := by
  apply Subtype.ext
  rw [coe_conjSL, ← map_inv]
  rfl

@[expose] def diagA (a : Fˣ) : GL (Fin 3) F where
  val := diagonal ![(a : F), 1, 1]
  inv := diagonal ![((a⁻¹ : Fˣ) : F), 1, 1]
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp

theorem coe_diagA (a : Fˣ) :
    ((diagA a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![(a : F), 1, 1] :=
  rfl

theorem coe_diagA_inv (a : Fˣ) :
    (((diagA a)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![((a⁻¹ : Fˣ) : F), 1, 1] :=
  rfl

theorem conjSL_diagA_transvection (a : Fˣ) {i j : Fin 3} (hij : i ≠ j) (c : F) :
    conjSL (diagA a) (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection hij
        (![(a : F), 1, 1] i * c * ![((a⁻¹ : Fˣ) : F), 1, 1] j) := by
  apply Subtype.ext
  rw [coe_conjSL, coe_diagA, coe_diagA_inv]
  change diagonal ![(a : F), 1, 1] * Matrix.transvection i j c *
      diagonal ![((a⁻¹ : Fˣ) : F), 1, 1] =
    Matrix.transvection i j (![(a : F), 1, 1] i * c * ![((a⁻¹ : Fˣ) : F), 1, 1] j)
  ext k l
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> (try exact absurd rfl hij) <;> fin_cases k <;> fin_cases l <;>
    simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]

end Conj

theorem mul_comm_of_card_le_three {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 3)
    (x y : G) : x * y = y * x := by
  have hpos := Nat.card_pos (α := G)
  have key : Nat.card G = 1 ∨ (Nat.card G).Prime := by
    have h3 : Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3 := by omega
    rcases h3 with h3 | h3 | h3
    · exact Or.inl h3
    · exact Or.inr (h3 ▸ Nat.prime_two)
    · exact Or.inr (h3 ▸ Nat.prime_three)
  rcases key with h1 | hp
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.1 h1).1
    exact Subsingleton.elim _ _
  · haveI : Fact (Nat.card G).Prime := ⟨hp⟩
    haveI : IsCyclic G := isCyclic_of_prime_card rfl
    exact (IsCyclic.commutative (α := G)).is_comm.comm x y

section Graph

variable {F : Type} [Field F] {C : Type} [Group C]

@[expose] def frameGraph (ρ : SL(3, F) →* C) : Subgroup (GL (Fin 3) F × C) where
  carrier := {p | ∀ h : SL(3, F), p.2 * ρ h * p.2⁻¹ = ρ (conjSL p.1 h)}
  mul_mem' {p p'} hp hp' h := by
    show (p.2 * p'.2) * ρ h * (p.2 * p'.2)⁻¹ = ρ (conjSL (p.1 * p'.1) h)
    rw [conjSL_mul, ← hp, ← hp' h]
    group
  one_mem' h := by
    show 1 * ρ h * 1⁻¹ = ρ (conjSL 1 h)
    rw [conjSL_one, one_mul, inv_one, mul_one]
  inv_mem' {p} hp h := by
    show p.2⁻¹ * ρ h * p.2⁻¹⁻¹ = ρ (conjSL p.1⁻¹ h)
    have h1 := hp (conjSL p.1⁻¹ h)
    rw [← conjSL_mul, mul_inv_cancel, conjSL_one] at h1
    rw [← h1]
    group

theorem conjSL_scalar (c : Fˣ) (h : SL(3, F)) :
    conjSL (Matrix.GeneralLinearGroup.scalar (Fin 3) c) h = h := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_conjSL, ← map_inv, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.GeneralLinearGroup.coe_scalar]
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [Units.val_inv_eq_inv_val]
  field_simp

theorem exists_frameHom [Finite F] {p f : ℕ}
    (hF : Sec4.PiField true p f F) (hq : Sec4.ModThree true (p ^ f)) (hq2 : 2 < p ^ f)
    [Finite C] (ρ : SL(3, F) →* C) (hρ : ∃ g, ρ g ≠ 1)
    (hcard : Nat.card C = Nat.card SL(3, F))
    (hab : ∀ N : Subgroup C, N.Normal → (∀ x y : N, x * y = y * x) → N = ⊥)
    (c : Fˣ → C)
    (hc : ∀ (a : Fˣ) (h : SL(3, F)), c a * ρ h * (c a)⁻¹ = ρ (conjSL (diagA a) h)) :
    ∃ Ψ : GL (Fin 3) F →* C, (∀ h, Ψ (Matrix.SpecialLinearGroup.toGL h) = ρ h) ∧
      (∀ a, Ψ (diagA a) = c a) ∧ Function.Surjective Ψ ∧
      Ψ.ker =
        (Matrix.ProjGenLinGroup.mk : GL (Fin 3) F →* Matrix.ProjGenLinGroup (Fin 3) F).ker := by
  classical
  obtain ⟨hkerZ, hQn, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.sl3_hom_structure ρ hρ hcard
  set Q := ρ.range with hQ
  haveI : Q.Normal := hQn
  have hidx : Q.index ≤ 3 := by
    have h1 := Subgroup.card_ker_mul_card_range ρ
    have h2 := Subgroup.card_mul_index Q
    have hker3 : Nat.card ρ.ker ≤ 3 := by
      calc Nat.card ρ.ker ≤ Nat.card (Subgroup.center SL(3, F)) := Subgroup.card_le_of_le hkerZ
        _ = Nat.card (rootsOfUnity (max (Fintype.card (Fin 3)) 1) F) :=
          Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity).toEquiv
        _ ≤ 3 := by
          have h3 : max (Fintype.card (Fin 3)) 1 = 3 := by simp
          rw [h3]
          exact card_rootsOfUnity F 3
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    have e : Nat.card Q * Q.index = Nat.card Q * Nat.card ρ.ker := by
      rw [h2, hcard, ← h1, mul_comm]
    have := Nat.eq_of_mul_eq_mul_left hQpos e
    omega
  have hQcomm : ∀ x y : C, x * y * x⁻¹ * y⁻¹ ∈ Q := by
    intro x y
    have hcomm := mul_comm_of_card_le_three (G := C ⧸ Q)
      (by rw [← Subgroup.index_eq_card]; exact hidx) (x : C ⧸ Q) (y : C ⧸ Q)
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hcomm]
    group
  set CQ := Subgroup.centralizer (Q : Set C) with hCQ
  have hZQ : CQ ⊓ Q = ⊥ := by
    refine hab _ inferInstance ?_
    rintro ⟨x, hxC, hxQ⟩ ⟨y, hyC, hyQ⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (Subgroup.mem_centralizer_iff.1 hxC y hyQ).symm
  have hCQ1 : CQ = ⊥ := by
    refine hab _ inferInstance ?_
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hk : x * y * x⁻¹ * y⁻¹ ∈ CQ ⊓ Q :=
      ⟨CQ.mul_mem (CQ.mul_mem (CQ.mul_mem hx hy) (CQ.inv_mem hx)) (CQ.inv_mem hy), hQcomm x y⟩
    rw [hZQ, Subgroup.mem_bot] at hk
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [hk, one_mul]
  set S := frameGraph ρ with hS
  have hSsl : ∀ h' : SL(3, F), (Matrix.SpecialLinearGroup.toGL h', ρ h') ∈ S := fun h' h => by
    show ρ h' * ρ h * (ρ h')⁻¹ = ρ (conjSL _ h)
    rw [conjSL_toGL, map_mul, map_mul, map_inv]
  have hSD : ∀ a : Fˣ, (diagA a, c a) ∈ S := fun a h => hc a h
  have hSsc : ∀ z : Fˣ, (Matrix.GeneralLinearGroup.scalar (Fin 3) z, (1 : C)) ∈ S :=
    fun z h => by
      show 1 * ρ h * 1⁻¹ = ρ (conjSL _ h)
      rw [conjSL_scalar, one_mul, inv_one, mul_one]
  let π₁ : S →* GL (Fin 3) F := (MonoidHom.fst _ _).comp S.subtype
  have hinj : Function.Injective π₁ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨g, x⟩, hgx⟩ h1
    change g = 1 at h1
    subst h1
    have hx : x ∈ CQ := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨h, rfl⟩
      have h2 := hgx h
      rw [conjSL_one] at h2
      calc ρ h * x = (x * ρ h * x⁻¹) * x := by rw [h2]
        _ = x * ρ h := by group
    rw [hCQ1, Subgroup.mem_bot] at hx
    subst hx
    rfl
  have hsurj : Function.Surjective π₁ := by
    intro g
    set a := Matrix.GeneralLinearGroup.det g with ha
    have hdet : ((g * (diagA a)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
      rw [Units.val_mul, Matrix.det_mul, coe_diagA_inv, det_diagonal, Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, mul_one]
      rw [ha, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply]
      exact mul_inv_cancel₀ (by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _)
    set h' : SL(3, F) := ⟨_, hdet⟩ with hh'
    have hgl : Matrix.SpecialLinearGroup.toGL h' = g * (diagA a)⁻¹ := Units.ext rfl
    refine ⟨⟨(Matrix.SpecialLinearGroup.toGL h', ρ h') * (diagA a, c a),
      S.mul_mem (hSsl h') (hSD a)⟩, ?_⟩
    change Matrix.SpecialLinearGroup.toGL h' * diagA a = g
    rw [hgl, inv_mul_cancel_right]
  let e := MulEquiv.ofBijective π₁ ⟨hinj, hsurj⟩
  let Ψ : GL (Fin 3) F →* C := ((MonoidHom.snd _ _).comp S.subtype).comp e.symm.toMonoidHom
  have hΨmem : ∀ g, (g, Ψ g) ∈ S := by
    intro g
    have h1 : ((e.symm g : S) : GL (Fin 3) F × C).1 = g := e.apply_symm_apply g
    have h2 := (e.symm g).2
    have h3 : ((e.symm g : S) : GL (Fin 3) F × C) = (g, Ψ g) := Prod.ext h1 rfl
    rw [h3] at h2
    exact h2
  have hΨuniq : ∀ g x, (g, x) ∈ S → Ψ g = x := by
    intro g x hx
    have h1 : (⟨(g, Ψ g), hΨmem g⟩ : S) = ⟨(g, x), hx⟩ := hinj rfl
    exact congrArg (fun s : S => (s : GL (Fin 3) F × C).2) h1
  haveI hperf : Group.IsPerfect ↥(CFSG.PGLModel.projImage (Sec4.slPi true 3 (p ^ f) F)) :=
    Sec13.isPerfect_projImage_slPi hF hq2
  have hker : Ψ.ker = (Matrix.ProjGenLinGroup.mk : GL (Fin 3) F →* _).ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Sec4.mk_eq_one_iff_mem_statedScalars]
    constructor
    · intro hg
      have hS1 := hΨmem g
      rw [hg] at hS1
      refine Sec4.mem_statedScalars_of_comm_mod hF hq fun s hs => ?_
      have hsdet : (s : Matrix (Fin 3) (Fin 3) F).det = 1 := (Sec4.mem_slPi_true _).1 hs
      set h : SL(3, F) := ⟨s, hsdet⟩ with hh
      have hrel := hS1 h
      rw [one_mul, inv_one, mul_one] at hrel
      have hkerel : conjSL g h * h⁻¹ ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, ← hrel, mul_inv_cancel]
      obtain ⟨r, hr3, hr⟩ := (Matrix.SpecialLinearGroup.mem_center_iff).1 (hkerZ hkerel)
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [zero_pow (by simp)] at hr3
        exact zero_ne_one hr3
      refine ⟨Units.mk0 r hr0, ?_⟩
      have hs' : Matrix.SpecialLinearGroup.toGL h = s := Units.ext rfl
      have hgs : Matrix.SpecialLinearGroup.toGL (conjSL g h) = g * s * g⁻¹ :=
        Units.ext (by rw [Units.val_mul, Units.val_mul, ← hs']; rfl)
      calc Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 r hr0) =
          Matrix.SpecialLinearGroup.toGL (conjSL g h * h⁻¹) :=
            Units.ext (by rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, hr]; rfl)
        _ = g * s * g⁻¹ * s⁻¹ := by rw [map_mul, map_inv, hgs, hs']
    · rintro ⟨z, rfl⟩
      exact hΨuniq _ _ (hSsc z)
  have hrange :
      (Matrix.ProjGenLinGroup.mk : GL (Fin 3) F →* Matrix.ProjGenLinGroup (Fin 3) F).range =
      CFSG.PGLModel.projImage (Sec4.glPi true 3 (p ^ f) F) := by
    rw [MonoidHom.range_eq_map]
    rfl
  have hcardP : Nat.card (CFSG.PGLModel.projImage (Sec4.glPi true 3 (p ^ f) F)) = Nat.card C := by
    rw [Sec16.ProofKSL3Two.card_projImage_glPi hF, hcard,
      Nat.card_congr (Sec4.slPiTrueEquiv (p ^ f) F).toEquiv]
  have hcardR : Nat.card Ψ.range = Nat.card C := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange Ψ).toEquiv,
      Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, hrange, hcardP]
  have hΨsurj : Function.Surjective Ψ := by
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ hcardR
  exact ⟨Ψ, fun h => hΨuniq _ _ (hSsl h), fun a => hΨuniq _ _ (hSD a), hΨsurj, hker⟩

theorem nonempty_mulEquiv_projImage_of_surjective {q : ℕ} (Ψ : GL (Fin 3) F →* C)
    (hΨ : Function.Surjective Ψ)
    (hker : Ψ.ker =
      (Matrix.ProjGenLinGroup.mk : GL (Fin 3) F →* Matrix.ProjGenLinGroup (Fin 3) F).ker) :
    Nonempty (C ≃* CFSG.PGLModel.projImage (Sec4.glPi true 3 q F)) := by
  have hrange :
      (Matrix.ProjGenLinGroup.mk : GL (Fin 3) F →* Matrix.ProjGenLinGroup (Fin 3) F).range =
      CFSG.PGLModel.projImage (Sec4.glPi true 3 q F) := by
    rw [MonoidHom.range_eq_map]
    rfl
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective Ψ hΨ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans
    ((QuotientGroup.quotientKerEquivRange _).trans (MulEquiv.subgroupCongr hrange))⟩

end Graph

section ThreeD4

set_option linter.unusedSectionVars false

open CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
  CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem rootChar_frameTuple (x : Kˣ) (v : Fin d4.rank → ℤ) :
    rootChar (τ := d4) ![x, x, x⁻¹, x] v = x ^ (v 0 + v 1 + v 3 - v 2) := by
  show ∏ i : Fin 4, (![x, x, x⁻¹, x] : Fin 4 → Kˣ) i ^ v i =
    x ^ (v (0 : Fin 4) + v (1 : Fin 4) + v (3 : Fin 4) - v (2 : Fin 4))
  rw [Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, _root_.inv_zpow']
  rw [← _root_.zpow_add, ← _root_.zpow_add, ← _root_.zpow_add]
  congr 1
  ring

theorem rootDiagUnit_mul_rootDiagUnit (a b : Fin d4.rank → Kˣ) :
    rootDiagUnit d4 a * rootDiagUnit d4 b = rootDiagUnit d4 (a * b) :=
  Units.ext (rootDiag_mul_rootDiag a b)

theorem entrywise_rootDiagUnit (σ' : K →+* K) (a : Fin d4.rank → Kˣ) :
    Units.map (entrywiseHom σ') (rootDiagUnit d4 a) =
      rootDiagUnit d4 fun i => Units.map σ'.toMonoidHom (a i) :=
  Units.ext (entrywise_rootDiag σ' a)

theorem frameTuple_conj_xa (x : Kˣ) {k : ℕ} (hk : k < 24) (u : K) :
    rootDiagUnit d4 ![x, x, x⁻¹, x] * ((xa k u : adjointGroup d4 K) : ModGL d4 K) *
        (rootDiagUnit d4 ![x, x, x⁻¹, x])⁻¹ =
      ((xa k (((x ^ (d4Root k 0 + d4Root k 1 + d4Root k 3 - d4Root k 2) : Kˣ) : K) * u) :
        adjointGroup d4 K) : ModGL d4 K) := by
  rw [← rootChar_frameTuple]
  exact rootDiagUnit_conj_xPar_d4 _ (isRoot_d4Root hk) u

theorem conj_triple {G : Type*} [Group G] (g A B C : G) :
    g * (A * B * C) * g⁻¹ = (g * A * g⁻¹) * (g * B * g⁻¹) * (g * C * g⁻¹) := by
  group

variable {σ' : K →+* K} (hσ' : ∀ c, σ' (σ' (σ' c)) = c)

theorem frameTuple_conj_fP1 (x : Kˣ) (hx : σ' (x : K) = x) (c : K) :
    rootDiagUnit d4 ![x, x, x⁻¹, x] * ((fP1 σ' hσ' c : adjointGroup d4 K) : ModGL d4 K) *
        (rootDiagUnit d4 ![x, x, x⁻¹, x])⁻¹ =
      ((fP1 σ' hσ' ((x : K) * c) : adjointGroup d4 K) : ModGL d4 K) := by
  rw [fP1_eq, fP1_eq, Subgroup.coe_mul, Subgroup.coe_mul, conj_triple,
    frameTuple_conj_xa x (by norm_num), frameTuple_conj_xa x (by norm_num),
    frameTuple_conj_xa x (by norm_num), Subgroup.coe_mul, Subgroup.coe_mul]
  have e0 : d4Root 0 0 + d4Root 0 1 + d4Root 0 3 - d4Root 0 2 = 1 := by decide
  have e1 : d4Root 1 0 + d4Root 1 1 + d4Root 1 3 - d4Root 1 2 = 1 := by decide
  have e3 : d4Root 3 0 + d4Root 3 1 + d4Root 3 3 - d4Root 3 2 = 1 := by decide
  have a1 : (x : K) * σ' c = σ' ((x : K) * c) := by rw [map_mul, hx]
  have a2 : (x : K) * σ' (σ' c) = σ' (σ' ((x : K) * c)) := by rw [map_mul, map_mul, hx, hx]
  rw [e0, e1, e3, zpow_one, a1, a2]

theorem frameTuple_conj_fM1 (x : Kˣ) (hx : σ' (x : K) = x) (c : K) :
    rootDiagUnit d4 ![x, x, x⁻¹, x] * ((fM1 σ' hσ' c : adjointGroup d4 K) : ModGL d4 K) *
        (rootDiagUnit d4 ![x, x, x⁻¹, x])⁻¹ =
      ((fM1 σ' hσ' (((x⁻¹ : Kˣ) : K) * c) : adjointGroup d4 K) : ModGL d4 K) := by
  rw [fM1_eq, fM1_eq, Subgroup.coe_mul, Subgroup.coe_mul, conj_triple,
    frameTuple_conj_xa x (by norm_num), frameTuple_conj_xa x (by norm_num),
    frameTuple_conj_xa x (by norm_num), Subgroup.coe_mul, Subgroup.coe_mul]
  have e0 : d4Root 4 0 + d4Root 4 1 + d4Root 4 3 - d4Root 4 2 = -1 := by decide
  have e1 : d4Root 6 0 + d4Root 6 1 + d4Root 6 3 - d4Root 6 2 = -1 := by decide
  have e3 : d4Root 10 0 + d4Root 10 1 + d4Root 10 3 - d4Root 10 2 = -1 := by decide
  have hxi : σ' (((x⁻¹ : Kˣ) : K)) = ((x⁻¹ : Kˣ) : K) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx]
  have a1 : ((x⁻¹ : Kˣ) : K) * σ' c = σ' (((x⁻¹ : Kˣ) : K) * c) := by rw [map_mul, hxi]
  have a2 : ((x⁻¹ : Kˣ) : K) * σ' (σ' c) = σ' (σ' (((x⁻¹ : Kˣ) : K) * c)) := by
    rw [map_mul, map_mul, hxi, hxi]
  rw [e0, e1, e3, _root_.zpow_neg_one, a1, a2]

theorem frameTuple_conj_fP2 (μ : Kˣ) (x : Kˣ) (c : K) :
    rootDiagUnit d4 ![x, x, x⁻¹, x] * ((fP2 σ' hσ' μ c : adjointGroup d4 K) : ModGL d4 K) *
        (rootDiagUnit d4 ![x, x, x⁻¹, x])⁻¹ =
      ((fP2 σ' hσ' μ c : adjointGroup d4 K) : ModGL d4 K) := by
  rw [fP2_eq, Subgroup.coe_mul, Subgroup.coe_mul, conj_triple,
    frameTuple_conj_xa x (by norm_num), frameTuple_conj_xa x (by norm_num),
    frameTuple_conj_xa x (by norm_num)]
  have e0 : d4Root 5 0 + d4Root 5 1 + d4Root 5 3 - d4Root 5 2 = 0 := by decide
  have e1 : d4Root 7 0 + d4Root 7 1 + d4Root 7 3 - d4Root 7 2 = 0 := by decide
  have e3 : d4Root 9 0 + d4Root 9 1 + d4Root 9 3 - d4Root 9 2 = 0 := by decide
  rw [e0, e1, e3, zpow_zero, Units.val_one, one_mul, one_mul, one_mul]

theorem frameTuple_conj_fM2 (μ : Kˣ) (x : Kˣ) (c : K) :
    rootDiagUnit d4 ![x, x, x⁻¹, x] * ((fM2 σ' hσ' μ c : adjointGroup d4 K) : ModGL d4 K) *
        (rootDiagUnit d4 ![x, x, x⁻¹, x])⁻¹ =
      ((fM2 σ' hσ' μ c : adjointGroup d4 K) : ModGL d4 K) := by
  rw [fM2_eq, Subgroup.coe_mul, Subgroup.coe_mul, conj_triple,
    frameTuple_conj_xa x (by norm_num), frameTuple_conj_xa x (by norm_num),
    frameTuple_conj_xa x (by norm_num)]
  have e0 : d4Root 11 0 + d4Root 11 1 + d4Root 11 3 - d4Root 11 2 = 0 := by decide
  have e1 : d4Root 14 0 + d4Root 14 1 + d4Root 14 3 - d4Root 14 2 = 0 := by decide
  have e3 : d4Root 16 0 + d4Root 16 1 + d4Root 16 3 - d4Root 16 2 = 0 := by decide
  rw [e0, e1, e3, zpow_zero, Units.val_one, one_mul, one_mul, one_mul]

theorem frameTuple_conj_fP3 (μ : Kˣ) (x : Kˣ) (hx : σ' (x : K) = x) (c : K) :
    rootDiagUnit d4 ![x, x, x⁻¹, x] * ((fP3 σ' hσ' μ c : adjointGroup d4 K) : ModGL d4 K) *
        (rootDiagUnit d4 ![x, x, x⁻¹, x])⁻¹ =
      ((fP3 σ' hσ' μ ((x : K) * c) : adjointGroup d4 K) : ModGL d4 K) := by
  rw [fP3_eq, fP3_eq, Subgroup.coe_mul, Subgroup.coe_mul, conj_triple,
    frameTuple_conj_xa x (by norm_num), frameTuple_conj_xa x (by norm_num),
    frameTuple_conj_xa x (by norm_num), Subgroup.coe_mul, Subgroup.coe_mul]
  have e0 : d4Root 15 0 + d4Root 15 1 + d4Root 15 3 - d4Root 15 2 = 1 := by decide
  have e1 : d4Root 13 0 + d4Root 13 1 + d4Root 13 3 - d4Root 13 2 = 1 := by decide
  have e3 : d4Root 12 0 + d4Root 12 1 + d4Root 12 3 - d4Root 12 2 = 1 := by decide
  have a1 : (x : K) * -((μ : K) * c) = -((μ : K) * ((x : K) * c)) := by ring
  have a2 : (x : K) * -σ' ((μ : K) * c) = -σ' ((μ : K) * ((x : K) * c)) := by
    rw [map_mul, map_mul, map_mul, hx]
    ring
  have a3 : (x : K) * -σ' (σ' ((μ : K) * c)) = -σ' (σ' ((μ : K) * ((x : K) * c))) := by
    simp only [map_mul, hx]
    ring
  rw [e0, e1, e3, zpow_one, a1, a2, a3]

theorem frameTuple_conj_fM3 (μ : Kˣ) (x : Kˣ) (hx : σ' (x : K) = x) (c : K) :
    rootDiagUnit d4 ![x, x, x⁻¹, x] * ((fM3 σ' hσ' μ c : adjointGroup d4 K) : ModGL d4 K) *
        (rootDiagUnit d4 ![x, x, x⁻¹, x])⁻¹ =
      ((fM3 σ' hσ' μ (((x⁻¹ : Kˣ) : K) * c) : adjointGroup d4 K) : ModGL d4 K) := by
  rw [fM3_eq, fM3_eq, Subgroup.coe_mul, Subgroup.coe_mul, conj_triple,
    frameTuple_conj_xa x (by norm_num), frameTuple_conj_xa x (by norm_num),
    frameTuple_conj_xa x (by norm_num), Subgroup.coe_mul, Subgroup.coe_mul]
  have e0 : d4Root 20 0 + d4Root 20 1 + d4Root 20 3 - d4Root 20 2 = -1 := by decide
  have e1 : d4Root 18 0 + d4Root 18 1 + d4Root 18 3 - d4Root 18 2 = -1 := by decide
  have e3 : d4Root 17 0 + d4Root 17 1 + d4Root 17 3 - d4Root 17 2 = -1 := by decide
  have hxi : σ' (((x⁻¹ : Kˣ) : K)) = ((x⁻¹ : Kˣ) : K) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx]
  have a1 : ((x⁻¹ : Kˣ) : K) * -(((μ⁻¹ : Kˣ) : K) * c) =
      -(((μ⁻¹ : Kˣ) : K) * (((x⁻¹ : Kˣ) : K) * c)) := by ring
  have a2 : ((x⁻¹ : Kˣ) : K) * -σ' (((μ⁻¹ : Kˣ) : K) * c) =
      -σ' (((μ⁻¹ : Kˣ) : K) * (((x⁻¹ : Kˣ) : K) * c)) := by
    rw [map_mul, map_mul, map_mul, hxi]
    ring
  have a3 : ((x⁻¹ : Kˣ) : K) * -σ' (σ' (((μ⁻¹ : Kˣ) : K) * c)) =
      -σ' (σ' (((μ⁻¹ : Kˣ) : K) * (((x⁻¹ : Kˣ) : K) * c))) := by
    simp only [map_mul, hxi]
    ring
  rw [e0, e1, e3, _root_.zpow_neg_one, a1, a2, a3]

theorem rootDiagUnit_conj_rootDiagUnit (a b : Fin d4.rank → Kˣ) :
    rootDiagUnit d4 a * rootDiagUnit d4 b * (rootDiagUnit d4 a)⁻¹ = rootDiagUnit d4 b := by
  rw [rootDiagUnit_mul_rootDiagUnit, mul_comm, ← rootDiagUnit_mul_rootDiagUnit,
    mul_inv_cancel_right]

theorem a2Conj_rootDiagUnit_of_fixed (b : Fin d4.rank → Kˣ)
    (hb : ∀ i, Units.map σ.toRingHom.toMonoidHom (b i) = b i) :
    a2Conj σ d (rootDiagUnit d4 b) = rootDiagUnit d4 b := by
  have hb' : (fun i => Units.map σ.toRingHom.toMonoidHom (b i)) = b := funext hb
  unfold a2Conj a2S
  rw [entrywise_rootDiagUnit, hb']
  exact rootDiagUnit_conj_rootDiagUnit _ _

theorem exists_fixSub_frameHom (h : A2Std σ d q) {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hpq : p ^ f = q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    ∃ μ : Kˣ, (d : K) * σ (μ : K) = μ ∧
      ∃ Ψ : GL (Fin 3) (fixedField σ.toRingHom) →*
          ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ),
        Function.Surjective Ψ ∧
        Ψ.ker = (Matrix.ProjGenLinGroup.mk : GL (Fin 3) (fixedField σ.toRingHom) →*
          Matrix.ProjGenLinGroup (Fin 3) (fixedField σ.toRingHom)).ker ∧
        (∀ c, (((Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
            (show (0 : Fin 3) ≠ 1 by decide) c)) :
              ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ)) :
            graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
          ((fP1 σ.toRingHom h.toCore.cube_apply (c : K) : adjointGroup d4 K) :
            ModGL TwistTag.D4.tag K)) ∧
        (∀ c, (((Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) c)) :
              ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ)) :
            graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
          ((fP2 σ.toRingHom h.toCore.cube_apply μ (c : K) : adjointGroup d4 K) :
            ModGL TwistTag.D4.tag K)) ∧
        (∀ c, (((Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
            (show (0 : Fin 3) ≠ 2 by decide) c)) :
              ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ)) :
            graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
          ((fP3 σ.toRingHom h.toCore.cube_apply μ (c : K) : adjointGroup d4 K) :
            ModGL TwistTag.D4.tag K)) ∧
        (∀ c, (((Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 0 by decide) c)) :
              ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ)) :
            graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
          ((fM1 σ.toRingHom h.toCore.cube_apply (c : K) : adjointGroup d4 K) :
            ModGL TwistTag.D4.tag K)) ∧
        (∀ c, (((Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) c)) :
              ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ)) :
            graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
          ((fM2 σ.toRingHom h.toCore.cube_apply μ (c : K) : adjointGroup d4 K) :
            ModGL TwistTag.D4.tag K)) ∧
        (∀ c, (((Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 0 by decide) c)) :
              ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ)) :
            graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
          ((fM3 σ.toRingHom h.toCore.cube_apply μ (c : K) : adjointGroup d4 K) :
            ModGL TwistTag.D4.tag K)) ∧
        (∀ a : (fixedField σ.toRingHom)ˣ, (((Ψ (diagA a) :
            ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ)) :
            graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
          rootDiagUnit d4 ![Units.map (fixedField σ.toRingHom).subtype.toMonoidHom a,
            Units.map (fixedField σ.toRingHom).subtype.toMonoidHom a,
            (Units.map (fixedField σ.toRingHom).subtype.toMonoidHom a)⁻¹,
            Units.map (fixedField σ.toRingHom).subtype.toMonoidHom a]) := by
  classical
  have hc := h.toCore
  obtain ⟨ρ, hρ, hcard, μ, hμ, h1, h2, h3, h4, h5, h6⟩ := exists_hom_fixSub hc φ hφ
  have hFcard : Nat.card (fixedField σ.toRingHom) = p ^ f := by
    rw [hpq]
    exact CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom h.two_le h.card h.frob
  have hPi : Sec4.PiField true p f (fixedField σ.toRingHom) := ⟨hp, hf, hFcard⟩
  have hmod : Sec4.ModThree true (p ^ f) := by
    rw [hpq]
    exact h.mod3
  have hq2 : 2 < p ^ f := by
    have := h.two_le
    have := h.mod3
    omega
  let ι : (fixedField σ.toRingHom)ˣ →* Kˣ := Units.map (fixedField σ.toRingHom).subtype.toMonoidHom
  have hισ : ∀ a : (fixedField σ.toRingHom)ˣ, σ ((ι a : Kˣ) : K) = ((ι a : Kˣ) : K) :=
    fun a => (a : fixedField σ.toRingHom).2
  have hιfix : ∀ a : (fixedField σ.toRingHom)ˣ, Units.map σ.toRingHom.toMonoidHom (ι a) = ι a :=
    fun a => Units.ext (hισ a)
  have hιinv : ∀ a : (fixedField σ.toRingHom)ˣ,
      Units.map σ.toRingHom.toMonoidHom (ι a)⁻¹ = (ι a)⁻¹ :=
    fun a => by rw [map_inv, hιfix]
  have hpart : ∀ a : (fixedField σ.toRingHom)ˣ,
      ∃ y : ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ),
      (((y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : ModGL TwistTag.D4.tag K) =
        rootDiagUnit d4 ![ι a, ι a, (ι a)⁻¹, ι a] := by
    intro a
    obtain ⟨g, hg, hgc⟩ := A2Core.a2_torus_mem hc (hιfix a) (hιinv a)
    have hgY : (g : ModGL TwistTag.D4.tag K) ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
      rw [← hc.twisted_eq]
      exact ⟨g, (iSup_le fun i => hHatE_le_twistedGroup hc.cube_apply i) hg, rfl⟩
    refine ⟨⟨⟨g, hgY⟩, ?_⟩, hgc⟩
    show φ ⟨g, hgY⟩ = ⟨g, hgY⟩
    apply Subtype.ext
    rw [hφ]
    change a2Conj σ d (g : ModGL TwistTag.D4.tag K) = (g : ModGL TwistTag.D4.tag K)
    rw [hgc]
    refine a2Conj_rootDiagUnit_of_fixed _ fun i => ?_
    fin_cases i
    · exact hιfix a
    · exact hιfix a
    · exact hιinv a
    · exact hιfix a
  choose c hcc using hpart
  have hc' : ∀ (a : (fixedField σ.toRingHom)ˣ) (x : SL(3, fixedField σ.toRingHom)),
      c a * ρ x * (c a)⁻¹ = ρ (conjSL (diagA a) x) := by
    intro a
    have hσc := hc.cube_apply
    have fam : ∀ {i j : Fin 3} (hij : i ≠ j) (P : K → adjointGroup d4 K) (χ : K)
        (_ : ∀ c' : fixedField σ.toRingHom, (((ρ (Matrix.SpecialLinearGroup.transvection hij c') :
            ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ)) :
              graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
            ((P (c' : K) : adjointGroup d4 K) : ModGL d4 K))
        (_ : ∀ u : K, rootDiagUnit d4 ![ι a, ι a, (ι a)⁻¹, ι a] *
            ((P u : adjointGroup d4 K) : ModGL d4 K) *
            (rootDiagUnit d4 ![ι a, ι a, (ι a)⁻¹, ι a])⁻¹ =
              ((P (χ * u) : adjointGroup d4 K) : ModGL d4 K))
        (_ : ∀ c' : fixedField σ.toRingHom, χ * (c' : K) =
          (((![(a : fixedField σ.toRingHom), 1, 1] i * c' *
            ![((a⁻¹ : (fixedField σ.toRingHom)ˣ) : fixedField σ.toRingHom), 1, 1] j :
              fixedField σ.toRingHom)) : K))
        (c' : fixedField σ.toRingHom),
        c a * ρ (Matrix.SpecialLinearGroup.transvection hij c') * (c a)⁻¹ =
          ρ (conjSL (diagA a) (Matrix.SpecialLinearGroup.transvection hij c')) := by
      intro i j hij P χ hP hconj hχ c'
      rw [conjSL_diagA_transvection]
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hP, hP, hcc a, hconj, hχ]
    let ψ₁ : SL(3, fixedField σ.toRingHom) →* ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ) :=
      (MulAut.conj (c a)).toMonoidHom.comp ρ
    let ψ₂ : SL(3, fixedField σ.toRingHom) →* ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ) :=
      ρ.comp (conjSL (diagA a))
    have hψ := forall_mem_of_transvections
      ((MonoidHom.fst ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ)
        ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ)).eqLocus
        (MonoidHom.snd ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ)
          ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ)))
      (ψ₁.prod ψ₂)
      (fun c' => fam _ _ _ h1 (frameTuple_conj_fP1 hσc _ (hισ a))
        (fun c' => by
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, mul_one, one_mul, Subfield.coe_mul] <;>
        first | rfl | (rw [mul_comm]; rfl)) c')
      (fun c' => fam _ _ 1 h2 (fun u => by rw [one_mul]; exact frameTuple_conj_fP2 hσc μ _ u)
        (fun c' => by
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, mul_one, one_mul, Subfield.coe_mul] <;>
        first | rfl | (rw [mul_comm]; rfl)) c')
      (fun c' => fam _ _ _ h3 (frameTuple_conj_fP3 hσc μ _ (hισ a))
        (fun c' => by
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, mul_one, one_mul, Subfield.coe_mul] <;>
        first | rfl | (rw [mul_comm]; rfl)) c')
      (fun c' => fam _ _ _ h4 (frameTuple_conj_fM1 hσc _ (hισ a))
        (fun c' => by
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, mul_one, one_mul, Subfield.coe_mul] <;>
        first | rfl | (rw [mul_comm]; rfl)) c')
      (fun c' => fam _ _ 1 h5 (fun u => by rw [one_mul]; exact frameTuple_conj_fM2 hσc μ _ u)
        (fun c' => by
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, mul_one, one_mul, Subfield.coe_mul] <;>
        first | rfl | (rw [mul_comm]; rfl)) c')
      (fun c' => fam _ _ _ h6 (frameTuple_conj_fM3 hσc μ _ (hισ a))
        (fun c' => by
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, mul_one, one_mul, Subfield.coe_mul] <;>
        first | rfl | (rw [mul_comm]; rfl)) c')
    intro x
    exact hψ x
  obtain ⟨Ψ, hΨρ, hΨc, hΨs, hΨk⟩ := exists_frameHom hPi hmod hq2 ρ hρ hcard
    (A2Core.a2_noAbel_fixSub hc φ hφ) c hc'
  refine ⟨μ, hμ, Ψ, hΨs, hΨk, fun c' => ?_, fun c' => ?_, fun c' => ?_, fun c' => ?_,
    fun c' => ?_, fun c' => ?_, fun a => ?_⟩
  · rw [hΨρ]; exact h1 c'
  · rw [hΨρ]; exact h2 c'
  · rw [hΨρ]; exact h3 c'
  · rw [hΨρ]; exact h4 c'
  · rw [hΨρ]; exact h5 c'
  · rw [hΨρ]; exact h6 c'
  · rw [hΨc]; exact hcc a

theorem nonempty_fixSub_mulEquiv_projImage (h : A2Std σ d q) {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hpq : p ^ f = q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K)) :
    Nonempty (↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ) ≃*
      CFSG.PGLModel.projImage (Sec4.glPi true 3 (p ^ f) ↥(fixedField σ.toRingHom))) := by
  obtain ⟨-, -, Ψ, hΨ, hker, -⟩ := exists_fixSub_frameHom h hp hf hpq φ hφ
  exact nonempty_mulEquiv_projImage_of_surjective Ψ hΨ hker

end ThreeD4

section Transfer

set_option linter.unusedSectionVars false

open CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
  CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

theorem diagramMap_conj_rootDiagUnit {L : Type} [Field L] (b : Fin d4.rank → Lˣ) :
    diagramMap TwistTag.D4 L * rootDiagUnit d4 b * (diagramMap TwistTag.D4 L)⁻¹ =
      rootDiagUnit d4 (fun i => b (TwistTag.D4.perm.symm i)) := by
  rw [diagramMap_mul_rootDiagUnit, mul_inv_cancel_right]

theorem rootDiagUnit_inv' {L : Type} [Field L] (b : Fin d4.rank → Lˣ) :
    (rootDiagUnit d4 b)⁻¹ = rootDiagUnit d4 b⁻¹ :=
  Units.ext rfl

theorem coe_gammaP_HSL {K : Type} [Field K] (t : Kˣ) (u : adjointGroup Tag.D4 K) :
    ((gammaP K (HSL t) u : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
      rootDiagUnit Tag.D4 (fun j => t ^ Tag.D4.cartan ⟨2, by decide⟩ j) *
        CFSG.HardMathSupport.Lang.D4Three.d4P K * (u : ModGL Tag.D4 K) *
        (CFSG.HardMathSupport.Lang.D4Three.d4P K)⁻¹ *
          (rootDiagUnit Tag.D4 (fun j => t ^ Tag.D4.cartan ⟨2, by decide⟩ j))⁻¹ := by
  simp only [gammaP, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    sl2At_HSL, CFSG.HardMathSupport.Lang.D4Three.coe_d4Graph, pow_one]
  change torusElt Tag.D4 K ⟨2, by decide⟩ t * _ * (torusElt Tag.D4 K ⟨2, by decide⟩ t)⁻¹ = _
  rw [torusElt_eq_rootDiagUnit]
  simp only [mul_assoc]

theorem tuple_ext4 {L : Type*} {a b : Fin d4.rank → L} (h0 : a 0 = b 0) (h1 : a 1 = b 1)
    (h2 : a 2 = b 2) (h3 : a 3 = b 3) : a = b := by
  funext i
  fin_cases i
  exacts [h0, h1, h2, h3]

theorem rootChar_tTuple {L : Type} [Field L] (d μ : Lˣ) (v : Fin d4.rank → ℤ) :
    rootChar (τ := d4) ![1, d, μ, d ^ 2] v = d ^ (v 1 + 2 * v 3) * μ ^ v 2 := by
  show ∏ i : Fin 4, (![1, d, μ, d ^ 2] : Fin 4 → Lˣ) i ^ v i =
    d ^ (v (1 : Fin 4) + 2 * v (3 : Fin 4)) * μ ^ v (2 : Fin 4)
  rw [Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, _root_.one_zpow, one_mul]
  rw [← _root_.zpow_natCast d 2, ← _root_.zpow_mul, mul_right_comm, ← _root_.zpow_add]
  norm_num

theorem tTuple_conj_xa {L : Type} [Field L] (d μ : Lˣ) {k : ℕ} (hk : k < 24) (u : L) :
    rootDiagUnit d4 ![1, d, μ, d ^ 2] * ((xa k u : adjointGroup d4 L) : ModGL d4 L) *
        (rootDiagUnit d4 ![1, d, μ, d ^ 2])⁻¹ =
      ((xa k (((d ^ (d4Root k 1 + 2 * d4Root k 3) * μ ^ d4Root k 2 : Lˣ) : L) * u) :
        adjointGroup d4 L) : ModGL d4 L) := by
  rw [← rootChar_tTuple]
  exact rootDiagUnit_conj_xPar_d4 _ (isRoot_d4Root hk) u

theorem xa_triple_congr {L : Type} [Field L] {i j k : ℕ} {a a' b b' c c' : L} (ha : a = a')
    (hb : b = b') (hc : c = c') : xa i a * xa j b * xa k c = xa i a' * xa j b' * xa k c' := by
  subst ha hb hc
  rfl

theorem conj_xa_triple {L : Type} [Field L] (T : ModGL d4 L) (i j k : ℕ) (a b c : L) :
    T * ((xa i a * xa j b * xa k c : adjointGroup d4 L) : ModGL d4 L) * T⁻¹ =
      (T * ((xa i a : adjointGroup d4 L) : ModGL d4 L) * T⁻¹) *
        (T * ((xa j b : adjointGroup d4 L) : ModGL d4 L) * T⁻¹) *
          (T * ((xa k c : adjointGroup d4 L) : ModGL d4 L) * T⁻¹) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  group

section TTuple

variable {L : Type} [Field L] {σ' : L →+* L} (hσ' : ∀ c, σ' (σ' (σ' c)) = c) {d μ : Lˣ}
  (hd3 : (d : L) ^ 3 = 1) (hσd : σ' (d : L) = d) (hσμ : σ' (μ : L) = (d : L) ^ 2 * μ)
  {c : L} (hσc : σ' c = c)

include hd3 hσc in
theorem tTuple_conj_P1 :
    rootDiagUnit d4 ![1, d, μ, d ^ 2] *
        ((xa 0 c * xa 1 ((d : L) ^ 2 * c) * xa 3 ((d : L) * c) : adjointGroup d4 L) :
          ModGL d4 L) * (rootDiagUnit d4 ![1, d, μ, d ^ 2])⁻¹ =
      ((fP1 σ' hσ' c : adjointGroup d4 L) : ModGL d4 L) := by
  rw [conj_xa_triple, tTuple_conj_xa d μ (by norm_num), tTuple_conj_xa d μ (by norm_num),
    tTuple_conj_xa d μ (by norm_num), ← Subgroup.coe_mul, ← Subgroup.coe_mul, fP1_eq]
  congr 1
  have e0 : d4Root 0 1 + 2 * d4Root 0 3 = 0 ∧ d4Root 0 2 = 0 := by decide
  have e1 : d4Root 1 1 + 2 * d4Root 1 3 = 1 ∧ d4Root 1 2 = 0 := by decide
  have e3 : d4Root 3 1 + 2 * d4Root 3 3 = 2 ∧ d4Root 3 2 = 0 := by decide
  refine xa_triple_congr ?_ ?_ ?_
  · rw [e0.1, e0.2]; simp
  · rw [e1.1, e1.2, hσc]
    simp only [_root_.zpow_one, _root_.zpow_zero, mul_one]
    linear_combination c * hd3
  · rw [e3.1, e3.2, hσc, hσc]
    simp only [_root_.zpow_zero, mul_one, Units.val_zpow_eq_zpow_val]
    norm_num
    linear_combination c * hd3

include hσc in
theorem tTuple_conj_M1 :
    rootDiagUnit d4 ![1, d, μ, d ^ 2] *
        ((xa 4 c * xa 6 ((d : L) * c) * xa 10 ((d : L) ^ 2 * c) : adjointGroup d4 L) :
          ModGL d4 L) * (rootDiagUnit d4 ![1, d, μ, d ^ 2])⁻¹ =
      ((fM1 σ' hσ' c : adjointGroup d4 L) : ModGL d4 L) := by
  rw [conj_xa_triple, tTuple_conj_xa d μ (by norm_num), tTuple_conj_xa d μ (by norm_num),
    tTuple_conj_xa d μ (by norm_num), ← Subgroup.coe_mul, ← Subgroup.coe_mul, fM1_eq]
  congr 1
  have e4 : d4Root 4 1 + 2 * d4Root 4 3 = 0 ∧ d4Root 4 2 = 0 := by decide
  have e6 : d4Root 6 1 + 2 * d4Root 6 3 = -1 ∧ d4Root 6 2 = 0 := by decide
  have e10 : d4Root 10 1 + 2 * d4Root 10 3 = -2 ∧ d4Root 10 2 = 0 := by decide
  have hd0 : (d : L) ≠ 0 := Units.ne_zero d
  refine xa_triple_congr ?_ ?_ ?_
  · rw [e4.1, e4.2]; simp
  · rw [e6.1, e6.2]
    simp only [hσc, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
      Units.val_pow_eq_pow_val, pow_one, _root_.zpow_zero, mul_one,
      _root_.zpow_neg, _root_.zpow_one]
    field_simp
  · rw [e10.1, e10.2]
    simp only [hσc, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
      Units.val_pow_eq_pow_val, pow_one, _root_.zpow_zero, mul_one,
      _root_.zpow_neg, zpow_ofNat]
    field_simp

include hσc hσμ hσd in
theorem tTuple_conj_P2 :
    rootDiagUnit d4 ![1, d, μ, d ^ 2] *
        ((xa 5 c * xa 7 ((d : L) * c) * xa 9 (-((d : L) ^ 2 * c)) : adjointGroup d4 L) :
          ModGL d4 L) * (rootDiagUnit d4 ![1, d, μ, d ^ 2])⁻¹ =
      ((fP2 σ' hσ' μ c : adjointGroup d4 L) : ModGL d4 L) := by
  rw [conj_xa_triple, tTuple_conj_xa d μ (by norm_num), tTuple_conj_xa d μ (by norm_num),
    tTuple_conj_xa d μ (by norm_num), ← Subgroup.coe_mul, ← Subgroup.coe_mul, fP2_eq]
  congr 1
  have e5 : d4Root 5 1 + 2 * d4Root 5 3 = 0 ∧ d4Root 5 2 = 1 := by decide
  have e7 : d4Root 7 1 + 2 * d4Root 7 3 = 1 ∧ d4Root 7 2 = 1 := by decide
  have e9 : d4Root 9 1 + 2 * d4Root 9 3 = 2 ∧ d4Root 9 2 = 1 := by decide
  refine xa_triple_congr ?_ ?_ ?_
  · rw [e5.1, e5.2]; simp
  · rw [e7.1, e7.2]
    simp only [map_mul, hσc, hσμ, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.val_pow_eq_pow_val, pow_one, _root_.zpow_one]
    ring
  · rw [e9.1, e9.2]
    simp only [map_mul, map_pow, hσc, hσμ, hσd, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.val_pow_eq_pow_val, pow_one,
      _root_.zpow_one, zpow_ofNat]
    ring

include hd3 hσc hσμ hσd in
theorem tTuple_conj_M2 :
    rootDiagUnit d4 ![1, d, μ, d ^ 2] *
        ((xa 11 c * xa 14 ((d : L) ^ 2 * c) * xa 16 (-((d : L) * c)) : adjointGroup d4 L) :
          ModGL d4 L) * (rootDiagUnit d4 ![1, d, μ, d ^ 2])⁻¹ =
      ((fM2 σ' hσ' μ c : adjointGroup d4 L) : ModGL d4 L) := by
  rw [conj_xa_triple, tTuple_conj_xa d μ (by norm_num), tTuple_conj_xa d μ (by norm_num),
    tTuple_conj_xa d μ (by norm_num), ← Subgroup.coe_mul, ← Subgroup.coe_mul, fM2_eq]
  congr 1
  have e11 : d4Root 11 1 + 2 * d4Root 11 3 = 0 ∧ d4Root 11 2 = -1 := by decide
  have e14 : d4Root 14 1 + 2 * d4Root 14 3 = -1 ∧ d4Root 14 2 = -1 := by decide
  have e16 : d4Root 16 1 + 2 * d4Root 16 3 = -2 ∧ d4Root 16 2 = -1 := by decide
  have hd0 : (d : L) ≠ 0 := Units.ne_zero d
  have hμ0 : (μ : L) ≠ 0 := Units.ne_zero μ
  refine xa_triple_congr ?_ ?_ ?_
  · rw [e11.1, e11.2]; simp
  · rw [e14.1, e14.2]
    simp only [map_mul, map_inv₀, map_pow, hσc, hσμ, hσd, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, pow_one, _root_.zpow_neg,
      _root_.zpow_one, zpow_ofNat]
    field_simp
    linear_combination c * hd3
  · rw [e16.1, e16.2]
    simp only [map_mul, map_inv₀, map_pow, map_neg, hσc, hσμ, hσd, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, pow_one,
      _root_.zpow_neg, _root_.zpow_one,
      zpow_ofNat]
    field_simp
    linear_combination (-c) * hd3

include hd3 hσc hσμ hσd in
theorem tTuple_conj_P3 :
    rootDiagUnit d4 ![1, d, μ, d ^ 2] *
        ((xa 15 (-c) * xa 13 (-c) * xa 12 (-c) : adjointGroup d4 L) : ModGL d4 L) *
          (rootDiagUnit d4 ![1, d, μ, d ^ 2])⁻¹ =
      ((fP3 σ' hσ' μ c : adjointGroup d4 L) : ModGL d4 L) := by
  rw [conj_xa_triple, tTuple_conj_xa d μ (by norm_num), tTuple_conj_xa d μ (by norm_num),
    tTuple_conj_xa d μ (by norm_num), ← Subgroup.coe_mul, ← Subgroup.coe_mul, fP3_eq]
  congr 1
  have e15 : d4Root 15 1 + 2 * d4Root 15 3 = 3 ∧ d4Root 15 2 = 1 := by decide
  have e13 : d4Root 13 1 + 2 * d4Root 13 3 = 2 ∧ d4Root 13 2 = 1 := by decide
  have e12 : d4Root 12 1 + 2 * d4Root 12 3 = 1 ∧ d4Root 12 2 = 1 := by decide
  refine xa_triple_congr ?_ ?_ ?_
  · rw [e15.1, e15.2]
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, pow_one,
      _root_.zpow_one, zpow_ofNat]
    linear_combination (-(μ : L) * c) * hd3
  · rw [e13.1, e13.2]
    simp only [map_mul, hσc, hσμ, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.val_pow_eq_pow_val, pow_one, _root_.zpow_one,
      zpow_ofNat]
    ring
  · rw [e12.1, e12.2]
    simp only [map_mul, map_pow, hσc, hσμ, hσd, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.val_pow_eq_pow_val, pow_one,
      _root_.zpow_one, zpow_ofNat]
    linear_combination ((d : L) * μ * c) * hd3

include hd3 hσc hσμ hσd in
theorem tTuple_conj_M3 :
    rootDiagUnit d4 ![1, d, μ, d ^ 2] *
        ((xa 20 (-c) * xa 18 (-c) * xa 17 (-c) : adjointGroup d4 L) : ModGL d4 L) *
          (rootDiagUnit d4 ![1, d, μ, d ^ 2])⁻¹ =
      ((fM3 σ' hσ' μ c : adjointGroup d4 L) : ModGL d4 L) := by
  rw [conj_xa_triple, tTuple_conj_xa d μ (by norm_num), tTuple_conj_xa d μ (by norm_num),
    tTuple_conj_xa d μ (by norm_num), ← Subgroup.coe_mul, ← Subgroup.coe_mul, fM3_eq]
  congr 1
  have e20 : d4Root 20 1 + 2 * d4Root 20 3 = -3 ∧ d4Root 20 2 = -1 := by decide
  have e18 : d4Root 18 1 + 2 * d4Root 18 3 = -2 ∧ d4Root 18 2 = -1 := by decide
  have e17 : d4Root 17 1 + 2 * d4Root 17 3 = -1 ∧ d4Root 17 2 = -1 := by decide
  have hd0 : (d : L) ≠ 0 := Units.ne_zero d
  have hμ0 : (μ : L) ≠ 0 := Units.ne_zero μ
  refine xa_triple_congr ?_ ?_ ?_
  · rw [e20.1, e20.2]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
      Units.val_pow_eq_pow_val, pow_one,
      _root_.zpow_neg, _root_.zpow_one, zpow_ofNat]
    field_simp
    linear_combination c * hd3
  · rw [e18.1, e18.2]
    simp only [map_mul, map_inv₀, hσc, hσμ, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, pow_one, _root_.zpow_neg,
      _root_.zpow_one, zpow_ofNat]
    field_simp
  · rw [e17.1, e17.2]
    simp only [map_mul, map_inv₀, map_pow, hσc, hσμ, hσd, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, pow_one, _root_.zpow_neg,
      _root_.zpow_one, zpow_ofNat]
    field_simp
    linear_combination (-c) * hd3

end TTuple

theorem baseChangeGL_xa_triple {L L' : Type} [Field L] [Field L'] (f : L →+* L') {i j k : ℕ}
    (hi : i < 24) (hj : j < 24) (hk : k < 24) (a b c : L) :
    baseChangeGL (τ := d4) f ((xa i a * xa j b * xa k c : adjointGroup d4 L) : ModGL d4 L) =
      ((xa i (f a) * xa j (f b) * xa k (f c) : adjointGroup d4 L') : ModGL d4 L') := by
  have h1 : ∀ {n : ℕ} (hn : n < 24) (u : L), baseChangeGL (τ := d4) f
      ((xa n u : adjointGroup d4 L) : ModGL d4 L) = ((xa n (f u) : adjointGroup d4 L') :
        ModGL d4 L') := by
    intro n hn u
    rw [coe_xPar_d4_eq_pinnedX (isRoot_d4Root hn), coe_xPar_d4_eq_pinnedX (isRoot_d4Root hn),
      baseChangeGL_pinnedX, map_mul, map_intCast]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, h1 hi, h1 hj, h1 hk,
    Subgroup.coe_mul, Subgroup.coe_mul]

theorem exists_gammaP_HSL_frameHom {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hp2 : p ≠ 2) (hq : p ^ f % 3 = 1)
    {t : Kˣ} (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) :
    ∃ Ψ : GL (Fin 3) K →* ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup (gammaP K (HSL t))),
      Function.Surjective Ψ ∧
      Ψ.ker = (Matrix.ProjGenLinGroup.mk : GL (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K).ker ∧
      (∀ c : K, ((Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 1 by decide) c)) : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
        ((xa 0 c * xa 1 ((t : K) ^ 2 * c) * xa 3 ((t : K) * c) : adjointGroup d4 K) :
          ModGL d4 K)) ∧
      (∀ c : K, ((Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 3) ≠ 2 by decide) c)) : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
        ((xa 5 c * xa 7 ((t : K) * c) * xa 9 (-((t : K) ^ 2 * c)) : adjointGroup d4 K) :
          ModGL d4 K)) ∧
      (∀ c : K, ((Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 2 by decide) c)) : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
        ((xa 15 (-c) * xa 13 (-c) * xa 12 (-c) : adjointGroup d4 K) : ModGL d4 K)) ∧
      (∀ c : K, ((Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
          (show (1 : Fin 3) ≠ 0 by decide) c)) : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
        ((xa 4 c * xa 6 ((t : K) * c) * xa 10 ((t : K) ^ 2 * c) : adjointGroup d4 K) :
          ModGL d4 K)) ∧
      (∀ c : K, ((Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 1 by decide) c)) : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
        ((xa 11 c * xa 14 ((t : K) ^ 2 * c) * xa 16 (-((t : K) * c)) : adjointGroup d4 K) :
          ModGL d4 K)) ∧
      (∀ c : K, ((Ψ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
          (show (2 : Fin 3) ≠ 0 by decide) c)) : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
        ((xa 20 (-c) * xa 18 (-c) * xa 17 (-c) : adjointGroup d4 K) : ModGL d4 K)) ∧
      (∀ a : Kˣ, ((Ψ (diagA a) : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
        rootDiagUnit Tag.D4 ![a, a, a⁻¹, a]) := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨K₃, _, _, _, _, hK₃, Fr, hFr⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.graphType_exists_ext hf K hK
  have : Fintype K₃ := Fintype.ofFinite K₃
  set ι : K →+* K₃ := algebraMap K K₃ with hι
  have hFrι : ∀ c : K, Fr (ι c) = ι c :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.graphType_frobenius_algebraMap
      hK Fr hFr
  have hFrcomp : Fr.toRingHom.comp ι = ι := RingHom.ext hFrι
  set d : K₃ˣ := Units.map ι.toMonoidHom t with hd
  have hdFr : Units.map Fr.toRingHom.toMonoidHom d = d := Units.ext (hFrι t)
  have hd3 : d ^ 3 = 1 := by rw [hd, ← map_pow, ht3, map_one]
  have hd1 : d ≠ 1 := by
    intro h
    apply ht1
    apply Units.ext
    apply ι.injective
    have h' := congrArg Units.val h
    simpa [hd] using h'
  have hodd : ringChar K₃ ≠ 2 := by rw [ringChar.eq K₃ p]; exact hp2
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have hA : A2Std Fr d (p ^ f) := ⟨hq2, hK₃, hFr, hq, hodd, hdFr, hd3, hd1⟩
  have hc := hA.toCore
  have hFr3 : ∀ c, Fr (Fr (Fr c)) = c := fun c => by
    rw [hFr, hFr, hFr, ← pow_mul, ← pow_mul, show p ^ f * (p ^ f * p ^ f) = (p ^ f) ^ 3 by ring,
      ← hK₃, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have : CharP (AlgebraicClosure K₃) p :=
    charP_of_injective_algebraMap (algebraMap K₃ (AlgebraicClosure K₃)).injective p
  have htw : CFSG.Blueprint.twistedFixedGroup TwistTag.D4 K₃ Fr.toRingHom =
      graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom :=
    (triality_both_field_orientations_simple_full_ambient_fixed_group p f hp hf K₃ hK₃
      (AlgebraicClosure K₃) 1 (Or.inl rfl) Fr.toRingHom (fun c => by simpa using hFr c)
      (iterateFrobenius (AlgebraicClosure K₃) p f)
      (fun c => iterateFrobenius_def p f c)).2.2.1
  have hYle : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom ≤ adjointGroup TwistTag.D4.tag K₃ :=
    (graphFixedRootGroup_le TwistTag.D4 K₃ Fr.toRingHom).trans inf_le_left
  obtain ⟨gs, hgs, hgsc⟩ := A2Core.a2_torus_mem hc (a := 1) (b := d) (map_one _) hdFr
  have hsY : a2S d ∈ graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom := by
    have h1 : (gs : ModGL TwistTag.D4.tag K₃) = a2S d := hgsc
    rw [← h1, ← hc.twisted_eq]
    exact ⟨gs, (iSup_le fun i => hHatE_le_twistedGroup hc.cube_apply i) hgs, rfl⟩
  let sY : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom := ⟨a2S d, hsY⟩
  let φ : MulAut (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) :=
    MulAut.conj sY * fieldActor Fr Fr
  have hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K₃) = a2Conj Fr d (y : ModGL TwistTag.D4.tag K₃) := by
    intro y
    show ((sY * fieldActor Fr Fr y * sY⁻¹ : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) :
      ModGL TwistTag.D4.tag K₃) = _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_fieldActor]
    rfl
  obtain ⟨μ, hμ, ΨF, hΨFs, hΨFk, hF1, hF2, hF3, hF4, hF5, hF6, hFD⟩ :=
    exists_fixSub_frameHom hA hp hf rfl φ hφ

  have hFrμ : Units.map Fr.toRingHom.toMonoidHom μ = d⁻¹ * μ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    show Fr (μ : K₃) = _
    rw [eq_inv_mul_iff_mul_eq₀ (Units.ne_zero d)]
    exact hμ
  set S3 : Fin d4.rank → K₃ˣ := ![1, 1, d, 1] with hS3
  have hs3 : a2S d = rootDiagUnit d4 S3 := rfl
  have hdinv : d⁻¹ = d ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hd3])
  set Tt : Fin d4.rank → K₃ˣ := ![1, d, μ, d ^ 2] with hTt
  set T : ModGL TwistTag.D4.tag K₃ := rootDiagUnit d4 Tt with hT
  set Ht : Fin d4.rank → K₃ˣ := fun j => d ^ Tag.D4.cartan ⟨2, by decide⟩ j with hHt
  set H : ModGL TwistTag.D4.tag K₃ := rootDiagUnit d4 Ht with hH
  set P : ModGL TwistTag.D4.tag K₃ := diagramMap TwistTag.D4 K₃ with hP
  have hσT : Units.map (entrywiseHom Fr.toRingHom) T = (a2S d)⁻¹ * T := by
    rw [hT, entrywise_rootDiagUnit, hs3, rootDiagUnit_inv', rootDiagUnit_mul_rootDiagUnit]
    congr 1
    refine tuple_ext4 ?_ ?_ ?_ ?_
    · show Units.map Fr.toRingHom.toMonoidHom 1 = (1 : K₃ˣ)⁻¹ * 1
      simp
    · show Units.map Fr.toRingHom.toMonoidHom d = (1 : K₃ˣ)⁻¹ * d
      rw [hdFr, inv_one, one_mul]
    · show Units.map Fr.toRingHom.toMonoidHom μ = d⁻¹ * μ
      exact hFrμ
    · show Units.map Fr.toRingHom.toMonoidHom (d ^ 2) = (1 : K₃ˣ)⁻¹ * d ^ 2
      rw [map_pow, hdFr, inv_one, one_mul]
  have hRT : P * ((a2S d)⁻¹ * T) * P⁻¹ = T * H := by
    rw [hs3, rootDiagUnit_inv', hT, rootDiagUnit_mul_rootDiagUnit, hP, diagramMap_conj_rootDiagUnit,
      hH, rootDiagUnit_mul_rootDiagUnit]
    congr 1
    have e0 : TwistTag.D4.perm.symm 0 = 3 := by decide
    have e1 : TwistTag.D4.perm.symm 1 = 0 := by decide
    have e2 : TwistTag.D4.perm.symm 2 = 2 := by decide
    have e3 : TwistTag.D4.perm.symm 3 = 1 := by decide
    have c0 : Tag.D4.cartan ⟨2, by decide⟩ 0 = -1 := by decide
    have c1 : Tag.D4.cartan ⟨2, by decide⟩ 1 = -1 := by decide
    have c2 : Tag.D4.cartan ⟨2, by decide⟩ 2 = 2 := by decide
    have c3 : Tag.D4.cartan ⟨2, by decide⟩ 3 = -1 := by decide
    refine tuple_ext4 ?_ ?_ ?_ ?_
    · show (S3⁻¹ * Tt) (TwistTag.D4.perm.symm 0) = Tt 0 * Ht 0
      rw [e0]
      show (1 : K₃ˣ)⁻¹ * d ^ 2 = 1 * d ^ Tag.D4.cartan ⟨2, by decide⟩ 0
      rw [c0, _root_.zpow_neg_one, hdinv, inv_one, one_mul]
    · show (S3⁻¹ * Tt) (TwistTag.D4.perm.symm 1) = Tt 1 * Ht 1
      rw [e1]
      show (1 : K₃ˣ)⁻¹ * 1 = d * d ^ Tag.D4.cartan ⟨2, by decide⟩ 1
      rw [c1, _root_.zpow_neg_one, mul_inv_cancel, inv_one, one_mul]
    · show (S3⁻¹ * Tt) (TwistTag.D4.perm.symm 2) = Tt 2 * Ht 2
      rw [e2]
      show d⁻¹ * μ = μ * d ^ Tag.D4.cartan ⟨2, by decide⟩ 2
      rw [c2, hdinv, mul_comm]
      rfl
    · show (S3⁻¹ * Tt) (TwistTag.D4.perm.symm 3) = Tt 3 * Ht 3
      rw [e3]
      show (1 : K₃ˣ)⁻¹ * d = d ^ 2 * d ^ Tag.D4.cartan ⟨2, by decide⟩ 3
      rw [c3, _root_.zpow_neg_one, inv_one, one_mul, pow_two, mul_inv_cancel_right]
  let ιG : ModGL Tag.D4 K →* ModGL TwistTag.D4.tag K₃ := baseChangeGL (τ := TwistTag.D4.tag) ι
  have hσι : ∀ w : ModGL Tag.D4 K,
      Units.map (entrywiseHom Fr.toRingHom) (ιG w) = ιG w := fun w => by
    show Units.map (entrywiseHom Fr.toRingHom) (baseChangeGL ι w) = baseChangeGL ι w
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hFrcomp]
  have hιP : ιG (CFSG.HardMathSupport.Lang.D4Three.d4P K) = P :=
    baseChangeGL_diagramMap ι TwistTag.D4
  have hιH : ιG (rootDiagUnit Tag.D4 (fun j => t ^ Tag.D4.cartan ⟨2, by decide⟩ j)) = H := by
    show baseChangeGL ι (rootDiagUnit d4 (fun j => t ^ Tag.D4.cartan ⟨2, by decide⟩ j)) = H
    rw [baseChangeGL_rootDiagUnit, hH, hHt]
    congr 1
    funext j
    rw [map_zpow]
  have hfixrel : ∀ u : adjointGroup Tag.D4 K, gammaP K (HSL t) u = u →
      P * ιG (u : ModGL Tag.D4 K) * P⁻¹ = H⁻¹ * ιG (u : ModGL Tag.D4 K) * H := by
    intro u hu
    have h1 := congrArg (fun x : adjointGroup Tag.D4 K => ιG (x : ModGL Tag.D4 K)) hu
    rw [coe_gammaP_HSL, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hιP, hιH] at h1
    calc P * ιG (u : ModGL Tag.D4 K) * P⁻¹ =
        H⁻¹ * (H * P * ιG (u : ModGL Tag.D4 K) * P⁻¹ * H⁻¹) * H := by group
      _ = H⁻¹ * ιG (u : ModGL Tag.D4 K) * H := by rw [h1]
  have hfixrel' : ∀ u : adjointGroup Tag.D4 K,
      P * ιG (u : ModGL Tag.D4 K) * P⁻¹ = H⁻¹ * ιG (u : ModGL Tag.D4 K) * H →
        gammaP K (HSL t) u = u := by
    intro u hu
    apply Subtype.ext
    apply (show Function.Injective ιG from baseChangeGL_injective (τ := TwistTag.D4.tag) ι)
    rw [coe_gammaP_HSL, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hιP, hιH]
    calc H * P * ιG (u : ModGL Tag.D4 K) * P⁻¹ * H⁻¹ =
        H * (P * ιG (u : ModGL Tag.D4 K) * P⁻¹) * H⁻¹ := by group
      _ = ιG (u : ModGL Tag.D4 K) := by rw [hu]; group
  have hΘY : ∀ u : ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup (gammaP K (HSL t))),
      T * ιG ((u : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) * T⁻¹ ∈
        graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom := by
    intro u
    rw [← htw, mem_twistedFixedGroup_iff_twistHom]
    refine ⟨conj_rootDiagUnit_mem_adjointGroup Tt
      (baseChangeGL_mem_adjointGroup ι u.1.2), ?_⟩
    rw [twistHom_apply, map_mul, map_mul, map_inv, hσT, hσι, ← hP]
    have hrel := hfixrel _ u.2
    calc P * ((a2S d)⁻¹ * T * ιG ((u : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) *
          ((a2S d)⁻¹ * T)⁻¹) * P⁻¹ =
        (P * ((a2S d)⁻¹ * T) * P⁻¹) *
          (P * ιG ((u : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) * P⁻¹) *
            (P * ((a2S d)⁻¹ * T) * P⁻¹)⁻¹ := by group
      _ = (T * H) * (H⁻¹ * ιG ((u : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) * H) *
            (T * H)⁻¹ := by rw [hRT, hrel]
      _ = T * ιG ((u : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) * T⁻¹ := by group
  have hΘφ : ∀ u : ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup (gammaP K (HSL t))),
      φ ⟨_, hΘY u⟩ = ⟨_, hΘY u⟩ := by
    intro u
    apply Subtype.ext
    rw [hφ]
    show a2S d * Units.map (entrywiseHom Fr.toRingHom)
      (T * ιG ((u : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) * T⁻¹) * (a2S d)⁻¹ = _
    rw [map_mul, map_mul, map_inv, hσT, hσι]
    group
  let Θ : ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup (gammaP K (HSL t))) →*
      ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ) :=
    { toFun := fun u => ⟨⟨_, hΘY u⟩, hΘφ u⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        show T * ιG (1 : ModGL Tag.D4 K) * T⁻¹ = 1
        rw [map_one, mul_one, mul_inv_cancel]
      map_mul' := fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        show T * ιG (((a : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) *
            ((b : adjointGroup Tag.D4 K) : ModGL Tag.D4 K)) * T⁻¹ =
          (T * ιG ((a : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) * T⁻¹) *
            (T * ιG ((b : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) * T⁻¹)
        rw [map_mul]
        group }
  have hΘinj : Function.Injective Θ := by
    intro a b hab
    have h1 := congrArg (fun y : ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ) =>
      ((y : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) : ModGL TwistTag.D4.tag K₃)) hab
    change T * ιG ((a : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) * T⁻¹ =
      T * ιG ((b : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) * T⁻¹ at h1
    have h2 := (show Function.Injective ιG from baseChangeGL_injective (τ := TwistTag.D4.tag) ι)
      (mul_left_cancel (mul_right_cancel h1))
    exact Subtype.ext (Subtype.ext h2)
  have hΘsurj : Function.Surjective Θ := by
    rintro ⟨⟨y, hyY⟩, hyφ⟩
    have hyφ' : a2Conj Fr d y = y := by
      have h1 := congrArg Subtype.val (show φ ⟨y, hyY⟩ = ⟨y, hyY⟩ from hyφ)
      rw [hφ] at h1
      exact h1
    have hσy : Units.map (entrywiseHom Fr.toRingHom) y = (a2S d)⁻¹ * y * a2S d := by
      have h1 : a2S d * Units.map (entrywiseHom Fr.toRingHom) y * (a2S d)⁻¹ = y := hyφ'
      calc Units.map (entrywiseHom Fr.toRingHom) y =
          (a2S d)⁻¹ * (a2S d * Units.map (entrywiseHom Fr.toRingHom) y * (a2S d)⁻¹) * a2S d := by
            group
        _ = (a2S d)⁻¹ * y * a2S d := by rw [h1]
    set y' := T⁻¹ * y * T with hy'
    have hy'adj : y' ∈ adjointGroup TwistTag.D4.tag K₃ := by
      have h1 := conj_rootDiagUnit_mem_adjointGroup Tt⁻¹ (hYle hyY)
      rw [← rootDiagUnit_inv', inv_inv] at h1
      exact h1
    have hy'σ : Units.map (entrywiseHom Fr.toRingHom) y' = y' := by
      rw [hy', map_mul, map_mul, map_inv, hσT, hσy]
      group
    have hy'mem : y' ∈ entrywiseFixedGroup TwistTag.D4.tag Fr := ⟨hy'adj, hy'σ⟩
    rw [entrywiseFixedGroup_D4_eq_fixedFieldImage_of_cube Fr hFr3] at hy'mem
    obtain ⟨v, hv, hvy⟩ := hy'mem
    let e := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.graphTypeFixedEquiv hf
      hK hK₃ Fr hFr
    have hecomp : ι.comp e.symm.toRingHom = (fixSubfield Fr).subtype := RingHom.ext fun z => by
      have h1 :=
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.graphTypeFixedEquiv_apply
        hf hK hK₃ Fr hFr (e.symm z)
      rw [RingEquiv.apply_symm_apply] at h1
      exact h1.symm
    have huad : baseChangeGL e.symm.toRingHom v ∈ adjointGroup Tag.D4 K :=
      baseChangeGL_mem_adjointGroup _ hv
    let u₀ : adjointGroup Tag.D4 K := ⟨baseChangeGL e.symm.toRingHom v, huad⟩
    have hιu : ιG (u₀ : ModGL Tag.D4 K) = y' := by
      change baseChangeGL (τ := TwistTag.D4.tag) ι (baseChangeGL e.symm.toRingHom v) = y'
      rw [baseChangeGL_baseChangeGL, hecomp]
      exact hvy
    have hyfix : P * Units.map (entrywiseHom Fr.toRingHom) y * P⁻¹ = y := by
      have hyT : y ∈ CFSG.Blueprint.twistedFixedGroup TwistTag.D4 K₃ Fr.toRingHom := by
        rw [htw]
        exact hyY
      have h1 := ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K₃ Fr.toRingHom).1 hyT).2
      rw [twistHom_apply] at h1
      exact h1
    have hyT : y = T * y' * T⁻¹ := by
      rw [hy']
      group
    have hu₀fix : gammaP K (HSL t) u₀ = u₀ := by
      refine hfixrel' u₀ ?_
      rw [hιu]
      have h1 : Units.map (entrywiseHom Fr.toRingHom) y =
          ((a2S d)⁻¹ * T) * y' * ((a2S d)⁻¹ * T)⁻¹ := by
        rw [hyT, map_mul, map_mul, map_inv, hσT, hy'σ]
      rw [h1] at hyfix
      have h2 : (T * H) * (P * y' * P⁻¹) * (T * H)⁻¹ = T * y' * T⁻¹ := by
        rw [← hRT, ← hyT]
        calc P * ((a2S d)⁻¹ * T) * P⁻¹ * (P * y' * P⁻¹) * (P * ((a2S d)⁻¹ * T) * P⁻¹)⁻¹ =
            P * ((a2S d)⁻¹ * T * y' * ((a2S d)⁻¹ * T)⁻¹) * P⁻¹ := by group
          _ = y := hyfix
      calc P * y' * P⁻¹ = H⁻¹ * (T⁻¹ * ((T * H) * (P * y' * P⁻¹) * (T * H)⁻¹) * T) * H := by
            group
        _ = H⁻¹ * y' * H := by rw [h2]; group
    refine ⟨⟨u₀, hu₀fix⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change T * ιG (u₀ : ModGL Tag.D4 K) * T⁻¹ = y
    rw [hιu, hyT]
  let eΘ := MulEquiv.ofBijective Θ ⟨hΘinj, hΘsurj⟩
  let eF : K ≃+* fixedField Fr.toRingHom :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.graphTypeFixedEquiv hf hK hK₃
      Fr hFr
  have heF : ∀ c : K, ((eF c : fixedField Fr.toRingHom) : K₃) = ι c := fun c => rfl
  let GLe : GL (Fin 3) K →* GL (Fin 3) (fixedField Fr.toRingHom) :=
    Matrix.GeneralLinearGroup.map eF.toRingHom
  have hGLtr : ∀ {i j : Fin 3} (hij : i ≠ j) (c : K),
      GLe (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c)) =
        Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij (eF c)) := by
    intro i j hij c
    apply Units.ext
    show eF.toRingHom.mapMatrix (1 + Matrix.single i j c) = 1 + Matrix.single i j (eF c)
    rw [map_add, map_one, RingHom.mapMatrix_apply, Matrix.map_single]
    rfl
  have hGLD : ∀ a : Kˣ, GLe (diagA a) = diagA (Units.map eF.toRingHom.toMonoidHom a) := by
    intro a
    apply Units.ext
    show eF.toRingHom.mapMatrix (diagonal ![(a : K), 1, 1]) =
      diagonal ![((Units.map eF.toRingHom.toMonoidHom a : (fixedField Fr.toRingHom)ˣ) :
        fixedField Fr.toRingHom), 1, 1]
    rw [RingHom.mapMatrix_apply, diagonal_map (map_zero _)]
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact map_one _
    · exact map_one _
  have hGLinj : Function.Injective GLe := fun g g' h => Units.ext (by
    ext i j
    have h1 := congrArg (fun x : GL (Fin 3) (fixedField Fr.toRingHom) =>
      (x : Matrix (Fin 3) (Fin 3) (fixedField Fr.toRingHom)) i j) h
    exact eF.injective h1)
  have hGLsurj : Function.Surjective GLe := fun g =>
    ⟨Matrix.GeneralLinearGroup.map eF.symm.toRingHom g, Units.ext (Matrix.ext fun i j =>
      eF.apply_symm_apply _)⟩
  let Ψ : GL (Fin 3) K →* ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup (gammaP K (HSL t))) :=
    eΘ.symm.toMonoidHom.comp (ΨF.comp GLe)
  have hΨs : Function.Surjective Ψ := eΘ.symm.surjective.comp (hΨFs.comp hGLsurj)
  have hΨk : Ψ.ker =
      (Matrix.ProjGenLinGroup.mk : GL (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K).ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Matrix.ProjGenLinGroup.mk_eq_one]
    change eΘ.symm (ΨF (GLe g)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hΨFk, MonoidHom.mem_ker,
      Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar,
      Matrix.GeneralLinearGroup.center_eq_range_scalar]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨Units.map eF.symm.toRingHom.toMonoidHom w, hGLinj ?_⟩
      rw [← hw]
      show Matrix.GeneralLinearGroup.map eF.toRingHom (Matrix.GeneralLinearGroup.scalar (Fin 3)
        (Units.map eF.symm.toRingHom.toMonoidHom w)) = _
      rw [Matrix.GeneralLinearGroup.map_scalar]
      congr 1
      apply Units.ext
      show eF (eF.symm _) = _
      rw [RingEquiv.apply_symm_apply]
    · rintro ⟨w, rfl⟩
      exact ⟨Units.map eF.toRingHom.toMonoidHom w, (Matrix.GeneralLinearGroup.map_scalar _ _).symm⟩
  have key : ∀ (g : GL (Fin 3) K) (u : ModGL Tag.D4 K),
      (((ΨF (GLe g) : ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ)) :
        graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) : ModGL TwistTag.D4.tag K₃) =
        T * ιG u * T⁻¹ →
      ((Ψ g : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) = u := by
    intro g u hgu
    have h1 : Θ (Ψ g) = ΨF (GLe g) := eΘ.apply_symm_apply (ΨF (GLe g))
    have h2 := congrArg (fun y : ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ) =>
      ((y : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) : ModGL TwistTag.D4.tag K₃)) h1
    change T * ιG ((Ψ g : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) * T⁻¹ = _ at h2
    rw [hgu] at h2
    exact (show Function.Injective ιG from baseChangeGL_injective (τ := TwistTag.D4.tag) ι)
      (mul_left_cancel (mul_right_cancel h2))
  have hd3' : (d : K₃) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hd3, Units.val_one]
  have hσd' : Fr.toRingHom (d : K₃) = d := hFrι t
  have hσμ' : Fr.toRingHom (μ : K₃) = (d : K₃) ^ 2 * μ := by
    show Fr (μ : K₃) = _
    linear_combination (d : K₃) ^ 2 * hμ - Fr (μ : K₃) * hd3'
  have hι2 : ∀ c : K, ι ((t : K) ^ 2 * c) = (d : K₃) ^ 2 * ι c := fun c => by
    rw [map_mul, map_pow]
    rfl
  have hι1 : ∀ c : K, ι ((t : K) * c) = (d : K₃) * ι c := fun c => by
    rw [map_mul]
    rfl
  have hιn : ∀ c : K, ι (-c) = -ι c := fun c => map_neg ι c
  refine ⟨Ψ, hΨs, hΨk, fun c => key _ _ ?_, fun c => key _ _ ?_, fun c => key _ _ ?_,
    fun c => key _ _ ?_, fun c => key _ _ ?_, fun c => key _ _ ?_, fun a => key _ _ ?_⟩
  · rw [hGLtr, hF1 (eF c), heF]
    show _ = T * baseChangeGL (τ := TwistTag.D4.tag) ι ((xa 0 c * xa 1 ((t : K) ^ 2 * c) *
      xa 3 ((t : K) * c) : adjointGroup d4 K) : ModGL d4 K) * T⁻¹
    rw [baseChangeGL_xa_triple ι (by norm_num) (by norm_num) (by norm_num), hι2, hι1]
    exact (tTuple_conj_P1 hc.cube_apply hd3' (hFrι c)).symm
  · rw [hGLtr, hF2 (eF c), heF]
    show _ = T * baseChangeGL (τ := TwistTag.D4.tag) ι ((xa 5 c * xa 7 ((t : K) * c) *
      xa 9 (-((t : K) ^ 2 * c)) : adjointGroup d4 K) : ModGL d4 K) * T⁻¹
    rw [baseChangeGL_xa_triple ι (by norm_num) (by norm_num) (by norm_num), hι1, map_neg, hι2]
    exact (tTuple_conj_P2 hc.cube_apply hσd' hσμ' (hFrι c)).symm
  · rw [hGLtr, hF3 (eF c), heF]
    show _ = T * baseChangeGL (τ := TwistTag.D4.tag) ι ((xa 15 (-c) * xa 13 (-c) *
      xa 12 (-c) : adjointGroup d4 K) : ModGL d4 K) * T⁻¹
    rw [baseChangeGL_xa_triple ι (by norm_num) (by norm_num) (by norm_num), hιn]
    exact (tTuple_conj_P3 hc.cube_apply hd3' hσd' hσμ' (hFrι c)).symm
  · rw [hGLtr, hF4 (eF c), heF]
    show _ = T * baseChangeGL (τ := TwistTag.D4.tag) ι ((xa 4 c * xa 6 ((t : K) * c) *
      xa 10 ((t : K) ^ 2 * c) : adjointGroup d4 K) : ModGL d4 K) * T⁻¹
    rw [baseChangeGL_xa_triple ι (by norm_num) (by norm_num) (by norm_num), hι1, hι2]
    exact (tTuple_conj_M1 hc.cube_apply (hFrι c)).symm
  · rw [hGLtr, hF5 (eF c), heF]
    show _ = T * baseChangeGL (τ := TwistTag.D4.tag) ι ((xa 11 c * xa 14 ((t : K) ^ 2 * c) *
      xa 16 (-((t : K) * c)) : adjointGroup d4 K) : ModGL d4 K) * T⁻¹
    rw [baseChangeGL_xa_triple ι (by norm_num) (by norm_num) (by norm_num), hι2, map_neg, hι1]
    exact (tTuple_conj_M2 hc.cube_apply hd3' hσd' hσμ' (hFrι c)).symm
  · rw [hGLtr, hF6 (eF c), heF]
    show _ = T * baseChangeGL (τ := TwistTag.D4.tag) ι ((xa 20 (-c) * xa 18 (-c) *
      xa 17 (-c) : adjointGroup d4 K) : ModGL d4 K) * T⁻¹
    rw [baseChangeGL_xa_triple ι (by norm_num) (by norm_num) (by norm_num), hιn]
    exact (tTuple_conj_M3 hc.cube_apply hd3' hσd' hσμ' (hFrι c)).symm
  · rw [hGLD, hFD]
    set S : Fin d4.rank → Kˣ := ![a, a, a⁻¹, a] with hS
    show _ = T * baseChangeGL (τ := TwistTag.D4.tag) ι (rootDiagUnit d4 S) * T⁻¹
    rw [baseChangeGL_rootDiagUnit, hT, rootDiagUnit_conj_rootDiagUnit]
    congr 1
    refine tuple_ext4 ?_ ?_ ?_ ?_ <;> exact Units.ext rfl

theorem isPGLPiThree_fixedSubgroup_gammaP_HSL {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hp2 : p ≠ 2) (hq : p ^ f % 3 = 1)
    {t : Kˣ} (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) :
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3.IsPGLPiThree
      ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup (gammaP K (HSL t))) (p ^ f) := by
  obtain ⟨Ψ, hΨ, hker, -⟩ := exists_gammaP_HSL_frameHom hf hK hp2 hq ht3 ht1
  exact ⟨true, p, f, K, inferInstance, ⟨Fact.out, hf, hK⟩, rfl, hq,
    nonempty_mulEquiv_projImage_of_surjective Ψ hΨ hker⟩

end Transfer

section Assembly

set_option linter.unusedSectionVars false

open CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.RankThree.PartOne.CTP CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3

theorem isPGLPiThree_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X') {q : ℕ}
    (h : IsPGLPiThree X' q) : IsPGLPiThree X q := by
  obtain ⟨π, p, f, F, _, hF, hpq, hmod, ⟨e'⟩⟩ := h
  exact ⟨π, p, f, F, inferInstance, hF, hpq, hmod, ⟨e.trans e'⟩⟩

theorem gammaP_conj {K : Type} [Field K] (P B : SL2 K) :
    gammaP K (P * B * P⁻¹) = MulAut.conj (sl2At K ⟨2, by decide⟩ P) * gammaP K B *
      (MulAut.conj (sl2At K ⟨2, by decide⟩ P))⁻¹ := by
  refine MulEquiv.ext fun u => ?_
  simp only [gammaP, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv,
    d4Graph_one_sl2Two]

theorem isPGLPiThree_fixedSubgroup_gammaP_of_mod_three_eq_one {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) (hq : Nat.card K % 3 = 1) {B : SL2 K} (hB3 : B ^ 3 = 1)
    (hB1 : B ≠ 1) : IsPGLPiThree ↥(fixedSubgroup (gammaP K B)) (Nat.card K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
  have h3 : 3 ∣ Nat.card K - 1 := by
    have := Nat.card_pos (α := K)
    omega
  obtain ⟨P, t, hPt⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.exists_conj_HSL_of_three h3 B
    ⟨1, by rw [pow_one]; exact hB3⟩
  have hHSL3 : HSL t ^ 3 = 1 := by
    rw [← hPt, conj_pow, hB3, mul_one, mul_inv_cancel]
  have ht3 : t ^ 3 = 1 := by
    have h1 := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) hHSL3
    have h2 : ∀ n : ℕ,
        ((HSL t ^ n : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 = ((t ^ n : Kˣ) : K) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ih]
        simp [HSL, pow_succ]
    simp only [h2] at h1
    exact Units.ext (by simpa using h1)
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hB1
    have h1 : HSL (1 : Kˣ) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [HSL]
    rw [h1] at hPt
    calc B = P⁻¹ * (P * B * P⁻¹) * P := by group
      _ = 1 := by rw [hPt]; group
  have hfix := isPGLPiThree_fixedSubgroup_gammaP_HSL (K := K) (p := ringChar K) (f := f) f.pos hK
    hK2 (by rw [← hK]; exact hq) ht3 ht1
  rw [← hK] at hfix
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3.nonempty_fixedSubgroup_conj_equiv
    (MulAut.conj (sl2At K ⟨2, by decide⟩ P)) (gammaP K B)
  rw [← gammaP_conj, hPt] at e
  exact isPGLPiThree_of_mulEquiv e hfix

@[expose] def D4GraphA2FixIsoMinus : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 2 → ringChar K ≠ 3 → 5 ≤ Nat.card K →
    Nat.card K % 3 = 2 → ∀ B : SL2 K, B ^ 3 = 1 → B ≠ 1 →
      IsPGLPiThree ↥(fixedSubgroup (gammaP K B)) (Nat.card K)

theorem card_mod_three_ne_zero {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3) :
    Nat.card K % 3 ≠ 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  intro h0
  rw [Nat.card_eq_fintype_card, hcard] at h0
  have h3 : 3 ∣ ringChar K := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (Nat.dvd_of_mod_eq_zero h0)
  exact hK3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3).symm

theorem d4GraphA2FixIsoOdd_of_minus (h : D4GraphA2FixIsoMinus) : D4GraphA2FixIsoOdd := by
  intro K _ _ hK2 hK3 hK5 B hB3 hB1
  have h0 := card_mod_three_ne_zero hK3
  have h12 : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 := by omega
  rcases h12 with h1 | h2
  · exact isPGLPiThree_fixedSubgroup_gammaP_of_mod_three_eq_one hK2 h1 hB3 hB1
  · exact h K hK2 hK3 hK5 h2 B hB3 hB1

@[expose] def D4GraphA2FixIsoMinusB0 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 2 → ringChar K ≠ 3 → 5 ≤ Nat.card K →
    Nat.card K % 3 = 2 →
      IsPGLPiThree ↥(fixedSubgroup (gammaP K
        (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.orderThreeSL K))) (Nat.card K)

theorem d4GraphA2FixIsoMinus_of_B0 (h : D4GraphA2FixIsoMinusB0) : D4GraphA2FixIsoMinus := by
  intro K _ _ hK2 hK3 hK5 hq B hB3 hB1
  have h3 : 3 ∣ Nat.card K + 1 := by omega
  obtain ⟨S, hS⟩ := CFSG.HardMathSupport.Seitz.Proving.exists_conj_eq_orderThreeSL h3 hB3 hB1
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3.nonempty_fixedSubgroup_conj_equiv
    (MulAut.conj (sl2At K ⟨2, by decide⟩ S)) (gammaP K B)
  rw [← gammaP_conj, hS] at e
  exact isPGLPiThree_of_mulEquiv e (h K hK2 hK3 hK5 hq)

theorem d4GraphA2FixIsoOdd_of_minusB0 (h : D4GraphA2FixIsoMinusB0) : D4GraphA2FixIsoOdd :=
  d4GraphA2FixIsoOdd_of_minus (d4GraphA2FixIsoMinus_of_B0 h)

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Odd

end
