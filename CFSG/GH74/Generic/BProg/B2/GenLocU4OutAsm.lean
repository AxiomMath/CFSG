module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutCls
import CFSG.GH74.Generic.BProg.B2.GenLocL4OutAbs
import CFSG.GH74.Generic.BProg.B2.GenLocU4OutFrExt
import CFSG.GH74.Generic.BProg.B2.GenLocU4OutFrDa
import CFSG.GH74.Generic.BProg.B2.GenLocU4OutFrSplit
import CFSG.GH74.Generic.BProg.B2.GenLocU4OutFrDb
public import CFSG.GH74.Generic.BProg.B2.GenLocL4ExtAux

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Assembly.LowTwoRank Matrix Subgroup
  CFSG.GH74.Generic.S1.Uni CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace GenLocU4OutAsm

open GenLocU4Basic GenLocU4Out GenLocU4OutCls GenLocU4ExtMu

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

@[expose] noncomputable def cj (h : UnitaryFieldData p f K) {U : Matrix (Fin 4) (Fin 4) K}
    (hU : IsUnitaryU (p ^ f) U) : MulAut ↥(StatedSU 4 (p ^ f) K) :=
  GenLocDiagU.conjSUHom h 4 ⟨unitaryGL U hU, GenLocU4OutE16.mem_pfu h hU⟩

theorem coe_cj (h : UnitaryFieldData p f K) {U : Matrix (Fin 4) (Fin 4) K} (hU : IsUnitaryU (p ^ f) U)
    (g : ↥(StatedSU 4 (p ^ f) K)) :
    (((cj h hU g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      U * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * cstar (p ^ f) U := by
  show (((unitaryGL U hU * (g : GL (Fin 4) K) * (unitaryGL U hU)⁻¹ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) = _
  rw [Units.val_mul, Units.val_mul]
  rfl

omit [Finite K] in
theorem fixIn_neg {q : ℕ} {N : Matrix (Fin 4) (Fin 4) K} {g : ↥(StatedSU 4 q K)} :
    FixIn (-N) g ↔ FixIn N g := by
  unfold FixIn
  rw [Matrix.neg_mul, Matrix.mul_neg, neg_inj]

omit [Finite K] in
theorem fixOut_neg {q : ℕ} {M : Matrix (Fin 4) (Fin 4) K} {g : ↥(StatedSU 4 q K)} :
    FixOut q (-M) g ↔ FixOut q M g := by
  unfold FixOut
  rw [Matrix.neg_mul, Matrix.mul_neg, neg_inj]

omit [Finite K] in
theorem map_cstar (h : UnitaryFieldData p f K) (U : Matrix (Fin 4) (Fin 4) K) :
    (cstar (p ^ f) U).map (· ^ (p ^ f)) = Uᵀ := by
  have hbar : (⇑h.bar : K → K) = fun c => c ^ (p ^ f) := bar_eq_pow h
  rw [← hbar]
  unfold cstar
  rw [← hbar, Matrix.transpose_map, map_bar_bar h]

omit [Finite K] in
theorem Pt_Pbar' (h : UnitaryFieldData p f K) {U : Matrix (Fin 4) (Fin 4) K} (hU : IsUnitaryU (p ^ f) U) :
    U.map (· ^ (p ^ f)) * Uᵀ = 1 := by
  have hbar : (⇑h.bar : K → K) = fun c => c ^ (p ^ f) := bar_eq_pow h
  have := GenLocU4OutE16.Pt_Pbar h ((GenLocU4OutFrame.isUnitaryU_iff_cT h U).1 hU)
  rw [← hbar]
  exact mul_eq_one_comm.mp this

@[expose] def GFrame (q : ℕ) (U : Matrix (Fin 4) (Fin 4) K) (φ : MulAut ↥(StatedSU 4 q K))
    (M : Matrix (Fin 4) (Fin 4) K) : Prop :=
  ∃ Bm : Matrix (Fin 4) (Fin 4) K, IsGraphAut q Bm φ ∧
    (Bm * U.map (· ^ q) = U * M ∨ Bm * U.map (· ^ q) = U * (-M))

@[expose] def IFrame (q : ℕ) (U : Matrix (Fin 4) (Fin 4) K) (φ : MulAut ↥(StatedSU 4 q K))
    (N : Matrix (Fin 4) (Fin 4) K) : Prop :=
  ∃ y : Matrix (Fin 4) (Fin 4) K, IsInnerAut q y φ ∧ (y * U = U * N ∨ y * U = U * (-N))

theorem GFrame.fix (h : UnitaryFieldData p f K) {U : Matrix (Fin 4) (Fin 4) K} (hU : IsUnitaryU (p ^ f) U)
    {φ : MulAut ↥(StatedSU 4 (p ^ f) K)} {M : Matrix (Fin 4) (Fin 4) K} (hφ : GFrame (p ^ f) U φ M)
    {g : ↥(StatedSU 4 (p ^ f) K)} (hg : FixOut (p ^ f) M g) : φ (cj h hU g) = cj h hU g := by
  obtain ⟨Bm, hBg, hr⟩ := hφ
  have core : ∀ M' : Matrix (Fin 4) (Fin 4) K, Bm * U.map (· ^ (p ^ f)) = U * M' →
      FixOut (p ^ f) M' g → φ (cj h hU g) = cj h hU g := by
    intro M' hr hg'
    apply GenLocU4OutE16.ext_J
    apply GenLocU4OutE16.cancel_of_unitary hBg.1
    have e1 : (((φ (cj h hU g) : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        Bm = Bm * ((((cj h hU g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).map
          (· ^ (p ^ f)) := by
      rw [hBg.2 (cj h hU g), Matrix.mul_assoc, Matrix.mul_assoc, show cstar (p ^ f) Bm * Bm = 1 from hBg.1,
        Matrix.mul_one]
    have hBm : Bm = U * M' * Uᵀ := by
      calc Bm = Bm * (U.map (· ^ (p ^ f)) * Uᵀ) := by rw [Pt_Pbar' h hU, Matrix.mul_one]
        _ = (Bm * U.map (· ^ (p ^ f))) * Uᵀ := by rw [Matrix.mul_assoc]
        _ = _ := by rw [hr]
    have hbar : (⇑h.bar : K → K) = fun c => c ^ (p ^ f) := bar_eq_pow h
    rw [e1, coe_cj h hU g]
    have e2 : (U * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * cstar (p ^ f) U).map (· ^ (p ^ f)) =
        U.map (· ^ (p ^ f)) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) * Uᵀ := by
      rw [← hbar, Matrix.map_mul, Matrix.map_mul, hbar, map_cstar h U]
    rw [e2]
    calc Bm * (U.map (· ^ (p ^ f)) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) * Uᵀ)
        = (Bm * U.map (· ^ (p ^ f))) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = U * (M' * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f))) * Uᵀ := by
          rw [hr]; simp only [Matrix.mul_assoc]
      _ = U * (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * M') * Uᵀ := by rw [hg']
      _ = U * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * cstar (p ^ f) U * Bm := by
          rw [hBm]
          have : cstar (p ^ f) U * U = 1 := hU
          calc U * (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * M') * Uᵀ
              = U * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (cstar (p ^ f) U * U) * M' * Uᵀ := by
                rw [this]; simp only [Matrix.mul_assoc, Matrix.mul_one]
            _ = _ := by simp only [Matrix.mul_assoc]
  rcases hr with hr | hr
  · exact core M hr hg
  · exact core (-M) hr (fixOut_neg.2 hg)

theorem IFrame.fix (h : UnitaryFieldData p f K) {U : Matrix (Fin 4) (Fin 4) K} (hU : IsUnitaryU (p ^ f) U)
    {φ : MulAut ↥(StatedSU 4 (p ^ f) K)} {N : Matrix (Fin 4) (Fin 4) K} (hφ : IFrame (p ^ f) U φ N)
    {g : ↥(StatedSU 4 (p ^ f) K)} (hg : FixIn N g) : φ (cj h hU g) = cj h hU g := by
  obtain ⟨y, hy, hr⟩ := hφ
  have core : ∀ N' : Matrix (Fin 4) (Fin 4) K, y * U = U * N' → FixIn N' g →
      φ (cj h hU g) = cj h hU g := by
    intro N' hr hg'
    apply GenLocU4OutE16.ext_J
    rw [hy.2 (cj h hU g), coe_cj h hU g]
    have hUc : cstar (p ^ f) U * U = 1 := hU
    have hUc' : U * cstar (p ^ f) U = 1 := mul_eq_one_comm.mp hU
    have hyc : y * cstar (p ^ f) y = 1 := mul_eq_one_comm.mp hy.1
    have hy1 : cstar (p ^ f) U * y = N' * cstar (p ^ f) U := by
      calc cstar (p ^ f) U * y = cstar (p ^ f) U * y * (U * cstar (p ^ f) U) := by rw [hUc', Matrix.mul_one]
        _ = cstar (p ^ f) U * (y * U) * cstar (p ^ f) U := by simp only [Matrix.mul_assoc]
        _ = N' * cstar (p ^ f) U := by
          rw [hr]; simp only [← Matrix.mul_assoc, hUc, Matrix.one_mul]
    have hcomm : y * (U * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * cstar (p ^ f) U) =
        (U * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * cstar (p ^ f) U) * y := by
      calc y * (U * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * cstar (p ^ f) U)
          = (y * U) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * cstar (p ^ f) U := by
            simp only [Matrix.mul_assoc]
        _ = U * (N' * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) * cstar (p ^ f) U := by
            rw [hr]; simp only [Matrix.mul_assoc]
        _ = U * (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * N') * cstar (p ^ f) U := by rw [hg']
        _ = U * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (N' * cstar (p ^ f) U) := by
            simp only [Matrix.mul_assoc]
        _ = U * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (cstar (p ^ f) U * y) := by rw [hy1]
        _ = (U * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * cstar (p ^ f) U) * y := by
            simp only [Matrix.mul_assoc]
    calc y * (U * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * cstar (p ^ f) U) * cstar (p ^ f) y
        = (U * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * cstar (p ^ f) U) * y * cstar (p ^ f) y := by
          rw [hcomm]
      _ = U * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * cstar (p ^ f) U := by
          rw [Matrix.mul_assoc _ y, hyc, Matrix.mul_one]
  rcases hr with hr | hr
  · exact core N hr hg
  · exact core (-N) hr (fixIn_neg.2 hg)

omit [Finite K] in
theorem isInnerAut_mul (h : UnitaryFieldData p f K) {φ ψ : MulAut ↥(StatedSU 4 (p ^ f) K)}
    {y z : Matrix (Fin 4) (Fin 4) K} (hy : IsInnerAut (p ^ f) y φ) (hz : IsInnerAut (p ^ f) z ψ) :
    IsInnerAut (p ^ f) (y * z) (φ * ψ) := by
  have hbar : (⇑h.bar : K → K) = fun c => c ^ (p ^ f) := bar_eq_pow h
  refine ⟨isUnitaryU_mul h hy.1 hz.1, fun g => ?_⟩
  rw [MulAut.mul_apply, hy.2, hz.2 g]
  unfold cstar
  rw [← hbar, Matrix.map_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

omit [Finite K] in
theorem real_neg (hq : Odd (p ^ f)) {N : Matrix (Fin 4) (Fin 4) K} (hN : N.map (· ^ (p ^ f)) = N) :
    (-N).map (· ^ (p ^ f)) = -N := by
  ext i j
  have := congrFun (congrFun hN i) j
  simp only [Matrix.map_apply, Matrix.neg_apply] at this ⊢
  rw [hq.neg_pow, this]

omit [Finite K] in
theorem GFrame.mulI (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) {U : Matrix (Fin 4) (Fin 4) K}
    {φ ψ : MulAut ↥(StatedSU 4 (p ^ f) K)} {M N : Matrix (Fin 4) (Fin 4) K}
    (hφ : GFrame (p ^ f) U φ M) (hψ : IFrame (p ^ f) U ψ N) (hN : N.map (· ^ (p ^ f)) = N) :
    GFrame (p ^ f) U (φ * ψ) (M * N) := by
  obtain ⟨Bm, hBg, hr⟩ := hφ
  obtain ⟨y, hy, hs⟩ := hψ
  have hbar : (⇑h.bar : K → K) = fun c => c ^ (p ^ f) := bar_eq_pow h
  refine ⟨Bm * y.map (· ^ (p ^ f)), graphAut_mul_innerAut h hBg hy, ?_⟩
  have key : ∀ M' N' : Matrix (Fin 4) (Fin 4) K, Bm * U.map (· ^ (p ^ f)) = U * M' → y * U = U * N' →
      N'.map (· ^ (p ^ f)) = N' → Bm * y.map (· ^ (p ^ f)) * U.map (· ^ (p ^ f)) = U * (M' * N') := by
    intro M' N' h1 h2 h3
    have e : y.map (· ^ (p ^ f)) * U.map (· ^ (p ^ f)) = U.map (· ^ (p ^ f)) * N' := by
      rw [← hbar, ← Matrix.map_mul, h2, Matrix.map_mul, hbar, h3]
    calc Bm * y.map (· ^ (p ^ f)) * U.map (· ^ (p ^ f)) = Bm * (y.map (· ^ (p ^ f)) * U.map (· ^ (p ^ f))) := by
          rw [Matrix.mul_assoc]
      _ = Bm * (U.map (· ^ (p ^ f)) * N') := by rw [e]
      _ = (Bm * U.map (· ^ (p ^ f))) * N' := by rw [Matrix.mul_assoc]
      _ = U * (M' * N') := by rw [h1, Matrix.mul_assoc]
  have hNn := real_neg hq hN
  rcases hr with hr | hr <;> rcases hs with hs | hs
  · left; exact key _ _ hr hs hN
  · right; rw [key _ _ hr hs hNn, Matrix.mul_neg]
  · right; rw [key _ _ hr hs hN, Matrix.neg_mul]
  · left; rw [key _ _ hr hs hNn]; simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

omit [Finite K] in
theorem IFrame.mulI (h : UnitaryFieldData p f K) {U : Matrix (Fin 4) (Fin 4) K}
    {φ ψ : MulAut ↥(StatedSU 4 (p ^ f) K)} {N N' : Matrix (Fin 4) (Fin 4) K}
    (hφ : IFrame (p ^ f) U φ N) (hψ : IFrame (p ^ f) U ψ N') : IFrame (p ^ f) U (φ * ψ) (N * N') := by
  obtain ⟨y, hy, hr⟩ := hφ
  obtain ⟨z, hz, hs⟩ := hψ
  refine ⟨y * z, isInnerAut_mul h hy hz, ?_⟩
  have key : ∀ A B : Matrix (Fin 4) (Fin 4) K, y * U = U * A → z * U = U * B → y * z * U = U * (A * B) := by
    intro A B h1 h2
    rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  rcases hr with hr | hr <;> rcases hs with hs | hs
  · left; exact key _ _ hr hs
  · right; rw [key _ _ hr hs, Matrix.mul_neg]
  · right; rw [key _ _ hr hs, Matrix.neg_mul]
  · left; rw [key _ _ hr hs]; simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

omit [Finite K] in
theorem graphAut_mul_graphAut (h : UnitaryFieldData p f K) {φ ψ : MulAut ↥(StatedSU 4 (p ^ f) K)}
    {B M : Matrix (Fin 4) (Fin 4) K} (hB : IsGraphAut (p ^ f) B φ) (hM : IsGraphAut (p ^ f) M ψ) :
    IsInnerAut (p ^ f) (B * M.map (· ^ (p ^ f))) (φ * ψ) := by
  have hbar : (⇑h.bar : K → K) = fun c => c ^ (p ^ f) := bar_eq_pow h
  refine ⟨?_, fun g => ?_⟩
  · rw [← hbar]
    exact isUnitaryU_mul h hB.1 (isUnitaryU_map h hM.1)
  · rw [MulAut.mul_apply, hB.2, hM.2 g]
    unfold cstar
    rw [← hbar]
    simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_map, map_bar_bar h, Matrix.mul_assoc]

@[expose] def innerSubU (hp : p.Prime) {A : Type} [Group A] (hA : CFSG.IsElementaryAbelian 2 A)
    (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (h : UnitaryFieldData p f K) : Subgroup A where
  carrier := {a | IsInnerDiagU4 (α a)}
  mul_mem' := fun {a b} ha hb => by
    show IsInnerDiagU4 (α (a * b))
    obtain ⟨y, hy⟩ := isInnerAut_of_isInnerDiagU4 ha
    obtain ⟨z, hz⟩ := isInnerAut_of_isInnerDiagU4 hb
    rw [map_mul]
    exact isInnerDiagU4_of_isInnerAut (isInnerAut_mul h hy hz)
  one_mem' := by
    show IsInnerDiagU4 (α 1)
    rw [map_one]
    refine ⟨1, isUnitaryU_one (pow_ne_zero f hp.ne_zero), fun g => ?_⟩
    simp
  inv_mem' := fun {a} ha => by
    show IsInnerDiagU4 (α a⁻¹)
    have : a⁻¹ = a := inv_eq_of_mul_eq_one_right (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA a)
    rw [this]
    exact ha

theorem inner_cover (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (h : UnitaryFieldData p f K)
    {A : Type} [Group A] (hA : CFSG.IsElementaryAbelian 2 A) (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K))
    {u : A} (hu : ¬ IsInnerDiagU4 (α u)) :
    ∀ b : A, b ∈ innerSubU hp hA α h ∨ b * u ∈ innerSubU hp hA α h := by
  have hα2 : ∀ a : A, α a * α a = 1 := fun a => by
    rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA a, map_one]
  intro b
  by_cases hb : IsInnerDiagU4 (α b)
  · exact Or.inl hb
  · right
    rcases inner_or_graph hp hp2 hK (α b) (hα2 b) with hin | ⟨M, hM, -⟩
    · exact absurd hin hb
    rcases inner_or_graph hp hp2 hK (α u) (hα2 u) with hin | ⟨B, hB, -⟩
    · exact absurd hin hu
    show IsInnerDiagU4 (α (b * u))
    rw [map_mul]
    exact isInnerDiagU4_of_isInnerAut (graphAut_mul_graphAut h (isGraphAut_of_isGraphU4 hM) (isGraphAut_of_isGraphU4 hB))

theorem card_le_two_mul_innerSubU (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (h : UnitaryFieldData p f K) {A : Type} [Group A] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A)
    (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) {u : A} (hu : ¬ IsInnerDiagU4 (α u)) :
    Nat.card A ≤ 2 * Nat.card ↥(innerSubU hp hA α h) := by
  have hidx := GenLocL4Ext.index_le_two_of_cover (innerSubU hp hA α h) u (inner_cover hp hp2 hK h hA α hu)
  have h1 := Subgroup.card_mul_index (innerSubU hp hA α h)
  have : Nat.card ↥(innerSubU hp hA α h) * (innerSubU hp hA α h).index ≤ Nat.card ↥(innerSubU hp hA α h) * 2 :=
    Nat.mul_le_mul_left _ hidx
  omega

theorem mem_gamma_single' {J : Type} [Group J] {A : Type} [Group A] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A)
    (hcard : Nat.card A ≤ 4) (α : A →* MulAut J) {a : A} (ha : a ≠ 1) (x : J) (hx : α a x = x) :
    x ∈ gammaAct α := by
  have ha2 : a * a = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA a
  refine GenLocL4Out.mem_gamma_of_card hA α {a} ?_ x (by simpa using hx)
  have h2 : Nat.card ↥(Subgroup.zpowers a) = 2 := GenLocL4Out.card_zpowers_of_sq a ha ha2
  rw [Subgroup.zpowers_eq_closure] at h2
  omega

theorem mem_gamma_pair' {J : Type} [Group J] {A : Type} [Group A] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A)
    (hcard : Nat.card A ≤ 8) (α : A →* MulAut J) {a b : A} (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) (x : J)
    (hxa : α a x = x) (hxb : α b x = x) : x ∈ gammaAct α := by
  have ha2 : a * a = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA a
  have hb2 : b * b = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA b
  refine GenLocL4Out.mem_gamma_of_card hA α {a, b} ?_ x ?_
  · have := GenLocL4Out.four_le_card_closure_pair a b ha hb hab ha2 hb2
    omega
  · intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · exact hxa
    · exact hxb

omit [Finite K] in
theorem isReal_neg (hq : Odd (p ^ f)) {N : Matrix (Fin 4) (Fin 4) K} (hN : N.map (· ^ (p ^ f)) = N) :
    (-N).map (· ^ (p ^ f)) = -N := real_neg hq hN

omit [Finite K] in
theorem isReal_of_entries (hq : Odd (p ^ f)) (N : Matrix (Fin 4) (Fin 4) K)
    (hN : ∀ i j, N i j = 0 ∨ N i j = 1 ∨ N i j = -1) : N.map (· ^ (p ^ f)) = N := by
  have hp0 : p ^ f ≠ 0 := by
    intro h0; rw [h0] at hq; exact Nat.not_odd_zero hq
  ext i j
  simp only [Matrix.map_apply]
  rcases hN i j with h0 | h1 | h2
  · rw [h0, zero_pow hp0]
  · rw [h1, one_pow]
  · rw [h2, hq.neg_one_pow]

omit [Finite K] in
theorem tT_real (hq : Odd (p ^ f)) : (tT : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) = tT :=
  isReal_of_entries hq _ (fun i j => by fin_cases i <;> fin_cases j <;> simp [tT, Matrix.diagonal])

omit [Finite K] in
theorem tS_real (hq : Odd (p ^ f)) : (tS : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) = tS :=
  isReal_of_entries hq _ (fun i j => by fin_cases i <;> fin_cases j <;> simp [tS, Matrix.diagonal])

omit [Finite K] in
theorem xi_real (hq : Odd (p ^ f)) : (xi : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) = xi :=
  isReal_of_entries hq _ (fun i j => by fin_cases i <;> fin_cases j <;> simp [xi])

theorem top_of_comap (h : UnitaryFieldData p f K) {U : Matrix (Fin 4) (Fin 4) K} (hU : IsUnitaryU (p ^ f) U)
    {A : Type} [Group A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K))
    (hΓ : (gammaAct α).comap (cj h hU).toMonoidHom = ⊤) : gammaAct α = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have : (cj h hU).symm x ∈ (gammaAct α).comap (cj h hU).toMonoidHom := by rw [hΓ]; trivial
  simpa using this

theorem top_split (hSplit : OutSplitGen K p f) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) {A : Type} [Group A] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A)
    (hcard : Nat.card A ≤ 4) (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) {u t : A} (hu1 : u ≠ 1) (ht1 : t ≠ 1)
    (hut1 : u * t ≠ 1) {U : Matrix (Fin 4) (Fin 4) K} (hU : IsUnitaryU (p ^ f) U)
    (hFu : GFrame (p ^ f) U (α u) (mD : Matrix (Fin 4) (Fin 4) K))
    (hFt : IFrame (p ^ f) U (α t) (tT : Matrix (Fin 4) (Fin 4) K)) : gammaAct α = ⊤ := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  refine top_of_comap h hU α ?_
  refine hSplit hp hp2 hK hq _ ?_ ?_ ?_
  · intro g hg
    exact mem_gamma_single' hA hcard α hu1 (cj h hU g) (hFu.fix h hU hg)
  · intro g hg
    exact mem_gamma_single' hA hcard α ht1 (cj h hU g) (hFt.fix h hU hg)
  · intro g hg
    have hF : GFrame (p ^ f) U (α (u * t)) ((mD : Matrix (Fin 4) (Fin 4) K) * tT) := by
      rw [map_mul]; exact hFu.mulI h hodd hFt (tT_real hodd)
    exact mem_gamma_single' hA hcard α hut1 (cj h hU g) (hF.fix h hU hg)

theorem top_ext (hExt : OutExtGen K p f) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) {A : Type} [Group A] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A)
    (hcard : Nat.card A ≤ 4) (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) {u t : A} (hu1 : u ≠ 1) (ht1 : t ≠ 1)
    (hut1 : u * t ≠ 1) {U B' : Matrix (Fin 4) (Fin 4) K} (hU : IsUnitaryU (p ^ f) U)
    (hB'U : IsUnitaryU (p ^ f) B') (hB'M : IsMinusU (p ^ f) B')
    (hB'x : (xi : Matrix (Fin 4) (Fin 4) K) * B' = -(B' * xi))
    (hFu : GFrame (p ^ f) U (α u) B') (hFt : IFrame (p ^ f) U (α t) (xi : Matrix (Fin 4) (Fin 4) K)) :
    gammaAct α = ⊤ := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  refine top_of_comap h hU α ?_
  refine hExt hp hp2 hK hq B' hB'U hB'M hB'x _ ?_ ?_ ?_
  · intro g hg
    exact mem_gamma_single' hA hcard α hu1 (cj h hU g) (hFu.fix h hU hg)
  · intro g hg
    exact mem_gamma_single' hA hcard α ht1 (cj h hU g) (hFt.fix h hU hg)
  · intro g hg
    have hF : GFrame (p ^ f) U (α (u * t)) (B' * (xi : Matrix (Fin 4) (Fin 4) K)) := by
      rw [map_mul]; exact hFu.mulI h hodd hFt (xi_real hodd)
    exact mem_gamma_single' hA hcard α hut1 (cj h hU g) (hF.fix h hU hg)

theorem rank3_pkg {A : Type} [Group A] (hA : CFSG.IsElementaryAbelian 2 A) {u a b : A} (hab : a ≠ b)
    (hua : u ≠ a) (huab : u ≠ a * b) :
    a * b ≠ 1 ∧ u * a ≠ 1 ∧ u * a ≠ b ∧ u * b ≠ a ∧ u * a ≠ u * b := by
  have hsq : ∀ x : A, x * x = 1 := fun x => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA x
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hab
    calc a = a * (b * b) := by rw [hsq b, mul_one]
      _ = (a * b) * b := by rw [mul_assoc]
      _ = b := by rw [h, one_mul]
  · intro h
    apply hua
    calc u = u * (a * a) := by rw [hsq a, mul_one]
      _ = (u * a) * a := by rw [mul_assoc]
      _ = a := by rw [h, one_mul]
  · intro h
    apply huab
    calc u = u * (a * a) := by rw [hsq a, mul_one]
      _ = (u * a) * a := by rw [mul_assoc]
      _ = a * b := by rw [h, mul_comm']
  · intro h
    apply huab
    calc u = u * (b * b) := by rw [hsq b, mul_one]
      _ = (u * b) * b := by rw [mul_assoc]
      _ = a * b := by rw [h]
  · intro h
    exact hab (mul_left_cancel h)

theorem top_Db (hDb : OutDbGen K p f) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) {A : Type} [Group A] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A)
    (hcard : Nat.card A ≤ 8) (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) {u t s : A} (hu1 : u ≠ 1) (ht1 : t ≠ 1)
    (hs1 : s ≠ 1) (hts : t ≠ s) (hut : u ≠ t) (hus : u ≠ s) (hutt : u ≠ t * s)
    {U : Matrix (Fin 4) (Fin 4) K} (hU : IsUnitaryU (p ^ f) U)
    (hFu : GFrame (p ^ f) U (α u) (mD : Matrix (Fin 4) (Fin 4) K))
    (hFt : IFrame (p ^ f) U (α t) (tT : Matrix (Fin 4) (Fin 4) K))
    (hFs : IFrame (p ^ f) U (α s) (tS : Matrix (Fin 4) (Fin 4) K)) : gammaAct α = ⊤ := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨hts1, hut1, hut_s, hus_t, hut_us⟩ := rank3_pkg hA hts hut hutt
  obtain ⟨-, hus1, -, -, -⟩ := rank3_pkg hA hts.symm hus (by rw [mul_comm']; exact hutt)
  have hFts : IFrame (p ^ f) U (α (t * s)) ((tT : Matrix (Fin 4) (Fin 4) K) * tS) := by
    rw [map_mul]; exact hFt.mulI h hFs
  have hFut : GFrame (p ^ f) U (α (u * t)) ((mD : Matrix (Fin 4) (Fin 4) K) * tT) := by
    rw [map_mul]; exact hFu.mulI h hodd hFt (tT_real hodd)
  have hFus : GFrame (p ^ f) U (α (u * s)) ((mD : Matrix (Fin 4) (Fin 4) K) * tS) := by
    rw [map_mul]; exact hFu.mulI h hodd hFs (tS_real hodd)
  refine top_of_comap h hU α ?_
  refine hDb hp hp2 hK hq _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro g h1 h2
    exact mem_gamma_pair' hA hcard α ht1 hs1 hts (cj h hU g) (hFt.fix h hU h1) (hFs.fix h hU h2)
  · intro g h1 h2
    exact mem_gamma_pair' hA hcard α hu1 ht1 hut (cj h hU g) (hFu.fix h hU h1) (hFt.fix h hU h2)
  · intro g h1 h2
    exact mem_gamma_pair' hA hcard α hu1 hs1 hus (cj h hU g) (hFu.fix h hU h1) (hFs.fix h hU h2)
  · intro g h1 h2
    exact mem_gamma_pair' hA hcard α hu1 hts1 hutt (cj h hU g) (hFu.fix h hU h1) (hFts.fix h hU h2)
  · intro g h1 h2
    exact mem_gamma_pair' hA hcard α hut1 hs1 hut_s (cj h hU g) (hFut.fix h hU h1) (hFs.fix h hU h2)
  · intro g h1 h2
    exact mem_gamma_pair' hA hcard α hus1 ht1 hus_t (cj h hU g) (hFus.fix h hU h1) (hFt.fix h hU h2)
  · intro g h1 h2
    exact mem_gamma_pair' hA hcard α hut1 hus1 hut_us (cj h hU g) (hFut.fix h hU h1) (hFus.fix h hU h2)

theorem top_Da (hDa : OutDaGen K p f) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) {A : Type} [Group A] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A)
    (hcard : Nat.card A ≤ 8) (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) {u x i : A} (hu1 : u ≠ 1) (hx1 : x ≠ 1)
    (hi1 : i ≠ 1) (hxi : x ≠ i) (hux : u ≠ x) (hui : u ≠ i) (huxi : u ≠ x * i)
    {U B' : Matrix (Fin 4) (Fin 4) K} (hU : IsUnitaryU (p ^ f) U)
    (hB'U : IsUnitaryU (p ^ f) B') (hB'M : IsMinusU (p ^ f) B')
    (hB'x : (tT : Matrix (Fin 4) (Fin 4) K) * B' = B' * tT)
    (hB'i : (xi : Matrix (Fin 4) (Fin 4) K) * B' = -(B' * xi))
    (hFu : GFrame (p ^ f) U (α u) B')
    (hFx : IFrame (p ^ f) U (α x) (tT : Matrix (Fin 4) (Fin 4) K))
    (hFi : IFrame (p ^ f) U (α i) (xi : Matrix (Fin 4) (Fin 4) K)) : gammaAct α = ⊤ := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨hxi1, hux1, hux_i, hui_x, hux_ui⟩ := rank3_pkg hA hxi hux huxi
  obtain ⟨-, hui1, -, -, -⟩ := rank3_pkg hA hxi.symm hui (by rw [mul_comm']; exact huxi)
  have hFxi : IFrame (p ^ f) U (α (x * i)) ((tT : Matrix (Fin 4) (Fin 4) K) * xi) := by
    rw [map_mul]; exact hFx.mulI h hFi
  have hFux : GFrame (p ^ f) U (α (u * x)) (B' * (tT : Matrix (Fin 4) (Fin 4) K)) := by
    rw [map_mul]; exact hFu.mulI h hodd hFx (tT_real hodd)
  have hFui : GFrame (p ^ f) U (α (u * i)) (B' * (xi : Matrix (Fin 4) (Fin 4) K)) := by
    rw [map_mul]; exact hFu.mulI h hodd hFi (xi_real hodd)
  refine top_of_comap h hU α ?_
  refine hDa hp hp2 hK hq B' hB'U hB'M hB'x hB'i _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro g h1 h2
    exact mem_gamma_pair' hA hcard α hx1 hi1 hxi (cj h hU g) (hFx.fix h hU h1) (hFi.fix h hU h2)
  · intro g h1 h2
    exact mem_gamma_pair' hA hcard α hu1 hx1 hux (cj h hU g) (hFu.fix h hU h1) (hFx.fix h hU h2)
  · intro g h1 h2
    exact mem_gamma_pair' hA hcard α hu1 hi1 hui (cj h hU g) (hFu.fix h hU h1) (hFi.fix h hU h2)
  · intro g h1 h2
    exact mem_gamma_pair' hA hcard α hu1 hxi1 huxi (cj h hU g) (hFu.fix h hU h1) (hFxi.fix h hU h2)
  · intro g h1 h2
    exact mem_gamma_pair' hA hcard α hux1 hi1 hux_i (cj h hU g) (hFux.fix h hU h1) (hFi.fix h hU h2)
  · intro g h1 h2
    exact mem_gamma_pair' hA hcard α hui1 hx1 hui_x (cj h hU g) (hFui.fix h hU h1) (hFx.fix h hU h2)
  · intro g h1 h2
    exact mem_gamma_pair' hA hcard α hux1 hui1 hux_ui (cj h hU g) (hFux.fix h hU h1) (hFui.fix h hU h2)

section Conj

open GenLocU4ExtMu

omit [Finite K] in
theorem isUnitaryU_cstar (h : UnitaryFieldData p f K) {U : Matrix (Fin 4) (Fin 4) K} (hU : IsUnitaryU (p ^ f) U) :
    IsUnitaryU (p ^ f) (cstar (p ^ f) U) := by
  have hbar : (⇑h.bar : K → K) = fun c => c ^ (p ^ f) := bar_eq_pow h
  rw [GenLocU4OutFrame.isUnitaryU_iff_cT h] at hU ⊢
  have : cstar (p ^ f) U = cT h U := by unfold cstar cT; rw [hbar]
  rw [this, cT_cT]
  exact mul_eq_one_comm.mp hU

omit [Finite K] in
theorem conj_minus (h : UnitaryFieldData p f K)
    {U B : Matrix (Fin 4) (Fin 4) K} (hU : IsUnitaryU (p ^ f) U) (hB : IsUnitaryU (p ^ f) B)
    (hBm : IsMinusU (p ^ f) B) :
    IsUnitaryU (p ^ f) (cstar (p ^ f) U * B * U.map (· ^ (p ^ f))) ∧
      IsMinusU (p ^ f) (cstar (p ^ f) U * B * U.map (· ^ (p ^ f))) := by
  have hbar : (⇑h.bar : K → K) = fun c => c ^ (p ^ f) := bar_eq_pow h
  have hUb : IsUnitaryU (p ^ f) (U.map (· ^ (p ^ f))) := by rw [← hbar]; exact isUnitaryU_map h hU
  refine ⟨isUnitaryU_mul h (isUnitaryU_mul h (isUnitaryU_cstar h hU) hB) hUb, ?_, ?_⟩
  · have e1 : (U.map (· ^ (p ^ f)))ᵀ = cstar (p ^ f) U := rfl
    have e2 : (cstar (p ^ f) U)ᵀ = U.map (· ^ (p ^ f)) := by unfold cstar; rw [Matrix.transpose_transpose]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, e1, e2, hBm.1, Matrix.mul_assoc]
  · intro μ hμ hμ2
    have hdU := det_pow_norm_one h hU
    have hdU0 := det_ne_zero_of_unitary h hU
    have hdetU : (cstar (p ^ f) U).det = h.bar U.det := by
      unfold cstar; rw [Matrix.det_transpose, hbar]
      exact (RingHom.map_det (h.bar : K →+* K) U).symm
    have hdetUb : (U.map (· ^ (p ^ f))).det = h.bar U.det := by
      rw [← hbar]; exact (RingHom.map_det (h.bar : K →+* K) U).symm
    rw [Matrix.det_mul, Matrix.det_mul, hdetU, hdetUb] at hμ2
    apply hBm.2 (μ * (h.bar U.det)⁻¹)
    · have hbn : (h.bar U.det) ^ (p ^ f + 1) = 1 := by
        rw [UnitaryFieldData.bar_apply, ← pow_mul, mul_comm, pow_mul, det_norm_one h hU, one_pow]
      rw [mul_pow, inv_pow, hμ, hbn]
      simp
    · have hb0 : h.bar U.det ≠ 0 := (map_ne_zero h.bar).2 hdU0
      calc μ * (h.bar U.det)⁻¹ * (μ * (h.bar U.det)⁻¹) = (μ * μ) * ((h.bar U.det)⁻¹ * (h.bar U.det)⁻¹) := by ring
        _ = B.det := by rw [hμ2]; field_simp

omit [Finite K] in
theorem rel_transport (h : UnitaryFieldData p f K) {U B y N : Matrix (Fin 4) (Fin 4) K} (ε : K)
    (hU : IsUnitaryU (p ^ f) U) (hyU : y * U = U * N) (hN : N.map (· ^ (p ^ f)) = N)
    (hyB : y * B = ε • (B * y.map (· ^ (p ^ f)))) :
    N * (cstar (p ^ f) U * B * U.map (· ^ (p ^ f))) = ε • ((cstar (p ^ f) U * B * U.map (· ^ (p ^ f))) * N) := by
  have hbar : (⇑h.bar : K → K) = fun c => c ^ (p ^ f) := bar_eq_pow h
  have hUc : cstar (p ^ f) U * U = 1 := hU
  have hUc' : U * cstar (p ^ f) U = 1 := mul_eq_one_comm.mp hU
  have e1 : N * cstar (p ^ f) U = cstar (p ^ f) U * y := by
    calc N * cstar (p ^ f) U = cstar (p ^ f) U * (U * N) * cstar (p ^ f) U := by
          rw [← Matrix.mul_assoc, hUc, Matrix.one_mul]
      _ = cstar (p ^ f) U * (y * U) * cstar (p ^ f) U := by rw [hyU]
      _ = cstar (p ^ f) U * y := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hUc', Matrix.mul_one]
  have e2 : y.map (· ^ (p ^ f)) * U.map (· ^ (p ^ f)) = U.map (· ^ (p ^ f)) * N := by
    rw [← hbar, ← Matrix.map_mul, hyU, Matrix.map_mul, hbar, hN]
  calc N * (cstar (p ^ f) U * B * U.map (· ^ (p ^ f)))
      = (N * cstar (p ^ f) U) * B * U.map (· ^ (p ^ f)) := by simp only [Matrix.mul_assoc]
    _ = cstar (p ^ f) U * (y * B) * U.map (· ^ (p ^ f)) := by rw [e1]; simp only [Matrix.mul_assoc]
    _ = ε • (cstar (p ^ f) U * B * (y.map (· ^ (p ^ f)) * U.map (· ^ (p ^ f)))) := by
        rw [hyB]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = ε • ((cstar (p ^ f) U * B * U.map (· ^ (p ^ f))) * N) := by rw [e2]; simp only [Matrix.mul_assoc]

theorem B_conj_rel {U B : Matrix (Fin 4) (Fin 4) K} (hU : IsUnitaryU (p ^ f) U) :
    B * U.map (· ^ (p ^ f)) = U * (cstar (p ^ f) U * B * U.map (· ^ (p ^ f))) := by
  have hUc' : U * cstar (p ^ f) U = 1 := mul_eq_one_comm.mp hU
  calc B * U.map (· ^ (p ^ f)) = (U * cstar (p ^ f) U) * B * U.map (· ^ (p ^ f)) := by rw [hUc', Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]

end Conj

section Frames

variable {A : Type} [Group A]

theorem frame_split (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) {u t : A} {B y : Matrix (Fin 4) (Fin 4) K}
    (hB : IsGraphAut (p ^ f) B (α u)) (hy : IsInnerAut (p ^ f) y (α t)) (hBm : IsMinusU (p ^ f) B)
    (hy2 : y * y = 1) (htr : y.trace = 0) (hyB : y * B = B * y.map (· ^ (p ^ f))) :
    ∃ U : Matrix (Fin 4) (Fin 4) K, IsUnitaryU (p ^ f) U ∧ GFrame (p ^ f) U (α u) (mD : Matrix (Fin 4) (Fin 4) K) ∧
      IFrame (p ^ f) U (α t) (tT : Matrix (Fin 4) (Fin 4) K) := by
  obtain ⟨U, hU, hyU, hBU⟩ := GenLocU4OutFrSplit.exists_split_frame hp hp2 hK hq hy.1 hy2 htr hB.1 hBm hyB
  exact ⟨U, hU, ⟨B, hB, hBU⟩, ⟨y, hy, hyU⟩⟩

theorem frame_ext (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (h : UnitaryFieldData p f K) (hodd : Odd (p ^ f)) (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) {u t : A}
    {B y : Matrix (Fin 4) (Fin 4) K} (hB : IsGraphAut (p ^ f) B (α u)) (hy : IsInnerAut (p ^ f) y (α t))
    (hBm : IsMinusU (p ^ f) B) (hy2 : y * y = -1) (hyB : y * B = -(B * y.map (· ^ (p ^ f)))) :
    ∃ (U B' : Matrix (Fin 4) (Fin 4) K), IsUnitaryU (p ^ f) U ∧ IsUnitaryU (p ^ f) B' ∧ IsMinusU (p ^ f) B' ∧
      (xi : Matrix (Fin 4) (Fin 4) K) * B' = -(B' * xi) ∧ GFrame (p ^ f) U (α u) B' ∧
      IFrame (p ^ f) U (α t) (xi : Matrix (Fin 4) (Fin 4) K) := by
  obtain ⟨U, hU, hyU⟩ := GenLocU4OutFrExt.exists_ext_frame hp hp2 hK hq hy.1 hy2
  obtain ⟨hB'U, hB'M⟩ := conj_minus h hU hB.1 hBm
  refine ⟨U, _, hU, hB'U, hB'M, ?_, ⟨B, hB, Or.inl (B_conj_rel hU)⟩, ⟨y, hy, Or.inl hyU⟩⟩
  have := rel_transport h (-1) hU hyU (xi_real hodd) (by rw [neg_one_smul]; exact hyB)
  rwa [neg_one_smul] at this

theorem frame_SE (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (h : UnitaryFieldData p f K) (hodd : Odd (p ^ f)) (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) {u a b : A}
    {B y z : Matrix (Fin 4) (Fin 4) K} (hB : IsGraphAut (p ^ f) B (α u)) (hBm : IsMinusU (p ^ f) B)
    (hy : IsInnerAut (p ^ f) y (α a)) (hz : IsInnerAut (p ^ f) z (α b)) (hy2 : y * y = 1) (hytr : y.trace = 0)
    (hyB : y * B = B * y.map (· ^ (p ^ f))) (hz2 : z * z = -1) (hzB : z * B = -(B * z.map (· ^ (p ^ f))))
    (hyz : y * z = z * y) :
    ∃ (U B' : Matrix (Fin 4) (Fin 4) K), IsUnitaryU (p ^ f) U ∧ IsUnitaryU (p ^ f) B' ∧ IsMinusU (p ^ f) B' ∧
      (tT : Matrix (Fin 4) (Fin 4) K) * B' = B' * tT ∧ (xi : Matrix (Fin 4) (Fin 4) K) * B' = -(B' * xi) ∧
      GFrame (p ^ f) U (α u) B' ∧ IFrame (p ^ f) U (α a) (tT : Matrix (Fin 4) (Fin 4) K) ∧
      IFrame (p ^ f) U (α b) (xi : Matrix (Fin 4) (Fin 4) K) := by
  obtain ⟨U, hU, hyU, hzU⟩ := GenLocU4OutFrDa.exists_da_frame hp hp2 hK hq hy.1 hy2 hytr hz.1 hz2 hyz
  obtain ⟨hB'U, hB'M⟩ := conj_minus h hU hB.1 hBm
  refine ⟨U, _, hU, hB'U, hB'M, ?_, ?_, ⟨B, hB, Or.inl (B_conj_rel hU)⟩, ⟨y, hy, hyU⟩, ⟨z, hz, Or.inl hzU⟩⟩
  · rcases hyU with hyU | hyU
    · have := rel_transport h 1 hU hyU (tT_real hodd) (by rw [one_smul]; exact hyB)
      rwa [one_smul] at this
    · have := rel_transport h 1 hU hyU (isReal_neg hodd (tT_real hodd)) (by rw [one_smul]; exact hyB)
      rw [one_smul, Matrix.neg_mul, Matrix.mul_neg, neg_inj] at this
      exact this
  · have := rel_transport h (-1) hU hzU (xi_real hodd) (by rw [neg_one_smul]; exact hzB)
    rwa [neg_one_smul] at this

theorem frame_Db (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) {u a b : A} {B y z : Matrix (Fin 4) (Fin 4) K}
    (hB : IsGraphAut (p ^ f) B (α u)) (hBm : IsMinusU (p ^ f) B)
    (hy : IsInnerAut (p ^ f) y (α a)) (hz : IsInnerAut (p ^ f) z (α b)) (hy2 : y * y = 1) (hytr : y.trace = 0)
    (hz2 : z * z = 1) (hztr : z.trace = 0) (hyz : y * z = z * y) (hyztr : (y * z).trace = 0)
    (hyB : y * B = B * y.map (· ^ (p ^ f))) (hzB : z * B = B * z.map (· ^ (p ^ f))) :
    ∃ U : Matrix (Fin 4) (Fin 4) K, IsUnitaryU (p ^ f) U ∧ GFrame (p ^ f) U (α u) (mD : Matrix (Fin 4) (Fin 4) K) ∧
      IFrame (p ^ f) U (α a) (tT : Matrix (Fin 4) (Fin 4) K) ∧ IFrame (p ^ f) U (α b) (tS : Matrix (Fin 4) (Fin 4) K) := by
  obtain ⟨U, εy, εz, hU, hεy, hεz, hyU, hzU, hBU⟩ := GenLocU4OutFrDb.exists_Db_frame hp hp2 hK hq hy.1 hy2 hytr
    hz.1 hz2 hztr hyz hyztr hB.1 hBm hyB hzB
  refine ⟨U, hU, ⟨B, hB, hBU⟩, ⟨y, hy, ?_⟩, ⟨z, hz, ?_⟩⟩
  · rcases hεy with h1 | h1
    · left; rw [h1, one_smul] at hyU; exact hyU
    · right; rw [h1, neg_one_smul] at hyU; exact hyU
  · rcases hεz with h1 | h1
    · left; rw [h1, one_smul] at hzU; exact hzU
    · right; rw [h1, neg_one_smul] at hzU; exact hzU

end Frames

section NLift

open GenLocU4ExtMu

omit [Finite K] in
theorem cstar_eq_of_sq_one {q : ℕ} {y : Matrix (Fin 4) (Fin 4) K} (hy : IsUnitaryU q y) (h2 : y * y = 1) :
    cstar q y = y := by
  have hyc : cstar q y * y = 1 := hy
  calc cstar q y = cstar q y * (y * y) := by rw [h2, Matrix.mul_one]
    _ = (cstar q y * y) * y := by rw [Matrix.mul_assoc]
    _ = y := by rw [hyc, Matrix.one_mul]

omit [Finite K] in
theorem cstar_eq_neg_of_sq_neg_one {q : ℕ} {y : Matrix (Fin 4) (Fin 4) K} (hy : IsUnitaryU q y)
    (h2 : y * y = -1) : cstar q y = -y := by
  have hyc : cstar q y * y = 1 := hy
  calc cstar q y = cstar q y * (y * (-y)) := by rw [Matrix.mul_neg, h2]; simp
    _ = (cstar q y * y) * (-y) := by rw [Matrix.mul_assoc]
    _ = -y := by rw [hyc, Matrix.one_mul]

theorem exists_nlift (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (h : UnitaryFieldData p f K) {A : Type} [Group A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K))
    (hmin : ∀ (a' : A) (M : Matrix (Fin 4) (Fin 4) K), IsGraphAut (p ^ f) M (α a') → IsMinusU (p ^ f) M)
    {u b : A} {B : Matrix (Fin 4) (Fin 4) K} (hB : IsGraphAut (p ^ f) B (α u)) (hbin : IsInnerDiagU4 (α b))
    (hα2 : α b * α b = 1) (hαb1 : α b ≠ 1) :
    ∃ y : Matrix (Fin 4) (Fin 4) K, IsInnerAut (p ^ f) y (α b) ∧ IsSqM (p ^ f) y.det ∧ (∀ c : K, y ≠ c • 1) ∧
      ((y * y = 1 ∧ y * B = B * y.map (· ^ (p ^ f))) ∨ (y * y = -1 ∧ y * B = -(B * y.map (· ^ (p ^ f))))) := by
  obtain ⟨y₀, hy₀⟩ := isInnerAut_of_isInnerDiagU4 hbin
  obtain ⟨ω, hω, hsq⟩ := normalize_lift hp hp2 hK hq h hα2 hy₀
  have hω' : ω ^ (p ^ f) * ω = 1 := by rw [← pow_succ]; exact hω
  have hy : IsInnerAut (p ^ f) (ω • y₀) (α b) := isInnerAut_smul hω' hy₀
  obtain ⟨hR, hBy⟩ := lift_rel' h α hmin hB hy₀
  have hdet := isSqM_det_smul hω (isSqM_det_of_minus hp hp2 hK h hB.1 hy₀.1 (hmin u B hB) hBy)
  have hq0 : p ^ f ≠ 0 := pow_ne_zero f hp.ne_zero
  refine ⟨ω • y₀, hy, hdet, fun c hc => hαb1 (eq_one_of_scalar hq0 hy hc), ?_⟩
  have hR' := rel_smul ω hR
  rcases hsq with hs | hs
  · left
    refine ⟨hs, ?_⟩
    rw [cstar_eq_of_sq_one hy.1 hs] at hR'
    exact hR'
  · right
    refine ⟨hs, ?_⟩
    rw [cstar_eq_neg_of_sq_neg_one hy.1 hs, Matrix.neg_mul] at hR'
    exact neg_eq_iff_eq_neg.mp hR'

omit [Finite K] in
theorem cstar_mul (h : UnitaryFieldData p f K) (y z : Matrix (Fin 4) (Fin 4) K) :
    cstar (p ^ f) (y * z) = cstar (p ^ f) z * cstar (p ^ f) y := by
  have hbar : (⇑h.bar : K → K) = fun c => c ^ (p ^ f) := bar_eq_pow h
  unfold cstar
  rw [← hbar, Matrix.map_mul, Matrix.transpose_mul]

omit [Finite K] in
theorem lifts_commute (h : UnitaryFieldData p f K) {A : Type} [Group A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K))
    (hmin : ∀ (a' : A) (M : Matrix (Fin 4) (Fin 4) K), IsGraphAut (p ^ f) M (α a') → IsMinusU (p ^ f) M)
    {u a b : A} {B y z : Matrix (Fin 4) (Fin 4) K} (hB : IsGraphAut (p ^ f) B (α u))
    (hy : IsInnerAut (p ^ f) y (α a)) (hz : IsInnerAut (p ^ f) z (α b)) : y * z = z * y := by
  have hbar : (⇑h.bar : K → K) = fun c => c ^ (p ^ f) := bar_eq_pow h
  have hyz : IsInnerAut (p ^ f) (y * z) (α (a * b)) := by rw [map_mul]; exact isInnerAut_mul h hy hz
  have Ry := (lift_rel' h α hmin hB hy).1
  have Rz := (lift_rel' h α hmin hB hz).1
  have Ryz := (lift_rel' h α hmin hB hyz).1
  rw [cstar_mul h, ← hbar, Matrix.map_mul, hbar] at Ryz
  have e1 : cstar (p ^ f) z * cstar (p ^ f) y * B = B * z.map (· ^ (p ^ f)) * y.map (· ^ (p ^ f)) := by
    rw [Matrix.mul_assoc, Ry, ← Matrix.mul_assoc, Rz]
  have e2 : B * (z.map (· ^ (p ^ f)) * y.map (· ^ (p ^ f))) = B * (y.map (· ^ (p ^ f)) * z.map (· ^ (p ^ f))) := by
    rw [← Matrix.mul_assoc, ← e1, Ryz]
  have hBc : cstar (p ^ f) B * B = 1 := hB.1
  have e3 : z.map (· ^ (p ^ f)) * y.map (· ^ (p ^ f)) = y.map (· ^ (p ^ f)) * z.map (· ^ (p ^ f)) := by
    have := congrArg (fun M => cstar (p ^ f) B * M) e2
    simp only [← Matrix.mul_assoc, hBc, Matrix.one_mul] at this
    exact this
  have e4 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M.map h.bar) e3
  simp only [Matrix.map_mul, ← hbar, map_bar_bar h] at e4
  exact e4.symm

end NLift

theorem exists_ne_one_of_one_lt' {A : Type} [Group A] [Finite A] (H : Subgroup A) (h : 1 < Nat.card H) :
    ∃ a : A, a ∈ H ∧ a ≠ 1 := by
  have h1 : H ≠ ⊥ := fun hb => by
    rw [hb] at h
    simp at h
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h1
  exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩

theorem exists_two_ne_one' {A : Type} [Group A] [Finite A] (H : Subgroup A) (h : 2 < Nat.card H) :
    ∃ a b : A, a ∈ H ∧ b ∈ H ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  obtain ⟨a, ha, ha1⟩ := exists_ne_one_of_one_lt' H (by omega)
  have hlt : ({1, a} : Set A).ncard < (H : Set A).ncard := by
    rw [Set.ncard_pair (Ne.symm ha1)]
    have : (H : Set A).ncard = Nat.card ↥H := (Nat.card_coe_set_eq _).symm
    omega
  obtain ⟨b, hb, hb2⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt (Set.toFinite _)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb2
  exact ⟨a, b, ha, hb, ha1, hb2.1, fun h => hb2.2 h.symm⟩

@[expose] def DataSplit {A : Type} [Group A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (u t : A) : Prop :=
  ∃ U : Matrix (Fin 4) (Fin 4) K, IsUnitaryU (p ^ f) U ∧ GFrame (p ^ f) U (α u) (mD : Matrix (Fin 4) (Fin 4) K) ∧
    IFrame (p ^ f) U (α t) (tT : Matrix (Fin 4) (Fin 4) K)

@[expose] def DataExt {A : Type} [Group A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (u t : A) : Prop :=
  ∃ U B' : Matrix (Fin 4) (Fin 4) K, IsUnitaryU (p ^ f) U ∧ IsUnitaryU (p ^ f) B' ∧ IsMinusU (p ^ f) B' ∧
    (xi : Matrix (Fin 4) (Fin 4) K) * B' = -(B' * xi) ∧ GFrame (p ^ f) U (α u) B' ∧
    IFrame (p ^ f) U (α t) (xi : Matrix (Fin 4) (Fin 4) K)

@[expose] def DataDb {A : Type} [Group A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (u a b : A) : Prop :=
  ∃ U : Matrix (Fin 4) (Fin 4) K, IsUnitaryU (p ^ f) U ∧ GFrame (p ^ f) U (α u) (mD : Matrix (Fin 4) (Fin 4) K) ∧
    IFrame (p ^ f) U (α a) (tT : Matrix (Fin 4) (Fin 4) K) ∧ IFrame (p ^ f) U (α b) (tS : Matrix (Fin 4) (Fin 4) K)

@[expose] def DataDa {A : Type} [Group A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (u x i : A) : Prop :=
  ∃ U B' : Matrix (Fin 4) (Fin 4) K, IsUnitaryU (p ^ f) U ∧ IsUnitaryU (p ^ f) B' ∧ IsMinusU (p ^ f) B' ∧
    (tT : Matrix (Fin 4) (Fin 4) K) * B' = B' * tT ∧ (xi : Matrix (Fin 4) (Fin 4) K) * B' = -(B' * xi) ∧
    GFrame (p ^ f) U (α u) B' ∧ IFrame (p ^ f) U (α x) (tT : Matrix (Fin 4) (Fin 4) K) ∧
    IFrame (p ^ f) U (α i) (xi : Matrix (Fin 4) (Fin 4) K)

theorem rank2_data (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) {A : Type} [Group A] [Finite A] (hR : IsRank23 A)
    (hcard : Nat.card A = 4) (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (hinj : Function.Injective α)
    (hsect : SectionalTwoRankLE ↥(innJoin α) 4) {u : A} (hu : ¬ IsInnerDiagU4 (α u)) :
    ∃ u t : A, u ≠ 1 ∧ t ≠ 1 ∧ u * t ≠ 1 ∧ (DataSplit α u t ∨ DataExt α u t) := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hA := hR.1
  have hα2 : ∀ a : A, α a * α a = 1 := fun a => by
    rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA a, map_one]
  have hmin : ∀ (a' : A) (M : Matrix (Fin 4) (Fin 4) K), IsGraphAut (p ^ f) M (α a') → IsMinusU (p ^ f) M :=
    fun a' M hM => outer_survivors hp hp2 hK hq α hR ⟨u, hu⟩ hsect a' (unitaryGL M hM.1) (isGraphU4_of_isGraphAut hM)
  have hu1 : u ≠ 1 := fun h1 => hu (by rw [h1, map_one]; exact ⟨1, isUnitaryU_one (pow_ne_zero f hp.ne_zero), fun g => by simp⟩)
  have hin := card_le_two_mul_innerSubU hp hp2 hK h hA α hu
  obtain ⟨t, htI, ht1⟩ := exists_ne_one_of_one_lt' (innerSubU hp hA α h) (by omega)
  have htin : IsInnerDiagU4 (α t) := htI
  have hut : u ≠ t := fun h1 => hu (h1 ▸ htin)
  have hut1 : u * t ≠ 1 := by
    intro h1
    apply hut
    calc u = u * (t * t) := by rw [WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA t, mul_one]
      _ = (u * t) * t := by rw [mul_assoc]
      _ = t := by rw [h1, one_mul]
  rcases inner_or_graph hp hp2 hK (α u) (hα2 u) with hin' | ⟨B, hBg, -⟩
  · exact absurd hin' hu
  have hB := isGraphAut_of_isGraphU4 hBg
  have hBm := hmin u _ hB
  have hαt1 : α t ≠ 1 := fun h1 => ht1 (hinj (by rw [h1, map_one]))
  obtain ⟨y, hy, hdet, hns, hcases⟩ := exists_nlift hp hp2 hK hq h α hmin hB htin (hα2 t) hαt1
  rcases hcases with ⟨hy2, hyB⟩ | ⟨hy2, hyB⟩
  · have htr := split_trace_zero hp hp2 hK hq hy.1 hy2 hdet hns
    exact ⟨u, t, hu1, ht1, hut1, Or.inl (frame_split hp hp2 hK hq α hB hy hBm hy2 htr hyB)⟩
  · exact ⟨u, t, hu1, ht1, hut1, Or.inr (frame_ext hp hp2 hK hq h hodd α hB hy hBm hy2 hyB)⟩

omit [Finite K] in
theorem sq_prod_of_comm {y z : Matrix (Fin 4) (Fin 4) K} (hyz : y * z = z * y) :
    (y * z) * (y * z) = (y * y) * (z * z) := by
  calc (y * z) * (y * z) = y * (z * y) * z := by simp only [Matrix.mul_assoc]
    _ = y * (y * z) * z := by rw [← hyz]
    _ = (y * y) * (z * z) := by simp only [Matrix.mul_assoc]

theorem rank3_data (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) {A : Type} [Group A] [Finite A] (hR : IsRank23 A)
    (hcard : Nat.card A = 8) (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (hinj : Function.Injective α)
    (hsect : SectionalTwoRankLE ↥(innJoin α) 4) {u : A} (hu : ¬ IsInnerDiagU4 (α u)) :
    ∃ u x i : A, u ≠ 1 ∧ x ≠ 1 ∧ i ≠ 1 ∧ x ≠ i ∧ u ≠ x ∧ u ≠ i ∧ u ≠ x * i ∧ (DataDb α u x i ∨ DataDa α u x i) := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq0 : p ^ f ≠ 0 := pow_ne_zero f hp.ne_zero
  have hA := hR.1
  have hα2 : ∀ a : A, α a * α a = 1 := fun a => by
    rw [← map_mul, WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA a, map_one]
  have hmin : ∀ (a' : A) (M : Matrix (Fin 4) (Fin 4) K), IsGraphAut (p ^ f) M (α a') → IsMinusU (p ^ f) M :=
    fun a' M hM => outer_survivors hp hp2 hK hq α hR ⟨u, hu⟩ hsect a' (unitaryGL M hM.1) (isGraphU4_of_isGraphAut hM)
  have hu1 : u ≠ 1 := fun h1 => hu (by rw [h1, map_one]; exact ⟨1, isUnitaryU_one hq0, fun g => by simp⟩)
  have hin := card_le_two_mul_innerSubU hp hp2 hK h hA α hu
  obtain ⟨a, b, haI, hbI, ha1, hb1, hab⟩ := exists_two_ne_one' (innerSubU hp hA α h) (by omega)
  have hain : IsInnerDiagU4 (α a) := haI
  have hbin : IsInnerDiagU4 (α b) := hbI
  have hua : u ≠ a := fun h1 => hu (h1 ▸ hain)
  have hub : u ≠ b := fun h1 => hu (h1 ▸ hbin)
  have huab : u ≠ a * b := fun h1 => hu (h1 ▸ (innerSubU hp hA α h).mul_mem haI hbI)
  obtain ⟨hab1, -, -, -, -⟩ := rank3_pkg hA hab hua huab
  rcases inner_or_graph hp hp2 hK (α u) (hα2 u) with hin' | ⟨B, hBg, -⟩
  · exact absurd hin' hu
  have hB := isGraphAut_of_isGraphU4 hBg
  have hBm := hmin u _ hB
  have hαa1 : α a ≠ 1 := fun h1 => ha1 (hinj (by rw [h1, map_one]))
  have hαb1 : α b ≠ 1 := fun h1 => hb1 (hinj (by rw [h1, map_one]))
  have hαab1 : α (a * b) ≠ 1 := fun h1 => hab1 (hinj (by rw [h1, map_one]))
  obtain ⟨y, hy, hdy, hnsy, hcy⟩ := exists_nlift hp hp2 hK hq h α hmin hB hain (hα2 a) hαa1
  obtain ⟨z, hz, hdz, hnsz, hcz⟩ := exists_nlift hp hp2 hK hq h α hmin hB hbin (hα2 b) hαb1
  have hyz : y * z = z * y := lifts_commute h α hmin hB hy hz
  have hw : IsInnerAut (p ^ f) (y * z) (α (a * b)) := by rw [map_mul]; exact isInnerAut_mul h hy hz
  obtain ⟨hRw, hBw⟩ := lift_rel' h α hmin hB hw
  have hdw : IsSqM (p ^ f) (y * z).det := isSqM_det_of_minus hp hp2 hK h hB.1 hw.1 hBm hBw
  have hnsw : ∀ c : K, y * z ≠ c • 1 := fun c hc => hαab1 (eq_one_of_scalar hq0 hw hc)
  have hsqw := sq_prod_of_comm hyz
  rcases hcy with ⟨hy2, hyB⟩ | ⟨hy2, hyB⟩ <;> rcases hcz with ⟨hz2, hzB⟩ | ⟨hz2, hzB⟩
  ·
    have hw2 : (y * z) * (y * z) = 1 := by rw [hsqw, hy2, hz2, Matrix.mul_one]
    have htry := split_trace_zero hp hp2 hK hq hy.1 hy2 hdy hnsy
    have htrz := split_trace_zero hp hp2 hK hq hz.1 hz2 hdz hnsz
    have htrw := split_trace_zero hp hp2 hK hq hw.1 hw2 hdw hnsw
    obtain ⟨U, hU, hFu, hFa, hFb⟩ := frame_Db hp hp2 hK hq α hB hBm hy hz hy2 htry hz2 htrz hyz htrw hyB hzB
    exact ⟨u, a, b, hu1, ha1, hb1, hab, hua, hub, huab, Or.inl ⟨U, hU, hFu, hFa, hFb⟩⟩
  ·
    have htry := split_trace_zero hp hp2 hK hq hy.1 hy2 hdy hnsy
    obtain ⟨U, B', hU, hB'U, hB'M, hB'x, hB'i, hFu, hFx, hFi⟩ :=
      frame_SE hp hp2 hK hq h hodd α hB hBm hy hz hy2 htry hyB hz2 hzB hyz
    exact ⟨u, a, b, hu1, ha1, hb1, hab, hua, hub, huab, Or.inr ⟨U, B', hU, hB'U, hB'M, hB'x, hB'i, hFu, hFx, hFi⟩⟩
  ·
    have htrz := split_trace_zero hp hp2 hK hq hz.1 hz2 hdz hnsz
    obtain ⟨U, B', hU, hB'U, hB'M, hB'x, hB'i, hFu, hFx, hFi⟩ :=
      frame_SE hp hp2 hK hq h hodd α hB hBm hz hy hz2 htrz hzB hy2 hyB hyz.symm
    exact ⟨u, b, a, hu1, hb1, ha1, hab.symm, hub, hua, (by rw [mul_comm']; exact huab),
      Or.inr ⟨U, B', hU, hB'U, hB'M, hB'x, hB'i, hFu, hFx, hFi⟩⟩
  ·
    have hw2 : (y * z) * (y * z) = 1 := by rw [hsqw, hy2, hz2]; simp
    have htrw := split_trace_zero hp hp2 hK hq hw.1 hw2 hdw hnsw
    have hwB : (y * z) * B = B * (y * z).map (· ^ (p ^ f)) := by
      rw [cstar_eq_of_sq_one hw.1 hw2] at hRw
      exact hRw
    have hwy : (y * z) * y = y * (y * z) := by
      calc (y * z) * y = y * (z * y) := by rw [Matrix.mul_assoc]
        _ = y * (y * z) := by rw [hyz]
    obtain ⟨U, B', hU, hB'U, hB'M, hB'x, hB'i, hFu, hFx, hFi⟩ :=
      frame_SE hp hp2 hK hq h hodd α hB hBm hw hy hw2 htrw hwB hy2 hyB hwy
    have hsq : ∀ x : A, x * x = 1 := fun x => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA x
    have hxia : a * b * a = b := by
      calc a * b * a = a * a * b := by rw [mul_assoc, mul_comm' b a, ← mul_assoc]
        _ = b := by rw [hsq a, one_mul]
    exact ⟨u, a * b, a, hu1, hab1, ha1, (fun h1 => hb1 (by simpa using h1)), huab, hua, (by rw [hxia]; exact hub),
      Or.inr ⟨U, B', hU, hB'U, hB'M, hB'x, hB'i, hFu, hFx, hFi⟩⟩

theorem outer_survivors' (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    {A : Type} [Group A] [Finite A] (hR : IsRank23 A) (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K))
    (hinj : Function.Injective α) (hsect : SectionalTwoRankLE ↥(innJoin α) 4) {u : A}
    (hu : ¬ IsInnerDiagU4 (α u)) :
    (Nat.card A = 4 ∧ ∃ u t : A, u ≠ 1 ∧ t ≠ 1 ∧ u * t ≠ 1 ∧ (DataSplit α u t ∨ DataExt α u t)) ∨
      (Nat.card A = 8 ∧ ∃ u x i : A, u ≠ 1 ∧ x ≠ 1 ∧ i ≠ 1 ∧ x ≠ i ∧ u ≠ x ∧ u ≠ i ∧ u ≠ x * i ∧
        (DataDb α u x i ∨ DataDa α u x i)) := by
  have hcard := GenLocBasic.card_eq_two_pow_pRank_type hR.1
  rcases hR.2 with h2 | h3
  · left
    have h4 : Nat.card A = 4 := by rw [hcard, h2]; norm_num
    exact ⟨h4, rank2_data hp hp2 hK hq hR h4 α hinj hsect hu⟩
  · right
    have h8 : Nat.card A = 8 := by rw [hcard, h3]; norm_num
    exact ⟨h8, rank3_data hp hp2 hK hq hR h8 α hinj hsect hu⟩

theorem gammaAct_su4_outer_of_classes (hSplit : OutSplitGen K p f) (hDb : OutDbGen K p f)
    (hExt : OutExtGen K p f) (hDa : OutDaGen K p f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) {A : Type} [Group A] [Finite A]
    (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (hA : IsRank23 A) (hout : ∃ a : A, ¬ IsInnerDiagU4 (α a))
    (hsect : SectionalTwoRankLE ↥(innJoin α) 4) : gammaAct α = ⊤ := by
  by_cases hex : ∃ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E ∧ E ≤ α.ker
  · obtain ⟨E, hE, hk⟩ := hex
    exact gammaAct_eq_top_of_le_ker α hE hk
  · simp only [not_exists, not_and] at hex
    obtain ⟨hR, hg, -⟩ := range_reduction α hA hex
    rw [hg]
    have hfin : Finite ↥α.range := Finite.of_surjective _ α.rangeRestrict_surjective
    obtain ⟨a, ha⟩ := hout
    have hsectD : SectionalTwoRankLE ↥(innJoin α.range.subtype) 4 := by
      have : innJoin α.range.subtype = innJoin α := by
        unfold innJoin
        rw [Subgroup.range_subtype]
      rw [this]
      exact hsect
    have huD : ¬ IsInnerDiagU4 (α.range.subtype ⟨α a, a, rfl⟩) := ha
    have hAe := hR.1
    rcases outer_survivors' hp hp2 hK hq hR α.range.subtype Subtype.val_injective hsectD huD with
      ⟨hc, u, t, hu1, ht1, hut1, hd | hd⟩ | ⟨hc, u, x, i, hu1, hx1, hi1, hxi, hux, hui, huxi, hd | hd⟩
    · obtain ⟨U, hU, hFu, hFt⟩ := hd
      exact top_split hSplit hp hp2 hK hq hAe (by omega) _ hu1 ht1 hut1 hU hFu hFt
    · obtain ⟨U, B', hU, hB'U, hB'M, hB'x, hFu, hFt⟩ := hd
      exact top_ext hExt hp hp2 hK hq hAe (by omega) _ hu1 ht1 hut1 hU hB'U hB'M hB'x hFu hFt
    · obtain ⟨U, hU, hFu, hFa, hFb⟩ := hd
      exact top_Db hDb hp hp2 hK hq hAe (by omega) _ hu1 hx1 hi1 hxi hux hui huxi hU hFu hFa hFb
    · obtain ⟨U, B', hU, hB'U, hB'M, hB'x, hB'i, hFu, hFx, hFi⟩ := hd
      exact top_Da hDa hp hp2 hK hq hAe (by omega) _ hu1 hx1 hi1 hxi hux hui huxi hU hB'U hB'M hB'x hB'i hFu hFx hFi

end GenLocU4OutAsm
