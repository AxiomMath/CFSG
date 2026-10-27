module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Iso
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSU
import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Conj
import CFSG.ClassicalGroups.Unitary.Simple
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Glue
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup Matrix CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ComponentClassification.Burgoyne
  CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.TBLit CFSG.Blueprint
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.ComponentClassification.Burgoyne.PSL (conj_range_normal signMat)

namespace Psu

section Transfer

variable {G : Type} [Group G] [Finite G]

theorem isCyclic_oddCoreIn_of_conj (B : Subgroup G) {t : G} (ht : t ∈ B) (c : G)
    (h : IsCyclic ↥(oddCoreIn (B.map (MulAut.conj c).toMonoidHom) (c * t * c⁻¹))) :
    IsCyclic ↥(oddCoreIn B t) := by
  rw [oddCoreIn_map_conj B ht c] at h
  exact isCyclic_of_surjective
    (Subgroup.equivMapOfInjective (oddCoreIn B t) (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective).symm.toMonoidHom
    (Subgroup.equivMapOfInjective (oddCoreIn B t) (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective).symm.surjective

end Transfer

theorem inn_le_map_conj {T : Type} [Group T] {B : Subgroup (MulAut T)}
    (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (c : MulAut T) :
    (MulAut.conj : T →* MulAut T).range ≤ B.map (MulAut.conj c).toMonoidHom := by
  rintro _ ⟨x, rfl⟩
  have hx : c⁻¹ * MulAut.conj x * c⁻¹⁻¹ ∈ (MulAut.conj : T →* MulAut T).range :=
    conj_range_normal.conj_mem _ ⟨x, rfl⟩ c⁻¹
  refine ⟨_, hB hx, ?_⟩
  simp [MulAut.conj_apply]
  group

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

@[expose] def normOne : Subgroup Kˣ where
  carrier := {γ | h.norm (γ : K) = 1}
  mul_mem' := fun {a b} (ha : h.norm (a : K) = 1) (hb : h.norm (b : K) = 1) => by
    show h.norm ((a * b : Kˣ) : K) = 1
    simp only [UnitaryFieldData.norm, Units.val_mul, map_mul] at ha hb ⊢
    calc (a : K) * (b : K) * (h.bar a * h.bar b) = ((a : K) * h.bar a) * ((b : K) * h.bar b) := by
          ring
      _ = 1 := by rw [ha, hb, one_mul]
  one_mem' := by
    show h.norm (((1 : Kˣ) : K)) = 1
    simp [UnitaryFieldData.norm]
  inv_mem' := fun {a} (ha : h.norm (a : K) = 1) => by
    show h.norm ((a⁻¹ : Kˣ) : K) = 1
    simp only [UnitaryFieldData.norm, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢
    rw [← mul_inv, ha, inv_one]

theorem isCyclic_normOne : IsCyclic ↥(normOne h) := by
  have := h.finite
  exact Subgroup.isCyclic _

@[expose] def uSplitHom (J : Finset (Fin n)) : ↥(normOne h) →* uU h n where
  toFun γ := uDiagJ h J (γ : Kˣ) 1 γ.2 (by simp [UnitaryFieldData.norm])
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change diagonal (fun i => if i ∈ J then (((1 : ↥(normOne h)) : Kˣ) : K) else
      ((1 : Kˣ) : K)) = 1
    rw [← diagonal_one]
    congr 1
    ext i
    split_ifs <;> simp
  map_mul' γ δ := by
    apply Subtype.ext
    apply Units.ext
    change diagonal (fun i => if i ∈ J then (((γ * δ : ↥(normOne h)) : Kˣ) : K) else
        ((1 : Kˣ) : K)) =
      diagonal (fun i => if i ∈ J then ((γ : Kˣ) : K) else ((1 : Kˣ) : K)) *
        diagonal (fun i => if i ∈ J then ((δ : Kˣ) : K) else ((1 : Kˣ) : K))
    rw [diagonal_mul_diagonal]
    congr 1
    ext i
    split_ifs <;> simp

theorem coe_uSplitHom (J : Finset (Fin n)) (γ : ↥(normOne h)) :
    (((uSplitHom h J γ : uU h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => if i ∈ J then ((γ : Kˣ) : K) else 1 := rfl

theorem isCyclic_oddCoreIn_uSign (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ B)
    {J : Finset (Fin n)} {a b : Fin n} (ha : a ∈ J) (hb : b ∉ J) :
    IsCyclic ↥(oddCoreIn B (uConjAut h (by omega) (uSign h J))) := by
  have := h.finite
  have := isCyclic_normOne h
  refine isCyclic_of_le_range ((uConjAut h (by omega)).comp (uSplitHom h J)) fun y hy => ?_
  obtain ⟨α, β, hα, hβ, rfl⟩ := split_oddCoreIn h hp2 hn hinj hB ha hb hy
  have hαβ : h.norm (((α / β : Kˣ)) : K) = 1 := by
    have hα' : (α : K) * h.bar α = 1 := hα
    have hβ' : (β : K) * h.bar β = 1 := hβ
    rw [Units.val_div_eq_div_val, UnitaryFieldData.norm, map_div₀, div_mul_div_comm, hα', hβ',
      div_one]
  refine ⟨⟨α / β, hαβ⟩, ?_⟩
  refine (uConjAut_eq_of_eq_smul h hn (c := (β : K)) β.ne_zero ?_).symm
  rw [coe_uSplitHom, coe_uDiagJ, ← diagonal_smul]
  congr 1
  ext i
  by_cases hi : i ∈ J
  · simp only [hi, ↓reduceIte, Pi.smul_apply, smul_eq_mul, Units.val_div_eq_div_val]
    field_simp
  · simp [hi]

section Paired

variable {m : ℕ}

theorem smul_one_mul_smul_one (x y : K) :
    ((x • (1 : Matrix (Fin m) (Fin m) K)) * (y • 1)) = (x * y) • 1 := by
  rw [Matrix.smul_mul, Matrix.one_mul, smul_smul]

@[expose] def uPairDiag (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1) (a : Kˣ) :
    uU h (m + m) :=
  ⟨uGL h (prPhi m l ((a : K) • 1) ((h.bar (a : K))⁻¹ • 1))
    ((prPhi_unitary_iff h h2 hl hN _ _).2 (by
      rw [smul_one_map h, smul_one_mul_smul_one, mul_inv_cancel₀ ((map_ne_zero h.bar).2 a.ne_zero),
        one_smul])), uGL_mem h _ _⟩

theorem coe_uPairDiag (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1) (a : Kˣ) :
    (((uPairDiag h h2 hl hN a : uU h (m + m)) : GL (Fin (m + m)) K) :
      Matrix (Fin (m + m)) (Fin (m + m)) K) =
      prPhi m l ((a : K) • 1) ((h.bar (a : K))⁻¹ • 1) := rfl

@[expose] def uPairHom (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1) :
    Kˣ →* uU h (m + m) :=
  MonoidHom.mk' (uPairDiag h h2 hl hN) fun a b => by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, coe_uPairDiag, coe_uPairDiag, coe_uPairDiag,
      prPhi_mul h2 hl, smul_one_mul_smul_one, smul_one_mul_smul_one, Units.val_mul, map_mul,
      mul_inv]

theorem coe_uPairHom (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) (hN : h.norm l = -1) (a : Kˣ) :
    (((uPairHom h h2 hl hN a : uU h (m + m)) : GL (Fin (m + m)) K) :
      Matrix (Fin (m + m)) (Fin (m + m)) K) =
      prPhi m l ((a : K) • 1) ((h.bar (a : K))⁻¹ • 1) := rfl

theorem isCyclic_oddCoreIn_uPairA (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) (hm : 2 ≤ m)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU (m + m) (p ^ f) K) →*
      MulAut (StatedProj (StatedSU (m + m) (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU (m + m) (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU (m + m) (p ^ f) K) →*
      MulAut (StatedProj (StatedSU (m + m) (p ^ f) K))).range ≤ B)
    {l : K} (hl : l ≠ 0) (hN : h.norm l = -1) :
    IsCyclic ↥(oddCoreIn B (uConjAut h (by omega) (uPairA h h2 hl hN))) := by
  have := h.finite
  refine isCyclic_of_le_range ((uConjAut h (by omega)).comp (uPairHom h h2 hl hN)) fun y hy => ?_
  obtain ⟨a, b, D, hab, hD, rfl⟩ := paired_oddCoreIn h hp2 h2 hm hinj hB hl hN hy
  have ha : a ≠ 0 := fun e => by rw [e, map_zero, zero_mul] at hab; exact zero_ne_one hab
  refine ⟨Units.mk0 a ha, ?_⟩
  show uConjAut h (by omega) (uPairHom h h2 hl hN (Units.mk0 a ha)) = uConjAut h (by omega) D
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [coe_uPairHom, hD, eq_inv_of_mul_eq_one_right hab]
  rfl

end Paired

include h in
theorem two_ne_zero_of_ne_two (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  have := h.charP
  intro e
  have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
  rw [CharP.cast_eq_zero_iff K p] at e'
  have := Nat.le_of_dvd (by norm_num) e'
  have := h.prime.two_le
  exact hp2 (by omega)

theorem uConjAut_conj_eq (hn : 3 ≤ n) {A A' H : uU h n} {c : K} (hc : c ≠ 0)
    (hH : ((((H : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((H : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
        c • ((A' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    uConjAut h (by omega) H⁻¹ * uConjAut h (by omega) A * (uConjAut h (by omega) H⁻¹)⁻¹ =
      uConjAut h (by omega) A' := by
  rw [← map_inv, inv_inv, ← map_mul, ← map_mul]
  refine uConjAut_eq_of_eq_smul h hn hc ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul]
  exact hH

theorem isCyclic_oddCoreIn_innerSplit (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ B)
    {t : MulAut (StatedProj (StatedSU n (p ^ f) K))} (htB : t ∈ B)
    {A : uU h n} (htA : t = uConjAut h (by omega) A) {l : K} (hl0 : l ≠ 0)
    (hlN : h.norm l = 1)
    (hAA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (l ^ 2) • 1)
    (hns : ∀ c : Kˣ, (A : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) c) :
    IsCyclic ↥(oddCoreIn B t) := by
  have := h.finite
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_ne_two h hp2
  set M := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  have hU : (M.map h.bar)ᵀ * M = 1 := (mem_uU h).1 A.2
  have hNi : h.bar l⁻¹ * l⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hlN, inv_one]
  have hU' : ((l⁻¹ • M).map h.bar)ᵀ * (l⁻¹ • M) = 1 := by
    rw [show (l⁻¹ • M).map h.bar = h.bar l⁻¹ • M.map h.bar by
      ext i j; simp [map_mul]]
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi, one_smul]
  have hA'2 : (l⁻¹ • M) * (l⁻¹ • M) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hAA, smul_smul, smul_smul]
    rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
  obtain ⟨Hm, J, hHU, hHA⟩ := exists_split_unitary_normal_form h h2 hU' hA'2
  set HG := uGL h Hm hHU with hHG
  have hHi : (((HG : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (Hm.map h.bar)ᵀ := rfl
  have hconj : (((HG : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M *
      ((HG : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = l • signMat K J := by
    rw [hHi, coe_uGL]
    have e : M = l • (l⁻¹ • M) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
      Matrix.one_mul]
  have hHH : Hm * (Hm.map h.bar)ᵀ = 1 := mul_eq_one_comm.1 hHU
  have hJ : ∃ a ∈ J, ∃ b, b ∉ J := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hs, hsJ⟩ : ∃ s : K, s ≠ 0 ∧ signMat K J = s • 1 := by
      by_cases hne : J.Nonempty
      · obtain ⟨a, ha⟩ := hne
        refine ⟨-1, neg_ne_zero.2 one_ne_zero, ?_⟩
        ext i j
        simp [signMat, diagonal_apply, one_apply, hcon a ha i]
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        refine ⟨1, one_ne_zero, ?_⟩
        ext i j
        simp [signMat, diagonal_apply, one_apply, hne]
    have e : l⁻¹ • M = s • 1 := by
      calc l⁻¹ • M = (l⁻¹ • M) * (Hm * (Hm.map h.bar)ᵀ) := by rw [hHH, Matrix.mul_one]
        _ = (Hm * signMat K J) * (Hm.map h.bar)ᵀ := by rw [← Matrix.mul_assoc, hHA]
        _ = s • 1 := by
            rw [hsJ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hHH]
    apply hns (Units.mk0 (l * s) (mul_ne_zero hl0 hs))
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar]
    change M = _
    have e2 : M = l • (l⁻¹ • M) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    rw [e2, e, smul_smul, Matrix.smul_one_eq_diagonal]
    rfl
  obtain ⟨a, ha, b, hb⟩ := hJ
  have hct := uConjAut_conj_eq h hn (A := A) (A' := uSign h J) (H := ⟨HG, uGL_mem h _ _⟩) hl0
    (by rw [coe_uSign]; exact hconj)
  refine isCyclic_oddCoreIn_of_conj B htB (uConjAut h (by omega) (⟨HG, uGL_mem h _ _⟩ : uU h n)⁻¹)
    ?_
  rw [htA, hct]
  exact isCyclic_oddCoreIn_uSign h hp2 hn hinj (inn_le_map_conj hB _) ha hb

theorem isCyclic_oddCoreIn_innerPaired (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ B)
    {t : MulAut (StatedProj (StatedSU n (p ^ f) K))} (htB : t ∈ B)
    {A : uU h n} (htA : t = uConjAut h (by omega) A) {l : K} (hl0 : l ≠ 0)
    (hlN : h.norm l = -1)
    (hAA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (l ^ 2) • 1) :
    IsCyclic ↥(oddCoreIn B t) := by
  have := h.finite
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_ne_two h hp2
  set M := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  have hU : (M.map h.bar)ᵀ * M = 1 := (mem_uU h).1 A.2
  have hNi : h.bar l⁻¹ * l⁻¹ = -1 := by
    rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hlN, inv_neg, inv_one]
  have hU' : ((l⁻¹ • M).map h.bar)ᵀ * (l⁻¹ • M) = -1 := by
    rw [show (l⁻¹ • M).map h.bar = h.bar l⁻¹ • M.map h.bar by
      ext i j; simp [map_mul]]
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi, neg_one_smul]
  have hA'2 : (l⁻¹ • M) * (l⁻¹ • M) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hAA, smul_smul, smul_smul]
    rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
  obtain ⟨m, rfl⟩ := exists_half_of_antiunitary h h2 hU' hA'2
  have hm : 2 ≤ m := by omega
  obtain ⟨Hm, hHU, hHA⟩ := exists_paired_unitary_normal_form h h2 hU' hA'2 hl0 hlN
  set HG := uGL h Hm hHU with hHG
  have hHi : (((HG : GL (Fin (m + m)) K)⁻¹ : GL (Fin (m + m)) K) :
      Matrix (Fin (m + m)) (Fin (m + m)) K) = (Hm.map h.bar)ᵀ := rfl
  have hconj : (((HG : GL (Fin (m + m)) K)⁻¹ : GL (Fin (m + m)) K) :
      Matrix (Fin (m + m)) (Fin (m + m)) K) * M *
      ((HG : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
        (1 : K) • ((uPairA (m := m) h h2 hl0 hlN : GL (Fin (m + m)) K) :
          Matrix (Fin (m + m)) (Fin (m + m)) K) := by
    rw [hHi, coe_uGL, coe_uPairA, one_smul]
    have e : M = l • (l⁻¹ • M) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
      Matrix.one_mul, prA, ← map_smul, fromBlocks_smul]
    congr 2
    · rw [smul_zero]
    · rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    · rw [smul_smul, ← sq]
    · rw [smul_zero]
  have hct := uConjAut_conj_eq h hn (A := A) (A' := uPairA h h2 hl0 hlN)
    (H := ⟨HG, uGL_mem h _ _⟩) one_ne_zero hconj
  refine isCyclic_oddCoreIn_of_conj B htB
    (uConjAut h (by omega) (⟨HG, uGL_mem h _ _⟩ : uU h (m + m))⁻¹) ?_
  rw [htA, hct]
  exact isCyclic_oddCoreIn_uPairA h hp2 h2 hm hinj (inn_le_map_conj hB _) hl0 hlN

include h in
theorem conj_injective_psu (hp2 : p ≠ 2) (hn : 3 ≤ n) :
    Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hnq : (n, p ^ f) ≠ (3, 2) := fun e => by
    have hodd : Odd (p ^ f) := (h.prime.odd_of_ne_two hp2).pow
    rw [(Prod.mk.inj e).2] at hodd
    exact absurd hodd (by decide)
  have hsimple : IsSimpleGroup (StatedProj (StatedSU n (p ^ f) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f h.card_eq_sq n hn hnq
  have hperfSU : Group.IsPerfect (StatedSU n (p ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU h.card_eq_sq hn hnq
  have hperf : Group.IsPerfect (StatedProj (StatedSU n (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hcenter : Subgroup.center (StatedProj (StatedSU n (p ^ f) K)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (StatedProj (StatedSU n (p ^ f) K))) with h | h
    · exact h
    · exfalso
      have hcomm : ⁅(⊤ : Subgroup (StatedProj (StatedSU n (p ^ f) K))), ⊤⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x _ y _ =>
          Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y
      have htop : ⁅(⊤ : Subgroup (StatedProj (StatedSU n (p ^ f) K))), ⊤⁆ = ⊤ :=
        hperf.commutator_eq_top
      obtain ⟨a, ha⟩ := exists_ne (1 : StatedProj (StatedSU n (p ^ f) K))
      have hmem : a ∈ ⁅(⊤ : Subgroup (StatedProj (StatedSU n (p ^ f) K))), ⊤⁆ :=
        htop ▸ Subgroup.mem_top a
      rw [hcomm, Subgroup.mem_bot] at hmem
      exact ha hmem
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hcomm : ∀ y : StatedProj (StatedSU n (p ^ f) K), x * y = y * x := by
    intro y
    have := congrArg (fun α : MulAut (StatedProj (StatedSU n (p ^ f) K)) => α y)
      (MonoidHom.mem_ker.1 hx)
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [this]
  have hz : x ∈ Subgroup.center (StatedProj (StatedSU n (p ^ f) K)) :=
    Subgroup.mem_center_iff.mpr fun y => (hcomm y).symm
  rw [hcenter, Subgroup.mem_bot] at hz
  exact hz

end Psu

open Psu

section Main

variable {p f n : ℕ} {K : Type} [Field K]

theorem oddCoreCyclic_psu (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hn : 3 ≤ n) :
    OddCoreCyclic (StatedProj (StatedSU n (p ^ f) K)) := by
  intro B hB t htB ht
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hinj := conj_injective_psu h hp2 hn
  have hq' : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨_, e⟩ => by
    have hodd : Odd (p ^ f) := (h.prime.odd_of_ne_two hp2).pow
    rw [e] at hodd
    exact absurd hodd (by decide)
  obtain ⟨A, φ, hα⟩ := exists_uConjAut_mul_uFieldAut h hn hq' t
  have hsq : (uConjAut h (by omega) A * uFieldAut h (by omega) φ) ^ 2 = 1 := by
    rw [← hα, ← ht, pow_orderOf_eq_one]
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  rcases uFieldAut_eq_or_of_sq h hn hq' hsq with rfl | hφ
  ·
    rw [map_one, mul_one] at hα hsq
    rw [← map_pow] at hsq
    obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hn _).1 hsq
    have hAA : Am * Am = (c : K) • 1 := by
      have e := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar]
        at e
      rw [← pow_two, e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have hU : (Am.map h.bar)ᵀ * Am = 1 := (mem_uU h).1 A.2
    have hN : h.norm (c : K) = 1 := by
      have e : ((Am * Am).map h.bar)ᵀ * (Am * Am) = 1 := by
        rw [Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ Am Am, hU,
          Matrix.one_mul, hU]
      rw [hAA] at e
      have e1 := congrFun (congrFun e ⟨0, by omega⟩) ⟨0, by omega⟩
      simp [Matrix.mul_apply, Matrix.one_apply] at e1
      rw [UnitaryFieldData.norm, mul_comm]
      simpa [Matrix.smul_apply, Matrix.one_apply] using e1
    obtain ⟨l, hl0, hlc⟩ := exists_sq_eq_of_norm_eq_one h hp2 hN
    have hAA' : Am * Am = (l ^ 2) • 1 := by rw [hAA, hlc]
    have hNl : h.norm l * h.norm l = 1 := by
      rw [← hN, ← hlc, UnitaryFieldData.norm, UnitaryFieldData.norm, map_pow]
      ring
    rcases mul_self_eq_one_iff.1 hNl with hN1 | hN1
    · have hns : ∀ c : Kˣ, (A : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) c := by
        intro c' e
        have h1 : uConjAut h (by omega) A = 1 := (uConjAut_eq_one_iff h hn A).2 ⟨c', e⟩
        rw [h1] at hα
        rw [hα, orderOf_one] at ht
        exact absurd ht (by decide)
      exact isCyclic_oddCoreIn_innerSplit h hp2 hn hinj hB htB hα hl0 hN1 hAA' hns
    · exact isCyclic_oddCoreIn_innerPaired h hp2 hn hinj hB htB hα hl0 hN1 hAA'
  ·
    have hφe : φ = barEq h := RingEquiv.ext hφ
    subst hφe
    rw [graph_sq] at hsq
    obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hn _).1 hsq
    have hAc : Am * Am.map h.bar = (c : K) • 1 := by
      have e := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
      simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, coe_uGlAut]
        at e
      change ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (barEq h) = _
      rw [e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [hα, graph_oddCoreIn_eq_bot h hp2 hn hinj hB hAc]
    infer_instance

theorem no911_psu {Y : Type} [Group Y] [Finite Y] (hn : 3 ≤ n) (hp2 : p ≠ 2)
    (hL : LieModel Y .PSU n p f) : No911 Y := by
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · obtain ⟨⟨hp, hf, -, -⟩, K', _, _, hKc, ⟨θ⟩⟩ := hc
    have h : UnitaryFieldData p f K' := ⟨hp, hf, by rw [hKc, ← pow_mul, mul_comm]⟩
    have := h.finite
    exact no911_of_mulEquiv θ (no911_of_oddCoreCyclic (oddCoreCyclic_psu h hp2 hn))
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
