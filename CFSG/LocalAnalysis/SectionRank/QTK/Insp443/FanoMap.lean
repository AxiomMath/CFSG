module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermFano
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch7Fano
public import CFSG.Quasithin.Vol2.KGFactC31Concl

public section

namespace CFSG.SectionRank.QTK.Insp443.PermKit

open Equiv CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native CFSG.Quasithin.H13
  CFSG.Quasithin.H13.Fano CFSG.SectionRank.QTK.Insp443.PermKit.Native
open scoped Matrix

@[expose] def pmask (p : FanoPoint) : ℕ := vmask3 p.1

theorem maskVec_vmask3 (v : Fin 3 → ZMod 2) : maskVec 3 (vmask3 v) = v := by
  revert v
  decide

theorem pmask_bounds (p : FanoPoint) : 1 ≤ pmask p ∧ pmask p < 8 := by
  revert p
  decide

@[expose] def pointOf (q : ℕ) (h1 : 1 ≤ q) (h8 : q < 8) : FanoPoint :=
  ⟨maskVec 3 q, by interval_cases q <;> decide⟩

theorem pmask_pointOf {q : ℕ} (h1 : 1 ≤ q) (h8 : q < 8) : pmask (pointOf q h1 h8) = q := by
  interval_cases q <;> rfl

@[expose] noncomputable def rowMap (rows : List ℕ) : Multiplicative (Fin 6 → ZMod 2) →* PMod where
  toFun c := Multiplicative.ofAdd fun p =>
    ∑ i : Fin 6, Multiplicative.toAdd c i * rowBit rows i (pmask p)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext p
    simp
  map_mul' c d := by
    apply Multiplicative.toAdd.injective
    funext p
    simp only [toAdd_ofAdd, toAdd_mul, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem toAdd_rowMap (rows : List ℕ) (c : Multiplicative (Fin 6 → ZMod 2)) (p : FanoPoint) :
    Multiplicative.toAdd (rowMap rows c) p =
      ∑ i : Fin 6, Multiplicative.toAdd c i * rowBit rows i (pmask p) := rfl

variable {rows : List ℕ}

theorem rowMap_mem (hev : ∀ i : Fin 6, ∑ p : FanoPoint, rowBit rows i (pmask p) = 0)
    (c : Multiplicative (Fin 6 → ZMod 2)) : rowMap rows c ∈ fanoCore := by
  rw [mem_fanoCore]
  simp only [toAdd_rowMap]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hev, mul_zero, Finset.sum_const_zero]

theorem rowMap_injective (hrl : rows.length = 6)
    (hind : ∀ m < 64, (∀ q, 1 ≤ q → q < 8 → bsum rows m q = false) → m = 0) :
    Function.Injective (rowMap rows) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨m, hm, hmc⟩ := exists_maskVec (Multiplicative.toAdd c)
  have hm0 : m = 0 := hind m (by simpa using hm) fun q hq1 hq8 => by
    have h1 := congrArg (fun F : PMod => Multiplicative.toAdd F (pointOf q hq1 hq8)) hc
    simp only [toAdd_rowMap, toAdd_one, Pi.zero_apply] at h1
    rw [← hmc, pmask_pointOf, sum_maskVec_eq_ind_bsum hrl] at h1
    by_contra hb
    rw [Bool.not_eq_false] at hb
    rw [hb, if_pos rfl] at h1
    exact one_ne_zero h1
  apply Multiplicative.toAdd.injective
  rw [← hmc, hm0]
  funext i
  simp [maskVec]

variable {G : Type*} [Group G] {w : Fin 6 → G} (hw : EBasis w)

@[expose] noncomputable def fanoEquiv
    (hev : ∀ i : Fin 6, ∑ p : FanoPoint, rowBit rows i (pmask p) = 0) (hrl : rows.length = 6)
    (hind : ∀ m < 64, (∀ q, 1 ≤ q → q < 8 → bsum rows m q = false) → m = 0) :
    ↥(eSub hw) ≃* ↥fanoCore :=
  MulEquiv.ofBijective
    (((rowMap rows).codRestrict fanoCore (rowMap_mem hev)).comp (ecoords hw).toMonoidHom)
    (Function.Injective.bijective_of_nat_card_le
      (fun x y hxy => (ecoords hw).injective
        (rowMap_injective hrl hind (congrArg Subtype.val hxy)))
      (by rw [card_fanoCore, card_eSub]; norm_num))

theorem coe_fanoEquiv (hev : ∀ i : Fin 6, ∑ p : FanoPoint, rowBit rows i (pmask p) = 0)
    (hrl : rows.length = 6)
    (hind : ∀ m < 64, (∀ q, 1 ≤ q → q < 8 → bsum rows m q = false) → m = 0) (u : ↥(eSub hw)) :
    ((fanoEquiv hw hev hrl hind u : ↥fanoCore) : PMod) = rowMap rows (ecoords hw u) := rfl

theorem fanoEquiv_conj (hev : ∀ i : Fin 6, ∑ p : FanoPoint, rowBit rows i (pmask p) = 0)
    (hrl : rows.length = 6)
    (hind : ∀ m < 64, (∀ q, 1 ≤ q → q < 8 → bsum rows m q = false) → m = 0)
    {a : Fin 3 → G} (ha : EBasis a) {g : G} (hgW : g ∈ eNorm hw) (hgA : g ∈ eNorm ha)
    (hfano : ∀ j : Fin 6, ∀ q, 1 ≤ q → q < 8 →
      ∑ i : Fin 6, eMat hw ⟨g, hgW⟩ i j * rowBit rows i q =
        rowBit rows j (vmask3 ((eMat ha ⟨g, hgA⟩)ᵀ *ᵥ maskVec 3 q)))
    {γ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hγ : ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (eMat ha ⟨g, hgA⟩)ᵀ)
    (u u' : ↥(eSub hw)) (hu : (u' : G) = g * u * g⁻¹) :
    ((fanoEquiv hw hev hrl hind u' : ↥fanoCore) : PMod) =
      fanoPermAct γ (fanoEquiv hw hev hrl hind u) := by
  rw [coe_fanoEquiv, coe_fanoEquiv]
  apply Multiplicative.toAdd.injective
  funext p
  rw [fanoPermAct_apply, toAdd_rowMap, toAdd_rowMap, ecoords_conj hw ⟨g, hgW⟩ u u' hu]
  set c := Multiplicative.toAdd (ecoords hw u)
  have hp : pmask (fanoPointAct γ⁻¹ p) =
      vmask3 ((eMat ha ⟨g, hgA⟩)ᵀ *ᵥ maskVec 3 (pmask p)) := by
    rw [pmask, fanoPointAct_val, hγ, pmask, maskVec_vmask3]
  rw [hp]
  obtain ⟨hq1, hq8⟩ := pmask_bounds p
  simp only [← hfano _ _ hq1 hq8, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end CFSG.SectionRank.QTK.Insp443.PermKit

end
