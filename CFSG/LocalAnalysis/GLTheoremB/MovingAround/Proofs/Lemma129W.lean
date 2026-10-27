module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129W

@[expose] def kconj {Y : Type*} [Group Y] (a : Y) (K : Subgroup Y) (i : ℕ) : Subgroup Y :=
  K.map (MulAut.conj (a ^ i)).toMonoidHom

@[expose] def kstar {Y : Type*} [Group Y] (p : ℕ) (a : Y) (K : Subgroup Y) : Subgroup Y :=
  ⨆ i : Fin p, kconj a K i

section Regular

variable {Y : Type*} [Group Y] {Q : Type*} [Group Q] [Fintype Q] [DecidableEq Q]

private def conjEmb (ρ : Q →* Y) (K : Subgroup Y) (x : Q) : K →* Y :=
  (MulAut.conj (ρ x)).toMonoidHom.comp K.subtype

private theorem conjEmb_apply (ρ : Q →* Y) (K : Subgroup Y) (x : Q) (k : K) :
    conjEmb ρ K x k = ρ x * k * (ρ x)⁻¹ := rfl

private theorem conjEmb_injective (ρ : Q →* Y) (K : Subgroup Y) (x : Q) :
    Function.Injective (conjEmb ρ K x) :=
  (MulAut.conj (ρ x)).injective.comp K.subtype_injective

private theorem conjEmb_one (ρ : Q →* Y) (K : Subgroup Y) (k : K) : conjEmb ρ K 1 k = k := by
  simp [conjEmb_apply]

private abbrev ConjComm (ρ : Q →* Y) (K : Subgroup Y) : Prop :=
  Pairwise fun x y : Q => ∀ k l : K, Commute (conjEmb ρ K x k) (conjEmb ρ K y l)

variable {ρ : Q →* Y} {K : Subgroup Y}

private def prodHom (hc : ConjComm ρ K) : (Q → K) →* Y :=
  MonoidHom.noncommPiCoprod (conjEmb ρ K) hc

private theorem prodHom_mulSingle (hc : ConjComm ρ K) (x : Q) (k : K) :
    prodHom hc (Pi.mulSingle x k) = ρ x * k * (ρ x)⁻¹ :=
  MonoidHom.noncommPiCoprod_mulSingle (conjEmb ρ K) x k

private def shiftHom (K : Type*) [Group K] (q : Q) : (Q → K) →* (Q → K) where
  toFun f x := f (q⁻¹ * x)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem shiftHom_mulSingle {K : Type*} [Group K] (q x : Q) (k : K) :
    shiftHom K q (Pi.mulSingle x k) = Pi.mulSingle (q * x) k := by
  funext y
  simp only [shiftHom, MonoidHom.coe_mk, OneHom.coe_mk, Pi.mulSingle_apply, inv_mul_eq_iff_eq_mul]

private theorem prodHom_shift (hc : ConjComm ρ K) (q : Q) (f : Q → K) :
    prodHom hc (fun x => f (q⁻¹ * x)) = ρ q * prodHom hc f * (ρ q)⁻¹ := by
  have key : (prodHom hc).comp (shiftHom K q) =
      (MulAut.conj (ρ q)).toMonoidHom.comp (prodHom hc) := by
    refine MonoidHom.pi_ext fun x k => ?_
    simp only [MonoidHom.coe_comp, Function.comp_apply, shiftHom_mulSingle, prodHom_mulSingle,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul]
    group
  exact DFunLike.congr_fun key f

private def wreathHom (hc : ConjComm ρ K) : RegularWreathProduct ↥K Q →* Y where
  toFun w := prodHom hc w.left * ρ w.right
  map_one' := by simp
  map_mul' w₁ w₂ := by
    simp only [RegularWreathProduct.mul_left, RegularWreathProduct.mul_right, map_mul,
      prodHom_shift]
    group

private theorem wreathHom_apply (hc : ConjComm ρ K) (w : RegularWreathProduct ↥K Q) :
    wreathHom hc w = prodHom hc w.left * ρ w.right := rfl

private theorem wreathHom_mulSingle (hc : ConjComm ρ K) (x : Q) (k : K) :
    wreathHom hc ⟨Pi.mulSingle x k, 1⟩ = ρ x * k * (ρ x)⁻¹ := by
  rw [wreathHom_apply]
  simp [prodHom_mulSingle]

private theorem prodHom_range (hc : ConjComm ρ K) :
    (prodHom hc).range = ⨆ x : Q, (conjEmb ρ K x).range :=
  MonoidHom.noncommPiCoprod_range (conjEmb ρ K)

private theorem prodHom_injective (hK : ∀ z ∈ K, (∀ y ∈ K, z * y = y * z) → z = 1)
    (hc : ConjComm ρ K) : Function.Injective (prodHom hc) := by
  refine MonoidHom.injective_noncommPiCoprod_of_iSupIndep (conjEmb ρ K) ?_ (conjEmb_injective ρ K)
  intro x
  rw [Subgroup.disjoint_def]
  rintro z ⟨k₀, rfl⟩ hz
  have hle : (⨆ y, ⨆ (_ : y ≠ x), (conjEmb ρ K y).range) ≤
      Subgroup.centralizer ((conjEmb ρ K x).range : Set Y) := by
    refine iSup₂_le fun y hy => ?_
    rintro _ ⟨l, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (hc hy l k).symm.eq
  have hz' := Subgroup.mem_centralizer_iff.1 (hle hz)
  have hk₀ : k₀ = 1 := by
    refine Subtype.ext (hK k₀ k₀.2 fun y hy => ?_)
    have h := hz' (conjEmb ρ K x ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (conjEmb_injective ρ K x h).symm
  rw [hk₀, map_one]

private theorem prodHom_range_le_normalizer (hc : ConjComm ρ K) :
    (prodHom hc).range ≤ Subgroup.normalizer (K : Set Y) := by
  rw [prodHom_range]
  refine iSup_le fun x => ?_
  rw [Subgroup.le_normalizer_iff]
  rintro _ ⟨l, rfl⟩ k hk
  by_cases hx : x = 1
  · subst hx
    simp only [conjEmb_apply, map_one, one_mul, inv_one, mul_one]
    exact K.mul_mem (K.mul_mem l.2 hk) (K.inv_mem l.2)
  · have h : conjEmb ρ K x l * k = k * conjEmb ρ K x l := by
      have := (hc hx l ⟨k, hk⟩).eq
      rwa [conjEmb_one] at this
    rw [h, mul_inv_cancel_right]
    exact hk

private theorem wreathHom_injective (hK : ∀ z ∈ K, (∀ y ∈ K, z * y = y * z) → z = 1)
    (hρ : ∀ q : Q, q ≠ 1 → ρ q ∉ Subgroup.normalizer (K : Set Y)) (hc : ConjComm ρ K) :
    Function.Injective (wreathHom hc) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have hw' : prodHom hc w.left * ρ w.right = 1 := hw
  have h1 : w.right = 1 := by
    by_contra hne
    refine hρ _ hne ?_
    rw [eq_inv_of_mul_eq_one_right hw']
    exact Subgroup.inv_mem _ (prodHom_range_le_normalizer hc ⟨w.left, rfl⟩)
  have h2 : w.left = 1 := by
    apply prodHom_injective hK hc
    rw [h1, map_one, mul_one] at hw'
    rw [hw', map_one]
  exact RegularWreathProduct.ext h2 h1

private theorem wreathHom_range (hc : ConjComm ρ K) :
    (wreathHom hc).range = (⨆ x : Q, (conjEmb ρ K x).range) ⊔ ρ.range := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ⟨w.right, rfl⟩)
    rw [← prodHom_range hc]
    exact ⟨w.left, rfl⟩
  · refine sup_le (iSup_le fun x => ?_) ?_
    · rintro _ ⟨k, rfl⟩
      exact ⟨⟨Pi.mulSingle x k, 1⟩, wreathHom_mulSingle hc x k⟩
    · rintro _ ⟨q, rfl⟩
      exact ⟨⟨1, q⟩, by simp [wreathHom_apply]⟩

end Regular

private def zpHom {Y : Type*} [Group Y] (p : ℕ) [NeZero p] (a : Y) (ha : a ^ p = 1) :
    Multiplicative (ZMod p) →* Y where
  toFun q := a ^ (Multiplicative.toAdd q).val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, ZMod.val_add]
    rw [← pow_eq_pow_mod _ ha, pow_add]

theorem exists_wreath_equiv {Y : Type*} [Group Y] [Finite Y] (p : ℕ) [Fact p.Prime]
    (K : Subgroup Y) (a : Y) (ha : a ^ p = 1)
    (hcomm : ∀ i j : Fin p, i ≠ j → ∀ x ∈ kconj a K i, ∀ y ∈ kconj a K j, x * y = y * x)
    (hcenter : ∀ z ∈ K, (∀ y ∈ K, z * y = y * z) → z = 1)
    (hcap : ∀ m : ℕ, 0 < m → m < p → a ^ m ∉ Subgroup.normalizer (K : Set Y)) :
    ∃ e : ↥(kstar p a K ⊔ Subgroup.zpowers a) ≃* RegularWreathProduct ↥K (Multiplicative (ZMod p)),
      RegularWreathProduct.rightHom
        (e ⟨a, Subgroup.mem_sup_right (Subgroup.mem_zpowers a)⟩) = Multiplicative.ofAdd (1 : ZMod p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let ρ : Multiplicative (ZMod p) →* Y := zpHom p a ha
  have hρ_apply : ∀ q, ρ q = a ^ (Multiplicative.toAdd q).val := fun _ => rfl
  have hc : ConjComm ρ K := by
    intro x y hxy k l
    have hne : (⟨(Multiplicative.toAdd x).val, ZMod.val_lt _⟩ : Fin p) ≠
        ⟨(Multiplicative.toAdd y).val, ZMod.val_lt _⟩ := by
      intro h
      exact hxy (Multiplicative.toAdd.injective (ZMod.val_injective p (Fin.mk.inj h)))
    exact hcomm _ _ hne _ (Subgroup.mem_map.2 ⟨k, k.2, rfl⟩) _ (Subgroup.mem_map.2 ⟨l, l.2, rfl⟩)
  have hρ : ∀ q : Multiplicative (ZMod p), q ≠ 1 → ρ q ∉ Subgroup.normalizer (K : Set Y) := by
    intro q hq
    have h0 : (Multiplicative.toAdd q).val ≠ 0 := by
      intro h
      exact hq (Multiplicative.toAdd.injective ((ZMod.val_eq_zero _).1 h))
    exact hcap _ (Nat.pos_of_ne_zero h0) (ZMod.val_lt _)
  have hrange : (⨆ x : Multiplicative (ZMod p), (conjEmb ρ K x).range) ⊔ ρ.range =
      kstar p a K ⊔ Subgroup.zpowers a := by
    congr 1
    · apply le_antisymm
      · refine iSup_le fun x => ?_
        refine le_trans ?_ (le_iSup (fun i : Fin p => kconj a K i)
          ⟨(Multiplicative.toAdd x).val, ZMod.val_lt _⟩)
        rintro _ ⟨k, rfl⟩
        exact Subgroup.mem_map.2 ⟨k, k.2, rfl⟩
      · refine iSup_le fun i => ?_
        refine le_trans ?_ (le_iSup (fun x => (conjEmb ρ K x).range)
          (Multiplicative.ofAdd ((i : ℕ) : ZMod p)))
        rintro _ ⟨k, hk, rfl⟩
        refine ⟨⟨k, hk⟩, ?_⟩
        have hval : ((i : ℕ) : ZMod p).val = (i : ℕ) := ZMod.val_cast_of_lt i.2
        rw [conjEmb_apply, hρ_apply]
        simp only [toAdd_ofAdd, hval]
        rfl
    · apply le_antisymm
      · rintro _ ⟨q, rfl⟩
        exact Subgroup.npow_mem_zpowers a _
      · rw [Subgroup.zpowers_le]
        refine ⟨Multiplicative.ofAdd 1, ?_⟩
        simp [hρ_apply, ZMod.val_one]
  have hinj := wreathHom_injective hcenter hρ hc
  have hrange' := (wreathHom_range hc).trans hrange
  have hgen : wreathHom hc ⟨1, Multiplicative.ofAdd 1⟩ = a := by
    simp [wreathHom_apply, hρ_apply, ZMod.val_one]
  refine ⟨(MulEquiv.subgroupCongr hrange'.symm).trans (MonoidHom.ofInjective hinj).symm, ?_⟩
  have key : (MonoidHom.ofInjective hinj).symm
      ⟨a, ⟨⟨1, Multiplicative.ofAdd 1⟩, hgen⟩⟩ = ⟨1, Multiplicative.ofAdd 1⟩ := by
    apply hinj
    rw [MonoidHom.apply_ofInjective_symm]
    exact hgen.symm
  exact congrArg RegularWreathProduct.rightHom key

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129W

end
