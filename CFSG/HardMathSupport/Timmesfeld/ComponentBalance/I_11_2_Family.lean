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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

variable {G : Type*} [Group G]

@[expose] def centreIn (H : Subgroup G) : Subgroup G := H ⊓ Subgroup.centralizer (H : Set G)

theorem mem_centreIn {H : Subgroup G} {x : G} :
    x ∈ centreIn H ↔ x ∈ H ∧ ∀ g ∈ H, g * x = x * g := by
  unfold centreIn
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

theorem centreIn_le (H : Subgroup G) : centreIn H ≤ H := inf_le_left

theorem centreIn_comm {H : Subgroup G} {a b : G} (ha : a ∈ centreIn H) (hb : b ∈ centreIn H) :
    a * b = b * a :=
  (mem_centreIn.1 hb).2 a (centreIn_le H ha)

theorem map_subtype_center (H : Subgroup G) :
    (Subgroup.center H).map H.subtype = centreIn H := by
  ext x
  rw [Subgroup.mem_map, mem_centreIn]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun g hg => ?_⟩
    have := Subgroup.mem_center_iff.1 hy ⟨g, hg⟩
    exact congrArg Subtype.val this
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hc g g.2), rfl⟩

theorem card_centreIn (H : Subgroup G) : Nat.card (centreIn H) = Nat.card (Subgroup.center H) := by
  rw [← map_subtype_center H]
  exact Subgroup.card_map_of_injective H.subtype_injective

variable {ι : Type*} (L : ι → Subgroup G)

abbrev CommFam : Prop :=
  Pairwise fun i j : ι => ∀ x y : G, x ∈ L i → y ∈ L j → Commute x y

abbrev restSup (k : ι) : Subgroup G := ⨆ (j) (_ : j ≠ k), L j

variable {L}

theorem CommFam.of_mul_comm
    (h : ∀ i j, i ≠ j → ∀ a ∈ L i, ∀ b ∈ L j, a * b = b * a) : CommFam L :=
  fun i j hij x y hx hy => h i j hij x hx y hy

theorem mem_restSup_of_mem {k j : ι} (hjk : j ≠ k) {x : G} (hx : x ∈ L j) : x ∈ restSup L k :=
  (le_iSup₂ (f := fun (j : ι) (_ : j ≠ k) => L j) j hjk) hx

theorem CommFam.le_centralizer (h : CommFam L) {i j : ι} (hij : j ≠ i) :
    L j ≤ Subgroup.centralizer (L i : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact (h hij.symm g x hg hx).eq

theorem CommFam.restSup_le_centralizer (h : CommFam L) (k : ι) :
    restSup L k ≤ Subgroup.centralizer (L k : Set G) :=
  iSup₂_le fun _ hj => h.le_centralizer hj

theorem CommFam.le_centralizer_restSup (h : CommFam L) (k : ι) :
    L k ≤ Subgroup.centralizer (restSup L k : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have := h.restSup_le_centralizer k hg
  rw [Subgroup.mem_centralizer_iff] at this
  exact (this x hx).symm

theorem CommFam.mem_centreIn_of_eq_mul (h : CommFam L) {k : ι} {e y c : G} (he : e ∈ L k)
    (hy : y ∈ restSup L k) (hc : ∀ g ∈ L k, g * c = c * g) (hec : e = y * c) :
    e ∈ centreIn (L k) := by
  refine mem_centreIn.2 ⟨he, ?_⟩
  have hy' : ∀ g ∈ L k, g * y = y * g := fun g hg =>
    Subgroup.mem_centralizer_iff.1 (h.restSup_le_centralizer k hy) g hg
  subst hec
  intro g hg
  rw [← mul_assoc, hy' g hg, mul_assoc, hc g hg, ← mul_assoc]

theorem CommFam.mem_centreIn_of_eq_mul_of_mem_centralizer (h : CommFam L) {k : ι} {e y c : G}
    (he : e ∈ L k) (hy : y ∈ restSup L k)
    (hc : c ∈ Subgroup.centralizer ((⨆ i, L i : Subgroup G) : Set G)) (hec : e = y * c) :
    e ∈ centreIn (L k) :=
  h.mem_centreIn_of_eq_mul he hy
    (fun g hg => Subgroup.mem_centralizer_iff.1 hc g (le_iSup L k hg)) hec

theorem CommFam.centreIn_le_centralizer_iSup (h : CommFam L) (k : ι) :
    centreIn (L k) ≤ Subgroup.centralizer ((⨆ i, L i : Subgroup G) : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  have hle : (⨆ i, L i : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    refine iSup_le fun i => ?_
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hik : i = k
    · subst hik
      exact (mem_centreIn.1 hz).2 g hg
    · exact (h (Ne.symm hik) z g (centreIn_le (L k) hz) hg).eq.symm
  intro g hg
  have := hle hg
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

theorem CommFam.centreIn_le_centreIn_iSup (h : CommFam L) (k : ι) :
    centreIn (L k) ≤ centreIn (⨆ i, L i) :=
  le_inf ((centreIn_le _).trans (le_iSup L k)) (h.centreIn_le_centralizer_iSup k)

theorem CommFam.centreIn_iSup_inf_eq (h : CommFam L) (k : ι) :
    centreIn (⨆ i, L i) ⊓ L k = centreIn (L k) := by
  refine le_antisymm ?_ (le_inf (h.centreIn_le_centreIn_iSup k) (centreIn_le _))
  intro x hx
  obtain ⟨hxJ, hxk⟩ := Subgroup.mem_inf.1 hx
  exact mem_centreIn.2 ⟨hxk, fun g hg => (mem_centreIn.1 hxJ).2 g (le_iSup L k hg)⟩

theorem CommFam.inf_restSup_le_centreIn (h : CommFam L) (k : ι) :
    L k ⊓ restSup L k ≤ centreIn (L k) ⊓ centreIn (⨆ i, L i) := by
  intro x hx
  obtain ⟨hxk, hxr⟩ := Subgroup.mem_inf.1 hx
  have hZk : x ∈ centreIn (L k) :=
    h.mem_centreIn_of_eq_mul hxk hxr (c := 1) (fun g _ => by simp) (by simp)
  exact Subgroup.mem_inf.2 ⟨hZk, h.centreIn_le_centreIn_iSup k hZk⟩

theorem CommFam.inf_restSup_le_centreIn_left (h : CommFam L) (k : ι) :
    L k ⊓ restSup L k ≤ centreIn (L k) :=
  (h.inf_restSup_le_centreIn k).trans inf_le_left

section Product

variable [Fintype ι]

@[expose] noncomputable def famProd (h : CommFam L) : (∀ i, L i) →* G := Subgroup.noncommPiCoprod h

theorem range_famProd (h : CommFam L) : (famProd h).range = ⨆ i, L i :=
  Subgroup.noncommPiCoprod_range

theorem famProd_mulSingle [DecidableEq ι] (h : CommFam L) (i : ι) (y : L i) :
    famProd h (Pi.mulSingle i y) = (y : G) :=
  Subgroup.noncommPiCoprod_mulSingle i y

theorem famProd_apply (h : CommFam L) (f : ∀ i, L i) :
    famProd h f = Finset.noncommProd Finset.univ (fun i => (f i : G))
      (fun i _ j _ hij => h hij _ _ (f i).prop (f j).prop) :=
  Subgroup.noncommPiCoprod_apply h f

theorem famProd_eq_mul_update [DecidableEq ι] (h : CommFam L) (f : ∀ i, L i) (k : ι) :
    famProd h f = (f k : G) * famProd h (Function.update f k 1) := by
  have : f = Pi.mulSingle k (f k) * Function.update f k 1 := by
    ext i
    by_cases hik : i = k
    · subst hik
      simp
    · simp [hik]
  conv_lhs => rw [this]
  rw [map_mul, famProd_mulSingle]

theorem famProd_update_mem_restSup [DecidableEq ι] (h : CommFam L) (f : ∀ i, L i) (k : ι) :
    famProd h (Function.update f k 1) ∈ restSup L k := by
  rw [famProd_apply]
  refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
  by_cases hik : i = k
  · subst hik
    simp
  · simp only [Function.update_of_ne hik]
    exact mem_restSup_of_mem hik (f i).2

theorem ker_famProd_apply_mem_centreIn [DecidableEq ι] (h : CommFam L) {f : ∀ i, L i}
    (hf : f ∈ (famProd h).ker) (k : ι) : (f k : G) ∈ centreIn (L k) := by
  have h1 : famProd h f = 1 := hf
  have h2 := famProd_eq_mul_update h f k
  rw [h1] at h2
  have hr := famProd_update_mem_restSup h f k
  have : (f k : G) = (famProd h (Function.update f k 1))⁻¹ := eq_inv_of_mul_eq_one_left h2.symm
  exact h.mem_centreIn_of_eq_mul (f k).2 (inv_mem hr) (c := 1) (fun g _ => by simp) (by rw [this]; simp)

theorem exists_famProd_eq (h : CommFam L) {x : G} (hx : x ∈ ⨆ i, L i) :
    ∃ f : ∀ i, L i, famProd h f = x := by
  rw [← range_famProd h] at hx
  exact hx

theorem CommFam.centreIn_iSup_eq_iSup (h : CommFam L) :
    centreIn (⨆ i, L i) = ⨆ i, centreIn (L i) := by
  classical
  refine le_antisymm ?_ (iSup_le fun k => h.centreIn_le_centreIn_iSup k)
  intro z hz
  obtain ⟨hzJ, hzc⟩ := mem_centreIn.1 hz
  obtain ⟨f, rfl⟩ := exists_famProd_eq h hzJ
  rw [famProd_apply]
  refine Subgroup.noncommProd_mem _ _ fun k _ => ?_
  refine le_iSup (fun i => centreIn (L i)) k ?_
  have h2 := famProd_eq_mul_update h f k
  have hr := famProd_update_mem_restSup h f k
  have hk : (f k : G) = famProd h f * (famProd h (Function.update f k 1))⁻¹ := by
    rw [h2]; simp
  refine h.mem_centreIn_of_eq_mul (f k).2 (y := (famProd h (Function.update f k 1))⁻¹ )
    (c := famProd h f) (inv_mem hr) (fun g hg => (hzc g (le_iSup L k hg)))
    ?_
  rw [hk]
  have hcomm : famProd h f * (famProd h (Function.update f k 1))⁻¹ =
      (famProd h (Function.update f k 1))⁻¹ * famProd h f := by
    have hrJ : famProd h (Function.update f k 1) ∈ ⨆ i, L i := by
      rw [← range_famProd h]; exact ⟨_, rfl⟩
    have hc : Commute (famProd h (Function.update f k 1)) (famProd h f) := hzc _ hrJ
    exact hc.inv_left.eq.symm
  exact hcomm

end Product

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance

end
