module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
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

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

theorem exists_perfect_factors_mul_comm {X : Type*} [Group X] {H K : Subgroup X}
    (hHK : ⁅H, K⁆ = ⊥) {h k : X} (hh : h ∈ H) (hk : k ∈ K) : h * k = k * h := by
  have h1 : ⁅h, k⁆ ∈ ⁅H, K⁆ := commutator_mem_commutator hh hk
  rw [hHK, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem exists_perfect_factors_le_normalizer {X : Type*} [Group X] {H K : Subgroup X}
    (hHK : ⁅H, K⁆ = ⊥) : K ≤ Subgroup.normalizer (H : Set X) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : k * h * k⁻¹ = h := by
      rw [← exists_perfect_factors_mul_comm hHK hh hk, mul_inv_cancel_right]
    rw [e]
    exact hh
  · intro hc
    have hc' : k * h * k⁻¹ * k⁻¹ = k⁻¹ * (k * h * k⁻¹) :=
      exists_perfect_factors_mul_comm hHK hc (K.inv_mem hk)
    have e : h = k * h * k⁻¹ := by
      calc h = k⁻¹ * (k * h * k⁻¹) * k := by group
        _ = k * h * k⁻¹ * k⁻¹ * k := by rw [← hc']
        _ = k * h * k⁻¹ := by group
    rw [e]
    exact hc

theorem exists_perfect_factors_commutator_commutator_eq_bot {P : Type*} [Group P]
    {K A B : Subgroup P} (hK : ∀ N : Subgroup P, ⁅K, N⁆ = ⊥) (hAB : ⁅A, B⁆ ≤ K) :
    ⁅⁅A, A⁆, B⁆ = ⊥ := by
  have hBA : ⁅B, A⁆ ≤ K := by
    rw [commutator_comm]
    exact hAB
  exact Subgroup.commutator_commutator_eq_bot_of_rotate
    (le_bot_iff.mp ((commutator_mono hAB le_rfl).trans (hK A).le))
    (le_bot_iff.mp ((commutator_mono hBA le_rfl).trans (hK A).le))

theorem exists_perfect_factors_normal_comap {P X : Type*} [Group P] [Group X]
    {D₁ D₂ : Subgroup X} (f : P →* X) (hD : D₁ ⊔ D₂ = f.range) (hcomm : ⁅D₁, D₂⁆ = ⊥) :
    (D₁.comap f).Normal := by
  have hle : f.range ≤ Subgroup.normalizer (D₁ : Set X) := by
    rw [← hD]
    exact sup_le Subgroup.le_normalizer (exists_perfect_factors_le_normalizer hcomm)
  refine ⟨fun n hn g => ?_⟩
  have hn' : f n ∈ D₁ := Subgroup.mem_comap.mp hn
  have hfg : f g ∈ f.range := MonoidHom.mem_range.mpr ⟨g, rfl⟩
  have hg := (Subgroup.mem_normalizer_iff.mp (hle hfg) (f n)).mp hn'
  show f (g * n * g⁻¹) ∈ D₁
  rw [map_mul, map_mul, map_inv]
  exact hg

theorem exists_perfect_factors_map_comap {P X : Type*} [Group P] [Group X] (f : P →* X)
    {D : Subgroup X} (hD : D ≤ f.range) : (D.comap f).map f = D :=
  Subgroup.map_comap_eq_self hD

theorem exists_perfect_factors_map_commutator {P X : Type*} [Group P] [Group X] (f : P →* X)
    {D : Subgroup X} (hD : Group.IsPerfect ↥D) (hmap : (D.comap f).map f = D) :
    (⁅D.comap f, D.comap f⁆).map f = D := by
  rw [map_commutator, hmap]
  exact Subgroup.isPerfect_iff.mp hD

theorem exists_perfect_factors_isPerfect_commutator {P X : Type*} [Group P] [Group X]
    (f : P →* X) (hker : f.ker ≤ Subgroup.center P) {D : Subgroup X}
    (hD : Group.IsPerfect ↥D) (hmap : (D.comap f).map f = D) :
    Group.IsPerfect ↥⁅D.comap f, D.comap f⁆ := by
  let g : ↥(D.comap f) →* ↥D :=
    { toFun := fun q => ⟨f (q : P), q.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f (a : P) (b : P)) }
  have hsurj : Function.Surjective g := by
    intro d
    have hd : (d : X) ∈ (D.comap f).map f := by
      rw [hmap]
      exact d.2
    obtain ⟨q, hq, hfq⟩ := Subgroup.mem_map.mp hd
    exact ⟨⟨q, hq⟩, Subtype.ext hfq⟩
  have hgker : g.ker ≤ Subgroup.center ↥(D.comap f) := by
    intro x hx
    have h1 : f (x : P) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have h2 : (x : P) ∈ Subgroup.center P := hker (MonoidHom.mem_ker.mpr h1)
    exact Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_center_iff.mp h2 (y : P))
  obtain ⟨-, hperf, -⟩ := CFSG.LocalCores.central_extension_derived_of_surjective g hsurj hgker hD
  haveI := hperf
  have hm : Group.IsPerfect ↥((commutator ↥(D.comap f)).map (D.comap f).subtype) :=
    Group.IsPerfect.map (D.comap f).subtype
  have hsub : (commutator ↥(D.comap f)).map (D.comap f).subtype = ⁅D.comap f, D.comap f⁆ := by
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hsub] at hm
  exact hm

theorem exists_perfect_factors {P X : Type*} [Group P] [Finite P] [Group X]
    (hP : Group.IsPerfect P) (f : P →* X) (hker : f.ker ≤ Subgroup.center P)
    (D₁ D₂ : Subgroup X) (hD : D₁ ⊔ D₂ = f.range) (hcomm : ⁅D₁, D₂⁆ = ⊥)
    (h₁ : Group.IsPerfect D₁) (h₂ : Group.IsPerfect D₂) :
    ⁅D₁.comap f, D₁.comap f⁆.Normal ∧ ⁅D₂.comap f, D₂.comap f⁆.Normal ∧
    ⁅⁅D₁.comap f, D₁.comap f⁆, ⁅D₂.comap f, D₂.comap f⁆⁆ = ⊥ ∧
    ⁅D₁.comap f, D₁.comap f⁆ ⊔ ⁅D₂.comap f, D₂.comap f⁆ = ⊤ ∧
    ⁅D₁.comap f, D₁.comap f⁆.map f = D₁ ∧ ⁅D₂.comap f, D₂.comap f⁆.map f = D₂ ∧
    Group.IsPerfect ↥⁅D₁.comap f, D₁.comap f⁆ ∧ Group.IsPerfect ↥⁅D₂.comap f, D₂.comap f⁆ := by
  have hN₁ : (D₁.comap f).Normal :=
    exists_perfect_factors_normal_comap (D₁ := D₁) (D₂ := D₂) f hD hcomm
  have hN₂ : (D₂.comap f).Normal :=
    exists_perfect_factors_normal_comap (D₁ := D₂) (D₂ := D₁) f
      (by rw [sup_comm]; exact hD) (by rw [commutator_comm]; exact hcomm)
  have hmap₁ : (D₁.comap f).map f = D₁ :=
    exists_perfect_factors_map_comap f (le_sup_left.trans hD.le)
  have hmap₂ : (D₂.comap f).map f = D₂ :=
    exists_perfect_factors_map_comap f (le_sup_right.trans hD.le)
  have hmapP₁ : (⁅D₁.comap f, D₁.comap f⁆).map f = D₁ :=
    exists_perfect_factors_map_commutator f h₁ hmap₁
  have hmapP₂ : (⁅D₂.comap f, D₂.comap f⁆).map f = D₂ :=
    exists_perfect_factors_map_commutator f h₂ hmap₂
  have hK : ∀ N : Subgroup P, ⁅f.ker, N⁆ = ⊥ := fun N =>
    le_bot_iff.mp ((commutator_mono hker le_rfl).trans (commutator_center_left N).le)
  have hc12 : ⁅D₁.comap f, D₂.comap f⁆ ≤ f.ker := by
    rw [commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have h := commutator_mem_commutator (Subgroup.mem_comap.mp hg₁ : f g₁ ∈ D₁)
      (Subgroup.mem_comap.mp hg₂ : f g₂ ∈ D₂)
    rw [hcomm, Subgroup.mem_bot] at h
    exact h
  have hc1 : ⁅⁅D₁.comap f, D₁.comap f⁆, D₂.comap f⁆ = ⊥ :=
    exists_perfect_factors_commutator_commutator_eq_bot hK hc12
  have hP₂Q₂ : ⁅D₂.comap f, D₂.comap f⁆ ≤ D₂.comap f :=
    Subgroup.commutator_le_right (D₂.comap f) (D₂.comap f)
  have hPP : ⁅⁅D₁.comap f, D₁.comap f⁆, ⁅D₂.comap f, D₂.comap f⁆⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono (le_refl ⁅D₁.comap f, D₁.comap f⁆) hP₂Q₂).trans hc1.le)
  have hkQ₁ : f.ker ≤ D₁.comap f := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact D₁.one_mem
  have hQ12 : D₁.comap f ⊔ D₂.comap f = ⊤ := by
    have hmapsup : ((D₁.comap f) ⊔ (D₂.comap f)).map f = f.range := by
      rw [Subgroup.map_sup, hmap₁, hmap₂, hD]
    have h : (f.range).comap f = (D₁.comap f ⊔ D₂.comap f) ⊔ f.ker := by
      rw [← hmapsup, Subgroup.comap_map_eq]
    have htop : (⊤ : Subgroup P) = (D₁.comap f ⊔ D₂.comap f) ⊔ f.ker := by
      rw [← h, MonoidHom.range_eq_map, Subgroup.comap_map_eq, top_sup_eq]
    rw [sup_eq_left.mpr (hkQ₁.trans le_sup_left)] at htop
    exact htop.symm
  haveI hNS : (D₁.comap f ⊔ D₂.comap f).Normal := by
    rw [hQ12]
    infer_instance
  have hQle : D₁.comap f ≤ ⁅D₁.comap f, D₁.comap f⁆ ⊔ f.ker := by
    intro x hx
    have hfx : f x ∈ (⁅D₁.comap f, D₁.comap f⁆).map f := by
      rw [hmapP₁]
      exact Subgroup.mem_comap.mp hx
    obtain ⟨y, hy, hfy⟩ := Subgroup.mem_map.mp hfx
    have hk : y⁻¹ * x ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfy, inv_mul_cancel]
    have h := mul_mem_sup hy hk
    rwa [mul_inv_cancel_left] at h
  have hQ₁Q₂ : ⁅D₁.comap f, D₂.comap f⁆ = ⊥ := by
    have h := commutator_mono hQle (le_refl (D₂.comap f))
    rw [commutator_sup_right, hc1, hK, sup_bot_eq] at h
    exact le_bot_iff.mp h
  have hQ₂Q₁ : ⁅D₂.comap f, D₁.comap f⁆ = ⊥ := by
    rw [commutator_comm]
    exact hQ₁Q₂
  have hexp : ⁅D₁.comap f ⊔ D₂.comap f, D₁.comap f ⊔ D₂.comap f⁆ =
      ⁅D₁.comap f, D₁.comap f⁆ ⊔ ⁅D₂.comap f, D₂.comap f⁆ := by
    rw [commutator_sup_right, commutator_sup_left (D₁.comap f),
      commutator_sup_left (D₂.comap f), hQ₁Q₂, hQ₂Q₁]
    simp only [sup_bot_eq, bot_sup_eq]
  have hT : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊤ := by
    rw [← _root_.commutator_def]
    exact hP.commutator_eq_top
  have hsum : ⁅D₁.comap f, D₁.comap f⁆ ⊔ ⁅D₂.comap f, D₂.comap f⁆ = ⊤ := by
    rw [← hexp, hQ12]
    exact hT
  exact ⟨inferInstance, inferInstance, hPP, hsum, hmapP₁, hmapP₂,
    exists_perfect_factors_isPerfect_commutator f hker h₁ hmap₁,
    exists_perfect_factors_isPerfect_commutator f hker h₂ hmap₂⟩

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
