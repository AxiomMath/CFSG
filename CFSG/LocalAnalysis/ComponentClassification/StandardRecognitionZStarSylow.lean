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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

namespace CFSG.ComponentClassification.StandardRecognition

open Subgroup

variable {G : Type*} [Group G]

theorem mem_sylow_of_mem_center_of_orderOf_eq_two {L : Type*} [Group L] {x : L}
    (hx : x ∈ center L) (hx2 : orderOf x = 2) (T : Sylow 2 L) : x ∈ (T : Subgroup L) := by
  have : (zpowers x).Normal := normal_of_le_center (zpowers_le.mpr hx)
  have hp : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2, pow_one])
  exact IsPGroup.le_sylow_of_normal hp T (mem_zpowers x)

theorem exists_sylow_eq_map_of_normalizer_map_le [Finite G] {q : ℕ} [Fact q.Prime] (L : Subgroup G)
    (T : Sylow q L)
    (hN : normalizer (((T : Subgroup L).map L.subtype : Subgroup G) : Set G) ≤ L) :
    ∃ S : Sylow q G, (T : Subgroup L).map L.subtype = S := by
  obtain ⟨S, hST⟩ := T.exists_comap_subtype_eq
  have hmap : (L.comap (S : Subgroup G).subtype).map (S : Subgroup G).subtype =
      (T : Subgroup L).map L.subtype := by
    rw [map_comap_eq, subtype_range, ← hST, map_comap_eq, subtype_range, inf_comm]
  have hself : normalizer ((L.comap (S : Subgroup G).subtype : Subgroup S) : Set S) =
      L.comap (S : Subgroup G).subtype := by
    refine le_antisymm (fun x hx => ?_) le_normalizer
    have hmapped := le_normalizer_map (S : Subgroup G).subtype (mem_map.mpr ⟨x, hx, rfl⟩)
    rw [hmap] at hmapped
    exact hN hmapped
  have : Group.IsNilpotent (S : Subgroup G) := S.isPGroup'.isNilpotent
  have htop := normalizerCondition_iff_only_full_group_self_normalizing.mp
    Group.normalizerCondition_of_isNilpotent _ hself
  have hSL : (S : Subgroup G) ≤ L := fun x hx => by
    have hx' : (⟨x, hx⟩ : (S : Subgroup G)) ∈ L.comap (S : Subgroup G).subtype := by
      rw [htop]
      trivial
    exact hx'
  refine ⟨S, ?_⟩
  rw [← hmap, map_comap_eq, subtype_range, inf_eq_left.mpr hSL]

theorem conj_eq_of_mem_normalizer_of_forall_mulAut_fix {L : Subgroup G} {T : Subgroup L}
    {x : T} (hfix : ∀ φ : MulAut T, φ x = x) {s : G}
    (hs : s ∈ normalizer ((T.map L.subtype : Subgroup G) : Set G)) :
    s * ((x : L) : G) * s⁻¹ = (x : L) := by
  let e : T ≃* T.map L.subtype := T.equivMapOfInjective L.subtype L.subtype_injective
  let ψ : MulAut (T.map L.subtype) := (T.map L.subtype).normalizerMonoidHom ⟨s, hs⟩
  have h : ψ (e x) = e x := by
    have := congrArg e (hfix (e.trans (ψ.trans e.symm)))
    simpa only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] using this
  have h' := congrArg Subtype.val h
  rwa [normalizerMonoidHom_apply_apply_coe, coe_equivMapOfInjective_apply] at h'

theorem exists_mem_normalizer_conj_eq_of_le_centralizer [Finite G] {q : ℕ} [Fact q.Prime]
    (S : Sylow q G) {t y : G} (htS : (S : Subgroup G) ≤ centralizer ({t} : Set G))
    (hvS : (S : Subgroup G) ≤ centralizer ({y * t * y⁻¹} : Set G)) :
    ∃ n ∈ normalizer ((S : Subgroup G) : Set G), n * t * n⁻¹ = y * t * y⁻¹ := by
  have hyS : ((y • S : Sylow q G) : Subgroup G) ≤ centralizer ({y * t * y⁻¹} : Set G) := by
    intro x hx
    rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hx
    have hx' : y⁻¹ * x * y ∈ (S : Subgroup G) := by
      simpa [MulAut.smul_def, MulAut.conj_inv_apply] using hx
    have hc := mem_centralizer_singleton_iff.mp (htS hx')
    rw [mem_centralizer_singleton_iff]
    calc x * (y * t * y⁻¹) = y * (y⁻¹ * x * y * t) * y⁻¹ := by group
      _ = y * (t * (y⁻¹ * x * y)) * y⁻¹ := by rw [hc]
      _ = y * t * y⁻¹ * x := by group
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (centralizer ({y * t * y⁻¹} : Set G))
    ((y • S).subtype hyS) (S.subtype hvS)
  rw [Sylow.smul_subtype] at hc
  have hc' := Sylow.subtype_injective hc
  rw [Subgroup.smul_def, smul_smul] at hc'
  refine ⟨(c : G) * y, Sylow.smul_eq_iff_mem_normalizer.mp hc', ?_⟩
  have hcv := mem_centralizer_singleton_iff.mp c.2
  calc (c : G) * y * t * ((c : G) * y)⁻¹ = c * (y * t * y⁻¹) * (c : G)⁻¹ := by group
    _ = y * t * y⁻¹ * c * (c : G)⁻¹ := by rw [hcv]
    _ = y * t * y⁻¹ := by group

private theorem rigid_sylow_aux [Finite G] {t : G} {H : Subgroup G}
    (hH : H = centralizer ({t} : Set G)) (ht : orderOf t = 2) {K : Subgroup G} (hKH : K ≤ H)
    (T : Sylow 2 H)
    (hfix : ∀ φ : MulAut (T : Subgroup H), ∀ x : (T : Subgroup H), ((x : H) : G) = t → φ x = x)
    (hcent : ∀ u ∈ K, orderOf u = 2 → ∃ k ∈ K, ∃ z ∈ center (T : Subgroup H),
      ((z : H) : G) = k⁻¹ * u * k) :
    (∃ S : Sylow 2 G, (T : Subgroup H).map H.subtype = S) ∧
      ∀ g : G, g⁻¹ * t * g ∈ K → g⁻¹ * t * g = t := by
  have hmemH : ∀ {x : G}, x ∈ H ↔ x * t = t * x := by
    intro x
    rw [hH, mem_centralizer_singleton_iff]
  have htH : t ∈ H := hmemH.mpr rfl
  have htZ : (⟨t, htH⟩ : H) ∈ center H := mem_center_iff.mpr fun g =>
    Subtype.ext (hmemH.mp g.2)
  have htT : (⟨t, htH⟩ : H) ∈ (T : Subgroup H) :=
    mem_sylow_of_mem_center_of_orderOf_eq_two htZ (by rw [orderOf_mk, ht]) T
  have hfixG : ∀ s ∈ normalizer (((T : Subgroup H).map H.subtype : Subgroup G) : Set G),
      s * t * s⁻¹ = t := fun s hs =>
    conj_eq_of_mem_normalizer_of_forall_mulAut_fix (x := ⟨⟨t, htH⟩, htT⟩)
      (fun φ => hfix φ _ rfl) hs
  have hNH : normalizer (((T : Subgroup H).map H.subtype : Subgroup G) : Set G) ≤ H :=
    fun s hs => hmemH.mpr (by
      calc s * t = s * t * s⁻¹ * s := by group
        _ = t * s := by rw [hfixG s hs])
  obtain ⟨S, hS⟩ := exists_sylow_eq_map_of_normalizer_map_le H T hNH
  refine ⟨⟨S, hS⟩, fun g hg => ?_⟩
  have hu2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [show g⁻¹ * t * g = (MulAut.conj g⁻¹) t by simp, MulEquiv.orderOf_eq, ht]
  obtain ⟨k, hkK, z, hzZ, hz⟩ := hcent _ hg hu2
  have hSt : (S : Subgroup G) ≤ centralizer ({t} : Set G) := hH ▸ hS ▸ map_subtype_le _
  have hSv : (S : Subgroup G) ≤ centralizer ({(g * k)⁻¹ * t * (g * k)⁻¹⁻¹} : Set G) := by
    intro s hs
    rw [← hS] at hs
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hs
    rw [mem_centralizer_singleton_iff]
    have hzw := congrArg (fun q : (T : Subgroup H) => ((q : H) : G))
      (mem_center_iff.mp hzZ ⟨w, hw⟩)
    simp only [Subgroup.coe_mul, hz] at hzw
    calc H.subtype w * ((g * k)⁻¹ * t * (g * k)⁻¹⁻¹) = (w : G) * (k⁻¹ * (g⁻¹ * t * g) * k) := by
          simp only [coe_subtype]
          group
      _ = k⁻¹ * (g⁻¹ * t * g) * k * w := hzw
      _ = (g * k)⁻¹ * t * (g * k)⁻¹⁻¹ * H.subtype w := by
          simp only [coe_subtype]
          group
  obtain ⟨n, hn, hnt⟩ := exists_mem_normalizer_conj_eq_of_le_centralizer S hSt hSv
  rw [← hS] at hn
  have hv : k⁻¹ * (g⁻¹ * t * g) * k = t := by
    have h := hfixG n hn
    rw [hnt] at h
    calc k⁻¹ * (g⁻¹ * t * g) * k = (g * k)⁻¹ * t * (g * k)⁻¹⁻¹ := by group
      _ = t := h
  have hkt : k * t = t * k := hmemH.mp (hKH hkK)
  calc g⁻¹ * t * g = k * (k⁻¹ * (g⁻¹ * t * g) * k) * k⁻¹ := by group
    _ = k * t * k⁻¹ := by rw [hv]
    _ = t := by rw [hkt, mul_inv_cancel_right]

theorem rigid_sylow_central_involution_excludes_internal_fusion [Finite G] {t : G}
    (ht : orderOf t = 2) {K : Subgroup G} (hKH : K ≤ centralizer ({t} : Set G))
    (T : Sylow 2 (centralizer ({t} : Set G)))
    (hfix : ∀ φ : MulAut (T : Subgroup (centralizer ({t} : Set G))),
      ∀ x : (T : Subgroup (centralizer ({t} : Set G))),
        ((x : centralizer ({t} : Set G)) : G) = t → φ x = x)
    (hcent : ∀ u ∈ K, orderOf u = 2 → ∃ k ∈ K,
      ∃ z ∈ center (T : Subgroup (centralizer ({t} : Set G))),
        ((z : centralizer ({t} : Set G)) : G) = k⁻¹ * u * k) :
    (∃ S : Sylow 2 G,
        (T : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype = S) ∧
      ∀ g : G, g⁻¹ * t * g ∈ K → g⁻¹ * t * g = t :=
  rigid_sylow_aux rfl ht hKH T hfix hcent

end CFSG.ComponentClassification.StandardRecognition
