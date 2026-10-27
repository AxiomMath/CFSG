module

public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting
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
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ClassicalInvolution.GlaubermanAut

open SemidirectProduct

section Abstract

variable {V J : Type*} [CommGroup V] [Group J] (ρ : J →* MulAut V)

theorem conj_inl (γ : V ⋊[ρ] J) (v : V) : γ * inl v * γ⁻¹ = inl (ρ γ.right v) := by
  have h := inl_left_mul_inr_right γ
  have e1 : (inr γ.right : V ⋊[ρ] J) * inl v * (inr γ.right)⁻¹ = inl (ρ γ.right v) := by
    rw [inl_aut, map_inv]
  calc γ * inl v * γ⁻¹ = (inl γ.left * inr γ.right) * inl v * (inl γ.left * inr γ.right)⁻¹ := by
        rw [h]
    _ = inl γ.left * ((inr γ.right : V ⋊[ρ] J) * inl v * (inr γ.right)⁻¹) * (inl γ.left)⁻¹ := by
        group
    _ = inl (ρ γ.right v) := by
        rw [e1, ← map_mul, ← map_inv, ← map_mul, mul_comm γ.left, mul_assoc, mul_inv_cancel,
          mul_one]

variable {ρ}

theorem exists_invariant_complement [Finite V] [Finite J] {p : ℕ} [Fact p.Prime]
    (hV : IsPGroup p V) (W : Subgroup V) (hW : ∀ j : J, ∀ w ∈ W, ρ j w ∈ W) (P : Subgroup J)
    (hP : ¬ p ∣ P.index) (U : Subgroup V) (hU : ∀ s ∈ P, ∀ u ∈ U, ρ s u ∈ U)
    (hWU : W ⊓ U = ⊥) (hWU' : W ⊔ U = ⊤) :
    ∃ U₀ : Subgroup V, (∀ j : J, ∀ u ∈ U₀, ρ j u ∈ U₀) ∧ W ⊓ U₀ = ⊥ ∧ W ⊔ U₀ = ⊤ := by
  classical
  have : Finite (V ⋊[ρ] J) := Finite.of_equiv (V × J) SemidirectProduct.equivProd.symm
  let N : Subgroup (V ⋊[ρ] J) := W.map inl
  have hN : ∀ x : V ⋊[ρ] J, x ∈ N ↔ x.right = 1 ∧ x.left ∈ W := by
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨right_inl w, by simpa using hw⟩
    · rintro ⟨h1, h2⟩
      refine ⟨x.left, h2, ?_⟩
      conv_rhs => rw [← inl_left_mul_inr_right x, h1]
      simp
  have hNnormal : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨w, hw, rfl⟩ := hn
    rw [conj_inl]
    exact ⟨ρ g.right w, hW _ w hw, rfl⟩
  have : IsMulCommutative N := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨w₁, -, rfl⟩ := ha
    obtain ⟨w₂, -, rfl⟩ := hb
    apply Subtype.ext
    change inl w₁ * inl w₂ = inl w₂ * inl w₁
    rw [← map_mul, ← map_mul, mul_comm]
  let H : Subgroup (V ⋊[ρ] J) := P.comap rightHom
  let K₀ : Subgroup (V ⋊[ρ] J) :=
    { carrier := {γ | γ.left ∈ U ∧ γ.right ∈ P}
      one_mem' := ⟨U.one_mem, P.one_mem⟩
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨?_, ?_⟩
        · rw [mul_left]
          exact U.mul_mem ha1 (hU _ ha2 _ hb1)
        · rw [mul_right]
          exact P.mul_mem ha2 hb2
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        refine ⟨?_, ?_⟩
        · rw [inv_left]
          exact hU _ (P.inv_mem ha2) _ (U.inv_mem ha1)
        · rw [inv_right]
          exact P.inv_mem ha2 }
  have hNK : N ⊓ K₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro γ ⟨h1, h2, h3⟩
    have h1' : γ ∈ N := h1
    rw [hN] at h1'
    have : γ.left ∈ W ⊓ U := ⟨h1'.2, h2⟩
    rw [hWU, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact SemidirectProduct.ext this h1'.1
  have hsup : N ⊔ K₀ = H := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro γ hγ
        rw [hN] at hγ
        change γ.right ∈ P
        rw [hγ.1]
        exact P.one_mem
      · intro γ hγ
        exact hγ.2
    · intro γ hγ
      have hγ' : γ.right ∈ P := hγ
      have hmem : γ.left ∈ W ⊔ U := by rw [hWU']; exact Subgroup.mem_top _
      obtain ⟨w, hw, u, hu, hwu⟩ := Subgroup.mem_sup.1 hmem
      have e : γ = inl w * (inl u * inr γ.right) := by
        rw [← mul_assoc, ← map_mul, hwu, inl_left_mul_inr_right]
      rw [e]
      refine Subgroup.mul_mem_sup (hN _ |>.2 ⟨right_inl w, by simpa using hw⟩) ?_
      refine ⟨?_, ?_⟩
      · simpa [mul_left] using hu
      · simpa [mul_right] using hγ'
  have hcop : Nat.Coprime H.index (Nat.card N) := by
    have h1 : H.index = P.index := Subgroup.index_comap_of_surjective P rightHom_surjective
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hV
    have h2 : Nat.card N ∣ p ^ k := by
      rw [← hk]
      have : Nat.card N = Nat.card W :=
        Nat.card_congr (Subgroup.equivMapOfInjective W inl inl_injective).symm.toEquiv
      rw [this]
      exact Subgroup.card_subgroup_dvd_card W
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right h2
      (Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hP).symm)
  obtain ⟨D, -, hND, hND'⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting N H K₀ hcop hNK hsup
  refine ⟨D.comap inl, ?_, ?_, ?_⟩
  · intro j u hu
    have hj : (inr j : V ⋊[ρ] J) ∈ N ⊔ D := by rw [hND']; exact Subgroup.mem_top _
    obtain ⟨n, hn, d, hd, hnd⟩ := Subgroup.mem_sup_of_normal_left.1 hj
    have hdr : d.right = j := by
      have := congrArg (fun x : V ⋊[ρ] J => x.right) hnd
      simpa [mul_right, (hN n).1 hn |>.1] using this
    have hdu : d * inl u * d⁻¹ ∈ D := D.mul_mem (D.mul_mem hd hu) (D.inv_mem hd)
    rw [conj_inl, hdr] at hdu
    exact hdu
  · rw [eq_bot_iff]
    intro w ⟨hw, hw'⟩
    have : inl w ∈ N ⊓ D := ⟨⟨w, hw, rfl⟩, hw'⟩
    rw [hND, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (inl_injective (this.trans (map_one inl).symm))
  · rw [eq_top_iff]
    intro v _
    have hv : (inl v : V ⋊[ρ] J) ∈ N ⊔ D := by rw [hND']; exact Subgroup.mem_top _
    obtain ⟨n, hn, d, hd, hnd⟩ := Subgroup.mem_sup_of_normal_left.1 hv
    obtain ⟨w, hw, rfl⟩ := hn
    have hdv : d = inl (w⁻¹ * v) := by
      rw [map_mul, map_inv, ← hnd]
      group
    have hmem : w⁻¹ * v ∈ D.comap inl := by
      change inl (w⁻¹ * v) ∈ D
      rw [← hdv]
      exact hd
    have : v = w * (w⁻¹ * v) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hw hmem

end Abstract

section Ambient

variable {Ω : Type*} [Group Ω]

theorem exists_invariant_complement_subgroup [Finite Ω] {p : ℕ} [Fact p.Prime]
    (V W J R U : Subgroup Ω) (hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hVp : IsPGroup p V)
    (hWV : W ≤ V) (hJV : J ≤ Subgroup.normalizer (V : Set Ω))
    (hJW : J ≤ Subgroup.normalizer (W : Set Ω)) (hR : ¬ p ∣ R.relIndex J)
    (hRU : R ≤ Subgroup.normalizer (U : Set Ω)) (hUV : U ≤ V) (hWU : W ⊓ U = ⊥)
    (hWU' : W ⊔ U = V) :
    ∃ U₀ : Subgroup Ω, U₀ ≤ V ∧ J ≤ Subgroup.normalizer (U₀ : Set Ω) ∧ W ⊓ U₀ = ⊥ ∧
      W ⊔ U₀ = V := by
  let _ : CommGroup V := { (inferInstance : Group V) with
    mul_comm := fun a b => Subtype.ext (hVcomm _ a.2 _ b.2) }
  let ρ : J →* MulAut V := V.normalizerMonoidHom.comp (Subgroup.inclusion hJV)
  have hρ : ∀ (j : J) (v : V), ((ρ j v : V) : Ω) = j * v * (j : Ω)⁻¹ := fun j v => rfl
  have hmemW : ∀ (j : J) (x : Ω), x ∈ W ↔ (j : Ω) * x * (j : Ω)⁻¹ ∈ W := fun j x =>
    Subgroup.mem_normalizer_iff.1 (hJW j.2) x
  have hmemU : ∀ (j : R) (x : Ω), x ∈ U ↔ (j : Ω) * x * (j : Ω)⁻¹ ∈ U := fun j x =>
    Subgroup.mem_normalizer_iff.1 (hRU j.2) x
  have h1 : W.subgroupOf V ⊓ U.subgroupOf V = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxW, hxU⟩
    have : (x : Ω) ∈ W ⊓ U := ⟨hxW, hxU⟩
    rw [hWU, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  have h2 : W.subgroupOf V ⊔ U.subgroupOf V = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hWV hUV, hWU', Subgroup.subgroupOf_self]
  obtain ⟨U₀, hinv, hinf, hsup⟩ := exists_invariant_complement (ρ := ρ)
    (p := p) hVp (W.subgroupOf V) (fun j w hw => (hmemW j w).1 hw)
    (R.subgroupOf J) hR (U.subgroupOf V) (fun s hs u hu => (hmemU ⟨s, hs⟩ u).1 hu) h1 h2
  have hinv' : ∀ (j : J) (x : Ω), x ∈ U₀.map V.subtype →
      (j : Ω) * x * (j : Ω)⁻¹ ∈ U₀.map V.subtype := by
    rintro j x ⟨u, hu, rfl⟩
    exact ⟨ρ j u, hinv j u hu, hρ j u⟩
  refine ⟨U₀.map V.subtype, Subgroup.map_subtype_le U₀, ?_, ?_, ?_⟩
  · intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hinv' ⟨j, hj⟩ x, fun hx => ?_⟩
    have := hinv' ⟨j⁻¹, J.inv_mem hj⟩ _ hx
    simpa [mul_assoc] using this
  · rw [eq_bot_iff]
    rintro x ⟨hxW, u, hu, rfl⟩
    have hu' : u ∈ W.subgroupOf V ⊓ U₀ := ⟨hxW, hu⟩
    rw [hinf, Subgroup.mem_bot] at hu'
    rw [hu']
    exact Subgroup.one_mem _
  · have h3 := congrArg (Subgroup.map V.subtype) hsup
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hWV] at h3
    rw [h3]
    ext x
    simp

end Ambient

end CFSG.ClassicalInvolution.GlaubermanAut
