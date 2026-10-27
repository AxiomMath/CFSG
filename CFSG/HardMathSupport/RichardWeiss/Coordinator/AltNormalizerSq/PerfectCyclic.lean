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
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

namespace CFSG.HardMathSupport.RichardWeiss.Coordinator

open Equiv Equiv.Perm

theorem exists_derivedSeries_succ_eq (G : Type*) [Group G] [Finite G] :
    ∃ n : ℕ, derivedSeries G (n + 1) = derivedSeries G n := by
  by_contra h
  push Not at h
  have hlt : ∀ n, Nat.card (derivedSeries G (n + 1)) < Nat.card (derivedSeries G n) := by
    intro n
    have hle : derivedSeries G (n + 1) ≤ derivedSeries G n := by
      rw [derivedSeries_succ]
      exact Subgroup.commutator_le_left _ _
    exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hle (h n))
  have hbound : ∀ n, Nat.card (derivedSeries G n) + n ≤ Nat.card G := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hlt n
      omega
  have h1 := hbound (Nat.card G + 1)
  have h2 : 0 < Nat.card (derivedSeries G (Nat.card G + 1)) := Nat.card_pos
  omega

theorem derivedSeries_perm_eq_alternatingGroup {α : Type*} [Fintype α] [DecidableEq α]
    (h5 : 5 ≤ Fintype.card α) {n : ℕ} (hn : 1 ≤ n) :
    derivedSeries (Perm α) n = alternatingGroup α := by
  have h5' : 5 ≤ Nat.card α := by rwa [Nat.card_eq_fintype_card]
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · rw [derivedSeries_succ, derivedSeries_zero, ← commutator_def]
      exact alternatingGroup.commutator_perm_eq h5'
    · rw [derivedSeries_succ, ih hn']
      exact commutator_alternatingGroup_eq_self h5'

theorem exists_not_isCyclic_isPGroup_alternatingGroup {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 2 * p ≤ k) : ∃ E : Subgroup (Perm (Fin k)),
      E ≤ alternatingGroup (Fin k) ∧ IsPGroup p E ∧ ¬ IsCyclic E := by
  have hp2' := hp.two_le
  set c : Perm (Fin p) := finRotate p with hcdef
  have hc : orderOf c = p := by
    rw [hcdef, (isCycle_finRotate_of_le hp2').orderOf, support_finRotate_of_le hp2',
      Finset.card_univ, Fintype.card_fin]
  have hcsign : sign c = 1 := by
    rw [hcdef, sign_finRotate]
    obtain ⟨m, hm⟩ := hp.eq_two_or_odd'.resolve_left hp2
    rw [hm, show 2 * m + 1 - 1 = 2 * m by omega, pow_mul]
    simp
  let Z : Subgroup (Perm (Fin p) × Perm (Fin p)) :=
    (Subgroup.zpowers c).prod (Subgroup.zpowers c)
  let e : (Fin p ⊕ Fin p) ⊕ Fin (k - 2 * p) ≃ Fin k :=
    ((finSumFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv).trans (finCongr (by omega))
  let φ : Perm (Fin p) × Perm (Fin p) →* Perm (Fin k) :=
    e.permCongrHom.toMonoidHom.comp
      ((Perm.sumCongrHom _ _).comp ((MonoidHom.inl _ _).comp (Perm.sumCongrHom _ _)))
  have hinl : Function.Injective
      (MonoidHom.inl (Perm (Fin p ⊕ Fin p)) (Perm (Fin (k - 2 * p)))) :=
    fun a b h => congrArg Prod.fst h
  have hφ : Function.Injective φ := by
    simp only [φ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    exact e.permCongrHom.injective.comp
      (Perm.sumCongrHom_injective.comp (hinl.comp Perm.sumCongrHom_injective))
  have hsign_pow : ∀ a ∈ Subgroup.zpowers c, sign a = 1 := by
    rintro _ ⟨n, rfl⟩
    simp [hcsign]
  refine ⟨Z.map φ, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_alternatingGroup]
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Equiv.permCongrHom,
      MulEquiv.coe_mk, sign_permCongr, Perm.sumCongrHom_apply, MonoidHom.inl_apply,
      sign_sumCongr, Perm.sign_one, mul_one]
    rw [hsign_pow _ hx.1, hsign_pow _ hx.2, mul_one]
  · have hcp : c ^ p = 1 := by
      have := pow_orderOf_eq_one c
      rwa [hc] at this
    have hZ : IsPGroup p Z := by
      intro g
      refine ⟨1, ?_⟩
      obtain ⟨⟨a, b⟩, ⟨⟨m, hm⟩, ⟨n, hn⟩⟩⟩ := g
      apply Subtype.ext
      simp only [pow_one, Subgroup.coe_pow, Prod.pow_mk, Subgroup.coe_one, Prod.mk_eq_one]
      dsimp only at hm hn
      constructor
      · rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcp, one_zpow]
      · rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcp, one_zpow]
    exact hZ.map φ
  · intro hcyc
    have hZc : IsCyclic Z :=
      isCyclic_of_surjective (Subgroup.equivMapOfInjective Z φ hφ).symm (MulEquiv.surjective _)
    have hprod : IsCyclic (Subgroup.zpowers c × Subgroup.zpowers c) :=
      isCyclic_of_surjective (Subgroup.prodEquiv _ _) (MulEquiv.surjective _)
    obtain ⟨-, -, hcop⟩ := Group.isCyclic_prod_iff.1 hprod
    rw [Nat.card_zpowers, hc, Nat.coprime_self] at hcop
    exact hp.one_lt.ne' hcop

theorem lt_two_mul_of_perfect_cyclic {X : Type*} [Group X] [Finite X] {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {J : Subgroup X}
    (hJ : ∀ V : Subgroup X, V ≤ J → ⁅V, V⁆ = V → ∀ A : Subgroup X, A ≤ V → IsPGroup p A →
      IsCyclic A)
    (ρ : ↥J →* Perm (Fin k)) (hρ : Function.Surjective ρ) : k < 2 * p := by
  by_contra hk
  push Not at hk
  have hp2' := hp.two_le
  have hk5 : 5 ≤ Fintype.card (Fin k) := by
    rw [Fintype.card_fin]
    omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := exists_derivedSeries_succ_eq ↥J
  have hDperf : ⁅derivedSeries ↥J (n + 1), derivedSeries ↥J (n + 1)⁆ =
      derivedSeries ↥J (n + 1) := by
    rw [hn, ← derivedSeries_succ]
    exact hn
  have hDimg : (derivedSeries ↥J (n + 1)).map ρ = alternatingGroup (Fin k) := by
    rw [map_derivedSeries_eq hρ]
    exact derivedSeries_perm_eq_alternatingGroup hk5 (by omega)
  generalize derivedSeries ↥J (n + 1) = D at hDperf hDimg
  obtain ⟨E, hEA, hEp, hEnc⟩ := exists_not_isCyclic_isPGroup_alternatingGroup hp hp2 hk
  set H : Subgroup ↥J := D ⊓ E.comap ρ with hH
  let f : ↥H →* ↥E := (ρ.comp H.subtype).codRestrict E fun h => h.2.2
  have hf : Function.Surjective f := by
    intro e
    have he : (e : Perm (Fin k)) ∈ D.map ρ := hDimg ▸ hEA e.2
    obtain ⟨d, hdD, hde⟩ := he
    refine ⟨⟨d, hdD, ?_⟩, ?_⟩
    · show ρ d ∈ E
      rw [hde]
      exact e.2
    · exact Subtype.ext hde
  obtain ⟨P⟩ : Nonempty (Sylow p ↥H) := inferInstance
  have hPtop : (P : Subgroup ↥H).map f = ⊤ := by
    have htop : IsPGroup p (⊤ : Subgroup ↥E) := hEp.to_subgroup ⊤
    have := (P.mapSurjective hf).is_maximal' htop le_top
    rw [Sylow.coe_mapSurjective] at this
    exact this.symm
  let g : ↥(P : Subgroup ↥H) →* ↥E := f.comp (P : Subgroup ↥H).subtype
  have hg : Function.Surjective g := by
    intro e
    have he : e ∈ (P : Subgroup ↥H).map f := hPtop ▸ Subgroup.mem_top e
    obtain ⟨x, hxP, hxe⟩ := he
    exact ⟨⟨x, hxP⟩, hxe⟩
  set V : Subgroup X := D.map J.subtype with hV
  set A : Subgroup X := ((P : Subgroup ↥H).map H.subtype).map J.subtype with hA
  have hVJ : V ≤ J := Subgroup.map_subtype_le D
  have hVperf : ⁅V, V⁆ = V := by
    rw [hV, ← Subgroup.map_commutator, hDperf]
  have hAV : A ≤ V :=
    Subgroup.map_mono ((Subgroup.map_subtype_le _).trans inf_le_left)
  have hAp : IsPGroup p A := (P.2.map _).map _
  have hAcyc : IsCyclic A := hJ V hVJ hVperf A hAV hAp
  let e1 := Subgroup.equivMapOfInjective (P : Subgroup ↥H) H.subtype H.subtype_injective
  let e2 := Subgroup.equivMapOfInjective ((P : Subgroup ↥H).map H.subtype) J.subtype
    J.subtype_injective
  have : IsCyclic ↥(P : Subgroup ↥H) :=
    isCyclic_of_surjective (e1.trans e2).symm (MulEquiv.surjective _)
  exact hEnc (isCyclic_of_surjective g hg)

end CFSG.HardMathSupport.RichardWeiss.Coordinator
