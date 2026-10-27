module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

open Module Polynomial
open scoped IsMulCommutative

namespace CFSG.HardMathSupport.Curtis.Coordinator.SPLCell

section Invariant

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def InvSet (S : Set (Module.End K V)) (N : Submodule K V) : Prop :=
  ∀ f ∈ S, ∀ v ∈ N, f v ∈ N

theorem exists_minimal_invSet [Module.Finite K V] (S : Set (Module.End K V)) (U : Submodule K V)
    (hU : InvSet S U) (hU0 : U ≠ ⊥) :
    ∃ M : Submodule K V, M ≤ U ∧ M ≠ ⊥ ∧ InvSet S M ∧
      ∀ N : Submodule K V, N ≤ M → InvSet S N → N = ⊥ ∨ N = M := by
  obtain ⟨M, ⟨hMU, hM0, hMi⟩, hmin⟩ :=
    (InvImage.wf (fun N : Submodule K V => Module.finrank K N) wellFounded_lt).has_min
      {N | N ≤ U ∧ N ≠ ⊥ ∧ InvSet S N} ⟨U, le_rfl, hU0, hU⟩
  refine ⟨M, hMU, hM0, hMi, fun N hNM hNi => ?_⟩
  by_contra hcon
  push Not at hcon
  exact hmin N ⟨hNM.trans hMU, hcon.1, hNi⟩
    (Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hNM hcon.2))

end Invariant

section Schur

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]

theorem injective_of_mem_adjoin {T : Set (Module.End K M)} (hT : T.Pairwise Commute)
    (hirr : ∀ N : Submodule K M, (∀ f ∈ T, ∀ v ∈ N, f v ∈ N) → N = ⊥ ∨ N = ⊤)
    {r : Module.End K M} (hr : r ∈ Algebra.adjoin K T) (hr0 : r ≠ 0) :
    Function.Injective r := by
  have hcomm : ∀ f ∈ T, Commute f r := fun f hf =>
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hr (fun b hb => by
      by_cases h : f = b
      · subst h
        exact Commute.refl f
      · exact hT hf hb h)
  have hinv : ∀ f ∈ T, ∀ v ∈ LinearMap.ker r, f v ∈ LinearMap.ker r := by
    intro f hf v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have h2 : f (r v) = r (f v) := by
      have := congrArg (fun g : Module.End K M => g v) (hcomm f hf).eq
      simpa using this
    rw [← h2, hv, map_zero]
  rcases hirr _ hinv with h | h
  · exact LinearMap.ker_eq_bot.mp h
  · exact absurd (LinearMap.ker_eq_top.mp h) hr0

theorem commute_of_mem_adjoin_both {T : Set (Module.End K M)} (hT : T.Pairwise Commute)
    {a b : Module.End K M} (ha : a ∈ Algebra.adjoin K T) (hb : b ∈ Algebra.adjoin K T) :
    Commute b a := by
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha (fun f hf => ?_)
  refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb (fun g hg => ?_)).symm
  by_cases h : f = g
  · subst h
    exact Commute.refl f
  · exact hT hf hg h

@[reducible] noncomputable def adjoinCommRing {T : Set (Module.End K M)} (hT : T.Pairwise Commute) :
    CommRing (Algebra.adjoin K T) :=
  { (inferInstance : Ring (Algebra.adjoin K T)) with
    mul_comm := fun a b => Subtype.ext (commute_of_mem_adjoin_both hT b.2 a.2).eq }

theorem noZeroDivisors_adjoin [Nontrivial M] {T : Set (Module.End K M)} (hT : T.Pairwise Commute)
    (hirr : ∀ N : Submodule K M, (∀ f ∈ T, ∀ v ∈ N, f v ∈ N) → N = ⊥ ∨ N = ⊤) :
    NoZeroDivisors (Algebra.adjoin K T) := by
  refine ⟨fun {a b} hab => ?_⟩
  by_contra hcon
  push Not at hcon
  have ha : (a : Module.End K M) ≠ 0 := fun h => hcon.1 (Subtype.ext h)
  have hinj := injective_of_mem_adjoin hT hirr a.2 ha
  have hb : (b : Module.End K M) = 0 := by
    ext v
    have h1 := congrArg (fun x : Algebra.adjoin K T => (x : Module.End K M) v) hab
    simp only [Subalgebra.coe_mul, Module.End.mul_apply, Subalgebra.coe_zero,
      LinearMap.zero_apply] at h1
    exact hinj (by rw [h1]; simp)
  exact hcon.2 (Subtype.ext hb)

theorem isCyclic_quotient_ker [Nontrivial M] {T : Set (Module.End K M)} (hT : T.Pairwise Commute)
    (hirr : ∀ N : Submodule K M, (∀ f ∈ T, ∀ v ∈ N, f v ∈ N) → N = ⊥ ∨ N = ⊤)
    {G : Type*} [Group G] [Finite G] (ψ : G →* Module.End K M) (hψ : ∀ g, ψ g ∈ T) :
    IsCyclic (G ⧸ ψ.ker) := by
  let ψ' : G →* Algebra.adjoin K T := ψ.codRestrict _ (fun g => Algebra.subset_adjoin (hψ g))
  let ψ'' : G →* (Algebra.adjoin K T)ˣ := ψ'.toHomUnits
  have hker : ψ''.ker = ψ.ker := by
    ext g
    simp [ψ'', ψ', MonoidHom.mem_ker, Subtype.ext_iff]
  have hinj : Function.Injective (QuotientGroup.kerLift ψ'') := QuotientGroup.kerLift_injective ψ''
  have hnz : NoZeroDivisors (Algebra.adjoin K T) := noZeroDivisors_adjoin hT hirr
  let _ : CommRing (Algebra.adjoin K T) := adjoinCommRing hT
  have : IsDomain (Algebra.adjoin K T) := NoZeroDivisors.to_isDomain _
  have hc : IsCyclic (G ⧸ ψ''.ker) :=
    isCyclic_of_injective_ringHom ((Units.coeHom (Algebra.adjoin K T)).comp (QuotientGroup.kerLift ψ''))
      (Units.val_injective.comp hinj)
  have := hc
  exact isCyclic_of_surjective (QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom
    (QuotientGroup.quotientMulEquivOfEq hker).surjective

theorem irreducible_minpoly_of_mem [Nontrivial M] [Module.Finite K M] {T : Set (Module.End K M)}
    (hT : T.Pairwise Commute)
    (hirr : ∀ N : Submodule K M, (∀ f ∈ T, ∀ v ∈ N, f v ∈ N) → N = ⊥ ∨ N = ⊤)
    {z : Module.End K M} (hz : z ∈ T) : Irreducible (minpoly K z) := by
  have hnz : NoZeroDivisors (Algebra.adjoin K T) := noZeroDivisors_adjoin hT hirr
  let _ : CommRing (Algebra.adjoin K T) := adjoinCommRing hT
  have : IsDomain (Algebra.adjoin K T) := NoZeroDivisors.to_isDomain _
  let z' : Algebra.adjoin K T := ⟨z, Algebra.subset_adjoin hz⟩
  have hint : IsIntegral K z := IsIntegral.of_finite K z
  have hint' : IsIntegral K z' := by
    rw [← isIntegral_algHom_iff (Subalgebra.val (Algebra.adjoin K T)) Subtype.val_injective]
    exact hint
  have h1 := minpoly.irreducible hint'
  have h2 : minpoly K z = minpoly K z' :=
    minpoly.algHom_eq (Subalgebra.val (Algebra.adjoin K T)) Subtype.val_injective z'
  rw [h2]
  exact h1

end Schur

section StabFam

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {G : Type*} [CommGroup G]

@[expose] def stabOn (ρ : G →* (V ≃ₗ[K] V)) (M : Submodule K V) : Subgroup G where
  carrier := {g | ∀ v ∈ M, ρ g v = v}
  mul_mem' := by
    intro a b ha hb v hv
    rw [map_mul, LinearEquiv.mul_apply, hb v hv, ha v hv]
  one_mem' := by
    intro v hv
    simp
  inv_mem' := by
    intro a ha v hv
    have := ha v hv
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [this]
      _ = v := by rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem mem_stabOn {ρ : G →* (V ≃ₗ[K] V)} {M : Submodule K V} {g : G} :
    g ∈ stabOn ρ M ↔ ∀ v ∈ M, ρ g v = v := Iff.rfl

@[expose] def famSet (ρ : G →* (V ≃ₗ[K] V)) (z : Module.End K V) : Set (Module.End K V) :=
  insert z (Set.range fun g => ((ρ g : V ≃ₗ[K] V) : Module.End K V))

end StabFam

section Piece

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
variable {G : Type*} [CommGroup G] [Finite G]

theorem exists_piece (ρ : G →* (V ≃ₗ[K] V)) (z : Module.End K V)
    (hz : ∀ g, Commute z ((ρ g : V ≃ₗ[K] V) : Module.End K V))
    (U : Submodule K V) (hU0 : U ≠ ⊥) (hUi : InvSet (famSet ρ z) U) :
    ∃ M : Submodule K V, M ≤ U ∧ M ≠ ⊥ ∧ InvSet (famSet ρ z) M ∧
      IsCyclic (G ⧸ stabOn ρ M) ∧
      ∃ h : K[X], Irreducible h ∧ h.Monic ∧ (∀ v ∈ M, aeval z h v = 0) ∧
        ∀ q : K[X], aeval z q = 0 → h ∣ q := by
  obtain ⟨M, hMU, hM0, hMi, hmin⟩ := exists_minimal_invSet (famSet ρ z) U hUi hU0
  have hρM : ∀ g : G, ∀ v ∈ M, ρ g v ∈ M := fun g v hv =>
    hMi _ (Or.inr ⟨g, rfl⟩) v hv
  have hzM : ∀ v ∈ M, z v ∈ M := fun v hv => hMi _ (Or.inl rfl) v hv
  have hnt : Nontrivial M := Submodule.nontrivial_iff_ne_bot.mpr hM0
  let zM : Module.End K M := z.restrict hzM
  let ψ : G →* Module.End K M :=
    { toFun := fun g => ((ρ g : V ≃ₗ[K] V) : Module.End K V).restrict (hρM g)
      map_one' := by
        ext v
        simp
      map_mul' := fun g h => by
        ext v
        simp }
  have hψ_apply : ∀ g (v : M), ((ψ g v : M) : V) = ρ g v := fun g v => rfl
  let T : Set (Module.End K M) := insert zM (Set.range ψ)
  have hψT : ∀ g, ψ g ∈ T := fun g => Or.inr ⟨g, rfl⟩
  have hzT : zM ∈ T := Or.inl rfl
  have hzψ : ∀ g, Commute zM (ψ g) := by
    intro g
    refine LinearMap.ext fun v => Subtype.ext ?_
    exact congrArg (fun f : Module.End K V => f (v : V)) (hz g).eq
  have hψψ : ∀ g h, Commute (ψ g) (ψ h) := by
    intro g h
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  have hTc : T.Pairwise Commute := by
    intro a ha b hb hab
    rcases ha with rfl | ⟨g, rfl⟩ <;> rcases hb with rfl | ⟨h, rfl⟩
    · exact absurd rfl hab
    · exact hzψ h
    · exact (hzψ g).symm
    · exact hψψ g h
  have hirr : ∀ N : Submodule K M, (∀ f ∈ T, ∀ v ∈ N, f v ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    have hNV : InvSet (famSet ρ z) (N.map M.subtype) := by
      intro f hf w hw
      obtain ⟨v, hv, rfl⟩ := hw
      rcases hf with rfl | ⟨g, rfl⟩
      · exact ⟨zM v, hN zM hzT v hv, rfl⟩
      · exact ⟨ψ g v, hN (ψ g) (hψT g) v hv, rfl⟩
    have hle : N.map M.subtype ≤ M := by
      rintro w ⟨v, -, rfl⟩
      exact v.2
    rcases hmin (N.map M.subtype) hle hNV with h | h
    · left
      exact Submodule.map_injective_of_injective (Submodule.injective_subtype M)
        (h.trans (Submodule.map_bot M.subtype).symm)
    · right
      rw [eq_top_iff]
      intro v _
      have hv : (v : V) ∈ N.map M.subtype := by rw [h]; exact v.2
      obtain ⟨w, hw, hwv⟩ := hv
      exact (Subtype.ext hwv : w = v) ▸ hw
  refine ⟨M, hMU, hM0, hMi, ?_, ?_⟩
  · have hker : stabOn ρ M = ψ.ker := by
      ext g
      rw [mem_stabOn, MonoidHom.mem_ker]
      constructor
      · intro h
        ext v
        exact h v v.2
      · intro h v hv
        have := congrArg (fun f : Module.End K M => ((f ⟨v, hv⟩ : M) : V)) h
        simpa [hψ_apply] using this
    have hc := isCyclic_quotient_ker hTc hirr ψ hψT
    exact isCyclic_of_surjective (QuotientGroup.quotientMulEquivOfEq hker.symm).toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq hker.symm).surjective
  · have hirrz : Irreducible (minpoly K zM) := irreducible_minpoly_of_mem hTc hirr hzT
    have hint : IsIntegral K zM := IsIntegral.of_finite K zM
    have hpow : ∀ (n : ℕ) (v : M), (((zM ^ n) v : M) : V) = (z ^ n) v := by
      intro n
      induction n with
      | zero => intro v; rfl
      | succ n ih =>
        intro v
        rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
        rfl
    have hev : ∀ (q : K[X]) (v : M), (((aeval zM q) v : M) : V) = (aeval z q) v := by
      intro q
      induction q using Polynomial.induction_on' with
      | add p q hp hq =>
        intro v
        simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq]
      | monomial n a =>
        intro v
        simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
          Submodule.coe_smul, hpow]
    refine ⟨minpoly K zM, hirrz, minpoly.monic hint, fun v hv => ?_, fun q hq => ?_⟩
    · have := hev (minpoly K zM) ⟨v, hv⟩
      rw [minpoly.aeval, LinearMap.zero_apply] at this
      exact (this.symm.trans rfl : _)
    · refine minpoly.dvd K zM ?_
      refine LinearMap.ext fun v => Subtype.ext ?_
      have := hev q v
      rw [hq, LinearMap.zero_apply] at this
      simpa using this

end Piece

section GroupLemmas

variable {G : Type*} [CommGroup G] [Finite G]

omit [Finite G] in
theorem card_quot_eq_of_cyclic {p : ℕ} (hp : p.Prime) (hGp : ∀ g : G, g ^ p = 1) (D : Subgroup G)
    (hcyc : IsCyclic (G ⧸ D)) (a : G) (haD : a ∉ D) : Nat.card (G ⧸ D) = p := by
  have hexp : Monoid.exponent (G ⧸ D) ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H y => rw [← QuotientGroup.mk_pow, hGp, QuotientGroup.mk_one]
  rw [IsCyclic.exponent_eq_card] at hexp
  rcases (Nat.dvd_prime hp).1 hexp with h | h
  · exfalso
    have hu : Nat.card (G ⧸ D) = 1 := h
    have : Subsingleton (G ⧸ D) := (Nat.card_eq_one_iff_unique.1 hu).1
    apply haD
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  · exact h

theorem stable_acts_trivially {p r k : ℕ} (hp : p.Prime) (hr : r.Prime) (hrp : ¬ r ∣ p - 1)
    (hGp : ∀ g : G, g ^ p = 1) (γ : MulAut G) (hγ : γ ^ r ^ k = 1) (D : Subgroup G)
    (hcyc : IsCyclic (G ⧸ D)) (hDγ : D.map (γ : G →* G) = D) (a : G) (haD : a ∉ D) (x : G) :
    γ x * x⁻¹ ∈ D := by
  let γbar : MulAut (G ⧸ D) := QuotientGroup.congr D D γ hDγ
  have happly : ∀ (n : ℕ) (y : G),
      (γbar ^ n) (QuotientGroup.mk y) = QuotientGroup.mk ((γ ^ n) y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, MulAut.mul_apply, pow_succ, MulAut.mul_apply]
      have : γbar (QuotientGroup.mk y) = QuotientGroup.mk (γ y) := rfl
      rw [this, ih]
  have hpow : γbar ^ r ^ k = 1 := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H y => rw [happly, hγ]; rfl
  have hord : orderOf γbar ∣ r ^ k := orderOf_dvd_of_pow_eq_one hpow
  have hcardQ : Nat.card (G ⧸ D) = p := card_quot_eq_of_cyclic hp hGp D hcyc a haD
  have hcardAut : Nat.card (MulAut (G ⧸ D)) = p - 1 := by
    rw [IsCyclic.card_mulAut, hcardQ, Nat.totient_prime hp]
  have hord2 : orderOf γbar ∣ p - 1 := hcardAut ▸ orderOf_dvd_natCard γbar
  have hcop : Nat.Coprime (r ^ k) (p - 1) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hr).2 hrp)
  have h1 : orderOf γbar = 1 := Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd hord hord2)
  have h2 : γbar = 1 := orderOf_eq_one_iff.1 h1
  have h3 : (QuotientGroup.mk (γ x) : G ⧸ D) = QuotientGroup.mk x := by
    have := congrArg (fun e : MulAut (G ⧸ D) => e (QuotientGroup.mk x)) h2
    exact this
  have h4 := QuotientGroup.eq.1 h3
  have h5 := inv_mem h4
  simpa [mul_comm] using h5

end GroupLemmas

section SubgroupLemmas

variable {G : Type*} [CommGroup G] [Finite G]

theorem sup_eq_top_of_index_prime {p : ℕ} (hp : p.Prime) {D D' : Subgroup G} (hD : D.index = p)
    (hD' : D'.index = p) (hne : D ≠ D') : D ⊔ D' = ⊤ := by
  have hdvd : (D ⊔ D').index ∣ p := hD ▸ Subgroup.index_dvd_of_le (le_sup_left : D ≤ D ⊔ D')
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact Subgroup.index_eq_one.1 h
  · exfalso
    have hcard : ∀ E : Subgroup G, E.index = p → Nat.card E * p = Nat.card G := fun E hE => by
      rw [← hE]; exact Subgroup.card_mul_index E
    have h1 : Nat.card (D ⊔ D' : Subgroup G) * p = Nat.card G := hcard _ h
    have h2 : Nat.card D * p = Nat.card G := hcard _ hD
    have h3 : Nat.card D' * p = Nat.card G := hcard _ hD'
    have hp0 : 0 < p := hp.pos
    have e1 : D = D ⊔ D' :=
      Subgroup.eq_of_le_of_card_ge (le_sup_left : D ≤ D ⊔ D') (by
        have := Nat.eq_of_mul_eq_mul_right hp0 (h1.trans h2.symm)
        exact this.le)
    have e2 : D' = D ⊔ D' :=
      Subgroup.eq_of_le_of_card_ge (le_sup_right : D' ≤ D ⊔ D') (by
        have := Nat.eq_of_mul_eq_mul_right hp0 (h1.trans h3.symm)
        exact this.le)
    exact hne (e1.trans e2.symm)

end SubgroupLemmas

section Indep

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {G : Type*} [CommGroup G] [Fintype G]

open Classical in
@[expose] noncomputable def sumOver (ρ : G →* (V ≃ₗ[K] V)) (D : Subgroup G) : V → V :=
  fun v => ∑ g : G, if g ∈ D then ρ g v else 0

open Classical in
theorem sumOver_def (ρ : G →* (V ≃ₗ[K] V)) (D : Subgroup G) (v : V) :
    sumOver ρ D v = ∑ g : G, if g ∈ D then ρ g v else 0 := rfl

theorem sumOver_add (ρ : G →* (V ≃ₗ[K] V)) (D : Subgroup G) (v w : V) :
    sumOver ρ D (v + w) = sumOver ρ D v + sumOver ρ D w := by
  classical
  simp only [sumOver_def, map_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  split_ifs <;> simp

theorem sumOver_smul (ρ : G →* (V ≃ₗ[K] V)) (D : Subgroup G) (c : K) (v : V) :
    sumOver ρ D (c • v) = c • sumOver ρ D v := by
  classical
  simp only [sumOver_def, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  split_ifs <;> simp

@[expose] noncomputable def sumOverLin (ρ : G →* (V ≃ₗ[K] V)) (D : Subgroup G) :
    V →ₗ[K] V where
  toFun := sumOver ρ D
  map_add' := sumOver_add ρ D
  map_smul' := sumOver_smul ρ D

theorem sumOverLin_apply (ρ : G →* (V ≃ₗ[K] V)) (D : Subgroup G) (v : V) :
    sumOverLin ρ D v = sumOver ρ D v := rfl

theorem ρ_sumOver (ρ : G →* (V ≃ₗ[K] V)) (D : Subgroup G) {d : G} (hd : d ∈ D) (v : V) :
    ρ d (sumOver ρ D v) = sumOver ρ D v := by
  classical
  rw [sumOver_def, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft d) _ _ (fun x => ?_)
  by_cases hx : x ∈ D
  · have : d * x ∈ D := D.mul_mem hd hx
    simp [hx, this, ← LinearEquiv.mul_apply, ← map_mul]
  · have : d * x ∉ D := fun h => hx ((Subgroup.mul_mem_cancel_left D hd).1 h)
    simp [hx, this]

theorem ρ_sumOver_comm (ρ : G →* (V ≃ₗ[K] V)) (D : Subgroup G) (h : G) (v : V) :
    ρ h (sumOver ρ D v) = sumOver ρ D (ρ h v) := by
  classical
  rw [sumOver_def, map_sum, sumOver_def]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hg : g ∈ D
  · simp only [hg, ↓reduceIte]
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul, mul_comm]
  · simp [hg]

theorem sumOver_of_fixed (ρ : G →* (V ≃ₗ[K] V)) (D : Subgroup G) {w : V}
    (hw : ∀ d ∈ D, ρ d w = w) : sumOver ρ D w = (Nat.card D : K) • w := by
  classical
  rw [sumOver_def]
  have : ∀ g : G, (if g ∈ D then ρ g w else 0) = if g ∈ D then w else 0 := by
    intro g
    by_cases hg : g ∈ D
    · simp [hg, hw g hg]
    · simp [hg]
  simp only [this]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  have hc : (Finset.univ.filter (· ∈ D)).card = Nat.card D := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc, Nat.cast_smul_eq_nsmul]

theorem sum_absorb (ρ : G →* (V ≃ₗ[K] V)) (h : G) (v : V) :
    ∑ g : G, ρ g (ρ h v) = ∑ g : G, ρ g v := by
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun g => ?_)
  simp [← LinearEquiv.mul_apply, ← map_mul]

theorem sumOver_eq_zero_of_sup (ρ : G →* (V ≃ₗ[K] V)) {D D' : Subgroup G} (hsup : D ⊔ D' = ⊤)
    {w : V} (hw' : ∀ d ∈ D', ρ d w = w) (hw : ∑ g : G, ρ g w = 0)
    (hG : ((Fintype.card G : ℕ) : K) ≠ 0) : sumOver ρ D w = 0 := by
  classical
  set u := sumOver ρ D w with hu_def
  have hu : ∀ g : G, ρ g u = u := by
    intro g
    have hg : g ∈ D ⊔ D' := hsup ▸ Subgroup.mem_top g
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hg
    rw [map_mul, LinearEquiv.mul_apply, hu_def, ρ_sumOver_comm, hw' z hz]
    exact ρ_sumOver ρ D hy w
  have h1 : ∑ g : G, ρ g u = (Fintype.card G : K) • u := by
    simp only [hu, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have h2 : ∑ g : G, ρ g u = 0 := by
    rw [hu_def, sumOver_def]
    simp only [map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun h _ => ?_
    by_cases hh : h ∈ D
    · simp only [hh, ↓reduceIte]
      rw [sum_absorb, hw]
    · simp [hh]
  rw [h2] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_left hG

theorem iSupIndep_of_fixed {ι : Type*} (ρ : G →* (V ≃ₗ[K] V)) (M : ι → Submodule K V)
    (D : ι → Subgroup G) (hsup : ∀ i j, i ≠ j → D i ⊔ D j = ⊤)
    (hfix : ∀ i, ∀ w ∈ M i, ∀ d ∈ D i, ρ d w = w) (hker : ∀ i, ∀ w ∈ M i, ∑ g : G, ρ g w = 0)
    (hcard : ∀ i, ((Nat.card (D i) : ℕ) : K) ≠ 0) (hG : ((Fintype.card G : ℕ) : K) ≠ 0) :
    iSupIndep M := by
  intro i
  rw [Submodule.disjoint_def]
  intro w hwi hw
  have hker_sup : ⨆ (j) (_ : j ≠ i), M j ≤ LinearMap.ker (sumOverLin ρ (D i)) := by
    refine iSup₂_le fun j hj w' hw' => ?_
    rw [LinearMap.mem_ker, sumOverLin_apply]
    exact sumOver_eq_zero_of_sup ρ (hsup i j (Ne.symm hj)) (hfix j w' hw') (hker j w' hw') hG
  have h1 := hker_sup hw
  rw [LinearMap.mem_ker, sumOverLin_apply, sumOver_of_fixed ρ (D i) (hfix i w hwi)] at h1
  exact (smul_eq_zero.1 h1).resolve_left (hcard i)

end Indep

section Orbit

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem aeval_semilinear (σ : K →+* K) (f : V →ₛₗ[σ] V) (z : Module.End K V)
    (hz : ∀ v, f (z v) = z (f v)) (q : K[X]) (v : V) :
    f (aeval z q v) = aeval z (q.map σ) (f v) := by
  have hpow : ∀ (n : ℕ) (v : V), f ((z ^ n) v) = (z ^ n) (f v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, ih, hz]
      rfl
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, Polynomial.map_add]
  | monomial n a =>
    simp [aeval_monomial, Module.algebraMap_end_apply, hpow, map_smulₛₗ]

end Orbit

section OrbitStep

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {G : Type*} [CommGroup G] [Fintype G]

structure PieceProps (ρ : G →* (V ≃ₗ[K] V)) (z : Module.End K V) (h : K[X])
    (N : Submodule K V) (D : Subgroup G) : Prop where
  ne_bot : N ≠ ⊥
  inv : InvSet (famSet ρ z) N
  stab : stabOn ρ N = D
  aeval_zero : ∀ v ∈ N, aeval z h v = 0
  sum_zero : ∀ v ∈ N, ∑ g : G, ρ g v = 0

theorem PieceProps.map {ρ : G →* (V ≃ₗ[K] V)} {z : Module.End K V} {h : K[X]} {N : Submodule K V}
    {D : Subgroup G} (σ : K ≃+* K) (f : V →ₛₗ[(σ : K →+* K)] V) (hf : Function.Injective f)
    (γ : MulAut G) (hfρ : ∀ g v, f (ρ g v) = ρ (γ g) (f v)) (hfz : ∀ v, f (z v) = z (f v))
    (hh : h.map (σ.symm : K →+* K) = h) (hN : PieceProps ρ z h N D) :
    PieceProps ρ z h (N.map f) (D.map (γ : G →* G)) := by
  have : RingHomSurjective (σ : K →+* K) := ⟨σ.surjective⟩
  have hfρ' : ∀ g v, ρ g (f v) = f (ρ (γ⁻¹ g) v) := by
    intro g v
    rw [hfρ]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hbot
    apply hN.ne_bot
    rw [eq_bot_iff]
    intro v hv
    have : f v ∈ N.map f := ⟨v, hv, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    have : v = 0 := hf (by rw [this, map_zero])
    rw [this]
    exact Submodule.zero_mem _
  · intro F hF w hw
    obtain ⟨v, hv, rfl⟩ := hw
    rcases hF with rfl | ⟨g, rfl⟩
    · exact ⟨_, hN.inv _ (Or.inl rfl) v hv, hfz v⟩
    · refine ⟨ρ (γ⁻¹ g) v, hN.inv _ (Or.inr ⟨_, rfl⟩) v hv, ?_⟩
      exact (hfρ' g v).symm
  · ext g
    rw [mem_stabOn, Subgroup.mem_map]
    constructor
    · intro hg
      refine ⟨γ⁻¹ g, ?_, by simp⟩
      rw [← hN.stab, mem_stabOn]
      intro v hv
      apply hf
      rw [hfρ, MulAut.apply_inv_self]
      exact hg (f v) ⟨v, hv, rfl⟩
    · rintro ⟨g', hg', rfl⟩ w ⟨v, hv, rfl⟩
      rw [← hN.stab, mem_stabOn] at hg'
      change ρ (γ g') (f v) = f v
      rw [← hfρ, hg' v hv]
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := hw
    have h1 := aeval_semilinear (σ : K →+* K) f z hfz (h.map (σ.symm : K →+* K)) v
    have h3 : (h.map (σ.symm : K →+* K)).map (σ : K →+* K) = h := by
      rw [Polynomial.map_map]
      have : (σ : K →+* K).comp (σ.symm : K →+* K) = RingHom.id K := by
        ext x; simp
      rw [this, Polynomial.map_id]
    rw [h3, hh, hN.aeval_zero v hv, map_zero] at h1
    exact h1.symm
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := hw
    have : ∑ g : G, ρ g (f v) = f (∑ g : G, ρ g v) := by
      rw [map_sum]
      exact Fintype.sum_equiv (γ⁻¹ : MulAut G).toEquiv _ _ (fun g => hfρ' g v)
    rw [this, hN.sum_zero v hv, map_zero]

end OrbitStep

section Main

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
variable {G : Type*} [CommGroup G] [Fintype G]

omit [Module.Finite K V] [Fintype G] in
theorem fam_comm (ρ : G →* (V ≃ₗ[K] V)) (z : Module.End K V)
    (hz : ∀ g, Commute z ((ρ g : V ≃ₗ[K] V) : Module.End K V)) {F : Module.End K V}
    (hF : F ∈ famSet ρ z) (g : G) (v : V) : ρ g (F v) = F (ρ g v) := by
  rcases hF with rfl | ⟨h, rfl⟩
  · exact (congrArg (fun F : Module.End K V => F v) (hz g).eq).symm
  · change ρ g (ρ h v) = ρ h (ρ g v)
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul, mul_comm]

theorem exists_five_pieces {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrp : ¬ r ∣ p - 1) (hpK : (p : K) ≠ 0) (hGp : ∀ g : G, g ^ p = 1)
    (hGK : ((Fintype.card G : ℕ) : K) ≠ 0)
    (ρ : G →* (V ≃ₗ[K] V)) (hρinj : Function.Injective ρ)
    (z : Module.End K V) (hz : ∀ g, Commute z ((ρ g : V ≃ₗ[K] V) : Module.End K V))
    (hzp : z ^ p = 1) (γ : MulAut G) (k : ℕ) (hγ : γ ^ r ^ k = 1) (g₀ : G) (hg₀ : γ g₀ ≠ g₀)
    (σ : K ≃+* K) (f : V →ₛₗ[(σ : K →+* K)] V) (hf : Function.Bijective f)
    (hfρ : ∀ g v, f (ρ g v) = ρ (γ g) (f v)) (hfz : ∀ v, f (z v) = z (f v))
    (hσ : ∀ h : K[X], h.Monic → Irreducible h → h ∣ X ^ p - 1 → h.map (σ : K →+* K) = h) :
    ∃ h : K[X], Irreducible h ∧ h.Monic ∧ h ∣ X ^ p - 1 ∧
      ∃ M : Fin 5 → Submodule K V, (∀ i, M i ≠ ⊥) ∧ (∀ i, ∀ v ∈ M i, aeval z h v = 0) ∧
        (∀ i, ∀ v ∈ M i, z v ∈ M i) ∧ iSupIndep M := by
  classical
  have : RingHomSurjective (σ : K →+* K) := ⟨σ.surjective⟩
  set a : G := γ g₀ * g₀⁻¹ with ha_def
  have ha1 : a ≠ 1 := fun h => hg₀ (mul_inv_eq_one.1 h)
  have hρa : ρ a ≠ 1 := fun h => ha1 (hρinj (by rw [h, map_one]))
  let Na : Module.End K V := ∑ i ∈ Finset.range p, ((ρ (a ^ i) : V ≃ₗ[K] V) : Module.End K V)
  let U : Submodule K V := LinearMap.ker Na
  have hNa_apply : ∀ v, Na v = ∑ i ∈ Finset.range p, ρ (a ^ i) v := fun v => by
    simp [Na, LinearMap.sum_apply]
  have hUi : InvSet (famSet ρ z) U := by
    intro F hF v hv
    rw [LinearMap.mem_ker, hNa_apply] at hv ⊢
    calc ∑ i ∈ Finset.range p, ρ (a ^ i) (F v) = ∑ i ∈ Finset.range p, F (ρ (a ^ i) v) :=
          Finset.sum_congr rfl fun i _ => fam_comm ρ z hz hF _ v
      _ = F (∑ i ∈ Finset.range p, ρ (a ^ i) v) := by rw [map_sum]
      _ = 0 := by rw [hv, map_zero]
  have hU0 : U ≠ ⊥ := by
    obtain ⟨w, hw⟩ : ∃ w, ρ a w ≠ w := by
      by_contra hcon
      push Not at hcon
      exact hρa (LinearEquiv.ext hcon)
    intro hbot
    have hmem : ρ a w - w ∈ U := by
      rw [LinearMap.mem_ker, hNa_apply]
      have : ∀ i : ℕ, ρ (a ^ i) (ρ a w - w) = ρ (a ^ (i + 1)) w - ρ (a ^ i) w := by
        intro i
        rw [map_sub, ← LinearEquiv.mul_apply, ← map_mul, ← pow_succ]
      simp only [this]
      rw [Finset.sum_range_sub (fun i => ρ (a ^ i) w) p, hGp a, pow_zero, map_one]
      simp
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hw hmem
  have hUsum : ∀ v ∈ U, ∑ g : G, ρ g v = 0 := by
    intro v hv
    rw [LinearMap.mem_ker, hNa_apply] at hv
    have h1 : ∑ g : G, ρ g (∑ i ∈ Finset.range p, ρ (a ^ i) v) = (p : K) • ∑ g : G, ρ g v := by
      simp only [map_sum]
      rw [Finset.sum_comm]
      simp only [sum_absorb, Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]
    rw [hv] at h1
    simp only [map_zero, Finset.sum_const_zero] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left hpK
  obtain ⟨M, hMU, hM0, hMi, hcyc, h, hirr, hmon, hMh, hdvd⟩ :=
    exists_piece ρ z hz U hU0 hUi
  let D : Subgroup G := stabOn ρ M
  have haD : a ∉ D := by
    intro haD
    apply hM0
    rw [eq_bot_iff]
    intro v hv
    have h1 : Na v = (p : K) • v := by
      rw [hNa_apply]
      have : ∀ i : ℕ, ρ (a ^ i) v = v := fun i => (mem_stabOn.1 (D.pow_mem haD i)) v hv
      simp only [this, Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]
    have h2 : Na v = 0 := LinearMap.mem_ker.1 (hMU hv)
    rw [h1] at h2
    rw [Submodule.mem_bot]
    exact (smul_eq_zero.1 h2).resolve_left hpK
  have hDindex : D.index = p := card_quot_eq_of_cyclic hp hGp D hcyc a haD
  have hDγ : D.map (γ : G →* G) ≠ D := by
    intro hDγ
    exact haD (stable_acts_trivially hp hr hrp hGp γ hγ D hcyc hDγ a haD g₀)
  have hdvd' : h ∣ X ^ p - 1 := by
    apply hdvd
    simp [hzp]
  have hhσ : h.map (σ : K →+* K) = h := hσ h hmon hirr hdvd'
  have hh : h.map (σ.symm : K →+* K) = h := by
    have := congrArg (fun q : K[X] => q.map (σ.symm : K →+* K)) hhσ
    simp only [Polynomial.map_map] at this
    have h2 : (σ.symm : K →+* K).comp (σ : K →+* K) = RingHom.id K := by
      ext x; simp
    rw [h2, Polynomial.map_id] at this
    exact this.symm
  have hP0 : PieceProps ρ z h M D :=
    ⟨hM0, hMi, rfl, hMh, fun v hv => hUsum v (hMU hv)⟩
  let φ : Subgroup G → Subgroup G := fun H => H.map (γ : G →* G)
  let Pi : ℕ → Submodule K V := fun i => (Submodule.map f)^[i] M
  let Di : ℕ → Subgroup G := fun i => φ^[i] D
  have hPi : ∀ i, PieceProps ρ z h (Pi i) (Di i) := by
    intro i
    induction i with
    | zero => exact hP0
    | succ i ih =>
      have e1 : Pi (i + 1) = (Pi i).map f := by
        simp only [Pi]; rw [Function.iterate_succ_apply']
      have e2 : Di (i + 1) = φ (Di i) := by
        simp only [Di]; rw [Function.iterate_succ_apply']
      rw [e1, e2]
      exact PieceProps.map σ f hf.1 γ hfρ hfz hh ih
  have hDiIndex : ∀ i, (Di i).index = p := by
    intro i
    induction i with
    | zero => exact hDindex
    | succ i ih =>
      have e2 : Di (i + 1) = φ (Di i) := by
        simp only [Di]; rw [Function.iterate_succ_apply']
      rw [e2]
      change ((Di i).map (γ : G →* G)).index = p
      rw [Subgroup.index_map_equiv (Di i) γ]
      exact ih
  have hiter : ∀ (n : ℕ) (H : Subgroup G), φ^[n] H = H.map ((γ ^ n : MulAut G) : G →* G) := by
    intro n
    induction n with
    | zero =>
      intro H
      show H = H.map ((1 : MulAut G) : G →* G)
      exact (Subgroup.map_id H).symm
    | succ n ih =>
      intro H
      rw [Function.iterate_succ_apply', ih]
      change (H.map ((γ ^ n : MulAut G) : G →* G)).map (γ : G →* G) = _
      rw [Subgroup.map_map, pow_succ']
      rfl
  have hper : Function.IsPeriodicPt φ (r ^ k) D := by
    change φ^[r ^ k] D = D
    rw [hiter, hγ]
    exact Subgroup.map_id D
  have hdvdm : Function.minimalPeriod φ D ∣ r ^ k := hper.minimalPeriod_dvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).1 hdvdm
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hj
    exact hDγ (Function.minimalPeriod_eq_one_iff_isFixedPt.1 hj)
  have h5 : 5 ≤ Function.minimalPeriod φ D := by
    rw [hj]
    exact hr5.trans (Nat.le_self_pow hj0 r)
  have hdistinct : ∀ i j : Fin 5, i ≠ j → Di i ≠ Di j := by
    intro i j hij heq
    have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := φ) (x := D)
    exact hij (Fin.ext (hinj (Set.mem_Iio.2 (lt_of_lt_of_le i.2 h5))
      (Set.mem_Iio.2 (lt_of_lt_of_le j.2 h5)) heq))
  refine ⟨h, hirr, hmon, hdvd', fun i => Pi i, fun i => (hPi i).ne_bot, fun i => (hPi i).aeval_zero,
    fun i v hv => (hPi i).inv z (Or.inl rfl) v hv, ?_⟩
  refine iSupIndep_of_fixed ρ (fun i : Fin 5 => Pi i) (fun i : Fin 5 => Di i) ?_ ?_ ?_ ?_ hGK
  · intro i j hij
    exact sup_eq_top_of_index_prime hp (hDiIndex i) (hDiIndex j) (hdistinct i j hij)
  · intro i w hw d hd
    have := (hPi i).stab
    rw [← this] at hd
    exact mem_stabOn.1 hd w hw
  · intro i w hw
    exact (hPi i).sum_zero w hw
  · intro i hc
    have h1 := Subgroup.card_mul_index (Di i)
    rw [hDiIndex i] at h1
    apply hGK
    have : ((Fintype.card G : ℕ) : K) = ((Nat.card (Di i) * p : ℕ) : K) := by
      rw [h1, Nat.card_eq_fintype_card]
    rw [this]
    push_cast
    rw [hc, zero_mul]

end Main

section NumberTheory

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem exists_frobenius_exponent (σ : K ≃+* K) {n f : ℕ} (hf : Nat.card K = 2 ^ f)
    (hσ : σ ^ n = 1) :
    ∃ a : ℕ, (∀ x : K, σ x = x ^ 2 ^ a) ∧ f ∣ a * n := by
  classical
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  have : Fintype K := Fintype.ofFinite K
  have hsig : ∀ x : (ZMod 2), σ (algebraMap (ZMod 2) K x) = algebraMap (ZMod 2) K x := by
    intro x
    have := RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod 2) K)) (algebraMap (ZMod 2) K)
    exact congrArg (fun f => f x) this
  let σa : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv hsig
  obtain ⟨m, hm⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) K).2 σa
  have hF : ∀ (k : ℕ) (x : K), ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) ^ k) x =
      x ^ 2 ^ k := by
    intro k x
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp
  have hσx : ∀ x : K, σ x = x ^ 2 ^ (m : ℕ) := by
    intro x
    have := hF m x
    simp only at hm
    rw [hm] at this
    exact this
  refine ⟨m, hσx, ?_⟩
  have hσn : ∀ (k : ℕ) (x : K), (σ ^ k) x = x ^ 2 ^ (m * k) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', RingAut.mul_apply, ih, map_pow, hσx, ← pow_mul, ← pow_add]
      ring_nf
  have hFn : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) ^ (m * n) = 1 := by
    refine AlgEquiv.ext fun x => ?_
    rw [hF, ← hσn, hσ]
    rfl
  have h1 := orderOf_dvd_of_pow_eq_one hFn
  rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic] at h1
  have h2 : f = Module.finrank (ZMod 2) K := by
    have := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_zmod, hf] at this
    exact Nat.pow_right_injective (le_refl 2) this
  rw [h2]
  exact h1

theorem exists_pow_modEq {p r i a f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    (hrp : ¬ r ∣ p - 1) (hdiv : f ∣ a * r ^ i) : ∃ j : ℕ, 2 ^ a ≡ (2 ^ f) ^ j [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  let U : (ZMod p)ˣ := Units.mk0 2 h2
  let H : Subgroup (ZMod p)ˣ := Subgroup.zpowers (U ^ f)
  obtain ⟨t, ht⟩ := hdiv
  have hnorm : ((QuotientGroup.mk (U ^ a) : (ZMod p)ˣ ⧸ H)) ^ r ^ i = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← pow_mul, ht, pow_mul]
    exact H.pow_mem (Subgroup.mem_zpowers _) t
  have hord1 : orderOf (QuotientGroup.mk (U ^ a) : (ZMod p)ˣ ⧸ H) ∣ r ^ i :=
    orderOf_dvd_of_pow_eq_one hnorm
  have hcardG : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hord2 : orderOf (QuotientGroup.mk (U ^ a) : (ZMod p)ˣ ⧸ H) ∣ p - 1 :=
    (orderOf_dvd_natCard _).trans (hcardG ▸ Subgroup.card_quotient_dvd_card H)
  have hcop : Nat.Coprime (r ^ i) (p - 1) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hr).2 hrp)
  have hord : orderOf (QuotientGroup.mk (U ^ a) : (ZMod p)ˣ ⧸ H) = 1 :=
    Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd hord1 hord2)
  have hmem : U ^ a ∈ H := by
    rw [← QuotientGroup.eq_one_iff]
    exact orderOf_eq_one_iff.1 hord
  have hpow : U ^ a ∈ Submonoid.powers (U ^ f) := mem_powers_iff_mem_zpowers.2 hmem
  obtain ⟨j, hj⟩ := hpow
  refine ⟨j, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  have h3 := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hj
  simp only [Units.val_pow_eq_pow_val] at h3
  have hU : (U : ZMod p) = 2 := rfl
  rw [hU] at h3
  push_cast
  rw [← h3]

theorem map_eq_of_irreducible_dvd {p r i f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    (hrp : ¬ r ∣ p - 1) (hf : Nat.card K = 2 ^ f) (σ : K ≃+* K) (hσ : σ ^ r ^ i = 1)
    {h : K[X]} (hmon : h.Monic) (hirr : Irreducible h) (hdvd : h ∣ X ^ p - 1) :
    h.map (σ : K →+* K) = h := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_cases hX : h = X - 1
  · subst hX
    simp
  have : Fact (Irreducible h) := ⟨hirr⟩
  have : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hf]
  let E := AdjoinRoot h
  let ε : E := AdjoinRoot.root h
  have hεroot : aeval ε h = 0 := AdjoinRoot.eval₂_root h
  have hεp : ε ^ p = 1 := by
    obtain ⟨c, hc⟩ := hdvd
    have : aeval ε (X ^ p - 1 : K[X]) = 0 := by rw [hc, map_mul, hεroot, zero_mul]
    simpa [sub_eq_zero] using this
  have hε1 : ε ≠ 1 := by
    intro h1
    apply hX
    have h2 : aeval (algebraMap K E 1) h = 0 := by rw [map_one, ← h1]; exact hεroot
    rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at h2
    have h3 : h.eval 1 = 0 := (algebraMap K E).injective (h2.trans (map_zero _).symm)
    have h4 : X - C 1 ∣ h := Polynomial.dvd_iff_isRoot.2 h3
    have h5 := (Polynomial.irreducible_X_sub_C (1 : K)).associated_of_dvd hirr h4
    have h6 := eq_of_monic_of_associated hmon (Polynomial.monic_X_sub_C (1 : K)) h5.symm
    simpa using h6
  have horder : orderOf ε = p := orderOf_eq_prime hεp hε1
  obtain ⟨a, hσa, hfa⟩ := exists_frobenius_exponent σ hf hσ
  obtain ⟨j, hj⟩ := exists_pow_modEq hp hp2 hr hrp hfa
  have hcharE : CharP E 2 := charP_of_injective_algebraMap (algebraMap K E).injective 2
  have : ExpChar E 2 := ExpChar.prime Nat.prime_two
  let φ : E →+* E := iterateFrobenius E 2 a
  have hφε : φ ε = ε ^ 2 ^ a := by simp [φ, iterateFrobenius_def]
  have hφalg : ∀ c : K, φ (algebraMap K E c) = algebraMap K E (σ c) := by
    intro c
    simp [φ, iterateFrobenius_def, ← map_pow, hσa]
  have hφroot : aeval (φ ε) (h.map (σ : K →+* K)) = 0 := by
    have h1 := Polynomial.hom_eval₂ h (algebraMap K E) φ ε
    have h2 : φ.comp (algebraMap K E) = (algebraMap K E).comp (σ : K →+* K) := by
      ext c
      exact hφalg c
    rw [h2] at h1
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [← h1]
    have : eval₂ (algebraMap K E) ε h = 0 := hεroot
    rw [this, map_zero]
  have hconj : ∀ n : ℕ, aeval (ε ^ ((2 ^ f) ^ n)) h = 0 := by
    intro n
    induction n with
    | zero => simpa using hεroot
    | succ n ih =>
      have h1 : aeval ((ε ^ ((2 ^ f) ^ n)) ^ (2 ^ f)) h = (aeval (ε ^ ((2 ^ f) ^ n)) h) ^ (2 ^ f) := by
        rw [← hcardK, ← Polynomial.expand_aeval, FiniteField.Polynomial.expand_card, map_pow]
      rw [pow_succ, pow_mul, h1, ih, zero_pow (by positivity)]
  have hroot : aeval (φ ε) h = 0 := by
    have h1 : ε ^ (2 ^ a) = ε ^ ((2 ^ f) ^ j) := by
      rw [← pow_mod_orderOf ε (2 ^ a), ← pow_mod_orderOf ε ((2 ^ f) ^ j), horder]
      exact congrArg (ε ^ ·) hj
    rw [hφε, h1]
    exact hconj j
  have hirr' : Irreducible (h.map (σ : K →+* K)) := by
    have := (MulEquiv.irreducible_iff (Polynomial.mapEquiv σ) (x := h)).2 hirr
    simpa using this
  have e1 := minpoly.eq_of_irreducible_of_monic hirr hroot hmon
  have e2 := minpoly.eq_of_irreducible_of_monic hirr' hφroot (hmon.map (σ : K →+* K))
  exact e2.trans e1.symm

end NumberTheory

end CFSG.HardMathSupport.Curtis.Coordinator.SPLCell
