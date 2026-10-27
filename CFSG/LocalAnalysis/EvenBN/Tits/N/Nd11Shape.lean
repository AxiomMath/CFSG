module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.Frattini
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11

private theorem nd11_eq_two_or_four {m : ℕ} (h1 : 1 < m) (h4 : m ∣ 4) : m = 2 ∨ m = 4 := by
  have := Nat.le_of_dvd (by norm_num) h4
  interval_cases m <;> omega

private theorem nd11_card_tors {m : ℕ} (h : m = 2 ∨ m = 4) :
    Nat.card {z : Multiplicative (ZMod m) // z * z = 1} = 2 := by
  rcases h with rfl | rfl <;> (rw [Nat.card_eq_fintype_card]; decide)

private theorem nd11_counts {ι : Type} [Fintype ι] (n : ι → ℕ) (hn : ∀ i, n i = 2 ∨ n i = 4)
    (hι : Fintype.card ι = 8) (hprod : ∏ i, n i = 2 ^ 10) :
    Fintype.card {i // n i = 2} = 6 ∧ Fintype.card {i // n i = 4} = 2 := by
  classical
  have hAB : (Finset.univ.filter (fun i => n i = 2)).card +
      (Finset.univ.filter (fun i => ¬ n i = 2)).card = 8 := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, hι]
  have hB : Finset.univ.filter (fun i => ¬ n i = 2) = Finset.univ.filter (fun i => n i = 4) :=
    Finset.filter_congr fun i _ => ⟨fun h => (hn i).resolve_left h, fun h => by omega⟩
  have hp : ∏ i, n i = 2 ^ (Finset.univ.filter (fun i => n i = 2)).card *
      4 ^ (Finset.univ.filter (fun i => ¬ n i = 2)).card := by
    have : ∏ i, n i = ∏ i, (if n i = 2 then 2 else 4) :=
      Finset.prod_congr rfl fun i _ => by rcases hn i with h | h <;> simp [h]
    rw [this, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  rw [hp, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add] at hprod
  have h10 := Nat.pow_right_injective (le_refl 2) hprod
  rw [Fintype.card_subtype, Fintype.card_subtype]
  rw [hB] at hAB h10
  omega

private theorem nd11_pi_equiv {ι : Type} [Fintype ι] (n : ι → ℕ) (hn : ∀ i, n i = 2 ∨ n i = 4)
    (h2 : Fintype.card {i // n i = 2} = 6) (h4 : Fintype.card {i // n i = 4} = 2) :
    Nonempty (((i : ι) → Multiplicative (ZMod (n i))) ≃*
      Multiplicative (Fin 6 → ZMod 2) × (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  classical
  have e₁ : ((i : ι) → Multiplicative (ZMod (n i))) ≃*
      (((i : {i // n i = 2}) → Multiplicative (ZMod (n i))) ×
        ((i : {i // ¬ n i = 2}) → Multiplicative (ZMod (n i)))) :=
    { Equiv.piEquivPiSubtypeProd (fun i => n i = 2) (fun i => Multiplicative (ZMod (n i))) with
      map_mul' := fun _ _ => rfl }
  have σ₂ : {i // n i = 2} ≃ Fin 6 := Fintype.equivFinOfCardEq h2
  have h4' : Fintype.card {i // ¬ n i = 2} = 2 :=
    (Fintype.card_congr (Equiv.subtypeEquivRight fun i =>
      ⟨fun h => (hn i).resolve_left h, fun h => by omega⟩)).trans h4
  have σ₄ : {i // ¬ n i = 2} ≃ Fin 2 := Fintype.equivFinOfCardEq h4'
  have e₂a : ((i : {i // n i = 2}) → Multiplicative (ZMod (n i))) ≃*
      ({i // n i = 2} → Multiplicative (ZMod 2)) :=
    MulEquiv.piCongrRight fun i => AddEquiv.toMultiplicative (ZMod.ringEquivCongr i.2).toAddEquiv
  have e₂b : ({i // n i = 2} → Multiplicative (ZMod 2)) ≃* (Fin 6 → Multiplicative (ZMod 2)) :=
    { Equiv.arrowCongr σ₂ (Equiv.refl _) with map_mul' := fun _ _ => rfl }
  have e₂c : (Fin 6 → Multiplicative (ZMod 2)) ≃* Multiplicative (Fin 6 → ZMod 2) :=
    (MulEquiv.piMultiplicative (fun _ : Fin 6 => ZMod 2)).symm
  have e₃a : ((i : {i // ¬ n i = 2}) → Multiplicative (ZMod (n i))) ≃*
      ({i // ¬ n i = 2} → Multiplicative (ZMod 4)) :=
    MulEquiv.piCongrRight fun i => AddEquiv.toMultiplicative
      (ZMod.ringEquivCongr ((hn i).resolve_left i.2)).toAddEquiv
  have e₃b : ({i // ¬ n i = 2} → Multiplicative (ZMod 4)) ≃* (Fin 2 → Multiplicative (ZMod 4)) :=
    { Equiv.arrowCongr σ₄ (Equiv.refl _) with map_mul' := fun _ _ => rfl }
  have e₃c : (Fin 2 → Multiplicative (ZMod 4)) ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
    { piFinTwoEquiv (fun _ => Multiplicative (ZMod 4)) with map_mul' := fun _ _ => rfl }
  exact ⟨e₁.trans (MulEquiv.prodCongr (e₂a.trans (e₂b.trans e₂c)) (e₃a.trans (e₃b.trans e₃c)))⟩

private theorem nd11_eq_of_ne_one :
    ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a = b := by
  decide

theorem abelian_shape {Γ : Type*} [Group Γ] [Finite Γ] [IsMulCommutative Γ]
    (hcard : Nat.card Γ = 2 ^ 10) (S : Subgroup Γ) (hS4 : Nat.card S = 4)
    (hsq : ∀ x : Γ, x * x ∈ S) (hsq' : ∀ s ∈ S, ∃ x : Γ, x * x = s) (hex : ∀ x : Γ, x ^ 4 = 1) :
    Nonempty (Γ ≃* Multiplicative (Fin 6 → ZMod 2) ×
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  classical
  letI : CommGroup Γ :=
    { (inferInstance : Group Γ) with mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  obtain ⟨ι, hι, n, hn1, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite Γ
  have hdvd : ∀ i, n i ∣ 4 := by
    intro i
    have hy : (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (n i))) :
        (j : ι) → Multiplicative (ZMod (n j))) ^ 4 = 1 := by
      have h := congrArg e (hex (e.symm (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (n i))))))
      rwa [map_pow, MulEquiv.apply_symm_apply, e.map_one] at h
    have hi := congrFun hy i
    rw [Pi.pow_apply, Pi.mulSingle_eq_same, Pi.one_apply] at hi
    have := orderOf_dvd_of_pow_eq_one hi
    rwa [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one] at this
  have hn : ∀ i, n i = 2 ∨ n i = 4 := fun i => nd11_eq_two_or_four (hn1 i) (hdvd i)
  have hprod : ∏ i, n i = 2 ^ 10 := by
    rw [← hcard, Nat.card_congr e.toEquiv, Nat.card_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (n i)) ≃ ZMod (n i)),
      Nat.card_zmod]
  let sq : Γ →* Γ := powMonoidHom 2
  have hrange : sq.range = S := by
    ext s
    constructor
    · rintro ⟨x, rfl⟩
      simpa [sq, pow_two] using hsq x
    · intro hs
      obtain ⟨x, hx⟩ := hsq' s hs
      exact ⟨x, by simpa [sq, pow_two] using hx⟩
  have hker : Nat.card sq.ker = 2 ^ 8 := by
    have h := Subgroup.card_ker_mul_card_range sq
    rw [hrange, hS4, hcard] at h
    omega
  have hcardι : Fintype.card ι = 8 := by
    have h1 : Nat.card sq.ker = Nat.card {x : Γ // x * x = 1} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [sq, pow_two, MonoidHom.mem_ker])
    have h2 : Nat.card {x : Γ // x * x = 1} =
        Nat.card {y : (i : ι) → Multiplicative (ZMod (n i)) // y * y = 1} :=
      Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
        show x * x = 1 ↔ e x * e x = 1
        rw [← map_mul]
        exact (map_eq_one_iff e e.injective).symm)
    have h3 : Nat.card {y : (i : ι) → Multiplicative (ZMod (n i)) // y * y = 1} =
        ∏ i, Nat.card {z : Multiplicative (ZMod (n i)) // z * z = 1} := by
      have e1 : {y : (i : ι) → Multiplicative (ZMod (n i)) // y * y = 1} ≃
          {y : (i : ι) → Multiplicative (ZMod (n i)) // ∀ i, y i * y i = 1} :=
        Equiv.subtypeEquivRight fun y => by simp [funext_iff]
      rw [Nat.card_congr e1, Nat.card_congr (Equiv.subtypePiEquivPi (p := fun i z => z * z = 1)),
        Nat.card_pi]
    have h4 : ∏ i, Nat.card {z : Multiplicative (ZMod (n i)) // z * z = 1} =
        2 ^ Fintype.card ι := by
      rw [Finset.prod_congr rfl fun i _ => nd11_card_tors (hn i), Finset.prod_const,
        Finset.card_univ]
    have h5 : 2 ^ Fintype.card ι = 2 ^ 8 := by rw [← h4, ← h3, ← h2, ← h1, hker]
    exact Nat.pow_right_injective (le_refl 2) h5
  obtain ⟨hA, hB⟩ := nd11_counts n hn hcardι hprod
  obtain ⟨E⟩ := nd11_pi_equiv n hn hA hB
  exact ⟨e.trans E⟩

theorem frattini_eq_squares {Γ : Type*} [Group Γ] [Finite Γ] [IsMulCommutative Γ]
    (h2 : IsPGroup 2 Γ) (S : Subgroup Γ) (hsq : ∀ x : Γ, x * x ∈ S)
    (hsq' : ∀ s ∈ S, ∃ x : Γ, x * x = s) : frattini Γ = S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent Γ := h2.isNilpotent
  letI : CommGroup Γ :=
    { (inferInstance : Group Γ) with mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  apply le_antisymm
  · intro x hx
    by_contra hxS
    haveI : Module (ZMod 2) (Additive (Γ ⧸ S)) := AddCommGroup.zmodModule (n := 2) (fun q => by
      obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
      have hq : q = Additive.ofMul (QuotientGroup.mk y : Γ ⧸ S) := by
        rw [hy]; rfl
      rw [hq, ← ofMul_pow, pow_two, ← QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (hsq y)]
      rfl)
    have hv : (Additive.ofMul (QuotientGroup.mk x : Γ ⧸ S)) ≠ 0 := by
      intro h
      exact hxS ((QuotientGroup.eq_one_iff x).1 (ofMul_eq_zero.1 h))
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual (ZMod 2) (Additive (Γ ⧸ S)),
        f (Additive.ofMul (QuotientGroup.mk x : Γ ⧸ S)) ≠ 0 :=
      not_forall.1 fun h => hv ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).1 h)
    let φ : Γ →* Multiplicative (ZMod 2) :=
      (AddMonoidHom.toMultiplicativeRight f.toAddMonoidHom).comp (QuotientGroup.mk' S)
    have hφx : φ x ≠ 1 := fun h => hf (by simpa [φ] using h)
    have hsurj : Function.Surjective φ := by
      intro y
      by_cases hy : y = 1
      · exact ⟨1, by rw [map_one, hy]⟩
      · exact ⟨x, nd11_eq_of_ne_one _ _ hφx hy⟩
    have hind : φ.ker.index = 2 := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top]
      simp
    have hK : IsCoatom φ.ker :=
      Subgroup.isCoatom_of_index_prime (by rw [hind]; exact Nat.prime_two)
    exact hφx (MonoidHom.mem_ker.1 (frattini_le_coatom hK hx))
  · intro s hs
    obtain ⟨x, rfl⟩ := hsq' s hs
    unfold frattini Order.radical
    rw [Subgroup.mem_iInf]
    intro K
    rw [Subgroup.mem_iInf]
    intro hK
    exact Subgroup.mul_self_mem_of_index_two ((h2.isCoatom_iff_index_eq_prime).1 hK) x

end CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11
