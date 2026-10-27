module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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

namespace CFSG.QuasithinUnique.Setup.X7

theorem isIrreducible_iff {G k V : Type*} [Monoid G] [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : ρ.IsIrreducible ↔ Nontrivial V ∧
    ∀ U : Submodule k V, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  constructor
  · intro h
    refine ⟨?_, fun U hU => ?_⟩
    · by_contra hv
      rw [not_nontrivial_iff_subsingleton] at hv
      exact bot_ne_top (α := Subrepresentation ρ)
        (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
    · rcases h.eq_bot_or_eq_top (⟨U, fun g _ hv => hU g _ hv⟩ : Subrepresentation ρ) with h1 | h1
      · exact Or.inl (congrArg Subrepresentation.toSubmodule h1)
      · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)
  · rintro ⟨hv, h⟩
    have hnt : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⊥, ⊤, fun h' => ?_⟩
      obtain ⟨x, y, hxy⟩ := hv
      have h1 : (⊥ : Subrepresentation ρ).toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule :=
        congrArg Subrepresentation.toSubmodule h'
      have h2 : (⊥ : Submodule k V) = ⊤ := h1
      have h3 : x - y ∈ (⊥ : Submodule k V) := h2 ▸ Submodule.mem_top
      exact hxy (sub_eq_zero.mp ((Submodule.mem_bot k).mp h3))
    refine ⟨fun Z => ?_⟩
    rcases h Z.toSubmodule (fun g u hu => Z.apply_mem_toSubmodule g hu) with h1 | h1
    · exact Or.inl (Subrepresentation.toSubmodule_injective h1)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h1)

@[expose] def fixedSub {G k V : Type*} [Group G] [Field k] [AddCommMonoid V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) : Submodule k V where
  carrier := {w | ∀ h ∈ H, ρ h w = w}
  zero_mem' := fun h _ => map_zero _
  add_mem' := fun {x y} hx hy h hh => by rw [map_add, hx h hh, hy h hh]
  smul_mem' := fun c x hx h hh => by rw [map_smul, hx h hh]

theorem mem_fixedSub {G k V : Type*} [Group G] [Field k] [AddCommMonoid V] [Module k V]
    {ρ : Representation k G V} {H : Subgroup G} {w : V} : w ∈ fixedSub ρ H ↔ ∀ h ∈ H, ρ h w = w :=
  Iff.rfl

theorem p_nsmul_eq_zero_of_charP {p : ℕ} {V : Type*} (k : Type*) [Field k] [CharP k p]
    [AddCommGroup V] [Module k V] (x : V) : p • x = 0 := by
  have : ((p : ℕ) : k) = 0 := CharP.cast_eq_zero k p
  rw [← Nat.cast_smul_eq_nsmul k, this, zero_smul]

section PGroup

variable {p : ℕ} {G V : Type*} (k : Type*) [Group G] [Finite G] [Field k] [CharP k p]
    [AddCommGroup V] [Module k V]


theorem exists_fixed_ne_zero_of_pGroup (hp : p.Prime) (hG : IsPGroup p G) (ρ : G →* (V →ₗ[k] V))
    {v : V} (hv : v ≠ 0) :
    ∃ w : V, w ≠ 0 ∧ (∀ g, ρ g w = w) ∧ w ∈ Submodule.span k (Set.range fun g => ρ g v) := by
  have _ : Fact p.Prime := ⟨hp⟩
  let s : Set V := Set.range fun g => ρ g v
  let X : AddSubgroup V := AddSubgroup.closure s
  have hsfin : Finite s := (Set.finite_range _).to_subtype
  have hfin : Finite X := by
    refine AddCommGroup.finite_of_fg_isAddTorsion X (fun x => ?_)
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨p, hp.pos, Subtype.ext (p_nsmul_eq_zero_of_charP k _)⟩
  have hXinv : ∀ g : G, ∀ x ∈ X, ρ g x ∈ X := by
    intro g x hx
    refine AddSubgroup.closure_induction (p := fun x _ => ρ g x ∈ X) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨h, rfl⟩
      refine AddSubgroup.subset_closure ⟨g * h, ?_⟩
      simp
    · simp
    · intro x y _ _ hx hy
      rw [map_add]; exact X.add_mem hx hy
    · intro x _ hx
      rw [map_neg]; exact X.neg_mem hx
  let φ : G →* Equiv.Perm X :=
    { toFun := fun g =>
        { toFun := fun x => ⟨ρ g x, hXinv g x x.2⟩
          invFun := fun x => ⟨ρ g⁻¹ x, hXinv g⁻¹ x x.2⟩
          left_inv := fun x => Subtype.ext (by simp [← Module.End.mul_apply, ← map_mul])
          right_inv := fun x => Subtype.ext (by simp [← Module.End.mul_apply, ← map_mul]) }
      map_one' := by ext x; simp
      map_mul' := fun g h => by ext x; simp [Module.End.mul_apply] }
  let _ : MulAction G X := MulAction.compHom X φ
  have hv0 : v ∈ X := AddSubgroup.subset_closure ⟨1, by simp⟩
  have h2 : p ∣ Nat.card X := by
    have hord : addOrderOf (⟨v, hv0⟩ : X) = p := by
      refine addOrderOf_eq_prime ?_ ?_
      · exact Subtype.ext (p_nsmul_eq_zero_of_charP k v)
      · intro h; exact hv (by simpa using congrArg Subtype.val h)
    have := addOrderOf_dvd_natCard (⟨v, hv0⟩ : X)
    rwa [hord] at this
  have hfix0 : (0 : X) ∈ MulAction.fixedPoints G X := by
    intro g
    exact Subtype.ext (by simp [MulAction.compHom_smul_def, φ])
  obtain ⟨b, hb, hb0⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point X h2 hfix0
  refine ⟨b, ?_, fun g => ?_, ?_⟩
  · intro h; exact hb0 (Subtype.ext h.symm)
  · exact congrArg Subtype.val (hb g)
  · have hbX : (b : V) ∈ X := b.2
    refine AddSubgroup.closure_induction
      (p := fun x _ => x ∈ Submodule.span k (Set.range fun g => ρ g v)) ?_ ?_ ?_ ?_ hbX
    · intro x hx; exact Submodule.subset_span hx
    · exact Submodule.zero_mem _
    · intro x y _ _ hx hy; exact Submodule.add_mem _ hx hy
    · intro x _ hx; exact Submodule.neg_mem _ hx

theorem exists_fixed_mem_of_pGroup (hp : p.Prime) (hG : IsPGroup p G) (ρ : G →* (V →ₗ[k] V))
    (W : Submodule k V)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (hne : W ≠ ⊥) : ∃ w ∈ W, w ≠ 0 ∧ ∀ g, ρ g w = w := by
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨w, hw0, hwf, hwspan⟩ := exists_fixed_ne_zero_of_pGroup k hp hG ρ hv0
  refine ⟨w, ?_, hw0, hwf⟩
  refine (Submodule.span_le.mpr ?_) hwspan
  rintro _ ⟨g, rfl⟩
  exact hW g v hvW

end PGroup


section Regular

variable {G : Type*} (k : Type*) [Group G] [Field k]

@[expose] def regRep : G →* ((G → k) →ₗ[k] (G → k)) where
  toFun h := LinearMap.funLeft k k (fun g => h⁻¹ * g)
  map_one' := by ext c g; simp [LinearMap.funLeft]
  map_mul' h₁ h₂ := by ext c g; simp [LinearMap.funLeft, mul_assoc]

theorem regRep_apply (h : G) (c : G → k) (g : G) : regRep k h c g = c (h⁻¹ * g) := rfl

end Regular

section Norm

variable {p : ℕ} {G V : Type*} (k : Type*) [Group G] [Fintype G] [Field k] [CharP k p]
    [AddCommGroup V] [Module k V]

theorem linearIndependent_orbit_of_norm_ne_zero (hp : p.Prime) (hG : IsPGroup p G)
    (ρ : G →* (V →ₗ[k] V)) (v : V) (hv : ∑ g, ρ g v ≠ 0) :
    LinearIndependent k (fun g : G => ρ g v) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  let Φ := Fintype.linearCombination k (fun g : G => ρ g v)
  have hΦ : ∀ h c, Φ (regRep k h c) = ρ h (Φ c) := by
    intro h c
    simp only [Φ, Fintype.linearCombination_apply, map_sum, map_smul, regRep_apply]
    refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ (fun g => ?_)
    simp [← Module.End.mul_apply, ← map_mul]
  have hker : ∀ h, ∀ c ∈ LinearMap.ker Φ, regRep k h c ∈ LinearMap.ker Φ := by
    intro h c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [hΦ, hc, map_zero]
  have hcker : c ∈ LinearMap.ker Φ := by
    rw [LinearMap.mem_ker]
    simpa [Φ, Fintype.linearCombination_apply] using hc
  have hne' : LinearMap.ker Φ ≠ ⊥ := by
    obtain ⟨g, hg⟩ := hne
    intro hbot
    rw [hbot] at hcker
    have : c = 0 := hcker
    exact hg (by simp [this])
  obtain ⟨w, hwker, hw0, hwfix⟩ := exists_fixed_mem_of_pGroup k hp hG (regRep k)
    (LinearMap.ker Φ) hker hne'
  have hconst : ∀ g, w g = w 1 := by
    intro g
    have := congrFun (hwfix g) g
    rw [regRep_apply, inv_mul_cancel] at this
    exact this.symm
  have hΦw : Φ w = w 1 • ∑ g, ρ g v := by
    simp only [Φ, Fintype.linearCombination_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun g _ => by rw [hconst g])
  have hw1 : w 1 ≠ 0 := by
    intro h
    apply hw0
    funext g
    rw [hconst g, h]; rfl
  have : Φ w = 0 := hwker
  rw [hΦw] at this
  exact hv ((smul_eq_zero.mp this).resolve_left hw1)

theorem equivFun_orbit_basis (ρ : G →* (V →ₗ[k] V)) (b : Module.Basis G k V)
    (hb : ∀ g h, b (g * h) = ρ g (b h)) (g : G) (x : V) :
    b.equivFun (ρ g x) = regRep k g (b.equivFun x) := by
  classical
  have : (b.equivFun : V →ₗ[k] (G → k)) ∘ₗ ρ g = regRep k g ∘ₗ (b.equivFun : V →ₗ[k] (G → k)) := by
    refine b.ext (fun h => ?_)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_apply,
      Module.Basis.repr_self]
    rw [← hb]
    funext g'
    simp only [regRep_apply, Module.Basis.repr_self, Finsupp.single_apply]
    have key : (g * h = g') ↔ (h = g⁻¹ * g') := by
      rw [eq_inv_mul_iff_mul_eq, eq_comm]
    by_cases h' : g * h = g'
    · simp [key.mp h']
    · have hne : ¬ h = g⁻¹ * g' := fun hh => h' (key.mpr hh)
      simp [h', hne]
  exact congrArg (fun T : V →ₗ[k] (G → k) => T x) this


theorem orbit_regular_of_norm_ne_zero [FiniteDimensional k V] (hp : p.Prime) (hG : IsPGroup p G)
    (ρ : G →* (V →ₗ[k] V)) (v : V) (hv : ∑ g, ρ g v ≠ 0)
    (hdim : Module.finrank k V = Fintype.card G) :
    ∃ b : Module.Basis G k V, (∀ g, b g = ρ g v) ∧ (∀ g h, b (g * h) = ρ g (b h)) ∧
      Module.finrank k (fixedSub ρ ⊤) = 1 := by
  classical
  have hli := linearIndependent_orbit_of_norm_ne_zero k hp hG ρ v hv
  have : Nonempty G := ⟨1⟩
  let b : Module.Basis G k V := basisOfLinearIndependentOfCardEqFinrank hli hdim.symm
  have hbg : ∀ g, b g = ρ g v := fun g => by simp [b]
  have hb : ∀ g h, b (g * h) = ρ g (b h) := by
    intro g h
    rw [hbg, hbg, ← Module.End.mul_apply, ← map_mul]
  refine ⟨b, hbg, hb, ?_⟩
  set n : V := ∑ g, ρ g v with hn
  have hnfix : ∀ g, ρ g n = n := by
    intro g
    simp only [hn, map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => by
      simp [← Module.End.mul_apply, ← map_mul])
  have hfix : fixedSub ρ ⊤ = Submodule.span k {n} := by
    apply le_antisymm
    · intro w hw
      have hc : ∀ g, b.equivFun w g = b.equivFun w 1 := by
        intro g
        have h1 := equivFun_orbit_basis k ρ b hb g w
        rw [hw g trivial] at h1
        have := congrFun h1 g
        rw [regRep_apply, inv_mul_cancel] at this
        exact this
      have hw' : w = b.equivFun w 1 • n := by
        conv_lhs => rw [← b.sum_equivFun w]
        simp only [hn, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [hc g, hbg]
      exact Submodule.mem_span_singleton.mpr ⟨_, hw'.symm⟩
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact fun g _ => hnfix g
  rw [hfix]
  exact finrank_span_singleton hv

end Norm

section HighestVector

variable {p : ℕ} {G V : Type*} (k : Type*) [Group G] [Field k] [CharP k p] [AddCommGroup V]
    [Module k V]

theorem fixedSub_eq_span_and_irreducible (hp : p.Prime) (ρ : Representation k G V)
    (Pm Pp : Subgroup G) [Finite Pp] (hPp : IsPGroup p Pp) (J : G)
    (hJ : ∀ u ∈ Pm, J * u * J⁻¹ ∈ Pp) (v : V) (hv0 : v ≠ 0) (hv : v ∈ fixedSub ρ Pp)
    (hspan : Submodule.span k (Set.range fun u : Pm => ρ u v) = ⊤)
    (hline : ∃ n ∈ fixedSub ρ Pm, ∀ w ∈ fixedSub ρ Pm, ∃ c : k, w = c • n) :
    fixedSub ρ Pp = Submodule.span k {v} ∧ ρ.IsIrreducible := by
  classical
  obtain ⟨n, hn, hline⟩ := hline
  have hconj : ∀ w ∈ fixedSub ρ Pp, ∃ c : k, w = c • ρ J n := by
    intro w hw
    have hw' : ρ J⁻¹ w ∈ fixedSub ρ Pm := by
      intro u hu
      have := hw (J * u * J⁻¹) (hJ u hu)
      calc ρ u (ρ J⁻¹ w) = ρ J⁻¹ (ρ (J * u * J⁻¹) w) := by
            rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
            congr 2
            group
        _ = ρ J⁻¹ w := by rw [this]
    obtain ⟨c, hc⟩ := hline _ hw'
    refine ⟨c, ?_⟩
    calc w = ρ J (ρ J⁻¹ w) := by rw [← Module.End.mul_apply, ← map_mul]; simp
      _ = c • ρ J n := by rw [hc, map_smul]
  obtain ⟨c₀, hc₀⟩ := hconj v hv
  have hc₀ne : c₀ ≠ 0 := by
    rintro rfl
    apply hv0
    simpa using hc₀
  have hfix : fixedSub ρ Pp = Submodule.span k {v} := by
    apply le_antisymm
    · intro w hw
      obtain ⟨c, hc⟩ := hconj w hw
      refine Submodule.mem_span_singleton.mpr ⟨c / c₀, ?_⟩
      rw [hc₀, smul_smul, div_mul_cancel₀ _ hc₀ne, hc]
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hv
  refine ⟨hfix, (isIrreducible_iff ρ).mpr ⟨⟨v, 0, hv0⟩, fun W hW => ?_⟩⟩
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0, hwfix⟩ := exists_fixed_mem_of_pGroup k hp hPp (ρ.comp Pp.subtype) W
    (fun g w hw => hW g.1 w hw) hbot
  have hwmem : w ∈ fixedSub ρ Pp := fun h hh => hwfix ⟨h, hh⟩
  rw [hfix] at hwmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwmem
  have hcne : c ≠ 0 := by
    rintro rfl
    apply hw0
    rw [← hc]
    simp
  have hvW : v ∈ W := by
    have : v = c⁻¹ • w := by rw [← hc, smul_smul, inv_mul_cancel₀ hcne, one_smul]
    rw [this]
    exact W.smul_mem _ hwW
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro _ ⟨u, rfl⟩
  exact hW u v hvW

end HighestVector

open scoped Matrix

section MatrixRep

variable {G κ k : Type*} [Group G] [Field k] [Fintype κ] [DecidableEq κ]

@[expose] def matRep (R : G →* Matrix κ κ k) : Representation k G (κ → k) where
  toFun g := Matrix.mulVecLin (R g)
  map_one' := by rw [map_one, Matrix.mulVecLin_one]; rfl
  map_mul' g h := by rw [map_mul, Matrix.mulVecLin_mul]; rfl

theorem matRep_apply (R : G →* Matrix κ κ k) (g : G) (w : κ → k) :
    matRep R g w = (R g).mulVec w := rfl

theorem span_orbit_eq_top_of_coords (R : G →* Matrix κ κ k) (Pm : Subgroup G) (v : κ → k)
    (hli : LinearIndependent k (fun x : κ => fun u : Pm => ((R u).mulVec v) x)) :
    Submodule.span k (Set.range fun u : Pm => matRep R u v) = ⊤ := by
  by_contra hne
  have hlt : Submodule.span k (Set.range fun u : Pm => matRep R u v) < ⊤ :=
    lt_top_iff_ne_top.mpr hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  apply hφ0
  set a : κ → k := fun x => φ (fun j => if x = j then 1 else 0) with ha
  have hφa : ∀ w, φ w = ∑ x, w x * a x := by
    intro w
    rw [LinearMap.pi_apply_eq_sum_univ φ w]
    simp [ha, smul_eq_mul]
  have hzero : ∀ u : Pm, φ (matRep R u v) = 0 := by
    intro u
    have : φ (matRep R u v) ∈ Submodule.map φ (Submodule.span k (Set.range fun u : Pm => matRep R u v)) :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨u, rfl⟩)
    rw [hφ] at this
    simpa using this
  have hsum : ∑ x, a x • (fun u : Pm => ((R u).mulVec v) x) = 0 := by
    funext u
    have := hzero u
    rw [hφa] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [matRep_apply, mul_comm]
  have ha0 : ∀ x, a x = 0 := Fintype.linearIndependent_iff.mp hli a hsum
  refine LinearMap.ext (fun w => ?_)
  rw [hφa]
  simp [ha0]

theorem hline_of_cocyclic (R : G →* Matrix κ κ k) (Pm : Subgroup G) (y : κ → k)
    (hy : Submodule.span k (Set.range fun u : Pm => (R (u : G)⁻¹)ᵀ.mulVec y) = ⊤) :
    ∃ n ∈ fixedSub (matRep R) Pm, ∀ w ∈ fixedSub (matRep R) Pm, ∃ c : k, w = c • n := by
  classical
  let ℓ : (κ → k) →ₗ[k] k :=
    { toFun := fun w => y ⬝ᵥ w
      map_add' := fun a b => dotProduct_add _ _ _
      map_smul' := fun c w => by simp [dotProduct_smul] }
  have hℓ : ∀ w ∈ fixedSub (matRep R) Pm, ℓ w = 0 → w = 0 := by
    intro w hw hlw
    have horb : ∀ u : Pm, ((R (u : G)⁻¹)ᵀ.mulVec y) ⬝ᵥ w = 0 := by
      intro u
      rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
      have := hw ((u : G)⁻¹) (Pm.inv_mem u.2)
      rw [matRep_apply] at this
      rw [this]
      exact hlw
    let ψ : (κ → k) →ₗ[k] k :=
      { toFun := fun z => z ⬝ᵥ w
        map_add' := fun a b => add_dotProduct _ _ _
        map_smul' := fun c z => by simp [smul_dotProduct] }
    have hψ : Submodule.span k (Set.range fun u : Pm => (R (u : G)⁻¹)ᵀ.mulVec y) ≤ LinearMap.ker ψ := by
      rw [Submodule.span_le]
      rintro _ ⟨u, rfl⟩
      exact horb u
    rw [hy] at hψ
    funext x
    have := hψ (Submodule.mem_top : (Pi.single x (1 : k) : κ → k) ∈ (⊤ : Submodule k (κ → k)))
    rw [LinearMap.mem_ker] at this
    simpa [ψ] using this
  let F₀ := fixedSub (matRep R) Pm
  have hinj : Function.Injective (ℓ.domRestrict F₀) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h0 : w = 0 := Subtype.ext (hℓ w w.2 hw)
    exact h0
  have hrank : Module.finrank k F₀ ≤ 1 := by
    calc Module.finrank k F₀ ≤ Module.finrank k k := LinearMap.finrank_le_finrank_of_injective hinj
      _ = 1 := Module.finrank_self k
  obtain ⟨n, hn⟩ := finrank_le_one_iff.mp hrank
  exact ⟨n.1, n.2, fun w hw => by
    obtain ⟨c, hc⟩ := hn ⟨w, hw⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩⟩

theorem coords_linearIndependent_of_span (R : G →* Matrix κ κ k) (Pm : Subgroup G) (v : κ → k)
    (hspan : Submodule.span k (Set.range fun u : Pm => matRep R u v) = ⊤) :
    LinearIndependent k (fun x : κ => fun u : Pm => ((R u).mulVec v) x) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  let ψ : (κ → k) →ₗ[k] k :=
    { toFun := fun w => ∑ x, a x * w x
      map_add' := fun w w' => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c w => by simp [Finset.mul_sum, mul_left_comm] }
  have hψ : Submodule.span k (Set.range fun u : Pm => matRep R u v) ≤ LinearMap.ker ψ := by
    rw [Submodule.span_le]
    rintro _ ⟨u, rfl⟩
    have := congrFun ha u
    simpa [ψ, Finset.sum_apply, matRep_apply] using this
  rw [hspan] at hψ
  intro x
  have := hψ (Submodule.mem_top : (Pi.single x (1 : k) : κ → k) ∈ (⊤ : Submodule k (κ → k)))
  rw [LinearMap.mem_ker] at this
  simpa [ψ, Pi.single_apply] using this

end MatrixRep

section FixedSub

variable {G V k : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]

theorem fixedSub_comp_subtype (ρ : Representation k G V) (H : Subgroup G) :
    fixedSub (ρ.comp H.subtype) ⊤ = fixedSub ρ H := by
  ext w
  simp only [mem_fixedSub, Subgroup.mem_top, forall_true_left, MonoidHom.comp_apply,
    Subgroup.subtype_apply]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g.1 g.2⟩

theorem hline_of_finrank_le_one [FiniteDimensional k V] (ρ : Representation k G V) (H : Subgroup G)
    (h : Module.finrank k (fixedSub ρ H) ≤ 1) :
    ∃ n ∈ fixedSub ρ H, ∀ w ∈ fixedSub ρ H, ∃ c : k, w = c • n := by
  obtain ⟨n, hn⟩ := finrank_le_one_iff.mp h
  exact ⟨n.1, n.2, fun w hw => by
    obtain ⟨c, hc⟩ := hn ⟨w, hw⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩⟩

end FixedSub


section Node

variable {p : ℕ} {G V : Type*} (k : Type*) [Group G] [Fintype G] [Field k] [CharP k p]
    [AddCommGroup V] [Module k V]

theorem pGroup_norm_orbit_independence [FiniteDimensional k V] (hp : p.Prime) (hG : IsPGroup p G)
    (ρ : G →* (V →ₗ[k] V)) :
    (Nontrivial V → ∃ w : V, w ≠ 0 ∧ ∀ g, ρ g w = w) ∧
    (∀ v : V, ∑ g, ρ g v ≠ 0 → LinearIndependent k (fun g : G => ρ g v)) ∧
    (∀ v : V, ∑ g, ρ g v ≠ 0 → Module.finrank k V = Fintype.card G →
      ∃ b : Module.Basis G k V, (∀ g, b g = ρ g v) ∧ (∀ g h, b (g * h) = ρ g (b h)) ∧
        Module.finrank k (fixedSub ρ ⊤) = 1) := by
  refine ⟨fun hnt => ?_, fun v hv => linearIndependent_orbit_of_norm_ne_zero k hp hG ρ v hv,
    fun v hv hdim => orbit_regular_of_norm_ne_zero k hp hG ρ v hv hdim⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw0, hwf, -⟩ := exists_fixed_ne_zero_of_pGroup k hp hG ρ hv
  exact ⟨w, hw0, hwf⟩

end Node

end CFSG.QuasithinUnique.Setup.X7
