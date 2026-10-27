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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.CGT.T75N

open Equiv Matrix MatrixGroups

section Count

theorem card_modEq_set_fixed {α : Type*} [Finite α] {p k : ℕ} [Fact p.Prime] (σ : Perm α)
    (hσ : σ ^ p ^ k = 1) (S : Set α) (hS : ∀ x, x ∈ S ↔ σ x ∈ S) :
    Nat.card S ≡ Nat.card {x : α | x ∈ S ∧ σ x = x} [MOD p] := by
  classical
  have : Fintype α := Fintype.ofFinite α
  let τ : Perm S := σ.subtypePerm (fun x => (hS x).symm)
  have hτ : τ ^ p ^ k = 1 := by
    have h1 : τ ^ p ^ k = (σ ^ p ^ k).subtypePerm (fun x => by
        simp only [hσ, Perm.coe_one]; exact Iff.rfl) := Perm.subtypePerm_pow _ _ _
    rw [h1]
    ext x
    simp [hσ]
  have hmod := Perm.card_compl_support_modEq hτ
  have hfix : ∀ y : S, y ∈ τ.supportᶜ ↔ σ y.1 = y.1 := by
    intro y
    rw [Finset.mem_compl, Perm.mem_support, not_not]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  have hcard : (τ.supportᶜ).card = Nat.card {x : α | x ∈ S ∧ σ x = x} := by
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, (hfix x.1).1 x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, (hfix _).2 y.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [hcard, ← Nat.card_eq_fintype_card] at hmod
  exact hmod.symm

end Count

section Ppd

variable {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Module F V] [Finite V]
  {n p : ℕ} [hp : Fact p.Prime]

omit [Fintype F] in
theorem card_modEq_submodule (y : V ≃ₗ[F] V) (hy : y ^ p = 1) (W : Submodule F V)
    (hW : ∀ v ∈ W, y v ∈ W) :
    Nat.card W ≡ Nat.card {v : V | v ∈ W ∧ y v = v} [MOD p] := by
  let σ : Perm V := MulAction.toPermHom (V ≃ₗ[F] V) V y
  have hσ : σ ^ p ^ 1 = 1 := by
    rw [pow_one, ← map_pow, hy, map_one]
  have hpow : ∀ k : ℕ, ∀ v ∈ W, (y ^ k) v ∈ W := by
    intro k
    induction k with
    | zero => intro v hv; simpa using hv
    | succ k ih =>
      intro v hv
      rw [pow_succ, LinearEquiv.mul_apply]
      exact ih _ (hW v hv)
  have hinv : ∀ v ∈ W, y⁻¹ v ∈ W := by
    intro v hv
    have h1 : y⁻¹ = y ^ (p - 1) := by
      have hp1 : 1 ≤ p := hp.out.one_lt.le
      have : y * y ^ (p - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hp1, hy]
      exact (inv_eq_of_mul_eq_one_right this)
    rw [h1]
    exact hpow _ v hv
  have hS : ∀ x, x ∈ (W : Set V) ↔ σ x ∈ (W : Set V) := by
    intro x
    constructor
    · intro hx; exact hW x hx
    · intro hx
      have : y⁻¹ (y x) ∈ W := hinv _ hx
      simpa using this
  have h := card_modEq_set_fixed σ hσ (W : Set V) hS
  have e : {x : V | x ∈ (W : Set V) ∧ σ x = x} = {v : V | v ∈ W ∧ y v = v} := rfl
  rw [e] at h
  exact h


omit [Fintype F] in
theorem natCard_eq_pow {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Module F V]
    [Finite V] (W : Submodule F V) : Nat.card W = Fintype.card F ^ Module.finrank F W := by
  have : Module.Finite F W := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card (α := F)]

theorem simple_of_ppd (hn : Module.finrank F V = n) (hpn : p ∣ Fintype.card F ^ n - 1)
    (hnp : ∀ k, 0 < k → k < n → ¬ p ∣ Fintype.card F ^ k - 1)
    (y : V ≃ₗ[F] V) (hy : y ^ p = 1) (hy1 : y ≠ 1) :
    (∀ v : V, y v = v → v = 0) ∧
      ∀ W : Submodule F V, (∀ v ∈ W, y v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  set q := Fintype.card F with hq
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hmod1 : ∀ k : ℕ, p ∣ q ^ k - 1 → q ^ k ≡ 1 [MOD p] := fun k hk =>
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq1)).2 hk).symm
  have hmod2 : ∀ k : ℕ, q ^ k ≡ 1 [MOD p] → p ∣ q ^ k - 1 := fun k hk =>
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq1)).1 hk.symm
  let Fix : Submodule F V := LinearMap.ker (y.toLinearMap - LinearMap.id)
  have hFix : ∀ v : V, v ∈ Fix ↔ y v = v := by
    intro v
    simp [Fix, LinearMap.mem_ker, sub_eq_zero]
  have hcardV : Nat.card V = q ^ n := by
    have : Module.Finite F V := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card (α := F), hn]
  have hFixZero : ∀ v : V, y v = v → v = 0 := by
    have hm := card_modEq_submodule y hy ⊤ (fun _ _ => trivial)
    have e1 : Nat.card (⊤ : Submodule F V) = q ^ n := by
      rw [← hcardV]; exact Nat.card_congr Submodule.topEquiv.toEquiv
    have e2 : {v : V | v ∈ (⊤ : Submodule F V) ∧ y v = v} = (Fix : Set V) := by
      ext v; simp [hFix]
    rw [e1, e2] at hm
    have hm' : q ^ n ≡ q ^ Module.finrank F Fix [MOD p] := by
      have := natCard_eq_pow Fix
      rw [show Nat.card (Fix : Set V) = Nat.card Fix from rfl, this] at hm
      exact hm
    have hj : p ∣ q ^ Module.finrank F Fix - 1 :=
      hmod2 _ (hm'.symm.trans (hmod1 n hpn))
    have hjle : Module.finrank F Fix ≤ n := hn ▸ Submodule.finrank_le Fix
    have hj0 : Module.finrank F Fix = 0 := by
      by_contra hne
      have hpos : 0 < Module.finrank F Fix := Nat.pos_of_ne_zero hne
      rcases lt_or_eq_of_le hjle with hlt | heq
      · exact hnp _ hpos hlt hj
      · apply hy1
        have htop : Fix = ⊤ := Submodule.eq_top_of_finrank_eq (heq.trans hn.symm)
        ext v
        exact (hFix v).1 (htop ▸ Submodule.mem_top)
    intro v hv
    have : v ∈ Fix := (hFix v).2 hv
    rw [Submodule.finrank_eq_zero.1 hj0] at this
    simpa using this
  refine ⟨hFixZero, fun W hW => ?_⟩
  have hm := card_modEq_submodule y hy W hW
  have e : {v : V | v ∈ W ∧ y v = v} = {0} := by
    ext v
    constructor
    · rintro ⟨-, hv⟩
      exact hFixZero v hv
    · intro hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact ⟨W.zero_mem, map_zero y⟩
  rw [e] at hm
  have hcard1 : Nat.card ({0} : Set V) = 1 := by simp
  rw [hcard1, natCard_eq_pow W] at hm
  have hk : p ∣ q ^ Module.finrank F W - 1 := hmod2 _ hm
  have hkle : Module.finrank F W ≤ n := hn ▸ Submodule.finrank_le W
  rcases Nat.eq_zero_or_pos (Module.finrank F W) with h0 | hpos
  · left; exact Submodule.finrank_eq_zero.1 h0
  · rcases lt_or_eq_of_le hkle with hlt | heq
    · exact absurd hk (hnp _ hpos hlt)
    · right; exact Submodule.eq_top_of_finrank_eq (heq.trans hn.symm)


theorem isCyclic_of_isPGroup_ppd (hn : Module.finrank F V = n) (hn0 : 0 < n)
    (hpn : p ∣ Fintype.card F ^ n - 1)
    (hnp : ∀ k, 0 < k → k < n → ¬ p ∣ Fintype.card F ^ k - 1)
    (P : Subgroup (V ≃ₗ[F] V)) (hP : IsPGroup p P) : IsCyclic P := by
  classical
  have hfin : Finite (V ≃ₗ[F] V) :=
    Finite.of_injective (fun f : V ≃ₗ[F] V => (f : V → V))
      (fun f g h => LinearEquiv.ext (congrFun h))
  by_cases hbot : P = ⊥
  · subst hbot
    infer_instance
  have hnt : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hbot
  have hcn : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  have hpc : IsPGroup p (Subgroup.center P) :=
    hP.of_injective (Subgroup.center P).subtype Subtype.val_injective
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hpc
  have hpdvd : p ∣ Nat.card (Subgroup.center P) := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hm
      have := Nat.card_eq_one_iff_unique.1 hm
      obtain ⟨a, b, hab⟩ := exists_pair_ne (Subgroup.center P)
      exact hab (this.1.elim a b)
    · rw [hm]; exact dvd_pow_self p hpos.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) p hpdvd
  set y : V ≃ₗ[F] V := ((z : P) : V ≃ₗ[F] V) with hy
  have hyp : y ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    have := congrArg (fun w : Subgroup.center P => ((w : P) : V ≃ₗ[F] V)) this
    simpa using this
  have hy1 : y ≠ 1 := by
    intro h1
    have : z = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact h1
    rw [this, orderOf_one] at hz
    exact hp.out.one_lt.ne hz
  obtain ⟨-, hsimple⟩ := simple_of_ppd hn hpn hnp y hyp hy1
  let A : Subalgebra F (V →ₗ[F] V) := Subalgebra.centralizer F {(y : V →ₗ[F] V)}
  have hmemA : ∀ a : V →ₗ[F] V, a ∈ A ↔ (y : V →ₗ[F] V) * a = a * (y : V →ₗ[F] V) := by
    intro a
    rw [Subalgebra.mem_centralizer_iff]
    simp
  have hnzd : ∀ a b : A, a * b = 0 → a = 0 ∨ b = 0 := by
    intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    have ha' : (a : V →ₗ[F] V) ≠ 0 := fun h => ha (Subtype.ext h)
    have hya := (hmemA a).1 a.2
    have hker : LinearMap.ker (a : V →ₗ[F] V) = ⊥ := by
      rcases hsimple (LinearMap.ker (a : V →ₗ[F] V)) (fun v hv => by
        rw [LinearMap.mem_ker] at hv ⊢
        have h3 := congrArg (fun m : V →ₗ[F] V => m v) hya
        simp only [Module.End.mul_apply] at h3
        show (a : V →ₗ[F] V) (y v) = 0
        exact h3.symm.trans (by rw [hv, map_zero])) with h | h
      · exact h
      · exact absurd (LinearMap.ker_eq_top.1 h) ha'
    apply Subtype.ext
    ext v
    have h1 : ((a * b : A) : V →ₗ[F] V) v = 0 := by rw [hab]; rfl
    have h2 : (a : V →ₗ[F] V) ((b : V →ₗ[F] V) v) = 0 := h1
    have : (b : V →ₗ[F] V) v ∈ LinearMap.ker (a : V →ₗ[F] V) := h2
    rw [hker] at this
    simpa using this
  have : Nontrivial V := by
    have : 0 < Module.finrank F V := hn ▸ hn0
    exact Module.nontrivial_of_finrank_pos this
  have hnt' : Nontrivial A := ⟨⟨0, 1, fun h => by
    have := congrArg (fun a : A => (a : V →ₗ[F] V)) h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h2 := congrArg (fun m : V →ₗ[F] V => m v) this
    simp at h2
    exact hv h2.symm⟩⟩
  have hfinA : Finite A := by
    have : Finite (V →ₗ[F] V) :=
      Finite.of_injective (fun f : V →ₗ[F] V => (f : V → V))
        (fun f g h => LinearMap.ext (congrFun h))
    infer_instance
  have hdom : IsDomain A := by
    have : NoZeroDivisors A := ⟨fun {a b} h => hnzd a b h⟩
    exact NoZeroDivisors.to_isDomain A
  have hfield : IsField A := Finite.isDomain_to_isField A
  let _ : CommRing A := { (inferInstance : Ring A) with mul_comm := hfield.mul_comm }
  have : IsDomain A := hdom
  have hcomm : ∀ w : P, (y : V →ₗ[F] V) * ((w : V ≃ₗ[F] V) : V →ₗ[F] V) =
      ((w : V ≃ₗ[F] V) : V →ₗ[F] V) * (y : V →ₗ[F] V) := by
    intro w
    have h := Subgroup.mem_center_iff.1 z.2 w
    have h' : (w : V ≃ₗ[F] V) * y = y * (w : V ≃ₗ[F] V) := congrArg Subtype.val h
    ext v
    have := congrArg (fun m : V ≃ₗ[F] V => m v) h'
    simp at this ⊢
    exact this.symm
  let f : P →* A :=
    { toFun := fun w => ⟨((w : V ≃ₗ[F] V) : V →ₗ[F] V), (hmemA _).2 (hcomm w)⟩
      map_one' := by apply Subtype.ext; rfl
      map_mul' := fun a b => by apply Subtype.ext; rfl }
  refine isCyclic_of_injective_ringHom f (fun a b hab => ?_)
  have := congrArg (fun x : A => (x : V →ₗ[F] V)) hab
  apply Subtype.ext
  exact LinearEquiv.toLinearMap_injective this

end Ppd


theorem isCyclic_of_isPGroup_of_cyclic_hall {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (T : Subgroup X) [IsCyclic T] {M : ℕ} (hX : Nat.card X = Nat.card T * M)
    (hM : ¬ p ∣ M) (P : Subgroup X) (hP : IsPGroup p P) : IsCyclic P := by
  have hp := Fact.out (p := p.Prime)
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · exfalso; apply hM; rw [h0]; exact dvd_zero p
    · exact h0
  have hfac : (Nat.card X).factorization p = (Nat.card T).factorization p := by
    rw [hX, Nat.factorization_mul hTpos.ne' hMpos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hM, add_zero]
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := T) p
    (n := (Nat.card T).factorization p) (Nat.ordProj_dvd _ _)
  have hS : Nat.card (K.map T.subtype) = p ^ (Nat.card X).factorization p := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK, hfac]
  let S : Sylow p X := Sylow.ofCard (K.map T.subtype) hS
  obtain ⟨S', hPS'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S S'
  have hKcyc : IsCyclic K := inferInstance
  have hScyc : IsCyclic (K.map T.subtype) :=
    isCyclic_of_surjective _ (T.subtype.subgroupMap_surjective K)
  have hS'cyc : IsCyclic (S' : Subgroup X) := by
    have hScyc' : IsCyclic (S : Subgroup X) := hScyc
    rw [← hg]
    have : ((g • S : Sylow p X) : Subgroup X) =
        (S : Subgroup X).map (MulAut.conj g).toMonoidHom := rfl
    rw [this]
    exact isCyclic_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap (S : Subgroup X))
      (MonoidHom.subgroupMap_surjective _ _)
  exact isCyclic_of_injective (Subgroup.inclusion hPS') (Subgroup.inclusion_injective hPS')


section GLTransfer

variable {F : Type} [Field F] [Fintype F] {n p : ℕ} [hp : Fact p.Prime]

noncomputable def glToLinEquiv (n : ℕ) (F : Type) [Field F] :
    GL (Fin n) F →* ((Fin n → F) ≃ₗ[F] (Fin n → F)) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin n → F)).toMonoidHom).comp
    (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := F)).toMonoidHom

omit [Fintype F] in
theorem glToLinEquiv_injective : Function.Injective (glToLinEquiv n F) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin n → F)).injective.comp
    (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := F)).injective

theorem isCyclic_of_isPGroup_of_embed {G : Type*} [Group G] (ι : G →* GL (Fin n) F)
    (hι : Function.Injective ι) (hn0 : 0 < n) (hpn : p ∣ Fintype.card F ^ n - 1)
    (hnp : ∀ k, 0 < k → k < n → ¬ p ∣ Fintype.card F ^ k - 1) (P : Subgroup G)
    (hP : IsPGroup p P) : IsCyclic P := by
  let φ : G →* ((Fin n → F) ≃ₗ[F] (Fin n → F)) := (glToLinEquiv n F).comp ι
  have hφ : Function.Injective φ := glToLinEquiv_injective.comp hι
  have hPm : IsPGroup p (P.map φ) := hP.map φ
  have hc : IsCyclic (P.map φ) :=
    isCyclic_of_isPGroup_ppd (F := F) (V := Fin n → F) (Module.finrank_fin_fun F) hn0 hpn hnp
      (P.map φ) hPm
  exact isCyclic_of_injective (Subgroup.equivMapOfInjective P φ hφ).toMonoidHom
    (Subgroup.equivMapOfInjective P φ hφ).injective

end GLTransfer

end CFSG.CGT.T75N
