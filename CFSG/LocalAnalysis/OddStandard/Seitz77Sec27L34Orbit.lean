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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.OddStandard.Seitz77

open Matrix

abbrev V8 : Type := Fin 8 → ZMod 2

theorem card_V8 : Nat.card V8 = 256 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

@[expose] def glPerm (g : GL (Fin 8) (ZMod 2)) : Equiv.Perm V8 where
  toFun v := (g : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v
  invFun v := ((g⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v
  left_inv v := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  right_inv v := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]

theorem glPerm_apply (g : GL (Fin 8) (ZMod 2)) (v : V8) :
    glPerm g v = (g : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v := rfl

@[expose] def glPermHom : GL (Fin 8) (ZMod 2) →* Equiv.Perm V8 where
  toFun := glPerm
  map_one' := by
    ext v
    simp [glPerm_apply]
  map_mul' g h := by
    ext v
    simp [glPerm_apply, Matrix.mulVec_mulVec]

theorem glPermHom_apply (g : GL (Fin 8) (ZMod 2)) (v : V8) :
    glPermHom g v = (g : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v := rfl

theorem glPermHom_zero (g : GL (Fin 8) (ZMod 2)) : glPermHom g 0 = 0 := by
  simp [glPermHom_apply]

theorem glPermHom_add (g : GL (Fin 8) (ZMod 2)) (v w : V8) :
    glPermHom g (v + w) = glPermHom g v + glPermHom g w := by
  simp [glPermHom_apply, Matrix.mulVec_add]

theorem eq_one_of_forall_glPerm_eq {g : GL (Fin 8) (ZMod 2)} (h : ∀ v, glPermHom g v = v) :
    g = 1 := by
  apply Units.ext
  ext i j
  have := h (Pi.single j 1)
  have h2 := congrFun this i
  simpa [glPermHom_apply, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.one_apply,
    Pi.single_apply] using h2

theorem exists_orbit_card_le_three {T X : Type*} [Group T] [Finite T] [MulAction T X] [Finite X]
    (hT : IsPGroup 3 T) (hX : ¬ 9 ∣ Nat.card X) :
    ∃ x : X, Nat.card (MulAction.orbit T x) ≤ 3 := by
  classical
  by_contra h
  push Not at h
  apply hX
  have key : ∀ x : X, 9 ∣ Nat.card (MulAction.orbit T x) := by
    intro x
    have hidx : Nat.card (MulAction.orbit T x) = (MulAction.stabilizer T x).index := by
      rw [Nat.card_coe_set_eq, MulAction.index_stabilizer]
    have hdvd : Nat.card (MulAction.orbit T x) ∣ Nat.card T := by
      rw [hidx]
      exact Subgroup.index_dvd_card _
    obtain ⟨n, hn⟩ := hT.exists_card_dvd_pow
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (hdvd.trans hn)
    have h4 : 3 < 3 ^ j := hj' ▸ h x
    have hj2 : 2 ≤ j := by
      by_contra hlt
      have hlt' : j < 2 := not_le.mp hlt
      interval_cases j <;> simp at h4
    rw [hj']
    calc 9 = 3 ^ 2 := by norm_num
      _ ∣ 3 ^ j := pow_dvd_pow 3 hj2
  have : Fintype (Quotient (MulAction.orbitRel T X)) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits T X), Nat.card_sigma]
  exact Finset.dvd_sum fun ω _ => key _

theorem exists_nonzero_orbit_le_three {G : Type*} [Group G] [Finite G]
    (φ : G →* Equiv.Perm V8) (h0 : ∀ g, φ g 0 = 0) (T : Subgroup G) (hT : IsPGroup 3 T) :
    ∃ v : V8, v ≠ 0 ∧ Nat.card {w : V8 // ∃ t ∈ T, w = φ t v} ≤ 3 := by
  have hinv : ∀ (g : G) (v : V8), v ≠ 0 ↔ φ g v ≠ 0 := by
    intro g v
    constructor
    · intro hv h
      exact hv ((φ g).injective (h.trans (h0 g).symm))
    · intro hv h
      exact hv (by rw [h, h0])
  let ψ : T →* Equiv.Perm {v : V8 // v ≠ 0} :=
    { toFun := fun t => (φ t).subtypePerm fun v => (hinv t v).symm
      map_one' := Equiv.ext fun x => Subtype.ext (by simp)
      map_mul' := fun a b => Equiv.ext fun x => Subtype.ext (by
        simp only [Subgroup.coe_mul, map_mul]; rfl) }
  let _ : MulAction T {v : V8 // v ≠ 0} := MulAction.compHom _ ψ
  have hX : ¬ 9 ∣ Nat.card {v : V8 // v ≠ 0} := by
    have h1 : Nat.card {v : V8 // v ≠ 0} = 255 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
        ← Nat.card_eq_fintype_card, card_V8]
    rw [h1]
    norm_num
  obtain ⟨x, hx⟩ := exists_orbit_card_le_three hT hX
  refine ⟨x.1, x.2, le_trans ?_ hx⟩
  have hsmul : ∀ (t : T) (y : {v : V8 // v ≠ 0}), (t • y).1 = φ t y.1 := fun t y => rfl
  refine Nat.card_le_card_of_injective
    (fun w => (⟨⟨w.1, ?_⟩, ?_⟩ : MulAction.orbit T x)) ?_
  · obtain ⟨w, t, ht, rfl⟩ := w
    exact (hinv t x.1).1 x.2
  · obtain ⟨w, t, ht, rfl⟩ := w
    exact ⟨⟨t, ht⟩, Subtype.ext (hsmul _ _)⟩
  · intro a b hab
    exact Subtype.ext (congrArg (fun y => y.1.1) hab)

@[expose] def glAddHom (g : GL (Fin 8) (ZMod 2)) : V8 →+ V8 :=
  (Matrix.mulVecLin (g : Matrix (Fin 8) (Fin 8) (ZMod 2))).toAddMonoidHom

@[expose] def fixAddSubgroup (g : GL (Fin 8) (ZMod 2)) : AddSubgroup V8 :=
  AddMonoidHom.eqLocus (glAddHom g) (AddMonoidHom.id V8)

theorem card_fix_eq (g : GL (Fin 8) (ZMod 2)) :
    Nat.card {v : V8 // glPermHom g v = v} = Nat.card (fixAddSubgroup g) :=
  Nat.card_congr (Equiv.refl _)

theorem card_fixAddSubgroup_dvd (g : GL (Fin 8) (ZMod 2)) :
    Nat.card (fixAddSubgroup g) ∣ 256 := by
  rw [← card_V8]
  exact AddSubgroup.card_addSubgroup_dvd_card _

theorem card_modEq_card_fixed {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α)
    {p : ℕ} [Fact p.Prime] (hσ : σ ^ p = 1) :
    Fintype.card α ≡ Fintype.card {a : α // σ a = a} [MOD p] := by
  have h := Equiv.Perm.card_compl_support_modEq (n := 1) (p := p) (σ := σ) (by simpa using hσ)
  have e : Fintype.card {a : α // σ a = a} = (σ.supportᶜ).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext a
    simp
  rw [e]
  exact h.symm

theorem card_V8_modEq_card_fix (g : GL (Fin 8) (ZMod 2)) {p : ℕ} [Fact p.Prime]
    (hg : g ^ p = 1) : 256 ≡ Nat.card (fixAddSubgroup g) [MOD p] := by
  have hσ : (glPermHom g) ^ p = 1 := by rw [← map_pow, hg, map_one]
  have h := card_modEq_card_fixed (glPermHom g) hσ
  rw [← Nat.card_eq_fintype_card, card_V8] at h
  rw [← Nat.card_eq_fintype_card, card_fix_eq] at h
  exact h

theorem card_orbit_mul_card_stab {G : Type*} [Group G] [Finite G] (φ : G →* Equiv.Perm V8)
    (T : Subgroup G) (v : V8) :
    Nat.card {w : V8 // ∃ t ∈ T, w = φ t v} * Nat.card {t : T // φ t v = v} =
      Nat.card T := by
  let _ : MulAction T V8 := MulAction.compHom V8 (φ.comp T.subtype)
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer T v)
  rw [MulAction.index_stabilizer] at h1
  have e1 : (MulAction.orbit T v).ncard = Nat.card {w : V8 // ∃ t ∈ T, w = φ t v} := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  have e2 : Nat.card (MulAction.stabilizer T v) = Nat.card {t : T // φ t v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun t => MulAction.mem_stabilizer_iff)
  rw [e1, e2] at h1
  rw [mul_comm]
  exact h1

theorem card_V8_modEq_one_of_pgroup {G : Type*} [Group G] (ρ : G →* GL (Fin 8) (ZMod 2))
    (Q : Subgroup G) {p : ℕ} [Fact p.Prime] (hQ : IsPGroup p Q)
    (h : ∀ v : V8, (∀ q ∈ Q, glPermHom (ρ q) v = v) → v = 0) : 256 ≡ 1 [MOD p] := by
  let _ : MulAction Q V8 := MulAction.compHom V8 ((glPermHom.comp ρ).comp Q.subtype)
  have h1 := hQ.card_modEq_card_fixedPoints V8
  have h2 : Nat.card (MulAction.fixedPoints Q V8) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨0, fun q => glPermHom_zero (ρ q)⟩, fun a => Subtype.ext ?_⟩
    exact h a.1 fun q hq => a.2 ⟨q, hq⟩
  rw [h2, card_V8] at h1
  exact h1

theorem card_fix_modEq_one {g h : GL (Fin 8) (ZMod 2)} (hcomm : g * h = h * g) {p : ℕ}
    [Fact p.Prime] (hg : g ^ p = 1) (hfpf : ∀ v, glPermHom g v = v → v = 0) :
    Nat.card (fixAddSubgroup h) ≡ 1 [MOD p] := by
  have hF : ∀ v : V8, glPermHom h (glPermHom g v) = glPermHom g v ↔ glPermHom h v = v := by
    intro v
    have hc : glPermHom h (glPermHom g v) = glPermHom g (glPermHom h v) := by
      rw [← Equiv.Perm.mul_apply, ← map_mul, ← hcomm, map_mul, Equiv.Perm.mul_apply]
    rw [hc]
    exact (glPermHom g).injective.eq_iff
  let σ : Equiv.Perm {v : V8 // glPermHom h v = v} := (glPermHom g).subtypePerm hF
  have hσ : σ ^ p = 1 := by
    have h1 : (glPermHom g) ^ p = 1 := by rw [← map_pow, hg, map_one]
    ext x
    simp [σ, h1]
  have hmod := card_modEq_card_fixed σ hσ
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_fix_eq h] at hmod
  have hone : Nat.card {a : {v : V8 // glPermHom h v = v} // σ a = a} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨⟨0, glPermHom_zero h⟩, ?_⟩, fun a => ?_⟩
    · exact Subtype.ext (glPermHom_zero g)
    · refine Subtype.ext (Subtype.ext ?_)
      exact hfpf a.1.1 (congrArg Subtype.val a.2)
  rw [hone] at hmod
  exact hmod

theorem eq_one_of_fix_conditions {h : GL (Fin 8) (ZMod 2)} {p : ℕ} (hp : p = 5 ∨ p = 17)
    (h7 : 256 ≡ Nat.card (fixAddSubgroup h) [MOD 7])
    (hmod : Nat.card (fixAddSubgroup h) ≡ 1 [MOD p]) : h = 1 := by
  have hdvd := card_fixAddSubgroup_dvd h
  have hmem : Nat.card (fixAddSubgroup h) ∈ Nat.divisors 256 :=
    Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
  have h256 : Nat.card (fixAddSubgroup h) = 256 := by
    have hdiv : Nat.divisors 256 = {1, 2, 4, 8, 16, 32, 64, 128, 256} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hp with rfl | rfl <;>
    rcases hmem with h | h | h | h | h | h | h | h | h <;>
    simp [h, Nat.ModEq] at h7 hmod ⊢
  have htop : fixAddSubgroup h = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [h256]
    exact card_V8.symm
  apply eq_one_of_forall_glPerm_eq
  intro v
  have : v ∈ fixAddSubgroup h := htop ▸ AddSubgroup.mem_top v
  exact this

theorem zmod_three_pow_fixes_aux {G X : Type*} [Group G] (φ : G →* Equiv.Perm X) (z : G)
    (hz3 : z ^ 3 = 1) (x : X) (hfpf : φ z x ≠ x) (k : ℕ)
    (hk : φ (z ^ k) x = x) : k % 3 = 0 := by
  have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h3 with h | h | h
  · exact h
  · exfalso
    rw [pow_eq_pow_mod k hz3, h, pow_one] at hk
    exact hfpf hk
  · exfalso
    rw [pow_eq_pow_mod k hz3, h] at hk
    apply hfpf
    calc φ z x = φ z (φ (z ^ 2) x) := by rw [hk]
      _ = φ (z ^ 3) x := by rw [← Equiv.Perm.mul_apply, ← map_mul, ← pow_succ']
      _ = x := by rw [hz3, map_one, Equiv.Perm.one_apply]

theorem zmod_three_orbit_injective_aux {G X : Type*} [Group G] (φ : G →* Equiv.Perm X)
    (z : G) (hz3 : z ^ 3 = 1) (v : X) (hfpf : φ z v ≠ v)
    (i j : ZMod 3) (h : φ (z ^ i.val) v = φ (z ^ j.val) v) : i = j := by
  have h1 : φ (z ^ (j.val + (3 - i.val))) v = v := by
    calc φ (z ^ (j.val + (3 - i.val))) v
        = φ (z ^ (3 - i.val)) (φ (z ^ j.val) v) := by
          rw [add_comm, pow_add, map_mul, Equiv.Perm.mul_apply]
      _ = φ (z ^ (3 - i.val)) (φ (z ^ i.val) v) := by rw [h]
      _ = φ (z ^ (3 - i.val + i.val)) v := by
          rw [pow_add, map_mul, Equiv.Perm.mul_apply]
      _ = v := by
          rw [Nat.sub_add_cancel (ZMod.val_lt i).le, hz3, map_one, Equiv.Perm.one_apply]
  have h2 := zmod_three_pow_fixes_aux φ z hz3 v hfpf _ h1
  have hi := ZMod.val_lt i
  have hj := ZMod.val_lt j
  exact ZMod.val_injective 3 (by omega)

theorem exists_hom_zmod_three_of_small_orbit {G X : Type*} [Group G] (φ : G →* Equiv.Perm X)
    (T : Subgroup G) (z : G) (hzT : z ∈ T) (hz3 : z ^ 3 = 1)
    (hzc : ∀ t ∈ T, t * z = z * t) (v : X) (hfpf : φ z v ≠ v)
    (horb : ∀ t ∈ T, ∃ i : ZMod 3, φ t v = φ (z ^ i.val) v) :
    ∃ c : T →* Multiplicative (ZMod 3), c ⟨z, hzT⟩ = Multiplicative.ofAdd 1 := by
  have hinj : ∀ i j : ZMod 3, φ (z ^ i.val) v = φ (z ^ j.val) v → i = j :=
    fun i j h => zmod_three_orbit_injective_aux φ z hz3 v hfpf i j h
  choose! e he using horb
  have hcomm : ∀ t ∈ T, ∀ k : ℕ, t * z ^ k = z ^ k * t := fun t ht k =>
    (Commute.pow_right (hzc t ht : Commute t z) k).eq
  have hmul : ∀ a ∈ T, ∀ b ∈ T, e (a * b) = e a + e b := by
    intro a ha b hb
    apply hinj
    rw [← he _ (T.mul_mem ha hb)]
    calc φ (a * b) v = φ a (φ b v) := by rw [map_mul, Equiv.Perm.mul_apply]
      _ = φ a (φ (z ^ (e b).val) v) := by rw [he b hb]
      _ = φ (a * z ^ (e b).val) v := by rw [map_mul, Equiv.Perm.mul_apply]
      _ = φ (z ^ (e b).val * a) v := by rw [hcomm a ha]
      _ = φ (z ^ (e b).val) (φ a v) := by rw [map_mul, Equiv.Perm.mul_apply]
      _ = φ (z ^ (e b).val) (φ (z ^ (e a).val) v) := by rw [he a ha]
      _ = φ (z ^ (e b).val * z ^ (e a).val) v := by rw [map_mul, Equiv.Perm.mul_apply]
      _ = φ (z ^ ((e a).val + (e b).val)) v := by rw [← pow_add, add_comm]
      _ = φ (z ^ (e a + e b).val) v := by rw [ZMod.val_add, ← pow_eq_pow_mod _ hz3]
  refine ⟨MonoidHom.mk' (fun t : T => Multiplicative.ofAdd (e t.1)) ?_, ?_⟩
  · intro a b
    exact congrArg Multiplicative.ofAdd (hmul a.1 a.2 b.1 b.2)
  · show Multiplicative.ofAdd (e z) = Multiplicative.ofAdd 1
    refine congrArg Multiplicative.ofAdd (hinj _ _ ?_)
    rw [← he z hzT, ZMod.val_one, pow_one]

end CFSG.OddStandard.Seitz77
