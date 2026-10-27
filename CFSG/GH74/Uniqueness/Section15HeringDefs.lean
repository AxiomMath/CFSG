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
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
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

namespace CFSG.GH74.Uniqueness.Hering

open Subgroup MulAction
open scoped commutatorElement

@[expose] def HasRegularNormal (G Ω : Type*) [Group G] [MulAction G Ω] : Prop :=
  ∃ N : Subgroup G, N.Normal ∧ ∀ x y : Ω, ∃! n : N, (n : G) • x = y

section Abstract

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem isPretransitive_of_normal [FaithfulSMul G Ω] (h2 : IsMultiplyPretransitive G Ω 2)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : IsPretransitive N Ω := by
  have : IsPreprimitive G Ω := isPreprimitive_of_is_two_pretransitive h2
  apply IsQuasiPreprimitive.isPretransitive_of_normal
  intro hfix
  apply hN
  rw [eq_bot_iff]
  intro n hn
  rw [mem_bot]
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Ω)
  intro x
  have hx : x ∈ fixedPoints N Ω := hfix ▸ Set.mem_univ x
  rw [one_smul]
  exact hx ⟨n, hn⟩

theorem hasRegularNormal_of_abelian [FaithfulSMul G Ω] (N : Subgroup G) [hN : N.Normal]
    (htr : IsPretransitive N Ω) (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) :
    HasRegularNormal G Ω := by
  refine ⟨N, hN, fun x y => ?_⟩
  obtain ⟨n, hn⟩ := htr.exists_smul_eq x y
  refine ⟨n, hn, fun n' hn' => ?_⟩
  have hfix : ∀ z : Ω, ((n⁻¹ * n' : N) : G) • z = z := by
    intro z
    obtain ⟨c, rfl⟩ := htr.exists_smul_eq x z
    have hc : ((n⁻¹ * n' : N) : G) * (c : G) = (c : G) * ((n⁻¹ * n' : N) : G) :=
      hab _ (n⁻¹ * n').2 _ c.2
    change ((n⁻¹ * n' : N) : G) • ((c : G) • x) = (c : G) • x
    rw [smul_smul, hc, mul_smul]
    congr 1
    rw [Subgroup.coe_mul, mul_smul, hn', ← hn, Subgroup.coe_inv]
    change (n : G)⁻¹ • ((n : G) • x) = x
    exact inv_smul_smul _ _
  have h1 : ((n⁻¹ * n' : N) : G) = 1 :=
    FaithfulSMul.eq_of_smul_eq_smul (α := Ω) (fun z => by rw [hfix, one_smul])
  have : n⁻¹ * n' = 1 := Subtype.ext h1
  rw [inv_mul_eq_one] at this
  exact this.symm

structure EndHyp (G Ω : Type*) [Group G] [MulAction G Ω] (p : ℕ) (ω : Ω) (K P : Subgroup G) :
    Prop where
  prime : p.Prime
  three_le : 3 ≤ p
  faithful : FaithfulSMul G Ω
  twoTrans : IsMultiplyPretransitive G Ω 2
  card : Nat.card Ω = 2 ^ p
  K_le : K ≤ stabilizer G ω
  K_normal : ∀ h ∈ stabilizer G ω, ∀ k ∈ K, h * k * h⁻¹ ∈ K
  card_K : Nat.card K = 2 ^ p - 1
  K_fix : ∀ k ∈ K, k ≠ 1 → ∀ x : Ω, k • x = x → x = ω
  card_stab : Nat.card (stabilizer G ω) = (2 ^ p - 1) * p
  P_le : P ≤ stabilizer G ω
  card_P : Nat.card P = p
  card_normalizer : Nat.card (normalizer (P : Set G)) = 2 * p
  centralizer_le : centralizer (P : Set G) ≤ P
  solvable : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥
  closure : normalClosure (K : Set G) = ⊤

end Abstract

section RingAut

variable {F : Type*} [Field F] [Finite F]

instance finite_ringAut : Finite (F ≃+* F) :=
  Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective

theorem charP_two_of_card {m : ℕ} (hm : m ≠ 0) (hF : Nat.card F = 2 ^ m) : CharP F 2 := by
  have : Fintype F := Fintype.ofFinite F
  have h : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, hF, Nat.cast_pow, Nat.cast_ofNat] at h
  exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (pow_eq_zero_iff hm |>.mp h)

noncomputable def ringAutEquivGal [CharP F 2] :
    letI := ZMod.algebra F 2
    (F ≃+* F) ≃* (F ≃ₐ[ZMod 2] F) :=
  letI := ZMod.algebra F 2
  { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) (fun x => by
      have := RingHom.ext_zmod ((σ : F →+* F).comp (algebraMap (ZMod 2) F))
        (algebraMap (ZMod 2) F)
      exact RingHom.congr_fun this x)
    invFun := fun τ => τ.toRingEquiv
    left_inv := fun σ => by ext x; rfl
    right_inv := fun τ => by ext x; rfl
    map_mul' := fun σ τ => by ext x; rfl }

theorem isCyclic_ringAut {m : ℕ} (hm : m ≠ 0) (hF : Nat.card F = 2 ^ m) :
    IsCyclic (F ≃+* F) := by
  have := charP_two_of_card hm hF
  let := ZMod.algebra F 2
  exact isCyclic_of_surjective (ringAutEquivGal (F := F)).symm.toMonoidHom
    (ringAutEquivGal (F := F)).symm.surjective

theorem card_ringAut {m : ℕ} (hm : m ≠ 0) (hF : Nat.card F = 2 ^ m) :
    Nat.card (F ≃+* F) = m := by
  have := charP_two_of_card hm hF
  let := ZMod.algebra F 2
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_congr (ringAutEquivGal (F := F)).toEquiv, IsGalois.card_aut_eq_finrank]
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
  rw [ZMod.card, ← Nat.card_eq_fintype_card, hF] at h
  exact (Nat.pow_right_injective le_rfl h).symm

theorem ringAut_mul_comm {m : ℕ} (hm : m ≠ 0) (hF : Nat.card F = 2 ^ m) (σ τ : F ≃+* F) :
    σ * τ = τ * σ := by
  have := isCyclic_ringAut hm hF
  exact IsCyclic.commGroup.mul_comm σ τ

theorem card_fixed_pow (A : Subgroup (F ≃+* F)) :
    Nat.card {x : F // ∀ σ ∈ A, σ x = x} ^ Nat.card A = Nat.card F := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Fintype A := Fintype.ofFinite A
  have h1 := FixedPoints.finrank_eq_card A F
  have h2 := Module.card_eq_pow_finrank (K := FixedPoints.subfield A F) (V := F)
  rw [h1] at h2
  have h3 : Nat.card {x : F // ∀ σ ∈ A, σ x = x} = Nat.card (FixedPoints.subfield A F) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun x => ?_)
    change (∀ σ ∈ A, σ x = x) ↔ ∀ g : A, g • x = x
    exact ⟨fun h g => h g g.2, fun h σ hσ => h ⟨σ, hσ⟩⟩
  rw [h3, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h2]

end RingAut

section Setting

variable {F : Type*} [Field F]

@[expose] def mulSubgroup (G F : Type*) [Group G] [Field F] [MulAction G F] : Subgroup G where
  carrier := {g | ∃ a : Fˣ, ∀ x : F, g • x = a * x}
  mul_mem' := by
    rintro g h ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, fun x => by rw [mul_smul, hb, ha, Units.val_mul, mul_assoc]⟩
  one_mem' := ⟨1, fun x => by simp⟩
  inv_mem' := by
    rintro g ⟨a, ha⟩
    refine ⟨a⁻¹, fun x => ?_⟩
    rw [inv_smul_eq_iff, ha, ← mul_assoc, Units.mul_inv, one_mul]

@[expose] def stab01 (G F : Type*) [Group G] [Field F] [MulAction G F] : Subgroup G :=
  stabilizer G (0 : F) ⊓ stabilizer G (1 : F)

open Classical in
@[expose] noncomputable def semilinPart (F : Type*) [Field F] {G : Type*} [Group G]
    [MulAction G F] (g : G) : F ≃+* F :=
  if h : ∃ σ : F ≃+* F, ∀ x : F, g • x = (g • (1 : F)) * σ x then h.choose else RingEquiv.refl F

structure Hyp (G F : Type*) [Group G] [Field F] [MulAction G F] (m : ℕ) : Prop where
  two_le : 2 ≤ m
  card : Nat.card F = 2 ^ m
  faithful : FaithfulSMul G F
  twoTrans : IsMultiplyPretransitive G F 2
  stab : ∀ g : G, g • (0 : F) = 0 → ∃ (a : Fˣ) (σ : F ≃+* F), ∀ x : F, g • x = a * σ x
  mul : ∀ a : Fˣ, ∃ g : G, ∀ x : F, g • x = a * x

variable {G : Type*} [Group G] [MulAction G F] {m : ℕ}

theorem mem_mulSubgroup {g : G} : g ∈ mulSubgroup G F ↔ ∃ a : Fˣ, ∀ x : F, g • x = a * x :=
  Iff.rfl

theorem mem_stab01 {g : G} : g ∈ stab01 G F ↔ g • (0 : F) = 0 ∧ g • (1 : F) = 1 :=
  Iff.rfl

theorem stab01_le_stabilizer : stab01 G F ≤ stabilizer G (0 : F) := inf_le_left

theorem smul_eq_of_mem_mulSubgroup {g : G} (hg : g ∈ mulSubgroup G F) (x : F) :
    g • x = (g • (1 : F)) * x := by
  obtain ⟨a, ha⟩ := hg
  rw [ha, ha 1, mul_one]

theorem mulSubgroup_le_stabilizer : mulSubgroup G F ≤ stabilizer G (0 : F) := by
  intro g hg
  rw [mem_stabilizer_iff, smul_eq_of_mem_mulSubgroup hg, mul_zero]

theorem smul_one_ne_zero {g : G} (hg : g • (0 : F) = 0) : g • (1 : F) ≠ 0 := by
  intro h
  rw [← hg] at h
  exact one_ne_zero (smul_left_cancel g h)

theorem smul_eq_semilinPart (hG : Hyp G F m) {g : G} (hg : g • (0 : F) = 0) (x : F) :
    g • x = (g • (1 : F)) * semilinPart F g x := by
  have hex : ∃ σ : F ≃+* F, ∀ x : F, g • x = (g • (1 : F)) * σ x := by
    obtain ⟨a, σ, h⟩ := hG.stab g hg
    refine ⟨σ, fun x => ?_⟩
    rw [h 1, map_one, mul_one, h x]
  unfold semilinPart
  split
  · next h => exact h.choose_spec x
  · next h => exact absurd hex h

theorem semilinPart_eq (hG : Hyp G F m) {g : G} (hg : g • (0 : F) = 0) {a : F}
    {σ : F ≃+* F} (h : ∀ x : F, g • x = a * σ x) : semilinPart F g = σ := by
  have ha : g • (1 : F) = a := by rw [h 1, map_one, mul_one]
  ext x
  have h1 := smul_eq_semilinPart hG hg x
  rw [h x, ha] at h1
  have ha0 : a ≠ 0 := ha ▸ smul_one_ne_zero hg
  exact (mul_left_cancel₀ ha0 h1).symm

theorem semilinPart_mul (hG : Hyp G F m) {g h : G} (hg : g • (0 : F) = 0)
    (hh : h • (0 : F) = 0) : semilinPart F (g * h) = semilinPart F g * semilinPart F h := by
  apply semilinPart_eq hG (by rw [mul_smul, hh, hg])
    (a := (g • (1 : F)) * semilinPart F g (h • (1 : F)))
  intro x
  rw [mul_smul, smul_eq_semilinPart hG hh x, smul_eq_semilinPart hG hg, map_mul, ← mul_assoc]
  rfl

theorem semilinPart_one (hG : Hyp G F m) : semilinPart F (1 : G) = (1 : F ≃+* F) :=
  semilinPart_eq hG (one_smul G 0) (a := 1) (fun x => by simp)

@[expose] noncomputable def rho (hG : Hyp G F m) : stabilizer G (0 : F) →* (F ≃+* F) where
  toFun g := semilinPart F (g : G)
  map_one' := semilinPart_one hG
  map_mul' g h := semilinPart_mul hG g.2 h.2

theorem rho_apply (hG : Hyp G F m) (g : stabilizer G (0 : F)) :
    rho hG g = semilinPart F (g : G) := rfl

theorem semilinPart_eq_one_iff (hG : Hyp G F m) {g : G} (hg : g • (0 : F) = 0) :
    semilinPart F g = 1 ↔ g ∈ mulSubgroup G F := by
  constructor
  · intro h
    have h0 : g • (1 : F) ≠ 0 := smul_one_ne_zero hg
    refine ⟨Units.mk0 _ h0, fun x => ?_⟩
    rw [smul_eq_semilinPart hG hg x, h]
    rfl
  · rintro ⟨a, ha⟩
    exact semilinPart_eq hG hg (a := a) (fun x => by rw [ha]; rfl)

theorem smul_eq_of_mem_stab01 (hG : Hyp G F m) {g : G} (hg : g ∈ stab01 G F) (x : F) :
    g • x = semilinPart F g x := by
  rw [smul_eq_semilinPart hG hg.1 x, show g • (1 : F) = 1 from hg.2, one_mul]

theorem conj_mem_mulSubgroup (hG : Hyp G F m) {h k : G} (hh : h ∈ stabilizer G (0 : F))
    (hk : k ∈ mulSubgroup G F) : h * k * h⁻¹ ∈ mulSubgroup G F := by
  obtain ⟨a, ha⟩ := hk
  refine ⟨Units.map (semilinPart F h).toMonoidHom a, fun x => ?_⟩
  have hh0 : h • (0 : F) = 0 := hh
  set y := h⁻¹ • x with hy
  have hx : x = h • y := by rw [hy, smul_inv_smul]
  rw [mul_smul, mul_smul, ← hy, ha, hx, smul_eq_semilinPart hG hh0 (a * y),
    smul_eq_semilinPart hG hh0 y, map_mul, Units.coe_map]
  change _ = semilinPart F h (a : F) * _
  ring

theorem mulSubgroup_comm (hG : Hyp G F m) {a b : G} (ha : a ∈ mulSubgroup G F)
    (hb : b ∈ mulSubgroup G F) : a * b = b * a := by
  have := hG.faithful
  obtain ⟨c₁, h₁⟩ := ha
  obtain ⟨c₂, h₂⟩ := hb
  apply FaithfulSMul.eq_of_smul_eq_smul (α := F)
  intro x
  simp only [mul_smul, h₁, h₂]
  ring

theorem eq_zero_of_mem_mulSubgroup (hG : Hyp G F m) {k : G} (hk : k ∈ mulSubgroup G F)
    (hk1 : k ≠ 1) {x : F} (hx : k • x = x) : x = 0 := by
  have := hG.faithful
  by_contra hx0
  apply hk1
  apply FaithfulSMul.eq_of_smul_eq_smul (α := F)
  intro y
  have h1 : k • (1 : F) = 1 := by
    rw [smul_eq_of_mem_mulSubgroup hk x] at hx
    exact mul_right_cancel₀ hx0 (hx.trans (one_mul x).symm)
  rw [smul_eq_of_mem_mulSubgroup hk y, h1, one_mul, one_smul]

theorem stab01_inf_mulSubgroup (hG : Hyp G F m) : stab01 G F ⊓ mulSubgroup G F = ⊥ := by
  have := hG.faithful
  rw [eq_bot_iff]
  rintro g ⟨hg, hk⟩
  rw [mem_bot]
  apply FaithfulSMul.eq_of_smul_eq_smul (α := F)
  intro x
  rw [smul_eq_of_mem_mulSubgroup hk x, show g • (1 : F) = 1 from hg.2, one_mul, one_smul]

theorem exists_mulSubgroup (hG : Hyp G F m) (a : Fˣ) :
    ∃ k ∈ mulSubgroup G F, ∀ x : F, k • x = a * x := by
  obtain ⟨k, hk⟩ := hG.mul a
  exact ⟨k, ⟨a, hk⟩, hk⟩

theorem exists_mul_stab01 (hG : Hyp G F m) {h : G} (hh : h ∈ stabilizer G (0 : F)) :
    ∃ k ∈ mulSubgroup G F, ∃ γ ∈ stab01 G F, h = k * γ := by
  have hh0 : h • (0 : F) = 0 := hh
  obtain ⟨k, hk, hkx⟩ := exists_mulSubgroup hG (Units.mk0 _ (smul_one_ne_zero hh0))
  refine ⟨k, hk, k⁻¹ * h, ⟨?_, ?_⟩, by group⟩
  · change (k⁻¹ * h) • (0 : F) = 0
    rw [mul_smul, hh0]
    exact mulSubgroup_le_stabilizer ((mulSubgroup G F).inv_mem hk)
  · change (k⁻¹ * h) • (1 : F) = 1
    rw [mul_smul, inv_smul_eq_iff, hkx]
    simp

@[expose] noncomputable def mulSubgroupHom : mulSubgroup G F →* Fˣ where
  toFun k := Units.mk0 ((k : G) • (1 : F))
    (smul_one_ne_zero (mulSubgroup_le_stabilizer k.2 : (k : G) • (0 : F) = 0))
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp only [Subgroup.coe_mul, mul_smul, Units.val_mk0, Units.val_mul]
    rw [smul_eq_of_mem_mulSubgroup a.2 ((b : G) • (1 : F))]

theorem mulSubgroupHom_bijective (hG : Hyp G F m) : Function.Bijective (mulSubgroupHom (G := G) (F := F)) := by
  have := hG.faithful
  constructor
  · intro a b hab
    have h1 : (a : G) • (1 : F) = (b : G) • (1 : F) := congrArg Units.val hab
    apply Subtype.ext
    apply FaithfulSMul.eq_of_smul_eq_smul (α := F)
    intro x
    rw [smul_eq_of_mem_mulSubgroup a.2, smul_eq_of_mem_mulSubgroup b.2, h1]
  · intro a
    obtain ⟨k, hk, hkx⟩ := exists_mulSubgroup hG a
    refine ⟨⟨k, hk⟩, ?_⟩
    ext
    change k • (1 : F) = a
    rw [hkx, mul_one]

theorem card_mulSubgroup [Finite F] (hG : Hyp G F m) : Nat.card (mulSubgroup G F) = 2 ^ m - 1 := by
  rw [Nat.card_congr (MulEquiv.ofBijective _ (mulSubgroupHom_bijective hG)).toEquiv,
    Nat.card_units, hG.card]

theorem isCyclic_mulSubgroup [Finite F] (hG : Hyp G F m) : IsCyclic (mulSubgroup G F) :=
  isCyclic_of_injective mulSubgroupHom (mulSubgroupHom_bijective hG).1

theorem semilinPart_injOn_stab01 (hG : Hyp G F m) {g h : G} (hg : g ∈ stab01 G F)
    (hh : h ∈ stab01 G F) (he : semilinPart F g = semilinPart F h) : g = h := by
  have := hG.faithful
  apply FaithfulSMul.eq_of_smul_eq_smul (α := F)
  intro x
  rw [smul_eq_of_mem_stab01 hG hg, smul_eq_of_mem_stab01 hG hh, he]

@[expose] noncomputable def rhoStab01 (hG : Hyp G F m) : stab01 G F →* (F ≃+* F) :=
  (rho hG).comp (Subgroup.inclusion stab01_le_stabilizer)

theorem rhoStab01_apply (hG : Hyp G F m) (g : stab01 G F) :
    rhoStab01 hG g = semilinPart F (g : G) := rfl

theorem rhoStab01_injective (hG : Hyp G F m) : Function.Injective (rhoStab01 hG) :=
  fun g h he => Subtype.ext (semilinPart_injOn_stab01 hG g.2 h.2 he)

theorem isCyclic_stab01 [Finite F] (hG : Hyp G F m) : IsCyclic (stab01 G F) := by
  have := isCyclic_ringAut (by have := hG.two_le; omega) hG.card
  exact isCyclic_of_injective (rhoStab01 hG) (rhoStab01_injective hG)

theorem card_stab01_le [Finite F] (hG : Hyp G F m) : Nat.card (stab01 G F) ≤ m := by
  rw [← card_ringAut (by have := hG.two_le; omega) hG.card]
  exact Nat.card_le_card_of_injective _ (rhoStab01_injective hG)

theorem commutator_stabilizer_le [Finite F] (hG : Hyp G F m) :
    ⁅stabilizer G (0 : F), stabilizer G (0 : F)⁆ ≤ mulSubgroup G F := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hc : ⁅a, b⁆ ∈ stabilizer G (0 : F) :=
    (stabilizer G (0 : F)).mul_mem ((stabilizer G (0 : F)).mul_mem
      ((stabilizer G (0 : F)).mul_mem ha hb) ((stabilizer G (0 : F)).inv_mem ha))
      ((stabilizer G (0 : F)).inv_mem hb)
  rw [← semilinPart_eq_one_iff hG hc]
  have h := congrArg (rho hG) (show (⟨⁅a, b⁆, hc⟩ : stabilizer G (0 : F)) =
    ⁅(⟨a, ha⟩ : stabilizer G (0 : F)), ⟨b, hb⟩⁆ from rfl)
  rw [rho_apply, map_commutatorElement] at h
  change semilinPart F ⁅a, b⁆ = 1
  rw [h, commutatorElement_def, ringAut_mul_comm (by have := hG.two_le; omega) hG.card
    (rho hG ⟨a, ha⟩) (rho hG ⟨b, hb⟩)]
  group

theorem stab01_comm [Finite F] (hG : Hyp G F m) {a b : G} (ha : a ∈ stab01 G F)
    (hb : b ∈ stab01 G F) : a * b = b * a := by
  have := isCyclic_stab01 hG
  have h := IsCyclic.commGroup.mul_comm (⟨a, ha⟩ : stab01 G F) ⟨b, hb⟩
  exact congrArg Subtype.val h

end Setting

end CFSG.GH74.Uniqueness.Hering
