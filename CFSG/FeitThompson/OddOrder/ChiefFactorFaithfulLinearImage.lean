module

public import CFSG.FeitThompson.OddOrder.ChiefFactorFixedLineDimension
public import CFSG.FeitThompson.OddOrder.PrimeDimAbelianImageTwoModels
public import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
public import Mathlib.GroupTheory.FixedPointFree
import CFSG.FeitThompson.OddOrder.QuotientFrobeniusAction

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace ChiefFactorFaithfulImage

open Subgroup Module Representation ChiefFactorLinearAction ChiefFactorFixedLine

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

def mulAutMultiplicativeMulEquivLinearEquiv (p : ℕ) (V : Type*) [AddCommGroup V]
    [Module (ZMod p) V] : MulAut (Multiplicative V) ≃* (V ≃ₗ[ZMod p] V) where
  toFun f := addEquivEquivZModLinearEquiv p V V (AddEquiv.toMultiplicative.symm f)
  invFun g := AddEquiv.toMultiplicative ((addEquivEquivZModLinearEquiv p V V).symm g)
  left_inv f := by ext v; simp
  right_inv g := by ext v; simp
  map_mul' f g := by ext v; simp

@[simp]
theorem mulAutMultiplicativeMulEquivLinearEquiv_apply (p : ℕ) (V : Type*) [AddCommGroup V]
    [Module (ZMod p) V] (f : MulAut (Multiplicative V)) (v : V) :
    mulAutMultiplicativeMulEquivLinearEquiv p V f v
      = Multiplicative.toAdd (f (Multiplicative.ofAdd v)) := by
  simp [mulAutMultiplicativeMulEquivLinearEquiv]

variable {M : Type*} [Group M] (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

def factorLinearAut (H H₀ : Subgroup M) [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) : M →* (V ≃ₗ[ZMod p] V) :=
  (mulAutMultiplicativeMulEquivLinearEquiv p V).toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (factorConjAut H H₀))

theorem factorLinearAut_apply {H H₀ : Subgroup M} [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) (g : M) (y : ↥H ⧸ H₀.subgroupOf H) :
    factorLinearAut p H H₀ e g (Multiplicative.toAdd (e y))
      = Multiplicative.toAdd (e (factorConjAut H H₀ g y)) := by
  simp [factorLinearAut, MulAut.congr_apply]

theorem factorLinearAut_apply' {H H₀ : Subgroup M} [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) (g : M) (v : V) :
    factorLinearAut p H H₀ e g v
      = Multiplicative.toAdd (e (factorConjAut H H₀ g (e.symm (Multiplicative.ofAdd v)))) := by
  simpa using factorLinearAut_apply p e g (e.symm (Multiplicative.ofAdd v))

theorem factorLinearAut_eq_one_iff {H H₀ : Subgroup M} [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) {g : M} :
    factorLinearAut p H H₀ e g = 1 ↔ factorConjAut H H₀ g = 1 := by
  constructor
  · intro hg
    ext y
    refine e.injective (Multiplicative.toAdd.injective ?_)
    rw [← factorLinearAut_apply p e g y, hg]
    rfl
  · intro hg
    ext v
    rw [factorLinearAut_apply' p e g v, hg]
    simp

theorem factorLinearAut_eq_self_iff {H H₀ : Subgroup M} [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) (g : M) (y : ↥H ⧸ H₀.subgroupOf H) :
    factorLinearAut p H H₀ e g (Multiplicative.toAdd (e y)) = Multiplicative.toAdd (e y)
      ↔ factorConjAut H H₀ g y = y := by
  rw [factorLinearAut_apply]
  exact ⟨fun h => e.injective (Multiplicative.toAdd.injective h), fun h => by rw [h]⟩

theorem factorConjAut_eq_one_of_mem_centralizer {H H₀ : Subgroup M} [H.Normal] [H₀.Normal]
    {g : M} (hg : g ∈ Subgroup.centralizer (H : Set M)) : factorConjAut H H₀ g = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [factorConjAut_mk, MulAut.one_apply]
    congr 1
    refine Subtype.ext ?_
    rw [MulAut.conjNormal_apply]
    have h := (Subgroup.mem_centralizer_iff.1 hg) (y : M) y.2
    rw [← h]
    group

theorem factorLinearAut_eq_one_of_mem_centralizer {H H₀ : Subgroup M} [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) {g : M}
    (hg : g ∈ Subgroup.centralizer (H : Set M)) : factorLinearAut p H H₀ e g = 1 :=
  (factorLinearAut_eq_one_iff p e).2 (factorConjAut_eq_one_of_mem_centralizer hg)

theorem isMulCommutative_quotient {H H₀ : Subgroup M} [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    IsMulCommutative (↥H ⧸ H₀.subgroupOf H) :=
  ⟨⟨fun x y => e.injective (by rw [map_mul, map_mul, mul_comm' (e x)])⟩⟩

def factorLinearImage (H H₀ D : Subgroup M) [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) : Subgroup (V ≃ₗ[ZMod p] V) :=
  D.map (factorLinearAut p H H₀ e)

theorem mem_factorLinearImage {H H₀ D : Subgroup M} [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) {f : V ≃ₗ[ZMod p] V} :
    f ∈ factorLinearImage p H H₀ D e ↔ ∃ g ∈ D, factorLinearAut p H H₀ e g = f :=
  Subgroup.mem_map

theorem factorLinearAut_mem_factorLinearImage {H H₀ D : Subgroup M} [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) {g : M} (hg : g ∈ D) :
    factorLinearAut p H H₀ e g ∈ factorLinearImage p H H₀ D e :=
  (mem_factorLinearImage p e).2 ⟨g, hg, rfl⟩

theorem factorLinearImage_zpowers {H H₀ : Subgroup M} [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) (b : M) :
    factorLinearImage p H H₀ (Subgroup.zpowers b) e
      = Subgroup.zpowers (factorLinearAut p H H₀ e b) :=
  MonoidHom.map_zpowers _ _

theorem factorLinearImage_sup {H H₀ D D' : Subgroup M} [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    factorLinearImage p H H₀ (D ⊔ D') e
      = factorLinearImage p H H₀ D e ⊔ factorLinearImage p H H₀ D' e :=
  Subgroup.map_sup _ _ _

def actionKernel (H H₀ U : Subgroup M) [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) : Subgroup ↥U :=
  MonoidHom.ker ((factorLinearAut p H H₀ e).comp U.subtype)

theorem mem_actionKernel {H H₀ U : Subgroup M} [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) {u : ↥U} :
    u ∈ actionKernel p H H₀ U e ↔ factorLinearAut p H H₀ e (u : M) = 1 := Iff.rfl

instance instNormalActionKernel {H H₀ U : Subgroup M} [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    (actionKernel p H H₀ U e).Normal := by
  unfold actionKernel; infer_instance

theorem mem_factorCentralizer_zpowers_iff {H H₀ B : Subgroup M} [H.Normal] [H₀.Normal] {b : M}
    (hB : B = Subgroup.zpowers b) {y : ↥H ⧸ H₀.subgroupOf H} :
    y ∈ factorCentralizer H H₀ B ↔ factorConjAut H H₀ b y = y := by
  rw [mem_factorCentralizer]
  refine ⟨fun h => h b (hB ▸ Subgroup.mem_zpowers b), fun h d hd => ?_⟩
  exact apply_eq_self_of_mem_zpowers (factorConjAut H H₀) h (hB ▸ hd)

theorem mem_invariants_iff [Fact p.Prime] {H H₀ B : Subgroup M} [H.Normal] [H₀.Normal] {b : M}
    (hB : B = Subgroup.zpowers b) (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) {v : V} :
    v ∈ (linearGroupRep (Subgroup.zpowers (factorLinearAut p H H₀ e b))).invariants
      ↔ e.symm (Multiplicative.ofAdd v) ∈ factorCentralizer H H₀ B := by
  rw [mem_invariants_zpowers_iff, mem_factorCentralizer_zpowers_iff (H := H) (H₀ := H₀) hB,
    ← factorLinearAut_eq_self_iff p e b (e.symm (Multiplicative.ofAdd v))]
  simp

def factorCentralizerEquivInvariants [Fact p.Prime] {H H₀ B : Subgroup M} [H.Normal] [H₀.Normal]
    {b : M} (hB : B = Subgroup.zpowers b)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    ↥(factorCentralizer H H₀ B)
      ≃ ↥(linearGroupRep (Subgroup.zpowers (factorLinearAut p H H₀ e b))).invariants :=
  Equiv.subtypeEquiv (e.toEquiv.trans (Multiplicative.toAdd (α := V))) fun y => by
    rw [mem_invariants_iff p hB e]; simp

theorem natCard_invariants_eq [Fact p.Prime] {H H₀ B : Subgroup M} [H.Normal] [H₀.Normal]
    {b : M} (hB : B = Subgroup.zpowers b)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    Nat.card ↥(linearGroupRep (Subgroup.zpowers (factorLinearAut p H H₀ e b))).invariants
      = Nat.card ↥(factorCentralizer H H₀ B) :=
  (Nat.card_congr (factorCentralizerEquivInvariants p hB e)).symm

structure IsFaithfulImageSetup (H A U B H₀ : Subgroup M) (b : M) (q : ℕ) : Prop
    extends IsFixedLineSetup H A U B H₀ q where
  eq_zpowers : B = Subgroup.zpowers b
  commutator_centralizes : ⁅U, U⁆ ≤ Subgroup.centralizer (H : Set M)

namespace IsFaithfulImageSetup

variable {H A U B H₀ : Subgroup M} {b : M} {q : ℕ}

section Basic

variable (hs : IsFaithfulImageSetup H A U B H₀ b q)

include hs

theorem mem_B : b ∈ B := hs.eq_zpowers ▸ Subgroup.mem_zpowers b

theorem orderOf_b : orderOf b = q := by rw [← Nat.card_zpowers, ← hs.eq_zpowers, hs.card_B]

theorem b_ne_one : b ≠ 1 := fun h => by
  have h2 := hs.orderOf_b
  rw [h, orderOf_one] at h2
  exact hs.prime_q.one_lt.ne h2

theorem conj_mem_U {a : M} (ha : a ∈ A) {u : M} (hu : u ∈ U) : a * u * a⁻¹ ∈ U := by
  have h := hs.normal_U.conj_mem ⟨u, hs.le_U hu⟩ (by rwa [Subgroup.mem_subgroupOf]) ⟨a, ha⟩
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

theorem le_normalizer_U : B ≤ Subgroup.normalizer (U : Set M) := fun x hx =>
  Subgroup.mem_normalizer_iff.2 fun u =>
    ⟨fun hu => hs.conj_mem_U (hs.le_B hx) hu, fun hu => by
      have h := hs.conj_mem_U (A.inv_mem (hs.le_B hx)) hu
      rwa [show x⁻¹ * (x * u * x⁻¹) * (x⁻¹)⁻¹ = u by group] at h⟩

theorem sup_eq_A : U ⊔ B = A := by
  have h2 := congrArg (Subgroup.map A.subtype) hs.isComplement_B.sup_eq_top
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hs.le_U, inf_eq_left.2 hs.le_B, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h2
  exact h2

def conjAut : ↥B →* MulAut ↥U := conjOnNormalized U hs.le_normalizer_U

theorem coe_conjAut_apply (x : ↥B) (u : ↥U) :
    ((hs.conjAut x u : ↥U) : M) = (x : M) * (u : M) * (x : M)⁻¹ :=
  conjOnNormalized_apply_coe _ _ _

theorem zpowers_eq_top : Subgroup.zpowers (⟨b, hs.mem_B⟩ : ↥B) = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun x => ?_
  obtain ⟨n, hn⟩ : (x : M) ∈ Subgroup.zpowers b := hs.eq_zpowers ▸ x.2
  exact ⟨n, Subtype.ext (by simpa using hn)⟩

theorem fixedPointFree_conjAut :
    MonoidHom.FixedPointFree (hs.conjAut ⟨b, hs.mem_B⟩ : ↥U → ↥U) := by
  intro u hu
  have hcoe : b * (u : M) * b⁻¹ = (u : M) := by
    have h := congrArg (Subtype.val (p := fun y : M => y ∈ U)) hu
    rwa [hs.coe_conjAut_apply] at h
  have hmem : (u : M) ∈ U ⊓ Subgroup.centralizer {b} := by
    refine ⟨u.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc (u : M) * b = (b * (u : M) * b⁻¹) * b := by rw [hcoe]
      _ = b * (u : M) := by group
  rw [hs.centralizer_inf_eq_bot b hs.mem_B hs.b_ne_one, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

end Basic

section Linear

variable [H.Normal] [H₀.Normal] (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem conjAut_mem_actionKernel (hs : IsFaithfulImageSetup H A U B H₀ b q)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) (x : ↥B) {u : ↥U}
    (hu : u ∈ actionKernel p H H₀ U e) : hs.conjAut x u ∈ actionKernel p H H₀ U e := by
  rw [mem_actionKernel] at hu ⊢
  rw [hs.coe_conjAut_apply, map_mul, map_mul, hu, map_inv, mul_one, mul_inv_cancel]

theorem isInvariantSubgroup_actionKernel (hs : IsFaithfulImageSetup H A U B H₀ b q)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    IsInvariantSubgroup hs.conjAut (actionKernel p H H₀ U e) :=
  isInvariantSubgroup_iff_forall_map_eq.2 fun x => le_antisymm
    (by rintro y ⟨u, hu, rfl⟩; exact hs.conjAut_mem_actionKernel p e x hu)
    (fun y hy => ⟨hs.conjAut x⁻¹ y, hs.conjAut_mem_actionKernel p e x⁻¹ hy, by
      change hs.conjAut x (hs.conjAut x⁻¹ y) = y
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]⟩)

theorem isMulCommutative_factorLinearImage_U (hs : IsFaithfulImageSetup H A U B H₀ b q)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    IsMulCommutative ↥(factorLinearImage p H H₀ U e) := by
  refine ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨u, hu, hux⟩ := (mem_factorLinearImage p e).1 x.2
  obtain ⟨v, hv, hvy⟩ := (mem_factorLinearImage p e).1 y.2
  refine Subtype.ext ?_
  have hcomm := Subgroup.commutator_mem_commutator hu hv
  rw [commutatorElement_def] at hcomm
  have h1 : factorLinearAut p H H₀ e (u * v * u⁻¹ * v⁻¹) = 1 :=
    factorLinearAut_eq_one_of_mem_centralizer p e (hs.commutator_centralizes hcomm)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hux, hvy] at h1
  have h2 : (x : V ≃ₗ[ZMod p] V) * (y : V ≃ₗ[ZMod p] V) = (y : V ≃ₗ[ZMod p] V) * x :=
    mul_inv_eq_one.1 (by rw [mul_inv_rev]; simpa [mul_assoc] using h1)
  exact h2

theorem factorLinearImage_B_eq_zpowers (hs : IsFaithfulImageSetup H A U B H₀ b q)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    factorLinearImage p H H₀ B e = Subgroup.zpowers (factorLinearAut p H H₀ e b) := by
  rw [hs.eq_zpowers, factorLinearImage_zpowers]

theorem factorLinearImage_A_eq (hs : IsFaithfulImageSetup H A U B H₀ b q)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    factorLinearImage p H H₀ A e
      = factorLinearImage p H H₀ U e ⊔ Subgroup.zpowers (factorLinearAut p H H₀ e b) := by
  rw [← factorLinearImage_zpowers, ← factorLinearImage_sup, ← hs.eq_zpowers, hs.sup_eq_A]

theorem mem_normalizer_factorLinearImage (hs : IsFaithfulImageSetup H A U B H₀ b q)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    factorLinearAut p H H₀ e b
      ∈ Subgroup.normalizer (factorLinearImage p H H₀ U e : Set (V ≃ₗ[ZMod p] V)) := by
  refine Subgroup.mem_normalizer_iff.2 fun f => ?_
  constructor
  · rintro hf
    obtain ⟨u, hu, rfl⟩ := (mem_factorLinearImage p e).1 hf
    refine (mem_factorLinearImage p e).2 ⟨b * u * b⁻¹, hs.conj_mem_U (hs.le_B hs.mem_B) hu, ?_⟩
    rw [map_mul, map_mul, map_inv]
  · intro hf
    obtain ⟨u, hu, hueq⟩ := (mem_factorLinearImage p e).1 hf
    refine (mem_factorLinearImage p e).2 ⟨b⁻¹ * u * b, by
      simpa using hs.conj_mem_U (A.inv_mem (hs.le_B hs.mem_B)) hu, ?_⟩
    rw [map_mul, map_mul, map_inv, hueq]
    group

variable [Finite M] [Group.IsSolvable M]

theorem natCard_quotient_eq (hs : IsFaithfulImageSetup H A U B H₀ b q)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) (hp : p.Prime) :
    Nat.card (↥H ⧸ H₀.subgroupOf H) = p ^ q := by
  rw [hs.natCard_quotient_eq_pow, hs.natCard_factorCentralizer_B_eq e hp]

theorem ne_q (hs : IsFaithfulImageSetup H A U B H₀ b q)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) (hp : p.Prime) : p ≠ q := by
  intro h
  have hpH : p ∣ Nat.card ↥H :=
    (dvd_pow_self p hs.prime_q.pos.ne').trans
      ((hs.natCard_quotient_eq p e hp) ▸ Subgroup.card_quotient_dvd_card _)
  have hqA : p ∣ Nat.card ↥A := h ▸ hs.card_B ▸ Subgroup.card_dvd_of_le hs.le_B
  have hdvd := Nat.dvd_gcd hpH hqA
  rw [hs.coprime] at hdvd
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one hdvd)

theorem finrank_eq (hs : IsFaithfulImageSetup H A U B H₀ b q)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) (hp : p.Prime) :
    Module.finrank (ZMod p) V = q :=
  hs.toIsFixedLineSetup.finrank_eq e hp

theorem nontrivial_quotient (hs : IsFaithfulImageSetup H A U B H₀ b q)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) (hp : p.Prime) :
    Nontrivial (↥H ⧸ H₀.subgroupOf H) := by
  rw [← Finite.one_lt_card_iff_nontrivial, hs.natCard_quotient_eq p e hp]
  exact Nat.one_lt_pow hs.prime_q.pos.ne' hp.one_lt

theorem nontrivial_of_prime (hs : IsFaithfulImageSetup H A U B H₀ b q)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) (hp : p.Prime) : Nontrivial V :=
  have := hs.nontrivial_quotient p e hp
  (e.toEquiv.trans (Multiplicative.toAdd (α := V))).symm.nontrivial

theorem factorLinearImage_U_ne_bot (hs : IsFaithfulImageSetup H A U B H₀ b q)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) (hp : p.Prime) :
    factorLinearImage p H H₀ U e ≠ ⊥ := by
  intro hbot
  have hall : ∀ y : ↥H ⧸ H₀.subgroupOf H, y = 1 := by
    intro y
    have hy : y ∈ factorCentralizer H H₀ U := by
      refine mem_factorCentralizer.2 fun u hu => ?_
      have h1 : factorLinearAut p H H₀ e u ∈ factorLinearImage p H H₀ U e :=
        factorLinearAut_mem_factorLinearImage p e hu
      rw [hbot, Subgroup.mem_bot] at h1
      rw [(factorLinearAut_eq_one_iff p e).1 h1]
      rfl
    rwa [hs.factorCentralizer_U, Subgroup.mem_bot] at hy
  obtain ⟨x, y, hxy⟩ := (hs.nontrivial_quotient p e hp).exists_pair_ne
  exact hxy ((hall x).trans (hall y).symm)

theorem orderOf_factorLinearAut_b (hs : IsFaithfulImageSetup H A U B H₀ b q)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) (hp : p.Prime) :
    orderOf (factorLinearAut p H H₀ e b) = q := by
  have hdvd : orderOf (factorLinearAut p H H₀ e b) ∣ q := hs.orderOf_b ▸ orderOf_map_dvd _ b
  rcases (Nat.dvd_prime hs.prime_q).1 hdvd with h1 | h1
  · exfalso
    rw [orderOf_eq_one_iff] at h1
    have htop : factorCentralizer H H₀ B = ⊤ :=
      eq_top_iff.2 fun y _ => (mem_factorCentralizer_zpowers_iff hs.eq_zpowers).2
        ((factorLinearAut_eq_one_iff p e).1 h1 ▸ rfl)
    have hcard : Nat.card (↥H ⧸ H₀.subgroupOf H) = p := by
      rw [← Subgroup.card_top (G := ↥H ⧸ H₀.subgroupOf H), ← htop,
        hs.natCard_factorCentralizer_B_eq e hp]
    rw [hs.natCard_quotient_eq p e hp] at hcard
    exact hs.prime_q.one_lt.ne'
      (Nat.pow_right_injective hp.two_le (hcard.trans (pow_one p).symm))
  · exact h1

theorem inf_centralizer_eq_bot (hs : IsFaithfulImageSetup H A U B H₀ b q)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    factorLinearImage p H H₀ U e ⊓ Subgroup.centralizer {factorLinearAut p H H₀ e b} = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 ?_
  intro a ha
  obtain ⟨haD, haC⟩ := Subgroup.mem_inf.1 ha
  obtain ⟨u, hu, rfl⟩ := (mem_factorLinearImage p e).1 haD
  rw [Subgroup.mem_centralizer_singleton_iff] at haC
  have hker : (⟨u, hu⟩ : ↥U)⁻¹ * hs.conjAut ⟨b, hs.mem_B⟩ ⟨u, hu⟩ ∈ actionKernel p H H₀ U e := by
    rw [mem_actionKernel]
    have hcoe : (((⟨u, hu⟩ : ↥U)⁻¹ * hs.conjAut ⟨b, hs.mem_B⟩ ⟨u, hu⟩ : ↥U) : M)
        = u⁻¹ * (b * u * b⁻¹) := by
      rw [Subgroup.coe_mul, hs.coe_conjAut_apply]
      simp
    rw [hcoe, map_mul, map_inv, map_mul, map_mul, map_inv,
      show factorLinearAut p H H₀ e b * factorLinearAut p H H₀ e u
          * (factorLinearAut p H H₀ e b)⁻¹ = factorLinearAut p H H₀ e u from by
        rw [← haC]; group]
    exact inv_mul_cancel _
  have hres := mem_of_inv_mul_apply_mem hs.prime_q (B := ↥B) (ρ := hs.conjAut)
    (by simpa using hs.card_B) hs.zpowers_eq_top hs.fixedPointFree_conjAut
    (hs.isInvariantSubgroup_actionKernel p e) hker
  rw [mem_actionKernel] at hres
  exact hres

theorem finrank_invariants [Fact p.Prime] (hs : IsFaithfulImageSetup H A U B H₀ b q)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    Module.finrank (ZMod p)
      ↥(linearGroupRep (Subgroup.zpowers (factorLinearAut p H H₀ e b))).invariants = 1 := by
  have hp : p.Prime := Fact.out
  have hfin : Finite V := Finite.of_equiv _ (e.toEquiv.trans (Multiplicative.toAdd (α := V)))
  have hcard : Nat.card
      ↥(linearGroupRep (Subgroup.zpowers (factorLinearAut p H H₀ e b))).invariants = p := by
    rw [natCard_invariants_eq p hs.eq_zpowers e, hs.natCard_factorCentralizer_B_eq e hp]
  have hfd : Module.Finite (ZMod p)
      ↥(linearGroupRep (Subgroup.zpowers (factorLinearAut p H H₀ e b))).invariants :=
    Module.Finite.of_finite
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod p)
    (V := ↥(linearGroupRep (Subgroup.zpowers (factorLinearAut p H H₀ e b))).invariants)
  rw [hcard, Nat.card_zmod] at h2
  exact (Nat.pow_right_injective hp.two_le ((pow_one p).trans h2)).symm

theorem isIrreducible_factorLinearImage_A [Fact p.Prime]
    (hs : IsFaithfulImageSetup H A U B H₀ b q)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) :
    (linearGroupRep (factorLinearImage p H H₀ A e)).IsIrreducible := by
  have hcomm : IsMulCommutative (↥H ⧸ H₀.subgroupOf H) := isMulCommutative_quotient e
  refine isIrreducible_linearGroupRep_iff.2 ⟨hs.nontrivial_of_prime p e Fact.out, fun W hW => ?_⟩
  set S := subgroupOfSubmodule e W with hS
  have hSA : ∀ a ∈ A, ∀ x ∈ S, factorConjAut H H₀ a x ∈ S := by
    intro a ha x hx
    rw [hS, mem_subgroupOfSubmodule] at hx ⊢
    have hmem := hW _ (factorLinearAut_mem_factorLinearImage p e ha) _ hx
    rwa [factorLinearAut_apply] at hmem
  have hSM : ∀ g : M, ∀ x ∈ S, factorConjAut H H₀ g x ∈ S :=
    forall_factorConjAut_mem H H₀ hs.isComplement_A.sup_eq_top _ hSA
  have hnormal := normal_factorPreimage H H₀ _ hSM
  rcases hs.isChiefFactor.eq_or_eq hnormal (le_factorPreimage H H₀ hs.isChiefFactor.le _)
    (factorPreimage_le H H₀ _) with h | h
  · refine Or.inl (subgroupOfSubmodule_injective e ?_)
    rw [subgroupOfSubmodule_bot]
    exact factorPreimage_injective H H₀ (h.trans (factorPreimage_bot H H₀ hs.isChiefFactor.le).symm)
  · refine Or.inr (subgroupOfSubmodule_injective e ?_)
    rw [subgroupOfSubmodule_top]
    exact factorPreimage_injective H H₀ (h.trans (factorPreimage_top H H₀).symm)

noncomputable def primeDimLinearSetup [Fact p.Prime] [Fact q.Prime]
    (hs : IsFaithfulImageSetup H A U B H₀ b q)
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V) : PrimeDimLinearSetup p q V where
  ne_char := Ne.symm (hs.ne_q p e Fact.out)
  finrank_eq := hs.finrank_eq p e Fact.out
  A := factorLinearImage p H H₀ U e
  b := factorLinearAut p H H₀ e b
  A_ne_bot := hs.factorLinearImage_U_ne_bot p e Fact.out
  isMulCommutative_A := hs.isMulCommutative_factorLinearImage_U p e
  orderOf_b := hs.orderOf_factorLinearAut_b p e Fact.out
  b_mem_normalizer := hs.mem_normalizer_factorLinearImage p e
  isIrreducible_sup := by
    rw [← hs.factorLinearImage_A_eq p e]; exact hs.isIrreducible_factorLinearImage_A p e
  inf_centralizer_b := hs.inf_centralizer_eq_bot p e
  finrank_invariants := hs.finrank_invariants p e

end Linear

end IsFaithfulImageSetup

end ChiefFactorFaithfulImage

end CFSG.FeitThompson
