module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJAssembleFrame
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWCoreThree
public import CFSG.LieType.Steinberg.CentralExt.TrialityCoprime
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6RouteWStarProved
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJGlue

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Subgroup CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
  CFSG.ClassicalInvolution.G2D4Models CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg

open scoped MatrixGroups

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)



section Transport

variable {K : Type} [Field K] [Finite K]

@[expose] def twistedEquivFixed (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (σ : K →+* K) (hσq : ∀ c, σ c = c ^ q) :
    twistedGroup σ ≃* graphFixedRootGroup TwistTag.D4 K σ :=
  (Subgroup.equivMapOfInjective (twistedGroup σ) (adjointGroup d4 K).subtype
    Subtype.val_injective).trans
    (MulEquiv.subgroupCongr
      (CFSG.LieType.Steinberg.CentralExt.TrialityClosed.map_twistedGroup_eq_graphFixedRootGroup hK2 hq
        hK hσq))

theorem coe_twistedEquivFixed (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (σ : K →+* K) (hσq : ∀ c, σ c = c ^ q) (x : twistedGroup σ) :
    ((twistedEquivFixed hK2 hq hK σ hσq x : graphFixedRootGroup TwistTag.D4 K σ) :
      ModGL TwistTag.D4.tag K) = twistedIncl σ x := rfl

theorem mem_JTw_iff_fieldActorFixed (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (σ : K ≃+* K) (hσq : ∀ c, σ.toRingHom c = c ^ q)
    (x : twistedGroup σ.toRingHom) :
    x ∈ JTw σ.toRingHom ↔
      twistedEquivFixed hK2 hq hK σ.toRingHom hσq x ∈ fieldActorFixed σ := by
  rw [mem_JTw, mem_fieldActorFixed]
  constructor
  · intro h
    refine Subtype.ext ((coe_fieldActor σ σ _).trans ?_)
    rw [coe_twistedEquivFixed]
    exact h
  · intro h
    have h' := (coe_fieldActor σ σ _).symm.trans (congrArg Subtype.val h)
    rw [coe_twistedEquivFixed] at h'
    exact h'

end Transport

section Exists

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] [CharP K ℓ] {r : ℕ}

theorem exists_phi6JData_tw (hf : 1 ≤ f) (hℓ2 : ℓ ≠ 2) (hq3 : 3 ≤ ℓ ^ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσq : ∀ c, σ c = c ^ (ℓ ^ f)) (hr : r.Prime)
    (hr3 : 3 < r) (hrd : (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1) :
    Nonempty (Phi6JData (twistedGroup σ.toRingHom) (JTw σ.toRingHom) (fixedField σ.toRingHom) r
      (ℓ ^ f)) := by
  obtain ⟨D⟩ := exists_phi6JData_C hf hℓ2 hq3 hK hσq hr hr3 hrd
  have hℓ : ℓ.Prime := Fact.out
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hq2 : 2 ≤ ℓ ^ f := by omega
  exact ⟨D.transport (twistedEquivFixed hK2 hq2 hK σ.toRingHom hσq)
    (mem_JTw_iff_fieldActorFixed hK2 hq2 hK σ hσq)⟩

end Exists

section Glue

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K] {r : ℕ}

theorem phi6Placement_of_JData (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσq : ∀ c, σ c = c ^ (ℓ ^ f))
    (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c) (hq4 : 4 ≤ ℓ ^ f)
    (D : Phi6JData (twistedGroup σ.toRingHom) (JTw σ.toRingHom) (fixedField σ.toRingHom) r
      (ℓ ^ f)) :
    Phi6Placement σ.toRingHom hσ (ℓ ^ f) D.E₀ D.w :=
  phi6Placement_of_J_data hℓ hℓ2 hf hK σ hσq hσ D.E₀ D.w D.hww D.hw1 D.hwJ D.θ.range
    (D.hθsimple hq4).2 (D.hθsimple hq4).1 D.hθcard
    (fun x hx => by obtain ⟨s, rfl⟩ := hx; exact D.hθw s)
    (by rintro _ ⟨s, rfl⟩; exact D.hθJ s) D.x₀ D.hx₀E D.hx₀1
    (fun x hx => by obtain ⟨s, rfl⟩ := hx; exact D.hθx s) D.c D.hcE D.hc1 D.hcJ D.a D.b D.haE D.hbE
    D.a_mem_commutator D.b_mem_commutator D.hab

theorem phi6PlacementThree_of_JData (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσq : ∀ c, σ c = c ^ (ℓ ^ f))
    (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c) (hq3 : ℓ ^ f = 3)
    (D : Phi6JData (twistedGroup σ.toRingHom) (JTw σ.toRingHom) (fixedField σ.toRingHom) r
      (ℓ ^ f)) :
    Phi6PlacementThree σ.toRingHom hσ D.E₀ D.w := by
  obtain ⟨g, hgJ, hg, hMconj⟩ := exists_g_for_placement hℓ hℓ2 hf hK σ hσq hσ D.w D.hww D.hw1 D.hwJ
  have hconjJ : ∀ y ∈ JTw σ.toRingHom, g * y * g⁻¹ ∈ JTw σ.toRingHom := fun y hy =>
    mul_mem (mul_mem hgJ hy) (inv_mem hgJ)
  have hcard : Nat.card D.θ.range = 12 := by
    rw [D.hθcard, hq3]
    norm_num
  exact ⟨g, D.θ, D.x₀, D.c, D.a, D.b, hg, D.hθker, hcard, D.hθw, D.hx₀E, D.hx₀1, D.hθx,
    fun s => hconjJ _ (D.hθJ s), D.hcE, D.hc1, hconjJ D.c D.hcJ, D.haE, D.hbE,
    hMconj _ D.a_mem_commutator, hMconj _ D.b_mem_commutator, D.hab⟩

end Glue

section Main

theorem phi6PlacementSome_holds (r : ℕ) (hr5 : 5 ≤ r) : Coordinator.Phi6PlacementSome r := by
  intro ℓ f hℓ hℓ2 hf hq5 K _ _ hK σ hσq hσ hr hrℓ hd
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  obtain ⟨D⟩ := exists_phi6JData_tw hf hℓ2 (by omega) hK σ hσq hr (by omega) hd
  exact ⟨D.E₀, D.w, D.P, D.hEp, D.hEc, D.hww, D.hwE, D.hEP, D.hPc, D.hPΩ,
    ⟨D.u, D.x₁, D.hu, D.hu1, D.hx₁E, D.hx₁1, D.huw, D.hux⟩,
    phi6Placement_of_JData hℓ hℓ2 hf hK σ hσq hσ (by omega) D⟩

theorem phi6PlacementSomeThree_holds (r : ℕ) (hr5 : 5 ≤ r) : Phi6PlacementSomeThree r := by
  intro ℓ f hℓ hℓ2 hf hlt K _ _ hK σ hσq hσ hr hrℓ hd
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hq3 : ℓ ^ f = 3 := by
    have hodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
    have h3 : 3 ≤ ℓ := by
      have := hℓ.two_le
      rcases Nat.lt_or_ge ℓ 3 with h | h
      · omega
      · exact h
    have : 3 ≤ ℓ ^ f := le_trans h3 (Nat.le_self_pow (by omega) ℓ)
    obtain ⟨k, hk⟩ := hodd
    omega
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  obtain ⟨D⟩ := exists_phi6JData_tw hf hℓ2 (by omega) hK σ hσq hr (by omega) hd
  exact ⟨D.E₀, D.w, D.P, D.hEp, D.hEc, D.hww, D.hwE, D.hEP, D.hPc, D.hPΩ,
    ⟨D.u, D.x₁, D.hu, D.hu1, D.hx₁E, D.hx₁1, D.huw, D.hux⟩,
    phi6PlacementThree_of_JData hℓ hℓ2 hf hK σ hσq hσ hq3 D⟩

end Main

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
