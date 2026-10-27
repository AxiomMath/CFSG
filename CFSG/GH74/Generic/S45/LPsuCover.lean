module

public import CFSG.GH74.Generic.S45.LUniFix
public import CFSG.GH74.Generic.S45.LCoverEq
public import CFSG.GH74.Generic.S45.LOddG
public import CFSG.LieType.Steinberg.CentralExt.UnitaryHigher
public import CFSG.GH74.Generic.S45.LUniLift

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.Blueprint Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open scoped Matrix

theorem psu_fixed_data {S : Type} [Group S] [Finite S] {n r f : ℕ} (hn : 3 ≤ n) (hr2 : r ≠ 2)
    (hmodel : StatedClassicalModel S .PSU n r f)
    (h1b : ∀ {K : Type} [Field K] (h : UnitaryFieldData r f K) (A : Matrix (Fin n) (Fin n) K) (l : K),
      (A.map h.bar)ᵀ * A = 1 → A * A = (l * l) • 1 → h.bar l * l = -1 →
        Uni.FixConcl h n A id)
    (h2a : ∀ {K : Type} [Field K] (h : UnitaryFieldData r f K) (A : Matrix (Fin n) (Fin n) K),
      (A.map h.bar)ᵀ * A = 1 → A * A.map h.bar = (-1 : K) • 1 →
        Uni.FixConcl h n A (fun M => M.map h.bar))
    {ya : MulAut S} (hsq : ya * ya = 1) :
    ∃ (F : Type) (_ : Field F) (_ : UnitaryFieldData r f F) (θ : unitarySU r f F n →* S)
      (τ : MulAut ↥(unitarySU r f F n)) (c : ↥(unitarySU r f F n)),
        Function.Surjective θ ∧ (∀ g, θ (τ g) = ya (θ g)) ∧ τ c = c ∧ orderOf (θ c) = 4 := by
  classical
  obtain ⟨hadm, F, _, _, hF, ⟨e₀⟩⟩ := hmodel
  have hr : r.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hud : UnitaryFieldData r f F := ⟨hr, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : S ≃* unitaryPSU hud n := e₀.trans (unitaryPSUEquiv hud (by omega)).symm
  let θ : unitarySU r f F n →* S := ψ.symm.toMonoidHom.comp (unitaryProj hud n)
  have hθ : Function.Surjective θ := ψ.symm.surjective.comp (unitaryProj_surjective hud n)
  have hθ1 : ∀ g : unitarySU r f F n, θ g = 1 ↔ g ∈ unitaryScalars hud n := by
    intro g
    change ψ.symm (unitaryProj hud n g) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ker_unitaryProj]
  have hker : θ.ker ≤ Subgroup.center (unitarySU r f F n) := fun g hg =>
    unitaryScalars_le_center hud n ((hθ1 g).1 hg)
  obtain ⟨A, φ, hA, hAu, hlift, hinv⟩ := exists_lift_unitarySU' hud hr2 hn θ hθ hker
    (ya : S ≃* S)
  obtain ⟨hφ, hcomp⟩ := hinv (fun x => by
    have := congrArg (fun φ : MulAut S => φ x) hsq
    simpa using this)
  obtain ⟨c, hc, hc2, hc4⟩ := Uni.exists_fixed_unitary hud hr2 hn (h1b hud) (h2a hud) hA hAu hφ
    hcomp
  have hτinv : ∀ g, unitaryConjHom A φ hA (unitaryConjHom A φ hA g) = g := fun g =>
    congrArg (fun F : unitarySU r f F n →* unitarySU r f F n => F g) hcomp
  let τ : MulAut ↥(unitarySU r f F n) :=
    MulEquiv.ofBijective (unitaryConjHom A φ hA) (Function.Involutive.bijective hτinv)
  refine ⟨F, inferInstance, hud, θ, τ, c, hθ, hlift, hc, ?_⟩
  have h2 : ¬ θ c ^ (2 ^ 1) = 1 := by
    rw [pow_one, ← map_pow]
    intro h1
    exact hc2 ((hθ1 _).1 h1)
  have h4 : θ c ^ (2 ^ (1 + 1)) = 1 := by
    rw [show 2 ^ (1 + 1) = 4 by norm_num, ← map_pow]
    exact (hθ1 _).2 hc4
  rw [orderOf_eq_prime_pow h2 h4]
  norm_num

theorem Hyp1310.false_of_su_fixed {K : Type} [Group K] [Finite K] {y : MulAut K}
    {L : Subgroup K} (hyp : Hyp1310 K y L) {yb : MulAut (K ⧸ Subgroup.center K)}
    (hyb : ∀ k : K, yb (QuotientGroup.mk k) = QuotientGroup.mk (y k))
    {F : Type} [Field F] {p f n : ℕ} (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (θ : unitarySU p f F n →* K ⧸ Subgroup.center K) (hθ : Function.Surjective θ)
    (τ : MulAut ↥(unitarySU p f F n)) (hτ : ∀ g, θ (τ g) = yb (θ g))
    (c : ↥(unitarySU p f F n)) (hc : τ c = c) (hord : orderOf (θ c) = 4) : False := by
  classical
  obtain ⟨hKp, hZ2, -, -, hno4, -⟩ := hyp.data
  have : Finite F := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have hK : Nat.card F = (p ^ f) ^ 2 := h.card_eq_sq
  have hPp : Group.IsPerfect ↥(unitarySU p f F n) := (isPerfect_and_center_unitarySU' h hp2 hn).1
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* ↥(unitarySU p f F n)),
      Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup 2 π.ker →
        ∃ σ : ↥(unitarySU p f F n) →* E, ∀ x, π (σ x) = x := by
    intro E _ _ π hπ hcen h2'
    set ι := CFSG.LieType.Universal.Unitary.equivStatedSU hK n with hι
    let π' : E →* CFSG.LieType.Universal.Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F p f) n :=
      ι.symm.toMonoidHom.comp π
    have hπ' : Function.Surjective π' := ι.symm.surjective.comp hπ
    have hker : π'.ker = π.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      change ι.symm (π x) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff]
    obtain ⟨s, hs, -⟩ := CFSG.LieType.Steinberg.su_central_two_extension_splitting hK hp2 (n := n) (by omega) hπ'
      (hker ▸ hcen) (hker ▸ h2')
    refine ⟨s.comp ι.symm.toMonoidHom, fun x => ?_⟩
    have := hs (ι.symm x)
    change ι.symm (π (s (ι.symm x))) = ι.symm x at this
    exact ι.symm.injective this
  let η : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  have hη : Function.Surjective η := QuotientGroup.mk'_surjective _
  have hηker : η.ker = Subgroup.center K := QuotientGroup.ker_mk' _
  have hη2 : IsPGroup 2 η.ker := by rw [hηker]; exact hZ2
  obtain ⟨x, hx, h4⟩ := exists_fixed_dvd_of_cover hKp hPp hsplit hη hηker.le hη2 hθ
    (y := y) (yb := yb) (fun k => (hyb k).symm) hτ hc (by rw [hord])
  exact hno4 x hx h4

end CFSG.GH74.Generic.S45
