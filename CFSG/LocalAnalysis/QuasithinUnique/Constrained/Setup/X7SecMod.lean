module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3H13
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTwist

public section

namespace CFSG.QuasithinUnique.Setup.X7Sec

open scoped MatrixGroups Matrix

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.X3 CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Fix

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [Finite V]

theorem card_fix_le {X M Fx : Submodule k V} (hXM : X ≤ M) :
    Nat.card ↥X * Nat.card ↥(M ⊓ Fx) ≤ Nat.card ↥M * Nat.card ↥(X ⊓ Fx) := by
  have h1 := natCard_sup_mul_natCard_inf X Fx
  have h2 := natCard_sup_mul_natCard_inf M Fx
  have h3 : Nat.card ↥(X ⊔ Fx) ≤ Nat.card ↥(M ⊔ Fx) :=
    Nat.le_of_dvd Nat.card_pos (natCard_dvd_of_le (sup_le_sup_right hXM Fx))
  have hF : 0 < Nat.card ↥Fx := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right (c := Nat.card ↥Fx) ?_ hF
  calc Nat.card ↥X * Nat.card ↥(M ⊓ Fx) * Nat.card ↥Fx
      = (Nat.card ↥X * Nat.card ↥Fx) * Nat.card ↥(M ⊓ Fx) := by ring
    _ = (Nat.card ↥(X ⊔ Fx) * Nat.card ↥(X ⊓ Fx)) * Nat.card ↥(M ⊓ Fx) := by rw [← h1]
    _ ≤ (Nat.card ↥(M ⊔ Fx) * Nat.card ↥(X ⊓ Fx)) * Nat.card ↥(M ⊓ Fx) := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3)
    _ = (Nat.card ↥(M ⊔ Fx) * Nat.card ↥(M ⊓ Fx)) * Nat.card ↥(X ⊓ Fx) := by ring
    _ = (Nat.card ↥M * Nat.card ↥Fx) * Nat.card ↥(X ⊓ Fx) := by rw [h2]
    _ = Nat.card ↥M * Nat.card ↥(X ⊓ Fx) * Nat.card ↥Fx := by ring

end Fix

section Srep

variable {F : Type} [Field F] {N : Type} [Group N] {V : Type} [AddCommGroup V]
  [Module (ZMod 2) V]

@[expose] noncomputable def srep (σ : N →* (V ≃ₗ[ZMod 2] V)) (L : Subgroup N)
    (φ : SL(3, F) →* ↥L) (U : Submodule (ZMod 2) V) (hU : Offender.IsInvariant σ L U) :
    Representation (ZMod 2) SL(3, F) ↥U :=
  (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := ↥U)).comp
    ((resSub σ L U hU).comp φ)

theorem srep_apply (σ : N →* (V ≃ₗ[ZMod 2] V)) (L : Subgroup N) (φ : SL(3, F) →* ↥L)
    (U : Submodule (ZMod 2) V) (hU : Offender.IsInvariant σ L U) (x : SL(3, F)) (u : ↥U) :
    ((srep σ L φ U hU x u : ↥U) : V) = σ ((φ x : ↥L) : N) (u : V) :=
  resSub_apply σ L U hU (φ x) u

theorem srep_twist_equiv (σ : N →* (V ≃ₗ[ZMod 2] V)) (L : Subgroup N) (φ : SL(3, F) →* ↥L)
    (n : N) (Φ : SL(3, F) →* SL(3, F))
    (hΦ : ∀ x, n * ((φ x : ↥L) : N) * n⁻¹ = ((φ (Φ x) : ↥L) : N))
    (U : Submodule (ZMod 2) V) (hU : Offender.IsInvariant σ L U)
    (hU' : Offender.IsInvariant σ L (U.map (σ n : V →ₗ[ZMod 2] V))) :
    Nonempty (Representation.Equiv (srep σ L φ U hU)
      ((srep σ L φ (U.map (σ n : V →ₗ[ZMod 2] V)) hU').comp Φ)) := by
  refine ⟨Representation.Equiv.mk (LinearEquiv.submoduleMap (σ n) U) fun x => ?_⟩
  refine LinearMap.ext fun u => ?_
  apply Subtype.ext
  have h1 : ((((LinearEquiv.submoduleMap (σ n) U) ∘ₗ (srep σ L φ U hU x)) u :
      ↥(U.map (σ n : V →ₗ[ZMod 2] V))) : V) = σ n (σ ((φ x : ↥L) : N) (u : V)) := by
    simp [srep_apply]
  have h2 : (((srep σ L φ (U.map (σ n : V →ₗ[ZMod 2] V)) hU').comp Φ x ∘ₗ
      (LinearEquiv.submoduleMap (σ n) U)) u : V) =
      σ ((φ (Φ x) : ↥L) : N) (σ n (u : V)) := by
    simp [srep_apply]
  rw [h1, h2, ← hΦ x, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

theorem srep_isIrreducible (σ : N →* (V ≃ₗ[ZMod 2] V)) (L : Subgroup N) (φ : SL(3, F) →* ↥L)
    (hφ : Function.Surjective φ) (U : Submodule (ZMod 2) V) (hU : Offender.IsInvariant σ L U)
    (hs : IsLSimple σ L U) : (srep σ L φ U hU).IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  refine ⟨?_, fun S hS => ?_⟩
  · obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff U).1 hs.2.1
    exact ⟨⟨⟨u, hu⟩, 0, fun h => hu0 (congrArg Subtype.val h)⟩⟩
  · let W' : Submodule (ZMod 2) V := S.map U.subtype
    have hW' : Offender.IsInvariant σ L W' := by
      intro l hl w hw
      obtain ⟨x, hx⟩ := hφ ⟨l, hl⟩
      obtain ⟨u, hu, rfl⟩ := hw
      refine ⟨srep σ L φ U hU x u, hS x u hu, ?_⟩
      rw [Submodule.subtype_apply, srep_apply, hx]
      rfl
    have hle : W' ≤ U := by
      rintro w ⟨u, _, rfl⟩
      exact u.2
    rcases hs.2.2 W' hW' hle with h0 | h1
    · left
      refine eq_bot_iff.2 fun u hu => ?_
      have : (u : V) ∈ W' := ⟨u, hu, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact (Submodule.mem_bot _).2 (Subtype.ext this)
    · right
      refine eq_top_iff.2 fun u _ => ?_
      have hu : (u : V) ∈ W' := by rw [h1]; exact u.2
      obtain ⟨s, hs', hsu⟩ := hu
      have hsu' : s = u := Subtype.ext hsu
      rw [← hsu']
      exact hs'

end Srep

section Dual

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {N : Type} [Group N] {V : Type}
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem srep_dual_equiv {f : ℕ} (hf : 1 ≤ f) (hF : Fintype.card F = 2 ^ f)
    (σ : N →* (V ≃ₗ[ZMod 2] V)) (L : Subgroup N) (φ : SL(3, F) →* ↥L)
    (hφ : Function.Surjective φ) (n : N) (A : GL (Fin 3) F) (j : ℕ)
    (hn : ∀ x, n * ((φ x : ↥L) : N) * n⁻¹ = ((φ (graphFieldHom A j x) : ↥L) : N))
    (U : Submodule (ZMod 2) V) (hU : Offender.IsInvariant σ L U)
    (hU' : Offender.IsInvariant σ L (U.map (σ n : V →ₗ[ZMod 2] V)))
    (hs' : IsLSimple σ L (U.map (σ n : V →ₗ[ZMod 2] V))) :
    Nonempty (Representation.Equiv (srep σ L φ U hU)
      (srep σ L φ (U.map (σ n : V →ₗ[ZMod 2] V)) hU').dual) := by
  obtain ⟨e₁⟩ := srep_twist_equiv σ L φ n (graphFieldHom A j) hn U hU hU'
  obtain ⟨-, e₂⟩ := graphFieldTwistsDual f F hf hF _
    (srep σ L φ (U.map (σ n : V →ₗ[ZMod 2] V)) hU')
    (srep_isIrreducible σ L φ hφ _ hU' hs') A j
  obtain ⟨e₂⟩ := e₂
  exact ⟨e₁.trans e₂⟩

theorem srep_dual_equiv' {f : ℕ} (hf : 1 ≤ f) (hF : Fintype.card F = 2 ^ f)
    (σ : N →* (V ≃ₗ[ZMod 2] V)) (L : Subgroup N) (φ : SL(3, F) →* ↥L)
    (hφ : Function.Surjective φ) (n : N) (A : GL (Fin 3) F) (j : ℕ)
    (hn : ∀ x, n * ((φ x : ↥L) : N) * n⁻¹ = ((φ (graphFieldHom A j x) : ↥L) : N))
    (U U' : Submodule (ZMod 2) V) (hU : Offender.IsInvariant σ L U)
    (hU' : Offender.IsInvariant σ L U')
    (hUU' : U' = U.map (σ n : V →ₗ[ZMod 2] V)) (hs' : IsLSimple σ L U') :
    Nonempty (Representation.Equiv (srep σ L φ U hU) (srep σ L φ U' hU').dual) := by
  subst hUU'
  exact srep_dual_equiv hf hF σ L φ hφ n A j hn U hU hU' hs'

end Dual

section Kernel

variable {F : Type} [Field F] {N : Type} [Group N] {V : Type} [AddCommGroup V]
  [Module (ZMod 2) V]

theorem fix_iff_centralizer (σ : N →* (V ≃ₗ[ZMod 2] V)) (L : Subgroup N) [L.Normal]
    (hLq : CFSG.IsQuasisimple ↥L) {U : Submodule (ZMod 2) V} (hU : IsNontrivialLSimple σ L U)
    {a : N} (ha2 : a * a = 1) (haU : ∀ u ∈ U, σ a u ∈ U) :
    (∀ u ∈ U, σ a u = u) ↔ a ∈ Subgroup.centralizer (L : Set N) :=
  ⟨fun hfix => mem_centralizer_of_fix σ L hLq hU.1.1 hU.2 hfix,
    fun hc => fix_of_commute_involution L hU.1 ha2 hc haU⟩

theorem srep_ker_scalars (σ : N →* (V ≃ₗ[ZMod 2] V)) (L : Subgroup N) [L.Normal]
    (hLq : CFSG.IsQuasisimple ↥L) {φ : SL(3, F) →* ↥L} (hc : Cover φ)
    {U : Submodule (ZMod 2) V} (hU : IsNontrivialLSimple σ L U) (x : SL(3, F))
    (hx : srep σ L φ U hU.1.1 x = 1) : x ∈ scalars 3 F := by
  have hfix : ∀ u ∈ U, σ ((φ x : ↥L) : N) u = u := by
    intro u hu
    have := congrArg (fun T : Module.End (ZMod 2) ↥U => ((T ⟨u, hu⟩ : ↥U) : V)) hx
    simpa [srep_apply] using this
  have hcent := mem_centralizer_of_fix σ L hLq hU.1.1 hU.2 hfix
  refine (hc.mem_center_iff x).1 ?_
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hcent (g : N) g.2)

end Kernel

section Lift

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ} {N : Type} [Group N] {V : Type}
  [AddCommGroup V] [Module (ZMod 2) V]

omit [CharP F 2] in
theorem exists_lift_involution (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (σ : N →* (V ≃ₗ[ZMod 2] V)) (L : Subgroup N) [L.Normal] (hLq : CFSG.IsQuasisimple ↥L)
    {φ : SL(3, F) →* ↥L} (h : Cover φ) {a : N} (ha2 : a * a = 1)
    (hin : alphaP h a ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 F))
    (S : Submodule (ZMod 2) V → Prop)
    (hS : ∀ U, S U → IsLSimple σ L U ∧ ∀ u ∈ U, σ a u ∈ U) :
    ∃ s : SL(3, F), s * s = 1 ∧ ∀ U, S U → ∀ u ∈ U, σ a u = σ ((φ s : ↥L) : N) u := by
  have : Group.IsPerfect ↥L := hLq.1
  obtain ⟨s, hs2, hconj⟩ := exists_inner_involution h hF hf ha2 hin
  refine ⟨s, hs2, fun U hUS u hu => ?_⟩
  set c : N := ((φ s : ↥L) : N) with hc
  have hcL : c ∈ L := (φ s).2
  have hac : a * c = c * a := by
    have := hconj (φ s)
    rw [← hc] at this
    have h2 : a * c * a⁻¹ = c := by rw [this]; group
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hc2 : c * c = 1 := by
    rw [hc, ← Subgroup.coe_mul, ← map_mul, hs2, map_one]
    rfl
  set x : N := c⁻¹ * a with hx
  have hxc : x ∈ Subgroup.centralizer (L : Set N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h2 : a * l * a⁻¹ = c * l * c⁻¹ := hconj ⟨l, hl⟩
    have h3 : l * (c⁻¹ * a) = (c⁻¹ * a) * l := by
      calc l * (c⁻¹ * a) = c⁻¹ * (c * l * c⁻¹) * a := by group
        _ = c⁻¹ * (a * l * a⁻¹) * a := by rw [h2]
        _ = (c⁻¹ * a) * l := by group
    exact h3
  have hx2 : x * x = 1 := by
    have h1 : x * x = c⁻¹ * (c⁻¹ * (a * a)) := by
      rw [hx]
      calc c⁻¹ * a * (c⁻¹ * a) = c⁻¹ * (a * c⁻¹) * a := by group
        _ = c⁻¹ * (c⁻¹ * a) * a := by
          have : a * c⁻¹ = c⁻¹ * a := by
            calc a * c⁻¹ = c⁻¹ * (c * a) * c⁻¹ := by group
              _ = c⁻¹ * (a * c) * c⁻¹ := by rw [hac]
              _ = c⁻¹ * a := by group
          rw [this]
        _ = c⁻¹ * (c⁻¹ * (a * a)) := by group
    rw [h1, ha2, mul_one, ← mul_inv_rev, hc2, inv_one]
  obtain ⟨hsimple, hstab⟩ := hS U hUS
  have hxU : ∀ w ∈ U, σ x w ∈ U := by
    intro w hw
    have : σ x w = σ c⁻¹ (σ a w) := by rw [hx, map_mul]; rfl
    rw [this]
    exact hsimple.1 c⁻¹ (L.inv_mem hcL) _ (hstab w hw)
  have hfix := fix_of_commute_involution L hsimple hx2 hxc hxU
  have h1 : σ c⁻¹ (σ a u) = u := by
    have := hfix u hu
    rwa [hx, map_mul] at this
  calc σ a u = σ c (σ c⁻¹ (σ a u)) := by rw [ρ_apply_inv]
    _ = σ c u := by rw [h1]

end Lift

end CFSG.QuasithinUnique.Setup.X7Sec
