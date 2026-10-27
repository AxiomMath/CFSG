module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Input
public import CFSG.LocalAnalysis.EvenSporadicStandard.StdKGroup
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutXbar

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.EvenSporadicStandard.M24Std
  CFSG.EvenSporadicStandard.M23Std

@[expose] def wreathS6Z2 : Subgroup (Equiv.Perm (Fin 2 × Fin 6)) where
  carrier := {σ | ∀ x y : Fin 2 × Fin 6, x.1 = y.1 ↔ (σ x).1 = (σ y).1}
  mul_mem' := by
    intro σ τ hσ hτ x y
    exact (hτ x y).trans (hσ (τ x) (τ y))
  one_mem' := fun _ _ => Iff.rfl
  inv_mem' := by
    intro σ hσ x y
    have := hσ (σ⁻¹ x) (σ⁻¹ y)
    simpa using this.symm

@[expose] def Fin77aProp21Outcome (G : Type) [Group G] (z : G) : Prop :=
  z ∈ fusionZStar G ∨
  (Nonempty (egaLayer G ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) ∧
    ∃ f : G →* Equiv.Perm (Fin 2 × Fin 6), Function.Injective f ∧ ∀ g, f g ∈ wreathS6Z2) ∨
  (LieModel (egaLayer G) .PSp 2 2 2 ∧ z ∉ egaLayer G ⊔ centralizer (egaLayer G : Set G) ∧
    Nonempty (↥(egaLayer G ⊓ centralizer ({z} : Set G)) ≃* Equiv.Perm (Fin 6))) ∨
  (Nonempty (egaLayer G ≃* alternatingGroup (Fin 8)) ∧
    z ∉ egaLayer G ⊔ centralizer (egaLayer G : Set G)) ∨
  (LieModel (egaLayer G) .PSU 4 2 1 ∧ z ∉ egaLayer G ⊔ centralizer (egaLayer G : Set G))

@[expose] def Fin77aProp21K : Prop :=
  ∀ (V : Type) [Group V], (∀ x y : V, x * y = y * x) → (∀ x : V, x * x = 1) →
    Nat.card V = 256 → ∀ (G : Type) [Group G] [Finite G], CFSG.SectionRank.IsKGroupCat G →
    ∀ (ρ : G →* MulAut V), Function.Injective ρ → ∀ z : G, orderOf z = 2 →
    Nonempty (↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)) →
    Fin77aProp21Outcome G z

variable {G : Type} [Group G]

@[expose] noncomputable def xbarAction (L1 : Subgroup G) : Xbar L1 →* MulAut ↥L1 :=
  QuotientGroup.lift ((centralizer (L1 : Set G)).subgroupOf (normalizer (L1 : Set G)))
    L1.normalizerMonoidHom (le_of_eq L1.normalizerMonoidHom_ker.symm)

theorem xbarAction_injective (L1 : Subgroup G) : Function.Injective (xbarAction L1) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have h : x ∈ L1.normalizerMonoidHom.ker := hq
  rw [L1.normalizerMonoidHom_ker] at h
  exact (QuotientGroup.eq_one_iff x).2 h

variable [Finite G] {L : Subgroup G} {z : G} {F L1 N : Subgroup G}

namespace OutSetup

variable (S : OutSetup L z F L1 N)

include S

theorem orderOf_zbar : orderOf (QuotientGroup.mk S.zX : Xbar L1) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two, ← QuotientGroup.mk_mul]
    have : S.zX * S.zX = 1 := Subtype.ext (by simpa using S.one.z_mul_self)
    rw [this, QuotientGroup.mk_one]
  · intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    have hLF : L1 ≤ F := fun x hx => S.L1_cz x hx (by
      have := (mem_centralizer_iff.1 h x hx).symm
      rwa [S.coe_zX] at this)
    have h1 := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hLF)
    rw [S.L1_card, S.one.F_card] at h1
    omega

theorem isKGroupCat_xbar (h : StdHyp G L) : CFSG.SectionRank.IsKGroupCat (Xbar L1) := by
  have hne : L1 ≠ ⊥ := fun h0 => by
    have := S.L1_card
    rw [h0, Subgroup.card_bot] at this
    omega
  exact (h.isKGroupCat_normalizer hne S.L1_comm).quotient _

theorem prop21_outcome (hP : Fin77aProp21K) (hK : CFSG.SectionRank.IsKGroupCat (Xbar L1))
    (hC : Nonempty (centralizer ({(QuotientGroup.mk S.zX : Xbar L1)} : Set (Xbar L1)) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))) :
    Fin77aProp21Outcome (Xbar L1) (QuotientGroup.mk S.zX) :=
  hP ↥L1 (fun x y => Subtype.ext (S.L1_comm x x.2 y y.2)) (fun x => Subtype.ext (S.L1_sq x x.2))
    S.L1_card (Xbar L1) hK (xbarAction L1) (xbarAction_injective L1) _ S.orderOf_zbar hC

end OutSetup

end CFSG.EvenSporadicStandard.M22Std
