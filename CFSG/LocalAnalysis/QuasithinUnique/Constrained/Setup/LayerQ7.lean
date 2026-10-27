module

public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerPlaneAux
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.QuasithinUnique
open scoped commutatorElement

universe v

section Generic

variable {X : Type*} [Group X]

theorem map_normalizerMonoidHom_subgroupOf {H : Subgroup X}
    (n : ↥(Subgroup.normalizer (H : Set X))) (K : Subgroup X) :
    (K.subgroupOf H).map (H.normalizerMonoidHom n).toMonoidHom =
      (conjSub (n : X) K).subgroupOf H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have e : ((H.normalizerMonoidHom n x : ↥H) : X) = (n : X) * (x : X) * (n : X)⁻¹ := by simp
    rw [Subgroup.mem_subgroupOf, mem_conjSub]
    show (n : X)⁻¹ * ((H.normalizerMonoidHom n x : ↥H) : X) * (n : X) ∈ K
    rw [e]
    have e2 : (n : X)⁻¹ * ((n : X) * (x : X) * (n : X)⁻¹) * (n : X) = (x : X) := by group
    rw [e2]
    exact Subgroup.mem_subgroupOf.1 hx
  · intro hy
    have hy' : (n : X)⁻¹ * (y : X) * (n : X) ∈ K := mem_conjSub.1 (Subgroup.mem_subgroupOf.1 hy)
    have hyH : (n : X)⁻¹ * (y : X) * (n : X) ∈ H := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (H : Set X)).inv_mem n.2)
        (y : X)).1 y.2
      simpa using this
    refine ⟨⟨_, hyH⟩, hy', ?_⟩
    apply Subtype.ext
    show (n : X) * ((n : X)⁻¹ * (y : X) * (n : X)) * (n : X)⁻¹ = y
    group

end Generic

section Orbit

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem isQuasisimple_of_isComponentIn {G L : Subgroup (V ≃ₗ[k] V)} (hL : IsComponentIn L G) :
    CFSG.IsQuasisimple ↥L :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1) hL.2.1

theorem isComponentIn_conjSub {G L : Subgroup (V ≃ₗ[k] V)} (hL : IsComponentIn L G)
    {a : V ≃ₗ[k] V} (ha : a ∈ Subgroup.normalizer (G : Set (V ≃ₗ[k] V))) :
    IsComponentIn (conjSub a L) G := by
  have hle : conjSub a L ≤ G := by
    intro x hx
    have hx' : a⁻¹ * x * a ∈ L := mem_conjSub.1 hx
    have := (Subgroup.mem_normalizer_iff.1 ha (a⁻¹ * x * a)).1 (hL.1 hx')
    simpa [mul_assoc] using this
  refine ⟨hle, ?_⟩
  have h := map_normalizerMonoidHom_subgroupOf (H := G) ⟨a, ha⟩ L
  rw [← h]
  exact CFSG.LocalCores.isComponent_map_mulEquiv (G.normalizerMonoidHom ⟨a, ha⟩) hL.2

theorem commutator_eq_bot_of_isComponentIn_ne [Finite V] {G X Y : Subgroup (V ≃ₗ[k] V)}
    (hX : IsComponentIn X G) (hY : IsComponentIn Y G) (hne : X ≠ Y) : ⁅X, Y⁆ = ⊥ := by
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  have hne' : X.subgroupOf G ≠ Y.subgroupOf G := fun h => hne (by
    have h1 := congrArg (Subgroup.map G.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hX.1, Subgroup.map_subgroupOf_eq_of_le hY.1] at h1)
  rcases CFSG.LocalCores.distinct_components_commute hX.2 hY.2 with h | h
  · exact absurd h hne'
  · refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun x hx => ?_
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h (show (⟨x, hX.1 hx⟩ : ↥G) ∈
      X.subgroupOf G from hx)
    have h2 := Subgroup.mem_centralizer_iff.1 h1 ⟨y, hY.1 hy⟩ (show (⟨y, hY.1 hy⟩ : ↥G) ∈
      Y.subgroupOf G from hy)
    exact congrArg Subtype.val h2

theorem exists_orbit_family [Finite V] {G A L : Subgroup (V ≃ₗ[k] V)}
    (hAG : A ≤ Subgroup.normalizer (G : Set (V ≃ₗ[k] V))) (hL : IsComponentIn L G)
    {a₀ : V ≃ₗ[k] V} (ha₀ : a₀ ∈ A) (hmove : conjSub a₀ L ≠ L) :
    ∃ (s : ℕ) (Lfam : Fin s → Subgroup (V ≃ₗ[k] V)), 2 ≤ s ∧ Function.Injective Lfam ∧
      (∀ i, IsComponentIn (Lfam i) G) ∧
      (∀ a ∈ A, ∀ i, ∃ j, conjSub a (Lfam i) = Lfam j) ∧
      (∀ i j, ∃ a ∈ A, conjSub a (Lfam i) = Lfam j) := by
  classical
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  let O : Set (Subgroup (V ≃ₗ[k] V)) := {X | ∃ a ∈ A, X = conjSub a L}
  have hOfin : Finite ↥O := inferInstance
  obtain ⟨s, e₀⟩ : ∃ s, Nonempty (↥O ≃ Fin s) := ⟨Nat.card ↥O, ⟨Finite.equivFin ↥O⟩⟩
  let e := e₀.some
  let Lfam : Fin s → Subgroup (V ≃ₗ[k] V) := fun i => (e.symm i).1
  have hmem : ∀ i, ∃ b ∈ A, Lfam i = conjSub b L := fun i => (e.symm i).2
  have hconjO : ∀ a ∈ A, ∀ i, conjSub a (Lfam i) ∈ O := by
    intro a ha i
    obtain ⟨b, hb, hbi⟩ := hmem i
    exact ⟨a * b, A.mul_mem ha hb, by rw [hbi, conjSub_mul]⟩
  have hLO : L ∈ O := ⟨1, A.one_mem, (conjSub_one L).symm⟩
  have hLO' : conjSub a₀ L ∈ O := ⟨a₀, ha₀, rfl⟩
  have hs : 2 ≤ s := by
    have hnt : Nontrivial ↥O := ⟨⟨⟨L, hLO⟩, ⟨conjSub a₀ L, hLO'⟩, fun h => hmove.symm
      (congrArg Subtype.val h)⟩⟩
    have h1 : 1 < Nat.card ↥O := Finite.one_lt_card_iff_nontrivial.2 hnt
    have h2 : Nat.card ↥O = s := by
      rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  refine ⟨s, Lfam, hs, fun i j h => e.symm.injective (Subtype.ext h), fun i => ?_, ?_, ?_⟩
  · obtain ⟨b, hb, hbi⟩ := hmem i
    rw [hbi]
    exact isComponentIn_conjSub hL (hAG hb)
  · intro a ha i
    refine ⟨e ⟨_, hconjO a ha i⟩, ?_⟩
    show conjSub a (Lfam i) = (e.symm (e ⟨_, hconjO a ha i⟩)).1
    rw [Equiv.symm_apply_apply]
  · intro i j
    obtain ⟨b, hb, hbi⟩ := hmem i
    obtain ⟨c, hc, hcj⟩ := hmem j
    refine ⟨c * b⁻¹, A.mul_mem hc (A.inv_mem hb), ?_⟩
    rw [hbi, hcj, ← conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]

end Orbit

end CFSG.QuasithinUnique.Setup.Layer
