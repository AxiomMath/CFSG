module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Quotient.QuotientAction
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralizerSemiregular
public import CFSG.LinearAlgebra.CoprimeActions.AbelianFixedFreeLinearCyclic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

open Quotient

variable {G : Type} [Group G] [Finite G]

theorem isCyclic_of_le_actor_of_coprime_card {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) (A : Subgroup G) (hAB : A ≤ B)
    (hcop : Nat.Coprime (Nat.card A) p) : IsCyclic A := by
  have hp : p.Prime := h.oddPrimeClassTwoAction.setting.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨h.oddPrimeClassTwoAction.setting.class_le_two⟩
  haveI : Fact (Monoid.exponent ↥P = p) := ⟨h.oddPrimeClassTwoAction.setting.exponent⟩
  have hB := h.oddPrimeClassTwoAction.setting.normB
  haveI : Nontrivial (Additive (Pbar P)) := by
    haveI := nontrivial_Pbar_of_extraspecial h.extraspecial
    infer_instance
  haveI : Finite (Additive (Pbar P)) := by
    haveI : Finite P := inferInstance
    haveI : Finite (Pbar P) := inferInstance
    exact inferInstanceAs (Finite (Pbar P))
  haveI : FiniteDimensional (ZMod p) (Additive (Pbar P)) := Module.Finite.of_finite
  haveI : IsMulCommutative A := by
    haveI := h.oddPrimeClassTwoAction.setting.abelian
    refine ⟨⟨fun a b => ?_⟩⟩
    have := IsMulCommutative.is_comm.comm (⟨a.1, hAB a.2⟩ : B) ⟨b.1, hAB b.2⟩
    exact Subtype.ext (by simpa using congrArg Subtype.val this)
  let σ : Representation (ZMod p) A (Additive (Pbar P)) :=
    { toFun := fun a => (action p hB (Subgroup.inclusion hAB a)).toLinearMap
      map_one' := by
        ext x
        show action p hB (Subgroup.inclusion hAB 1) x = x
        rw [map_one, map_one]; rfl
      map_mul' := by
        intro a b
        ext x
        show action p hB (Subgroup.inclusion hAB (a * b)) x =
          action p hB (Subgroup.inclusion hAB a) (action p hB (Subgroup.inclusion hAB b) x)
        rw [map_mul, map_mul]; rfl }
  have hσ : ∀ a : A, ∀ x, σ a x = action p hB ⟨a.1, hAB a.2⟩ x := fun a x => rfl
  refine CFSG.LinearAlgebra.CoprimeActions.AbelianFixedFreeLinearCyclic.isCyclic_of_fixedFree σ ?_
  intro a ha1 v hv
  have h9 := commutator_actorTwoCore_sup_actor_center_eq_bot h
  have hexp : Monoid.exponent ↥P = p := h.oddPrimeClassTwoAction.setting.exponent
  have hX : twoCoreCommutator T B ⊔ B ≤ Subgroup.centralizer (centerP P : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h9
  have haB : a.1 ∈ B := hAB a.2
  have hab' : a.1 ∈ (twoCoreCommutator T B ⊔ B : Subgroup G) := (le_sup_right : B ≤ twoCoreCommutator T B ⊔ B) haB
  have hbc : ∀ x ∈ centerP P, a.1 * x = x * a.1 := fun x hx => (hX hab' x hx).symm
  have hpow : ∀ x : G, x ∈ centerP P → x ^ p = 1 := by
    intro x hx
    have hxP : x ∈ P := by
      obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hx
      exact y.2
    have := Monoid.pow_exponent_eq_one (⟨x, hxP⟩ : ↥P)
    rw [hexp] at this
    exact congrArg Subtype.val this
  have hcop' : Nat.Coprime (orderOf a.1) p := by
    refine Nat.Coprime.coprime_dvd_left ?_ hcop
    have : orderOf a ∣ Nat.card A := orderOf_dvd_natCard _
    simpa using this
  have ha1' : a.1 ≠ 1 := fun h' => ha1 (Subtype.ext h')
  induction v using Additive.rec with | _ v => ?_
  induction v using QuotientGroup.induction_on with | _ x => ?_
  obtain ⟨g, hg⟩ := x
  rw [hσ, show (⟨a.1, hAB a.2⟩ : B) = ⟨a.1, haB⟩ from rfl,
    fixed_iff_commutator_mem_center hB ⟨a.1, haB⟩ hg] at hv
  have h1 := ProofSupport.CoprimeFixedCentralCoset.commutator_eq_one hp (centerP P) hpow a.1 g hbc
    hv hcop'
  have hcomm : g ∈ Subgroup.centralizer ({a.1} : Set G) := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have : a.1 * g = g * a.1 := by
      calc a.1 * g = (a.1 * g * a.1⁻¹ * g⁻¹) * g * a.1 := by group
        _ = g * a.1 := by rw [h1]; group
    exact this
  have hgc : g ∈ centerP P := by
    rw [← centralizer_nonidentity_actor_eq_center h a.1 haB ha1']
    exact ⟨hg, hcomm⟩
  obtain ⟨hgP, hgZ⟩ := mem_centerP.1 hgc
  have hgP' : hgP = hg := rfl
  have : (QuotientGroup.mk (⟨g, hg⟩ : P) : Pbar P) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hgZ
  rw [this]
  rfl

end Section5
end CFSG.LocalAnalysis.RankThreeUC
