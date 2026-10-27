module

public import CFSG.Quasithin.Background.SmithCurtisBasic

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis

section NontrivialFactor

variable {F : Type} [Field F] {G : Type} [Group G]

theorem rep_trivial_of_commute {V : Type} [AddCommGroup V] [Module F V]
    (hperf : commutator G = ⊤) (ρ : Representation F G V)
    (hcomm : ∀ a b : G, ρ a * ρ b = ρ b * ρ a) (g : G) : ρ g = 1 := by
  let S : Subgroup G :=
    { carrier := {g | ρ g = 1}
      mul_mem' := fun {a b} ha hb => by
        show ρ (a * b) = 1
        rw [map_mul]; exact (by rw [show ρ a = 1 from ha, show ρ b = 1 from hb, mul_one])
      one_mem' := map_one ρ
      inv_mem' := fun {a} ha => by
        show ρ a⁻¹ = 1
        have h1 : ρ a⁻¹ * ρ a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        rwa [show ρ a = 1 from ha, mul_one] at h1 }
  have hle : commutator G ≤ S := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    show ρ (a * b * a⁻¹ * b⁻¹) = 1
    have h1 : ρ (a * b) = ρ (b * a) := by rw [map_mul, map_mul]; exact hcomm a b
    calc ρ (a * b * a⁻¹ * b⁻¹) = ρ ((a * b) * (a⁻¹ * b⁻¹)) := by rw [mul_assoc, mul_assoc]
      _ = ρ (a * b) * ρ (a⁻¹ * b⁻¹) := map_mul _ _ _
      _ = ρ (b * a) * ρ (a⁻¹ * b⁻¹) := by rw [h1]
      _ = ρ (b * a * (a⁻¹ * b⁻¹)) := (map_mul _ _ _).symm
      _ = 1 := by rw [show b * a * (a⁻¹ * b⁻¹) = 1 by group, map_one]
  have : g ∈ S := hle (by rw [hperf]; exact Subgroup.mem_top g)
  exact this

theorem exists_nontrivial_simple_subquotient (hperf : commutator G = ⊤) :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V]
      (ρ : Representation F G V), Module.finrank F V = n → (∃ (g : G) (v : V), ρ g v ≠ v) →
      ∃ (Q : Type) (_ : AddCommGroup Q) (_ : Module F Q) (_ : Module.Finite F Q)
        (σ : Representation F G Q), IsSimpleRep σ ∧ (∃ (g : G) (q : Q), σ g q ≠ q) ∧
          Module.finrank F Q ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ ρ hn hnt
  by_cases hs : IsSimpleRep ρ
  · exact ⟨V, inferInstance, inferInstance, inferInstance, ρ, hs, hnt, hn.le⟩
  have hVnt : Nontrivial V := by
    obtain ⟨g, v, hv⟩ := hnt
    exact ⟨⟨ρ g v, v, hv⟩⟩
  obtain ⟨W, hW, hW0, hWt⟩ : ∃ W : Submodule F V, (∀ g : G, ∀ w ∈ W, ρ g w ∈ W) ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by
    by_contra hcon
    push Not at hcon
    exact hs ⟨hVnt, fun W hW => by
      by_contra h
      push Not at h
      exact h.2 (hcon W hW h.1)⟩
  have hWpos : 0 < Module.finrank F W := Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 hW0)
  have hWlt : Module.finrank F W < n := hn ▸ Submodule.finrank_lt hWt
  by_cases ha : ∃ g, ∃ w ∈ W, ρ g w ≠ w
  · obtain ⟨g, w, hw, hgw⟩ := ha
    obtain ⟨Q, i1, i2, i3, σ, h1, h2, h3⟩ :=
      ih _ hWlt W (restrictRep ρ W hW) rfl ⟨g, ⟨w, hw⟩, fun h => hgw (congrArg Subtype.val h)⟩
    exact ⟨Q, i1, i2, i3, σ, h1, h2, h3.trans hWlt.le⟩
  push Not at ha
  by_cases hb : ∃ (g : G) (v : V), ρ g v - v ∉ W
  · obtain ⟨g, v, hgv⟩ := hb
    have hle : ∀ g : G, W ≤ W.comap (ρ g) := fun g w hw => hW g w hw
    have hqlt : Module.finrank F (V ⧸ W) < n := by
      have := Submodule.finrank_quotient_add_finrank W
      omega
    obtain ⟨Q, i1, i2, i3, σ, h1, h2, h3⟩ :=
      ih _ hqlt (V ⧸ W) (ρ.quotient W hle) rfl ⟨g, Submodule.Quotient.mk v, fun h => hgv (by
        exact (Submodule.Quotient.eq W).1 (by simpa using h))⟩
    exact ⟨Q, i1, i2, i3, σ, h1, h2, h3.trans hqlt.le⟩
  push Not at hb
  exfalso
  obtain ⟨g, v, hgv⟩ := hnt
  have hcomm : ∀ a b : G, ρ a * ρ b = ρ b * ρ a := by
    intro a b
    ext v
    have h1 : ρ a (ρ b v - v) = ρ b v - v := ha a _ (hb b v)
    have h2 : ρ b (ρ a v - v) = ρ a v - v := ha b _ (hb a v)
    rw [map_sub, sub_eq_iff_eq_add] at h1 h2
    rw [Module.End.mul_apply, Module.End.mul_apply, h1, h2]
    abel
  exact hgv (by rw [rep_trivial_of_commute hperf ρ hcomm g, Module.End.one_apply])

end NontrivialFactor

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
