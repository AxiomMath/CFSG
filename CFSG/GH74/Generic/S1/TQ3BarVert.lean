module

public import CFSG.GH74.Generic.S1.LayerPair
public import CFSG.GH74.Generic.S1.QuatRank

public section

open Subgroup CFSG CFSG.GH74 CFSG.Assembly.LowTwoRank CFSG.GH74.Filter.ClassicalOdd CFSG.LocalCores
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.Generic.S1

@[expose] def KL3Table : Prop :=
  ∀ (M : Type) [Group M] [Finite M], IsQuasisimple M → GHList (M ⧸ center M) →
    ∀ (F : Type) [Field F] [Finite F], Nat.card F = 3 →
      ∀ P : Subgroup M, Nonempty (↥P ≃* SL(3, F)) → ∀ y ∈ P, orderOf y = 2 →
        Group.IsSolvable ↥(centralizer ({y} : Set M)) →
          P = ⊤ ∨
            ((∀ α : MulAut M, Odd (orderOf α) → (∀ p ∈ P, α p = p) → α = 1) ∧
              ∃ E : Subgroup (M ⧸ center M), CFSG.Open.IsElemAbelian 2 E ∧ 4 < Nat.card E)

theorem isSolvable_of_forall_perfect {X : Type*} [Group X] [Finite X]
    (h : ∀ Q : Subgroup X, ⁅Q, Q⁆ = Q → Q = ⊥) : Group.IsSolvable X := by
  classical
  obtain ⟨_, ⟨m, rfl⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup X))
    (Set.range (derivedSeries X)) ⟨derivedSeries X 0, 0, rfl⟩
  have hperf : ⁅derivedSeries X m, derivedSeries X m⁆ = derivedSeries X m := by
    have hle : derivedSeries X (m + 1) ≤ derivedSeries X m := by
      rw [derivedSeries_succ]
      exact Subgroup.commutator_le_self _
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact absurd hlt (hmin _ ⟨m + 1, rfl⟩)
    · rw [← derivedSeries_succ]
      exact heq
  exact (Group.isSolvable_def X).2 ⟨m, h _ hperf⟩

section Vertical

variable {H : Type} [Group H] [Finite H]

theorem vertical_case (hH : Gen4 H) (hK : KL3Table) {F : Type} [Field F] [Finite F]
    (hF3 : Nat.card F = 3) {M A' J' : Subgroup H} (hM : IsComponent M)
    (hGH : GHList (↥M ⧸ center ↥M)) (hAM : A' ≤ M) (hAq : IsQuasisimple ↥A')
    (hAe : Nonempty (↥A' ≃* SL(3, F))) {y : H} (hyA : y ∈ A') (hy2 : orderOf y = 2)
    (hsolv : ∀ P : Subgroup H, P ≤ centralizer ({y} : Set H) → ⁅P, P⁆ = P → P = ⊥)
    (hJodd : OddGenerated J') (hJA : ∀ a ∈ A', ∀ j ∈ J', a * j = j * a)
    (φ : Q8 →* H) (hφ : Function.Injective φ) (hφJ : ∀ g, φ g ∈ J') : A' = M := by
  obtain ⟨eA⟩ := hAe
  have hMq : IsQuasisimple ↥M := hM.1
  set P : Subgroup ↥M := A'.subgroupOf M with hP
  have hPe : Nonempty (↥P ≃* SL(3, F)) := ⟨(Subgroup.subgroupOfEquivOfLe hAM).trans eA⟩
  set yM : ↥M := ⟨y, hAM hyA⟩ with hyM
  have hyP : yM ∈ P := hyA
  have hyM2 : orderOf yM = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hy2
  have hsolvM : Group.IsSolvable ↥(centralizer ({yM} : Set ↥M)) := by
    apply isSolvable_of_forall_perfect
    intro Q hQ
    set Q' : Subgroup H := (Q.map (centralizer ({yM} : Set ↥M)).subtype).map M.subtype with hQ'
    have hQ'perf : ⁅Q', Q'⁆ = Q' := by
      rw [hQ', ← Subgroup.map_commutator, ← Subgroup.map_commutator, hQ]
    have hQ'le : Q' ≤ centralizer ({y} : Set H) := by
      rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.1 q.2
      exact congrArg Subtype.val this
    have hbot := hsolv Q' hQ'le hQ'perf
    rw [eq_bot_iff]
    intro q hq
    have : ((q : ↥(centralizer ({yM} : Set ↥M))) : ↥M).1 ∈ Q' :=
      ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    have h1 : ((q : ↥(centralizer ({yM} : Set ↥M))) : ↥M) = 1 := Subtype.ext this
    have h2 : q = 1 := Subtype.ext h1
    rw [h2]
    exact Subgroup.one_mem _
  rcases hK ↥M hMq hGH F hF3 P hPe yM hyP hyM2 hsolvM with hP' | ⟨hAut, E, hE, hcard⟩
  · apply le_antisymm hAM
    intro m hm
    have : (⟨m, hm⟩ : ↥M) ∈ P := by rw [hP']; trivial
    exact this
  · exfalso
    have hconjmem : ∀ (g : H) (K : Subgroup H) (x : H),
        x ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ K := fun g K x => by
      constructor
      · rintro ⟨a, ha, rfl⟩
        simpa [MulAut.conj_apply, mul_assoc] using ha
      · intro h
        exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩
    have hMnorm : ∀ g ∈ J', g ∈ normalizer (M : Set H) := by
      intro g hg
      have hM' : IsComponent (M.map (MulAut.conj g).toMonoidHom) :=
        CFSG.LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent (MulAut.conj g) hM
      rcases distinct_components_commute hM hM' with h | h
      · rw [Subgroup.mem_normalizer_iff]
        intro x
        have hz : ∀ z, z ∈ M ↔ g⁻¹ * z * g ∈ M := fun z => by
          rw [← hconjmem]
          rw [← h]
        have := hz (g * x * g⁻¹)
        rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
        exact this.symm
      · exfalso
        refine quasisimple_not_commutative hAq (fun a b => ?_)
        have hbM' : (b : H) ∈ M.map (MulAut.conj g).toMonoidHom := by
          rw [hconjmem]
          have hc := hJA b b.2 g hg
          rw [show g⁻¹ * (b : H) * g = b by
            calc g⁻¹ * (b : H) * g = g⁻¹ * (g * b) := by rw [← hc]; group
              _ = b := by group]
          exact hAM b.2
        have h1 := Subgroup.commutator_mem_commutator (hAM a.2) hbM'
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact Subtype.ext h1
    have hOddC : ∀ g ∈ J', Odd (orderOf g) → ∀ m ∈ M, g * m = m * g := by
      intro g hg hgo m hm
      have hgN := hMnorm g hg
      set α : MulAut ↥M := M.normalizerMonoidHom ⟨g, hgN⟩ with hα
      have hαodd : Odd (orderOf α) := by
        refine Odd.of_dvd_nat hgo ?_
        calc orderOf α ∣ orderOf (⟨g, hgN⟩ : ↥(normalizer (M : Set H))) := orderOf_map_dvd _ _
          _ = orderOf g := Subgroup.orderOf_mk _ _
      have hαP : ∀ p ∈ P, α p = p := by
        intro p hp
        apply Subtype.ext
        have hpA : (p : H) ∈ A' := hp
        have hc := hJA p hpA g hg
        show g * (p : H) * g⁻¹ = p
        rw [← hc]
        group
      have hα1 := hAut α hαodd hαP
      have h2 := congrArg (fun β : MulAut ↥M => ((β ⟨m, hm⟩ : ↥M) : H)) hα1
      have h3 : g * m * g⁻¹ = m := h2
      calc g * m = g * m * g⁻¹ * g := by group
        _ = m * g := by rw [h3]
    have hJC : J' ≤ centralizer (M : Set H) := by
      rw [← hJodd]
      refine (Subgroup.closure_le _).2 fun g hg => ?_
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro m hm
      exact (hOddC g hg.1 hg.2 m hm).symm
    have hcent : ∀ a : Q8, ∀ m ∈ M, φ a * m = m * φ a := fun a m hm =>
      (Subgroup.mem_centralizer_iff.1 (hJC (hφJ a)) m hm).symm
    have := card_le_four_of_quaternion_centralizer hH φ hφ hcent E hE
    omega

end Vertical

end CFSG.GH74.Generic.S1
