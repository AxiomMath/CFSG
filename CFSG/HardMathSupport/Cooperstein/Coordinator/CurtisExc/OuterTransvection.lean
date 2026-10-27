module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.OuterTransvectionCore
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.OffenderUnits
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorBinary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor

theorem natCard_ker_opA_eq_fix {W : Type} [CommGroup W] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] (θ : W ≃* Multiplicative V) (x : MulAut W) :
    Nat.card {w : W // x w = w} = Nat.card ↥(LinearMap.ker (opA (binUnits θ x))) := by
  refine Nat.card_congr ((θ.toEquiv.trans Multiplicative.toAdd).subtypeEquiv fun w => ?_)
  have e : (binUnits θ x).val (Multiplicative.toAdd (θ w)) = Multiplicative.toAdd (θ (x w)) := by
    rw [binUnits_val]; simp
  show x w = w ↔ opA (binUnits θ x) (Multiplicative.toAdd (θ w)) = 0
  rw [opA_apply, e]
  constructor
  · intro h
    rw [h]
    exact vec_add_self _
  · intro h
    have h' : Multiplicative.toAdd (θ (x w)) = Multiplicative.toAdd (θ w) := by
      have := congrArg (fun y => y + Multiplicative.toAdd (θ w)) h
      simpa [add_assoc, vec_add_self] using this
    exact θ.injective (Multiplicative.toAdd.injective h')


theorem finrank_range_of_card {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (f : Module.End (ZMod 2) V) {d : ℕ} (hd : Nat.card V = 2 ^ d) (k : ℕ)
    (hk : Nat.card ↥(LinearMap.ker f) = 2 ^ k) :
    Module.finrank (ZMod 2) ↥(LinearMap.range f) + k = d := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have hcV : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod]
  have hck : Nat.card ↥(LinearMap.ker f) = 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.ker f) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(LinearMap.ker f)), Nat.card_zmod]
  have e1 : Module.finrank (ZMod 2) V = d :=
    Nat.pow_right_injective (le_refl 2) (hcV.symm.trans hd)
  have e2 : Module.finrank (ZMod 2) ↥(LinearMap.ker f) = k :=
    Nat.pow_right_injective (le_refl 2) (hck.symm.trans hk)
  omega

theorem conj_eq_iff {M : Type*} [Group M] (b x y : M) :
    x * b * x⁻¹ = y * b * y⁻¹ ↔ b * (x⁻¹ * y) = (x⁻¹ * y) * b := by
  constructor
  · intro h
    calc b * (x⁻¹ * y) = x⁻¹ * (x * b * x⁻¹) * y := by group
      _ = x⁻¹ * (y * b * y⁻¹) * y := by rw [h]
      _ = (x⁻¹ * y) * b := by group
  · intro h
    calc x * b * x⁻¹ = x * (b * (x⁻¹ * y)) * y⁻¹ * x⁻¹ * x * x⁻¹ * x⁻¹⁻¹ * 1 := by group
      _ = x * ((x⁻¹ * y) * b) * y⁻¹ * x⁻¹ * x * x⁻¹ * x⁻¹⁻¹ * 1 := by rw [h]
      _ = y * b * y⁻¹ := by group

theorem card_tvClass_eq_index {W : Type} [CommGroup W] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] (θ : W ≃* Multiplicative V) (L : Subgroup (MulAut W)) (b : MulAut W) :
    Nat.card ↥(tvClass (L.map (binUnits θ).toMonoidHom) (binUnits θ b)) =
      ((Subgroup.centralizer {b}).subgroupOf L).index := by
  set Ψ := binUnits θ with hΨ
  let C : Subgroup ↥L := (Subgroup.centralizer {b}).subgroupOf L
  let F : ↥L → ↥(tvClass (L.map Ψ.toMonoidHom) (Ψ b)) := fun g =>
    ⟨Ψ g.1 * Ψ b * (Ψ g.1)⁻¹, ⟨Ψ g.1, ⟨g.1, g.2, rfl⟩, rfl⟩⟩
  have hFeq : ∀ x y : ↥L, F x = F y ↔ x⁻¹ * y ∈ C := by
    intro x y
    rw [Subtype.ext_iff]
    show Ψ x.1 * Ψ b * (Ψ x.1)⁻¹ = Ψ y.1 * Ψ b * (Ψ y.1)⁻¹ ↔ _
    have h1 : ∀ z : MulAut W, Ψ z * Ψ b * (Ψ z)⁻¹ = Ψ (z * b * z⁻¹) := fun z => by simp
    rw [h1, h1, Ψ.injective.eq_iff, conj_eq_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h h' hh'
      rw [Set.mem_singleton_iff.1 hh']
      exact h
    · intro h
      exact h b (Set.mem_singleton b)
  have hsurj : Function.Surjective F := by
    rintro ⟨_, g', ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  have hwd : ∀ x y : ↥L, QuotientGroup.leftRel C x y → F x = F y := fun x y h =>
    (hFeq x y).2 ((QuotientGroup.leftRel_apply).1 h)
  let G : (↥L ⧸ C) → ↥(tvClass (L.map Ψ.toMonoidHom) (Ψ b)) := Quotient.lift F hwd
  have hG : Function.Bijective G := by
    refine ⟨?_, ?_⟩
    · intro x y
      induction x using Quotient.inductionOn
      induction y using Quotient.inductionOn
      intro h
      exact Quotient.sound ((QuotientGroup.leftRel_apply).2 ((hFeq _ _).1 h))
    · intro t
      obtain ⟨g, rfl⟩ := hsurj t
      exact ⟨(g : ↥L ⧸ C), rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective G hG)).symm


theorem no_outer_transvection
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)} (hirr : X1.IsIrrOn L)
    {b : MulAut W} (hbN : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1)
    (hbtv : Nat.card W = 2 * Nat.card {w : W // b w = w})
    (hinv : ∀ x ∈ L, x ≠ 1 → x * x = 1 → 2 ^ 5 * Nat.card {w : W // x w = w} ≤ Nat.card W)
    {d : ℕ} (hd : Nat.card W = 2 ^ d) :
    Odd (((Subgroup.centralizer {b}).subgroupOf L).index) ∧
    d ≤ ((Subgroup.centralizer {b}).subgroupOf L).index ∧
    ((Subgroup.centralizer {b}).subgroupOf L).index ≤ d + 1 := by
  classical
  obtain ⟨V, _, _, _, ⟨θ⟩⟩ := Layer.Actor.exists_binModel_of_binary hW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWn : Nontrivial W := hirr.1
  have hVfin : Finite V := Finite.of_equiv W (θ.toEquiv.trans Multiplicative.toAdd)
  have hcardV : Nat.card V = 2 ^ d := (natCard_eq θ).symm.trans hd
  set Ψ : MulAut W ≃* (Module.End (ZMod 2) V)ˣ := binUnits θ with hΨ
  set L' : Subgroup (Module.End (ZMod 2) V)ˣ := L.map Ψ.toMonoidHom with hL'
  have e : ∀ (x : MulAut W) (w : W),
      (Ψ x).val (Multiplicative.toAdd (θ w)) = Multiplicative.toAdd (θ (x w)) := by
    intro x w; rw [hΨ, binUnits_val]; simp
  have hirr' : ∀ U : Submodule (ZMod 2) V, (∀ g ∈ L', ∀ u ∈ U, g.val u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    set U₀ : Subgroup W :=
      { carrier := {x | Multiplicative.toAdd (θ x) ∈ U}
        one_mem' := by simp
        mul_mem' := fun {x y} hx hy => by
          have : Multiplicative.toAdd (θ (x * y)) =
              Multiplicative.toAdd (θ x) + Multiplicative.toAdd (θ y) := by simp
          show Multiplicative.toAdd (θ (x * y)) ∈ U
          rw [this]; exact U.add_mem hx hy
        inv_mem' := fun {x} hx => by
          have : Multiplicative.toAdd (θ x⁻¹) = - Multiplicative.toAdd (θ x) := by simp
          show Multiplicative.toAdd (θ x⁻¹) ∈ U
          rw [this]; exact U.neg_mem hx } with hU₀
    have hU₀inv : ∀ g ∈ L, ∀ u ∈ U₀, g u ∈ U₀ := by
      intro g hg u hu
      have h1 := hU (Ψ g) ⟨g, hg, rfl⟩ (Multiplicative.toAdd (θ u)) hu
      show Multiplicative.toAdd (θ (g u)) ∈ U
      rwa [e] at h1
    rcases hirr.2 U₀ hU₀inv with h0 | h0
    · left
      rw [eq_bot_iff]
      intro w hw
      have hx : θ.symm (Multiplicative.ofAdd w) ∈ U₀ := by
        show Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd w))) ∈ U
        simpa using hw
      rw [h0, Subgroup.mem_bot] at hx
      rw [Submodule.mem_bot]
      have := congrArg (fun x => Multiplicative.toAdd (θ x)) hx
      simpa using this
    · right
      rw [eq_top_iff]
      intro w _
      have hx : θ.symm (Multiplicative.ofAdd w) ∈ U₀ := by rw [h0]; exact Subgroup.mem_top _
      have hx' : Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd w))) ∈ U := hx
      simpa using hx'
  have hbN' : ∀ g ∈ L', Ψ b * g * (Ψ b)⁻¹ ∈ L' := by
    rintro _ ⟨g0, hg0, rfl⟩
    refine ⟨b * g0 * b⁻¹, ((Subgroup.mem_normalizer_iff.mp hbN) g0).1 hg0, ?_⟩
    simp
  have hb2' : Ψ b * Ψ b = 1 := by rw [← map_mul, hb2, map_one]
  have hrk : ∀ x : MulAut W, ∀ k, Nat.card {w : W // x w = w} = 2 ^ k →
      Module.finrank (ZMod 2) ↥(LinearMap.range (opA (Ψ x))) + k = d := by
    intro x k hk
    refine finrank_range_of_card (opA (Ψ x)) hcardV k ?_
    rw [← natCard_ker_opA_eq_fix θ x]
    exact hk
  have hexp : ∀ x : MulAut W, ∃ k, Nat.card {w : W // x w = w} = 2 ^ k := by
    intro x
    have h1 := natCard_ker_opA_eq_fix θ x
    have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
    refine ⟨Module.finrank (ZMod 2) ↥(LinearMap.ker (opA (Ψ x))), ?_⟩
    rw [h1, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(LinearMap.ker (opA (Ψ x)))),
      Nat.card_zmod]
  have hbr : Module.finrank (ZMod 2) ↥(LinearMap.range (opA (Ψ b))) = 1 := by
    obtain ⟨k, hk⟩ := hexp b
    have := hrk b k hk
    rw [hk, hd] at hbtv
    have h1 : d = k + 1 :=
      Nat.pow_right_injective (le_refl 2) (by show 2 ^ d = 2 ^ (k + 1); rw [hbtv, pow_succ'])
    omega
  have hrank : ∀ x ∈ L', x ≠ 1 → x * x = 1 →
      5 ≤ Module.finrank (ZMod 2) ↥(LinearMap.range (opA x)) := by
    rintro _ ⟨x, hx, rfl⟩ hne hsq
    have hx1 : x ≠ 1 := fun h => hne (by rw [h, map_one])
    have hxx : x * x = 1 := Ψ.injective (by rw [map_mul, map_one]; exact hsq)
    obtain ⟨k, hk⟩ := hexp x
    have h1 := hinv x hx hx1 hxx
    rw [hk, hd, ← pow_add] at h1
    have h2 : 5 + k ≤ d := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
    have := hrk x k hk
    show 5 ≤ Module.finrank (ZMod 2) ↥(LinearMap.range (opA (Ψ x)))
    omega
  have hfr : Module.finrank (ZMod 2) V = d := by
    have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
    have hcV : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod]
    exact Nat.pow_right_injective (le_refl 2) (hcV.symm.trans hcardV)
  obtain ⟨c1, c2, c3⟩ := outer_transvection_core hirr' hbN' hb2' hbr hrank
  rw [card_tvClass_eq_index θ L b] at c1 c2 c3
  rw [hfr] at c2 c3
  exact ⟨c1, c2, c3⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
