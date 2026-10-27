module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6KProd
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6Split

public section

open scoped commutatorElement

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

section Generic

variable {G : Type*} [Group G]

theorem le_of_perfect_le_sup_of_comm {A B X : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hinf : A ⊓ B = ⊥) (hX : ⁅X, X⁆ = X) (hXAB : X ≤ A ⊔ B) : X ≤ B := by
  refine hX.symm.le.trans (Subgroup.commutator_le.2 fun x hx y hy => ?_)
  set x' : ↥(A ⊔ B) := ⟨x, hXAB hx⟩ with hx'
  set y' : ↥(A ⊔ B) := ⟨y, hXAB hy⟩ with hy'
  have h1 : KProd.projA A B hAB hinf ⁅x', y'⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subtype.ext (hAA _ (KProd.projA A B hAB hinf x').2 _ (KProd.projA A B hAB hinf y').2))
  have h2 := (KProd.projA_eq_one_iff A B hAB hinf ⁅x', y'⁆).1 h1
  have h3 : ((⁅x', y'⁆ : ↥(A ⊔ B)) : G) = ⁅x, y⁆ := by
    simp [commutatorElement_def, hx', hy']
  rwa [h3] at h2

theorem commutator_le_centralizer_of_stable {N P I : Subgroup G}
    (hII : ∀ i ∈ I, ∀ i' ∈ I, i * i' = i' * i)
    (hIc : ∀ g ∈ N, ∀ i ∈ I, g * i = i * g)
    (hNP : ∀ g ∈ N, ∀ p ∈ P, g * p * g⁻¹ ∈ P)
    (hst : ∀ g ∈ N, ∀ p ∈ P, g * p * g⁻¹ * p⁻¹ ∈ I) :
    ⁅N, N⁆ ≤ centralizer (P : Set G) := by
  refine Subgroup.commutator_le.2 fun g hg h hh => ?_
  have key : ∀ p ∈ P, g * h * p * (g * h)⁻¹ = h * g * p * (h * g)⁻¹ := by
    intro p hp
    have e1 : h * p * h⁻¹ = (h * p * h⁻¹ * p⁻¹) * p := by group
    have e2 : g * p * g⁻¹ = (g * p * g⁻¹ * p⁻¹) * p := by group
    have e3 : g * (h * p * h⁻¹) * g⁻¹ =
        (g * (h * p * h⁻¹ * p⁻¹) * g⁻¹) * (g * p * g⁻¹) := by group
    have e4 : h * (g * p * g⁻¹) * h⁻¹ =
        (h * (g * p * g⁻¹ * p⁻¹) * h⁻¹) * (h * p * h⁻¹) := by group
    have hc1 : g * (h * p * h⁻¹ * p⁻¹) * g⁻¹ = h * p * h⁻¹ * p⁻¹ := by
      have := hIc g hg _ (hst h hh p hp)
      calc g * (h * p * h⁻¹ * p⁻¹) * g⁻¹ = (g * (h * p * h⁻¹ * p⁻¹)) * g⁻¹ := rfl
        _ = ((h * p * h⁻¹ * p⁻¹) * g) * g⁻¹ := by rw [this]
        _ = h * p * h⁻¹ * p⁻¹ := by group
    have hc2 : h * (g * p * g⁻¹ * p⁻¹) * h⁻¹ = g * p * g⁻¹ * p⁻¹ := by
      have := hIc h hh _ (hst g hg p hp)
      calc h * (g * p * g⁻¹ * p⁻¹) * h⁻¹ = (h * (g * p * g⁻¹ * p⁻¹)) * h⁻¹ := rfl
        _ = ((g * p * g⁻¹ * p⁻¹) * h) * h⁻¹ := by rw [this]
        _ = g * p * g⁻¹ * p⁻¹ := by group
    have hcomm := hII _ (hst h hh p hp) _ (hst g hg p hp)
    calc g * h * p * (g * h)⁻¹ = g * (h * p * h⁻¹) * g⁻¹ := by group
      _ = (g * (h * p * h⁻¹ * p⁻¹) * g⁻¹) * (g * p * g⁻¹) := e3
      _ = (h * p * h⁻¹ * p⁻¹) * ((g * p * g⁻¹ * p⁻¹) * p) := by rw [hc1]; group
      _ = ((h * p * h⁻¹ * p⁻¹) * (g * p * g⁻¹ * p⁻¹)) * p := by group
      _ = ((g * p * g⁻¹ * p⁻¹) * (h * p * h⁻¹ * p⁻¹)) * p := by rw [hcomm]
      _ = (g * p * g⁻¹ * p⁻¹) * ((h * p * h⁻¹ * p⁻¹) * p) := by group
      _ = (h * (g * p * g⁻¹ * p⁻¹) * h⁻¹) * (h * p * h⁻¹) := by rw [hc2]; group
      _ = h * (g * p * g⁻¹) * h⁻¹ := e4.symm
      _ = h * g * p * (h * g)⁻¹ := by group
  rw [mem_centralizer_iff]
  intro p hp
  have hw : (h * g)⁻¹ ∈ N := N.inv_mem (N.mul_mem hh hg)
  have hq : (h * g)⁻¹ * p * ((h * g)⁻¹)⁻¹ ∈ P := hNP _ hw p hp
  have := key _ hq
  have e : g * h * ((h * g)⁻¹ * p * ((h * g)⁻¹)⁻¹) * (g * h)⁻¹ = ⁅g, h⁆ * p * ⁅g, h⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  have e' : h * g * ((h * g)⁻¹ * p * ((h * g)⁻¹)⁻¹) * (h * g)⁻¹ = p := by group
  rw [e, e'] at this
  calc p * ⁅g, h⁆ = (⁅g, h⁆ * p * ⁅g, h⁆⁻¹) * ⁅g, h⁆ := by rw [this]
    _ = ⁅g, h⁆ * p := by group

end Generic

namespace ModSplit

section Perfect

variable {V : Type*} [Group V] [Finite V] {Γ : Type*} [Group Γ] [Finite Γ] (ρ : Γ →* MulAut V)

theorem le_closure_commAct_of_fix_trivial (hcomm : ∀ a b : V, a * b = b * a)
    {k : Type*} [Field k] [Finite k] [CharP k 2] (hk : Nat.card k = 2 ^ 2)
    (X : Subgroup Γ) (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) k) (hperf : ⁅X, X⁆ = X)
    (V₀ : Subgroup V) (hV₀ : ∀ g ∈ X, ∀ v ∈ V₀, ρ g v ∈ V₀) (hcard : Nat.card V₀ = 2 ^ 4)
    (hfix : ∀ v ∈ V₀, (∀ g ∈ X, ρ g v = v) → v = 1) :
    V₀ ≤ Subgroup.closure {x : V | ∃ g ∈ X, ∃ w ∈ V₀, x = ρ g w * w⁻¹} := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup V := Subgroup.closure {x : V | ∃ g ∈ X, ∃ w ∈ V₀, x = ρ g w * w⁻¹} with hW
  have hgenV₀ : ∀ g ∈ X, ∀ w ∈ V₀, ρ g w * w⁻¹ ∈ V₀ := fun g hg w hw =>
    V₀.mul_mem (hV₀ g hg w hw) (V₀.inv_mem hw)
  have hWV₀ : W ≤ V₀ := (Subgroup.closure_le V₀).2 (by
    rintro x ⟨g, hg, w, hw, rfl⟩
    exact hgenV₀ g hg w hw)
  have hWinv : ∀ g ∈ X, ∀ z ∈ W, ρ g z ∈ W := by
    intro g hg z hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g', hg', w, hw, rfl⟩ := hx
      refine Subgroup.subset_closure ⟨g * g' * g⁻¹,
        X.mul_mem (X.mul_mem hg hg') (X.inv_mem hg), ρ g w, hV₀ g hg w hw, ?_⟩
      rw [map_mul, map_inv, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply,
        ρ_inv_apply_self]
    | one => rw [map_one]; exact W.one_mem
    | mul x y _ _ hx hy => rw [map_mul]; exact W.mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact W.inv_mem hx
  by_contra hne
  have hWne : W ≠ V₀ := fun heq => hne (le_of_eq heq.symm)
  have hcardW : Nat.card W < 2 ^ 4 := by
    by_contra hge
    push Not at hge
    exact hWne (Subgroup.eq_of_le_of_card_ge hWV₀ (by rw [hcard]; exact hge))
  obtain ⟨j, hj, hjW⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hcard ▸ Subgroup.card_dvd_of_le hWV₀ : Nat.card W ∣ 2 ^ 4)
  have hj4 : j < 4 := by
    by_contra hge
    push Not at hge
    have : j = 4 := le_antisymm hj hge
    rw [this] at hjW
    omega
  have hρW := Common.sl2_eq_one_of_card_lt (k := k) (m := 2) (d := j) e hk (le_refl 2)
    (restrictAct ρ X W hWinv) hjW (by omega)
  have hWfix : ∀ g ∈ X, ∀ z ∈ W, ρ g z = z := by
    intro g hg z hz
    have h3 := congrArg (fun f : X →* MulAut ↥W => ((f ⟨g, hg⟩ ⟨z, hz⟩ : ↥W) : V)) hρW
    have h4 : ((restrictAct ρ X W hWinv ⟨g, hg⟩ ⟨z, hz⟩ : ↥W) : V) = ρ g z := rfl
    have h5 : (((1 : X →* MulAut ↥W) ⟨g, hg⟩ ⟨z, hz⟩ : ↥W) : V) = z := rfl
    rw [h4, h5] at h3
    exact h3
  have hhom : ∀ v ∈ V₀, ∃ φ : ↥X →* V, ∀ g : ↥X, φ g = ρ (g : Γ) v * v⁻¹ := by
    intro v hv
    refine ⟨MonoidHom.mk' (fun g : ↥X => ρ (g : Γ) v * v⁻¹) fun a b => ?_, fun g => rfl⟩
    have hb : ρ (b : Γ) v * v⁻¹ ∈ W := Subgroup.subset_closure ⟨b, b.2, v, hv, rfl⟩
    have hfixb := hWfix a a.2 _ hb
    have hab : ρ ((a * b : ↥X) : Γ) v = (ρ (b : Γ) v * v⁻¹) * ρ (a : Γ) v := by
      rw [Subgroup.coe_mul, map_mul, MulAut.mul_apply]
      conv_lhs => rw [show ρ (b : Γ) v = (ρ (b : Γ) v * v⁻¹) * v by group]
      rw [map_mul, hfixb]
    show ρ ((a * b : ↥X) : Γ) v * v⁻¹ = (ρ (a : Γ) v * v⁻¹) * (ρ (b : Γ) v * v⁻¹)
    rw [hab]
    calc (ρ (b : Γ) v * v⁻¹) * ρ (a : Γ) v * v⁻¹
        = (ρ (b : Γ) v * v⁻¹) * (ρ (a : Γ) v * v⁻¹) := by group
      _ = (ρ (a : Γ) v * v⁻¹) * (ρ (b : Γ) v * v⁻¹) := hcomm _ _
  have hcv : ∀ v ∈ V₀, ∀ g ∈ X, ρ g v = v := by
    intro v hv g hg
    obtain ⟨φ, hφ⟩ := hhom v hv
    have hle : X ≤ φ.ker.map X.subtype := by
      refine hperf.symm.le.trans (Subgroup.commutator_le.2 fun a ha b hb => ?_)
      refine ⟨⁅(⟨a, ha⟩ : ↥X), ⟨b, hb⟩⁆, ?_, map_commutatorElement X.subtype _ _⟩
      show φ ⁅(⟨a, ha⟩ : ↥X), ⟨b, hb⟩⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
    obtain ⟨c, hc, hcg⟩ := hle hg
    have hφc : ρ (c : Γ) v * v⁻¹ = 1 := by
      rw [← hφ c]
      exact hc
    have h1 : ρ (c : Γ) v = v := mul_inv_eq_one.1 hφc
    rwa [show (c : Γ) = g from hcg] at h1
  have hV₀bot : V₀ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    exact Subgroup.mem_bot.2 (hfix v hv (fun g hg => hcv v hv g hg))
  rw [hV₀bot, Subgroup.card_bot] at hcard
  norm_num at hcard

end Perfect

end ModSplit

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
