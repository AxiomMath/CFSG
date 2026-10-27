module

public import CFSG.Quasithin.H13.A5S1517
public import CFSG.Quasithin.H13.A5S1326

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5

theorem fix_card_le_four : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → σ ≠ 1 →
    Fintype.card {x : W5 // pact σ x = x} ≤ 4 := by
  decide +kernel

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : A5.Setting G T L V)

@[expose] def PlainCase : Prop :=
  ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ T → InK4 (S.frame.ρ g)

theorem elemAbelian16_eq_V (hO : pCoreOf 2 (L ⊔ T) = V) (hP : PlainCase S) {E : Subgroup G}
    (hE : IsElemAbelian 2 E) (hET : E ≤ T) (hc : Nat.card E = 16) : E = V := by
  classical
  have hEN : E ≤ Subgroup.normalizer (V : Set G) := fun x hx => S.frame.T_le (hET hx)
  let f : ↥E →* Equiv.Perm (Fin 5) := S.frame.ρ.comp (Subgroup.inclusion hEN)
  have hf : ∀ e : ↥E, f e = S.frame.ρ ⟨e, hEN e.2⟩ := fun e => rfl
  have hfK : ∀ e : ↥E, InK4 (f e) := fun e => hP _ (hET e.2)
  have hker : ∀ e : ↥E, f e = 1 → (e : G) ∈ V := by
    intro e he
    have h1 : ((⟨e, hEN e.2⟩ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
        Subgroup.centralizer (V : Set G) := (S.rho_eq_one_iff _).1 he
    have h2 : (e : G) ∈ T ⊓ Subgroup.centralizer (V : Set G) := ⟨hET e.2, h1⟩
    rw [S.cT, hO] at h2
    exact h2
  have hcomm : ∀ a b : ↥E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  have hfix : ∀ k : f.ker, ∀ e : ↥E,
      pact (f e) (S.frame.ψ ⟨(k : ↥E), hker k k.2⟩) = S.frame.ψ ⟨(k : ↥E), hker k k.2⟩ := by
    intro k e
    have hc' : (e : G) * (k : ↥E) * (e : G)⁻¹ = (k : ↥E) := by
      have := congrArg Subtype.val (hcomm e k)
      calc (e : G) * (k : ↥E) * (e : G)⁻¹ = (k : ↥E) * e * (e : G)⁻¹ := by
            rw [show (e : G) * (k : ↥E) = (k : ↥E) * e from this]
        _ = (k : ↥E) := by group
    exact (S.conj_eq_iff ⟨e, hEN e.2⟩ ⟨(k : ↥E), hker k k.2⟩).1 hc'
  have hcard := Subgroup.card_ker_mul_card_range f
  have hrange_le : Nat.card f.range ≤ 4 := by
    have : Nat.card f.range ≤ Nat.card {σ : Equiv.Perm (Fin 5) // InK4 σ} := by
      refine Nat.card_le_card_of_injective (fun σ => ⟨(σ : Equiv.Perm (Fin 5)), ?_⟩) ?_
      · obtain ⟨e, he⟩ := σ.2
        rw [← he]; exact hfK e
      · intro a b hab
        exact Subtype.ext (congrArg (fun x : {σ : Equiv.Perm (Fin 5) // InK4 σ} => x.1) hab)
    rwa [Nat.card_eq_fintype_card (α := {σ : Equiv.Perm (Fin 5) // InK4 σ}), card_InK4] at this
  by_cases hall : ∀ e : ↥E, f e = 1
  ·
    have hle : E ≤ V := fun x hx => hker ⟨x, hx⟩ (hall ⟨x, hx⟩)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc, S.card_V])
  · exfalso
    push Not at hall
    obtain ⟨e0, he0⟩ := hall
    have hσK : InK4 (f e0) := hfK e0
    have hker4 : Nat.card f.ker ≤ 4 := by
      have : Nat.card f.ker ≤ Nat.card {x : W5 // pact (f e0) x = x} := by
        refine Nat.card_le_card_of_injective
          (fun k => ⟨S.frame.ψ ⟨(k : ↥E), hker k k.2⟩, hfix k e0⟩) ?_
        intro a b hab
        have h1 := congrArg (fun x : {x : W5 // pact (f e0) x = x} => x.1) hab
        have h2 := S.frame.ψ.injective h1
        exact Subtype.ext (Subtype.ext (congrArg (fun x : ↥V => (x : G)) h2))
      rw [Nat.card_eq_fintype_card (α := {x : W5 // pact (f e0) x = x})] at this
      exact this.trans (fix_card_le_four _ hσK he0)
    have hker_pos : 0 < Nat.card f.ker := Nat.card_pos
    have hrange_pos : 0 < Nat.card f.range := Nat.card_pos
    rw [hc] at hcard
    have hk4 : Nat.card f.ker = 4 := by nlinarith
    have hr4 : Nat.card f.range = 4 := by nlinarith
    have hsurj : ∀ τ : Equiv.Perm (Fin 5), InK4 τ → ∃ e : ↥E, f e = τ := by
      have h4 : Nat.card f.range = Nat.card {σ : Equiv.Perm (Fin 5) // InK4 σ} := by
        rw [Nat.card_eq_fintype_card (α := {σ : Equiv.Perm (Fin 5) // InK4 σ}), card_InK4, hr4]
      have hinj : Function.Injective (fun σ : f.range =>
          (⟨(σ : Equiv.Perm (Fin 5)), by
            obtain ⟨e, he⟩ := σ.2
            rw [← he]; exact hfK e⟩ : {σ : Equiv.Perm (Fin 5) // InK4 σ})) := by
        intro a b hab
        exact Subtype.ext (congrArg (fun x : {σ : Equiv.Perm (Fin 5) // InK4 σ} => x.1) hab)
      have hbij := (Nat.bijective_iff_injective_and_card _).2 ⟨hinj, h4⟩
      intro τ hτ
      obtain ⟨σ, hσ⟩ := hbij.2 ⟨τ, hτ⟩
      obtain ⟨e, he⟩ := σ.2
      exact ⟨e, by rw [he]; exact congrArg Subtype.val hσ⟩
    have hker2 : Nat.card f.ker ≤ 2 := by
      have hcardfix : Nat.card {x : W5 // x = 1 ∨ x = W4} = 2 := by
        rw [Nat.card_eq_fintype_card (α := {x : W5 // x = 1 ∨ x = W4})]; exact card_one_W4
      have : Nat.card f.ker ≤ Nat.card {x : W5 // x = 1 ∨ x = W4} := by
        refine Nat.card_le_card_of_injective (fun k => ⟨S.frame.ψ ⟨(k : ↥E), hker k k.2⟩, ?_⟩) ?_
        · apply fixed_K4
          intro τ hτ
          obtain ⟨e, he⟩ := hsurj τ hτ
          rw [← he]; exact hfix k e
        · intro a b hab
          have h1 := congrArg (fun x : {x : W5 // x = 1 ∨ x = W4} => x.1) hab
          have h2 := S.frame.ψ.injective h1
          exact Subtype.ext (Subtype.ext (congrArg (fun x : ↥V => (x : G)) h2))
      omega
    omega

end Setting

end CFSG.GH74.QTGen4.U42
