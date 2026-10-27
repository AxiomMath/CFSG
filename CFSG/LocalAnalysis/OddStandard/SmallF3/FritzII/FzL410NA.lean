module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Emb

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open _root_.Certificates

theorem fz410_normT (hA : FzL410.StageA) (τ : FzL410.A →+ FzL410.A)
    (h2 : ∀ p, τ (τ p) = p) (hρ : ∀ p, τ (FzL410.rho p) = FzL410.rho (τ p))
    (hfix : Nat.card {p : FzL410.A // τ p = p} = 16)
    (hfix2 : Nat.card {p : FzL410.A // τ p = p ∧ (2 : ℕ) • p = 0} = 4) :
    ∃ ψ : FzL410.A →+ FzL410.A, Function.Injective ψ ∧
      (∀ p, ψ (FzL410.rho p) = FzL410.rho (ψ p)) ∧ ∀ p, τ (ψ p) = ψ (FzL410.tt p) := by
  have hτ : ∀ p, τ p = FzL410.evEq (τ (1, 0, 0, 0)) (τ (0, 0, 1, 0)) p := fz410_eq_evEq τ hρ
  have hd2 : (2 : ℕ) • τ (0, 0, 1, 0) = 0 := (fz410_hom_gen_two τ).1
  generalize τ (1, 0, 0, 0) = c at hτ
  generalize τ (0, 0, 1, 0) = d at hτ hd2
  have hIsT : FzL410.IsT c d := by
    refine ⟨hd2, fun p => ?_, ?_, ?_⟩
    · rw [← hτ, ← hτ]; exact h2 p
    · refine Eq.trans ?_ hfix
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact congrArg Finset.card (Finset.filter_congr (fun p _ => by rw [hτ]))
    · refine Eq.trans ?_ hfix2
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact congrArg Finset.card (Finset.filter_congr (fun p _ => by rw [hτ]))
  obtain ⟨c0, d0, hd0, hconj, hcomm, hinj⟩ := hA c d hIsT
  let ψ0 : FzL410.A →+ FzL410.A := fz410EvEqHom c0 d0 hd0
  have hψ0 : ∀ p, ψ0 p = FzL410.evEq c0 d0 p := fun p => rfl
  have hinj0 : Function.Injective ψ0 :=
    (injective_iff_map_eq_zero ψ0).mpr (fun p hp => hinj p (by rw [← hψ0]; exact hp))
  obtain ⟨ψ', h1, h2'⟩ := fz410_hom_inv ψ0 hinj0
  refine ⟨ψ', ?_, ?_, ?_⟩
  · intro a b hab
    have := congrArg ψ0 hab
    rwa [h1, h1] at this
  · intro p
    apply hinj0
    have e : ψ0 (FzL410.rho (ψ' p)) = FzL410.rho p := by
      rw [hψ0, hcomm, ← hψ0, h1]
    rw [e, h1]
  · intro p
    have e1 : ψ0 (τ (ψ' p)) = FzL410.tt p := by
      rw [hψ0, hτ, hconj, ← hψ0, h1]
    calc τ (ψ' p) = ψ' (ψ0 (τ (ψ' p))) := (h2' _).symm
      _ = ψ' (FzL410.tt p) := by rw [e1]

variable {G : Type} [Group G]

theorem fzl410_NA (hA : FzL410.StageA) {P : Subgroup G} {rho t : G} {emb : FzL410.A → G}
    (E : Fz410EmbBase P rho emb) (ht2 : t ^ 2 = 1) (htn : ∀ p ∈ P, t * p * t⁻¹ ∈ P)
    (htr : t * rho = rho * t)
    (hfix : Nat.card {a : FzL410.A // t * emb a * t⁻¹ = emb a} = 16)
    (hfix2 : Nat.card {a : FzL410.A // t * emb a * t⁻¹ = emb a ∧ (2 : ℕ) • a = 0} = 4) :
    ∃ emb' : FzL410.A → G, Fz410EmbT P rho t emb' := by
  obtain ⟨τ, hτ⟩ := Fz410Coord.exists_act E.toFz410Coord htn
  have h2 : ∀ p, τ (τ p) = p := by
    intro p
    apply E.inj
    have e : t * (t * emb p * t⁻¹) * t⁻¹ = (t * t) * emb p * (t * t)⁻¹ := by group
    rw [← hτ, ← hτ, e, ← pow_two, ht2]
    simp
  have hρ : ∀ p, τ (FzL410.rho p) = FzL410.rho (τ p) := by
    intro p
    apply E.inj
    calc emb (τ (FzL410.rho p)) = t * emb (FzL410.rho p) * t⁻¹ := (hτ _).symm
      _ = t * (rho * emb p * rho⁻¹) * t⁻¹ := by rw [E.cj_rho]
      _ = (t * rho) * emb p * (t * rho)⁻¹ := by group
      _ = (rho * t) * emb p * (rho * t)⁻¹ := by rw [htr]
      _ = rho * (t * emb p * t⁻¹) * rho⁻¹ := by group
      _ = rho * emb (τ p) * rho⁻¹ := by rw [hτ]
      _ = emb (FzL410.rho (τ p)) := E.cj_rho _
  have hiff : ∀ a, τ a = a ↔ t * emb a * t⁻¹ = emb a := by
    intro a
    rw [hτ]
    exact ⟨fun h => by rw [h], fun h => E.inj _ _ h⟩
  have hfix' : Nat.card {p : FzL410.A // τ p = p} = 16 :=
    (Nat.card_congr (Equiv.subtypeEquivRight hiff)).trans hfix
  have hfix2' : Nat.card {p : FzL410.A // τ p = p ∧ (2 : ℕ) • p = 0} = 4 :=
    (Nat.card_congr (Equiv.subtypeEquivRight (fun a =>
      ⟨fun h => ⟨(hiff a).mp h.1, h.2⟩, fun h => ⟨(hiff a).mpr h.1, h.2⟩⟩))).trans hfix2
  obtain ⟨ψ, hψinj, hψρ, hψτ⟩ := fz410_normT hA τ h2 hρ hfix' hfix2'
  refine ⟨fun a => emb (ψ a), ⟨⟨Fz410Coord.comp E.toFz410Coord hψinj, fun a => ?_⟩, fun a => ?_⟩⟩
  · rw [E.cj_rho, hψρ]
  · rw [hτ, hψτ]

end CFSG.OddStandard.SmallF3.FritzII
