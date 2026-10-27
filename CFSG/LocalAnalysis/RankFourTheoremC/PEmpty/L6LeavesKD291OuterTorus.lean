module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Out

open CFSG.Open CFSG.LocalAnalysis.RankFourTheoremC

section Torus

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def torusEntry {G : Type*} [Group G] (a₀ a₁ a₂ : G →* Kˣ) : ℕ → (G →* Kˣ)
  | 0 => a₀
  | 1 => a₁
  | 2 => a₂
  | 3 => (a₀ * a₁ * a₂)⁻¹
  | _ + 4 => 1

theorem prod_torusEntry {G : Type*} [Group G] (a₀ a₁ a₂ : G →* Kˣ) (hn : 4 ≤ n)
    (x : G) : ∏ j : Fin n, torusEntry a₀ a₁ a₂ j.val x = 1 := by
  rw [Fin.prod_univ_eq_prod_range (fun i => torusEntry a₀ a₁ a₂ i x) n]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Finset.prod_range_add]
  have h2 : ∏ i ∈ Finset.range m, torusEntry a₀ a₁ a₂ (4 + i) x = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    rw [Nat.add_comm]
    rfl
  rw [h2, mul_one]
  simp [Finset.prod_range_succ, torusEntry]

theorem exists_torus {p : ℕ} (hn : 5 ≤ n) (χ : Multiplicative (ZMod p) →* Kˣ) :
    ∃ κ : (Fin 3 → Multiplicative (ZMod p)) →* (Fin n → Kˣ),
      (∀ x, ∏ j, κ x j = 1) ∧ (∀ x (m : Fin 3), κ x ⟨m.val, by omega⟩ = χ (x m)) ∧
        ∀ x, κ x ⟨4, by omega⟩ = 1 := by
  refine ⟨MonoidHom.pi (fun j : Fin n => torusEntry
    (χ.comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) 0))
    (χ.comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) 1))
    (χ.comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) 2)) j.val), ?_, ?_, ?_⟩
  · intro x
    simpa using prod_torusEntry
      (χ.comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) 0))
      (χ.comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) 1))
      (χ.comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod p)) 2)) (by omega) x
  · intro x m
    fin_cases m <;> simp [torusEntry]
  · intro x
    simp [torusEntry]

end Torus

theorem exists_diag_torus {K : Type} [Field K] [Finite K] {p n : ℕ} (hp : p.Prime) (hn : 5 ≤ n)
    (hpK : p ∣ Nat.card K - 1) :
    ∃ κ : (Fin 3 → Multiplicative (ZMod p)) →* (Fin n → Kˣ),
      (∀ x j, κ x j ^ p = 1) ∧ (∀ x, ∏ j, κ x j = 1) ∧
      ∀ x (c : Kˣ), (∀ j, κ x j = c) → x = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  have hprimU : IsPrimitiveRoot ζ p := by
    rw [← hζ]
    exact IsPrimitiveRoot.orderOf ζ
  obtain ⟨χ, hχ⟩ : ∃ χ : Multiplicative (ZMod p) →* Kˣ, Function.Injective χ :=
    ⟨(Subgroup.zpowers ζ).subtype.comp
        (AddEquiv.toMultiplicativeLeft hprimU.zmodEquivZPowers).toMonoidHom,
      Subtype.val_injective.comp (AddEquiv.toMultiplicativeLeft hprimU.zmodEquivZPowers).injective⟩
  obtain ⟨κ, hκdet, hκ, hκ4⟩ := exists_torus hn χ
  refine ⟨κ, fun x j => ?_, hκdet, fun x c hc => ?_⟩
  · have h1 : (κ x) ^ p = 1 := by rw [← map_pow, od_torus_pow, map_one]
    simpa using congrFun h1 j
  · have hc1 : c = 1 := by
      rw [← hc ⟨4, by omega⟩, hκ4]
    subst hc1
    funext m
    apply hχ
    rw [Pi.one_apply, map_one, ← hκ x m]
    exact hc _

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Out
