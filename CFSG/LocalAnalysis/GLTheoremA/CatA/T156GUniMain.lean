module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GMain
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType

section Unitary

variable {p : ℕ}

theorem geomBody_unitary (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (htag : lab.tag ≠ .triD4) {l n : ℕ} (hl : 2 ≤ l) (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    GeomBody p lab (LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n)))
        (LargeEvenGUSet (Fin (l + 1)) K (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n)))) := by
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 2 * n)
    (by rw [hK, ← pow_mul, mul_comm])
  refine fun _ _ => ⟨fun _ f hf hord => ?_, fun h' => absurd h' htag⟩
  have hd : 3 ≤ l + 1 := by omega
  obtain ⟨σ, hσf⟩ := Uni.exists_induced hf
  have hσord : orderOf σ = p := (Uni.orderOf_eq_of_induced hd hn hK hσf).trans hord
  have hσodd : Odd (orderOf σ) := by
    rw [hσord]
    exact hp.odd_of_ne_two hp2
  obtain ⟨hnr, hn', -⟩ := Uni.fixF_data hn hK σ hσodd
  rw [hσord] at hnr hn'
  by_cases hdq : (l + 1, 2 ^ (n / p)) = (3, 2)
  ·
    obtain ⟨hl3, hq2⟩ := Prod.mk.inj hdq
    have hl2 : l = 2 := by omega
    have hnp1 : n / p = 1 := by
      have h1 : 2 ^ (n / p) = 2 ^ 1 := by rw [hq2]; norm_num
      exact Nat.pow_right_injective (le_refl 2) h1
    have hnp : n = p := by rw [hnr, hnp1, one_mul]
    subst hl2
    subst hnp
    by_cases hp3 : n = 3
    · subst hp3
      exact Or.inr ⟨rfl, Uni.catalogIs_u3eight hK⟩
    · have hodd := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
      have h2 := hp.two_le
      exact Or.inl (Uni.fixAlt_u3 hp (by omega) hK f)
  ·
    have hlab₀ : LargeEvenInLambda2 ⟨.twA, l, n / p⟩ := by
      refine ⟨hn', ?_⟩
      dsimp only
      refine ⟨hl, fun hl2 => ?_⟩
      by_contra hlt
      have h1 : n / p = 1 := by omega
      apply hdq
      rw [hl2, h1]
      norm_num
    exact Or.inl (fixAlt_of_raw hlab₀ (Uni.exists_raw_unitary hd hn hK hp hp2 hdq hf hord))

theorem cAll_geomBody_twA (hp : p.Prime) (hp2 : p ≠ 2) {l n : ℕ} (hl : 2 ≤ l) (hn : 1 ≤ n) :
    MI.CAll ⟨.twA, l, n⟩ (GeomBody p ⟨.twA, l, n⟩) := by
  intro Q hQ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  exact recipeUnitary_and (fun K _ _ hK => geomBody_unitary hp hp2 (by simp) hl hn K hK) hQ

theorem cAll_geomBody_twD3 (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) :
    MI.CAll ⟨.twD, 3, n⟩ (GeomBody p ⟨.twD, 3, n⟩) := by
  intro Q hQ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  simp only [↓reduceIte] at hQ ⊢
  exact recipeUnitary_and
    (fun K _ _ hK => geomBody_unitary (l := 3) hp hp2 (by simp) (by norm_num) hn K hK) hQ

end Unitary

@[expose] def RestLabel₂ (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ lab.rank = 1) ∨ ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2) ∨
    (lab.tag = .D ∧ 4 ≤ lab.rank ∧ ¬ p ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twD ∧ lab.rank = 2) ∨
    lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
    (lab.tag = .E6 ∧ (p = 3 ∨ ¬ p ∣ 2 ^ lab.n - 1)) ∨ lab.tag = .twE6

@[expose] def T156Rest₂ : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → RestLabel₂ p lab →
    MI.CAll lab (GeomBody p lab)

theorem t156Rest_of_rest₂ (h : T156Rest₂) : T156Rest := by
  intro p hp hp2 lab hlab hr
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  by_cases htwA : t = .twA
  · subst htwA
    exact cAll_geomBody_twA hp hp2 hlab.2.1 hn
  by_cases htwD3 : t = .twD ∧ l = 3
  · obtain ⟨rfl, rfl⟩ := htwD3
    exact cAll_geomBody_twD3 hp hp2 hn
  refine h p hp hp2 ⟨t, l, n⟩ hlab ?_
  unfold RestLabel at hr
  unfold RestLabel₂
  dsimp only at hr ⊢
  rcases hr with h1 | h1 | h1 | h1 | ⟨h1, h2⟩ | h1 | h1 | h1 | h1 | h1 | h1
  · exact absurd h1 htwA
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · have hl2 : 2 ≤ l := by
      subst h1
      exact hlab.2
    have hl3 : l ≠ 3 := fun h3 => htwD3 ⟨h1, h3⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))))))

section Core


theorem t156FactOmega_of_rest₂ (h : T156Rest₂) (p : ℕ) : T156FactOmega p :=
  t156FactOmega_of_rest (t156Rest_of_rest₂ h) p

end Core

end CFSG.LocalAnalysis.GLTheoremA.T156

end
