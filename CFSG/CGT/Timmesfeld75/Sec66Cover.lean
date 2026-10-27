module

public import CFSG.CGT.Timmesfeld75.Sec66Fam

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {U Tb P : Subgroup G} {y y' : G} {q : ℕ}

@[expose] def sec66T (U Tb P : Subgroup G) : Set (Subgroup G) :=
  {S | ∃ j ∈ U ⊔ Tb ⊔ P, S = conjSubgroup j U}

omit [Finite G] in
theorem sec66T_U (U Tb P : Subgroup G) : U ∈ sec66T U Tb P :=
  ⟨1, (U ⊔ Tb ⊔ P).one_mem, (conjSubgroup_one U).symm⟩

omit [Finite G] in
theorem sec66T_B (hB : ∃ s ∈ U ⊔ Tb, Tb = conjSubgroup s U) : Tb ∈ sec66T U Tb P := by
  obtain ⟨s, hs, hsB⟩ := hB
  exact ⟨s, (le_sup_left : U ⊔ Tb ≤ U ⊔ Tb ⊔ P) hs, hsB⟩

omit [Finite G] in
theorem sec66T_P (hP : ∃ s ∈ U ⊔ P, P = conjSubgroup s U) : P ∈ sec66T U Tb P := by
  obtain ⟨s, hs, hsP⟩ := hP
  exact ⟨s, (sup_le (le_sup_left.trans le_sup_left) le_sup_right : U ⊔ P ≤ U ⊔ Tb ⊔ P) hs, hsP⟩

omit [Finite G] in
theorem sec66T_trace_card {Q : Subgroup G} (hQn : ∀ x ∈ U ⊔ Tb ⊔ P, conjSubgroup x Q = Q) :
    ∀ R ∈ sec66T U Tb P, Nat.card ↥(R ⊓ Q) = Nat.card ↥(U ⊓ Q) := by
  rintro R ⟨j, hj, rfl⟩
  have : conjSubgroup j U ⊓ Q = conjSubgroup j (U ⊓ Q) := by
    rw [conjSubgroup_inf, hQn j hj]
  rw [this, card_conjSubgroup]

theorem card_le_cube_of_sup_three {Q F₀ F₁ F₂ : Subgroup G} {a : ℕ} (hQ : Q = F₀ ⊔ F₁ ⊔ F₂)
    (hcomm : ∀ x ∈ Q, ∀ z ∈ Q, x * z = z * x) (hc0 : Nat.card ↥F₀ ≤ a)
    (hc1 : Nat.card ↥F₁ ≤ a) (hc2 : Nat.card ↥F₂ ≤ a) : Nat.card ↥Q ≤ a ^ 3 := by
  have hF₀ : F₀ ≤ Q := hQ ▸ le_sup_left.trans le_sup_left
  have hF₁ : F₁ ≤ Q := hQ ▸ le_sup_right.trans le_sup_left
  have hF₂ : F₂ ≤ Q := hQ ▸ le_sup_right
  have h1 : Nat.card ↥(F₀ ⊔ F₁) ≤ Nat.card ↥F₀ * Nat.card ↥F₁ :=
    card_sup_le_mul_of_commute fun x hx z hz => hcomm x (hF₀ hx) z (hF₁ hz)
  have h2 : Nat.card ↥(F₀ ⊔ F₁ ⊔ F₂) ≤ Nat.card ↥(F₀ ⊔ F₁) * Nat.card ↥F₂ :=
    card_sup_le_mul_of_commute fun x hx z hz => hcomm x ((sup_le hF₀ hF₁) hx) z (hF₂ hz)
  rw [← hQ] at h2
  have h3 : Nat.card ↥Q ≤ a * a * a :=
    h2.trans ((Nat.mul_le_mul_right _ h1).trans (Nat.mul_le_mul (Nat.mul_le_mul hc0 hc1) hc2))
  have h4 : a ^ 3 = a * a * a := by ring
  rw [h4]
  exact h3

theorem sec66Q_card_le (hQab : IsElemAbelian 2 (sec66Q U Tb P)) (hBT : Tb ∈ sec66T U Tb P)
    (hPT : P ∈ sec66T U Tb P)
    (htr : ∀ R ∈ sec66T U Tb P, Nat.card ↥(R ⊓ sec66Q U Tb P) =
      Nat.card ↥(U ⊓ sec66Q U Tb P)) :
    Nat.card ↥(sec66Q U Tb P) ≤ Nat.card ↥(U ⊓ sec66Q U Tb P) ^ 3 := by
  have hQeq := sec66Q_eq U Tb P
  have hF₀Q : (⨅ i, normIn U (sec66Fam U Tb P i)) ≤ sec66Q U Tb P := by
    rw [hQeq]
    exact le_sup_left.trans le_sup_left
  have hF₁Q : (⨅ i, normIn Tb (sec66Fam U Tb P i)) ≤ sec66Q U Tb P := by
    rw [hQeq]
    exact le_sup_right.trans le_sup_left
  have hF₂Q : (⨅ i, normIn P (sec66Fam U Tb P i)) ≤ sec66Q U Tb P := by
    rw [hQeq]
    exact le_sup_right
  have hF₀U : (⨅ i, normIn U (sec66Fam U Tb P i)) ≤ U :=
    (iInf_le (fun i => normIn U (sec66Fam U Tb P i)) 0).trans (normIn_le U (sec66Fam U Tb P 0))
  have hF₁B : (⨅ i, normIn Tb (sec66Fam U Tb P i)) ≤ Tb :=
    (iInf_le (fun i => normIn Tb (sec66Fam U Tb P i)) 0).trans (normIn_le Tb (sec66Fam U Tb P 0))
  have hF₂P : (⨅ i, normIn P (sec66Fam U Tb P i)) ≤ P :=
    (iInf_le (fun i => normIn P (sec66Fam U Tb P i)) 0).trans (normIn_le P (sec66Fam U Tb P 0))
  have hc0 : Nat.card ↥(⨅ i, normIn U (sec66Fam U Tb P i)) ≤ Nat.card ↥(U ⊓ sec66Q U Tb P) :=
    Subgroup.card_le_of_le (le_inf hF₀U hF₀Q)
  have hc1 : Nat.card ↥(⨅ i, normIn Tb (sec66Fam U Tb P i)) ≤ Nat.card ↥(Tb ⊓ sec66Q U Tb P) :=
    Subgroup.card_le_of_le (le_inf hF₁B hF₁Q)
  have hc2 : Nat.card ↥(⨅ i, normIn P (sec66Fam U Tb P i)) ≤ Nat.card ↥(P ⊓ sec66Q U Tb P) :=
    Subgroup.card_le_of_le (le_inf hF₂P hF₂Q)
  exact card_le_cube_of_sup_three hQeq (fun x hx z hz => elemAbelian_mul_comm hQab hx hz) hc0
    (hc1.trans (htr Tb hBT).le) (hc2.trans (htr P hPT).le)

end CFSG.CGT.Timmesfeld75
