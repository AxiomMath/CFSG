module

public import Mathlib.Data.Finset.Card

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Classical

@[expose] noncomputable def fcMaps (F : ℕ → Fin 1024 → Fin 1024) (Y : List ℕ) :
    Finset (Fin 1024 → Fin 1024) :=
  (Y.map F).toFinset

theorem mem_fcMaps {F : ℕ → Fin 1024 → Fin 1024} {Y : List ℕ} {x : Fin 1024 → Fin 1024} :
    x ∈ fcMaps F Y ↔ ∃ i ∈ Y, F i = x := by
  simp [fcMaps]

theorem card_fcMaps_le (F : ℕ → Fin 1024 → Fin 1024) (Y : List ℕ) :
    (fcMaps F Y).card ≤ Y.length := by
  simpa [fcMaps] using List.toFinset_card_le (Y.map F)

theorem fcComm_of_sq {a b : Fin 1024 → Fin 1024} (ha : a ∘ a = id) (hb : b ∘ b = id)
    (hab : (a ∘ b) ∘ (a ∘ b) = id) : a ∘ b = b ∘ a := by
  funext v
  have h1 : a (b (a (b (b v)))) = b v := congrFun hab (b v)
  have h2 : b (b v) = v := congrFun hb v
  have h3 : a (a (b (a v))) = b (a v) := congrFun ha (b (a v))
  rw [h2] at h1
  rw [h1] at h3
  exact h3

variable {F : ℕ → Fin 1024 → Fin 1024} {N e : ℕ} {mul : ℕ → ℕ → ℕ} {fam : List (List ℕ)}

theorem fcFamily_closed
    (hmul_lt : ∀ i < N, ∀ j < N, mul i j < N)
    (hmul : ∀ i < N, ∀ j < N, F (mul i j) = F i ∘ F j)
    (hinj : ∀ i < N, ∀ j < N, F i = F j → i = j)
    (he : e < N) (hFe : F e = id) (hbase : [e] ∈ fam)
    (hext : ∀ Y ∈ fam, (∀ i ∈ Y, i < N) → ∀ y < N, mul y y = e → y ∉ Y →
      (∀ x ∈ Y, mul y x = mul x y) → ∃ Z ∈ fam, ∀ i, i ∈ Z ↔ i ∈ Y ∨ ∃ x ∈ Y, i = mul y x)
    {X : Finset (Fin 1024 → Fin 1024)} (hXN : ∀ x ∈ X, ∃ i < N, F i = x)
    (hXmul : ∀ x ∈ X, ∀ y ∈ X, x ∘ y ∈ X) (hXsq : ∀ x ∈ X, x ∘ x = id) (hXne : X.Nonempty) :
    ∃ Z ∈ fam, (∀ i ∈ Z, i < N) ∧ fcMaps F Z = X := by
  have hcomm : ∀ x ∈ X, ∀ y ∈ X, x ∘ y = y ∘ x := fun x hx y hy =>
    fcComm_of_sq (hXsq x hx) (hXsq y hy) (hXsq _ (hXmul x hx y hy))
  have key : ∀ d : ℕ, ∀ Y ∈ fam, (∀ i ∈ Y, i < N) → e ∈ Y → fcMaps F Y ⊆ X →
      X.card - (fcMaps F Y).card = d → ∃ Z ∈ fam, (∀ i ∈ Z, i < N) ∧ fcMaps F Z = X := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro Y hY hYN heY hsub hd
      by_cases hX : X ⊆ fcMaps F Y
      · exact ⟨Y, hY, hYN, Finset.Subset.antisymm hsub hX⟩
      · obtain ⟨x, hxX, hxY⟩ := Finset.not_subset.1 hX
        obtain ⟨y, hyN, rfl⟩ := hXN x hxX
        have hyY : y ∉ Y := fun h => hxY (mem_fcMaps.2 ⟨y, h, rfl⟩)
        have hFY : ∀ z ∈ Y, F z ∈ X := fun z hz => hsub (mem_fcMaps.2 ⟨z, hz, rfl⟩)
        have hyy : mul y y = e := by
          refine hinj _ (hmul_lt y hyN y hyN) e he ?_
          rw [hmul y hyN y hyN, hFe]
          exact hXsq _ hxX
        have hcommY : ∀ z ∈ Y, mul y z = mul z y := fun z hz => by
          have hz' := hYN z hz
          refine hinj _ (hmul_lt y hyN z hz') _ (hmul_lt z hz' y hyN) ?_
          rw [hmul y hyN z hz', hmul z hz' y hyN]
          exact hcomm _ hxX _ (hFY z hz)
        obtain ⟨Z, hZ, hZY⟩ := hext Y hY hYN y hyN hyy hyY hcommY
        have hZN : ∀ i ∈ Z, i < N := fun i hi => by
          rcases (hZY i).1 hi with h | ⟨z, hz, rfl⟩
          · exact hYN i h
          · exact hmul_lt y hyN z (hYN z hz)
        have heZ : e ∈ Z := (hZY e).2 (Or.inl heY)
        have hZsub : fcMaps F Z ⊆ X := fun w hw => by
          obtain ⟨i, hi, rfl⟩ := mem_fcMaps.1 hw
          rcases (hZY i).1 hi with h | ⟨z, hz, rfl⟩
          · exact hFY i h
          · rw [hmul y hyN z (hYN z hz)]
            exact hXmul _ hxX _ (hFY z hz)
        have hlt : (fcMaps F Y).card < (fcMaps F Z).card := by
          refine Finset.card_lt_card ⟨fun w hw => ?_, fun hle => hxY (hle ?_)⟩
          · obtain ⟨i, hi, rfl⟩ := mem_fcMaps.1 hw
            exact mem_fcMaps.2 ⟨i, (hZY i).2 (Or.inl hi), rfl⟩
          · refine mem_fcMaps.2 ⟨mul y e, (hZY _).2 (Or.inr ⟨e, heY, rfl⟩), ?_⟩
            rw [hmul y hyN e he, hFe]
            rfl
        have hle : (fcMaps F Z).card ≤ X.card := Finset.card_le_card hZsub
        exact ih (X.card - (fcMaps F Z).card) (by omega) Z hZ hZN heZ hZsub rfl
  obtain ⟨x₀, hx₀⟩ := hXne
  have hid : id ∈ X := by simpa [hXsq x₀ hx₀] using hXmul x₀ hx₀ x₀ hx₀
  refine key _ [e] hbase (by simpa using he) (by simp) ?_ rfl
  intro w hw
  obtain ⟨i, hi, rfl⟩ := mem_fcMaps.1 hw
  have hi' : i = e := by simpa using hi
  subst hi'
  rw [hFe]
  exact hid

end CFSG.EvenSporadicStandard.TwoFi22.DS81
