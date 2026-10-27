module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.ThreePrimeSeven
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.AtlasOrders2
public import Certificates.Certificate295133

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem card_le_four_of_no_triples {G : Type*} [Group G] [Finite G]
    (hno : ∀ a b c : G, a ^ 2 = 1 → b ^ 2 = 1 → c ^ 2 = 1 → a * b = b * a → a * c = c * a →
      b * c = c * b → a = 1 ∨ b = 1 ∨ b = a ∨ c = 1 ∨ c = a ∨ c = b ∨ c = a * b)
    (E : Subgroup G) (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a ^ 2 = 1) :
    Nat.card E ≤ 4 := by
  classical
  by_contra hlt
  push Not at hlt
  have hE : (E : Set G).ncard = Nat.card E := by rw [← Nat.card_coe_set_eq]; rfl
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    by_contra hall
    push Not at hall
    have : (E : Set G) ⊆ (({1} : Finset G) : Set G) := fun x hx => by simp [hall x hx]
    have := Set.ncard_le_ncard this (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Finset.card_singleton] at this
    omega
  obtain ⟨b, hbE, hb1, hba⟩ : ∃ b ∈ E, b ≠ 1 ∧ b ≠ a := by
    by_contra hall
    push Not at hall
    have : (E : Set G) ⊆ (({1, a} : Finset G) : Set G) := fun x hx => by
      by_cases h1 : x = 1
      · simp [h1]
      · simp [hall x hx h1]
    have h := Set.ncard_le_ncard this (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h
    have := Finset.card_le_two (a := (1 : G)) (b := a)
    omega
  obtain ⟨c, hcE, hc1, hca, hcb, hcab⟩ : ∃ c ∈ E, c ≠ 1 ∧ c ≠ a ∧ c ≠ b ∧ c ≠ a * b := by
    by_contra hall
    push Not at hall
    have : (E : Set G) ⊆ (({1, a, b, a * b} : Finset G) : Set G) := fun x hx => by
      by_cases h1 : x = 1
      · simp [h1]
      by_cases h2 : x = a
      · simp [h2]
      by_cases h3 : x = b
      · simp [h3]
      · simp [hall x hx h1 h2 h3]
    have h := Set.ncard_le_ncard this (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h
    have := Finset.card_le_four (a := (1 : G)) (b := a) (c := b) (d := a * b)
    omega
  rcases hno a b c (h2 a haE) (h2 b hbE) (h2 c hcE) (hc a haE b hbE) (hc a haE c hcE)
    (hc b hbE c hcE) with h | h | h | h | h | h | h <;> contradiction

theorem u33_threePrime_bound
    {X : Type} [Group X]
    (hX : IsUThreeThree X) (H : Subgroup X) (hH : ¬ 3 ∣ Nat.card H) : Nat.card H ≤ 32 := by
  obtain ⟨e⟩ := equiv_of_lieModel (lieModel_of_isUThreeThree hX)
  have hcard : Nat.card X = 6048 := card_of_isUThreeThree hX
  have : Finite X := Nat.finite_of_card_ne_zero (by omega)
  have hno := Certificates.certificate295133
  have hord := noOrdersCheck_sound QP QP_ok (by norm_num : 0 < 14) (by norm_num : 0 < 21) hno.1
  have h8 := e8free_sound QP QP_ok hno.2
  have hord' : ∀ g : X, orderOf g = orderOf ((e g : QP.originalSubgroup) : Equiv.Perm (Fin 28)) := by
    intro g
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  refine card_le_of_not_three_dvd hcard (fun g => ?_) (fun g => ?_) ?_ H hH
  · rw [hord' g]; exact (hord _ (e g).2).1
  · rw [hord' g]; exact (hord _ (e g).2).2
  · intro E hc h2
    refine card_le_four_of_no_triples (fun a b c ha hb hc' hab hac hbc => ?_) E hc h2
    have key := h8 (e a : Equiv.Perm (Fin 28)) (e a).2 (e b : Equiv.Perm (Fin 28)) (e b).2
      (e c : Equiv.Perm (Fin 28)) (e c).2
      (by rw [← Subgroup.coe_pow, ← map_pow, ha]; simp)
      (by rw [← Subgroup.coe_pow, ← map_pow, hb]; simp)
      (by rw [← Subgroup.coe_pow, ← map_pow, hc']; simp)
      (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hab])
      (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hac])
      (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hbc])
    have hinj : Function.Injective (fun g : X => ((e g : QP.originalSubgroup) : Equiv.Perm (Fin 28))) :=
      fun x y hxy => e.injective (Subtype.ext hxy)
    have e1 : ∀ g : X, ((e g : QP.originalSubgroup) : Equiv.Perm (Fin 28)) = 1 ↔ g = 1 := fun g => by
      rw [← Subgroup.coe_one, ← map_one e, Subtype.coe_inj, e.apply_eq_iff_eq]
    rcases key with h | h | h
    · exact Or.inl ((e1 a).1 h)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · exact Or.inr (Or.inl ((e1 b).1 h))
      · exact Or.inr (Or.inr (Or.inl (hinj h)))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl ((e1 c).1 h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hinj h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hinj h))))))
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hinj ?_))))))
        simpa using h

theorem u33Atlas_proved :
    U33Atlas := fun X _ hX =>
  ⟨card_of_isUThreeThree hX, u33_threePrime_bound hX⟩

end CFSG.AGLEmbeddingD2.McLaughlin
