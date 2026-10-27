module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2ATests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Root
public import CFSG.Sporadic.Co1Block.TwoACent

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

open Subgroup CFSG.Open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block

@[expose] noncomputable def co1Cen2AQG : List GL24 :=
  [twoAQg 0, twoAQg 1, twoAQg 2, twoAQg 3, twoAQg 4, twoAQg 5, twoAQg 6, twoAQg 7]

@[expose] noncomputable def co1Cen2ABaseG : List GL24 := A₁ :: A₂ :: aG :: co1Cen2AQG

theorem rep_co1Cen2AQ :
    List.Forall₂ MRep co1Cen2AQRows co1Cen2AQG :=
  .cons (rep_iotaQ 0) (.cons (rep_iotaQ 1) (.cons (rep_iotaQ 2) (.cons (rep_iotaQ 3)
    (.cons (rep_iotaQ 4) (.cons (rep_iotaQ 5) (.cons (rep_iotaQ 6) (.cons (rep_iotaQ 7) .nil)))))))

theorem rep_co1Cen2ABase :
    List.Forall₂ MRep co1Cen2ABase co1Cen2ABaseG :=
  .cons rep_A₁ (.cons rep_A₂ (.cons rep_iotaA rep_co1Cen2AQ))

theorem co1Cen2AQG_mem : ∀ g ∈ co1Cen2AQG, g ∈ GA := by
  intro g hg
  simp only [co1Cen2AQG, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> rw [h] <;> exact iotaQ_mem_GA _

theorem co1Cen2ABaseG_mem : ∀ g ∈ co1Cen2ABaseG, g ∈ GA := by
  intro g hg
  rcases List.mem_cons.mp hg with h | hg
  · rw [h]; exact A₁_mem
  rcases List.mem_cons.mp hg with h | hg
  · rw [h]; exact A₂_mem
  rcases List.mem_cons.mp hg with h | hg
  · rw [h]; exact iotaA_mem_GA
  exact co1Cen2AQG_mem g hg

theorem twoAQg_mem_co1Cen2AQG {k : ℕ} (hk : k < 8) : twoAQg k ∈ co1Cen2AQG := by
  interval_cases k <;> simp [co1Cen2AQG]

theorem comm_twoAQ_of_comm {g : GL24} (hq : ∀ k < 8, g * twoAQg k = twoAQg k * g) :
    ∀ q ∈ twoAQ, g * q = q * g := by
  have hle : twoAQ ≤ Subgroup.centralizer {g} := by
    show Subgroup.closure (twoAQg '' {l | l < twoAQRows.length}) ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [twoAQRows_length] at hk
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hq k hk).symm
  intro q hqQ
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hqQ)).symm

theorem eq_one_or_eq_aG_of_comm
    {g : GL24}
    (hg : g ∈ GA ⊓ Subgroup.centralizer {aG}) (hq : ∀ k < 8, g * twoAQg k = twoAQg k * g) :
    g = 1 ∨ g = aG := by
  obtain ⟨b, hb⟩ := exists_roots qRep_twoA twoA_q_check
  have hT := card_mul_card_towerStab_brayE_le rep_iotaA twoA_cent_check twoA_q_check
    (fun i hi => (hb i hi).2)
  have hE : brayE aG twoAD1 twoABray = GA ⊓ Subgroup.centralizer {aG} := twoAE_eq
  rw [twoA_tower_prod, hE, card_cent_aG] at hT
  set T := towerStab (GA ⊓ Subgroup.centralizer {aG}) b twoARoots.length
  have hT2 : Nat.card T ≤ 2 := by omega
  have hQ := comm_twoAQ_of_comm hq
  have hgT : g ∈ T := mem_towerStab_of_lt hg _ fun i hi => hQ (b i) (hb i hi).1
  have haT : aG ∈ T := mem_towerStab_of_lt (Subgroup.mem_inf.2 ⟨iotaA_mem_GA,
    Subgroup.mem_centralizer_singleton_iff.2 rfl⟩) _ fun i hi =>
      (Subgroup.mem_centralizer_singleton_iff.1
        (Subgroup.mem_inf.1 (twoAQ_le (hb i hi).1)).2).symm
  by_contra hne
  push Not at hne
  have hsub : ({1, aG, g} : Set GL24) ⊆ (T : Set GL24) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [T.one_mem, haT, hgT]
  have hcard3 : ({1, aG, g} : Set GL24).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [aG_ne_one.symm, hne.1.symm]),
      Set.ncard_pair hne.2.symm]
  have h3 : 3 ≤ Nat.card T := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [hcard3, ← Nat.card_coe_set_eq] at this
  omega

theorem co1_pWitness_aG
    {glob : List (List ℕ)} {s₁ s₂ : List ℕ} {d₁ d₂ : List (List ℕ)} {zh₁ zh₂ : ℕ × ℕ}
    {dec₁ dec₂ : List (List ℕ)} {qd : List (List ℕ)} {qe : List ℕ}
    (h : co1Cen2ACheck glob s₁ s₂ d₁ d₂ zh₁ zh₂ dec₁ dec₂ qd qe = true) {E : Subgroup GL24}
    (hEG : E ≤ GA) (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) (haE : aG ∈ E) :
    PWitness GA E := by
  simp only [co1Cen2ACheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hG, hP₁⟩, hP₂⟩, hq⟩ := h
  refine RootWitness.pWitness rep_co1Cen2ABase co1Cen2ABaseG_mem hG rep_iotaA aG_ne_one hP₁ hP₂
    (Z := {1, aG}) (fun b hb h₁ h₂ => ?_) hEG hE haE ?_
  · have hc := RootWitness.comm_of_words rep_co1Cen2ABase hG rep_co1Cen2AQ hq h₁ h₂
    rcases eq_one_or_eq_aG_of_comm hb fun k hk => hc _ (twoAQg_mem_co1Cen2AQG hk) with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro hsub
    have hle : Nat.card E ≤ 2 := by
      have hE' : Nat.card E = (E : Set GL24).ncard := (Nat.card_coe_set_eq _).symm
      rw [hE']
      calc (E : Set GL24).ncard ≤ ({1, aG} : Set GL24).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ ({aG} : Set GL24).ncard + 1 := Set.ncard_insert_le 1 {aG}
        _ = 2 := by rw [Set.ncard_singleton]
    omega

end CFSG.ComponentClassification.RankTwoSporadic.Co1
