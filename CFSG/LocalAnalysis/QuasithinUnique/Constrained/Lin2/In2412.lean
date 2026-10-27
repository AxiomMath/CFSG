module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2412a

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

@[expose] def Lemma2_4_12_two : Prop :=
  Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
    ∀ B : Subgroup G, Lin2BProps T S (thompsonJ S) D B →
      ∀ f ∈ S ⊓ Subgroup.normalizer (B : Set G), f ≠ 1 → f ^ 2 = 1 →
        (∀ r ∈ thompsonJ S, (f * r) ^ 2 = 1 → ∃ s ∈ thompsonJ S, s⁻¹ * f * s = f * r) ∧
        ((∃ m : ℕ, n = 2 * m ∧ 1 < m ∧ IsShort2 (L ⊓ Subgroup.centralizer ({f} : Set G)) ∧
            IsLin2Type (L ⊓ Subgroup.centralizer ({f} : Set G)) m ∧
            blockU L ⊓ Subgroup.centralizer ({f} : Set G) =
              blockU (L ⊓ Subgroup.centralizer ({f} : Set G)) ∧
            pCoreOf 2 (L ⊓ Subgroup.centralizer ({f} : Set G)) =
              blockU L ⊓ Subgroup.centralizer ({f} : Set G)) ∨
          (n = 2 ∧
            ((centerOf L = ⊥ ∧
                Nonempty ((L ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) ≃*
                  Equiv.Perm (Fin 4)) ∧
                pCoreOf 2 (L ⊓ Subgroup.centralizer ({f} : Set G)) =
                  blockU L ⊓ Subgroup.centralizer ({f} : Set G)) ∨
              (centerOf L ≠ ⊥ ∧
                Nonempty ((L ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) ≃*
                  Equiv.Perm (Fin 4) × Multiplicative (ZMod 2)) ∧
                pCoreOf 2 (L ⊓ Subgroup.centralizer ({f} : Set G)) =
                  blockU L ⊓ Subgroup.centralizer ({f} : Set G))))) ∧
        Nat.card ((lin2Z L (thompsonJ S) ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G)) =
          2 ^ (n / 2) ∧
        (centerOf L = ⊥ →
          Nat.card ((thompsonJ S ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G)) =
            2 ^ (3 * n / 2)) ∧
        (centerOf L ≠ ⊥ →
          Nat.card ((thompsonJ S ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G)) =
            2 ^ (2 * n))

theorem complement_facts (h8 : Lemma2_4_8) {G : Type} [Group G] [Finite G]
    {T M H S L D : Subgroup G} {n : ℕ} (hcfg : Lin2Cfg G T M H S L n D) {B : Subgroup G}
    (hB : Lin2BProps T S (thompsonJ S) D B) :
    pCoreOf 2 L = pCoreOf 2 H ∧ thompsonJ S ⊓ (S ⊓ Subgroup.normalizer (B : Set G)) = ⊥ ∧
      thompsonJ S ⊔ (S ⊓ Subgroup.normalizer (B : Set G)) = S ∧
      L ⊓ (S ⊓ Subgroup.normalizer (B : Set G)) = ⊥ ∧
      H = L ⊔ (S ⊓ Subgroup.normalizer (B : Set G)) := by
  obtain ⟨-, -, -, -, -, -, -, -, hRT, hRTbot, -⟩ := hB
  obtain ⟨⟨-, -, hTR⟩, ⟨hQL, hUH⟩, ⟨-, hsyl, -⟩, -⟩ := h8 G T M H S L D n hcfg
  set F := S ⊓ Subgroup.normalizer (B : Set G) with hF
  have hRS : thompsonJ S ≤ S := thompsonJ_le_self S
  have hRL : thompsonJ S ≤ L := hsyl.1
  have h1 : thompsonJ S ⊓ F = ⊥ :=
    le_bot_iff.1 (hRTbot ▸ inf_le_inf_left _ (inf_le_inf_right _ hcfg.S_le_T))
  have h2 : thompsonJ S ⊔ F = S := by
    refine le_antisymm (sup_le hRS inf_le_left) fun s hs => ?_
    have hsT : s ∈ thompsonJ S ⊔ (T ⊓ Subgroup.normalizer (B : Set G)) :=
      hRT.ge (hcfg.S_le_T hs)
    obtain ⟨r, hr, t, ht, rfl⟩ := (mem_sup_iff_of_le_normalizer (N := thompsonJ S)
      (H := T ⊓ Subgroup.normalizer (B : Set G)) fun t ht => hTR ht.1).1 hsT
    have htS : t ∈ S := by
      have := S.mul_mem (S.inv_mem (hRS hr)) hs
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right ⟨htS, ht.2⟩)
  have hSL : S ⊓ L = thompsonJ S :=
    hsyl.eq_of_le (le_inf hRS hRL) inf_le_right (hcfg.S_isPGroup.to_inf_left)
  have h3 : L ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxR : x ∈ thompsonJ S := by
      rw [← hSL]
      exact ⟨hx.2.1, hx.1⟩
    have : x ∈ thompsonJ S ⊓ F := ⟨hxR, hx.2⟩
    rwa [h1] at this
  have h4 : H = L ⊔ F := by
    refine le_antisymm ?_ (sup_le hcfg.L_le_H (inf_le_left.trans hcfg.S_le_H))
    rw [hcfg.H_eq]
    refine sup_le le_sup_left ?_
    rw [← h2]
    exact sup_le (hRL.trans le_sup_left) le_sup_right
  exact ⟨hQL.trans hUH, h1, h2, h3, h4⟩

theorem lemma2_4_12_one (h8 : Lemma2_4_8) :
    Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
      ∀ B : Subgroup G, Lin2BProps T S (thompsonJ S) D B →
        IsCyclic ↥(S ⊓ Subgroup.normalizer (B : Set G)) ∧
          thompsonJ S ⊓ (S ⊓ Subgroup.normalizer (B : Set G)) = ⊥ ∧
          thompsonJ S ⊔ (S ⊓ Subgroup.normalizer (B : Set G)) = S ∧
          L ⊓ (S ⊓ Subgroup.normalizer (B : Set G)) = ⊥ ∧
          H = L ⊔ (S ⊓ Subgroup.normalizer (B : Set G)) := by
  intro G _ _ T M H S L D n hcfg B hB
  obtain ⟨hQL, h1, h2, h3, h4⟩ := complement_facts h8 hcfg hB
  exact ⟨hcfg.isCyclic_of_complement hQL (hcfg.S_isPGroup.to_le inf_le_left)
    (by rw [inf_comm]; exact h3) h4, h1, h2, h3, h4⟩

theorem lemma2_4_12_of (h8 : Lemma2_4_8) (h2 : Lemma2_4_12_two) : Lemma2_4_12 :=
  fun G _ _ T M H S L D n hcfg B hB =>
    ⟨lemma2_4_12_one h8 G T M H S L D n hcfg B hB, fun f hf hf1 hf2 => by
      obtain ⟨hQL, -, -, h3, h4⟩ := complement_facts h8 hcfg hB
      exact ⟨hcfg.even_of_involution hQL (hcfg.S_isPGroup.to_le inf_le_left)
        (by rw [inf_comm]; exact h3) h4 hf hf1 hf2, h2 G T M H S L D n hcfg B hB f hf hf1 hf2⟩⟩

end CFSG.QuasithinUnique.Lin2
