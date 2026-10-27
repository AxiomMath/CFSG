module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2412f

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

@[expose] def Lin2BlockConcl {G : Type} [Group G] (L : Subgroup G) (f : G) (n : ℕ) : Prop :=
  (∃ m : ℕ, n = 2 * m ∧ 1 < m ∧ IsShort2 (L ⊓ Subgroup.centralizer ({f} : Set G)) ∧
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
            blockU L ⊓ Subgroup.centralizer ({f} : Set G))))

@[expose] def Lemma2_4_12_block : Prop :=
  Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
    ∀ B : Subgroup G, Lin2BProps T S (thompsonJ S) D B →
      ∀ f ∈ S ⊓ Subgroup.normalizer (B : Set G), f ≠ 1 → f ^ 2 = 1 → Lin2BlockConcl L f n

@[expose] def Lemma2_4_12_Zne1 : Prop :=
  Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
    ∀ B : Subgroup G, Lin2BProps T S (thompsonJ S) D B →
      ∀ f ∈ S ⊓ Subgroup.normalizer (B : Set G), f ≠ 1 → f ^ 2 = 1 → centerOf L ≠ ⊥ →
        (∀ r ∈ thompsonJ S, (f * r) ^ 2 = 1 → ∃ s ∈ thompsonJ S, s⁻¹ * f * s = f * r) ∧
        Nat.card ((lin2Z L (thompsonJ S) ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G)) =
          2 ^ (n / 2) ∧
        Nat.card ((thompsonJ S ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G)) =
          2 ^ (2 * n)

theorem lemma2_4_12_two_of (h8 : Lemma2_4_8) (hb : Lemma2_4_12_block) (hz : Lemma2_4_12_Zne1) :
    Lemma2_4_12_two := by
  intro G _ _ T M H S L D n hcfg B hB f hf hf1 hf2
  by_cases hc : centerOf L = ⊥
  · obtain ⟨h1, h2, h3, -⟩ := counts_Zeq1 h8 hcfg hB hc hf hf1 hf2
    exact ⟨h1, hb G T M H S L D n hcfg B hB f hf hf1 hf2, h2, fun _ => h3,
      fun h => absurd hc h⟩
  · obtain ⟨h1, h2, h3⟩ := hz G T M H S L D n hcfg B hB f hf hf1 hf2 hc
    exact ⟨h1, hb G T M H S L D n hcfg B hB f hf hf1 hf2, h2, fun h => absurd h hc,
      fun _ => h3⟩

end CFSG.QuasithinUnique.Lin2
