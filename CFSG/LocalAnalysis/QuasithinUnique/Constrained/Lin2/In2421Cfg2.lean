module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3F
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Orders
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Hyp

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

namespace Lin2Hyp0

section Plain

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem R_le_normalizer_Z {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S)) :
    thompsonJ S ≤ Subgroup.normalizer (Z : Set G) := fun _ hc =>
  Subgroup.centralizer_le_normalizer (Z : Set G) (lin2Z_centralized E.h16 hcfg hZ hc)

theorem conj_involution_mem {s x : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1)
    (hx : x ∈ T) :
    x * s * x⁻¹ ∈ S ∧ x * s * x⁻¹ ∉ thompsonJ S ∧ (x * s * x⁻¹) ^ 2 = 1 := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp (E.TnS hcfg hx) s).mp hs, fun h => hsR ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (E.TnR hcfg hx) s).mpr h
  · have : (x * s * x⁻¹) ^ 2 = x * s ^ 2 * x⁻¹ := by simp only [pow_two]; group
    rw [this, hs2]; simp

end Plain

section WithRS

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D) (hRlt : thompsonJ S < S)

include E hcfg hRlt

theorem exists_f₀ : ∃ f₀ : G, f₀ ∈ S ∧ f₀ ∉ thompsonJ S ∧ f₀ ^ 2 = 1 ∧ Even n ∧
    (∀ s ∈ S, s ∉ thompsonJ S → s ^ 2 = 1 → ∃ c ∈ thompsonJ S, c⁻¹ * f₀ * c = s) ∧
    Nat.card ((lin2Z L (thompsonJ S) ⊓ Subgroup.centralizer ({f₀} : Set G) : Subgroup G)) =
      2 ^ (n / 2) ∧
    (centerOf L = ⊥ →
      Nat.card ((thompsonJ S ⊓ Subgroup.centralizer ({f₀} : Set G) : Subgroup G)) =
        2 ^ (3 * n / 2)) ∧
    (centerOf L ≠ ⊥ →
      Nat.card ((thompsonJ S ⊓ Subgroup.centralizer ({f₀} : Set G) : Subgroup G)) =
        2 ^ (2 * n)) ∧
    ((∃ m : ℕ, n = 2 * m ∧ 1 < m ∧ IsShort2 (L ⊓ Subgroup.centralizer ({f₀} : Set G)) ∧
          IsLin2Type (L ⊓ Subgroup.centralizer ({f₀} : Set G)) m ∧
          blockU L ⊓ Subgroup.centralizer ({f₀} : Set G) =
            blockU (L ⊓ Subgroup.centralizer ({f₀} : Set G)) ∧
          pCoreOf 2 (L ⊓ Subgroup.centralizer ({f₀} : Set G)) =
            blockU L ⊓ Subgroup.centralizer ({f₀} : Set G)) ∨
        (n = 2 ∧
          ((centerOf L = ⊥ ∧
              Nonempty ((L ⊓ Subgroup.centralizer ({f₀} : Set G) : Subgroup G) ≃*
                Equiv.Perm (Fin 4)) ∧
              pCoreOf 2 (L ⊓ Subgroup.centralizer ({f₀} : Set G)) =
                blockU L ⊓ Subgroup.centralizer ({f₀} : Set G)) ∨
            (centerOf L ≠ ⊥ ∧
              Nonempty ((L ⊓ Subgroup.centralizer ({f₀} : Set G) : Subgroup G) ≃*
                Equiv.Perm (Fin 4) × Multiplicative (ZMod 2)) ∧
              pCoreOf 2 (L ⊓ Subgroup.centralizer ({f₀} : Set G)) =
                blockU L ⊓ Subgroup.centralizer ({f₀} : Set G))))) := by
  obtain ⟨B, hB⟩ := E.exists_B hcfg
  obtain ⟨⟨hFcyc, hRF, hRFS, -, -⟩, hf⟩ := E.h12 G T M H S L D n hcfg B hB
  set F := S ⊓ Subgroup.normalizer (B : Set G) with hF
  have hFS : F ≤ S := inf_le_left
  have hRS : thompsonJ S ≤ S := thompsonJ_le_self S
  have hSR : S ≤ Subgroup.normalizer (thompsonJ S : Set G) := hcfg.S_le_T.trans (E.TnR hcfg)
  have hF2 : IsPGroup 2 F := hcfg.cs.sylow.isPGroup.to_le hFS
  have hFbot : F ≠ ⊥ := by
    intro h
    rw [h, sup_bot_eq] at hRFS
    exact hRlt.ne hRFS
  obtain ⟨f₀, hf₀F, hf₀2, hf₀1⟩ := exists_involution_of_isPGroup hF2 hFbot
  have hfus : ∀ f ∈ F, f ≠ 1 → f ^ 2 = 1 → ∀ r ∈ thompsonJ S, (f * r) ^ 2 = 1 →
      ∃ c ∈ thompsonJ S, c⁻¹ * f * c = f * r := fun f hfF hf1 hf2 r hr hr2 => by
    obtain ⟨-, hfus, -⟩ := hf f hfF hf1 hf2
    exact hfus r hr hr2
  obtain ⟨hev, -, hblk, hcardZ, hR1, hR2⟩ := hf f₀ hf₀F hf₀1 hf₀2
  have hf₀R : f₀ ∉ thompsonJ S := by
    intro h
    have : f₀ ∈ thompsonJ S ⊓ F := ⟨h, hf₀F⟩
    rw [hRF] at this
    exact hf₀1 (by simpa using this)
  refine ⟨f₀, hFS hf₀F, hf₀R, hf₀2, hev, ?_, hcardZ, hR1, hR2, hblk⟩
  intro s hs hsR hs2
  have h := exists_conj_involutions hSR hFS hFcyc hRF hRFS hfus (hFS hf₀F) hf₀R hf₀2 hs hsR hs2
  exact h

theorem card_Z_inf_centralizer {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S)) {s : G}
    (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1) :
    Nat.card (Z ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) = 2 ^ (n / 2) := by
  obtain ⟨f₀, -, -, -, -, hconj, hcZ, -⟩ := E.exists_f₀ hcfg hRlt
  obtain ⟨c, hc, rfl⟩ := hconj s hs hsR hs2
  rw [card_inf_centralizer_conj (E.R_le_normalizer_Z hcfg hZ hc), hZ]
  exact hcZ

end WithRS

end Lin2Hyp0

end CFSG.QuasithinUnique.Lin2
