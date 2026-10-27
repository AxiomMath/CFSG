module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Acc
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3F
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

namespace Lin2Hyp

section Inv

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

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
    exact (E.R_lt_S hcfg).ne hRFS
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

theorem exists_F : ∃ F : Subgroup G, IsCyclic ↥F ∧ F ≤ S ∧ thompsonJ S ⊓ F = ⊥ ∧
    thompsonJ S ⊔ F = S ∧
    (∀ f ∈ F, f ≠ 1 → f ^ 2 = 1 → ∀ r ∈ thompsonJ S, (f * r) ^ 2 = 1 →
      ∃ c ∈ thompsonJ S, c⁻¹ * f * c = f * r) := by
  obtain ⟨B, hB⟩ := E.exists_B hcfg
  obtain ⟨⟨hFcyc, hRF, hRFS, -, -⟩, hf⟩ := E.h12 G T M H S L D n hcfg B hB
  refine ⟨S ⊓ Subgroup.normalizer (B : Set G), hFcyc, inf_le_left, hRF, hRFS, ?_⟩
  intro f hfF hf1 hf2 r hr hr2
  obtain ⟨-, hfus, -⟩ := hf f hfF hf1 hf2
  exact hfus r hr hr2

theorem T_eq_sup_centralizer {s : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1) :
    T = thompsonJ S ⊔ (T ⊓ Subgroup.centralizer ({s} : Set G)) := by
  obtain ⟨F, hcyc, hFS, hRF, hRFS, hfus⟩ := E.exists_F hcfg
  exact eq_sup_centralizer_involution (thompsonJ_le_self S) hcfg.S_le_T (E.TnS hcfg) (E.TnR hcfg)
    hFS hcyc hRF hRFS hfus hs hsR hs2

theorem exists_mem_T_centralizer_not_mem_S {s : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S)
    (hs2 : s ^ 2 = 1) : ∃ x ∈ T ⊓ Subgroup.centralizer ({s} : Set G), x ∉ S :=
  exists_mem_centralizer_not_mem (thompsonJ_le_self S) hcfg.S_ne_T hcfg.S_le_T
    (E.T_eq_sup_centralizer hcfg hs hsR hs2)

end Inv

end Lin2Hyp

end CFSG.QuasithinUnique.Lin2
