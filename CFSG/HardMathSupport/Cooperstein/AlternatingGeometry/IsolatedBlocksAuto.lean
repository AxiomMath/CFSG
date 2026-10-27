module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.IsolatedBlocksFalse
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.IsoBlocksFixed
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaSRange

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Quasithin.A4 CFSG.Open
  CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
  CFSG.RankThree.PartTwo CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem false_of_iso_blocks {S L : Subgroup G}
    (hA : Asc81bHyp (L ⊔ S) S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) {d : ℕ} (hd : 5 ≤ d)
    (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hπ : Function.Surjective π)
    (hker : π.ker =
      (⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅blockV S L, L⁆)
    (hAlt : ∀ σ ∈ alternatingGroup (Fin d),
      ∃ l : ↥L, θ ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ = σ)
    (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hθV : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    (hD : EOffenderData S (blockV S L))
    {ι : Type} [Fintype ι] [DecidableEq ι] (a a' : ι → Fin d)
    (hIso : IsoBlocks (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) a a')
    (hι : Fintype.card ι = 3 ∨ 5 ≤ Fintype.card ι)
    (hne' : ⁅omegaOneCenterOf (thompsonJ S), S⁆ ≠ ⊥) : False := by
  classical
  set W : Subgroup (Perm (Fin d)) := ((thompsonJ S).subgroupOf (L ⊔ S)).map θ with hW
  set Sstar : Subgroup (Perm (Fin d)) := (S.subgroupOf (L ⊔ S)).map θ with hSstar
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  have hSN : ∀ s ∈ Sstar, s ∈ Subgroup.normalizer (W : Set (Perm (Fin d))) :=
    fun s hs => theta_S_le_normalizer hA le_sup_right θ W rfl hs
  have hSstar2 : IsPGroup 2 Sstar := (hS2.comap_subtype (K := L ⊔ S)).map θ
  have hrange : ∀ i j : ι, i ≠ j → rigidSwap a a' i j ∈ θ.range := by
    intro i j hij
    have hsgn : rigidSwap a a' i j ∈ alternatingGroup (Fin d) := by
      obtain ⟨d1, d2, d3, d4⟩ := hIso.disj i j hij
      rw [mem_alternatingGroup, rigidSwap, map_mul, sign_swap d1, sign_swap d4]
      rfl
    obtain ⟨l, hl⟩ := hAlt _ hsgn
    exact ⟨_, hl⟩
  have hSnorm : ∀ i j : ι, i ≠ j → ∀ s ∈ Sstar,
      rigidSwap a a' i j * s * (rigidSwap a a' i j)⁻¹ ∈ Sstar :=
    fun i j hij s hs => theta_S_conj_mem hA le_sup_right θ hθS W rfl
      (hIso.rigidSwap_mem_normalizer hij) (hrange i j hij) hs
  have hfixed := iso_blocks_fixed hIso hι hSN hSnorm hSstar2
  have hcard : Fintype.card (Fin 3) ≤ Fintype.card ι := by simp; omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine false_of_isolated_blocks hA hSL hperf hd π θ hπ hker hAlt hequiv hθV hθS hD
    (fun i => a (e i)) (fun i => a' (e i)) (fun i => hIso.ne _)
    (fun i j hij => hIso.disj _ _ (fun h => hij (e.injective h))) ?_ ?_ hne'
  · intro i
    obtain ⟨j, hj, hθj⟩ := hIso.swap_mem (e i)
    exact ⟨j, Subgroup.mem_subgroupOf.1 hj, hθj⟩
  · intro s hs i
    have hsS : θ s ∈ Sstar := ⟨s, Subgroup.mem_subgroupOf.2 hs, rfl⟩
    have hfx := hfixed _ hsS (e i)
    have hbm := hIso.blk_map (hSN _ hsS) (e i)
    obtain ⟨j', hj'⟩ := hbm
    have hjj : j' = e i := by
      refine hIso.blk_inj (x := θ s (a (e i))) ?_ ?_
      · rcases hj' with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact Or.inl h1
        · exact Or.inr h1
      · exact hfx
    subst hjj
    refine ⟨hfx, ?_⟩
    rcases hj' with ⟨-, h2⟩ | ⟨-, h2⟩
    · right; exact h2
    · left; exact h2

theorem false_of_isoPairs {S L : Subgroup G}
    (hA : Asc81bHyp (L ⊔ S) S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) {d : ℕ} (hd : 5 ≤ d)
    (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hπ : Function.Surjective π)
    (hker : π.ker =
      (⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅blockV S L, L⁆)
    (hAlt : ∀ σ ∈ alternatingGroup (Fin d),
      ∃ l : ↥L, θ ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ = σ)
    (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hθV : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    (hD : EOffenderData S (blockV S L))
    (hcount : Nat.card {x : Fin d // ∃ y, x < y ∧
        IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) x y} = 3 ∨
      5 ≤ Nat.card {x : Fin d // ∃ y, x < y ∧
        IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) x y})
    (hne' : ⁅omegaOneCenterOf (thompsonJ S), S⁆ ≠ ⊥) : False := by
  classical
  obtain ⟨a, a', hIso⟩ := exists_isoBlocks (((thompsonJ S).subgroupOf (L ⊔ S)).map θ)
  refine false_of_iso_blocks hA hSL hperf hd π θ hπ hker hAlt hequiv hθV hθS hD a a' hIso ?_ hne'
  rwa [← Nat.card_eq_fintype_card]

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
