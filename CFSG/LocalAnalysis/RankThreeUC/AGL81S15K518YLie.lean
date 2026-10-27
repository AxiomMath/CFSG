module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K518YCover
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Engine
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.ChevThree
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K518YLayer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN CFSG.AGLEmbedding

variable {X : Type} [Group X] [Finite X]

theorem exists_minOverBorel_le_gnA (hG : KFactChevGenThree) {T T₁ T₂ : Subgroup X}
    (hX : GNSetting X T) (hpar : GNParabolic T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : GNYComponent T T₁ T₂ Ls) (hcl : IsClassicalTwoOrG2 (↥Ls ⧸ Subgroup.center ↥Ls)) :
    (∃ P, IsMinOverBorel Ls (gnImg T T ⊓ Ls) P ∧ pElementSubgroup 2 P ≤ gnA T T₁ Ls) ∧
      (∃ P, IsMinOverBorel Ls (gnImg T T ⊓ Ls) P ∧ pElementSubgroup 2 P ≤ gnA T T₂ Ls) := by
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (gnImg T T ⊓ Ls) Ls :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf hX.sylow
      hLs.1.2.1
  obtain ⟨Ps, hPs, hgen, -⟩ := hG _ Ls (gnImg T T ⊓ Ls) hLs.1.2.2 hcl hS
  have hcov : ParabolicCover T T₁ T₂ Ls := fun P hP =>
    hpar Ls hLs.1 (isChevTwo_of_classicalTwoOrG2 hcl) P hP
  obtain ⟨⟨P₁, hP₁, h₁⟩, ⟨P₂, hP₂, h₂⟩⟩ := exists_parabolic_le_gnA hLs hcov hPs hgen
  exact ⟨⟨P₁, hPs P₁ hP₁, h₁⟩, ⟨P₂, hPs P₂ hP₂, h₂⟩⟩

theorem mem_sup_centralizer_of_classical (hG : KFactChevGenThree) (hO : KFact518Out)
    {T T₁ T₂ : Subgroup X} (hX : GNSetting X T) (hg : GNGood T T₁ T₂) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    (m1 : mS T T₁ p Ls = 1) (m2 : mS T T₂ p Ls = 1) (n1 : mN T₁ p = 1) (n2 : mN T₂ p = 1)
    (hn : Ls.Normal) (hcl : IsClassicalTwoOrG2 (↥Ls ⧸ Subgroup.center ↥Ls))
    (hr : ¬ RankOneChevTwo (↥Ls ⧸ Subgroup.center ↥Ls)) {x : X}
    (hxp : ∃ k : ℕ, orderOf x = p ^ k)
    (hxT : x ∈ Subgroup.centralizer (T₁ : Set X) ∨ x ∈ Subgroup.normalizer (T₂ : Set X)) :
    toStar T x ∈ Ls ⊔ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) := by
  have hZ := not_dvd_card_center_of_mS hg.centre hLs hinv hp m1 m2
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (gnImg T T ⊓ Ls) Ls :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf hX.sylow
      hLs.1.2.1
  have hNL : ∀ N : Subgroup (X ⧸ gnC T), N ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) := by
    haveI := hn
    intro N
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨k, hk⟩ := hxp
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1
    (hk ▸ orderOf_map_dvd (toStar T) x : orderOf (toStar T x) ∣ p ^ k)
  have key : ∀ Ti : Subgroup X, ∀ P, IsMinOverBorel Ls (gnImg T T ⊓ Ls) P →
      pElementSubgroup 2 P ≤ gnA T Ti Ls → mS T Ti p Ls = 1 → mN Ti p = 1 →
      x ∈ Subgroup.normalizer (Ti : Set X) →
      toStar T x ∈ Ls ⊔ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) := by
    intro Ti P hP hPA hm hN hx
    have hrank : CFSG.Open.pRank p (gnImg T (Subgroup.normalizer (Ti : Set X))) ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ CFSG.Open.pRank p (gnImg T (Subgroup.normalizer (Ti : Set X))) := by omega
      have h3 := two_le_pRank_of_map (QuotientGroup.mk' (gnC T)) hp hp2
        (Subgroup.normalizer (Ti : Set X)) h2
      have hN' : CFSG.Open.pRank p (Subgroup.normalizer (Ti : Set X)) = 1 := hN
      omega
    exact hO (X ⧸ gnC T) Ls (gnImg T (Subgroup.normalizer (Ti : Set X))) (gnImg T T ⊓ Ls) P
      hLs.1 hcl hr (hNL _) hS hP (hPA.trans inf_le_left) p hp hp2 hZ (dvd_card_gnA_of_mS hp hm)
      hrank (toStar T x) (Subgroup.mem_map_of_mem _ hx) ⟨j, hj⟩
  obtain ⟨⟨P₁, hP₁, h₁⟩, ⟨P₂, hP₂, h₂⟩⟩ := exists_minOverBorel_le_gnA hG hX hg.parabolic hLs hcl
  rcases hxT with h | h
  · exact key T₁ P₁ hP₁ h₁ m1 n1 (Subgroup.centralizer_le_normalizer _ h)
  · exact key T₂ P₂ hP₂ h₂ m2 n2 h

end CFSG.LocalAnalysis.RankThreeUC.S15
