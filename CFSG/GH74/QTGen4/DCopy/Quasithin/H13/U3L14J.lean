module

public import CFSG.Quasithin.H13.U3L14J
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem reduced_K_F4 (h1332 : Stmt13_3_2_F4) {K : Subgroup G} (hfK : quasithinIsFaithfulLocal T K)
    (hq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K)) :
    ¬ K ≤ centralizer (reducedAggregate (K ⊔ T) : Set G) ∧
      T ⊓ centralizer (reducedAggregate (K ⊔ T) : Set G) = pCoreOf 2 (K ⊔ T) := by
  obtain ⟨-, -, ⟨⟨VK, hVK⟩, -⟩, -⟩ := h1332 G T L S.h13 K hfK
  have hloc := hfK.1
  have hKc : K ∈ cComp (K ⊔ T) := hloc.2.1
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hloc.1, hloc.2.2.1⟩
  have hred := isTwoReducedIn_reducedAggregate (K ⊔ T)
  have hKV : ¬ K ≤ centralizer (reducedAggregate (K ⊔ T) : Set G) := by
    intro hle
    have hVKc : K ≤ centralizer (VK : Set G) := hle.trans (centralizer_le hVK.1)
    have h1 : ⁅VK, K⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hVKc)
    exact hVK.2.1 (hVK.2.2.2.1.symm.trans h1)
  exact ⟨hKV, (Ch3Sec3.centralizer_reduced_of_cComp hKc hq hTsyl hred hKV).2.1⟩

theorem hyp318_K_F4 (h1332 : Stmt13_3_2_F4) {K : Subgroup G} (hfK : quasithinIsFaithfulLocal T K)
    (hq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K))
    (hne : ∃ H : Subgroup G, IsHStar T (normalizer (K : Set G)) H) :
    Hyp318 T (normalizer (K : Set G)) K (reducedAggregate (K ⊔ T)) := by
  obtain ⟨-, ⟨hTK, -, hMK, huniq⟩, -, -⟩ := h1332 G T L S.h13 K hfK
  have hKc : K ∈ cComp (K ⊔ T) := hfK.1.2.1
  have hred := isTwoReducedIn_reducedAggregate (K ⊔ T)
  have hcen := (S.reduced_K_F4 h1332 hfK hq).2
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKc
  exact
    { inM := ⟨hMK, hTK⟩
      nonempty := hne
      perfect := le_antisymm (perfect_le_oTwoUpper le_rfl (Subgroup.isPerfect_iff.2 hperf))
        (oTwoUpper_le K)
      le_M := le_normalizer
      normal := le_rfl
      unique := ⟨⟨hMK, sup_le le_normalizer hTK⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
      reduced := hred
      centralizer := hcen.symm }

theorem ff_K_F4 (h1332 : Stmt13_3_2_F4) (hC58 : TheoremC58) (h317 : AS317Sylow) {K : Subgroup G}
    (hfK : quasithinIsFaithfulLocal T K)
    (hq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K))
    (hHK : A6.g1 T V ≤ normalizer (K : Set G))
    (hL2K : ¬ L₁Of L V₂ ≤ normalizer (K : Set G)) :
    ¬ thompsonJ T ≤ T ⊓ centralizer (reducedAggregate (K ⊔ T) : Set G) ∧
      IsFFInt (K ⊔ T) (reducedAggregate (K ⊔ T))
        (isTwoReducedIn_reducedAggregate (K ⊔ T)).2.2.1 := by
  obtain ⟨H, hH, -, hHZ⟩ := S.exists_hStar_K hHK hL2K
  have h318 := S.hyp318_K_F4 h1332 hfK hq ⟨H, hH⟩
  rcases theorem318_three hC58 h317 S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow h318
    with h | ⟨-, hZ, -⟩
  · exact h
  · exfalso
    apply hHZ
    intro x hx
    rw [mem_centralizer_iff]
    intro z hz
    exact ((mem_centralizer_iff.1 ((hZ H hH hz).2)) x hx).symm

end Set14

end CFSG.Quasithin.H13.U3
