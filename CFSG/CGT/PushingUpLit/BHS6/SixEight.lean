module

public import CFSG.CGT.PushingUpLit.BHS6.SixEightFamily
public import CFSG.CGT.PushingUpLit.BHS6.SixEightInput
public import CFSG.CGT.PushingUpLit.BHS6.SixEightGen

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem six_eight {G T : Subgroup Γ} (hG : CharTwo G) (hT : IsSylowOf 2 T G) :
    ∀ E : Subgroup Γ, E ∈ btBlocks G T → (∃ m : ℕ, 1 ≤ m ∧ IsNaturalAltModule ↥E m) →
      ¬ E ≤ cStarIn G T →
        ∃ F : Subgroup Γ, F ∈ btBlocks G T ∧ F ≤ E ∧ ¬ F ≤ cStarIn G T ∧
          IsNaturalAltModule ↥F 1 := by
  intro E hE ⟨m, hm, hn⟩ hEC
  have hE' : IsBTBlock G T E := hE
  obtain ⟨M, S, T', hMW, hS, hs, hc, hne, hSY, hy₀, hsurj, hpar⟩ :=
    exists_altSetup hG hT hE' hm hn
  have hEG : E ≤ G := hE'.le
  have hBN : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE'
  have hBW : baum T ≤ Subgroup.normalizer (M.W : Set Γ) := by
    rw [hMW]
    exact hBN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  by_contra hcon
  have hnob : ∀ F : Subgroup Γ, IsBTBlock G T F → F ≤ E → ¬ F ≤ cStarIn G T →
      ¬ IsNaturalAltModule ↥F 1 := fun F hF hFE hFC hF1 => hcon ⟨F, hF, hFE, hFC, hF1⟩
  let H : Subgroup (Equiv.Perm (Fin (2 * m + 1))) :=
    ((E ⊓ cStarIn G T).subgroupOf E).map M.Ψ
  have hHcyc : ∀ t ∈ T', ∀ x, t x ≠ x → ∀ c, (∀ t' ∈ T', t' c = c) → cyc x (t x) c ∈ H := by
    intro t ht x hx c hc'
    rcases M.exists_block_or_mem_cStar hEG hBN hBW S hS hs hc hSY hy₀ hsurj ht hx hc' with
      ⟨F, hF, hFE, hFC, hF1⟩ | ⟨g, hgC, hgd⟩
    · exact absurd hF1 (hnob F hF hFE hFC)
    · exact ⟨g, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.2 ⟨g.2, hgC⟩), hgd⟩
  have hfix : ∃ c, ∀ t ∈ T', t c = c := exists_fixed_of_swaps ⟨m, rfl⟩ hs hc
  have hAlt : alternatingGroup (Fin (2 * m + 1)) ≤ H :=
    alternatingGroup_le_of_cyc_mem H hs hc hne hfix hHcyc
  have hWT : M.W ≤ T := by
    rw [hMW]
    exact pCoreOf_le_sylow hG hT hE' hT
  have hWC : M.W ≤ cStarIn G T := fun w hw => by
    refine centralizer_le_cStarIn G T (Subgroup.mem_inf.2
      ⟨(isSylowTwoOf_of_isSylowOf hT).1 (hWT hw), ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (C1GN.omegaOneCenterOf_le_centerOf T hz).2 w
      (hWT hw)).symm
  apply hEC
  intro e he
  obtain ⟨h, hh, hhe⟩ := hAlt (hpar ⟨e, he⟩)
  have hker : M.Ψ (⟨e, he⟩ * h⁻¹) = 1 := by
    rw [map_mul, map_inv, hhe, mul_inv_cancel]
  have hWm : ((⟨e, he⟩ * h⁻¹ : ↥E) : Γ) ∈ M.W := (M.mem_W_iff _).2 hker
  have h1 : e = ((⟨e, he⟩ * h⁻¹ : ↥E) : Γ) * (h : Γ) :=
    (inv_mul_cancel_right e (h : Γ)).symm
  rw [h1]
  exact (cStarIn G T).mul_mem (hWC hWm) (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hh)).2

end CFSG.CGT.PushingUpLit.BHS6
