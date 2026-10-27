module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenNotSylow
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenRadOne
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenSolvC126
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenType
import CFSG.Quasithin.Background.C126NatClassG
public import CFSG.Quasithin.Background.C118WeakPair

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B2F CFSG.Quasithin.E2
  CFSG.Quasithin.B6 CFSG.Quasithin.C126.Nat

variable {G : Type} [Group G] [Finite G]

theorem single_block_aux_gen {P S MP V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : MinParabolic P S MP) (hPN : P ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hV)))} (hKJ : twoResidual P ≤ thompsonJ P)
    (hne : I.Nonempty) (hJeq : autI hV (thompsonJ P) = ⨆ L ∈ I, L)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (htrans : ∀ L ∈ I, ∀ L' ∈ I, ∃ t ∈ autI hV S, B1.conjAut t L = L')
    (hSb : autI hV S = autI hV (thompsonJ S)) :
    ∃ L, I = {L} ∧ autI hV P = L := by
  have hSP : S ≤ P := h.isSylow.1
  have hSJ : autI hV S ≤ ⨆ L ∈ I, L :=
    hSb ▸ ((autI_mono hV (B6.thompsonJ_le_of_sylow h.isSylow)).trans hJeq.le)
  obtain ⟨L, hI⟩ := exists_eq_singleton_of_transitive hne hcomm hSJ htrans
  refine ⟨L, hI, ?_⟩
  have hJL : autI hV (thompsonJ P) = L := by simpa [hI] using hJeq
  apply le_antisymm
  · rw [← sup_twoResidual_eq h.isSylow,
      autI_sup hV (hSP.trans hPN) ((twoResidual_le P).trans hPN)]
    refine sup_le ?_ ?_
    · rw [hSb]
      exact (autI_mono hV (B6.thompsonJ_le_of_sylow h.isSylow)).trans hJL.le
    · exact (autI_mono hV hKJ).trans hJL.le
  · rw [← hJL]
    exact autI_mono hV (B6.thompsonJ_le P)

theorem exists_single_block_e23_gen {P S MP V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : MinParabolic P S MP) (hS : baum S = S) (hPN : P ≤ Subgroup.normalizer (V : Set G))
    (hc : E23ConclGen P S V hV) :
    ∃ (L : Subgroup (MulAut (IntMod V hV))) (n : ℕ),
      autI hV P = L ∧ IsL2Natural L (fixV (autI hV (twoResidual P))) n := by
  obtain ⟨hKJ, I, hne, hJeq, hcomm, htrans, htype, h2, h3⟩ := hc
  have htrans' : ∀ L ∈ I, ∀ L' ∈ I, ∃ t : MulAut (IntMod V hV), B1.conjAut t L = L' :=
    fun L hL L' hL' => (htrans L hL L' hL').imp fun t ht => ht.2
  rcases uniform_type htrans' htype with hall | ⟨m, hm, hall⟩
  · obtain ⟨hSb, -⟩ := h2 hall
    rw [hS] at hSb
    obtain ⟨L, hI, hPL⟩ := single_block_aux_gen hV h hPN hKJ hne hJeq hcomm htrans hSb
    obtain ⟨n, hn⟩ := hall L (hI ▸ Finset.mem_singleton_self L)
    exact ⟨L, n, hPL, hn⟩
  · exfalso
    obtain ⟨hSb, -, hcl⟩ := h3 m hm hall
    rw [hS] at hSb
    obtain ⟨L, hI, hPL⟩ := single_block_aux_gen hV h hPN hKJ hne hJeq hcomm htrans hSb
    have hsyl := isSylowTwoOf_autI hV hPN h.isSylow
    have hTst : IsPGroup 2 (autI hV S) := hsyl.2.1
    rw [hSb, hPL] at hsyl
    obtain ⟨θ, -, -, hθ⟩ := hcl L (hI ▸ Finset.mem_singleton_self L)
    have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    exact not_isSylowTwoOf_swaps (by omega : 4 ≤ 2 ^ m + 1) θ hTst hθ hsyl

theorem e23ConclGen_of_inputs (hE : E23NonsolvGen) {H T M : Subgroup G}
    (hV : IsElemAbelian 2 (VZ T H)) (hmin : MinParabolic H T M) (hF : CharTwo H)
    (hred : IsTwoReducedIn H (VZ T H))
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G)) :
    E23ConclGen H T (VZ T H) hV := by
  by_cases hsolv : Group.IsSolvable H
  · exact e23ConclGen_of_isSolvable hV hmin hsolv hred hJ
  · exact ⟨twoResidual_le_thompsonJ hmin hred hJ, hE G H T M hV hmin hF hred hJ hsolv⟩

theorem inClassG_of_e23_gen (hE : E23NonsolvGen) {P S MP : Subgroup G}
    (h : MinParabolic P S MP) (hF : CharTwo P) (hS : baum S = S)
    (hJ : ¬ thompsonJ S ≤ Subgroup.centralizer (VZ S P : Set G)) : InClassG P S := by
  obtain ⟨-, hVel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo h.isSylow hF (le_refl _)
  have hc := e23ConclGen_of_inputs hE hVel h hF hred hJ
  have hPN : P ≤ Subgroup.normalizer (VZ S P : Set G) := hred.2.1
  obtain ⟨L, n, hPL, hnat⟩ := exists_single_block_e23_gen hVel h hS hPN hc
  by_cases hn : 2 ≤ n
  · exact ⟨h.isSylow, hF, (minParabolic_iff.1 h).1,
      hasNaturalFstar_of_single_block hVel hPN hPL hn hnat⟩
  · have hn1 : n = 1 := by
      obtain ⟨h1, -⟩ := hnat
      omega
    subst hn1
    obtain ⟨-, F, iF, iFin, hF2, e, -⟩ := hnat
    have hLsolv : Group.IsSolvable ↥L := by
      have hq : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card]; simpa using hF2
      have : Finite F := Finite.of_fintype F
      have hc6 : Nat.card ↥L = 6 := by
        rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
          hq]
        norm_num
      exact CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [hc6]; norm_num)
    have hUV : ¬ P ≤ Subgroup.centralizer (VZ S P : Set G) := fun hle =>
      hJ ((B6.thompsonJ_le S).trans (h.isSylow.1.trans hle))
    have hperf := perfectCore_le_centralizer_of_solvable hVel hPN (hPL ▸ hLsolv)
    have hsolv : Group.IsSolvable ↥P := C1Pack.isSolvable_of_perfectCore_le h hred hUV hperf
    exact inClassG_of_solvable_minParabolic_gen h hF hsolv hJ hS

theorem concl1Gen_of_natCase_core_weak (hE : E23NonsolvGen)
    {C₁ C₂ H T M V : Subgroup G} {hV : IsElemAbelian 2 V} (hP : IsC118WeakPair T C₁ C₂)
    (hmin : MinParabolic H T M) (hF : CharTwo H) (hred : IsTwoReducedIn H V)
    (hVZ : V = VZ T H) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hNat : NatCaseGen H T V hV)
    (hRF : ∀ {P : Subgroup G}, baum T ≤ P → P ≤ twoResidual H ⊔ baum T → ¬ P ≤ M →
      MinParabolic P (baum T) (P ⊓ M) → IsL2OrA3Block P (twoResidual P) →
      twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) :
    Concl1Gen C₁ C₂ H T := by
  subst hVZ
  have hT := hmin.isSylow
  obtain ⟨-, I, hFam, hn2⟩ := id hNat
  have hSyl : IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T) := by
    obtain ⟨-, -, -, -, -, h2, -⟩ := hFam
    exact (h2 fun L hL => (hn2 L hL).imp fun n h => h.2).2.2
  obtain ⟨P, hSP, hPK, hPM, hPT, hMinP, hFP, hJP⟩ :=
    C126.exists_minimal_parabolic_over_baum hmin hF hJ hSyl
  have hCls : InClassG P (baum T) := inClassG_of_e23_gen hE hMinP hFP (C1GN.baum_baum T) hJP
  obtain ⟨-, h1Z, -, h2B, h2char, -⟩ := id hP
  rcases hP.dichotomy hCls with h1 | h2 | h3
  · left
    have hC1T : C₁ ≤ centerOf T := h1Z.trans (C1GN.omegaOneCenterOf_le_centerOf T)
    have hHle : H ≤ Subgroup.centralizer (C₁ : Set G) := by
      rw [← hPT]
      refine sup_le (fun p hp => ?_) (fun t ht => ?_)
      · exact Subgroup.mem_centralizer_iff.2 fun c hc =>
          (Subgroup.mem_centralizer_iff.1 (h1 hc).2 p hp).symm
      · exact Subgroup.mem_centralizer_iff.2 fun c hc =>
          (Subgroup.mem_centralizer_iff.1 (hC1T hc).2 t ht).symm
    refine le_inf (fun c hc => hT.1 (hC1T hc).1) (fun c hc => ?_)
    exact Subgroup.mem_centralizer_iff.2 fun h hh =>
      (Subgroup.mem_centralizer_iff.1 (hHle hh) c hc).symm
  · right
    left
    have hTbaum : T ≤ Subgroup.normalizer (baum T : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
    have hTN : T ≤ Subgroup.normalizer (C₂ : Set G) :=
      hTbaum.trans (normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2char)
    rw [← hPT]
    exact sup_le h2 hTN
  · right
    right
    exact oneBlockGen_of_block hmin hF hred hJ hNat (hRF hSP hPK hPM hMinP h3) hSP hPK hPM hPT
      hMinP h3

theorem concl1Gen_of_natCase_single_weak (hE : E23NonsolvGen)
    {C₁ C₂ H T M V : Subgroup G} {hV : IsElemAbelian 2 V} (hP : IsC118WeakPair T C₁ C₂)
    (hmin : MinParabolic H T M) (hF : CharTwo H) (hred : IsTwoReducedIn H V)
    (hVZ : V = VZ T H) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hNat : NatCaseGen H T V hV)
    (hone : ∃ I, E23FamGen H T V hV I ∧
      (∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual H))) n) ∧
        I.card < 2) :
    Concl1Gen C₁ C₂ H T := by
  obtain ⟨I, hFam, hn2, hcard⟩ := hone
  have c := natCtxGen_of_fam hmin hF hred hJ hNat.1 hFam hn2
  exact concl1Gen_of_natCase_core_weak hE hP hmin hF hred hVZ hJ hNat
    fun hSP hPK hPM hMinP hBlk => radFree_of_natCtx_single c hcard hSP hPK hPM hMinP hBlk

end CFSG.AGLEmbeddingD2.GN
