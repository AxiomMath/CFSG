module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenSolv
public import CFSG.Quasithin.Background.C126MinPar
public import CFSG.Quasithin.Background.C1PackC126Solv
public import CFSG.Quasithin.Background.C118WeakPair

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B2F CFSG.Quasithin.E2
  CFSG.Quasithin.B6
open scoped commutatorElement

theorem exists_eq_singleton_of_transitive {V : Type*} [CommGroup V]
    {I : Finset (Subgroup (MulAut V))} {A : Subgroup (MulAut V)} (hne : I.Nonempty)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hA : A ≤ ⨆ L ∈ I, L) (htrans : ∀ L ∈ I, ∀ L' ∈ I, ∃ t ∈ A, B1.conjAut t L = L') :
    ∃ L, I = {L} := by
  have hnorm : ∀ L ∈ I, (⨆ L' ∈ I, L') ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    intro L hL
    refine iSup₂_le fun L' hL' => ?_
    by_cases h : L' = L
    · rw [h]
      exact Subgroup.le_normalizer
    · exact le_normalizer_of_commute (hcomm L' hL' L hL h)
  obtain ⟨L₀, hL₀⟩ := hne
  refine ⟨L₀, Finset.eq_singleton_iff_unique_mem.2 ⟨hL₀, fun L hL => ?_⟩⟩
  obtain ⟨t, ht, htL⟩ := htrans L₀ hL₀ L hL
  have htn : t ∈ Subgroup.normalizer (L₀ : Set (MulAut V)) := hnorm L₀ hL₀ (hA ht)
  rw [← htL]
  ext x
  rw [B1.mem_conjAut]
  have h := Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem htn) x
  simpa using h.symm

section

variable {G : Type} [Group G] [Finite G]

theorem exists_single_block_gen {P S MP V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : MinParabolic P S MP) (hsolv : Group.IsSolvable ↥P) (hred : IsTwoReducedIn P V)
    (hJ : ¬ thompsonJ S ≤ Subgroup.centralizer (V : Set G)) (hS : baum S = S) :
    ∃ L : Subgroup (MulAut (IntMod V hV)), autI hV P = L ∧ ActsAsNaturalL2 L (commV L) := by
  classical
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  obtain ⟨𝓗, I, B⟩ := exists_blocks hV hred hsolv h.isSylow hJ
  have hSb := autI_baum_gen B h hsolv hred hJ
  rw [hS] at hSb
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hSP : S ≤ P := h.isSylow.1
  have hKJ : twoResidual P ≤ thompsonJ P := twoResidual_le_thompsonJ h hred hJ
  have hSJ : autI hV S ≤ ⨆ L ∈ I, L :=
    hSb ▸ ((autI_mono hV (B6.thompsonJ_le_of_sylow h.isSylow)).trans B.eq.le)
  obtain ⟨L, hI⟩ := exists_eq_singleton_of_transitive (B.nonempty h.isSylow hred hJ)
    (fun L hL L' hL' hne a ha b hb => B.comm hL hL' hne ha hb) hSJ
    (fun L hL L' hL' => B.transitive h hred hJ hL hL')
  have hLI : L ∈ I := hI ▸ Finset.mem_singleton_self L
  refine ⟨L, ?_, ?_⟩
  · have hJL : autI hV (thompsonJ P) = L := by simpa [hI] using B.eq
    apply le_antisymm
    · rw [← sup_twoResidual_eq h.isSylow,
        autI_sup hV (hSP.trans hPN) ((twoResidual_le P).trans hPN)]
      refine sup_le ?_ ?_
      · rw [hSb]
        exact (autI_mono hV (B6.thompsonJ_le_of_sylow h.isSylow)).trans hJL.le
      · exact (autI_mono hV hKJ).trans hJL.le
    · rw [← hJL]
      exact autI_mono hV (B6.thompsonJ_le P)
  · rw [commV_eq_commSub]
    exact actsAsNaturalL2_of_full hW (B.hb.card_comm L (B.sub hLI)) (B.hb.le_stabSub (B.sub hLI))
      (B.hb.inf_centSub (B.sub hLI)) (B.hb.autSub_eq_top L (B.sub hLI))

theorem inClassG_of_solvable_minParabolic_gen {P S MP : Subgroup G} (h : MinParabolic P S MP)
    (hF : CharTwo P) (hsolv : Group.IsSolvable ↥P)
    (hJ : ¬ thompsonJ S ≤ Subgroup.centralizer (VZ S P : Set G)) (hS : baum S = S) :
    InClassG P S := by
  obtain ⟨-, hVel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo h.isSylow hF (le_refl _)
  obtain ⟨L, hL, hnat⟩ := exists_single_block_gen hVel h hsolv hred hJ hS
  obtain ⟨hn1, -, -⟩ := C1Pack.isNatL2Section_fstarPre hVel hred.2.1 hL hnat
  exact ⟨h.isSylow, hF, (minParabolic_iff.1 h).1, 1, le_rfl, hn1⟩

theorem exists_a3Block_gen_weak {C₁ C₂ H T M : Subgroup G} (hP : IsC118WeakPair T C₁ C₂)
    (hmin : MinParabolic H T M) (hF : CharTwo H)
    (hsolv : perfectCore H ≤ Subgroup.centralizer (VZ T H : Set G))
    (hM' : (H ⊓ Subgroup.centralizer (C₁ : Set G)) ⊔ (H ⊓ Subgroup.normalizer (C₂ : Set G)) ≤ M)
    (h1 : ¬ C₁ ≤ centerOf H) (h2 : ¬ H ≤ Subgroup.normalizer (C₂ : Set G)) :
    ∃ K : Subgroup G, IsChi0Block H K ∧ IsAltType K 3 ∧ ⁅K, thompsonJ T⁆ = K ∧
      H = T ⊔ conjClosure K T := by
  have hT := hmin.isSylow
  obtain ⟨-, h1Z, -, h2B, h2char, -⟩ := id hP
  have hPM'_of : ∀ P : Subgroup G, P ≤ H →
      (C₁ ≤ centerOf P ∨ P ≤ Subgroup.normalizer (C₂ : Set G)) → P ≤ M := by
    intro P hPU h
    rcases h with h1 | h2
    · have hPC : P ≤ H ⊓ Subgroup.centralizer (C₁ : Set G) :=
        le_inf hPU fun u hu => Subgroup.mem_centralizer_iff.2 fun c hc =>
          (Subgroup.mem_centralizer_iff.1 (h1 hc).2 u hu).symm
      exact (hPC.trans le_sup_left).trans hM'
    · exact ((le_inf hPU h2).trans le_sup_right).trans hM'
  obtain ⟨-, hVel, hredU⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G)
  · rcases C1Pack.c126_case_B h1Z h2B h2char hmin hF hJ with h | h
    · exact absurd h h1
    · exact absurd h h2
  have hUV : ¬ H ≤ Subgroup.centralizer (VZ T H : Set G) := fun hle =>
    hJ ((B6.thompsonJ_le T).trans (hT.1.trans hle))
  have hsolvH : Group.IsSolvable ↥H := C1Pack.isSolvable_of_perfectCore_le hmin hredU hUV hsolv
  obtain ⟨𝓗, I, B⟩ := exists_blocks hVel hredU hsolvH hT hJ
  have hSyl := isSylowTwoOf_baum_gen B hmin hsolvH hredU hJ
  obtain ⟨P, hSP, hPY, hPM, hPT, hMinP, hFP, hJP⟩ :=
    C126.exists_minimal_parabolic_over_baum hmin hF hJ hSyl
  have hPU : P ≤ H := hPT ▸ le_sup_left
  have hsolvP : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPU)
  have hbb : baum (baum T) = baum T := C1GN.baum_baum T
  have hCls : InClassG P (baum T) :=
    inClassG_of_solvable_minParabolic_gen hMinP hFP hsolvP hJP hbb
  have hPnotM : ¬ P ≤ M := hPM
  rcases hP.dichotomy hCls with h1' | h2' | h3
  · exact absurd (hPM'_of P hPU (Or.inl h1')) hPnotM
  · exact absurd (hPM'_of P hPU (Or.inr h2')) hPnotM
  have hKblock : IsBlock2 P (twoResidual P) := h3.1
  have hKalt : IsAltType (twoResidual P) 3 :=
    C1Pack.isAltType_three_of_isBlock2_of_solvable hKblock hsolvP
  have hKP : twoResidual P ≤ P := twoResidual_le P
  have hKU : twoResidual P ≤ H := hKP.trans hPU
  have hKblockU : IsBlock2 H (twoResidual P) :=
    ⟨hKblock.1, hKU, C1Pack.isSubnormal_twoResidual_lift hmin hsolvH hSyl hSP hPY⟩
  have hJT : thompsonJ T ≤ P := (B6.thompsonJ_le_baum T).trans hSP
  have hKJ : ⁅twoResidual P, thompsonJ T⁆ = twoResidual P := by
    obtain ⟨-, hVel', hredP⟩ := conjClosure_isTwoReducedIn_of_charTwo hMinP.isSylow hFP
      (le_refl _)
    obtain ⟨L, hL, hnat⟩ := exists_single_block_gen hVel' hMinP hsolvP hredP hJP hbb
    obtain ⟨-, hKf, hcomm⟩ := C1Pack.isNatL2Section_fstarPre hVel' hredP.2.1 hL hnat
    have hJS : thompsonJ (baum T) = thompsonJ T :=
      B6.thompsonJ_eq_of_le (B6.thompsonJ_le_baum T) inf_le_left
    have hPV : ¬ P ≤ Subgroup.centralizer (VZ (baum T) P : Set G) := fun hle =>
      hJP ((B6.thompsonJ_le _).trans (hMinP.isSylow.1.trans hle))
    have hKC : ¬ twoResidual P ≤ Subgroup.centralizer (VZ (baum T) P : Set G) :=
      MinParabolic.not_twoResidual_le_centralizer hredP hPV
    obtain ⟨a, haJ, ha2, haC⟩ := C1Pack.exists_involution_not_mem_centralizer hJP
    rw [hJS] at haJ
    have hNC := hcomm (twoResidual P) (thompsonJ T) hKf hJT hKC ⟨a, haJ, ha2, haC⟩
    have hQK : pCoreOf 2 (twoResidual P) ≤ Subgroup.centralizer (VZ (baum T) P : Set G) :=
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKP)
        ((le_normalizer_twoResidual P).trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)).trans
        (MinParabolic.pCoreOf_le_centralizer hredP)
    have hNC' : ¬ ⁅twoResidual P, thompsonJ T⁆ ≤ pCoreOf 2 (twoResidual P) := fun hle =>
      hNC (hle.trans hQK)
    have hJN : thompsonJ T ≤ Subgroup.normalizer (twoResidual P : Set G) :=
      hJT.trans (le_normalizer_twoResidual P)
    have hNL : ⁅twoResidual P, thompsonJ T⁆ ≤ twoResidual P :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hJN
    have hLN : twoResidual P ≤ Subgroup.normalizer
        ((⁅twoResidual P, thompsonJ T⁆ : Subgroup G) : Set G) :=
      A3.le_normalizer_commutator_left _ _
    have hq : IsAltQuotient (twoResidual P) (pCoreOf 2 (twoResidual P)) 3 := by
      obtain ⟨α, hαs, hαk, -⟩ := hKalt
      exact ⟨α, hαs, by rw [hαk, C1Pack.pCoreOf_subgroupOf_self]⟩
    exact C1GN.isShort2_eq_of_isAltQuotient hKblock.1 (by decide) le_rfl hq hNL hLN hNC'
  have hUeq : H = T ⊔ conjClosure (twoResidual P) T := by
    apply le_antisymm
    · calc H = P ⊔ T := hPT.symm
        _ = (baum T ⊔ twoResidual P) ⊔ T := by rw [sup_twoResidual_eq hMinP.isSylow]
        _ ≤ T ⊔ conjClosure (twoResidual P) T :=
          sup_le (sup_le (inf_le_left.trans le_sup_left)
            ((le_conjClosure _ T).trans le_sup_right)) le_sup_left
    · refine sup_le hT.1 (conjClosure_le fun t ht z hz => ?_)
      exact H.mul_mem (H.mul_mem (hT.1 ht) (hKU hz)) (H.inv_mem (hT.1 ht))
  exact ⟨twoResidual P, ⟨hKblockU, Or.inr (Or.inl hKalt)⟩, hKalt, hKJ, hUeq⟩

theorem concl1Gen_of_perfectCore_le_weak {C₁ C₂ H T M : Subgroup G}
    (hP : IsC118WeakPair T C₁ C₂)
    (hmin : MinParabolic H T M) (hF : CharTwo H)
    (hsolv : perfectCore H ≤ Subgroup.centralizer (VZ T H : Set G)) : Concl1Gen C₁ C₂ H T := by
  have hT := hmin.isSylow
  obtain ⟨-, h1Z, -, h2B, h2char, -⟩ := id hP
  by_cases h1 : C₁ ≤ centerOf H
  · exact Or.inl h1
  by_cases h2 : H ≤ Subgroup.normalizer (C₂ : Set G)
  · exact Or.inr (Or.inl h2)
  refine Or.inr (Or.inr ?_)
  have hTH : T ≤ H := hT.1
  have hC1T : C₁ ≤ T := h1Z.trans ((Subgroup.closure_le T).mpr fun x hx => hx.1.1)
  have hC1cent : ∀ t ∈ T, ∀ c ∈ C₁, c * t = t * c := fun t ht c hc =>
    ((Subgroup.mem_centralizer_iff.mp (B2F.omegaOneCenterOf_le_centerOf T (h1Z hc)).2 t ht)).symm
  have hA1 : H ⊓ Subgroup.centralizer (C₁ : Set G) ≤ M := by
    refine hmin.le_of_lt (le_inf hTH fun t ht => Subgroup.mem_centralizer_iff.mpr fun c hc =>
      hC1cent t ht c hc) (lt_of_le_of_ne inf_le_left fun he => h1 ?_)
    have hHC : H ≤ Subgroup.centralizer (C₁ : Set G) := by
      calc H = H ⊓ Subgroup.centralizer (C₁ : Set G) := he.symm
        _ ≤ _ := inf_le_right
    refine le_inf (hC1T.trans hTH) fun c hc => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    exact ((Subgroup.mem_centralizer_iff.mp (hHC hh) c hc)).symm
  have hTS : T ≤ Subgroup.normalizer (baum T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  have hTN2 : T ≤ Subgroup.normalizer (C₂ : Set G) :=
    hTS.trans (normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2char)
  have hA2 : H ⊓ Subgroup.normalizer (C₂ : Set G) ≤ M := by
    refine hmin.le_of_lt (le_inf hTH hTN2) (lt_of_le_of_ne inf_le_left fun he => h2 ?_)
    calc H = H ⊓ Subgroup.normalizer (C₂ : Set G) := he.symm
      _ ≤ _ := inf_le_right
  obtain ⟨K, hKb, hKalt, hKJ, hKH⟩ :=
    exists_a3Block_gen_weak hP hmin hF hsolv (sup_le hA1 hA2) h1 h2
  exact ⟨K, ⟨hKb.1, Or.inr ⟨3, by decide, le_rfl, hKalt⟩⟩, hKJ, hKH⟩

theorem concl1Gen_of_perfectCore_le {C₁ C₂ H T M : Subgroup G} (hP : IsC118Pair T C₁ C₂)
    (hmin : MinParabolic H T M) (hF : CharTwo H)
    (hsolv : perfectCore H ≤ Subgroup.centralizer (VZ T H : Set G)) : Concl1Gen C₁ C₂ H T :=
  concl1Gen_of_perfectCore_le_weak hP.toWeakSelf hmin hF hsolv

end

end CFSG.AGLEmbeddingD2.GN
