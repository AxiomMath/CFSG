module

public import CFSG.Quasithin.H13.L32AC32j
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC32i
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC33h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC52c

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem exists_ctxS_F4 (h30 : Lemma14_7_30_F4) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hT : ¬ T ≤ Subgroup.normalizer (K : Set G)) :
    ∃ t₀ : G, CtxS T L V (conjClosure K T ⊔ (l1 T L V ⊔ T)) K t₀ := by
  obtain ⟨-, -, S₀, -⟩ := h30 G T L V H S K hK
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := Setting147.TH' S
  have hK₀H : conjClosure K T ≤ H := conjClosure_le fun s hs k hk =>
    H.mul_mem (H.mul_mem (hTH hs) (hKH hk)) (H.inv_mem (hTH hs))
  have hKH₀ : K ≤ conjClosure K T ⊔ (l1 T L V ⊔ T) := (le_conjClosure K T).trans le_sup_left
  have hK₀ : K ∈ cComp (conjClosure K T ⊔ (l1 T L V ⊔ T)) :=
    mem_cComp_of_le_of_le hK hKH₀ (sup_le hK₀H S.hz.1.1)
  have h121 := lemma_1_2_1_three S.hyp.fsu.qtke S.hyp.fsu.simple S.hyp.fsu.nonabelian hA37 hA38
    S₀.hz.1.2 hK₀
  have hyN : ∀ y ∈ l1 T L V, y ^ 3 = 1 → y ∈ Subgroup.normalizer (K : Set G) :=
    fun y hy hy3 =>
      mem_normalizer_of_cube hKH₀ (h121.imp_right fun h => h.1) (Setting147.l1H' S₀ hy) hy3
  obtain ⟨t₀, ht₀T, ht₀N⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra h
    push Not at h
    exact hT h
  have ht₀H : t₀ ∈ conjClosure K T ⊔ (l1 T L V ⊔ T) := Setting147.TH' S₀ ht₀T
  have h2 : (conjSubgroupsBy (conjClosure K T ⊔ (l1 T L V ⊔ T)) K).ncard = 2 := by
    rcases h121 with hn | ⟨h2, -⟩
    · exact absurd ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH₀).mp hn ht₀H) ht₀N
    · exact h2
  exact ⟨t₀, S₀, hK₀, ht₀T, ht₀N, mem_normalizer_or_of_ncard h2 ht₀H ht₀N, hyN⟩

theorem l2_core_F4 (h30 : Lemma14_7_30_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (h29 : Thm14_7_29_F4) (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hT : ¬ T ≤ Subgroup.normalizer (K : Set G))
    (hL2 : (∃ n : ℕ, IsPSL 2 2 n (cStar K)) ∨ IsAlt 5 (cStar K)) :
    IsAlt 5 (cStar K) ∧ l1 T L V ≤ conjClosure K T := by
  obtain ⟨t₀, C₀⟩ := exists_ctxS_F4 h30 hA37 hA38 S hK hT
  obtain ⟨n, hn, hP⟩ : ∃ n : ℕ, 2 ≤ n ∧ IsPSL 2 2 n (cStar K) := by
    rcases hL2 with ⟨n, hP⟩ | hA
    · refine ⟨n, ?_, hP⟩
      by_contra hn
      obtain ⟨-, -, -, -, -, hn1, -⟩ := SBc6.exists_sl2_equiv_of_psl hP
      have hn1' : n = 1 := by omega
      subst hn1'
      have hcard := Z4c2.card_of_isPSL_two_two hP
      have hs : Group.IsSolvable (cStar K) :=
        isSolvable_of_isTwoThree (by rw [hcard]; exact ⟨1, 1, by norm_num⟩)
      obtain ⟨φ⟩ := modO2_mulEquiv hK
      exact not_isSolvable_of_mem_cComp (modO2Image_mem_cComp hK)
        (Group.isSolvable_of_surjective (f := ((cStarEquiv K).trans φ).toMonoidHom)
          (MulEquiv.surjective _))
    · exact ⟨2, le_rfl, C126.isPSL_two_two_two_of_alternating_five _ hA⟩
  have C : CtxL2 T L V (conjClosure K T ⊔ (l1 T L V ⊔ T)) K t₀ n := ⟨C₀, hn, hP⟩
  have hn2 := C.n_eq_two_F4 hA37 h29 h1222 h1332 h1334
  subst hn2
  exact ⟨isAlt_five_of_isPSL_two_two_two hP, C.l1_le_F4 hA37 h1222 h1332 h1334⟩

theorem mem_cComp_g1_F4
    (h7 : Lemma14_7_7_F4) (h30 : Lemma14_7_30_F4) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hA39 : A39ForSQTK)
    (h29 : Thm14_7_29_F4) (hSzB : SzAutBorelThree) (hD36 : D36) (hD37 : D37) (hD321 : D321)
    (hI5 : Insp5a) (h128 : Lemma128One) (S : Setting147 G T L V H) {K : Subgroup G}
    (hK : K ∈ cComp H) (hT : ¬ T ≤ Subgroup.normalizer (K : Set G))
    (hL2 : (∃ n : ℕ, IsPSL 2 2 n (cStar K)) ∨ IsAlt 5 (cStar K)) :
    K ∈ cComp (A6.g1 T V) ∧ IsAlt 5 (cStar K) ∧ l1 T L V ≤ conjClosure K T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hA5, hl1⟩ := l2_core_F4 h30 h1222 h1332 h1334 hA37 hA38 h29 S hK hT hL2
  have S₁ := setting_g1_F4 h1332 h1334 S
  have hHG : H ≤ A6.g1 T V := S.hz.2.1
  have hTH : T ≤ H := Setting147.TH' S
  have hTG : T ≤ A6.g1 T V := hTH.trans hHG
  have hKH := le_of_mem_cComp hK
  have hSH := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  have hSG := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTG

  obtain ⟨K₁, hK₁, hKK₁⟩ := CFSG.Quasithin.lemma_1_2_4_exists S.hyp.fsu.qtke S.hyp.fsu.simple
    S.hyp.fsu.nonabelian hA37 hA39 S₁.hz.1.2 hSG (hKH.trans hHG) (cComp_subset_lFamily hTH hK)

  obtain ⟨t₀, ht₀T, ht₀N⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra h
    push Not at h
    exact hT h
  have hne : K.map (MulAut.conj t₀).toMonoidHom ≠ K := fun h =>
    ht₀N (A38.map_conj_eq_iff.mp h)
  obtain ⟨hne₁, -⟩ := lemma_1_2_8_one_conj S.hyp.fsu.qtke S.hyp.fsu.simple S.hyp.fsu.nonabelian
    hA37 h128 (isLocal_of_mem_cComp_of_sylow hSH S.hz.1.2 hK)
    (isLocal_of_mem_cComp_of_sylow hSG S₁.hz.1.2 hK₁) hKK₁ ht₀T hne
  have hT₁ : ¬ T ≤ Subgroup.normalizer (K₁ : Set G) := fun h =>
    hne₁ (A38.map_conj_eq_iff.mpr (h ht₀T))

  have hL2₁ : (∃ m : ℕ, IsPSL 2 2 m (cStar K₁)) ∨ IsAlt 5 (cStar K₁) := by
    obtain ⟨-, -, S₀, hF⟩ := h30 G T L V (A6.g1 T V) S₁ K₁ hK₁
    have hK₀ : conjClosure K₁ T ≠ K₁ := fun h => hT₁ (by
      rw [← h]
      exact le_normalizer_conjClosure K₁ T)
    obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
    have h5 := (F918_5' hF (sqtkGroup_of_setting S₀) hK₀ hV₁I hIU W hW hirrU hD36 hD37 hD321
      hI5 hA37 hA38).1
    obtain ⟨eA⟩ := L1295B.nonempty_mulEquiv_autIH hF
    have h5' : FiveShape (cStar K₁) := fiveShape_congr ((cStarEquiv K₁).trans eA).symm h5
    rcases h5' with ⟨m, hm⟩ | ⟨m, hm⟩ | hm | hm
    · exact Or.inl ⟨m, hm⟩
    · exact (false_of_sz_F4 h7 h30 h1222 h1332 h1334 hA37 hA38 h29 hSzB S₁ hK₁ hm).elim
    · exact Or.inr hm
    · exact (false_of_l32_F4 h30 h1222 h1332 h1334 hA37 hA38 S₁ hK₁ hT₁ hm).elim
  obtain ⟨hA5₁, -⟩ := l2_core_F4 h30 h1222 h1332 h1334 hA37 hA38 h29 S₁ hK₁ hT₁ hL2₁

  have hK₁le : K₁ ≤ K ⊔ pCoreOf 2 K₁ :=
    (card_dvd_of_le hKK₁).2 (by rw [card_of_isAlt_five hA5, card_of_isAlt_five hA5₁])
  have hNT : pCoreOf 2 K₁ ≤ T :=
    (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK₁)).trans
      (L32A.pCoreOf_le_of_le S.hyp hTG)
  have hK₁H : K₁ ≤ H := hK₁le.trans (sup_le hKH (hNT.trans hTH))
  have hK₁c : K₁ ∈ cComp H := mem_cComp_of_le_of_le hK₁ hK₁H hHG
  have h37 : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H) :=
    hA37 _ (sqtkHyp_quotient_of_pCoreOf_ne_bot S.hyp.fsu.qtke S.hyp.fsu.simple
      S.hyp.fsu.nonabelian S.hz.1.2)
  have heq : K = K₁ := lemma_1_2_4_unique h37 (cComp_subset_lFamily hTH hK) hK hK₁c le_rfl hKK₁
  exact ⟨heq ▸ hK₁, hA5, hl1⟩

end CFSG.Quasithin.H13.L32A.C
