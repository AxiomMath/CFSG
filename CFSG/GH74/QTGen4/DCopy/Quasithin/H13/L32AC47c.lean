module

public import CFSG.Quasithin.H13.L32AC47c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC30b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC47a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk2

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

section Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem reduce_KL1T_F4 (h30 : Lemma14_7_30_F4) (h32 : Lemma14_7_32_F4) (S : Setting147 G T L V H)
    {K : Subgroup G} (hK : K ∈ cComp H) :
    CFSG.IsQuasisimple (cStar K) ∧ T ≤ Subgroup.normalizer (K : Set G) ∧
      Setting147 G T L V (K ⊔ (l1 T L V ⊔ T)) ∧
      HypF918 T V L (fsuV1 T V) V (K ⊔ (l1 T L V ⊔ T)) K := by
  obtain ⟨hq, -, S', hF⟩ := h30 G T L V H S K hK
  have hTK := h32 G T L V H S K hK
  rw [conjClosure_T_eq_self hTK] at S' hF
  exact ⟨hq, hTK, S', hF⟩

theorem lemma14_7_47_of_F4
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hF318 : A318Facts)
    (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hFine : F918Fine4)
    (h28 : Lemma14_7_28_F4) (h30 : Lemma14_7_30_F4) (h32 : Lemma14_7_32_F4) (h736 : Lemma14_7_36_F4)
    (h40 : Thm14_7_40_F4) (hHat6 : Lemma14_7_47_Hat6_F4) (hL32 : Lemma14_7_47_L32_F4) :
    Lemma14_7_47_F4 := by
  intro G _ _ T L V H S K hK
  obtain ⟨hq, hTK, S₀, hF⟩ := reduce_KL1T_F4 h30 h32 S hK
  have hK₀ : K ∈ cComp (K ⊔ (l1 T L V ⊔ T)) := hF.K_cComp
  have hl1H₀ : l1 T L V ≤ K ⊔ (l1 T L V ⊔ T) := le_sup_left.trans le_sup_right
  have hL3 := relIndex_l1_F4 h1222 h1332 h1334 S.hyp
  have hSQ := sqtkGroup_of_setting S₀

  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have h4 := (F918_4_fine' hF hSQ (conjClosure_T_eq_self hTK) hV₁I hIU W hW hirrU
    hD310 hD391 hI4 hFine).1
  obtain ⟨eA⟩ := L1295B.nonempty_mulEquiv_autIH hF
  obtain ⟨hlist, h7⟩ := fourList_of_mulEquiv ((cStarEquiv K).trans eA) h4

  have hperf : Group.IsPerfect (cStar K) := hq.1
  have hZodd := odd_card_center_cStar K
  have hZ : Subgroup.center (cStar K) = ⊥ ∨ Nat.card (Subgroup.center (cStar K)) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 (card_center_cStar_dvd_three_F4 h28 S hL3 hK) with
      h1 | h3
    · exact Or.inl (Subgroup.card_eq_one.mp h1)
    · exact Or.inr h3
  have hiso : Subgroup.center (cStar K) = ⊥ →
      (cStar K ⧸ Subgroup.center (cStar K)) ≃* cStar K := fun hb =>
    (QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot

  have hl1 : ∀ (X : Type) [Group X] [Finite X], Nonempty (cStar K ≃* X) → A318Exclusion X →
      l1 T L V ≤ K := by
    intro X _ _ ⟨eX⟩ hX
    have hQ' : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (cStarEquiv K) hq
    have hKeq := eq_oPrimeResidualOf_three_of_exclusion hF318 h36 h38 hSQ hK₀ hQ'
      ((cStarEquiv K).symm.trans eX) hX
    rw [hKeq]
    exact oTwoUpper_le_oPrimeResidualOf_three hL3 hl1H₀

  have h40' : ∀ n : ℕ, 1 < n → A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)) →
      l1 T L V ≤ K ∧ ((∃ n : ℕ, IsPSL n 2 1 (cStar K)) ∨ (∃ n : ℕ, IsAlt n (cStar K)) ∨
        IsPSU 3 3 1 (cStar K)) := by
    intro n hn hLie
    have hS5 := (h40 G T L V _ S₀ K hK₀ rfl n hn hLie).1
    obtain ⟨hA5, hodd⟩ := alt5_of_s5 hK₀ (le_normalizer_of_setting h37 h38 S₀ hK₀ hTK)
      (nontrivial_of_isQuasisimple hq) hS5
    exact ⟨(Subgroup.closure_le _).2 fun x hx => hodd x (hl1H₀ (Subgroup.subset_closure hx)) hx.2,
      Or.inr (Or.inl ⟨5, hA5⟩)⟩
  rcases hlist with ⟨n, hn, h | h | h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h | ⟨n, hn, h⟩ | h | h | h |
      h | h
  · exact h40' n hn (Or.inl h)
  · exact h40' n hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact h40' n hn (Or.inr (Or.inr (Or.inl h)))
  ·
    rcases Nat.lt_or_ge 1 n with hn1 | hn1
    · exact h40' n hn1 (Or.inr (Or.inl h))
    · obtain rfl : n = 1 := le_antisymm hn1 hn
      have hP : IsPSL 3 2 1 (cStar K) :=
        IsPSL.of_mulEquiv (hiso (center_eq_bot_of_psl_two hperf h hZodd)) h
      exact ⟨hL32 G T L V _ S₀ K hK₀ rfl hP, Or.inl ⟨3, hP⟩⟩
  · exact h40' n hn (Or.inr (Or.inr (Or.inr (Or.inl h))))
  ·
    rcases hZ with hb | h3
    · have hA : IsAlt 6 (cStar K) := IsAlt.of_mulEquiv (hiso hb) h
      exact ⟨hl1 _ hA a318Exclusion_alt6, Or.inr (Or.inl ⟨6, hA⟩)⟩
    · exact absurd ⟨hq, h3, h⟩ (hHat6 G T L V _ S₀ K hK₀ rfl)
  · exact h40' n hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  ·
    have hU : IsPSU 3 3 1 (cStar K) :=
      IsPSU.of_mulEquiv (hiso (center_eq_bot_of_psu_three_three hperf h hZodd)) h
    exact ⟨hl1 _ ⟨MulEquiv.refl _⟩
      (a318Exclusion_u33 (fun _ _ _ hX => two_le_pRank_of_isPSU_three_three1515e hX) hU),
      Or.inr (Or.inr hU)⟩
  ·
    have hP : IsPSL 4 2 1 (cStar K) :=
      IsPSL.of_mulEquiv (hiso (center_eq_bot_of_psl_two hperf h hZodd)) h
    exact ⟨hl1 _ ⟨MulEquiv.refl _⟩ (a318Exclusion_psl42 l34NotL42Fact1515e_of_cert hP),
      Or.inl ⟨4, hP⟩⟩
  ·
    have hP : IsPSL 5 2 1 (cStar K) :=
      IsPSL.of_mulEquiv (hiso (center_eq_bot_of_psl_two hperf h hZodd)) h
    exact ⟨hl1 _ ⟨MulEquiv.refl _⟩ (a318Exclusion_psl52 hP), Or.inl ⟨5, hP⟩⟩
  ·
    rcases hZ with hb | h3
    · have hA : IsAlt 7 (cStar K) := IsAlt.of_mulEquiv (hiso hb) h
      exact ⟨hl1 _ hA a318Exclusion_alt7, Or.inr (Or.inl ⟨7, hA⟩)⟩
    · exact absurd ⟨hq, h3, h⟩ (h7 h)
  ·
    exact absurd h (h736 G T L V H S K hK .M22)

end Setting

end CFSG.Quasithin.H13.L32A.C
