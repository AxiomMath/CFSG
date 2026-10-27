module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CenterData
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InputsCenter
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OuterRow

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OutInv

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

theorem mem_of_phi_mem_zpowers {t : H} (ht : t ∈ h.T)
    (hmem : phi hKa (wbarMk h.B ⟨t, Idx.mem_W_of_mem_T h ht⟩) ∈ zpowers (phi hKa (abar h))) :
    t ∈ zpowers h.a ⊔ h.B := by
  have hα2 : phi hKa (abar h) * phi hKa (abar h) = 1 := by
    rw [← map_mul, abar_mul_self, map_one]
  have hinj := GH74.KGroups.inducedHom_injective (K := OddBar h.K) h.isQuasisimple_K.1
  apply Idx.mem_of_actW h hKa ht
  rcases eq_one_or_eq_of_mem_zpowers hα2 hmem with h1 | h1
  · left
    have h2 : rhoL hKa ⟨t, Idx.mem_W_of_mem_T h ht⟩ = 1 := by
      have := congrArg (fun g : ↥(GAut hKa) => (g : MulAut (LK h))) h1
      rw [← rhoBar_mk]
      simpa using this
    apply hinj
    rw [map_one]
    exact h2
  · right
    have h2 : rhoL hKa ⟨t, Idx.mem_W_of_mem_T h ht⟩ = rhoL hKa ⟨h.a, h.a_mem_normalizer⟩ := by
      have := congrArg (fun g : ↥(GAut hKa) => (g : MulAut (LK h))) h1
      rw [← rhoBar_mk, ← rhoBar_mk]
      simpa using this
    exact hinj h2

theorem exists_center_config {t : H} (ht : t ∈ h.T) (htQ : t ∈ centralizer (h.Q : Set H)) :
    ∃ R : Subgroup ↥(GAut hKa), CenterSylowConfig ↥(GAut hKa) (NL hKa) (phi hKa (abar h))
      (Jhat hKa) R (phi hKa (wbarMk h.B ⟨t, Idx.mem_W_of_mem_T h ht⟩)) := by
  obtain ⟨Rh, hRM, hRS, hRQ⟩ := exists_sylow_image hKa
  have htW := Idx.mem_W_of_mem_T h ht
  set w : h.W := ⟨t, htW⟩ with hw
  set aw : h.W := ⟨h.a, h.a_mem_normalizer⟩ with haw
  set χ : h.W →* ↥(GAut hKa) := (phi hKa).comp (wbarMk h.B) with hχ
  have hτα : χ w * χ aw = χ aw * χ w := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.comm_a (Idx.mem_S_of_mem_T h ht))
  have hτJ : ∀ x ∈ Jhat hKa, χ w * x = x * χ w := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := mem_centralizer_iff.mp (tbar_mem_centralizer hKa ht) y hy
    show phi hKa (wbarMk h.B w) * phi hKa y = phi hKa y * phi hKa (wbarMk h.B w)
    rw [← map_mul, ← map_mul, h1]
  have hτR : ∀ r ∈ Rh, χ w * r = r * χ w := by
    intro r hr
    obtain ⟨q, hq, hqW, rfl⟩ := hRQ r hr
    have h1 : q * t = t * q := mem_centralizer_iff.mp htQ q hq
    show χ w * χ ⟨q, hqW⟩ = χ ⟨q, hqW⟩ * χ w
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h1.symm
  have hRα : Rh ≤ centralizer ({phi hKa (abar h)} : Set ↥(GAut hKa)) := by
    intro r hr
    obtain ⟨q, hq, hqW, rfl⟩ := hRQ r hr
    rw [mem_centralizer_singleton_iff]
    show χ ⟨q, hqW⟩ * χ aw = χ aw * χ ⟨q, hqW⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.comm_a (mem_inf.mp hq).1)
  have hτ2 : ∃ k : ℕ, χ w ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := h.orderOf_eq_two_pow_of_mem_S (Idx.mem_S_of_mem_T h ht)
    refine ⟨k, ?_⟩
    rw [← map_pow, ← map_one χ]
    congr 1
    apply Subtype.ext
    simp only [hw, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hk, pow_orderOf_eq_one]
  exact ⟨Rh, NL_normal hKa, centralizer_NL hKa, orderOf_phi_abar' hKa, (Jhat_component hKa).1,
    (Jhat_component hKa).2, Jhat_standard hKa, hRM, hRα, hRS, hτα, hτJ, hτR, hτ2⟩

theorem cfProp23Center_of
    (hCent : OuterL2Cent) (hAlt : CenterSylowAlt)
    (hLie : CenterSylowLie) (hSuz : CenterSylowSuz) : CFProp23Center := by
  intro H _ _ h htab t ht
  obtain ⟨htT, htQ⟩ := mem_inf.mp ht
  rcases htab with ⟨n, hn, ⟨eJ⟩, ⟨hKa, hK | hK⟩ | ⟨hKa, -, ⟨eK⟩⟩⟩ | ⟨hJ, hKa, -, hK⟩ |
      ⟨hJ, hKa, -, ⟨eK⟩⟩ | ⟨p, f, hp, hp2, hf, hJ, hKa, hK⟩ |
      ⟨p, f, hp, hp2, hf, h5, hJ, hKa, hK⟩ | ⟨p, f, hp, hp2, hf, h5, hJ, hKa, -, hK⟩ |
      ⟨p, f, hp, hp2, hf, hJ, hKa, hK⟩
  ·
    exact Idx.T_le_case_alt h hn ⟨eJ⟩ hKa hK htT
  ·
    obtain ⟨eK⟩ := hK
    obtain ⟨R, hcfg⟩ := exists_center_config hKa htT htQ
    refine mem_of_phi_mem_zpowers hKa htT (hAlt _ _ _ _ _ _ hcfg n hn ?_ ?_)
    · obtain ⟨eN⟩ := nonempty_NL_equiv hKa
      have hZK := IdxRed.center_eq_bot_of_alt (by omega) eK
      exact ⟨eN.trans ((QuotientGroup.quotientMulEquivOfEq hZK).trans
        (QuotientGroup.quotientBot.trans eK))⟩
    · obtain ⟨eJ'⟩ := nonempty_Jhat_equiv' hKa
      have hZJ := IdxRed.center_eq_bot_of_alt (by omega) eJ
      exact ⟨eJ'.trans ((QuotientGroup.quotientMulEquivOfEq hZJ).trans
        (QuotientGroup.quotientBot.trans eJ))⟩
  ·
    refine IdxKa.T_le_of_ne h hKa (IdxRed.center_eq_bot_of_alt (by omega) eJ) ?_ htT
    rw [Nat.card_congr eK.toEquiv, Nat.card_congr eJ.toEquiv]
  ·
    exact Idx.T_le_case_l34 h hJ hKa hK htT
  ·
    obtain ⟨R, hcfg⟩ := exists_center_config hKa htT htQ
    refine mem_of_phi_mem_zpowers hKa htT (hSuz _ _ _ _ _ _ hcfg ?_ ?_)
    · obtain ⟨eN⟩ := nonempty_NL_equiv hKa
      obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
      exact ⟨(eN.trans eZ).trans eK⟩
    · obtain ⟨eJ'⟩ := nonempty_Jhat_equiv' hKa
      obtain ⟨eZJ⟩ := nonempty_quotient_center_equiv_zStarBar h.J
      exact lieModel_of_mulEquiv_ne_zero (eJ'.trans eZJ).symm (by norm_num) hJ
  ·
    by_cases hin : h.a ∈ h.K ⊔ coreActionKernel h.K
    · obtain ⟨R, hcfg⟩ := exists_center_config hKa htT htQ
      refine mem_of_phi_mem_zpowers hKa htT (hLie _ _ _ _ _ _ hcfg p f hp hp2 hf
        (phi_abar_mem_NL hKa hin) (Jhat_le_NL hKa) ?_ ?_)
      · rcases hK with hK | hK | ⟨e, he, hK⟩
        · exact Or.inl (lieModel_NL hKa (by norm_num) hK)
        · exact Or.inr (Or.inl (lieModel_NL hKa (by norm_num) hK))
        · exact Or.inr (Or.inr ⟨e, he, lieModel_NL hKa (by norm_num) hK⟩)
      · obtain ⟨eJ'⟩ := nonempty_Jhat_equiv' hKa
        have hZJ := IdxRed.center_eq_bot_of_psl2 hJ
        exact lieModel_of_mulEquiv_ne_zero (eJ'.trans
          ((QuotientGroup.quotientMulEquivOfEq hZJ).trans QuotientGroup.quotientBot)).symm
          (by norm_num) hJ
    · exact indexElimOuter_of hCent H h ⟨p, f, hp, hp2, hf, hJ, hKa, hK⟩ hin htT
  ·
    exact Idx.T_le_case_psl2 h hp hp2 hf h5 hJ hKa hK htT
  ·
    refine IdxKa.T_le_of_ne h hKa (IdxRed.center_eq_bot_of_psl2 hJ) ?_ htT
    rw [Idx.card_of_lieModel_psl2 hp2 hK, Idx.card_of_lieModel_psl2 hp2 hJ]
  ·
    exact IdxSp.T_le_case_psp h hp hp2 hf hJ hKa hK htT

end OutInv

end CFSG.ComponentClassification.CatFactsL4U4
