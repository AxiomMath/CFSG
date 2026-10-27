module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarCent

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv CFSG.OddStandard.AltStdBal CFSG.ComponentClassification.RankTwoStandard

section Card

variable {X : Type} [Group X] [Finite X]

theorem card_sec_dvd_of_le {R₀ R₁ : Subgroup X} (hR : R₀ ≤ R₁) :
    Nat.card (Sec X R₁) ∣ Nat.card (Sec X R₀) := by
  have hC : centralizer (R₁ : Set X) ≤ centralizer (R₀ : Set X) := centralizer_le hR
  set ψ : ↥(centralizer (R₁ : Set X)) →* Sec X R₀ :=
    (QuotientGroup.mk' (CFSG.oddCore ↥(centralizer (R₀ : Set X)))).comp
      (Subgroup.inclusion hC) with hψ
  have hker : ψ.ker ≤ CFSG.oddCore ↥(centralizer (R₁ : Set X)) := by
    refine le_sSup ⟨inferInstance, ?_⟩
    have hle : ψ.ker.map (Subgroup.inclusion hC) ≤ CFSG.oddCore ↥(centralizer (R₀ : Set X)) := by
      rintro _ ⟨c, hc, rfl⟩
      exact (QuotientGroup.eq_one_iff _).1 hc
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hC)] at h1
    exact Odd.of_dvd_nat (ClassicalInvolution.QuaternionStructure.odd_natCard_oddCore _) h1
  calc Nat.card (Sec X R₁) = (CFSG.oddCore ↥(centralizer (R₁ : Set X))).index := rfl
    _ ∣ ψ.ker.index := Subgroup.index_dvd_of_le hker
    _ = Nat.card ψ.range := Subgroup.index_ker ψ
    _ ∣ Nat.card (Sec X R₀) := Subgroup.card_subgroup_dvd_card _

theorem sq_card_dvd_of_wreath {t : X} {A : Subgroup X} {m : ℕ} (hm : 4 ≤ m)
    (hW : WreathOutcome t A m) : (m.factorial / 2) * (m.factorial / 2) ∣ Nat.card X := by
  obtain ⟨K, hKc, hKne, -, ⟨eK⟩, -⟩ := hW
  set K' : Subgroup X := K.map (MulAut.conj t).toMonoidHom with hK'
  have hK'c : CFSG.IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv _ hKc
  have hc : ⁅K, K'⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hKc hK'c).resolve_left fun h => hKne h.symm
  have hKK' : K ≤ centralizer (K' : Set X) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
  have eK' : K' ≃* alternatingGroup (Fin m) :=
    (K.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm.trans eK
  have hcen : center K = ⊥ := center_eq_bot_of_alt hm eK
  have hcomm : ∀ (a : K) (b : K'), Commute (K.subtype a) (K'.subtype b) := fun a b =>
    (mem_centralizer_iff.1 (hKK' a.2) b b.2).symm
  let Φ := K.subtype.noncommCoprod K'.subtype hcomm
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have hab' : (a : X) * b = 1 := hab
    have ha : (a : X) = (b : X)⁻¹ := eq_inv_of_mul_eq_one_left hab'
    have hacen : a ∈ center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      change (g : X) * a = a * g
      rw [ha]
      exact (mem_centralizer_iff.1 (hKK' g.2) _ (inv_mem b.2)).symm
    rw [hcen, Subgroup.mem_bot] at hacen
    subst hacen
    have hb : (b : X) = 1 := by simpa using hab'
    exact Prod.ext rfl (Subtype.ext hb)
  have := Subgroup.card_dvd_of_injective Φ hΦ
  rwa [Nat.card_prod, card_eq_of_equiv_alt (by omega) eK,
    card_eq_of_equiv_alt (by omega) eK'] at this

omit [Finite X] in
theorem card_eq_of_hnOutcome {t : X} (hHN : HNOutcome t) :
    Nat.card X = 546061824000000 := by
  obtain ⟨W, -, hWi, -, ⟨eW⟩⟩ := hHN
  have h1 := Subgroup.card_mul_index W
  rw [hWi, Nat.card_congr eW.toEquiv, CFSG.Sporadic.HN.card_HN] at h1
  omega

end Card

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

theorem shapeTwo_dichotomy_thirteen (htri : ExactShapeTrichotomy)
    (hR2 : RankTwoAlternatingStandard) (h : Setting G L 13) (d : Cyc L Q z)
    (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin 13)) :
    CaseII e h.hn (L ⊔ zpowers u) z ∨ CaseII e h.hn (L ⊔ zpowers (u * z)) z ∨
      ∃ H : Subgroup G, WreathPair L z 13 H := by
  classical
  have h47 : ShapeTwoCentDoubleAt 13 := shapeTwoCentDoubleAt_of_ne htri hR2 le_rfl (by norm_num)
  obtain ⟨S₀, S₁, hS₀, hS₁, hS01⟩ : ∃ S₀ S₁ : Finset (Fin 13),
      S₀.card = 3 ∧ S₁.card = 4 ∧ S₀ ⊆ S₁ :=
    ⟨{0, 1, 2}, {0, 1, 2, 3}, by decide, by decide, by decide⟩
  have hex : ExactShape z L 13 := exactShape_of_setting h d T.card
  have hK := isKGroupCat_of_kProper h.std.kProper
  have ht₁ : z ∈ centralizer (corr (X := G) e (altSub S₁) : Set G) :=
    t_mem_centralizer_corr (X := G) e hex (altSub S₁)
  have hsec₁ := exactShape_section_root hex e (by omega) (by omega) ht₁
  have hKcat₁ : CFSG.SectionRank.IsKGroupCat (Sec G (corr (X := G) e (altSub S₁))) :=
    isKGroupCat_sec hK
      (centralizer_ne_top_of_ne_one h (exists_ne_one_of_card_ge_three e (by omega)))
  have hO₁ := oddCore_sec_eq_bot (corr (X := G) e (altSub S₁))
  rcases htri _ _ _ (13 - S₁.card) (by omega) hKcat₁ hO₁ hsec₁ with h1 | hW₁ | h1 | h1
  · exact (false_of_caseI htri h d T e (by norm_num) (by norm_num) (Or.inr hS₁) (by omega) ⟨ht₁, h1⟩).elim
  ·
    have ht₀ : z ∈ centralizer (corr (X := G) e (altSub S₀) : Set G) :=
      t_mem_centralizer_corr (X := G) e hex (altSub S₀)
    have hsec₀ := exactShape_section_three hex e hS₀ (by omega) ht₀
    have hKcat₀ : CFSG.SectionRank.IsKGroupCat (Sec G (corr (X := G) e (altSub S₀))) :=
      isKGroupCat_sec hK
        (centralizer_ne_top_of_ne_one h (exists_ne_one_of_card_ge_three e (by omega)))
    have hO₀ := oddCore_sec_eq_bot (corr (X := G) e (altSub S₀))
    rcases htri _ _ _ (13 - S₀.card) (by omega) hKcat₀ hO₀ hsec₀ with h2 | h2 | h2 | ⟨-, h2⟩
    · exact (false_of_caseI htri h d T e (by norm_num) (by norm_num) (Or.inl hS₀) (by omega) ⟨ht₀, h2⟩).elim
    · obtain ⟨H, hH⟩ := exists_wreathPair_of_caseIII_root hex e (by norm_num) hS₀ ⟨ht₀, h2⟩
      exact Or.inr (Or.inr ⟨H, hH⟩)
    · rcases caseII_of_centDoubleAt h47 h d T e (by norm_num) (Or.inl hS₀) (by omega)
        ⟨ht₀, h2⟩ with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Or.inl h3)
    ·
      exfalso
      have hdvd := (sq_card_dvd_of_wreath (by omega) hW₁).trans
        (card_sec_dvd_of_le (corr_mono e (altSub_mono hS01)))
      rw [card_eq_of_hnOutcome h2, hS₁] at hdvd
      revert hdvd
      norm_num [Nat.factorial]
  · rcases caseII_of_centDoubleAt h47 h d T e (by norm_num) (Or.inr hS₁) (by omega)
      ⟨ht₁, h1⟩ with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
  · omega

theorem false_of_shapeTwo_thirteen (htri : ExactShapeTrichotomy)
    (hR2 : RankTwoAlternatingStandard) (h : Setting G L 13) (d : Cyc L Q z)
    (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin 13)) : False :=
  false_of_shapeTwo_of_dichotomy htri h d T.card (by norm_num) T.cent T.outer T.sq e
    (shapeTwo_dichotomy_thirteen htri hR2 h d T e)

theorem false_of_outer_of_shapeTwo (h : Setting G L n) (S : Sylow 2 (centralizer (L : Set G)))
    (hcyc : IsCyclic (S : Subgroup (centralizer (L : Set G)))) (h2 : Nat.card S = 2)
    (hex : ∃ w : G, w ∈ centralizer (L : Set G) ∧ orderOf w = 2 ∧
      ¬ centralizer ({w} : Set G) ≤ L ⊔ centralizer (L : Set G))
    (htwo : ∀ (Q : Subgroup G) (z u : G), Cyc L Q z → ShapeTwo L Q z u → False) : False := by
  obtain ⟨w, hwK, hw2, hwO⟩ := hex
  obtain ⟨z, d⟩ := Cyc.of_sylow h S hcyc
  have hQ2 : Nat.card (sylowSub S) = 2 := (card_sylowSub S).trans h2
  obtain ⟨k, hkK, hkz⟩ := exists_conj_of_involution d hwK hw2
  have hO : ¬ centralizer ({z} : Set G) ≤ L ⊔ sylowSub S := by
    intro hle
    apply hwO
    intro c hc
    have hc' : k⁻¹ * c * k ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      rw [← hkz] at hc
      calc k⁻¹ * c * k * z = k⁻¹ * (c * (k * z * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * z * k⁻¹) * c) * k := by rw [hc]
        _ = z * (k⁻¹ * c * k) := by group
    have h1 : k⁻¹ * c * k ∈ L ⊔ centralizer (L : Set G) :=
      sup_le_sup_left d.le L (hle hc')
    have hkK' : k ∈ L ⊔ centralizer (L : Set G) := mem_sup_right hkK
    have := mul_mem (mul_mem hkK' h1) (inv_mem hkK')
    simpa [mul_assoc] using this
  obtain ⟨u, hu, huQ, hsq | hsq⟩ := exists_outer_sq_eq h d hQ2 hO
  · exact htwo _ z u d ⟨hQ2, hu, huQ, hsq⟩
  · exact false_of_shape_three h d hQ2 hu huQ hsq

end Main

end CFSG.OddStandard.AltStdSec
