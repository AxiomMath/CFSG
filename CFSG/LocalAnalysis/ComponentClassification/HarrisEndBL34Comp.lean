module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndOddLayer

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.EndB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer HarrisEnd

theorem false_of_component {G : Type} [Group G] [Finite G] {M : Subgroup G} {y : G}
    (hyM : y ∈ M) (hy2 : y ^ 2 = 1)
    (h44 : IsPGroup 2 (↥(centralizer ({y} : Set G) ⊓ M) ⧸
        pPrimeCore 2 ↥(centralizer ({y} : Set G) ⊓ M)) ∨
      Blueprint.LieModel (Bar (GSThmB.layerIn (centralizer ({y} : Set G) ⊓ M))) .PSL 2 7 1)
    {A : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)}
    (hAC : A ≤ centralizer {(QuotientGroup.mk ⟨y, hyM⟩ : ↥M ⧸ pPrimeCore 2 ↥M)})
    (hAn : ∀ g ∈ centralizer {(QuotientGroup.mk ⟨y, hyM⟩ : ↥M ⧸ pPrimeCore 2 ↥M)},
      ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hq : IsTwoQuasisimple ↥A) (hA2 : 2 ∣ Nat.card A) (hA7 : ¬ 7 ∣ Nat.card A) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  set y' : ↥M := ⟨y, hyM⟩ with hy'
  set Y' := centralizer ({y'} : Set ↥M) with hY'
  have hyy : y' * y' = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← sq, hy2, Subgroup.coe_one])
  have hCbar : centralizer ({π y'} : Set (↥M ⧸ pPrimeCore 2 ↥M)) = Y'.map π :=
    GSThmB.OddQuot.centralizer_singleton_map_eq hyy
  have hYmap : Y'.map M.subtype = centralizer ({y} : Set G) ⊓ M := by
    ext g
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact ⟨mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (mem_centralizer_singleton_iff.mp hg')), g'.2⟩
    · rintro ⟨hgy, hgM⟩
      exact ⟨⟨g, hgM⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext
        (mem_centralizer_singleton_iff.mp hgy)), rfl⟩
  have hAC' : A ≤ Y'.map π := hCbar ▸ hAC
  have hAn' : ∀ g ∈ Y'.map π, ∀ a ∈ A, g * a * g⁻¹ ∈ A := hCbar ▸ hAn
  rcases h44 with h2 | hL
  ·
    obtain ⟨e₁⟩ := nonempty_bar_map_equiv π not_two_dvd_card_ker_mk' Y'
    obtain ⟨e₂⟩ := nonempty_bar_map_equiv M.subtype (not_two_dvd_card_ker_subtype M) Y'
    rw [hYmap] at e₂
    have hP : IsPGroup 2 (↥(Y'.map π) ⧸ pPrimeCore 2 ↥(Y'.map π)) :=
      h2.of_equiv (e₁.trans e₂.symm).symm
    have hperf : Group.IsPerfect ↥(A.subgroupOf (Y'.map π)) := by
      have := hq.1
      exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hAC').symm.toMonoidHom)
        (subgroupOfEquivOfLe hAC').symm.surjective
    have hbot := eq_bot_of_isPerfect_of_isPGroup_quotient hP hperf
    have h1 : Nat.card A = 1 := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe hAC').toEquiv, hbot, card_bot]
    omega
  ·
    set Λ := GSThmB.layerIn (Y'.map π) with hΛ
    have hAΛ : A ≤ Λ := by
      have hnorm : (A.subgroupOf (Y'.map π)).Normal := ⟨fun n hn c => hAn' c c.2 n hn⟩
      have hcomp : IsTwoComponentIn A (Y'.map π) := ⟨hAC', hnorm.isSubnormal, hq⟩
      have hp := (isTwoComponentIn_iff hAC').mp hcomp
      intro x hx
      exact ⟨⟨x, hAC' hx⟩, (le_sSup (s := {L : Subgroup ↥(Y'.map π) | IsPComponent 2 L}) hp :
        _ ≤ pLayer ↥(Y'.map π) 2) (show (⟨x, hAC' hx⟩ : ↥(Y'.map π)) ∈ A.subgroupOf _ from hx),
        rfl⟩
    have hΛmap : (GSThmB.layerIn Y').map π = Λ :=
      GSThmB.OddQuot.map_layerIn π not_two_dvd_card_ker_mk' Y'
    have hΛmap' : (GSThmB.layerIn Y').map M.subtype =
        GSThmB.layerIn (centralizer ({y} : Set G) ⊓ M) := by
      rw [GSThmB.OddQuot.map_layerIn M.subtype (not_two_dvd_card_ker_subtype M) Y', hYmap]
    obtain ⟨e₁⟩ := nonempty_bar_map_equiv π not_two_dvd_card_ker_mk' (GSThmB.layerIn Y')
    obtain ⟨e₂⟩ := nonempty_bar_map_equiv M.subtype (not_two_dvd_card_ker_subtype M)
      (GSThmB.layerIn Y')
    rw [hΛmap] at e₁
    rw [hΛmap'] at e₂
    have hLΛ : Blueprint.LieModel (↥Λ ⧸ pPrimeCore 2 ↥Λ) .PSL 2 7 1 :=
      lieModel_psl2_of_mulEquiv (e₁.trans e₂.symm) hL
    have hsimp : IsSimpleGroup (↥Λ ⧸ pPrimeCore 2 ↥Λ) := isSimpleGroup_of_lieModel_psl2 hLΛ
    have h168 : Nat.card (↥Λ ⧸ pPrimeCore 2 ↥Λ) = 168 := by
      obtain ⟨hp, -, -, F, _, _, hF, ⟨e⟩⟩ := exists_psl2_of_lieModel hLΛ
      rw [Nat.card_congr e.toEquiv, SectionRank.OddCover.card_psl_two hp (by norm_num) hF]
      norm_num
    set ψ := QuotientGroup.mk' (pPrimeCore 2 ↥Λ) with hψ
    set AΛ := A.subgroupOf Λ with hAΛdef
    have hΛle : Λ ≤ Y'.map π := map_subtype_le _
    have hAΛn : AΛ.Normal := ⟨fun n hn c => hAn' c (hΛle c.2) n hn⟩
    have hcardAΛ : Nat.card AΛ = Nat.card A := by
      rw [hAΛdef, Nat.card_congr (subgroupOfEquivOfLe hAΛ).toEquiv]
    have hNn : (AΛ.map ψ).Normal := Subgroup.Normal.map hAΛn ψ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (AΛ.map ψ) with h | h
    ·
      have hle : AΛ ≤ pPrimeCore 2 ↥Λ := by
        intro a ha
        have : ψ a = 1 := by
          have := mem_map_of_mem ψ ha
          rw [h, mem_bot] at this
          exact this
        rwa [hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      have hdvd := Subgroup.card_dvd_of_le hle
      rw [hcardAΛ] at hdvd
      have hc : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥Λ)) := pPrimeCore_coprime_card
      exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) (dvd_refl 2) (hA2.trans hdvd) hc
    ·
      have hdvd : Nat.card (AΛ.map ψ) ∣ Nat.card AΛ := Subgroup.card_map_dvd AΛ ψ
      rw [h, card_top, h168, hcardAΛ] at hdvd
      exact hA7 ((by norm_num : 7 ∣ 168).trans hdvd)

end CFSG.ComponentClassification.HarrisLit.EndB
