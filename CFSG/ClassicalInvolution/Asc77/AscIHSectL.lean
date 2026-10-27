module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectI
public import CFSG.ClassicalInvolution.Asc77.AscE184Graph

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem exists_conj_omegaNbr (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hΩ' : HypOmegaMod p f (quotFamily Ω N)) (hN : Odd (Nat.card N)) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' N) ∈
      omegaNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ n ∈ N, J ∈ omegaNbr Ω (conjSub n K) := by
  obtain ⟨-, hne, Rb, hRb, hRbJ, hRbN⟩ := h
  obtain ⟨J₁, hJ₁, hRbsyl⟩ := exists_isSylow2In_of_mem_RSet hRb
  have hRb2 : IsPGroup 2 Rb := hRbsyl.2.1
  have h8 : 8 ≤ Nat.card Rb := hΩ'.eight_le_of_mem_RSet hp hRb
  have hJ₁eq : J₁ = J.map (QuotientGroup.mk' N) :=
    hΩ'.eq_of_le_of_le hJ₁ (map_mem_quotFamily hJ) hRb2 (by omega) hRbsyl.1 hRbJ
  rw [hJ₁eq] at hRbsyl
  obtain ⟨R₀, hR₀, hR₀J, -⟩ :=
    exists_mem_RSet_ge hJ (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G)) bot_le
  have hV₁ := isSylow2In_map_mk hN hR₀J
  obtain ⟨xb, hxbJ, hconj⟩ := exists_conjSub_eq_of_isSylow2In hV₁ hRbsyl
  obtain ⟨x, hxJ, hx⟩ := Subgroup.mem_map.mp hxbJ
  have hRΩ : conjSub x R₀ ∈ RSet Ω := RSet.conj hΩ.conjInvariant hR₀ x
  have hRJ : conjSub x R₀ ≤ J := by
    have := conjSub_mono (n := x) hR₀J.1
    rwa [conjSub_eq_self_of_mem hxJ] at this
  have hRmap : (conjSub x R₀).map (QuotientGroup.mk' N) = Rb := by
    rw [AscQuot.map_conjSub, hx]
    exact hconj
  have hR2 : IsPGroup 2 (conjSub x R₀) := isPGroup_conjSub x hR₀J.2.1
  obtain ⟨n, hn, hRn⟩ := exists_conj_normalizer hp hq hΩ hN hK hR2 (fun u hu =>
    hRbN (hRmap ▸ Subgroup.mem_map_of_mem _ hu))
  refine ⟨n, hn, hJ, ?_, conjSub x R₀, hRΩ, hRJ, hRn⟩
  intro hJK
  apply hne
  rw [hJK, AscQuot.map_conjSub, show QuotientGroup.mk' N n = 1 from
    (QuotientGroup.eq_one_iff _).mpr hn, conjSub_one]

theorem dEdgeless_quotFamily (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hΩ' : HypOmegaMod p f (quotFamily Ω N)) (hN : Odd (Nat.card N)) (hDE : DEdgeless Ω) :
    DEdgeless (quotFamily Ω N) := by
  rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hadj
  rcases hadj with h | h
  · obtain ⟨n, -, hn'⟩ := exists_conj_omegaNbr hp hq hΩ hΩ' hN hK hJ h
    exact hDE _ (hΩ.conjInvariant n K hK) J hJ (Or.inl hn')
  · obtain ⟨n, -, hn'⟩ := exists_conj_omegaNbr hp hq hΩ hΩ' hN hJ hK h
    exact hDE _ (hΩ.conjInvariant n J hJ) K hK (Or.inl hn')

omit [Finite G] [N.Normal] in
theorem dEdgeless_restrictFamily (hDE : DEdgeless Ω) (Y : Subgroup G) :
    DEdgeless (restrictFamily Ω Y) := by
  rintro K' hK' J' hJ' hadj
  have hK'Ω : K'.map Y.subtype ∈ Ω := mem_restrictFamily_iff.mp hK'
  have hJ'Ω : J'.map Y.subtype ∈ Ω := mem_restrictFamily_iff.mp hJ'
  rcases hadj with h | h
  · exact hDE _ hK'Ω _ hJ'Ω (Or.inl (omegaNbr_map h))
  · exact hDE _ hK'Ω _ hJ'Ω (Or.inr (omegaNbr_map h))

end Lift

section Datum

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem OmegaLie.card_eq_one_of_dEdgeless (D : OmegaLie p f Φ) (hΦ : HypOmegaMod p f Φ)
    (hDE : DEdgeless Φ) (hne : Φ.Nonempty) : D.card = 1 := by
  obtain ⟨K, hK⟩ := hne
  obtain ⟨i₀, hKi₀⟩ := D.exists_comp_of_mem hK
  have hsub : ∀ j : Fin D.card, j = i₀ := by
    intro j
    by_contra hji
    obtain ⟨R, -, hRΦ⟩ := D.meets j
    have hRj : R.map (D.hom j) ≤ D.comp j := Subgroup.map_le_range _ _
    have hcomm : Commutes (R.map (D.hom j)) K := fun x hx y hy =>
      D.comp_commute hji x (hRj hx) y (hKi₀ hy)
    have hKR : K ≠ R.map (D.hom j) := by
      intro h
      obtain ⟨z, hz⟩ := hΦ.classical K hK
      obtain ⟨x, hx, y, hy, hxy⟩ := ih8_exists_noncomm hz
      exact hxy (hcomm x (h ▸ hx) y hy)
    exact hDE K hK _ hRΦ (dAdj_of_commutes hRΦ hKR hcomm.symm)
  have hle : D.card ≤ 1 := Fin.subsingleton_iff_le_one.mp ⟨fun a b => (hsub a).trans (hsub b).symm⟩
  have hpos : 0 < D.card := i₀.pos
  omega

variable [Finite X]

theorem exists_datum_of_dEdgeless {n : ℕ} (hn : CITBelowU p f n) (hlt : Nat.card X < n)
    (hΦ : HypOmegaMod p f Φ) (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (hDE : DEdgeless Φ) (hne : Φ.Nonempty) :
    ∃ (t : StatedLieTag) (k e : ℕ) (_ : Ih8Model p f Φ t k e), HasLieType p f Φ t k := by
  obtain ⟨D⟩ := ih8_exists_omegaLie hn hΦ.conjInvariant hΦ.classical hne hO hlt
  have hcard := D.card_eq_one_of_dEdgeless hΦ hDE hne
  let i : Fin D.card := ⟨0, by omega⟩
  have hsurj := D.hom_surjective_of_gen hcard hgen i
  exact ⟨D.tag i, D.rank i, D.exp i,
    { isFundTag := D.isFundTag i
      admissible := D.admissible i
      exp_eq := D.exp_eq i
      ψ := D.hom i
      ker_le_center := D.ker_le_center i
      surj := hsurj
      cls := D.cls i
      cls_sub := fun _ hR => hR.1
      mem_iff := fun _ => D.mem_iff_exists_cls hcard i
      cls_conj := fun _ hR g => D.cls_conj hΦ.conjInvariant i hR g },
    D, hcard, i, rfl, rfl⟩

end Datum

section Thm6

variable {G : Type} [Group G] {Φ : Set (Subgroup G)} {t : StatedLieTag} {k e : ℕ}

theorem thm6_tag_of_datum (hP1 : Ih8SmallEdge p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (M : Ih8Model p f Φ t k e) (hne : Φ.Nonempty) (hDE : DEdgeless Φ)
    (hnpsl : ¬ (t = .PSL ∧ k = 2)) :
    (t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3) ∨ (t = .G2 ∧ k = 0) ∨
      (t = .trialityD4 ∧ k = 0) := by
  by_cases hG2 : t = .G2
  · subst hG2
    obtain ⟨hk, -⟩ := M.admissible.2.2
    exact Or.inr (Or.inr (Or.inl ⟨rfl, hk⟩))
  by_cases hD4 : t = .trialityD4
  · subst hD4
    exact Or.inr (Or.inr (Or.inr ⟨rfl, M.admissible.2.2⟩))
  have hq' : 5 ≤ p ^ e := by rw [M.exp_eq_f hD4]; exact hq
  have hedge : (∃ R ∈ ModelFund p t k e, ∃ S ∈ ModelFund p t k e, R ≠ S ∧ Commutes R S) →
      False := by
    rintro ⟨R, hR, S, hS, hRS, hc⟩
    exact M.not_dEdgeless_of_commutes hp2 hD4 hq (M.fund_subset_cls hne hG2 hD4 hR)
      (M.fund_subset_cls hne hG2 hD4 hS) hRS hc hDE
  rcases ih8_tag_cases hp2 hq' M.isFundTag M.admissible hG2 hD4 with hconn | hsmall
  · obtain ⟨R, hR⟩ := M.cls_nonempty hne
    obtain ⟨S, hS, hSR, hc⟩ := ih8_exists_edge_of_connected hp2 hq' M.isFundTag M.admissible hnpsl
      hconn (M.cls_sub hR)
    exact (hedge ⟨R, M.cls_sub hR, S, hS, hSR.symm, hc⟩).elim
  · rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hk2 : 2 ≤ k := M.admissible.2.2.1
      have : k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl | rfl
      · exact (hnpsl ⟨rfl, rfl⟩).elim
      · exact Or.inl ⟨rfl, rfl⟩
      · exact (hedge (hP1 _ _ _ M.admissible hp2 hq' (Or.inl ⟨rfl, rfl⟩))).elim
    · have hk3 : 3 ≤ k := M.admissible.2.2.1
      have : k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact (hedge (hP1 _ _ _ M.admissible hp2 hq' (Or.inr (Or.inl ⟨rfl, rfl⟩)))).elim
    · exact (hedge (hP1 _ _ _ M.admissible hp2 hq' (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))).elim
    · exact (hedge (hP1 _ _ _ M.admissible hp2 hq'
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))).elim
    · exact (hedge (hP1 _ _ _ M.admissible hp2 hq'
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))).elim
    · exact (hedge (hP1 _ _ _ M.admissible hp2 hq'
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))).elim

theorem thm6_tag_of_datum_top (hP1 : Ih8SmallEdge p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (M : Ih8Model p f Φ t k e) (hne : Φ.Nonempty) (hDE : DEdgeless Φ)
    (htop : (⊤ : Subgroup G) ∉ Φ) :
    (t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3) ∨ (t = .G2 ∧ k = 0) ∨
      (t = .trialityD4 ∧ k = 0) :=
  thm6_tag_of_datum hP1 hp2 hq M hne hDE (M.not_psl_two_sect hp2 hne htop)

theorem thm6_of_datum (hP1 : Ih8SmallEdge p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (M : Ih8Model p f Φ t k e) (hLie : HasLieType p f Φ t k) (hne : Φ.Nonempty)
    (hDE : DEdgeless Φ) (htop : (⊤ : Subgroup G) ∉ Φ) :
    HasLieType p f Φ .PSL 3 ∨ HasLieType p f Φ .PSU 3 ∨ HasLieType p f Φ .G2 0 ∨
      HasLieType p f Φ .trialityD4 0 := by
  rcases thm6_tag_of_datum_top hP1 hp2 hq M hne hDE htop with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl hLie
  · exact Or.inr (Or.inl hLie)
  · exact Or.inr (Or.inr (Or.inl hLie))
  · exact Or.inr (Or.inr (Or.inr hLie))

theorem thm6_tag_of_datum_five (hP1 : Ih8SmallEdge p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (M : Ih8Model p f Φ t k e) (hne : Φ.Nonempty) (hDE : DEdgeless Φ) :
    (t = .PSL ∧ k = 2) ∨ (t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3) ∨ (t = .G2 ∧ k = 0) ∨
      (t = .trialityD4 ∧ k = 0) := by
  by_cases hA1 : t = .PSL ∧ k = 2
  · exact Or.inl hA1
  exact Or.inr (thm6_tag_of_datum hP1 hp2 hq M hne hDE hA1)

end Thm6

section Quot

variable {G : Type} [Group G] {Φ : Set (Subgroup G)} {t : StatedLieTag} {k e : ℕ}
  (M : Ih8Model p f Φ t k e)

noncomputable def Ih8Model.quotKerEquiv :
    ((modelUniv t k p e Fact.out).K ⧸ M.ψ.ker) ≃* G :=
  QuotientGroup.quotientKerEquivOfSurjective M.ψ M.surj

theorem Ih8Model.bijective_of_g2d4 (hp2 : p ≠ 2) (ht : t = .G2 ∨ t = .trialityD4) :
    Function.Bijective M.ψ :=
  ⟨RouteD.G2D4.injective_of_ker_le_center hp2 ht k M.admissible.2.1 M.ψ M.ker_le_center, M.surj⟩

end Quot

section SectionThm

variable {Y₀ : Type} [Group Y₀] [Finite Y₀]

omit [Finite Y₀] in
theorem omegaGen_restrictFamily_omegaGen (Ω : Set (Subgroup Y₀)) :
    omegaGen (restrictFamily Ω (omegaGen Ω)) = ⊤ := by
  apply Subgroup.map_injective (omegaGen Ω).subtype_injective
  rw [Subgroup.map_top, Subgroup.range_subtype]
  refine le_antisymm (Subgroup.map_subtype_le _) ?_
  refine iSup₂_le fun L hL => ?_
  have hLY₀ : L ≤ omegaGen Ω := le_omegaGen hL
  have hmem : L.subgroupOf (omegaGen Ω) ≤ omegaGen (restrictFamily Ω (omegaGen Ω)) :=
    le_omegaGen ⟨L, hL, hLY₀, rfl⟩
  calc L = (L.subgroupOf (omegaGen Ω)).map (omegaGen Ω).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hLY₀).symm
    _ ≤ _ := Subgroup.map_mono hmem

theorem section_facts {e : ℕ} (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) {Λ₀ : Set (Subgroup Y₀)}
    (hΩ : HypOmegaMod p e Λ₀) (hne : Λ₀.Nonempty) (hDE : DEdgeless Λ₀) :
    HypOmegaMod p e (oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) ∧
      classicalInvolutionOddCore (↥(omegaGen Λ₀) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ₀)) =
        ⊥ ∧
      omegaGen (oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) = ⊤ ∧
      DEdgeless (oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) ∧
      (oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))).Nonempty := by
  set Y : Subgroup Y₀ := omegaGen Λ₀ with hY
  set N : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : HypOmegaMod p e (restrictFamily Λ₀ Y) := hΩ.restrict Y
  have hΛ' : HypOmegaMod p e (quotFamily (restrictFamily Λ₀ Y) N) :=
    oddQuotHyp p e hp2 h5 ↥Y _ hΛ N hNodd
  refine ⟨hΛ', CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y,
    omegaGen_quotFamily_of_gen _ N (omegaGen_restrictFamily_omegaGen Λ₀),
    dEdgeless_quotFamily hp2 h5 hΛ hΛ' hNodd (dEdgeless_restrictFamily hDE Y), ?_⟩
  obtain ⟨K, hK⟩ := hne
  exact ⟨_, ⟨K.subgroupOf Y, ⟨K, hK, le_omegaGen hK, rfl⟩, rfl⟩⟩

theorem natCard_section_le (Λ₀ : Set (Subgroup Y₀)) :
    Nat.card (↥(omegaGen Λ₀) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ₀)) ≤ Nat.card Y₀ := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (classicalInvolutionOddCore ↥(omegaGen Λ₀))
  have h2 : 0 < Nat.card (classicalInvolutionOddCore ↥(omegaGen Λ₀)) := Nat.card_pos
  have h3 : Nat.card ↥(omegaGen Λ₀) ≤ Nat.card Y₀ := Subgroup.card_le_card_group _
  calc _ ≤ Nat.card (↥(omegaGen Λ₀) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ₀)) *
        Nat.card (classicalInvolutionOddCore ↥(omegaGen Λ₀)) := Nat.le_mul_of_pos_right _ h2
    _ = Nat.card ↥(omegaGen Λ₀) := h1.symm
    _ ≤ Nat.card Y₀ := h3

theorem sectionThm6_exists_datum {e n : ℕ} (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e)
    (hIH : CITBelowU p e n) (hn : Nat.card Y₀ < n) {Λ₀ : Set (Subgroup Y₀)}
    (hΩ : HypOmegaMod p e Λ₀) (hne : Λ₀.Nonempty) (hDE : DEdgeless Λ₀) :
    ∃ (t : StatedLieTag) (k e' : ℕ)
      (_ : Ih8Model p e (oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) t k e'),
      HasLieType p e (oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) t k := by
  obtain ⟨hΦ, hO, hgen, hDEΦ, hneΦ⟩ := section_facts hp2 h5 hΩ hne hDE
  exact exists_datum_of_dEdgeless hIH ((natCard_section_le Λ₀).trans_lt hn) hΦ hO hgen hDEΦ hneΦ

theorem sectionThm6_datum {e n : ℕ} (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) (hP1 : Ih8SmallEdge p)
    (hIH : CITBelowU p e n) (hn : Nat.card Y₀ < n) {Λ₀ : Set (Subgroup Y₀)}
    (hΩ : HypOmegaMod p e Λ₀) (hne : Λ₀.Nonempty) (hDE : DEdgeless Λ₀)
    (hTop : (⊤ : Subgroup (↥(omegaGen Λ₀) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ₀))) ∉
      oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) :
    ∃ (t : StatedLieTag) (k e' : ℕ)
      (_ : Ih8Model p e (oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) t k e'),
      (t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3) ∨ (t = .G2 ∧ k = 0) ∨
        (t = .trialityD4 ∧ k = 0) := by
  obtain ⟨hΦ, hO, hgen, hDEΦ, hneΦ⟩ := section_facts hp2 h5 hΩ hne hDE
  obtain ⟨t, k, e', M, -⟩ := sectionThm6_exists_datum hp2 h5 hIH hn hΩ hne hDE
  exact ⟨t, k, e', M, thm6_tag_of_datum_top hP1 hp2 h5 M hneΦ hDEΦ hTop⟩

theorem sectionThm6 {e n : ℕ} (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) (hP1 : Ih8SmallEdge p)
    (hIH : CITBelowU p e n) (hn : Nat.card Y₀ < n) {Λ₀ : Set (Subgroup Y₀)}
    (hΩ : HypOmegaMod p e Λ₀) (hne : Λ₀.Nonempty) (hDE : DEdgeless Λ₀)
    (hTop : (⊤ : Subgroup (↥(omegaGen Λ₀) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ₀))) ∉
      oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) :
    SectionLieType p e Λ₀ (omegaGen Λ₀) .PSL 3 ∨ SectionLieType p e Λ₀ (omegaGen Λ₀) .PSU 3 ∨
      SectionLieType p e Λ₀ (omegaGen Λ₀) .G2 0 ∨
        SectionLieType p e Λ₀ (omegaGen Λ₀) .trialityD4 0 := by
  obtain ⟨hΦ, hO, hgen, hDEΦ, hneΦ⟩ := section_facts hp2 h5 hΩ hne hDE
  obtain ⟨t, k, e', M, hLie⟩ := sectionThm6_exists_datum hp2 h5 hIH hn hΩ hne hDE
  rcases thm6_of_datum hP1 hp2 h5 M hLie hneΦ hDEΦ hTop with h | h | h | h
  · exact Or.inl (sectionLieType_of_hasLieType hgen h)
  · exact Or.inr (Or.inl (sectionLieType_of_hasLieType hgen h))
  · exact Or.inr (Or.inr (Or.inl (sectionLieType_of_hasLieType hgen h)))
  · exact Or.inr (Or.inr (Or.inr (sectionLieType_of_hasLieType hgen h)))

theorem sectionThm6_five {e n : ℕ} (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) (hP1 : Ih8SmallEdge p)
    (hIH : CITBelowU p e n) (hn : Nat.card Y₀ < n) {Λ₀ : Set (Subgroup Y₀)}
    (hΩ : HypOmegaMod p e Λ₀) (hne : Λ₀.Nonempty) (hDE : DEdgeless Λ₀) :
    SectionLieType p e Λ₀ (omegaGen Λ₀) .PSL 2 ∨ SectionLieType p e Λ₀ (omegaGen Λ₀) .PSL 3 ∨
      SectionLieType p e Λ₀ (omegaGen Λ₀) .PSU 3 ∨ SectionLieType p e Λ₀ (omegaGen Λ₀) .G2 0 ∨
        SectionLieType p e Λ₀ (omegaGen Λ₀) .trialityD4 0 := by
  obtain ⟨hΦ, hO, hgen, hDEΦ, hneΦ⟩ := section_facts hp2 h5 hΩ hne hDE
  obtain ⟨t, k, e', M, hLie⟩ := sectionThm6_exists_datum hp2 h5 hIH hn hΩ hne hDE
  rcases thm6_tag_of_datum_five hP1 hp2 h5 M hneΦ hDEΦ with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl (sectionLieType_of_hasLieType hgen hLie)
  · exact Or.inr (Or.inl (sectionLieType_of_hasLieType hgen hLie))
  · exact Or.inr (Or.inr (Or.inl (sectionLieType_of_hasLieType hgen hLie)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (sectionLieType_of_hasLieType hgen hLie))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (sectionLieType_of_hasLieType hgen hLie))))

end SectionThm

end CFSG.ClassicalInvolution.Asc77
