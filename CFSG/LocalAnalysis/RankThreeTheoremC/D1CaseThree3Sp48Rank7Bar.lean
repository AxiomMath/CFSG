module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Perm
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanThreeCoverInvolve
import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G]

theorem catGroup_facts {d : TauCeti.ValidLieTypeIndex} (hd : IsCaseTwoIndex 3 d) :
    IsSimpleGroup (CatGroup d) ∧ Nat.card (CatGroup d) = 504 := by
  have h : IsCaseTwoGroup 3 (CatGroup d) := ⟨d, hd, ⟨MulEquiv.refl _⟩⟩
  exact ⟨isSimpleGroup_of_isCaseTwoGroup_three h,
    (CFSG.AGLEmbedding.KFactProofs.ThreeCover.l28_facts h).1⟩

theorem exists_bar_section {M S L : Subgroup G} (hLM : L ≤ M) (h : HasL28Quot S L) :
    ∃ (B : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (d : TauCeti.ValidLieTypeIndex)
      (ψ : ↥B →* CatGroup d),
      B ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) ∧
      barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≤
        Subgroup.normalizer (B : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      IsCaseTwoIndex 3 d ∧ Function.Surjective ψ := by
  obtain ⟨T, hTN, hNT, d, ψ, hd, hψ⟩ := h
  have hTM : T ≤ M := hTN.trans (inf_le_right.trans hLM)
  obtain ⟨hY, hcard⟩ := catGroup_facts hd
  let f : T →* ↥M ⧸ CFSG.pCore 2 ↥M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hTM)
  have hker : IsPGroup 2 f.ker := by
    refine (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).of_injective
      (((Subgroup.inclusion hTM).comp f.ker.subtype).codRestrict (CFSG.pCore 2 ↥M) fun x => ?_) ?_
    · exact (QuotientGroup.eq_one_iff _).mp x.2
    · intro x y hxy
      have h1 := congrArg (Subtype.val : ↥(CFSG.pCore 2 ↥M) → ↥M) hxy
      exact Subtype.ext (Subtype.ext (congrArg (Subtype.val : ↥M → G) h1))
  obtain ⟨ψ', hψ'⟩ := exists_surjective_range_of_isPGroup_ker f hker ψ hψ hY hcard
  refine ⟨f.range, d, ψ', ?_, ?_, hd, hψ'⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨⟨t, hTM t.2⟩, Subgroup.mem_subgroupOf.mpr (hTN t.2), rfl⟩
  · refine le_normalizer_of_forall_map_conj_le fun x hx => ?_
    obtain ⟨n, hn, rfl⟩ := hx
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    have hnN : (n : G) ∈ Subgroup.normalizer (S : Set G) ⊓ L := Subgroup.mem_subgroupOf.mp hn
    have hnt : (n : G) * t * (n : G)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hNT hnN) t).mp t.2
    refine ⟨⟨_, hnt⟩, ?_⟩
    have e : (⟨(n : G) * t * (n : G)⁻¹, hTM hnt⟩ : ↥M) = n * ⟨t, hTM t.2⟩ * n⁻¹ := rfl
    change QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(n : G) * t * (n : G)⁻¹, hTM hnt⟩ = _
    rw [e]
    simp [MulAut.conj_apply, f]
    rfl

theorem not_hasL28Quot_of_nineThreeFour {M S L : Subgroup G} (hLM : L ≤ M)
    (h4 : NineThreeFour M S L) : ¬ HasL28Quot S L := by
  intro hq
  obtain ⟨B, d, ψ, hBP, -, hd, hψ⟩ := exists_bar_section hLM hq
  obtain ⟨hY, hcard⟩ := catGroup_facts hd
  obtain ⟨-, hZ, -, -, hP⟩ := h4
  have hBL : B ≤ barM M L := hBP.trans (barM_mono inf_le_right)
  exact false_of_central_extension_section (Subgroup.center ↥(barM M L)) hZ
    ((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L)) hP
    (B.subgroupOf (barM M L)) (Subgroup.subgroupOf_mono _ hBP) hcard
    (ψ.comp (Subgroup.subgroupOfEquivOfLe hBL).toMonoidHom)
    (hψ.comp (Subgroup.subgroupOfEquivOfLe hBL).surjective)

theorem not_hasL28Quot_of_nineThreeFive {M S L : Subgroup G} (hLM : L ≤ M)
    (h5 : NineThreeFive M L) : ¬ HasL28Quot S L := by
  intro hq
  obtain ⟨B, d, ψ, hBP, -, hd, hψ⟩ := exists_bar_section hLM hq
  obtain ⟨hY, hcard⟩ := catGroup_facts hd
  obtain ⟨-, ⟨e⟩, -⟩ := h5
  have hBL : B ≤ barM M L := hBP.trans (barM_mono inf_le_right)
  exact false_of_alt_seven_section e (B.subgroupOf (barM M L)) hY hcard
    (ψ.comp (Subgroup.subgroupOfEquivOfLe hBL).toMonoidHom)
    (hψ.comp (Subgroup.subgroupOfEquivOfLe hBL).surjective)

theorem isPGroup_ker_comp_quotient {J Q : Type*} [Group J] [Group Q]
    (e : J ⧸ CFSG.pCore 2 J ≃* Q) :
    IsPGroup 2 (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 J))).ker := by
  refine (CFSG.pCore_isPGroup (p := 2) (G := J)).to_le fun x hx => ?_
  have h1 : e (QuotientGroup.mk' (CFSG.pCore 2 J) x) = 1 := hx
  rw [e.map_eq_one_iff] at h1
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem exists_normal_section {M S L : Subgroup G} (hLM : L ≤ M) (h : HasL28Quot S L) :
    ∃ (B : Subgroup ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L))) (d : TauCeti.ValidLieTypeIndex)
      (ψ : ↥B →* CatGroup d), B.Normal ∧ IsCaseTwoIndex 3 d ∧ Function.Surjective ψ := by
  obtain ⟨B, d, ψ, hBP, hPN, hd, hψ⟩ := exists_bar_section hLM h
  refine ⟨B.subgroupOf (barM M (Subgroup.normalizer (S : Set G) ⊓ L)), d,
    ψ.comp (Subgroup.subgroupOfEquivOfLe hBP).toMonoidHom, ?_, hd,
    hψ.comp (Subgroup.subgroupOfEquivOfLe hBP).surjective⟩
  rw [Subgroup.normal_subgroupOf_iff hBP]
  intro b k hb hk
  exact (Subgroup.mem_normalizer_iff.mp (hPN hk) b).mp hb

theorem not_hasL28Quot_of_perm {M S L : Subgroup G} (hLM : L ≤ M) {n : ℕ}
    (e : ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ≃* Equiv.Perm (Fin n)) :
    ¬ HasL28Quot S L := by
  intro hq
  obtain ⟨B, d, ψ, hB, hd, hψ⟩ := exists_normal_section hLM hq
  obtain ⟨hY, hcard⟩ := catGroup_facts hd
  exact false_of_perm_section _ (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (isPGroup_ker_comp_quotient e) B ψ hψ hY hcard

theorem not_hasL28Quot_of_perm_prod {M S L : Subgroup G} (hLM : L ≤ M) {r s : ℕ}
    (e : ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ≃*
        Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) :
    ¬ HasL28Quot S L := by
  intro hq
  obtain ⟨B, d, ψ, hB, hd, hψ⟩ := exists_normal_section hLM hq
  obtain ⟨hY, hcard⟩ := catGroup_facts hd
  exact false_of_perm_prod_section _ (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (isPGroup_ker_comp_quotient e) B ψ hψ hY hcard

theorem nineThreeTwo_of_hasL28Quot [Finite G] (hK3c : KFactBlockL28Transvection)
    {M S L : Subgroup G} (hyps : BlockL28Hyps M S L) (hq : HasL28Quot S L) :
    NineThreeTwo M S L := by
  have hLM : L ≤ M := hyps.2.2.1.le
  rcases hyps.2.2.2.1 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hyps.2.2.2.2.1
  · exact h2
  · exact absurd hq (hK3c G M S L hyps h3)
  · exact absurd hq (not_hasL28Quot_of_nineThreeFour hLM h4)
  · exact absurd hq (not_hasL28Quot_of_nineThreeFive hLM h5)
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    exact absurd hq (not_hasL28Quot_of_perm hLM e)
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    exact absurd hq (not_hasL28Quot_of_perm hLM e)
  · obtain ⟨-, N, r, -, -, -, -, -, -, φ, -⟩ := h8
    exact absurd hq (not_hasL28Quot_of_perm_prod hLM φ)

end CFSG.LocalAnalysis.RankThreeTheoremC
