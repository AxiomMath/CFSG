module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiHyp43
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78Inputs
import CFSG.LocalAnalysis.OddStandard.GlueAlt
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bActor

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin (ffJ IsFFStarOffender IsSylowIn)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (Pset)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)

@[expose] def GomiLemma44 : Prop :=
  ∀ {Ω : Type} [Group Ω] [Finite Ω] (G : Subgroup Ω), GomiHyp43 G →
    ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
      ∀ Y : Subgroup (MulAut U), CFSG.SignalizerFunctorTheorem.IsSectionOf ↥Y ↥G →
        ∀ L : Subgroup (MulAut U), L ≤ Y → CFSG.IsComponent (L.subgroupOf Y) →
          CFSG.pCore 2 ↥L = ⊥ → ⁅L, ffJ Y⁆ ≠ ⊥ → GomiHyp43Type ↥L

section Aux

private theorem isSectionOf_trans {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (h₁ : CFSG.SignalizerFunctorTheorem.IsSectionOf X Y)
    (h₂ : CFSG.SignalizerFunctorTheorem.IsSectionOf Y Z) :
    CFSG.SignalizerFunctorTheorem.IsSectionOf X Z := by
  obtain ⟨K₁, f₁, hf₁⟩ := h₁
  obtain ⟨K₂, f₂, hf₂⟩ := h₂
  have hsurj : Function.Surjective (f₂.subgroupComap K₁) := by
    rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := hf₂ y
    exact ⟨⟨z, hy⟩, rfl⟩
  refine ⟨(K₁.comap f₂).map K₂.subtype,
    (f₁.comp (f₂.subgroupComap K₁)).comp
      ((K₁.comap f₂).equivMapOfInjective K₂.subtype K₂.subtype_injective).symm.toMonoidHom,
    fun x => ?_⟩
  obtain ⟨k, rfl⟩ := (hf₁.comp hsurj) x
  exact ⟨(K₁.comap f₂).equivMapOfInjective K₂.subtype K₂.subtype_injective k, by simp⟩

private theorem odd_card_center_of_pCore {L : Type} [Group L] [Finite L]
    (h : CFSG.pCore 2 L = ⊥) : Odd (Nat.card (Subgroup.center L)) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center L)) 2 h2
  set N := Subgroup.zpowers (z : L)
  have hN2 : IsPGroup 2 ↥N := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one])
  have hNn : N.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hc : g * (z : L) = (z : L) * g := (Subgroup.mem_center_iff.mp z.2 g)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have : g * (z : L) ^ k * g⁻¹ = (z : L) ^ k := by
      rw [(Commute.zpow_right (show Commute g (z : L) from hc) k).eq, mul_assoc, mul_inv_cancel,
        mul_one]
    rw [this]
    exact Subgroup.zpow_mem_zpowers _ _
  have hle : N ≤ CFSG.pCore 2 L := le_sSup ⟨hNn, hN2⟩
  rw [h] at hle
  have hz1 : (z : L) = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
  have : z = 1 := Subtype.ext hz1
  rw [this, orderOf_one] at hz
  omega

variable {Y Y' : Type} [Group Y] [Group Y']

private theorem isChevTwo_of_mulEquiv (e : Y ≃* Y') (h : IsChevTwo Y) : IsChevTwo Y' := by
  rcases h with ⟨d, hd, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.symm.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hd, ⟨e.symm.trans f⟩⟩)

private theorem isGomiU3_of_mulEquiv (e : Y ≃* Y') (h : IsGomiU3 Y) : IsGomiU3 Y' := by
  obtain ⟨d, hd, ⟨f⟩⟩ := h
  exact ⟨d, hd, ⟨e.symm.trans f⟩⟩

private theorem isGomiSz_of_mulEquiv (e : Y ≃* Y') (h : IsGomiSz Y) : IsGomiSz Y' := by
  obtain ⟨d, hd, ⟨f⟩⟩ := h
  exact ⟨d, hd, ⟨e.symm.trans f⟩⟩

theorem card_center_dvd_six_of_schur
    (hSA : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    {K : Type*} [Group K] [Group.IsPerfect K]
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 7)) :
    Nat.card (Subgroup.center K) ∣ 6 := by
  let q : K →* alternatingGroup (Fin 7) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hd : Nat.card q.ker ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin 7))) := by
    rw [← CFSG.RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker.le]
    exact Subgroup.card_map_dvd _ _
  have h6 := (hSA 7 (by norm_num)).2
  rw [if_pos (Or.inr rfl)] at h6
  rwa [hker, h6] at hd

private noncomputable def centerQuotientEquiv (e : Y ≃* Y') :
    (Y ⧸ Subgroup.center Y) ≃* (Y' ⧸ Subgroup.center Y') :=
  QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y') e (Subgroup.map_center_eq e)

end Aux

private theorem false_of_center_three (h37 : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2
    = 1) → ∀ Y S L : Subgroup (MulAut W), GomiFact37Hyp Y S L → ⁅L, ffJ Y⁆ ≠ ⊥ → ¬
    (CFSG.IsQuasisimple ↥L ∧ Nat.card (Subgroup.center ↥L) = 3 ∧ IsAlt (↥L ⧸ Subgroup.center ↥L)
    7)) {U : Type} [CommGroup U]
    [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) {Y L : Subgroup (MulAut U)} (hLY : L ≤ Y)
    (hLcomp : CFSG.IsComponent (L.subgroupOf Y)) (hLq : CFSG.IsQuasisimple ↥L)
    (hLJ : ⁅L, ffJ Y⁆ ≠ ⊥) (h : Nat.card (Subgroup.center ↥L) = 3)
    (eA : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)) : False := by
  have hP : (Pset Y).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    apply hLJ
    have hJ0 : ffJ Y = ⊥ := by
      refine le_bot_iff.mp (iSup₂_le fun A hA => ?_)
      have hA' : A ∈ Pset Y := hA
      rw [hne] at hA'
      exact absurd hA' (Set.notMem_empty A)
    rw [hJ0, Subgroup.commutator_bot_right]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 ↥Y))
  have hS : IsSylowIn 2 ((Q : Subgroup ↥Y).map Y.subtype) Y := by
    refine ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, ?_⟩
    rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
    exact Q.not_dvd_index
  have hcardL : Nat.card ↥L = 3 * 2520 := by
    rw [← Subgroup.card_mul_index (Subgroup.center ↥L), h, Subgroup.index_eq_card,
      Nat.card_congr eA.toEquiv, nat_card_alternatingGroup]
    simp
    decide
  have h3 : ¬ Nonempty (↥L ≃* alternatingGroup (Fin 3)) := by
    rintro ⟨φ⟩
    have := Nat.card_congr φ.toEquiv
    rw [hcardL, nat_card_alternatingGroup] at this
    simp [Nat.factorial] at this
  have hhyp : GomiFact37Hyp Y ((Q : Subgroup ↥Y).map Y.subtype) L :=
    ⟨hP, hS, hLY, hLcomp.2, Or.inr ⟨hLq, h, ⟨eA⟩⟩, fun h3' => absurd h3' h3⟩
  exact h37 U hU Y _ L hhyp hLJ ⟨hLq, h, ⟨eA⟩⟩

private theorem card_center_eq_one
    (hSA : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (h37 : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → ∀ Y S L : Subgroup (MulAut
        W), GomiFact37Hyp Y S L → ⁅L, ffJ Y⁆ ≠ ⊥ → ¬ (CFSG.IsQuasisimple ↥L ∧ Nat.card
        (Subgroup.center ↥L) = 3 ∧ IsAlt (↥L ⧸ Subgroup.center ↥L)
        7)) {U : Type} [CommGroup U] [Finite U] (hU : ∀ u : U, u ^ 2 = 1)
    {Y L : Subgroup (MulAut U)} (hLY : L ≤ Y) (hLcomp : CFSG.IsComponent (L.subgroupOf Y))
    (hLq : CFSG.IsQuasisimple ↥L) (hO2 : CFSG.pCore 2 ↥L = ⊥) (hLJ : ⁅L, ffJ Y⁆ ≠ ⊥)
    {n : ℕ} (hn7 : 7 ≤ n) (eA : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin n)) :
    Nat.card (Subgroup.center ↥L) = 1 := by
  have hodd := odd_card_center_of_pCore hO2
  have : Group.IsPerfect ↥L := hLq.1
  by_cases h8 : 8 ≤ n
  · have hle := CFSG.OddStandard.GlueAlt.card_center_le_two_of_alt h8 eA
    obtain ⟨k, hk⟩ := hodd
    omega
  · obtain rfl : n = 7 := by omega
    have h6 := card_center_dvd_six_of_schur hSA eA
    have hpos : 0 < Nat.card (Subgroup.center ↥L) := Nat.card_pos
    have hle : Nat.card (Subgroup.center ↥L) ≤ 6 := Nat.le_of_dvd (by norm_num) h6
    interval_cases h : Nat.card (Subgroup.center ↥L)
    · rfl
    · exact absurd hodd (by decide)
    · exact (false_of_center_three h37 hU hLY hLcomp hLq hLJ h eA).elim
    · exact absurd hodd (by decide)
    · exact absurd h6 (by decide)
    · exact absurd hodd (by decide)

private theorem exists_type (h34 : GomiFact34) {Ω : Type} [Group Ω] [Finite Ω]
    {G : Subgroup Ω} (hG : GomiHyp43 G) {U : Type} [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) {Y : Subgroup (MulAut U)}
    (hYsec : CFSG.SignalizerFunctorTheorem.IsSectionOf ↥Y ↥G) {L : Subgroup (MulAut U)}
    (hLY : L ≤ Y) (hLcomp : CFSG.IsComponent (L.subgroupOf Y)) (hLq : CFSG.IsQuasisimple ↥L)
    (hO2 : CFSG.pCore 2 ↥L = ⊥) (hLJ : ⁅L, ffJ Y⁆ ≠ ⊥) :
    ∃ (K : Type) (_ : Group K), GomiHyp43Type K ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* (↥L ⧸ Subgroup.center ↥L)) := by
  have hJ : ¬ ffJ Y ≤ Subgroup.centralizer (L : Set (MulAut U)) := by
    intro hle
    apply hLJ
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (Subgroup.mem_centralizer_iff.mp (hle hj) l hl).symm
  obtain ⟨W', _, _, hW', X, A, K, hquad, f, hf⟩ := h34 U hU Y L hLY hLcomp hO2 hJ
  have hKq : CFSG.IsQuasisimple ↥K := hquad.2.2.2.1
  have hLsec : CFSG.SignalizerFunctorTheorem.IsSectionOf ↥L ↥Y :=
    ⟨L.subgroupOf Y, (Subgroup.subgroupOfEquivOfLe hLY).toMonoidHom,
      (Subgroup.subgroupOfEquivOfLe hLY).surjective⟩
  have hKsec : CFSG.SignalizerFunctorTheorem.IsSectionOf ↥K ↥G :=
    isSectionOf_trans (isSectionOf_trans ⟨⊤, f.comp (⊤ : Subgroup ↥L).subtype, fun k => by
      obtain ⟨l, rfl⟩ := hf k
      exact ⟨⟨l, trivial⟩, rfl⟩⟩ hLsec) hYsec
  have hKtype : GomiHyp43Type ↥K :=
    hG.sections ↥K hKq hKsec
      ⟨W', inferInstance, inferInstance, hW', X, A, K, hquad, ⟨MulEquiv.refl _⟩⟩
  have hrange : f.range = ⊤ := MonoidHom.range_eq_top.mpr hf
  have hne : f.range ≠ ⊥ := by
    rw [hrange]
    have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
    exact top_ne_bot
  obtain ⟨-, ⟨e₁⟩⟩ := CFSG.QuasithinUnique.Setup.X5.quasisimple_range_centerQuotientEquiv hLq f hne
  have eK : ↥f.range ≃* ↥K := (MulEquiv.subgroupCongr hrange).trans Subgroup.topEquiv
  exact ⟨↥K, inferInstance, hKtype, ⟨(centerQuotientEquiv eK).symm.trans e₁⟩⟩

theorem gomiLemma44_of_facts
    (hSA : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (h34 : GomiFact34) (h37 : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → ∀ Y S L
        : Subgroup (MulAut W), GomiFact37Hyp Y S L → ⁅L, ffJ Y⁆ ≠ ⊥ → ¬ (CFSG.IsQuasisimple ↥L ∧
        Nat.card (Subgroup.center ↥L) = 3 ∧ IsAlt (↥L ⧸ Subgroup.center ↥L) 7)) : GomiLemma44 := by
  intro Ω _ _ G hG U _ _ hU Y hYsec L hLY hLcomp hO2 hLJ
  have hLq : CFSG.IsQuasisimple ↥L :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hLY)).mp hLcomp.1
  obtain ⟨K, _, hKtype, ⟨eZ⟩⟩ := exists_type h34 hG hU hYsec hLY hLcomp hLq hO2 hLJ
  rcases hKtype with ⟨hch, hU3, hSz⟩ | ⟨n, hn7, ⟨g⟩⟩
  · exact Or.inl ⟨⟨hLq, hO2, isChevTwo_of_mulEquiv eZ hch.2.2⟩,
      fun h => hU3 (isGomiU3_of_mulEquiv eZ.symm h), fun h => hSz (isGomiSz_of_mulEquiv eZ.symm h)⟩
  · refine Or.inr ⟨n, hn7, ?_⟩
    have hZA : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
      alternatingGroup.center_eq_bot (by simp; omega)
    have hZK : Subgroup.center K = ⊥ := by
      have hmap := Subgroup.map_center_eq g
      rw [hZA] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective _ g.injective).mp hmap
    have eA : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin n) :=
      eZ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZK).trans
        (QuotientGroup.quotientBot.trans g))
    have hbot : Subgroup.center ↥L = ⊥ := Subgroup.card_eq_one.mp
      (card_center_eq_one hSA h37 hU hLY hLcomp hLq hO2 hLJ hn7 eA)
    exact ⟨(QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans eA⟩

end CFSG.GroupTheory
