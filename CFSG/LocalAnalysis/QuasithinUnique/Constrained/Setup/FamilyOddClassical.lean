module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Cover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.LocalAnalysis.SectionRank.Induction
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.Adapters.StatedPSLTwoSeven
public import CFSG.Adapters.LinearFieldTransport

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.Quasithin CFSG.SectionRank CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def PrimeLinearThreeExclusionProp : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ Lb : Subgroup (MulAut W), Group.IsPerfect ↥Lb → X1.IsIrrOn Lb →
      StatedClassicalModel (CQ Lb) .PSL 3 p 1 →
      ∀ B : Subgroup (MulAut W), B ≤ Subgroup.normalizer (Lb : Set (MulAut W)) → B ≠ ⊥ →
        IsElemAbelian2 B → Nat.card B * Nat.card (fixV B) < Nat.card W

@[expose] def PrimeUnitaryThreeExclusionProp : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ Lb : Subgroup (MulAut W), Group.IsPerfect ↥Lb → X1.IsIrrOn Lb →
      StatedClassicalModel (CQ Lb) .PSU 3 p 1 →
      ∀ B : Subgroup (MulAut W), B ≤ Subgroup.normalizer (Lb : Set (MulAut W)) → B ≠ ⊥ →
        IsElemAbelian2 B → Nat.card B * Nat.card (fixV B) < Nat.card W

@[expose] def PrimeSquareExclusionProp : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ Lb : Subgroup (MulAut W), Group.IsPerfect ↥Lb → X1.IsIrrOn Lb →
      StatedClassicalModel (CQ Lb) .PSL 2 p 2 →
      ∀ B : Subgroup (MulAut W), B ≤ Subgroup.normalizer (Lb : Set (MulAut W)) → B ≠ ⊥ →
        IsElemAbelian2 B → Nat.card B * Nat.card (fixV B) < Nat.card W

theorem statedClassicalModel_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {t : StatedLieTag} {n p f : ℕ} (h : StatedClassicalModel G t n p f) :
    StatedClassicalModel G' t n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

theorem equiv_projectiveSL_of_model {S : Type} [Group S] {p : ℕ} [Fact p.Prime]
    (h : StatedClassicalModel S .PSL 2 p 1) : Nonempty (S ≃* projectiveSL 2 (ZMod p)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod p) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one]
  let φ : K ≃+* ZMod p := FiniteField.ringEquivOfCardEq hcard
  exact ⟨e.trans
    (((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2))).trans
    (p2Equiv (ZMod p)).symm)⟩

theorem equiv_SL3_two_of_model_seven {S : Type} [Group S]
    (h : StatedClassicalModel S .PSL 2 7 1) :
    Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  CFSG.Open.StatedAPI.nonempty_mulEquiv_sl_three_two_of_psl_two_seven h

theorem sectionData_of_irrSection {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    {L A : Subgroup (MulAut V)} (hLq : CFSG.IsQuasisimple ↥L)
    (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut V))) (S : X1.IrrSection V L A) :
    ∃ (W : Type) (_ : CommGroup W) (_ : Finite W) (Lb Ab : Subgroup (MulAut W)),
      (∀ w : W, w * w = 1) ∧ CFSG.IsQuasisimple ↥Lb ∧ X1.IsIrrOn Lb ∧ Nonempty (CQ Lb ≃* CQ L) ∧
      Ab ≤ Subgroup.normalizer (Lb : Set (MulAut W)) ∧ Ab ≠ ⊥ ∧ IsElemAbelian2 Ab ∧
      IsQuadratic Ab ∧ Nat.card W ≤ Nat.card Ab * Nat.card (fixV Ab) := by
  set ρ : ↥L →* MulAut S.W := S.τW.comp (Subgroup.inclusion le_sup_left) with hρ
  refine ⟨S.W, S.commGroup, S.finite, ρ.range, (S.τW.comp (Subgroup.inclusion le_sup_right)).range,
    ?_, S.lbar_quasisimple, ?_, ?_, ?_, S.abar_ne_bot, S.abar_elem, S.abar_quadratic,
    S.abar_offender⟩
  · intro w
    obtain ⟨v, rfl⟩ := S.π_surjective w
    rw [← map_mul]
    have : v * v = 1 := Subtype.ext (hV v)
    rw [this, map_one]
  · refine ⟨S.nontrivial, fun U hU => S.irreducible U fun x hx u hu => ?_⟩
    exact hU (S.τW x) ⟨⟨x, hx⟩, congrArg S.τW (Subtype.ext rfl)⟩ u hu
  · have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
    have hφ : ∃ k, ρ.rangeRestrict k ≠ 1 := by
      obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 S.lbar_ne_bot
      obtain ⟨k, hk⟩ := hsurj a
      exact ⟨k, hk ▸ ha⟩
    have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hLq hφ
    exact ⟨(CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hLq hsurj hker).symm⟩
  · have key : ∀ a : ↥(L ⊔ A), (a : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) →
        ∀ y ∈ ρ.range, S.τW a * y * (S.τW a)⁻¹ ∈ ρ.range := by
      rintro a ha _ ⟨l, rfl⟩
      have hl : (a : MulAut V) * (l : MulAut V) * (a : MulAut V)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 ha l).1 l.2
      refine ⟨⟨_, hl⟩, ?_⟩
      have h1 : Subgroup.inclusion (le_sup_left : L ≤ L ⊔ A)
          ⟨(a : MulAut V) * (l : MulAut V) * (a : MulAut V)⁻¹, hl⟩ =
          a * Subgroup.inclusion (le_sup_left : L ≤ L ⊔ A) l * a⁻¹ := Subtype.ext rfl
      rw [hρ, MonoidHom.comp_apply, h1, map_mul, map_mul, map_inv]
      rfl
    rintro _ ⟨a, rfl⟩
    have haN : ((Subgroup.inclusion (le_sup_right : A ≤ L ⊔ A) a : ↥(L ⊔ A)) : MulAut V) ∈
        Subgroup.normalizer (L : Set (MulAut V)) := hAN a.2
    have haN' : (((Subgroup.inclusion (le_sup_right : A ≤ L ⊔ A) a)⁻¹ : ↥(L ⊔ A)) : MulAut V) ∈
        Subgroup.normalizer (L : Set (MulAut V)) := (Subgroup.normalizer _).inv_mem haN
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact key _ haN y hy
    · intro hy
      have := key _ haN' _ hy
      rw [map_inv] at this
      simpa [mul_assoc] using this

theorem isSQTKCat_of_le_aux {G : Type} [Group G] [Finite G] {H L : Subgroup G} (hLH : L ≤ H)
    (hH : IsSQTKCat ↥H) : IsSQTKCat ↥L :=
  CFSG.SectionRank.IsSQTKCat.of_le hLH hH

theorem oddClassicalSmall
    (hcat : CatalogStepHyp) (hlayer : ActorLayerProp)
    (hTrans : X1.ComponentTransferProp) (hSec : X1.IrreducibleSectionProp)
    (hA78 : NoAlt78BinaryLinearProp) (hlin3 : PrimeLinearThreeExclusionProp)
    (huni3 : PrimeUnitaryThreeExclusionProp) (hsq : PrimeSquareExclusionProp) :
    OddClassicalSmallProp := by
  intro V _ _ H T M E hFF hns hSQTK L hL p hp hp2 t n f hmod
  have hLq : CFSG.IsQuasisimple ↥L := isQuasisimple_of_isComp hL
  have hLH : L ≤ H := hL.1
  have hAL : ActorLayer V H T M := hlayer V H T M E hFF hns
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := hAL.odd_card_center hL
  have hSQTK_L : IsSQTKCat ↥L := isSQTKCat_of_le_aux hLH hSQTK
  have hstep : CatalogStepConclusion ↥L := hcat ↥L hLq hSQTK_L hZodd
  have hSQT_S : CFSG.IsStronglyQuasithin (CQ L) := hstep.2 (Subgroup.center ↥L) le_rfl
  have hsqt : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup (CQ L)) ≤ 2 := by
    intro q hq hq2
    exact (isStronglyQuasithin_iff.1 hSQT_S) q hq hq2
  have hres := sqt_odd_classical_restriction hsqt hp2 hmod
  have hLne : L ≠ ⊥ := by
    intro h
    have hsub : Subsingleton ↥L := ⟨fun x y => Subtype.ext
      ((Subgroup.mem_bot.1 (h ▸ x.2)).trans (Subgroup.mem_bot.1 (h ▸ y.2)).symm)⟩
    obtain ⟨a, b, hab⟩ := hLq.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (congrArg QuotientGroup.mk (Subsingleton.elim _ _))
  have hT := hTrans V H T M E hFF hns L hL
  obtain ⟨A, hAle, hAel, hAcomm, hAoff, hAmin⟩ := hT.offender
  have hbest : IsBestOffender H A := by
    have hTH : T ≤ H := hFF.sylow.1
    refine ⟨hAle.trans ((show X1.TL T L ≤ T from inf_le_left).trans hTH), ?_, hAel, hAoff, hAmin⟩
    rintro rfl
    exact hLne (by rw [← hAcomm, Subgroup.commutator_bot_right])
  have hAL_ne : ⁅L, A⁆ ≠ ⊥ := by rw [hAcomm]; exact hLne
  obtain ⟨hAN, -, ⟨S⟩⟩ := hSec V hFF.elementary H L A hL hbest hAL_ne
  obtain ⟨W, _, _, Lb, Ab, hW1, hq, hirr, ⟨ψ⟩, hn, hne, hel, hquad, hoff⟩ :=
    sectionData_of_irrSection hFF.elementary hLq hAN S
  have hperf : Group.IsPerfect ↥Lb := hq.1
  have hmodb : StatedClassicalModel (CQ Lb) t n p f := statedClassicalModel_of_mulEquiv ψ.symm hmod
  have hbig : ∀ q : ℕ, q ≠ 2 → q ≠ 3 → q.Prime → 5 ≤ q := by
    intro q hq2 hq3 hqp
    have h2 := hqp.two_le
    have h4 : q ≠ 4 := by
      rintro rfl
      norm_num at hqp
    omega
  rcases hres with ⟨rfl, rfl, hf12⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rcases hf12 with rfl | rfl
    ·
      have : Fact p.Prime := ⟨hp⟩
      by_cases hp11 : 11 ≤ p
      · exfalso
        have : Nontrivial W := hirr.1
        obtain ⟨α⟩ := equiv_projectiveSL_of_model hmodb
        have h1 := (primeLinearTwoCover hp11 hW1 hperf hirr.2 α).2 Ab hn hne hel
        exact absurd h1 (not_lt.2 hoff)
      · have hp3 : 3 ≤ p := by have := hp.two_le; omega
        interval_cases p
        · exact absurd rfl hmod.1.2.2.2.2
        · norm_num at hp
        · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
        · norm_num at hp
        · exfalso
          obtain ⟨e⟩ := equiv_SL3_two_of_model_seven hmod
          exact (hA78 V H T M E hFF hns L hL).2 3 le_rfl ⟨e⟩
        all_goals norm_num at hp
    ·
      by_cases hp3 : p = 3
      · subst hp3
        exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
      · exfalso
        exact absurd (hsq p hp (hbig p hp2 hp3 hp) W hW1 Lb hperf hirr hmodb Ab hn hne hel)
          (not_lt.2 hoff)
  ·
    exfalso
    exact absurd (hlin3 p hp hp2 W hW1 Lb hperf hirr hmodb Ab hn hne hel) (not_lt.2 hoff)
  ·
    by_cases hp3 : p = 3
    · subst hp3
      exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)
    · exfalso
      exact absurd (huni3 p hp (hbig p hp2 hp3 hp) W hW1 Lb hperf hirr hmodb Ab hn hne hel)
        (not_lt.2 hoff)

end CFSG.QuasithinUnique.Setup.Family
