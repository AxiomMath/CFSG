module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Candidates
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalog

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique.Setup.Family CFSG.SectionRank

theorem isSQT_of_injective {G G' : Type} [Group G] [Group G'] [Finite G'] (f : G →* G')
    (hf : Function.Injective f) (h : CFSG.IsStronglyQuasithin G') : CFSG.IsStronglyQuasithin G := by
  have : Finite G := Finite.of_injective f hf
  rw [isStronglyQuasithin_iff] at h ⊢
  intro q hq hq2
  exact (pRank_top_le_of_injective hq.one_lt f hf).trans (h q hq hq2)

theorem odd_card_center_of_component {V : Type} [CommGroup V] [Finite V]
    {H T M : Subgroup (MulAut V)} (hAL : ActorLayer V H T M) {L : Subgroup (MulAut V)}
    (hL : IsComp L H) : Odd (Nat.card (Subgroup.center ↥L)) := by
  have hLK : L ≤ oddOrderSubgroup H := by
    rw [← hAL.components_generate]
    exact le_iSup₂ (f := fun (L : Subgroup (MulAut V)) (_ : IsComp L H) => L) L hL
  have hcentral : (Subgroup.center ↥L).map L.subtype ≤ radIn H := by
    rintro _ ⟨z, hz, rfl⟩
    have hcomm : ∀ x ∈ oddOrderSubgroup H, x * (z : MulAut V) = (z : MulAut V) * x := by
      intro x hx
      have hle : oddOrderSubgroup H ≤ Subgroup.centralizer ({(z : MulAut V)} : Set (MulAut V)) := by
        rw [← hAL.components_generate]
        refine iSup₂_le fun L' hL' => ?_
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        by_cases hLL : L' = L
        · subst hLL
          have := Subgroup.mem_center_iff.1 hz ⟨y, hy⟩
          exact congrArg Subtype.val this.symm
        · exact (hAL.components_commute L L' hL hL' (Ne.symm hLL) z z.2 y hy)
      have := Subgroup.mem_centralizer_iff.1 (hle hx) (z : MulAut V) rfl
      exact this.symm
    rw [hAL.rad_eq_fitting, hAL.fitting_eq_center]
    exact ⟨hLK z.2, fun x hx => hcomm x hx⟩
  have hcard : Nat.card (Subgroup.center ↥L) ∣ Nat.card (radIn H) := by
    have := Subgroup.card_dvd_of_le hcentral
    rwa [Subgroup.card_map_of_injective L.subtype_injective] at this
  exact Odd.of_dvd_nat hAL.rad_odd hcard


theorem exists_section_data {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    {L A : Subgroup (MulAut V)} (hLq : CFSG.IsQuasisimple ↥L)
    (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut V))) (S : IrrSection V L A) :
    ∃ (W : Type) (_ : CommGroup W) (_ : Finite W) (Lb Ab : Subgroup (MulAut W)),
      (∀ w : W, w * w = 1) ∧ CFSG.IsQuasisimple ↥Lb ∧ IsIrrOn Lb ∧ Nonempty (CQ Lb ≃* CQ L) ∧
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

theorem false_of_two_extension {s : TauCeti.SporadicName} (hTwo : TwoExtensionFor s) {V : Type}
    [CommGroup V] [Finite V] {T M L : Subgroup (MulAut V)} (hT : ComponentTransfer V T M L)
    (e : ↥L ≃* NativeSporadic.Carrier s) : False := by
  have hLY : L ≤ HL T L := le_sup_left
  have hTY : TL T L ≤ HL T L := le_sup_right
  have hnormL : HL T L ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    sup_le Subgroup.le_normalizer inf_le_right
  have hKnorm : (L.subgroupOf (HL T L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).2 hnormL
  have hTp : IsPGroup 2 ((TL T L).subgroupOf (HL T L)) := hT.sylow.2.1.comap_subtype
  have hsup : L.subgroupOf (HL T L) ⊔ (TL T L).subgroupOf (HL T L) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hLY hTY]
    exact Subgroup.subgroupOf_self _
  have hiso : ↥(L.subgroupOf (HL T L)) ≃* NativeSporadic.Carrier s :=
    (Subgroup.subgroupOfEquivOfLe hLY).trans e
  obtain ⟨U₁, U₂, hne, hU₁, hU₂, hT₁, hT₂⟩ := hTwo ↥(HL T L) ((TL T L).subgroupOf (HL T L))
    (L.subgroupOf (HL T L)) hKnorm hTp hT.sylow.2.2 hsup ⟨hiso⟩
  have hP : (XL M T L).subgroupOf (HL T L) ≠ ⊤ := by
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact (hT.unique_max.1).not_ge h
  have hlemma : ∀ U : Subgroup ↥(HL T L), IsCoatom U → (TL T L).subgroupOf (HL T L) ≤ U →
      U = (XL M T L).subgroupOf (HL T L) := by
    intro U hU hTU
    have hY1 : U.map (HL T L).subtype ≤ XL M T L := by
      apply hT.unique_max.2.2
      · intro x hx
        exact ⟨⟨x, hTY hx⟩, hTU (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
      · refine lt_of_le_of_ne (Subgroup.map_subtype_le U) ?_
        intro h
        apply hU.1
        rw [eq_top_iff]
        intro u _
        have hu : (u : MulAut V) ∈ U.map (HL T L).subtype := by rw [h]; exact u.2
        obtain ⟨u', hu', hu'u⟩ := hu
        have : u' = u := Subtype.ext hu'u
        exact this ▸ hu'
    have hUP : U ≤ (XL M T L).subgroupOf (HL T L) := fun u hu => hY1 ⟨u, hu, rfl⟩
    exact ((hU.le_iff.1 hUP).resolve_left hP).symm
  exact hne ((hlemma U₁ hU₁ hT₁).trans (hlemma U₂ hU₂ hT₂).symm)

theorem nonempty_mulEquiv_of_cover_trivial {L S : Type} [Group L] [Group S]
    (e : (L ⧸ Subgroup.center L) ≃* S) (hZodd : Odd (Nat.card (Subgroup.center L)))
    (hcov : ∀ π : L →* S, Function.Surjective π → π.ker ≤ Subgroup.center L →
      Odd (Nat.card π.ker) → π.ker = ⊥) : Nonempty (L ≃* S) := by
  set π : L →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)) with hπ
  have hsurj : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center L := by
    ext x
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hbot : Subgroup.center L = ⊥ := by
    rw [← hker]
    exact hcov π hsurj hker.le (by rw [hker]; exact hZodd)
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm.trans e⟩

theorem noSporadicComponent_of
    (hJ4ord : J4OrderHyp) (hLayer : ActorLayerProp)
    (hTrans : ComponentTransferProp) (hSec : IrreducibleSectionProp)
    (hExcl : SporadicExclusion .M11 ∧ SporadicExclusion .M12 ∧ SporadicExclusion .M22 ∧
      SporadicExclusion .M23 ∧ SporadicExclusion .M24 ∧ SporadicExclusion .J1 ∧
      SporadicExclusion .He ∧ SporadicExclusion .J4)
    (hTwo : TwoExtensionFor .J2 ∧ TwoExtensionFor .HS ∧ TwoExtensionFor .Ru) :
    NoSporadicComponentProp := by
  obtain ⟨hM11, hM12, hM22, hM23, hM24, hJ1, hHe, hJ4⟩ := hExcl
  obtain ⟨hJ2t, hHSt, hRut⟩ := hTwo
  intro V _ _ H T M E hFF hns hsqt L hL hrep
  have hAL := hLayer V H T M E hFF hns
  have hLq : CFSG.IsQuasisimple ↥L := isQuasisimple_of_isComp hL
  have hLH : L ≤ H := hL.1
  have hZodd := odd_card_center_of_component hAL hL
  have hSQT_L : CFSG.IsStronglyQuasithin ↥L :=
    isSQT_of_injective (Subgroup.inclusion hLH) (Subgroup.inclusion_injective hLH) hsqt
  have hcat := catalog_sporadic_of hJ4ord ↥L hLq hSQT_L hZodd hrep
  have hSQT_CQ : CFSG.IsStronglyQuasithin (CQ L) := hcat.2 (Subgroup.center ↥L) le_rfl
  have hnt : Nontrivial (CQ L) := by
    obtain ⟨a, b, hab⟩ := hLq.2.2
    exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  have hLne : L ≠ ⊥ := by
    intro h
    have hsub : Subsingleton ↥L := ⟨fun x y => Subtype.ext
      ((Subgroup.mem_bot.1 (h ▸ x.2)).trans (Subgroup.mem_bot.1 (h ▸ y.2)).symm)⟩
    obtain ⟨a, b, hab⟩ := hLq.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (congrArg QuotientGroup.mk (Subsingleton.elim _ _))
  obtain ⟨s, hs, ⟨e⟩⟩ := unique_SQT_sporadic_eleven_candidate_restriction hSQT_CQ hrep
  have hT := hTrans V H T M E hFF hns L hL
  obtain ⟨A, hAle, hAel, hAcomm, hAoff, hAmin⟩ := hT.offender
  have hbest : IsBestOffender H A := by
    have hTH : T ≤ H := hFF.sylow.1
    refine ⟨hAle.trans ((show TL T L ≤ T from inf_le_left).trans hTH), ?_, hAel, hAoff, hAmin⟩
    rintro rfl
    exact hLne (by rw [← hAcomm, Subgroup.commutator_bot_right])
  have hAL_ne : ⁅L, A⁆ ≠ ⊥ := by rw [hAcomm]; exact hLne
  obtain ⟨hAN, -, ⟨S⟩⟩ := hSec V hFF.elementary H L A hL hbest hAL_ne
  obtain ⟨W, _, _, Lb, Ab, hW1, hq, hirr, ⟨ψ⟩, hn, hne, hel, hquad, hoff⟩ :=
    exists_section_data hFF.elementary hLq hAN S
  have hperf : Group.IsPerfect ↥L := hLq.1
  simp only [sqtkSporadicNames, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (hM11 W hW1 Lb Ab hq hirr ⟨ψ.trans e⟩ hn hne hel hquad) (not_lt.2 hoff)
  · exact absurd (hM12 W hW1 Lb Ab hq hirr ⟨ψ.trans e⟩ hn hne hel hquad) (not_lt.2 hoff)
  · exact absurd (hM22 W hW1 Lb Ab hq hirr ⟨ψ.trans e⟩ hn hne hel hquad) (not_lt.2 hoff)
  · exact absurd (hM23 W hW1 Lb Ab hq hirr ⟨ψ.trans e⟩ hn hne hel hquad) (not_lt.2 hoff)
  · exact absurd (hM24 W hW1 Lb Ab hq hirr ⟨ψ.trans e⟩ hn hne hel hquad) (not_lt.2 hoff)
  · exact absurd (hJ1 W hW1 Lb Ab hq hirr ⟨ψ.trans e⟩ hn hne hel hquad) (not_lt.2 hoff)
  · obtain ⟨eL⟩ := nonempty_mulEquiv_of_cover_trivial e hZodd
      fun π hπ hC hodd => J2_perfect_odd_cover_trivial (E := ↥L) π hπ hC hodd
    exact false_of_two_extension hJ2t hT eL
  · exact absurd (hJ4 W hW1 Lb Ab hq hirr ⟨ψ.trans e⟩ hn hne hel hquad) (not_lt.2 hoff)
  · obtain ⟨eL⟩ := nonempty_mulEquiv_of_cover_trivial e hZodd
      fun π hπ hC hodd => HS_perfect_odd_cover_trivial (E := ↥L) π hπ hC hodd
    exact false_of_two_extension hHSt hT eL
  · exact absurd (hHe W hW1 Lb Ab hq hirr ⟨ψ.trans e⟩ hn hne hel hquad) (not_lt.2 hoff)
  · obtain ⟨eL⟩ := nonempty_mulEquiv_of_cover_trivial e hZodd
      fun π hπ hC hodd => Ru_perfect_odd_cover_trivial (E := ↥L) π hπ hC hodd
    exact false_of_two_extension hRut hT eL

end CFSG.QuasithinUnique.Setup.X1
