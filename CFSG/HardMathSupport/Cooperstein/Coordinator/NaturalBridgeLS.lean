module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridge
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.NaturalSectionLS
public import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.Alternating.Multipliers.Small

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped commutatorElement

attribute [local instance] blockVCommGroup

theorem exists_isFFStarOffender_of_isFFModule {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} (hFF : IsFFModule H) : ∃ A, IsFFStarOffender H A := by
  obtain ⟨E, hEH, hE, hel, hoff⟩ := hFF
  obtain ⟨A, -, hA, -⟩ :=
    B1.exists_offender_below (X := H) ⟨hEH, hE, hel⟩ 0 (by simpa using hoff)
  exact ⟨A, hA⟩

theorem card_ker_dvd_card_hopfMultiplier {E S : Type} [Group E] [Group S] [Group.IsPerfect E]
    (q : E →* S) (hq : Function.Surjective q) (hker : q.ker ≤ Subgroup.center E) :
    Nat.card q.ker ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier S) := by
  rw [← CFSG.RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker]
  exact Subgroup.card_map_dvd _ _

theorem ker_comp_mk'_center {K Y : Type} [Group K] [Group Y] (e : K ⧸ Subgroup.center K ≃* Y) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))).ker = Subgroup.center K := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

section Seven


theorem card_center_dvd_six_of_alt7 {K : Type} [Group K] (hK : CFSG.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 7)) : Nat.card (Subgroup.center K) ∣ 6 := by
  have := hK.1
  have h := card_ker_dvd_card_hopfMultiplier (e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (ker_comp_mk'_center e).le
  rwa [ker_comp_mk'_center, (CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_seven).2]
    at h

end Seven

section LS

variable {G : Type} [Group G] {S L : Subgroup G}

theorem map_commV_autOn_blockV {K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (blockV S L : Set G)) :
    (@commV ↥(blockV S L) (blockVCommGroup S L) (autOn K (blockV S L))).map
      (blockV S L).subtype = ⁅blockV S L, K⁆ := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, commV, Subgroup.closure_le]
    rintro _ ⟨σ, hσ, v, rfl⟩
    obtain ⟨g, hgK, rfl⟩ := Setup.mem_autOn_iff.1 hσ
    show (g : G) * v * (g : G)⁻¹ * (v : G)⁻¹ ∈ ⁅blockV S L, K⁆
    have e : (g : G) * v * (g : G)⁻¹ * (v : G)⁻¹ = ⁅(v : G), (g : G)⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (⁅blockV S L, K⁆).inv_mem (Subgroup.commutator_mem_commutator v.2 hgK)
  · rw [Subgroup.commutator_le]
    intro w hw k hk
    have hmem : conjAct (blockV S L) ⟨k, hK hk⟩ ⟨w, hw⟩ * (⟨w, hw⟩ : ↥(blockV S L))⁻¹ ∈
        commV (autOn K (blockV S L)) :=
      Subgroup.subset_closure ⟨_, Setup.mem_autOn_iff.2 ⟨⟨k, hK hk⟩, hk, rfl⟩, ⟨w, hw⟩, rfl⟩
    refine ⟨_, (commV (autOn K (blockV S L))).inv_mem hmem, ?_⟩
    show ((k : G) * w * (k : G)⁻¹ * (w : G)⁻¹)⁻¹ = ⁅w, k⁆
    rw [commutatorElement_def]
    group

theorem mem_fixV_autOn_blockV_iff {K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (blockV S L : Set G)) (w : ↥(blockV S L)) :
    w ∈ @fixV ↥(blockV S L) (blockVCommGroup S L) (autOn K (blockV S L)) ↔
      (w : G) ∈ Subgroup.centralizer (K : Set G) := by
  rw [mem_fixV, Subgroup.mem_centralizer_iff]
  constructor
  · intro hw k hk
    have h1 := congrArg Subtype.val (hw _ (Setup.mem_autOn_iff.2 ⟨⟨k, hK hk⟩, hk, rfl⟩))
    rw [Setup.coe_conjAct_apply] at h1
    calc k * (w : G) = k * w * k⁻¹ * k := by group
      _ = w * k := by rw [h1]
  · intro hw x hx
    obtain ⟨g, hgK, rfl⟩ := Setup.mem_autOn_iff.1 hx
    apply Subtype.ext
    rw [Setup.coe_conjAct_apply, hw g hgK, mul_inv_cancel_right]

variable [Finite G] {X : Subgroup G}

theorem odd_card_center_autOn (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    Odd (Nat.card (Subgroup.center ↥(autOn L (blockV S L)))) := by
  set V := blockV S L with hVdef
  set Gs := autOn (L ⊔ S) V with hGs
  set Ls := autOn L V with hLs
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans (sup_le_normalizer_blockV S L)
  have hLG : Ls ≤ Gs := InternalSec.autOn_le_autOn_of_le le_sup_left
  have hO2 : CFSG.pCore 2 ↥Gs = ⊥ := by
    have h5 := pCoreOf_autOn_sup_eq_bot hA hL hSL
    rw [CFSG.Open.pCoreOf] at h5
    exact (Subgroup.map_eq_bot_iff_of_injective _ Gs.subtype_injective).mp h5
  have hKn : (Ls.subgroupOf Gs).Normal := ⟨fun k hk g => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact InternalSec.autOn_normal_of (sup_le Subgroup.le_normalizer hSL) _ g.2 _ hk⟩
  have h2 : ∀ y : ↥Gs, ∃ e : ℕ, y ^ 2 ^ e ∈ Ls.subgroupOf Gs := by
    intro y
    obtain ⟨e, he⟩ := InternalSec.autOn_two_of (Y := L ⊔ S) hLV (fun z hz => by
      obtain ⟨e, he⟩ := exists_pow_mem_sup hA.twoRadical.isPGroup hSL hz
      exact ⟨e, Subgroup.mem_sup_left he⟩) (y : MulAut ↥V) y.2
    exact ⟨e, by rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]; exact he⟩
  have hodd := StarAux.odd_card_centralizer (Ls.subgroupOf Gs) h2 hO2
  let f : ↥(Subgroup.center ↥Ls) →*
      ↥(Subgroup.centralizer ((Ls.subgroupOf Gs : Subgroup ↥Gs) : Set ↥Gs)) :=
    { toFun := fun z => ⟨⟨((z : ↥Ls) : MulAut ↥V), hLG (z : ↥Ls).2⟩, by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        apply Subtype.ext
        have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨(k : MulAut ↥V), hk⟩)
        exact h1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun a b hab => Subtype.ext (Subtype.ext
    (congrArg (fun x => ((x : ↥Gs) : MulAut ↥V)) (congrArg Subtype.val hab)))
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective f hf)

theorem nonempty_autOn_equiv_alternating (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G)) {m : ℕ}
    (hm : m = 7 ∨ 8 < m)
    (he : Nonempty (↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃*
      alternatingGroup (Fin m)))
    (h94 : GF2NoFFTripleA7) :
    Nonempty (↥(autOn L (blockV S L)) ≃* alternatingGroup (Fin m)) := by
  set V := blockV S L with hVdef
  set Gs := autOn (L ⊔ S) V with hGs
  set Ls := autOn L V with hLs
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v =>
    Subtype.ext ((CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _).2 _ v.2)
  have hLF : Ls = quasithinGenFitting Gs := (quasithinGenFitting_autOn_sup hA hL hSL).symm
  have hq := isQuasisimple_autOn hA hL hSL
  obtain ⟨B, hB⟩ := exists_isFFStarOffender_of_isFFModule (isFFModule_autOn_blockV hA hL hSL)
  obtain ⟨e1⟩ := nonempty_autOnCenterQuotientEquiv hA hL hSL
  obtain ⟨e2⟩ := he
  have eq : ↥Ls ⧸ Subgroup.center ↥Ls ≃* alternatingGroup (Fin m) :=
    (e1.trans (barMSupCenterEquiv hA hL hSL)).trans e2
  have hodd := odd_card_center_autOn hA hL hSL
  have hZ : Subgroup.center ↥Ls = ⊥ := by
    have := hq.1
    rcases hm with rfl | hm8
    · have hdvd := card_center_dvd_six_of_alt7 hq eq
      have hpos : 0 < Nat.card (Subgroup.center ↥Ls) := Nat.card_pos
      have hle : Nat.card (Subgroup.center ↥Ls) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      rw [Nat.odd_iff] at hodd
      have h13 : Nat.card (Subgroup.center ↥Ls) = 1 ∨ Nat.card (Subgroup.center ↥Ls) = 3 := by
        interval_cases h : Nat.card (Subgroup.center ↥Ls) <;> omega
      rcases h13 with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exact absurd hB (h94 ↥V hV2 Gs Ls hLF hq h3 ⟨eq⟩ B)
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
      have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by omega : 6 ≤ m')
        (eq.toMonoidHom.comp (QuotientGroup.mk' _))
        (eq.surjective.comp (QuotientGroup.mk'_surjective _)) (ker_comp_mk'_center eq).le
        (by rw [ker_comp_mk'_center]; exact hodd)
      rw [ker_comp_mk'_center] at h1
      exact Subgroup.eq_bot_of_card_eq _ h1
  exact ⟨(QuotientGroup.quotientBot (G := ↥Ls)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hZ.symm).trans eq)⟩

theorem gf2NaturalSection_of (hX : CFSG.Open.IsKGroup ↥X)
    (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    {m : ℕ} (hm : m = 7 ∨ 8 < m)
    (he : Nonempty (↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃*
      alternatingGroup (Fin m)))
    (h85 : GF2EightFive) (h94 : GF2NoFFTripleA7) :
    NaturalSectionLSL S L m ∨
      (m = 7 ∧ (∀ s ∈ S, ∃ l ∈ L, ∀ v ∈ blockV S L, s * v * s⁻¹ = l * v * l⁻¹) ∧
        Nat.card ↥⁅blockV S L, L⁆ = 2 ^ 4) := by
  classical
  set V := blockV S L with hVdef
  set Gs := autOn (L ⊔ S) V with hGs
  set Ls := autOn L V with hLs
  have hPV : L ⊔ S ≤ Subgroup.normalizer (V : Set G) := sup_le_normalizer_blockV S L
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hPV
  have hLG : Ls ≤ Gs := InternalSec.autOn_le_autOn_of_le le_sup_left
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v =>
    Subtype.ext ((CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _).2 _ v.2)
  obtain ⟨hLF, -, -, -⟩ := ffHyp_autOn hA hL hSL hX
  obtain ⟨B, hB⟩ := exists_isFFStarOffender_of_isFFModule (isFFModule_autOn_blockV hA hL hSL)
  have hiso := nonempty_autOn_equiv_alternating hA hL hSL hm he h94
  have hm' : m = 7 ∨ 9 ≤ m := by omega
  have hmap := map_commV_autOn_blockV (S := S) (L := L) hLV
  let ρ : ↥(L ⊔ S) →* ↥Gs := (Setup.rho V (L ⊔ S) hPV).codRestrict Gs fun g =>
    (Setup.range_rho hPV).le ⟨g, rfl⟩
  have hρ : ∀ (g : ↥(L ⊔ S)) (v : ↥V), (((ρ g : MulAut ↥V) v : ↥V) : G) = g * v * (g : G)⁻¹ :=
    fun g v => Setup.rho_apply_coe hPV g v
  rcases h85 ↥V hV2 Gs Ls hLF m hm' hiso ⟨B, hB⟩ with hnat | ⟨hm7, hGL, hcard⟩
  · left
    have hnatL := isAltNaturalSection_commV_of_le hLG (by omega) hnat
    obtain ⟨θs, πs, hπs, hkers, hrange, hequiv, hinj⟩ :=
      exists_permRep_of_isAltNaturalSection hLF hLG (by omega) (by omega) hiso hnatL
    let ι : ↥(commV Ls) ≃* ↥⁅V, L⁆ :=
      ((commV Ls).equivMapOfInjective V.subtype V.subtype_injective).trans
        (MulEquiv.subgroupCongr hmap)
    have hι : ∀ u, ((ι u : ↥⁅V, L⁆) : G) = ((u : ↥V) : G) := fun _ => rfl
    have hιs : ∀ t, (((ι.symm t : ↥(commV Ls)) : ↥V) : G) = t := fun t => by
      rw [← hι, ι.apply_symm_apply]
    refine ⟨πs.comp ι.symm.toMonoidHom, θs.comp ρ, hπs.comp ι.symm.surjective, ?_, ?_, ?_, ?_⟩
    · ext t
      have key : t ∈ (πs.comp ι.symm.toMonoidHom).ker ↔
          ((ι.symm t : ↥(commV Ls)) : ↥V) ∈ fixV Ls := by
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          ← MonoidHom.mem_ker, hkers, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨fun h => h.2, fun h => ⟨(ι.symm t).2, h⟩⟩
      rw [key, mem_fixV_autOn_blockV_iff hLV, hιs, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨t.2, h⟩, fun h => h.2⟩
    · intro σ hσ
      obtain ⟨x, hx⟩ := hrange hσ
      obtain ⟨g, hgL, hgx⟩ := Setup.mem_autOn_iff.1 x.2
      refine ⟨⟨g, hgL⟩, ?_⟩
      rw [MonoidHom.comp_apply, ← hx, MonoidHom.comp_apply]
      congr 1
      apply Subtype.ext
      refine MulEquiv.ext fun v => Subtype.ext ?_
      rw [hρ, Subgroup.coe_inclusion, ← hgx, Setup.coe_conjAct_apply]
    · intro g u u' hu' x hx
      refine hequiv (ρ g) (ι.symm u) (ι.symm u') ?_ x hx
      apply Subtype.ext
      rw [hρ, hιs, hιs]
      exact hu'
    · intro g hg
      have h1 : ρ g = 1 := hinj (hg.trans (map_one θs).symm)
      exact (Setup.rho_eq_one_iff hPV g).1 (congrArg Subtype.val h1)
  · right
    refine ⟨hm7, ?_, ?_⟩
    · intro s hs
      have hsG : Setup.rho V (L ⊔ S) hPV ⟨s, Subgroup.mem_sup_right hs⟩ ∈ Ls := by
        rw [← hGL]
        exact (Setup.range_rho hPV).le ⟨_, rfl⟩
      obtain ⟨g, hgL, hg⟩ := Setup.mem_autOn_iff.1 hsG
      refine ⟨g, hgL, fun v hv => ?_⟩
      have h1 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hg
      simp only [Setup.coe_conjAct_apply, Setup.rho_apply_coe] at h1
      exact h1.symm
    · have hc : Nat.card ↥(commV Ls) = 2 ^ 4 := by rw [← hGL]; exact hcard
      rw [← hmap, Subgroup.card_map_of_injective V.subtype_injective]
      exact hc

theorem gf2NaturalLSL_of (h85 : GF2EightFive)
    (h94 : GF2NoFFTripleA7) : GF2NaturalLSL := by
  intro G _ _ X S L hX hA hL hSL m hm he
  rcases gf2NaturalSection_of hX hA hL hSL hm he h85 h94 with h | ⟨h7, -, hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨h7, hc⟩

end LS

end CFSG.HardMathSupport.Cooperstein.Coordinator
