module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapInvLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamANorm
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2RowField

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open Matrix
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL descendAut)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)
open CFSG.LieType.Steinberg.TwistedE6 (sigma)
open CFSG.LieType.Ree (ReeTag)


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_twoNeighbourData {t : G} (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) {κ : Sp6Kind} (hκ : κ.IsGraphKind) (hk : TwoKindAt e t X₀ κ) :
    ∃ (Kb : Type) (_ : Group Kb) (τ : MulAut Kb)
      (qh : centralizerPerfectCore (subgroupToG e X₀) →* Kb),
      Function.Surjective qh ∧ qh.ker ≤ center (centralizerPerfectCore (subgroupToG e X₀)) ∧
      τ ∉ (MulAut.conj : Kb →* MulAut Kb).range ∧
      LieModel (fixedSubgroup (centerQuotientAut τ)) .PSp 3 2 1 ∧
      Sp6KindType (Kb ⧸ center Kb) 1 κ ∧
      ∀ (y : centralizerPerfectCore (subgroupToG e X₀))
        (hy : t * (y : G) * t⁻¹ ∈ centralizerPerfectCore (subgroupToG e X₀)),
        qh ⟨t * y * t⁻¹, hy⟩ = τ (qh y) := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have := charP_two_of_natCard_eq_two_pow hw.card_eq
  have htC := hw.mem_centralizer
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hKt := hw.inf_eq
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK2]
  obtain ⟨htX, hk⟩ := hk
  set X : Subgroup G := subgroupToG e X₀ with hXdef
  set D : Subgroup G := subgroupToG e (C3Levi K) with hDdef
  have hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype := rfl
  have hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype := rfl
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  obtain ⟨Kb, hKb, -, hcase⟩ := hk
  obtain ⟨-, -, hlt, hsK, hsN, hov, hty⟩ := hcase.resolve_right fun h => hκ.2 h.1
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Db : Subgroup (H ⧸ oddCore H) := (D.subgroupOf H).map π with hDbdef
  set t' : H := ⟨t, htX⟩ with ht'def
  set s : H ⧸ oddCore H := π t' with hsdef
  have ht't' : t' * t' = 1 := Subtype.ext htt
  have hss : s * s = 1 := by rw [hsdef, ← map_mul, ht't', map_one]
  have hsC : s ∉ centralizer (Kb : Set (H ⧸ oddCore H)) := by
    intro hc
    refine hov.1 ⟨1, MulEquiv.ext fun k => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, coe_normalizerMonoidHom_mk_apply Kb hsN,
      ← mem_centralizer_iff.1 hc k k.2, mul_inv_cancel_right]
  have hs1 : s ≠ 1 := fun h => hsK (h ▸ one_mem Kb)
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hss) hs1
  have hDL : D ≤ L := map_subtype_le _
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDL hd))
  have hsD : s ∈ centralizer (Db : Set (H ⧸ oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [hsdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_nonsplit hw.standard.standard htC hw.orderOf_eq hKt
    hw.card_eq e hXJ hcyc hX₀' hX htX hDe
  have hKbP : Group.IsPerfect Kb := hKb.1.1
  have hOut : Group.IsSolvable (Outer Kb) :=
    isSolvable_outer_of_sp6KindType_graph hKbP hκ.1 hκ.2 hty
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (pPrimeCore_two_quotient_oddCore_eq_bot H) hKb hlt.le hs2 hsD hsN hsC hsyl hOut
  have hlayer : D = inSubgroup layer (L ⊓ centralizer (X : Set G)) :=
    (inSubgroup_layer_inf_centralizer_nonsplit e hXJ hcyc hX₀').symm
  obtain ⟨hcen, -, hX₀D⟩ := centralizer_nonsplit hXJ hcyc hX₀'
  have hLX : L ⊓ centralizer (X : Set G) ≤ X ⊔ D := by
    rw [hX, hDe, inf_centralizer_map_symm, hcen, Subgroup.map_sup, Subgroup.map_sup]
  have hDH : D ≤ centralizer (X : Set G) := map_map_symm_le_centralizer e hX₀D
  have hDq : CFSG.IsQuasisimple D := isQuasisimple_map_C3Levi e
  let eD : C3Levi K ≃* D :=
    ((C3Levi K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((C3Levi K).map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)
  have hZD : center D = ⊥ := center_eq_bot_congr eD center_C3Levi_eq_bot
  have hXD : L ⊓ centralizer (X : Set G) ⊓ centralizer (D : Set G) ≤ X :=
    SeitzQ2.inf_centralizer_le_of_le_sup hLX (le_centralizer_iff.1 hDH) hZD
  have hOutL : IsPGroup 2 (Outer L) := SeitzQ2.isPGroup_outer_of_mulEquiv_F4_two hK2 e
  have ht1 : t ≠ 1 := fun h => by
    have h2 := hw.orderOf_eq
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  have htL : t ∉ L := LinearPilot.not_mem_of_mem_centralizer hw.center_eq_bot htC ht1
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hw.standard.standard htC hw.orderOf_eq
  have hB : HasBLift Kb := SeitzQ2.hasBLift_of_isPGroup_outer hOutL htC hw.orderOf_eq htL hCN
    hKt htX hlayer hDq hXD (isPerfect_iff.mp hKbP) hsN
    (le_commutator_zpowers_of_isQuasisimple hKb.1 hsN hsC)
  obtain ⟨qh, hqs, hqker, hqapp⟩ :=
    LinearPilot.exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  refine ⟨Kb, inferInstance, Kb.normalizerMonoidHom ⟨s, hsN⟩, qh, hqs, hqker, hov.1, hov.2.2.2,
    hty, fun y hy => ?_⟩
  apply Subtype.ext
  rw [coe_normalizerMonoidHom_mk_apply Kb hsN]
  have h1 := hqapp ⟨t * (y : G) * t⁻¹, hy⟩
  have h2 := hqapp y
  have hyH : (y : G) ∈ H := centralizerPerfectCore_le_centralizer X y.2
  refine h1.trans ?_
  have e1 : π ⟨t * (y : G) * t⁻¹, centralizerPerfectCore_le_centralizer X hy⟩ =
      π t' * π ⟨(y : G), hyH⟩ * (π t')⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  refine e1.trans ?_
  exact congrArg (fun z => π t' * z * (π t')⁻¹) h2.symm


theorem exists_twoSl6Cover {t : G} (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hk : TwoKindAt e t X₀ .linear6) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ 1 ∧
      ∃ Φ : SpecialLinearGroup (Fin 6) F →* G,
        Φ.range = centralizerPerfectCore (subgroupToG e X₀) ∧
        Φ.ker ≤ center (SpecialLinearGroup (Fin 6) F) := by
  obtain ⟨S, _, hS, ρ, hρ, hker, -⟩ :=
    exists_surjective_centralizerPerfectCore_nonsplit_F4_two_graph hw e hXJ hcyc hX₀
      (κ := .linear6) (by decide) hk
  exact exists_sl_cover_of_surjective (m := 5)
    (isPerfect_iff.mpr (commutator_centralizerPerfectCore _)) (by norm_num) hS ρ hρ hker

theorem exists_twoGraphLift {t : G} (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) {κ : Sp6Kind} (hκ : κ.IsGraphKind) (hk : TwoKindAt e t X₀ κ)
    {m : ℕ} (hm : 4 ≤ m) {F : Type} [Field F] [Finite F]
    (Φ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hE : Φ.range = centralizerPerfectCore (subgroupToG e X₀))
    (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin (m + 1)) F)) :
    ∃ β : MulAut (SpecialLinearGroup (Fin (m + 1)) F), (∀ g, Φ (β g) = t * Φ g * t⁻¹) ∧
      β * β = 1 ∧ descendAut (m + 1) F β * descendAut (m + 1) F β = 1 ∧
      descendAut (m + 1) F β ∉
        (MulAut.conj : projectiveSL (m + 1) F →* MulAut (projectiveSL (m + 1) F)).range ∧
      LieModel (fixedSubgroup (descendAut (m + 1) F β)) .PSp 3 2 1 := by
  have hn3 : 3 ≤ m + 1 := by omega
  have : Group.IsPerfect (SpecialLinearGroup (Fin (m + 1)) F) := graphTorus_isPerfect_SL hn3
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have htX : t ∈ centralizer (subgroupToG e X₀ : Set G) := hk.1
  have htN : t ∈ normalizer (Φ.range : Set G) := by
    rw [hE]
    exact normalizer_le_normalizer_centralizerPerfectCore _ (centralizer_le_normalizer _ htX)
  obtain ⟨β, hβ⟩ := exists_mulAut_comp_eq_conj hm Φ hker htN
  have hββ := mulAut_mul_self_of_comp_eq_conj hm Φ hker htt hβ
  set E := centralizerPerfectCore (subgroupToG e X₀) with hEdef
  obtain ⟨Kb, _, τ, qh, hqs, hqker, hτo, hτfix, -, hqt⟩ :=
    exists_twoNeighbourData hw e hXJ hcyc hX₀ hκ hk
  have hmemE : ∀ g, Φ g ∈ E := fun g => hE ▸ ⟨g, rfl⟩
  set Φ' : SpecialLinearGroup (Fin (m + 1)) F →* E := Φ.codRestrict _ hmemE
  have hΦ's : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hE] at hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, rfl⟩
  have hΦ'ker : Φ'.ker ≤ center (SpecialLinearGroup (Fin (m + 1)) F) := fun g hg =>
    hker (by
      rw [MonoidHom.mem_ker] at hg ⊢
      exact congrArg Subtype.val hg)
  set χ : SpecialLinearGroup (Fin (m + 1)) F →* Kb := qh.comp Φ'
  have hχs : Function.Surjective χ := hqs.comp hΦ's
  have hχker : χ.ker ≤ center (SpecialLinearGroup (Fin (m + 1)) F) := fun g hg =>
    CFSG.ComponentClassification.OddSelector.mem_center_of_map_mem_center Φ' hΦ'ker (hqker hg)
  have hχβ : ∀ g, χ (β g) = τ (χ g) := by
    intro g
    have hy : t * ((Φ' g : E) : G) * t⁻¹ ∈ E := by
      change t * Φ g * t⁻¹ ∈ E
      rw [← hβ]
      exact hmemE _
    have e1 : Φ' (β g) = ⟨t * ((Φ' g : E) : G) * t⁻¹, hy⟩ := Subtype.ext (hβ g)
    change qh (Φ' (β g)) = τ (qh (Φ' g))
    rw [e1, hqt]
  refine ⟨β, hβ, hββ, by rw [← map_mul, hββ, map_one], fun hin => hτo ?_, ?_⟩
  · exact graphTorus_mem_range_conj_of_descendAut hn3 χ hχs hχβ hin
  · obtain ⟨ε⟩ := nonempty_fixedSubgroup_descendAut_equiv hn3 χ hχs hχker hχβ
    exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv ε.symm hτfix

theorem exists_twoGraphCover6 {t : G} (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hk : TwoKindAt e t X₀ .linear6) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ 1) (Φ : SpecialLinearGroup (Fin 6) F →* G)
    (hE : Φ.range = centralizerPerfectCore (subgroupToG e X₀))
    (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) F)) :
    ∃ Φ₁ : SpecialLinearGroup (Fin 6) F →* G,
      Φ₁.range = centralizerPerfectCore (subgroupToG e X₀) ∧
      Φ₁.ker ≤ center (SpecialLinearGroup (Fin 6) F) ∧
      ∀ g, t * Φ₁ g * t⁻¹ = Φ₁ ((slConjugation 6 F (graphGram6 F) * slGraphAut 6 F) g) := by
  obtain ⟨β, hβ, -, hα2, hαo, hfix⟩ := exists_twoGraphLift hw e hXJ hcyc hX₀ (κ := .linear6)
    (by decide) hk (m := 5) (by norm_num) Φ hE hker
  obtain ⟨H, hH⟩ := exists_eq_conj_graphGram6 le_rfl hF (descendAut 6 F β) hα2 hαo hfix
  obtain ⟨Φ₁, hr, hk', hc⟩ := exists_cover_of_descendAut_eq (by norm_num) Φ hker hβ hH
  exact ⟨Φ₁, hr.trans hE, hk', hc⟩

theorem exists_twoGraphParamA_normalized [Finite K] [CharP K 2] {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hk : TwoKindAt e t X₀ .linear6) :
    ∃ ΦA : e6ScLevi K e6A5Nodes →* G, ΦA.range = centralizerPerfectCore (subgroupToG e X₀) ∧
      ΦA.ker ≤ center (e6ScLevi K e6A5Nodes) ∧
      (∀ x y : e6ScLevi K e6A5Nodes,
        (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y) ∧
      IsLeviNormalizedA e ΦA := by
  obtain ⟨F, _, _, hF, Φ, hr, hk'⟩ := exists_twoSl6Cover hw e hXJ hcyc hX₀ hk
  obtain ⟨ε⟩ := graphTorus_nonempty_ringEquiv hF hw.card_eq
  obtain ⟨ΦK, hrK, hkK⟩ := exists_cover_transport ε Φ hk'
  obtain ⟨Φ₁, hr₁, hk₁, hc₁⟩ := exists_twoGraphCover6 hw e hXJ hcyc hX₀ hk hw.card_eq ΦK
    (hrK.trans hr) hkK
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hw.card_eq, pow_one]
  have hD : perfectCore (Φ₁.range ⊓ centralizer ({t} : Set G)) = neighbourLeviG e .X := by
    rw [hr₁, perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit_F4 hw e hXJ hcyc hX₀']
    rfl
  obtain ⟨Φ', hr', hk'', hc', hn'⟩ := exists_normalized_cover6 e Φ₁ hk₁ hc₁ hD
  refine ⟨Φ'.comp (graphParamEquiv K (RingEquiv.refl K)).symm.toMonoidHom,
    (range_comp_graphParamEquiv_symm _ Φ').trans (hr'.trans hr₁),
    ker_comp_graphParamEquiv_symm_le_center _ hk'', conj_comp_graphParamEquiv_symm _ hc',
    fun s => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, hn']

end CFSG.SeitzReduction.F4Pilot
