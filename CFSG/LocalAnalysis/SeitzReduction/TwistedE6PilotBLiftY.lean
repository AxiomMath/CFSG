module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotBLiftYBasic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR8Lift
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotXiFusion
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotTorusConj
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift oddCoreLift SwapComponentData)

section Position

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem exists_conj_eq_w1C_of_le_leviY (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hF5 : LeviAutConj (leviY σ) (shortJ k σ)) (hT : TorusConjY k σ) (κ κ' : Fin 2)
    (ι : leviY σ κ ≃* leviY σ κ') (X'' : Subgroup (graphFixedRootGroup TwistTag.E6 K σ))
    (hX'' : X'' ≤ (((shortJ k σ).subgroupOf (leviY σ κ)).map ι.toMonoidHom).map
      (leviY σ κ').subtype)
    (hcard : Nat.card X'' = Nat.card (w1C k σ)) :
    ∃ c : graphFixedRootGroup TwistTag.E6 K σ,
      X'' = (w1C k σ).map (MulAut.conj c).toMonoidHom := by
  obtain rfl := eq_of_nonempty_leviY_mulEquiv hf hk hK hσ ι
  obtain ⟨c, hc⟩ := hF5 κ ι
  rw [hc] at hX''
  set X₀ := X''.map (MulAut.conj c⁻¹).toMonoidHom with hX₀
  have hX₀J : X₀ ≤ shortJ k σ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj, hjx⟩ := hX'' hx
    rw [← hjx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have e : c⁻¹ * (c * j * c⁻¹) * c = j := by group
    rw [e]
    exact hj
  have hX₀c : Nat.card X₀ = Nat.card (w1C k σ) := by
    rw [hX₀, card_map_of_injective (MulAut.conj c⁻¹).injective, hcard]
  obtain ⟨d, hd⟩ := hT X₀ hX₀J hX₀c
  refine ⟨c * d, ?_⟩
  have h1 : X'' = X₀.map (MulAut.conj c).toMonoidHom := by
    rw [hX₀, E6Pilot.map_conj_map_conj_eq_conj_mul, mul_inv_cancel]
    ext x
    simp
  rw [h1, hd, E6Pilot.map_conj_map_conj_eq_conj_mul]

end Position

section Layer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem exists_coords_w1C_of_conj_eq_mul_repYC (hset : StandardSetting G L) [CharP K 2]
    (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {κ : Fin 2} {g : G} (hg : g⁻¹ * t * g = t * (e.symm (repYC (apply_apply_eq hK hσ) κ) : G))
    {X : Subgroup G} (hX : X = ((w1C k σ).map e.symm.toMonoidHom).map L.subtype) :
    ∃ φ'' : graphFixedRootGroup TwistTag.E6 K σ →* G, Function.Injective φ'' ∧
      φ''.range = CFSG.conjugate L g ∧ X = (w1C k σ).map φ'' := by
  have hf : 1 ≤ f := by omega
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨hOut, -⟩ := outer_solvable_and_center_eq_bot_twistedE6 hK σ e
  obtain ⟨hXc, hWodd⟩ := card_map_symm_w1C hf hk hσ e (L := L)
  have hXodd : Odd (Nat.card X) := by rw [hX, hXc]; exact hWodd
  have hXJ : X ≤ ((shortJ k σ).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    exact map_mono (map_mono (w1C_le_shortJ σ))
  have hXcard : Nat.card X = Nat.card (w1C k σ) := by rw [hX, hXc]
  have hinner := exists_inner_repYC_twistedE6 hset hf2 hk hK hσ e ht hKt hg
  have hord : orderOf (repYC (apply_apply_eq hK hσ) κ) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_repY κ
  have hne : g⁻¹ * t * g ≠ t := hg ▸ mul_ne_self_of_ne_one (coe_symm_ne_one_of_orderOf e hord)
  choose Q hQ using exists_isCoreLeviDecomp_repYC (k := k) hf hk hK hσ
  exact exists_coords_eq_map_of_inner_of_classes hset hOut e ht hKt
    (repYC (apply_apply_eq hK hσ)) (k := κ) (Or.inr hg) hne hinner Q (leviY σ)
    (fun κ => (hQ κ).1) (fun κ => (hQ κ).2.1) (fun κ => (hQ κ).2.2.1) (fun κ => (hQ κ).2.2.2.1)
    (fun κ => (hQ κ).2.2.2.2) (classPredicate_repYC hf hk hK hσ hQ κ)
    (shortJ_le_leviY hk hK hσ) hXodd hXJ
    (fun κ' ι X'' hX'' hc => exists_conj_eq_w1C_of_le_leviY hf hk hK hσ
      (leviAutConj_leviY hf hk hK hσ) (torusConjY_holds hf hk hK hσ) κ κ' ι X'' hX''
      (hc.trans hXcard))

theorem w1C_centralizer_data (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    centralizer (w1C k σ : Set (graphFixedRootGroup TwistTag.E6 K σ)) =
        (w1Complement σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ⊔
          (omegaMinusLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ∧
      (w1Complement σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
        centralizer ((omegaMinusLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) :
          Set (graphFixedRootGroup TwistTag.E6 K σ)) ∧
      (w1Complement σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
        centralizer ((w1Complement σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) :
          Set (graphFixedRootGroup TwistTag.E6 K σ)) ∧
      Odd (Nat.card ((w1Complement σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ))) ∧
      CFSG.IsQuasisimple ((omegaMinusLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have hf : 1 ≤ f := by omega
  obtain ⟨-, hYD, -, hYodd, -⟩ := centralizer_w1Torus_inf_eq hf2 hk hK hσ (k := k)
  refine ⟨centralizer_shortRootTorus_subgroupOf hf2 hk hK hσ,
    subgroupOf_le_centralizer_subgroupOf hYD,
    subgroupOf_le_centralizer_subgroupOf (w1Complement_le_centralizer_self σ), ?_,
    isQuasisimple_omegaMinusLevi_subgroupOf hf hK hσ⟩
  rw [Nat.card_congr (subgroupOfEquivOfLe (w1Complement_le_C0 σ)).toEquiv]
  exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hYodd)

theorem mem_layer_of_conj_eq_mul_repYC (hset : StandardSetting G L) [CharP K 2]
    (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (hX : X = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    ∀ (κ : Fin 2) (g : G),
      g⁻¹ * t * g = t * (e.symm (repYC (apply_apply_eq hK hσ) κ) : G) →
      (e.symm (repYC (apply_apply_eq hK hσ) κ) : G) ∈ CFSG.conjugate L g →
      (e.symm (repYC (apply_apply_eq hK hσ) κ) : G) ∈
        inSubgroup layer (CFSG.conjugate L g ⊓ centralizer (X : Set G)) := by
  intro κ g hg hzg
  have hX' : X = ((w1C k σ).map e.symm.toMonoidHom).map L.subtype := hX
  obtain ⟨φ'', hφ'', hφ''r, hXW⟩ :=
    exists_coords_w1C_of_conj_eq_mul_repYC hset hf2 hk hK hσ e ht hKt hg hX'
  obtain ⟨hW, hYD, hY, hYodd, hD⟩ := w1C_centralizer_data hf2 hk hK hσ (k := k)
  have hDW : (omegaMinusLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      centralizer (w1C k σ : Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
    rw [hW]
    exact le_sup_right
  have hzX : (e.symm (repYC (apply_apply_eq hK hσ) κ) : G) ∈ centralizer (X : Set G) := by
    rw [hX']
    exact F4Pilot.map_le_centralizer_map L.subtype
      (F4Pilot.map_le_centralizer_map e.symm.toMonoidHom hDW)
      ⟨_, ⟨_, mem_subgroupOf.2 (repY_mem_omegaMinusLevi (apply_apply_eq hK hσ) κ), rfl⟩, rfl⟩
  have hz2' : orderOf (e.symm (repYC (apply_apply_eq hK hσ) κ) : G) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact orderOf_repY κ
  have hz2 : (e.symm (repYC (apply_apply_eq hK hσ) κ) : G) ^ 2 ^ 1 = 1 := by
    rw [pow_one, ← hz2']
    exact pow_orderOf_eq_one _
  rw [hXW] at hzX ⊢
  exact mem_layer_of_coords hφ'' hφ''r hW hYD hY hYodd hD hzg hzX hz2

end Layer

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem le_centralizer_oddCore_2E6_Y_of_two_le (hset : SeitzSetting G L) [CharP K 2]
    (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    D.subgroupOf (centralizer (X : Set G)) ≤
      centralizer (oddCore (centralizer (X : Set G)) : Set (centralizer (X : Set G))) :=
  le_centralizer_oddCore_2E6_Y_of_layer hset hf2 hk hK hσ e htC ht
    (twistedFusionIn_xiAut hf2 hk hK σ hσ) hX hDe
    (mem_layer_of_conj_eq_mul_repYC hset.standardSetting hf2 hk hK hσ e ht
      (inf_centralizer_eq_zpowers_twistedE6 hset (by omega) hK hσ e htC ht) hX)

theorem exists_surjective_neighbourCore_2E6_Y_of_two_le (hset : SeitzSetting G L) [CharP K 2]
    (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hout : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hmodel : LieModel Kc .POmegaPlus 4 2 (2 * f)) :
    perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) =
        Kc ∧ HasBLift Kc ∧
      ∃ q : centralizerPerfectCore X →* Kc, Function.Surjective q ∧
        q.ker ≤ center (centralizerPerfectCore X) ∧ Odd (Nat.card q.ker) ∧
        ∀ y : centralizerPerfectCore X, (q y : centralizer (X : Set G) ⧸
          oddCore (centralizer (X : Set G))) = QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
            ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩ :=
  exists_surjective_neighbourCore_2E6_Y_of_le_centralizer hset hf2 hk hK hσ e htC ht hX htX hDe
    (le_centralizer_oddCore_2E6_Y_of_two_le hset hf2 hk hK hσ e htC ht hX hDe) hKc hDK hsN hout
    hmodel

omit
  [Finite G] in
theorem commutator_ne_bot_of_le_sup_conj {Y : Type*} [Group Y] {s : Y} (hs : s * s = 1)
    {D Kc : Subgroup Y} (hDKK : D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom)
    (hsD : s ∈ centralizer (D : Set Y)) (hDp : ⁅D, D⁆ = D) (hD : D ≠ ⊥) :
    ⁅Kc, D⁆ ≠ ⊥ ∧ ⁅Kc.map (MulAut.conj s).toMonoidHom, D⁆ ≠ ⊥ := by
  have hss : (Kc.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s).toMonoidHom = Kc := by
    rw [F4Pilot.map_conj_map_conj_eq_map_conj_mul, hs, map_one]
    ext x
    simp
  refine ⟨fun hb => hD (UnitaryPilot.eq_bot_of_le_sup_of_commutator_eq_bot hDKK hDp hb
    (UnitaryPilot.commutator_map_conj_eq_bot_of_mem_centralizer hsD hb)), fun hb => hD
    (UnitaryPilot.eq_bot_of_le_sup_of_commutator_eq_bot hDKK hDp
      (hss ▸ UnitaryPilot.commutator_map_conj_eq_bot_of_mem_centralizer hsD hb) hb)⟩

theorem hasBLift_neighbour_2E6_Y (hset : SeitzSetting G L) [CharP K 2] (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDKK : (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤
      Kc ⊔ Kc.map (MulAut.conj
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom) :
    HasBLift Kc ∧ HasBLift (Kc ⊔ Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom) := by
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_2E6_Y hset hf2 hk hK hσ e htC ht hX htX hDe
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd => by
    rw [hDe] at hd
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hss : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ *
      QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ = 1 := by
    rw [← map_mul, show (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 from
      Subtype.ext htt, map_one]
  have hτD : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      centralizer (((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) : Subgroup _) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  obtain ⟨h1, h2⟩ := commutator_ne_bot_of_le_sup_conj hss hDKK hτD
    (commutator_eq_self_of_isQuasisimple' hcomp.2.2) (ne_bot_of_isQuasisimple hcomp.2.2)
  exact LinearPilot.hasBLift_of_isComponent_of_le_centralizer
    (le_centralizer_oddCore_2E6_Y_of_two_le hset hf2 hk hK hσ e htC ht hX hDe) hKc
    (F4Pilot.isComponent_map_conj hKc _) h1 h2

end Lift

section LeafInputs

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.SeitzReduction.OmegaPilot (OmegaNotOddLieInputAt)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem exists_isComponent_2E6_Y_of_leafInputs (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : OmegaNotOddLieInputAt 4) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hset : SeitzSetting G L) [CharP K 2] (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    OmegaPilot.OmegaHR8FieldAt t 4 f .POmegaMinus X D ∧
      ∃ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Kc ∧ ⁅(D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Kc⁆ ≠ ⊥ := by
  have h := omegaHR8FieldAt_2E6_Y hGLS hXodd hMinn hMcomp hset hf2 hk hK hσ e htC ht
    (twistedFusionIn_xiAut hf2 hk hK σ hσ) (torusConjY_holds (by omega) hk hK hσ) hX hDe
  refine ⟨h, ?_⟩
  obtain ⟨htX, ⟨Kc, hKc, hDKK, -⟩, -, -⟩ := h
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_2E6_Y hset hf2 hk hK hσ e htC ht hX htX hDe
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd => by
    rw [hDe] at hd
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hss : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ *
      QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ = 1 := by
    rw [← map_mul, show (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 from
      Subtype.ext htt, map_one]
  have hτD : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      centralizer (((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) : Subgroup _) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  obtain ⟨h1, -⟩ := commutator_ne_bot_of_le_sup_conj hss hDKK hτD
    (commutator_eq_self_of_isQuasisimple' hcomp.2.2) (ne_bot_of_isQuasisimple hcomp.2.2)
  exact ⟨Kc, hKc, by rw [commutator_comm]; exact h1⟩

theorem neighbourCore_field_2E6_Y_of_leafInputs (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : OmegaNotOddLieInputAt 4) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hset : SeitzSetting G L) [CharP K 2] (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDK : ⁅(D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Kc⁆ ≠ ⊥)
    (hKt : Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom = Kc) :
    center Kc = ⊥ ∧ LieModel Kc .POmegaPlus 4 2 (2 * f) ∧
      perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) =
        Kc ∧ HasBLift Kc ∧
      ∃ q : centralizerPerfectCore X →* Kc, Function.Surjective q ∧
        q.ker ≤ center (centralizerPerfectCore X) ∧ Odd (Nat.card q.ker) ∧
        ∀ y : centralizerPerfectCore X, (q y : centralizer (X : Set G) ⧸
          oddCore (centralizer (X : Set G))) = QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
            ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩ := by
  obtain ⟨⟨_, -, hall, -⟩, -⟩ := exists_isComponent_2E6_Y_of_leafInputs hGLS hXodd hMinn hMcomp
    hset hf2 hk hK hσ e htC ht hX hDe
  obtain ⟨-, ⟨-, hDK', -, hsN, hout, hZ, hmodel, -⟩ | ⟨hne, -⟩⟩ := hall Kc hKc hDK
  · exact ⟨hZ, hmodel, exists_surjective_neighbourCore_2E6_Y_of_two_le hset hf2 hk hK hσ e htC ht
      hX htX hDe hKc hDK'.le hsN hout hmodel⟩
  · exact absurd hKt hne

end LeafInputs

end CFSG.SeitzReduction.TwistedE6Pilot
