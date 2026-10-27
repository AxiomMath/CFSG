module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOrigActor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOrigRank

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Offender
open scoped Multiplicative MatrixGroups LinearAlgebra.Projectivization

section Defs

variable {G : Type} [Group G]

structure EvenSL2BridgeOutput (X R M V : Subgroup G) (n : ℕ) (F : Type) [Field F] (r : ℕ)
    (Lc : Fin r → Subgroup (MulAut V)) : Prop where
  C0_le_M : X ⊓ Subgroup.centralizer (V : Set G) ≤ M
  R_inf_C0 : R ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 X
  X_eq : X = oddOrderSubgroup X ⊔ R
  o2_trivial : pCoreOf 2 (autOn X V) = ⊥
  sylow : IsSylowTwoOf (autOn R V) (autOn X V)
  not_normal : ¬ ((autOn R V).subgroupOf (autOn X V)).Normal
  max : autOn R V ≤ autOn M V ∧ autOn M V < autOn X V ∧
    ∀ Y : Subgroup (MulAut V), autOn R V ≤ Y → Y < autOn X V → Y ≤ autOn M V
  offender : ∃ A : Subgroup G, IsReducedOffender R V A
  K_eq : autOn (oddOrderSubgroup X) V = oddOrderSubgroup (autOn X V)
  r_pos : 1 ≤ r
  r_pow : ∃ k : ℕ, r = 2 ^ k
  iso : ∀ i, Nonempty (↥(Lc i) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
  center_trivial : ∀ i, Subgroup.center ↥(Lc i) = ⊥
  transitive : ∀ i j, ∃ t ∈ autOn R V, (Lc i).map (MulAut.conj t).toMonoidHom = Lc j
  K_prod : oddOrderSubgroup (autOn X V) = ⨆ i, Lc i
  commute : ∀ i j, i ≠ j → ⁅Lc i, Lc j⁆ = ⊥
  direct : ∀ i, Lc i ⊓ (⨆ j, ⨆ (_ : j ≠ i), Lc j) = ⊥
  rank : r ≤ CFSG.pRank 3 X
  rank_le_two : CFSG.pRank 3 X ≤ 2 → r = 1 ∨ r = 2
  weight : ∀ A : Subgroup G, IsMaxElemAbelian R A →
    Nat.card V = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))

end Defs

section Fields

variable {V : Type} [CommGroup V] [Finite V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W] (θ : V ≃* Multiplicative W) {H T M : Subgroup (MulAut V)} {n : ℕ} {F : Type}
  [Field F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] {r : ℕ}
  {Lc : Fin r → Subgroup (MulAut V)}

omit [Finite V] [Finite W] in
theorem family_fields_of_gl_output
    (out : EvenSL2MaxOutput (H.map (binPsi θ).toMonoidHom) (T.map (binPsi θ).toMonoidHom)
      (M.map (binPsi θ).toMonoidHom) n F r (fun i => (Lc i).map (binPsi θ).toMonoidHom)) :
    1 ≤ r ∧ (∃ k : ℕ, r = 2 ^ k) ∧
      (∀ i, Nonempty (↥(Lc i) ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
      (∀ i, Subgroup.center ↥(Lc i) = ⊥) ∧
      (∀ i j, ∃ t ∈ T, (Lc i).map (MulAut.conj t).toMonoidHom = Lc j) ∧
      oddOrderSubgroup H = ⨆ i, Lc i ∧
      (∀ i j, i ≠ j → ⁅Lc i, Lc j⁆ = ⊥) ∧
      (∀ i, Lc i ⊓ (⨆ j, ⨆ (_ : j ≠ i), Lc j) = ⊥) := by
  have layer := out.offenders.family.layer
  have hinj : Function.Injective (binPsi θ).toMonoidHom := (binPsi θ).injective
  refine ⟨layer.r_pos, layer.r_pow, fun i => ⟨(mapEquiv (binPsi θ) (Lc i)).trans (layer.iso i).some⟩,
    fun i => ?_, fun i j => ?_, ?_, fun i j hij => ?_, fun i => ?_⟩
  · have h1 := layer.center_trivial i
    rw [← Subgroup.map_center_eq (mapEquiv (binPsi θ) (Lc i))] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (mapEquiv (binPsi θ) (Lc i)).injective).1 h1
  · obtain ⟨t, ht, hconj⟩ := layer.transitive i j
    obtain ⟨t', ht', rfl⟩ := ht
    refine ⟨t', ht', Subgroup.map_injective hinj ?_⟩
    rw [map_map_conj (binPsi θ) (Lc i) t']
    exact hconj
  · apply Subgroup.map_injective hinj
    have h1 : (oddOrderSubgroup H).map (binPsi θ).toMonoidHom =
        oddGen (H.map (binPsi θ).toMonoidHom) := map_closure_odd (binPsi θ) H
    rw [h1, Subgroup.map_iSup]
    exact layer.K_eq
  · have h1 := layer.commute i j hij
    rw [← map_commutator_mulEquiv (binPsi θ) (Lc i) (Lc j)] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h1
  · apply Subgroup.map_injective hinj
    have h1 := layer.direct i
    rw [Subgroup.map_inf _ _ _ hinj, Subgroup.map_bot]
    have h2 : (⨆ j, ⨆ (_ : j ≠ i), Lc j).map (binPsi θ).toMonoidHom =
        ⨆ j, ⨆ (_ : j ≠ i), (Lc j).map (binPsi θ).toMonoidHom := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun j => Subgroup.map_iSup _ _
    rw [h2]
    exact h1

end Fields

section Main

variable {G : Type} [Group G] [Finite G]

theorem even_SL2_setting_basic {X R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (hS : EvenSL2Setting X R M V n F) :
    X ⊓ Subgroup.centralizer (V : Set G) ≤ M ∧ R ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 X ∧
      X = oddOrderSubgroup X ⊔ R ∧ pCoreOf 2 (autOn X V) = ⊥ ∧ V ≤ R := by
  have hred := hS.reduced
  have hVe : IsElemAbelian 2 V := hred.2.2.1
  have hX : X ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hRX : R ≤ X := hS.sylow.1
  have hnn : ¬ X ≤ Subgroup.normalizer (R : Set G) := fun h =>
    hS.not_normal ((Subgroup.normal_subgroupOf_iff_le_normalizer hRX).mpr h)
  have hVX : ¬ X ≤ Subgroup.centralizer (V : Set G) := fun hc =>
    hS.thompson_ne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      ((B6.thompsonJ_le R).trans (hRX.trans hc)))
  obtain ⟨hXLR, -, hCM, hCR, -⟩ := reduced_detects_commutator hS.sylow hnn hS.max.1 hS.max.2.1
    hS.max.2.2 hred hVX
  have hV2 : IsPGroup 2 ↥V := fun v => ⟨1, Subtype.ext (by simpa using hVe.2 (v : G) v.2)⟩
  have hVn : (V.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hred.1).mpr hX
  exact ⟨hCM, hCR, hXLR, pCoreOf_autOn_eq_bot hred,
    (CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 V X hred.1 hVn hV2).trans
      hS.sylow.pCoreOf_le⟩

theorem even_SL2_setting_ffcore {X R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (hS : EvenSL2Setting X R M V n F) :
    ∃ A : Subgroup G, IsReducedOffender R V A ∧
      @FFCore V (commGroupOfElemAbelian hS.reduced.2.2.1) (autOn X V) (autOn R V) (autOn M V)
        (autOn A V) := by
  classical
  have hred := hS.reduced
  have hVe : IsElemAbelian 2 V := hred.2.2.1
  have hX : X ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hRX : R ≤ X := hS.sylow.1
  have hnn : ¬ X ≤ Subgroup.normalizer (R : Set G) := fun h =>
    hS.not_normal ((Subgroup.normal_subgroupOf_iff_le_normalizer hRX).mpr h)
  obtain ⟨hCM, hCR, -, hΛ, hVR⟩ := even_SL2_setting_basic hS
  obtain ⟨A, hAS, hAc⟩ : ∃ A, IsMaxElemAbelian R A ∧ ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hno
    push Not at hno
    exact hS.thompson_ne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (iSup₂_le fun A hA => hno A hA))
  have hAn : A ≤ Subgroup.normalizer (V : Set G) := hAS.1.trans (hRX.trans hX)
  have hoff : IsReducedOffender R V A :=
    ⟨hAS, hAc, inf_centralizer_eq_of_isMaxElemAbelian hVe hVR hAS,
      card_le_relIndex_mul_card hVe hVR hAS⟩
  have hAe := isElemAbelian2_autOn hVe hAS.2.1 hAn
  let _ : CommGroup V := commGroupOfElemAbelian hVe
  refine ⟨A, hoff, ⟨fun N hNH hNn hN2 => ?_, isSylowTwoOf_autOn hS.sylow hX,
    not_normal_autOn hS.sylow hX hΛ hCR hnn,
    autOn_max hX hS.max.1 hS.max.2.1 hS.max.2.2 hCM hRX,
    autOn_le_autOn V (hAS.1.trans hRX), autOn_ne_bot_of_not_le_centralizer hAn hAc, hAe.1, hAe.2,
    ?_⟩⟩
  · exact le_bot_iff.mp (hΛ ▸
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 N _ hNH hNn hN2)
  · rw [card_autOn_eq_relIndex hAn, card_fixV_autOn_eq hVe hAn]
    exact hoff.2.2.2

theorem even_SL2_original_bridge
    {X R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (hS : EvenSL2Setting X R M V n F) {r : ℕ} {Lc : Fin r → Subgroup (MulAut V)}
    (hLc : IsCompList (autOn X V) r Lc) : EvenSL2BridgeOutput X R M V n F r Lc := by
  classical
  have hred := hS.reduced
  have hVe : IsElemAbelian 2 V := hred.2.2.1
  have hX : X ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hRX : R ≤ X := hS.sylow.1
  obtain ⟨hCM, hCR, hXLR, hΛ, hVR⟩ := even_SL2_setting_basic hS
  obtain ⟨A₀, hoff, hFF⟩ := even_SL2_setting_ffcore hS
  obtain ⟨D, hD, ⟨α⟩⟩ := hS.component
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hS.card_eq]; positivity)
  let _ : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hS.card_eq
  have hchar : CharP F 2 := charP_two_of_card_pow hF
  let _ : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  let _ : DecidableEq (ℙ F (Fin 2 → F)) := Classical.decEq _
  let _ : CommGroup V := commGroupOfElemAbelian hVe
  have hV2 : ∀ v : V, v * v = 1 := fun v => Subtype.ext (by simpa [sq] using hVe.2 v v.2)
  obtain ⟨⟨W, hW1, hW2, hW3, θ, hout⟩, hwle⟩ := even_SL2_actor_max_output hV2 hFF
    hS.nonsolvable hS.two_le hF hD α hLc
  obtain ⟨hr1, hrpow, hiso, hctr, htrans, hKprod, hcomm, hdirect⟩ :=
    family_fields_of_gl_output θ hout
  have hle : ∀ i, Lc i ≤ autOn X V := fun i => (hLc.isComp i).1
  have hcomm' : ∀ i j, i ≠ j → ∀ x ∈ Lc i, ∀ y ∈ Lc j, x * y = y * x := fun i j hij x hx y hy =>
    (Subgroup.mem_centralizer_iff.1
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm i j hij)) hx) y hy).symm
  have hrank : r ≤ CFSG.pRank 3 X := rank_le_of_sl2_family hX hle hiso hcomm' hdirect
  have hweight : ∀ A : Subgroup G, IsMaxElemAbelian R A →
      Nat.card V = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
    intro A hA
    have hAn : A ≤ Subgroup.normalizer (V : Set G) := hA.1.trans (hRX.trans hX)
    have hlow := card_le_relIndex_mul_card hVe hVR hA
    by_cases hAc : A ≤ Subgroup.centralizer (V : Set G)
    · have h1 : A ⊓ Subgroup.centralizer (V : Set G) = A := inf_eq_left.2 hAc
      have h2 : V ⊓ Subgroup.centralizer (A : Set G) = V :=
        inf_eq_left.2 fun v hv => Subgroup.mem_centralizer_iff.2 fun a ha =>
          (Subgroup.mem_centralizer_iff.1 (hAc ha) v hv).symm
      rw [h1, h2, Subgroup.relIndex_self, one_mul]
    · have hup := hwle (autOn A V) (autOn_le_autOn V (hA.1.trans hRX))
        (autOn_ne_bot_of_not_le_centralizer hAn hAc) (isElemAbelian2_autOn hVe hA.2.1 hAn)
      rw [card_autOn_eq_relIndex hAn, card_fixV_autOn_eq hVe hAn] at hup
      exact le_antisymm hlow hup
  refine ⟨hCM, hCR, hXLR, hΛ, hFF.sylow, hFF.not_normal, hFF.max, ⟨A₀, hoff⟩,
    autOn_oddOrderSubgroup hX, hr1, hrpow, hiso, hctr, htrans, hKprod, hcomm, hdirect, hrank,
    fun h2 => ?_, hweight⟩
  obtain ⟨k, hk⟩ := hrpow
  have hr2 : r ≤ 2 := hrank.trans h2
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · left
      simpa using hk
    · right
      simpa using hk
  · exfalso
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    rw [hk] at hr2
    exact absurd (h4.trans hr2) (by norm_num)

end Main

end CFSG.QuasithinUnique.Setup.Lift
