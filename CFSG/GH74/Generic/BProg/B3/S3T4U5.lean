module

public import CFSG.GH74.Generic.BProg.B3.S3T4Leaf
public import CFSG.GH74.Generic.BProg.B3.S3T4U5A

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBUnitaryB
open CFSG.ComponentClassification.OddClassSelector
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

namespace S3T4

theorem commutator_mul_central_left {G : Type*} [Group G] {a b z : G} (hz : z ∈ center G) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h1 := mem_center_iff.mp hz b
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [← h1]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutator_mul_central_right {G : Type*} [Group G] {a b z : G} (hz : z ∈ center G) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h1 := mem_center_iff.mp hz a⁻¹
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [← h1]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem eq_commutator_comap_of_map {S : Type*} [Group S] {Z : Subgroup S} [Z.Normal]
    (hZ : Z ≤ center S) {X : Subgroup (S ⧸ Z)} {Y : Subgroup S} (hYp : ⁅Y, Y⁆ = Y)
    (hYX : Y.map (QuotientGroup.mk' Z) = X) :
    Y = ⁅X.comap (QuotientGroup.mk' Z), X.comap (QuotientGroup.mk' Z)⁆ := by
  have hle : Y ≤ X.comap (QuotientGroup.mk' Z) := by
    rw [← hYX]
    exact Subgroup.le_comap_map _ _
  refine le_antisymm ?_ ?_
  · rw [← hYp]
    exact Subgroup.commutator_mono hle hle
  · rw [Subgroup.commutator_le]
    have hlift : ∀ a ∈ X.comap (QuotientGroup.mk' Z), ∃ y ∈ Y, ∃ z ∈ Z, a = y * z := by
      intro a ha
      have ha' : QuotientGroup.mk' Z a ∈ Y.map (QuotientGroup.mk' Z) := by rw [hYX]; exact ha
      obtain ⟨y, hy, hya⟩ := ha'
      refine ⟨y, hy, y⁻¹ * a, ?_, by group⟩
      exact (QuotientGroup.eq (s := Z)).1 hya
    intro a ha b hb
    obtain ⟨y, hy, z, hz, rfl⟩ := hlift a ha
    obtain ⟨y', hy', z', hz', rfl⟩ := hlift b hb
    rw [commutator_mul_central_left (hZ hz), commutator_mul_central_right (hZ hz')]
    rw [← hYp]
    exact Subgroup.commutator_mem_commutator hy hy'

noncomputable abbrev hypι {p f : ℕ} {K : Type} [Field K] (hud : UnitaryFieldData p f K)
    (r ε : ℕ) : hypPSU hud r ε →* sesqProjUnitary hud (hypForm hud r ε) :=
  (projSpecial hud (hypForm hud r ε)).subtype.comp (hypModelEquiv hud).toMonoidHom

theorem hypι_injective {p f : ℕ} {K : Type} [Field K] (hud : UnitaryFieldData p f K)
    (r ε : ℕ) : Function.Injective (hypι hud r ε) :=
  Subtype.val_injective.comp (hypModelEquiv hud).injective

theorem exists_summand_of_inner_u {p f : ℕ} {K : Type} [Field K] (hud : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) {r : ℕ} (hr : 1 ≤ r) {X : Subgroup (hypPSU hud r 1)} {y : hypPSU hud r 1}
    (hy : orderOf y = 2) (hX : CFSG.Assembly.IsComponentOf X (fixedSubgroup (MulAut.conj y))) :
    ∃ (T : sesqUnitaryGroup (hypForm hud r 1)) (l : K),
      QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r 1)) T = hypι hud r 1 y ∧ l ≠ 0 ∧
      unitaryOp T * unitaryOp T = (l ^ 2) • 1 ∧ hud.norm l = 1 ∧
      2 ≤ finrank K (eigenPlus l (unitaryOp T)) ∧
      ((⁅(X.map (hypι hud r 1)).comap
            (QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r 1))),
          (X.map (hypι hud r 1)).comap
            (QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r 1)))⁆ :
          Subgroup (sesqUnitaryGroup (hypForm hud r 1))) : Set (sesqUnitaryGroup _)) =
        summandUnitarySet (hypForm hud r 1) (eigenPlus l (unitaryOp T))
          (eigenMinus l (unitaryOp T)) := by
  classical
  have : Fact p.Prime := ⟨hud.prime⟩
  have := hud.finite
  have hdim : finrank K (HypIndex r 1 → K) = 2 * r + 1 := UnitaryHigher.finrank_hypIndex_fun
  set ι := hypι hud r 1 with hιdef
  have hι : Function.Injective ι := hypι_injective hud r 1
  set Z := sesqNormOneScalars hud (hypForm hud r 1) with hZdef
  have hmap : (fixedSubgroup (MulAut.conj y)).map ι = projSpecial hud (hypForm hud r 1) ⊓
      fixedSubgroup (MulAut.conj (ι y)) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(hypModelEquiv hud x).2, ?_⟩
      change MulAut.conj (ι y) (ι x) = ι x
      have hx' : MulAut.conj y x = x := hx
      rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, ← MulAut.conj_apply, hx']
    · rintro ⟨hzN, hzψ⟩
      obtain ⟨x, hx⟩ := (hypModelEquiv hud).surjective ⟨z, hzN⟩
      have hxz : ι x = z := congrArg Subtype.val hx
      refine ⟨x, ?_, hxz⟩
      change MulAut.conj y x = x
      apply hι
      have hz' : MulAut.conj (ι y) z = z := hzψ
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hxz, ← MulAut.conj_apply, hz']
  have h1 := CFSG.ComponentClassification.SymmetricLocal.isComponentOf_map_of_injective ι hι hX
  rw [hmap] at h1
  have hX₂ : CFSG.Assembly.IsComponentOf (X.map ι) (fixedSubgroup (MulAut.conj (ι y))) := by
    refine isComponentOf_of_normal_le h1 inf_le_right ?_
    constructor
    intro m hm g
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    exact ⟨(projSpecial_normal hud (hypForm hud r 1)).conj_mem _ hm.1
      (g : sesqProjUnitary hud _), Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hm.2)
        (Subgroup.inv_mem _ g.2)⟩
  obtain ⟨T, hT⟩ := QuotientGroup.mk'_surjective Z (ι y)
  have hZc := sesqNormOneScalars_le_center hud (hypForm hud r 1)
  have hφZ := map_conj_eq_of_le_center hZc T
  rw [← hT, ← onQuotient_conj T hφZ] at hX₂
  have hTo : orderOf (QuotientGroup.mk T : sesqProjUnitary hud (hypForm hud r 1)) = 2 := by
    change orderOf (QuotientGroup.mk' Z T) = 2
    rw [hT, orderOf_injective ι hι, hy]
  have hTT : T * T ∈ center (sesqUnitaryGroup (hypForm hud r 1)) := by
    apply hZc
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two, ← hTo, pow_orderOf_eq_one]
  have hφφ : ∀ g, MulAut.conj T (MulAut.conj T g) = g := by
    intro g
    rw [MulAut.conj_apply, MulAut.conj_apply]
    have h2 := mem_center_iff.mp hTT g
    calc T * (T * g * T⁻¹) * T⁻¹ = (T * T) * g * (T * T)⁻¹ := by group
      _ = g := by rw [← h2, mul_inv_cancel_right]
  obtain ⟨Y, hY, ⟨σY, hσYs, -, hσYv⟩, -⟩ := central_lift _ hZc _ hφZ hφφ hX₂
  rw [fixedSubgroup_conj] at hY
  have hYX : Y.map (QuotientGroup.mk' Z) = X.map ι := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [← hσYv ⟨g, hg⟩]
      exact (σY ⟨g, hg⟩).2
    · intro hz
      obtain ⟨g, hg⟩ := hσYs ⟨z, hz⟩
      refine ⟨g, g.2, ?_⟩
      rw [← hσYv g, hg]
  have hYp : ⁅Y, Y⁆ = Y := OddProjectivePair.commutator_eq_self_of_isQuasisimple hY.2.2
  have hYeq := eq_commutator_comap_of_map hZc hYp hYX
  obtain ⟨l, hl0, hAA, hN, hP, hM, -, -, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure hud hp2 (by rw [hdim]; omega)
      (hypForm_isSymm hud) (hypForm_separatingLeft hud) hTo
  have hN1 : hud.norm l = 1 := by
    rcases hN with hN | hN
    · exact hN
    · obtain ⟨-, -, -, hdim2, -⟩ := hpaired hN
      rw [hdim] at hdim2
      omega
  have hY₁ : CFSG.IsComponent (Y.subgroupOf (centralizer {T})) :=
    (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  obtain ⟨A, W, hAW, hm2, hset, -⟩ := exists_summand_of_isComponent hp2 (hypForm_isSymm hud)
    (hypForm_separatingLeft hud) hl0 hAA hN1 hP hM hY₁
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hY.1, hYeq] at hset
  rcases hAW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨T, l, hT, hl0, hAA, hN1, hm2, hset⟩
  · refine ⟨T, -l, hT, neg_ne_zero.mpr hl0, by rw [neg_sq]; exact hAA,
      by rw [norm_neg']; exact hN1, ?_, ?_⟩
    · rw [eigenPlus_neg]
      exact hm2
    · rw [eigenPlus_neg, eigenMinus_neg]
      exact hset

theorem false_of_inner_pair_uni {N : Type} [Group N] [Finite N] {H L : Subgroup N} [H.Normal]
    {v w : N} (hsv : B2.ShapeInCent H v L) (hsw : B2.ShapeInCent H w L)
    (hsvw : B2.ShapeInCent H (v * w) L) (hv : v ∈ H) (hw : w ∈ H) {p f : ℕ} {K : Type}
    [Field K] (hud : UnitaryFieldData p f K) (hp2 : p ≠ 2) {r : ℕ} (hr : 1 ≤ r)
    (θ : ↥H ≃* hypPSU hud r 1) : False := by
  classical
  have hZ : center (hypPSU hud r 1) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have h1 : ((θ.symm z : ↥H) : N) = 1 := hsv.faithful _ fun k hk => by
      have h2 := mem_center_iff.mp hz (θ ⟨k, hk⟩)
      have h3 := congrArg (fun x => ((θ.symm x : ↥H) : N)) h2
      simpa only [map_mul, MulEquiv.symm_apply_apply, Subgroup.coe_mul] using h3.symm
    have h4 : θ.symm z = 1 := Subtype.ext h1
    simpa using congrArg θ h4
  have hcj := conj_injective hZ
  set X := (L.map (B2.PuL4GraphLin.rhoOf θ)).comap
    (MulAut.conj : hypPSU hud r 1 →* MulAut (hypPSU hud r 1)) with hXdef
  have hcomp : ∀ t : N, B2.ShapeInCent H t L → ∀ ht : t ∈ H,
      CFSG.Assembly.IsComponentOf X (fixedSubgroup (MulAut.conj (θ ⟨t, ht⟩))) := by
    intro t hs ht
    have h1 := B2.PuL4GraphLin.isComponentOf_map_rho hs θ
    have h2 : B2.PuL4GraphLin.rhoOf θ t = MulAut.conj (θ ⟨t, ht⟩) :=
      B2.PuL4GraphLin.rhoOf_mem θ ⟨t, ht⟩
    rw [h2] at h1
    exact (isComponentOf_comap_conj hcj h1).1
  have hord : ∀ t : N, B2.ShapeInCent H t L → ∀ ht : t ∈ H, orderOf (θ ⟨t, ht⟩) = 2 := by
    intro t hs ht
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hs.inv
  obtain ⟨Tv, lv, hTv, hlv0, hAAv, hNv, hmv, hsetv⟩ :=
    exists_summand_of_inner_u hud hp2 hr (hord v hsv hv) (hcomp v hsv hv)
  obtain ⟨Tw, lw, hTw, hlw0, hAAw, hNw, hmw, hsetw⟩ :=
    exists_summand_of_inner_u hud hp2 hr (hord w hsw hw) (hcomp w hsw hw)
  have hTT := mul_eq_smul_of_summand_eq hp2 (hypForm_isSymm hud) (hypForm_separatingLeft hud)
    hlv0 hlw0 hAAv hAAw hNv hNw hmv hmw (hsetv.symm.trans hsetw)
  have hZmem : Tv * Tw ∈ sesqNormOneScalars hud (hypForm hud r 1) :=
    ⟨lv * lw, by rw [norm_mul_eq', hNv, hNw, one_mul], hTT⟩
  have h1 : hypι hud r 1 (θ ⟨v, hv⟩ * θ ⟨w, hw⟩) = 1 := by
    rw [map_mul, ← hTv, ← hTw, ← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hZmem
  have h2 : θ ⟨v, hv⟩ * θ ⟨w, hw⟩ = 1 :=
    hypι_injective hud r 1 (h1.trans (map_one _).symm)
  have h3 : (⟨v, hv⟩ : ↥H) * ⟨w, hw⟩ = 1 := θ.injective (by rw [map_mul, h2, map_one])
  have h4 : v * w = 1 := congrArg Subtype.val h3
  have h5 := hsvw.inv
  rw [h4, orderOf_one] at h5
  omega

end S3T4

open S3T4 in
theorem innerPairU5_proved : InnerPairU5 := by
  intro N _ _ H L v w p f hp hp2 hf hM hsv hsw hsvw hv hw
  have hnorm : H.Normal := hsv.normal
  obtain ⟨⟨-, -, -⟩, F, _, _, hF, ⟨e₀⟩⟩ := B2.T4.T4OutCore.stated_PSU hM
  have hud : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := (unitary_hyperbolic_model_transport hud (r := 2) (ε := 1) (by norm_num)
    le_rfl).1
  let θ : ↥H ≃* hypPSU hud 2 1 := (e₀.trans (unitaryPSUEquiv hud (by norm_num)).symm).trans
    (hypProjTransport hud (R := R) hR).symm
  exact false_of_inner_pair_uni hsv hsw hsvw hv hw hud hp2 (by norm_num) θ

section CertifiedLeaf


theorem leaf514S3_proved : Leaf514S3 :=
  leaf514S3_of innerPairU5_proved

end CertifiedLeaf

end CFSG.GH74.Generic.BProg.B3
