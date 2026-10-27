module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf18CrossModel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Y
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf13Z
public import CFSG.ClassicalInvolution.Q3.TL4AECoverF

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

namespace TwinThin

namespace Cross

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {m : ℕ}

@[expose] def InducedBy (I : AEIdent P m) (u : G) (w : Wr m) : Prop :=
  ∀ x y : ↥(pSpan P), (y : G) = u * x * u⁻¹ → I.φ y = mkQ m w * I.φ x * (mkQ m w)⁻¹

theorem exists_induced (hm : 5 ≤ m) (hAut : TwinThinPf8.AEAut m) (I : AEIdent P m) {u : G}
    (hu : u ∈ Subgroup.normalizer (pSpan P : Set G)) (hP : ∀ L ∈ P, conjSub u L ∈ P) :
    ∃ w : Wr m, InducedBy I u w := by
  have hZ : Subgroup.center ↥I.φ.range = ⊥ := center_eq_bot_of_eq I.range_eq (center_Hn hm)
  have hk' : ∀ x : ↥(pSpan P), x ∈ I.φ.ker → TwinThinPf.conjOn _ u hu x ∈ I.φ.ker :=
    fun x hx => TwinThinPf.ker_invariant I.φ hu I.ker_le hZ hx
  let σ := TwinThinPf.induced I.φ hu hk'
  have hperm : TwinThinPf8.PermMembers I.φ.range σ := by
    intro β hβ c
    obtain ⟨M, hM, hMlab⟩ := I.label_surj β hβ c
    obtain ⟨β', hβ', c', hlab'⟩ := I.label _ (hP M hM)
    refine ⟨β', hβ', c', fun x hx => ?_⟩
    have hx' : (x : AEQ m) ∈ (M.subgroupOf _).map I.φ := by rw [hMlab]; exact hx
    obtain ⟨l, hl, hlx⟩ := I.exists_of_mem_map hM hx'
    have hxe : x = I.φ.rangeRestrict ⟨l, le_pSpan hM hl⟩ := Subtype.ext hlx.symm
    rw [hxe, TwinThinPf.induced_apply, ← hlab']
    exact ⟨TwinThinPf.conjOn _ u hu ⟨l, le_pSpan hM hl⟩,
      Subgroup.mem_subgroupOf.mpr (by rw [TwinThinPf.conjOn_apply]; exact conj_mem_conjSub hl), rfl⟩
  have hsurj : Function.Surjective σ := by
    intro r
    obtain ⟨x, rfl⟩ := I.φ.rangeRestrict_surjective r
    have hu' : u⁻¹ ∈ Subgroup.normalizer (pSpan P : Set G) := inv_mem hu
    refine ⟨I.φ.rangeRestrict (TwinThinPf.conjOn _ u⁻¹ hu' x), ?_⟩
    rw [TwinThinPf.induced_apply]
    congr 1
    apply Subtype.ext
    simp [TwinThinPf.conjOn_apply, mul_assoc]
  have hbij : Function.Bijective σ := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  obtain ⟨w, hw⟩ := hAut I.φ.range I.range_eq σ hbij hperm
  refine ⟨w, fun x y hxy => ?_⟩
  have h1 := hw (I.φ.rangeRestrict x)
  rw [TwinThinPf.induced_apply] at h1
  have hy : TwinThinPf.conjOn _ u hu x = y := Subtype.ext hxy.symm
  rw [hy] at h1
  exact h1

theorem map_conjSub_of_induced (I : AEIdent P m) {u : G}
    (hu : u ∈ Subgroup.normalizer (pSpan P : Set G)) {w : Wr m} (hw : InducedBy I u w)
    (L : Subgroup G) :
    ((conjSub u L).subgroupOf (pSpan P)).map I.φ =
      ((L.subgroupOf (pSpan P)).map I.φ).map (MulAut.conj (mkQ m w)).toMonoidHom := by
  have hu' : u⁻¹ ∈ Subgroup.normalizer (pSpan P : Set G) := inv_mem hu
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyL : u⁻¹ * (y : G) * u ∈ L := mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp hy)
    have hxP : u⁻¹ * (y : G) * u ∈ pSpan P := by
      have := TwinThinPf.conj_mem_of_normalizer hu' y.2
      simpa using this
    refine ⟨I.φ ⟨u⁻¹ * (y : G) * u, hxP⟩, ⟨⟨u⁻¹ * (y : G) * u, hxP⟩,
      Subgroup.mem_subgroupOf.mpr hyL, rfl⟩, ?_⟩
    have := hw ⟨u⁻¹ * (y : G) * u, hxP⟩ y (by show (y : G) = u * (u⁻¹ * (y : G) * u) * u⁻¹; group)
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    exact this.symm
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxL : (x : G) ∈ L := Subgroup.mem_subgroupOf.mp hx
    have hyP : u * (x : G) * u⁻¹ ∈ pSpan P := TwinThinPf.conj_mem_of_normalizer hu x.2
    refine ⟨⟨u * (x : G) * u⁻¹, hyP⟩, Subgroup.mem_subgroupOf.mpr (conj_mem_conjSub hxL), ?_⟩
    have := hw x ⟨u * (x : G) * u⁻¹, hyP⟩ rfl
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    exact this

theorem InducedBy.cent {I : AEIdent P m} {u : G} {w : Wr m} (hw : InducedBy I u w)
    {x : ↥(pSpan P)} (hux : u * (x : G) = (x : G) * u) :
    mkQ m w * I.φ x * (mkQ m w)⁻¹ = I.φ x :=
  (hw x x (by rw [hux]; group)).symm

theorem perm_eq_one_of_comm (hm : 5 ≤ m) (I : AEIdent P m) (h8 : ∀ L ∈ P, Nat.card ↥L = 8) {u : G}
    {w : Wr m} (hw : InducedBy I u w)
    (hcomm : ∀ L ∈ P, ∀ t : G, IsUniqueInvolution L t → u * t = t * u) : w.perm = 1 := by
  refine TwinThinPf18.perm_eq_one_of_cent_zBar hm w fun β hβ => ?_
  obtain ⟨L, hL, hlab⟩ := I.label_surj β hβ true
  obtain ⟨t, ht, hφt⟩ := TL4.AECov.exists_isUniqueInvolution I hm hL (h8 L hL) hlab
  have htX : t ∈ pSpan P := le_pSpan hL ht.mem
  have h1 := hw ⟨t, htX⟩ ⟨t, htX⟩ (by
    show t = u * t * u⁻¹
    rw [hcomm L hL t ht]
    group)
  rw [hφt] at h1
  exact h1.symm

theorem le_pCoreOf_of_inv {X Q : Subgroup G} (hQX : Q ≤ X)
    (hQn : ∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hQ2 : IsPGroup 2 ↥Q) : Q ≤ pCoreOf 2 X := by
  have hQnorm : (Q.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQX]
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hQn x hx y hy, fun hy => ?_⟩
    have := hQn x⁻¹ (X.inv_mem hx) _ hy
    simpa [mul_assoc] using this
  exact CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 Q X hQX hQnorm hQ2

theorem comm_mem_pCore_of_perm_one (hm : 5 ≤ m) (I : AEIdent P m) (hk : IsPGroup 2 I.φ.ker) {u : G}
    (hu : u ∈ Subgroup.normalizer (pSpan P : Set G)) {w : Wr m} (hw : InducedBy I u w)
    (hσ : w.perm = 1) : ∀ x ∈ pSpan P, u * x * u⁻¹ * x⁻¹ ∈ pCoreOf 2 (pSpan P) := by
  set V : Subgroup (AEQ m) := (vecSub m).map (mkQ m) with hV
  have hVn : V.Normal := vecSub_normal.map _ (QuotientGroup.mk'_surjective _)
  have hV2 : IsPGroup 2 V := by
    rintro ⟨_, v, hv, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, pow_one, pow_two, ← map_mul, vecSub_mul_self hv, map_one]
    rfl
  set Q : Subgroup G := (V.comap I.φ).map (pSpan P).subtype with hQ
  have hQ2 : IsPGroup 2 ↥Q := (hV2.comap_of_ker_isPGroup I.φ hk).map _
  have hQX : Q ≤ pSpan P := Subgroup.map_subtype_le _
  have hQn : ∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q := by
    intro x hx q hq
    obtain ⟨q', hq', rfl⟩ := hq
    refine ⟨⟨x, hx⟩ * q' * ⟨x, hx⟩⁻¹, ?_, rfl⟩
    show I.φ (⟨x, hx⟩ * q' * ⟨x, hx⟩⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv]
    exact hVn.conj_mem _ hq' _
  have hle := le_pCoreOf_of_inv hQX hQn hQ2
  intro x hx
  apply hle
  have hux : u * x * u⁻¹ ∈ pSpan P := TwinThinPf.conj_mem_of_normalizer hu hx
  refine ⟨⟨u * x * u⁻¹, hux⟩ * ⟨x, hx⟩⁻¹, ?_, rfl⟩
  show I.φ (⟨u * x * u⁻¹, hux⟩ * ⟨x, hx⟩⁻¹) ∈ V
  rw [map_mul, map_inv, hw ⟨x, hx⟩ ⟨u * x * u⁻¹, hux⟩ rfl]
  have hr : I.φ ⟨x, hx⟩ ∈ (aeSub m).map (mkQ m) := I.range_eq ▸ ⟨_, rfl⟩
  obtain ⟨a, -, ha⟩ := hr
  rw [← ha]
  exact TwinThinPf18.comm_mem_vecBar w a hσ

theorem pCoreOf_le_Zgrp_sup_ker (hm : 5 ≤ m) (I : AEIdent P m) (h8 : ∀ L ∈ P, Nat.card ↥L = 8) :
    pCoreOf 2 (pSpan P) ≤ Zgrp P ⊔ I.φ.ker.map (pSpan P).subtype := by
  intro x hx
  have hxX : x ∈ pSpan P := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 _ hx
  set T : Subgroup ↥(pSpan P) := (pCoreOf 2 (pSpan P)).subgroupOf (pSpan P) with hT
  have hTn : T.Normal := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2
    (pSpan P) (pSpan P) le_rfl (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hT2 : IsPGroup 2 ↥T :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 (pSpan P)).of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 (pSpan P))).symm
  have hxT : (⟨x, hxX⟩ : ↥(pSpan P)) ∈ T := hx
  have hker' := TL4.AECov.le_ker_permHom_of_normal I hm hTn hT2 hxT
  obtain ⟨w, hw, hwe⟩ := TL4.AECov.exists_mem_zSpan_of_mem_ker I hm h8 hker'
  have hzs : TL4.AECov.zSpan P ≤ (Zgrp P).comap (pSpan P).subtype := by
    rw [TL4.AECov.zSpan, Subgroup.closure_le]
    rintro y' ⟨L, hL, hy'⟩
    exact Subgroup.subset_closure ⟨L, hL, hy'⟩
  have hk : w⁻¹ * ⟨x, hxX⟩ ∈ I.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hwe, inv_mul_cancel]
  have hxe : x = (w : G) * ((w⁻¹ * ⟨x, hxX⟩ : ↥(pSpan P)) : G) := by
    simp
  rw [hxe]
  exact Subgroup.mul_mem_sup (hzs hw) ⟨_, hk, rfl⟩

end Cross

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
