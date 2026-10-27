module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Points

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped Pointwise

namespace G2

variable {K : Type} [Field K] [CharP K 2]

theorem eq_conj_of_forall_mem_g2BCGroup
    [Finite K] (hK : Nat.card K = 4) (α : MulAut ↥(adjointGroup .G2 K))
    (hα : ∀ z : ↥(adjointGroup .G2 K), (z : ModGL .G2 K) ∈ g2BCGroup K → α z = z) :
    ∃ g : ↥(adjointGroup .G2 K), (g : ModGL .G2 K) ∈ g2ShortParabolicRadical K ⊔ g2TorusR K ∧
      α = MulAut.conj g := by
  have hK4 : 4 ≤ Nat.card K := hK.ge
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := (even_G2_exact_automorphism_normal_form (f := 2) le_rfl K
    (by rw [hK]; norm_num)).1 α
  have hZ₀C : g2BCGroup K ≤ adjointGroup .G2 K :=
    g2BCGroup_le_g2ShortParabolicRadical.trans g2ShortParabolicRadical_le_adjointGroup
  have hXc : ∀ t : K, pinnedX .G2 K g2c t ∈ g2BCGroup K := fun t =>
    ⟨0, t, by simp [g2N, pinnedX_zero]⟩
  have key : ∀ t : K, pinnedX .G2 K g2c t =
      (g : ModGL .G2 K) * pinnedX .G2 K g2c (σ t) * (g : ModGL .G2 K)⁻¹ := by
    intro t
    have h1 := hgσ ⟨_, hZ₀C (hXc t)⟩
    rw [hα _ (hXc t)] at h1
    have h2 : Units.map (entrywiseHom σ.toRingHom) (pinnedX .G2 K g2c t) =
        pinnedX .G2 K g2c (σ t) :=
      Units.ext (entrywise_pinnedX σ.toRingHom g2c t)
    rw [h2] at h1
    exact h1
  have hgL : (g : ModGL .G2 K) ∈ g2LongCent K := by
    refine mem_inf.mpr ⟨g.2, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := key 1
    rw [map_one] at h1
    calc (g : ModGL .G2 K) * pinnedX .G2 K g2c 1 =
        (g : ModGL .G2 K) * pinnedX .G2 K g2c 1 * (g : ModGL .G2 K)⁻¹ * g := by group
      _ = pinnedX .G2 K g2c 1 * g := by rw [← h1]
  obtain ⟨-, hcent⟩ := g2Centr184 K hK4
  have hcomm : ∀ s : K, (g : ModGL .G2 K) * pinnedX .G2 K g2c s =
      pinnedX .G2 K g2c s * (g : ModGL .G2 K) := by
    intro s
    have h1 : pinnedX .G2 K g2c s ∈ g2Centralizer K (g2LongCent K : Set (ModGL .G2 K)) := by
      rw [hcent]
      exact mem_rootSubgroup.mpr ⟨s, rfl⟩
    exact mem_centralizer_iff.mp (mem_inf.mp h1).2 _ hgL
  have hσ : ∀ t, σ t = t := by
    intro t
    have h1 := key t
    rw [hcomm, mul_inv_cancel_right] at h1
    exact (pinnedX_injective .G2 K g2c h1).symm
  have hσ' : σ.toRingHom = RingHom.id K := RingHom.ext hσ
  have hαg : α = MulAut.conj g := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hgσ h, hσ', show Units.map (entrywiseHom (RingHom.id K)) (h : ModGL .G2 K) = h from
      Units.ext (entrywise_id _)]
    rfl
  refine ⟨g, ?_, hαg⟩
  have hgZ : (g : ModGL .G2 K) ∈ centralizer (g2BCGroup K : Set (ModGL .G2 K)) := by
    rw [mem_centralizer_iff]
    intro z hz
    have h1 := congrArg Subtype.val (hα ⟨z, hZ₀C hz⟩ hz)
    rw [hαg] at h1
    change (g : ModGL .G2 K) * z * (g : ModGL .G2 K)⁻¹ = z at h1
    calc z * (g : ModGL .G2 K) = (g : ModGL .G2 K) * z * (g : ModGL .G2 K)⁻¹ * g := by
          rw [h1]
      _ = (g : ModGL .G2 K) * z := by group
  have hgP : (g : ModGL .G2 K) ∈ g2Para K := by
    rw [← adjointGroup_inf_normalizer_eq]
    exact ⟨g.2, centralizer_le_normalizer _ hgZ⟩
  exact g2Para_inf_centralizer_le hK ⟨hgP, hgZ⟩

end G2

namespace Sec3Model

variable
  {G : Type} [Group G] {A A₁ E F : Subgroup G} {x : G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {f : ↥(adjointGroup .G2 K) →* G}

omit [Finite K] in
theorem act_apply (hM : Sec3Model G A A₁ E F x K f) (n : normalizer (A : Set G))
    (c : ↥(adjointGroup .G2 K)) : f (hM.act n c) = n * f c * (n : G)⁻¹ := by
  change f (hM.equivA.symm (A.normalizerMonoidHom n (hM.equivA c))) = _
  rw [coe_equivA_symm]
  rfl

theorem exists_mul_of_mem_normalizer (hK : Nat.card K = 4) (hM : Sec3Model G A A₁ E F x K f)
    {w : G} (hwN : w ∈ normalizer (A : Set G))
    (hwc : w ∈ centralizer ((E ⊓ A : Subgroup G) : Set G)) :
    ∃ k ∈ centralizer (A : Set G), ∃ c ∈ ((g2ShortParabolicRadical K ⊔ g2TorusR K).subgroupOf
      (adjointGroup .G2 K)).map f, w = k * c := by
  have hα : ∀ z : ↥(adjointGroup .G2 K), (z : ModGL .G2 K) ∈ g2BCGroup K →
      hM.act ⟨w, hwN⟩ z = z := by
    intro z hz
    apply hM.inj
    rw [act_apply]
    have hfz : f z ∈ E ⊓ A := by
      rw [← hM.E_eq]
      exact ⟨z, mem_subgroupOf.mpr hz, rfl⟩
    have h1 := mem_centralizer_iff.mp hwc (f z) hfz
    change w * f z * w⁻¹ = f z
    rw [← h1, mul_inv_cancel_right]
  obtain ⟨g, hg, hαg⟩ := G2.eq_conj_of_forall_mem_g2BCGroup hK _ hα
  have hfgA : f g ∈ A := by
    rw [← hM.range_eq]
    exact ⟨g, rfl⟩
  refine ⟨w * (f g)⁻¹, ?_, f g, ⟨g, mem_subgroupOf.mpr hg, rfl⟩, by group⟩
  have h1 : hM.act ⟨f g, le_normalizer hfgA⟩ = hM.act ⟨w, hwN⟩ := by
    rw [hM.act_of_mem hfgA, hαg]
    congr 1
    exact hM.equivA.symm_apply_eq.mpr (Subtype.ext rfl)
  have h2 : hM.act (⟨w, hwN⟩ * ⟨f g, le_normalizer hfgA⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  exact (hM.isActionHom_act.eq_one_iff _).mp h2

end Sec3Model

section Step33iii

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G} {x : G}
  {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U : Subgroup G}

theorem isPGroup_zpowers_of_pow {M : Type*} [Group M] {k : M} {n : ℕ} (hk : k ^ 2 ^ n = 1) :
    IsPGroup 2 (zpowers k) := by
  rintro ⟨_, hy⟩
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
  refine ⟨n, Subtype.ext ?_⟩
  change (k ^ i) ^ 2 ^ n = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]

omit [Finite G] in
theorem conj_mem_centralizer_of_mem {X : Subgroup G} {n c : G}
    (hn : n ∈ normalizer (X : Set G)) (hc : c ∈ centralizer (X : Set G)) :
    n * c * n⁻¹ ∈ centralizer (X : Set G) := by
  rw [mem_centralizer_iff]
  intro e he
  have he' : n⁻¹ * e * n ∈ X := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hn) e).mp he
    simpa using h1
  have h1 := mem_centralizer_iff.mp hc _ he'
  calc e * (n * c * n⁻¹) = n * ((n⁻¹ * e * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * e * n)) * n⁻¹ := by rw [h1]
    _ = n * c * n⁻¹ * e := by group

theorem sec3D_model
    (hD : Sec3D G A A₁ R g E F x Zs P T Q B₀ z y D J U) :
    D ⊔ zpowers x ≤ A ⊓ centralizer (E : Set G) ∧ x ∈ normalizer (D : Set G) ∧
      ∀ w ∈ normalizer (A : Set G), w ∈ centralizer ((E ⊓ A : Subgroup G) : Set G) →
        ∃ k ∈ centralizer (A : Set G), ∃ c ∈ D ⊔ zpowers x, w = k * c := by
  have hS := hD.suz.setting
  obtain ⟨K, _, _, _, hK, f, hM⟩ := exists_sec3Model hS
  have hD₀C : g2ShortParabolicRadical K ≤ adjointGroup .G2 K :=
    G2.g2ShortParabolicRadical_le_adjointGroup
  have hHrC : g2TorusR K ≤ adjointGroup .G2 K := G2.g2TorusR_le_adjointGroup
  have hPC : G2.g2Para K ≤ adjointGroup .G2 K :=
    sup_le (sup_le hD₀C (g2RankOne_le_adjointGroup g2ia)) hHrC
  have hDf : D = ((g2ShortParabolicRadical K).subgroupOf (adjointGroup .G2 K)).map f := by
    rw [hD.D_eq, hM.I_eq, Sec3.tr_pCoreOf hM.inj hPC, G2.pCoreOf_g2Para hK]
  have hDx : D ⊔ zpowers x =
      ((g2ShortParabolicRadical K ⊔ g2TorusR K).subgroupOf (adjointGroup .G2 K)).map f := by
    rw [hDf, ← hM.x_eq, Sec3.tr_sup hD₀C hHrC]
  have hRA : R ≤ centralizer (A : Set G) := hS.sylowR.le
  have hEAR : E ≤ A ⊔ R := hS.frame.E_le.trans (sup_le_sup_right hS.le _)
  refine ⟨?_, ?_, fun w hwN hwc => ?_⟩
  · rw [hDx]
    rintro _ ⟨c, hc, rfl⟩
    have hcZ : (c : ModGL .G2 K) ∈ centralizer (g2BCGroup K : Set (ModGL .G2 K)) :=
      sup_le (G2.g2ShortParabolicRadical_le_centralizer (K := K))
        (G2.g2TorusR_le_centralizer_g2BCGroup hK) (mem_subgroupOf.mp hc)
    have hfcA : f c ∈ A := by
      rw [← hM.range_eq]
      exact ⟨c, rfl⟩
    refine mem_inf.mpr ⟨hfcA, ?_⟩
    have hE : E ≤ centralizer ({f c} : Set G) := by
      rw [eq_inf_sup_of_le_sup hRA hS.frame.R_le_E hEAR]
      refine sup_le ?_ fun r hr => mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp (hRA hr) _ hfcA).symm
      rw [← hM.E_eq]
      rintro _ ⟨z, hz, rfl⟩
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact congrArg f (Subtype.ext (mem_centralizer_iff.mp hcZ _ (mem_subgroupOf.mp hz)))
    rw [mem_centralizer_iff]
    intro e he
    exact mem_centralizer_singleton_iff.mp (hE he)
  · have hxI : x ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G) := by
      have hx' : x ∈ ((g2TorusR K).subgroupOf (adjointGroup .G2 K)).map f := by
        rw [hM.x_eq]
        exact mem_zpowers x
      rw [hM.I_eq]
      exact Sec3.tr_mono le_sup_right hx'
    exact hD.D_eq ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hxI
  · obtain ⟨k, hk, c, hc, rfl⟩ := hM.exists_mul_of_mem_normalizer hK hwN hwc
    exact ⟨k, hk, c, hDx ▸ hc, rfl⟩

theorem mem_DR_of_mem_normalizer
    (hD : Sec3D G A A₁ R g E F x Zs P T Q B₀ z y D J U) {w : G}
    (hwN : w ∈ normalizer (A : Set G)) (hwc : w ∈ centralizer ((E ⊓ A : Subgroup G) : Set G))
    (hwR : w ∈ normalizer (R : Set G)) {n : ℕ} (hw : w ^ 2 ^ n = 1) : w ∈ D ⊔ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hD.suz.setting
  obtain ⟨hDxA, hxD, hdec⟩ := sec3D_model hD
  obtain ⟨k, hk, c, hc, rfl⟩ := hdec w hwN hwc
  have hcA : c ∈ A := (hDxA hc).1
  have hkc : k * c = c * k := (mem_centralizer_iff.mp hk c hcA).symm
  have hAK : ∀ v ∈ A, v ∈ centralizer (A : Set G) → v = 1 := fun v hv hvc => by
    have h1 : (⟨v, hv⟩ : ↥A) ∈ center ↥A := mem_center_iff.mpr fun a =>
      Subtype.ext (mem_centralizer_iff.mp hvc a a.2)
    rw [hS.center_eq, mem_bot] at h1
    exact congrArg Subtype.val h1
  have hkn : k ^ 2 ^ n = (c ^ 2 ^ n)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← (Commute.mul_pow hkc (2 ^ n)), hw]
  have hcn : c ^ 2 ^ n = 1 := by
    have h1 : (c ^ 2 ^ n)⁻¹ ∈ A := inv_mem (pow_mem hcA _)
    have h2 : (c ^ 2 ^ n)⁻¹ ∈ centralizer (A : Set G) := hkn ▸ pow_mem hk _
    exact inv_eq_one.mp (hAK _ h1 h2)
  have hkn' : k ^ 2 ^ n = 1 := by rw [hkn, hcn, inv_one]
  have hx3 : x ^ 3 = 1 := by
    rw [← hS.order_x]
    exact pow_orderOf_eq_one x
  have hcD : c ∈ D := G2.mem_of_pow_eq_one_of_mem_sup (zpowers_le.mpr hxD) hc hcn
    (fun h hh => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hh
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow])
    (Nat.Coprime.pow_left _ (by norm_num))
  have hkR : k ∈ normalizer (R : Set G) := by
    have hcR : c ∈ normalizer (R : Set G) := centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hS.sylowR.le hr) c hcA).symm)
    have h1 := mul_mem hwR (inv_mem hcR)
    rwa [mul_inv_cancel_right] at h1
  have hk2 := isPGroup_zpowers_of_pow hkn'
  have hsup : IsPGroup 2 ↥(R ⊔ zpowers k) :=
    hS.sylowR.isPGroup.to_sup_of_normal_left' hk2 (zpowers_le.mpr hkR)
  have hRk := hS.sylowR.eq_of_le le_sup_left (sup_le hS.sylowR.le (zpowers_le.mpr hk)) hsup
  have hkR' : k ∈ R := hRk ▸ mem_sup_right (mem_zpowers k)
  exact mul_mem (mem_sup_right hkR') (mem_sup_left hcD)

omit [Finite G] in
theorem mem_normalizer_inf {X Y : Subgroup G} {n : G} (hX : n ∈ normalizer (X : Set G))
    (hY : n ∈ normalizer (Y : Set G)) : n ∈ normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro w
  rw [mem_inf, mem_inf, mem_normalizer_iff.mp hX w, mem_normalizer_iff.mp hY w]

omit [Finite G] in
theorem mem_normalizer_normalizer {X : Subgroup G} {n : G} (hn : n ∈ normalizer (X : Set G)) :
    n ∈ normalizer ((normalizer (X : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro w
  refine ⟨fun h => mul_mem (mul_mem hn h) (inv_mem hn), fun h => ?_⟩
  have h1 := mul_mem (mul_mem (inv_mem hn) h) hn
  simpa [mul_assoc] using h1

theorem DR_facts
    (hD : Sec3D G A A₁ R g E F x Zs P T Q B₀ z y D J U) :
    IsPGroup 2 ↥(D ⊔ R) ∧ D ⊔ R ≤ centralizer (E : Set G) ∧
      (∀ c ∈ centralizer (E : Set G), ∀ n : ℕ, c ^ 2 ^ n = 1 → c ∈ D ⊔ R) ∧
      normalizer (E : Set G) ≤ normalizer ((D ⊔ R : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hD.suz.setting
  obtain ⟨hDxA, -, -⟩ := sec3D_model hD
  have hFr := hS.frame
  have hRA : R ≤ centralizer (A : Set G) := hS.sylowR.le
  have hDA : D ≤ A := (le_sup_left.trans hDxA).trans inf_le_left
  have hDC : D ≤ centralizer (E : Set G) := (le_sup_left.trans hDxA).trans inf_le_right
  have hRC : R ≤ centralizer (E : Set G) := fun r hr => mem_centralizer_iff.mpr fun e he =>
    congrArg Subtype.val (hFr.elemE.1.is_comm.comm ⟨e, he⟩ ⟨r, hFr.R_le_E hr⟩)
  have hD2 : IsPGroup 2 D := hD.D_eq ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRD : R ≤ normalizer (D : Set G) := fun r hr => centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun d hd => mem_centralizer_iff.mp (hRA hr) d (hDA hd))
  have h2 : IsPGroup 2 ↥(D ⊔ R) := hD2.to_sup_of_normal_left' hS.sylowR.isPGroup hRD
  have hle : D ⊔ R ≤ centralizer (E : Set G) := sup_le hDC hRC
  have hNA : normalizer (R : Set G) ≤ normalizer (A : Set G) := by
    have h := AS76b.Lemma36.normalizer_le hS.base.hyp31 hS.sylowR 1
    rwa [rightConjugate_one, rightConjugate_one] at h
  have hCR : centralizer (E : Set G) ≤ normalizer (R : Set G) :=
    (centralizer_le (by exact_mod_cast hFr.R_le_E)).trans (centralizer_le_normalizer _)
  have hmem : ∀ c ∈ centralizer (E : Set G), ∀ n : ℕ, c ^ 2 ^ n = 1 → c ∈ D ⊔ R :=
    fun c hc n hcn => mem_DR_of_mem_normalizer hD (hNA (hCR hc))
      (centralizer_le (by exact_mod_cast (inf_le_left : E ⊓ A ≤ E)) hc) (hCR hc) hcn
  have hconj : ∀ n ∈ normalizer (E : Set G), ∀ v ∈ D ⊔ R, n * v * n⁻¹ ∈ D ⊔ R := by
    intro n hn v hv
    obtain ⟨k, hk⟩ := h2 ⟨v, hv⟩
    refine hmem _ (conj_mem_centralizer_of_mem hn (hle hv)) k ?_
    have hk' : v ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [conj_pow, hk', mul_one, mul_inv_cancel]
  refine ⟨h2, hle, hmem, fun n hn => G2.mem_normalizer_of_conj (fun v hv => hconj n hn v hv)
    (fun v hv => ?_)⟩
  have h1 := hconj n⁻¹ (inv_mem hn) v hv
  rwa [inv_inv] at h1

end Step33iii

end CFSG.ComponentClassification.AS81
