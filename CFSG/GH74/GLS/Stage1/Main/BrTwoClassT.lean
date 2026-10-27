module

public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassI
public import CFSG.GH74.GLS.Stage2.Local.Bar
public import CFSG.GH74.GLS.Stage1.Main.BrPairStd4
public import CFSG.GH74.GLS.Stage1.Main.BrRankE16

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.GH74.GLS.Stage2.Final CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK.Lifted
open scoped commutatorElement Pointwise

section Transfer

variable {G : Type} [Group G] [Finite G] {z : G}

theorem inf_Oz_eq {K : Subgroup G} (hK : IsPCompIn 2 (Cz z) K) {w : G} (hw2 : w * w = 1)
    (hwN : w ∈ normalizer (K : Set G)) : (K ⊔ zpowers w) ⊓ Oz z = pPrimeCoreOf 2 K := by
  apply le_antisymm
  · rintro g ⟨hgB, hgO⟩
    have hzw : zpowers w ≤ normalizer (K : Set G) := Subgroup.zpowers_le.2 hwN
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left K (zpowers w) hzw
    have hg' : g ∈ (K : Set G) * (zpowers w : Set G) := by
      rw [← hmul]
      exact hgB
    obtain ⟨k, hk, a, ha, rfl⟩ := Set.mem_mul.1 hg'
    obtain ⟨c, hc⟩ := odd_orderOf_of_mem_odd (X := G) (N := Oz z) card_Oz_odd hgO
    have hgK : k * a ∈ K := by
      rcases eq_one_or_eq_of_mem_zpowers_sq hw2 ha with h | h
      · rw [h, mul_one]
        exact hk
      · rw [h] at hc ⊢
        have hsq : (k * w) * (k * w) ∈ K := by
          have e : (k * w) * (k * w) = k * (w * k * w⁻¹) := by
            calc (k * w) * (k * w) = k * (w * k * w⁻¹) * (w * w) := by group
              _ = k * (w * k * w⁻¹) := by rw [hw2, mul_one]
          rw [e]
          exact K.mul_mem hk ((Subgroup.mem_normalizer_iff.1 hwN k).1 hk)
        have hg1 : (k * w) ^ (2 * c + 1) = 1 := by rw [← hc]; exact pow_orderOf_eq_one _
        have e2 : (k * w) = ((k * w) * (k * w)) ^ (c + 1) := by
          calc (k * w) = (k * w) ^ (2 * c + 1) * (k * w) := by rw [hg1, one_mul]
            _ = ((k * w) * (k * w)) ^ (c + 1) := by
              rw [← pow_succ, ← pow_two, ← pow_mul]
              congr 1
        rw [e2]
        exact K.pow_mem hsq _
    exact inf_Oz_le hK ⟨hgK, hgO⟩
  · intro n hn
    exact ⟨(le_sup_left : K ≤ K ⊔ zpowers w) (Subgroup.map_subtype_le _ hn), pPrimeCoreOf_le_Oz hK hn⟩

end Transfer

section CenterBar

theorem card_center_le_two {X : Type} [Group X] {F : Type} [Field F] (e : X ≃* StatedSL 2 F) :
    Nat.card (center X) ≤ 2 := by
  classical
  let e' : X ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have hsub : ((center X : Subgroup X) : Set X) ⊆ (({1, e'.symm (-1)} : Finset X) : Set X) := by
    intro c hc
    have hzc : e' c ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e'.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_center_iff.1 hc g'
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hzc
    rw [Fintype.card_fin] at hr
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases sq_eq_one_iff.1 hr with h | h
    · left
      apply e'.injective
      rw [map_one]
      apply Subtype.ext
      rw [← hrA, h, map_one]
      rfl
    · right
      apply e'.injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [← hrA, h, map_neg, map_one]
      rfl
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at h1
  have h2 : (({1, e'.symm (-1)} : Finset X)).card ≤ 2 := Finset.card_le_two
  have h3 : Nat.card (center X) = ((center X : Subgroup X) : Set X).ncard := Nat.card_coe_set_eq _
  omega

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem center_imgBar_eq (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) {q : ℕ} (hL : HasSL2Model ↥(imgBar z K) (fun r => r = q)) :
    (center ↥(imgBar z K)).map (imgBar z K).subtype =
      zpowers (piC z ⟨z, mem_centralizer_singleton_iff.2 rfl⟩) := by
  set zb : CentralizerBar z := piC z ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ with hzb
  have hzbK : zb ∈ imgBar z K := by
    rcases hK with rfl | rfl
    · exact (zbar_facts4 hII hs).1.1
    · exact (zbar_facts4 hII hs).1.2
  have hzb1 : zb ≠ 1 := (zbar_facts4 hII hs).2
  have hzbc : zb ∈ center (CentralizerBar z) := toBar_z_mem_center z
  have hzb2 : zb * zb = 1 := by
    have hz2 : z * z = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hs.orderOf_z, pow_two] at this
    rw [hzb, ← map_mul]
    have : (⟨z, mem_centralizer_singleton_iff.2 rfl⟩ : ↥(Cz z)) *
        ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ = 1 := Subtype.ext hz2
    rw [this, map_one]
  have hle : zpowers zb ≤ (center ↥(imgBar z K)).map (imgBar z K).subtype := by
    rw [Subgroup.zpowers_le]
    refine ⟨⟨zb, hzbK⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hzbc g
  obtain ⟨F, iF, fF, -, ⟨e⟩⟩ := hL
  have hcard : Nat.card (center ↥(imgBar z K)) ≤ 2 := card_center_le_two e
  have hcard' : Nat.card ((center ↥(imgBar z K)).map (imgBar z K).subtype) ≤ 2 := by
    rw [Subgroup.card_map_of_injective (imgBar z K).subtype_injective]
    exact hcard
  have hzcard : Nat.card (zpowers zb) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rwa [pow_two]) hzb1
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hzcard]; exact hcard')).symm

end CenterBar

section PGLTransfer

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem pglOver_of_pglQuot (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) {q : ℕ} (hL : HasSL2Model ↥(imgBar z K) (fun r => r = q)) {w : G}
    (hwC : w ∈ Cz z) (hw2 : w * w = 1) (hwN : w ∈ normalizer (K : Set G)) {Fq : Type} [Field Fq]
    [Finite Fq] (hq : Nat.card Fq = q) (h : PGLQuot z w K Fq) :
    PGLOver (imgBar z K) (barOf z (zpowers w)) q := by
  classical
  have hM := m4_of_std hII hs
  have hKpc : IsPCompIn 2 (Cz z) K := by
    rcases hK with rfl | rfl
    · exact hs.comp_isPCompIn (Or.inl rfl)
    · exact hs.comp_isPCompIn (Or.inr rfl)
  have hKC : K ≤ Cz z := hKpc.1
  have hzK : z ∈ K := by
    rcases hK with rfl | rfl
    · exact hM.z_mem_comp (Or.inl rfl)
    · exact hM.z_mem_comp (Or.inr rfl)
  have hzC : z ∈ Cz z := mem_centralizer_singleton_iff.2 rfl
  set zb : CentralizerBar z := piC z ⟨z, hzC⟩ with hzb
  have hZeq : (center ↥(imgBar z K)).map (imgBar z K).subtype = zpowers zb :=
    center_imgBar_eq hII hs hK hL
  have hzbc : zb ∈ center (CentralizerBar z) := toBar_z_mem_center z
  set B : Subgroup G := K ⊔ zpowers w with hB
  have hwzp : zpowers w ≤ Cz z := Subgroup.zpowers_le.2 hwC
  have hBC : B ≤ Cz z := sup_le hKC hwzp
  set L : Subgroup (CentralizerBar z) := imgBar z K with hLdef
  set T : Subgroup (CentralizerBar z) := barOf z (zpowers w) with hTdef
  have hrange : ((piC z).comp (Subgroup.inclusion hBC)).range = L ⊔ T := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, hB, Subgroup.subgroupOf_sup hKC hwzp,
      Subgroup.map_sup]
    rfl
  let Φ₀ : ↥B →* ↥(L ⊔ T) :=
    ((piC z).comp (Subgroup.inclusion hBC)).codRestrict (L ⊔ T) (fun b => by
      rw [← hrange]
      exact ⟨b, rfl⟩)
  have hΦ₀surj : Function.Surjective Φ₀ := by
    intro y
    have : (y : CentralizerBar z) ∈ ((piC z).comp (Subgroup.inclusion hBC)).range := by
      rw [hrange]
      exact y.2
    obtain ⟨b, hb⟩ := this
    exact ⟨b, Subtype.ext hb⟩
  have hZcentral : ∀ n ∈ zpowers zb, ∀ g : CentralizerBar z, g * n = n * g := by
    intro n hn g
    have : n ∈ center (CentralizerBar z) := (Subgroup.zpowers_le.2 hzbc) hn
    exact Subgroup.mem_center_iff.1 this g
  have hZnormal : (((center ↥L).map L.subtype).subgroupOf (L ⊔ T)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : CentralizerBar z) ∈ zpowers zb := by
      rw [← hZeq]
      exact hn
    have e : (g : CentralizerBar z) * n * (g : CentralizerBar z)⁻¹ = n := by
      rw [hZcentral n hn' g]
      group
    rw [Subgroup.mem_subgroupOf, hZeq] at hn ⊢
    show (g : CentralizerBar z) * n * (g : CentralizerBar z)⁻¹ ∈ _
    rw [e]
    exact hn
  let Φ : ↥B →* ↥(L ⊔ T) ⧸ (((center ↥L).map L.subtype).subgroupOf (L ⊔ T)) :=
    (QuotientGroup.mk' _).comp Φ₀
  have hΦsurj : Function.Surjective Φ := (QuotientGroup.mk'_surjective _).comp hΦ₀surj
  have hker : Φ.ker = (pPrimeCoreOf 2 K ⊔ zpowers z).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have hΦb : Φ b = 1 ↔ piC z ⟨(b : G), hBC b.2⟩ ∈ zpowers zb := by
      show (QuotientGroup.mk (Φ₀ b) : _) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, ← hZeq]
      rfl
    rw [hΦb]
    have hpow : ∀ n : ℤ, zb ^ n = piC z ⟨z ^ n, zpow_mem hzC n⟩ := by
      intro n
      rw [hzb, ← map_zpow]
      rfl
    constructor
    · intro hb
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hb
      rw [hpow n] at hn
      have hb' : (b : G) * z ^ (-n) ∈ pPrimeCoreOf 2 K := by
        rw [← inf_Oz_eq hKpc hw2 hwN]
        refine ⟨?_, ?_⟩
        · exact B.mul_mem b.2 (Subgroup.zpow_mem _ (Subgroup.mem_sup_left hzK) _)
        · have hbc : (b : G) * z ^ (-n) ∈ Cz z :=
            (Cz z).mul_mem (hBC b.2) (zpow_mem hzC _)
          have hone : piC z ⟨(b : G) * z ^ (-n), hbc⟩ = 1 := by
            have e : (⟨(b : G) * z ^ (-n), hbc⟩ : ↥(Cz z)) =
                ⟨(b : G), hBC b.2⟩ * ⟨z ^ (-n), zpow_mem hzC _⟩ := rfl
            rw [e, map_mul, ← hn]
            have : (⟨z ^ (-n), zpow_mem hzC _⟩ : ↥(Cz z)) = ⟨z ^ n, zpow_mem hzC n⟩⁻¹ :=
              Subtype.ext (by simp)
            rw [this, map_inv]
            exact mul_inv_cancel _
          exact (hatMk_eq_one_iff (Cz z) ⟨(b : G) * z ^ (-n), hbc⟩).1 hone
      have e : (b : G) = ((b : G) * z ^ (-n)) * z ^ n := by group
      rw [e]
      exact Subgroup.mul_mem_sup hb' (Subgroup.zpow_mem _ (mem_zpowers z) n)
    · intro hb
      have hcomm : ∀ a ∈ pPrimeCoreOf 2 K, ∀ c ∈ zpowers z, a * c = c * a := by
        intro a ha c hc
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
        have haC : a ∈ Cz z := hKC (Subgroup.map_subtype_le _ ha)
        exact ((Commute.zpow_right (show Commute a z from
          (mem_centralizer_singleton_iff.1 haC)) k).eq)
      obtain ⟨a, ha, c, hc, hab⟩ :=
        CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hcomm hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      have haO : a ∈ Oz z := pPrimeCoreOf_le_Oz hKpc ha
      have haC : a ∈ Cz z := hKC (Subgroup.map_subtype_le _ ha)
      have hone : piC z ⟨a, haC⟩ = 1 := (hatMk_eq_one_iff (Cz z) ⟨a, haC⟩).2 haO
      have hbeq : (⟨(b : G), hBC b.2⟩ : ↥(Cz z)) = ⟨a, haC⟩ * ⟨z ^ k, zpow_mem hzC k⟩ :=
        Subtype.ext hab
      rw [hbeq, map_mul, hone, one_mul, ← hpow k]
      exact Subgroup.zpow_mem _ (mem_zpowers zb) k
  obtain ⟨hN₀, ⟨ψ⟩⟩ := h
  refine ⟨hZnormal, Fq, inferInstance, inferInstance, hq, ⟨?_⟩⟩
  exact (QuotientGroup.quotientKerEquivOfSurjective Φ hΦsurj).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans ψ)

end PGLTransfer

end CFSG.GH74.GLS.Stage1.Main
