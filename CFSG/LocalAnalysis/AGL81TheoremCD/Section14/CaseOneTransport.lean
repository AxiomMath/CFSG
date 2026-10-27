module

import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComp
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Transport
import CFSG.Quasithin.Vol2.Ch4Sec1Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneDefs

public section

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open scoped commutatorElement Pointwise

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

variable {G : Type} [Group G] [Finite G]

private theorem map_pLayerIn_conj_three (H : Subgroup G) (g : G) :
    pLayerIn 3 (H.map (MulAut.conj g).toMonoidHom) =
      (pLayerIn 3 H).map (MulAut.conj g).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let e : ↥H ≃* ↥(H.map (MulAut.conj g).toMonoidHom) := (MulAut.conj g).subgroupMap H
  have hlayer : (CFSG.pLayer ↥H 3).map e.toMonoidHom =
      CFSG.pLayer ↥(H.map (MulAut.conj g).toMonoidHom) 3 :=
    CFSG.ComponentClassification.UnbalancedGS.FixedLayerPComponent.map_pLayer_mulEquiv 3 e
  unfold pLayerIn
  rw [← hlayer, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem map_sSup_conj_eq (S : Set (Subgroup G)) (g : G) :
    (sSup S).map (MulAut.conj g).toMonoidHom =
      sSup ((fun Y : Subgroup G => Y.map (MulAut.conj g).toMonoidHom) '' S) := by
  rw [(gc_map_comap (MulAut.conj g).toMonoidHom).l_sSup, sSup_image]

private theorem isPComponentIn_map_conj_local {p : ℕ} {L H : Subgroup G} (g : G)
    (h : IsPComponentIn p L H) :
    IsPComponentIn p (L.map (MulAut.conj g).toMonoidHom)
      (H.map (MulAut.conj g).toMonoidHom) :=
  ⟨Subgroup.map_mono h.1,
    CFSG.ComponentClassification.CatFactsSp4.isPComponent_map_subgroupOf p
      (MulAut.conj g) h.1 h.2⟩

private theorem sSup_card_map_conj (p : ℕ) (H : Subgroup G) (g : G) :
    sSup {Y : Subgroup G | Y ≤ H.map (MulAut.conj g).toMonoidHom ∧ Nat.card Y = p} =
      (sSup {Y : Subgroup G | Y ≤ H ∧ Nat.card Y = p}).map
        (MulAut.conj g).toMonoidHom := by
  let S : Set (Subgroup G) := {Y | Y ≤ H ∧ Nat.card Y = p}
  let T : Set (Subgroup G) := {Y | Y ≤ H.map (MulAut.conj g).toMonoidHom ∧ Nat.card Y = p}
  have hST : (fun Y : Subgroup G => Y.map (MulAut.conj g).toMonoidHom) '' S = T := by
    ext Y
    constructor
    · rintro ⟨Z, hZ, rfl⟩
      exact ⟨Subgroup.map_mono hZ.1,
        (Subgroup.card_map_of_injective (MulAut.conj g).injective).trans hZ.2⟩
    · intro hY
      refine ⟨Y.map (MulAut.conj g⁻¹).toMonoidHom, ⟨?_, ?_⟩, ?_⟩
      · have h := Subgroup.map_mono hY.1 (f := (MulAut.conj g⁻¹).toMonoidHom)
        rwa [CFSG.Quasithin.H13.Ch4.map_conj_inv_map_conj H g] at h
      · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hY.2]
      · exact CFSG.Quasithin.H13.Ch4.map_conj_map_conj_inv Y g
  rw [map_sSup_conj_eq, hST]

private theorem sSup_comp_map_conj {M H : Subgroup G} {g : G} (hg : g ∈ M) :
    sSup {Y : Subgroup G | IsPComponentIn 3 Y (H.map (MulAut.conj g).toMonoidHom) ∧
        ¬ Y ≤ M} =
      (sSup {Y : Subgroup G | IsPComponentIn 3 Y H ∧ ¬ Y ≤ M}).map
        (MulAut.conj g).toMonoidHom := by
  have hM : M.map (MulAut.conj g).toMonoidHom = M :=
    CFSG.Quasithin.H13.Ch4.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)
  let S : Set (Subgroup G) := {Y | IsPComponentIn 3 Y H ∧ ¬ Y ≤ M}
  let T : Set (Subgroup G) :=
    {Y | IsPComponentIn 3 Y (H.map (MulAut.conj g).toMonoidHom) ∧ ¬ Y ≤ M}
  have hST : (fun Y : Subgroup G => Y.map (MulAut.conj g).toMonoidHom) '' S = T := by
    ext Y
    constructor
    · rintro ⟨Z, hZ, rfl⟩
      refine ⟨isPComponentIn_map_conj_local g hZ.1, ?_⟩
      intro hle
      apply hZ.2
      have hle' : Z.map (MulAut.conj g).toMonoidHom ≤ M.map (MulAut.conj g).toMonoidHom := by
        rwa [hM]
      exact (Subgroup.map_le_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective).mp hle'
    · intro hY
      have hY' : IsPComponentIn 3 (Y.map (MulAut.conj g⁻¹).toMonoidHom) H := by
        have h := isPComponentIn_map_conj_local g⁻¹ hY.1
        rwa [CFSG.Quasithin.H13.Ch4.map_conj_inv_map_conj H g] at h
      have hnle : ¬ Y.map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
        intro hle
        apply hY.2
        have hle' : Y ≤ M := by
          have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hle
          rwa [CFSG.Quasithin.H13.Ch4.map_conj_map_conj_inv Y g, hM] at h1
        exact hle'
      exact ⟨Y.map (MulAut.conj g⁻¹).toMonoidHom, ⟨hY', hnle⟩,
        CFSG.Quasithin.H13.Ch4.map_conj_map_conj_inv Y g⟩
  rw [map_sSup_conj_eq, hST]

theorem kSub_map_conj {M N : Subgroup G} {g : G} (hg : g ∈ M) :
    kSub 3 M (N.map (MulAut.conj g).toMonoidHom) =
      (kSub 3 M N).map (MulAut.conj g).toMonoidHom := by
  have hM : M.map (MulAut.conj g).toMonoidHom = M :=
    CFSG.Quasithin.H13.Ch4.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)
  have hlayer := map_pLayerIn_conj_three N g
  have hiff : pLayerIn 3 (N.map (MulAut.conj g).toMonoidHom) ≤ M ↔ pLayerIn 3 N ≤ M := by
    have hmap := (Subgroup.map_le_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective :
      (pLayerIn 3 N).map (MulAut.conj g).toMonoidHom ≤
        M.map (MulAut.conj g).toMonoidHom ↔ pLayerIn 3 N ≤ M)
    rw [hlayer]
    conv_lhs => rw [← hM]
    exact hmap
  have hcard := sSup_card_map_conj 3 N g
  have hcomp := sSup_comp_map_conj (M := M) (H := N) hg
  unfold kSub
  rw [hiff]
  by_cases hle : pLayerIn 3 N ≤ M
  · simp only [hle, if_true]
    exact hcard
  · simp only [hle, if_false]
    exact hcomp

theorem IsKComp.map_conj {M N A : Subgroup G} {g : G} (hg : g ∈ M)
    (hA : IsKComp M N A) :
    IsKComp M (N.map (MulAut.conj g).toMonoidHom)
      (A.map (MulAut.conj g).toMonoidHom) := by
  unfold IsKComp at hA ⊢
  rw [kSub_map_conj hg]
  exact isPComponentIn_map_conj_local g hA

private noncomputable def threeStarConjEquiv (A : Subgroup G) (g : G) :
    threeStar A ≃* threeStar (A.map (MulAut.conj g).toMonoidHom) :=
  QuotientGroup.congr (CFSG.pPrimeCore 3 ↥A)
    (CFSG.pPrimeCore 3 ↥(A.map (MulAut.conj g).toMonoidHom))
    ((MulAut.conj g).subgroupMap A)
    (CFSG.pPrimeCore_map_iso 3 ((MulAut.conj g).subgroupMap A))

private theorem mem_H2Fam_map_conj {M Q H : Subgroup G} {g : G} (hgM : g ∈ M)
    (hgQ : g ∈ Subgroup.normalizer (Q : Set G)) (hH : H ∈ H2Fam M Q) :
    H.map (MulAut.conj g).toMonoidHom ∈ H2Fam M Q := by
  rw [mem_H2Fam_iff] at hH ⊢
  have hM : M.map (MulAut.conj g).toMonoidHom = M :=
    CFSG.Quasithin.H13.Ch4.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hgM)
  have hQ : Q.map (MulAut.conj g).toMonoidHom = Q :=
    CFSG.Quasithin.H13.Ch4.map_conj_eq_of_mem_normalizer hgQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro htop
    apply hH.1
    ext x
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp
        (show MulAut.conj g x ∈ H.map (MulAut.conj g).toMonoidHom from by
          rw [htop]; trivial)
      exact (MulAut.conj g).injective hxy ▸ hy
  · rw [← hQ]
    exact Subgroup.map_mono hH.2.1
  · intro hle
    apply hH.2.2.1
    have hle' : H.map (MulAut.conj g).toMonoidHom ≤ M.map (MulAut.conj g).toMonoidHom := by
      rwa [hM]
    exact (Subgroup.map_le_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).mp hle'
  · have hO : pCoreOf 2 (H.map (MulAut.conj g).toMonoidHom) =
        (pCoreOf 2 H).map (MulAut.conj g).toMonoidHom :=
      CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g) H
    have hC : (Subgroup.centralizer (pCoreOf 2 H : Set G)).map
          (MulAut.conj g).toMonoidHom =
        Subgroup.centralizer ((pCoreOf 2 H).map (MulAut.conj g).toMonoidHom : Set G) :=
      CFSG.Glauberman.map_centralizer_eq_of_equiv (MulAut.conj g) (pCoreOf 2 H)
    rw [hO, ← hC, ← Subgroup.map_inf_eq H (Subgroup.centralizer (pCoreOf 2 H : Set G))
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective]
    exact Subgroup.map_mono hH.2.2.2

private theorem mem_H2StarFam_map_conj {M Q H : Subgroup G} {g : G} (hgM : g ∈ M)
    (hgQ : g ∈ Subgroup.normalizer (Q : Set G)) (hH : H ∈ H2StarFam M Q) :
    H.map (MulAut.conj g).toMonoidHom ∈ H2StarFam M Q := by
  rw [mem_H2StarFam_iff] at hH ⊢
  refine ⟨mem_H2Fam_map_conj hgM hgQ hH.1, fun H' hH' hle => ?_⟩
  have hgM' : g⁻¹ ∈ M := M.inv_mem hgM
  have hgQ' : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) := Subgroup.inv_mem _ hgQ
  have hH'' : H'.map (MulAut.conj g⁻¹).toMonoidHom ∈ H2Fam M Q :=
    mem_H2Fam_map_conj hgM' hgQ' hH'
  have hle' : H ≤ H'.map (MulAut.conj g⁻¹).toMonoidHom := by
    have h := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hle
    rwa [CFSG.Quasithin.H13.Ch4.map_conj_inv_map_conj H g] at h
  have heq : H'.map (MulAut.conj g⁻¹).toMonoidHom = H := hH.2 _ hH'' hle'
  rw [← CFSG.Quasithin.H13.Ch4.map_conj_map_conj_inv H' g, heq]

private theorem mem_calK_map_conj {M Q A : Subgroup G} {g : G} (hgM : g ∈ M)
    (hgQ : g ∈ Subgroup.normalizer (Q : Set G)) (hA : A ∈ calK M Q) :
    A.map (MulAut.conj g).toMonoidHom ∈ calK M Q := by
  obtain ⟨H, hH, hKA, htype⟩ := hA
  refine ⟨H.map (MulAut.conj g).toMonoidHom, mem_H2StarFam_map_conj hgM hgQ hH,
    IsKComp.map_conj hgM hKA, ?_⟩
  rcases htype with h34 | h11
  · exact Or.inl (IsL34Type.of_mulEquiv (threeStarConjEquiv A g) h34)
  · exact Or.inr (IsA11Type.of_mulEquiv (threeStarConjEquiv A g) h11)

theorem map_conj_mem_calKStar {M Q A : Subgroup G} {g : G} (hgM : g ∈ M)
    (hgQ : g ∈ Subgroup.normalizer (Q : Set G)) (hA : A ∈ calKStar M Q) :
    A.map (MulAut.conj g).toMonoidHom ∈ calKStar M Q := by
  refine ⟨mem_calK_map_conj hgM hgQ hA.1, fun J' hJ' hle => ?_⟩
  have hgM' : g⁻¹ ∈ M := M.inv_mem hgM
  have hgQ' : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) := Subgroup.inv_mem _ hgQ
  have hJ'' : J'.map (MulAut.conj g⁻¹).toMonoidHom ∈ calK M Q :=
    mem_calK_map_conj hgM' hgQ' hJ'
  have hAle : A ≤ J'.map (MulAut.conj g⁻¹).toMonoidHom := by
    have h := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hle
    rwa [CFSG.Quasithin.H13.Ch4.map_conj_inv_map_conj A g] at h
  have heq : J'.map (MulAut.conj g⁻¹).toMonoidHom = A := hA.2 _ hJ'' hAle
  rw [← CFSG.Quasithin.H13.Ch4.map_conj_map_conj_inv J' g, heq]

private theorem IsTwoPrimeComponentIn.map_conj_of_mem_normalizer {L H : Subgroup G} {g : G}
    (h : IsTwoPrimeComponentIn L H) (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    IsTwoPrimeComponentIn (L.map (MulAut.conj g).toMonoidHom) H := by
  let φ : MulAut ↥H := Subgroup.normalizerMonoidHom H ⟨g, hg⟩
  have hsub : (L.map (MulAut.conj g).toMonoidHom).subgroupOf H =
      (L.subgroupOf H).map φ.toMonoidHom := by
    ext y
    constructor
    · intro hy
      have hyK : (y : G) ∈ L.map (MulAut.conj g).toMonoidHom := hy
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hyK
      refine Subgroup.mem_map.mpr ⟨⟨k, h.1 hk⟩, Subgroup.mem_subgroupOf.mpr hk, ?_⟩
      apply Subtype.ext
      simpa [φ, MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] using hky
    · intro hy
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hy
      have hkL : (k : G) ∈ L := Subgroup.mem_subgroupOf.mp hk
      refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨(k : G), hkL, ?_⟩)
      have h := congrArg Subtype.val hky
      simpa [φ, MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] using h
  have hH : H.map (MulAut.conj g).toMonoidHom = H :=
    CFSG.Quasithin.H13.Ch4.map_conj_eq_of_mem_normalizer hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hH]
    exact Subgroup.map_mono h.1
  · rw [hsub]
    exact Subgroup.IsSubnormal.map φ.surjective h.2.1
  · let eL : ↥L ≃* ↥(L.map (MulAut.conj g).toMonoidHom) := (MulAut.conj g).subgroupMap L
    let e : ↥(L.map (MulAut.conj g).toMonoidHom) ⧸
        CFSG.pCore 2 ↥(L.map (MulAut.conj g).toMonoidHom) ≃*
        ↥L ⧸ CFSG.pCore 2 ↥L :=
      (QuotientGroup.congr (CFSG.pCore 2 ↥L)
        (CFSG.pCore 2 ↥(L.map (MulAut.conj g).toMonoidHom)) eL
        (CFSG.pCore_map_iso 2 eL)).symm
    exact CFSG.IsQuasisimple.of_mulEquiv e h.2.2.1
  · conv_lhs => rw [h.2.2.2, MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨hyL, hyodd⟩, rfl⟩
      refine ⟨Subgroup.mem_map_of_mem _ hyL, ?_⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] using hyodd
    · rintro ⟨hx, hxodd⟩
      obtain ⟨y, hyL, rfl⟩ := Subgroup.mem_map.mp hx
      refine ⟨y, ⟨hyL, ?_⟩, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] using hxodd

theorem S14Choice.map_conj_J {M N E Q J : Subgroup G} (h : S14Choice G M N E Q J) {t : G}
    (htM : t ∈ M) (htN : t ∈ N) (htQ : t ∈ Subgroup.normalizer (Q : Set G)) :
    S14Choice G M N E Q (J.map (MulAut.conj t).toMonoidHom) := by
  have htK : t ∈ Subgroup.normalizer (kSub 3 M N : Set G) :=
    inf_le_normalizer_kSub 3 M N ⟨htN, htM⟩
  refine { h with
    J_comp := IsTwoPrimeComponentIn.map_conj_of_mem_normalizer h.J_comp htK
    J_star := map_conj_mem_calKStar htM htQ h.J_star }

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
