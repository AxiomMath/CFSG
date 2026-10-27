module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldMember
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldSignalizer
public import CFSG.Quasithin.Background.KGSchurMult2
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTarget
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL34FUUniq
public import CFSG.GroupTheory.SylowNormalizedByPGroup

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

theorem exists_field_mirror_pump_in_normalizer
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h13 : Sol76T13.SolomonThm13Simple)
    (hmult : Quasithin.SchurMult2L3)
    (hglue : L34FieldSignalizerGluing)
    {G : Type} [Group G] [Finite G] {t v : G} {P W : Subgroup G}
    (hset : L34FieldNormalSetting G t P)
    (hmax : FooteLit.GSMirrorMaximal P)
    (hv : orderOf v = 2) (htv : t * v = v * t)
    (hvP : v ∈ coreActionKernel P)
    (hW : ∀ A : Subgroup G, A ≤ P → Open.IsElemAbelian 2 A →
      8 ≤ Nat.card A → GrSLit.wGroup A = W) :
    ∃ Q : Subgroup G,
      L34FieldNormalSetting G v Q ∧ FooteLit.GSMirrorMaximal Q ∧
      Nonempty (P ⧸ Open.fusionZStar P ≃* Q ⧸ Open.fusionZStar Q) ∧
      GSWeakCorr t P v Q ∧
      UnbalancedGS.gsFixedLayer P v ≤ Q ∧
      Q ≤ normalizer (W : Set G) ∧
      UnbalancedGS.gsFixedLayer P v ⊔ oddIn P = P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbase, ht, hPt, hPp, hPn, m, hm, hme, hPL⟩ := hset
  have hsimple : IsSimpleGroup G := hbase.1
  have : IsSimpleGroup G := hsimple
  have hnab : ∃ a b : G, a * b ≠ b * a := hbase.2.1
  have hKP : Assembly.KProper Blueprint.Catalog G := hbase.2.2.1
  have hv1 : v ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hv
    omega
  have hv2 : v * v = 1 := by
    rw [← pow_two, ← hv]
    exact pow_orderOf_eq_one v
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv2
  have hvZ : v ∉ center G := by
    rw [CatLeaf.center_eq_bot_of_simple hnab]
    simp only [mem_bot]
    exact hv1
  have hvC : v ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.mpr htv.symm
  have hvN : v ∈ normalizer (P : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hPt).mp hPn hvC
  obtain ⟨Q, hQv, hQpc, hTQ, -, -, -, -⟩ :=
    FooteLit.kProper_orbit_target_production_of_schreier hS hKP (a := t) ht (J := P) hPt hPp
      (b := v) hv hvZ htv hvN (mem_coreActionKernel.mp hvP).2
  have hcorrW : GrSLit.GSWeakCorr t P v Q :=
    ⟨ht, hv, htv, hPt, hPp, hQv, hQpc, hvN, (mem_coreActionKernel.mp hvP).2, hTQ⟩
  have hreach : FooteLit.GSMirrorReach P Q :=
    FooteLit.GSMirrorReach.tail_corr (FooteLit.GSMirrorReach.refl P) hcorrW
  have hPQ : Nonempty (P ⧸ Open.fusionZStar P ≃* Q ⧸ Open.fusionZStar Q) :=
    hmax Q hreach
  obtain ⟨ePQ⟩ := hPQ
  have hQL : Blueprint.LieModel (Q ⧸ Open.fusionZStar Q) .PSL 3 2 m :=
    LieType.CurtisTits.lieModel_of_mulEquiv ePQ hPL
  have hQmirror : FooteLit.GSMirrorMaximal Q := by
    intro M hM
    obtain ⟨eM⟩ := hmax M (hreach.trans hM)
    exact ⟨ePQ.symm.trans eM⟩
  obtain ⟨hQsol, h3Q⟩ :=
    mem_solomonKStar_of_field_mirror hbase hv ⟨hQv, hQpc⟩ hm hQL hQmirror
  have hQnorm : centralizer ({v} : Set G) ≤ normalizer (Q : Set G) := by
    intro h hh
    have hC : conjugate (centralizer ({v} : Set G)) h = centralizer ({v} : Set G) := by
      rw [CFSG.ComponentClassification.TBLit.L34FU.conjugate_centralizer]
      have hv' : h⁻¹ * v * h = v := by
        rw [mem_centralizer_singleton_iff] at hh
        rw [mul_assoc, ← hh, inv_mul_cancel_left]
      rw [hv']
    have hQh : FooteLit.IsTwoComponentIn (conjugate Q h) (centralizer ({v} : Set G)) := by
      have h' := Sol76.isTwoComponentIn_map (MulAut.conj h⁻¹) ⟨hQv, hQpc⟩
      rwa [show (centralizer ({v} : Set G)).map (MulAut.conj h⁻¹).toMonoidHom =
        conjugate (centralizer ({v} : Set G)) h from rfl, hC] at h'
    have heq : conjugate Q h = Q :=
      Sol76.eq_of_mem_kStarComponents_of_simple h13 hnab hKP
        (mem_centralizer_singleton_iff.mpr rfl)
        (fun _ hn => mem_centralizer_singleton_iff.mp hn) hv
        ⟨⟨hQv, hQpc⟩, hQsol⟩ h3Q
        ⟨hQh, Sol76.conjugate_mem_solomonKStar hQsol h⟩
    exact CFSG.ComponentClassification.TBLit.L34FU.mem_normalizer_of_conjugate_eq heq
  have htC : t ∈ centralizer ({v} : Set G) :=
    mem_centralizer_singleton_iff.mpr htv
  have htN : t ∈ normalizer (Q : Set G) := hQnorm htC
  have hconjQt : conjugate Q t = Q :=
    mem_normalizer_iff_map_conj_eq.mp (inv_mem htN)
  have hDQ : UnbalancedGS.gsFixedLayer P v ≤ Q := by
    have h := hTQ
    rw [hconjQt, sup_idem] at h
    exact h
  have hPq : IsQuasisimple (P ⧸ pPrimeCore 2 P) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 P (centralizer ({t} : Set G)) hPt).mp
      hPp).2.2
  have hDsup : UnbalancedGS.gsFixedLayer P v ⊔ oddIn P = P := by
    have h := gsFixedLayer_sup_map_pPrimeCore hv hPq hvN (mem_coreActionKernel.mp hvP).2
    simpa [oddIn] using h
  have hQn : (Q.subgroupOf (centralizer ({v} : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQv).mpr hQnorm
  have hsetQ : L34FieldNormalSetting G v Q :=
    ⟨hbase, hv, hQv, hQpc, hQn, m, hm, hme, hQL⟩
  have hzv2 : IsPGroup 2 (zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv, pow_one])
  obtain ⟨R, ⟨hRP, hR2, hRodd⟩, hzvR, -⟩ :=
    CFSG.GroupTheory.exists_isSylowIn_normalized_of_isPGroup (p := 2) (K := P) (Q := zpowers v)
      hzv2 (zpowers_le.mpr hvN)
  have hvR : v ∈ normalizer (R : Set G) := hzvR (mem_zpowers v)
  have hRsub : IsPGroup 2 (R.subgroupOf P) :=
    hR2.of_equiv (subgroupOfEquivOfLe hRP).symm
  have hRodd' : ¬ 2 ∣ (R.subgroupOf P).index := by
    rwa [show (R.subgroupOf P).index = R.relIndex P from rfl]
  have h3P : 3 ≤ CFSG.pRank 2 ↥P :=
    three_le_pRank_of_lieModel_fusionZStar (by omega) hPL
  have hrankR : CFSG.pRank 2 ↥R = CFSG.pRank 2 ↥P := by
    have h1 : CFSG.pRank 2 ↥((hRsub.toSylow hRodd' : Sylow 2 ↥P) : Subgroup ↥P) =
        CFSG.pRank 2 ↥P :=
      (CFSG.SectionRank.pRank_sylow (hRsub.toSylow hRodd')).2
    have h2 : CFSG.pRank 2 ↥R = CFSG.pRank 2 ↥(R.subgroupOf P) := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2)
        (Subgroup.subgroupOfEquivOfLe hRP)).symm
    have h3 : CFSG.pRank 2 ↥(R.subgroupOf P) =
        CFSG.pRank 2 ↥((hRsub.toSylow hRodd' : Sylow 2 ↥P) : Subgroup ↥P) :=
      (congrArg (fun S : Subgroup ↥P => CFSG.pRank 2 ↥S)
        (IsPGroup.toSylow_coe hRsub hRodd')).symm
    exact h2.trans (h3.trans h1)
  have h3R : 3 ≤ CFSG.pRank 2 ↥R := by
    rw [hrankR]
    exact h3P
  obtain ⟨E, hER, hE, hE8⟩ := exists_isElemTwo_of_three_le_pRank h3R
  have hoddP : Odd (Nat.card (oddIn P)) := by
    have hcard : Nat.card (oddIn P) = Nat.card (pPrimeCore 2 ↥P) :=
      Subgroup.card_map_of_injective (K := pPrimeCore 2 ↥P) (f := P.subtype)
        P.subtype_injective
    rw [hcard]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (G := ↥P) (p := 2))
  have hbot : R ⊓ oddIn P = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR2
    rw [hn]
    exact (hoddP.coprime_two_left).pow_left n
  have hRcent : R ≤ centralizer ({v} : Set G) := by
    intro r hr
    rw [mem_centralizer_singleton_iff]
    have hvrv : v⁻¹ * r * v ∈ R := by
      have h1 : v * r * v⁻¹ ∈ R := (mem_normalizer_iff.mp hvR r).mp hr
      simpa [hvinv] using h1
    have hc_mem : r⁻¹ * v⁻¹ * r * v ∈ R := by
      have h2 : r⁻¹ * (v⁻¹ * r * v) ∈ R := R.mul_mem (R.inv_mem hr) hvrv
      simpa [mul_assoc] using h2
    have hc_odd : r⁻¹ * v⁻¹ * r * v ∈ oddIn P := by
      simpa [oddIn] using (mem_coreActionKernel.mp hvP).2 r (hRP hr)
    have hc1 : r⁻¹ * v⁻¹ * r * v = 1 := by
      have h3 : r⁻¹ * v⁻¹ * r * v ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact ⟨hc_mem, hc_odd⟩
      exact mem_bot.mp h3
    have hcomm : r * v = v * r := by
      have h : r * (r⁻¹ * v⁻¹ * r * v) * v = v * r := by
        calc r * (r⁻¹ * v⁻¹ * r * v) * v = v⁻¹ * r * (v * v) := by group
          _ = v⁻¹ * r := by rw [hv2, mul_one]
          _ = v * r := by rw [hvinv]
      rwa [hc1, mul_one] at h
    exact hcomm
  have hEP : E ≤ P := hER.trans hRP
  have hEC : E ≤ centralizer ({v} : Set G) := hER.trans hRcent
  obtain ⟨W', -, hW'N, hW'eq⟩ := hglue G v Q hsetQ
  have hWE : GrSLit.wGroup E = W := hW E hEP hE.isElemAbelian hE8
  have hW'E : GrSLit.wGroup E = W' := hW'eq E hEC hE.isElemAbelian hE8
  have hW'W : W' = W := by rw [← hW'E, hWE]
  have hQN : Q ≤ normalizer (W : Set G) := by
    calc Q ≤ normalizer (Q : Set G) := Subgroup.le_normalizer
      _ ≤ normalizer (W' : Set G) := hW'N
      _ = normalizer (W : Set G) := by rw [hW'W]
  exact ⟨Q, hsetQ, hQmirror, ⟨ePQ⟩, hcorrW, hDQ, hQN, hDsup⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
