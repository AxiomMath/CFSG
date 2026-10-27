module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarSingleFacts
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixALeMStepZero
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKStarAut
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKInterSylow
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSixTwoComp
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSixStarEGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenLayerGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenCompGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenOneI
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenTrans
import CFSG.LocalAnalysis.AGL81I.Section3.SL3Arith
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot
import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Two
import CFSG.GroupTheory.SupCommute
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
import CFSG.GroupTheory.CoprimeCentralizerCover
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviPrime
import CFSG.GroupTheory.DihedralQuotientNormalizer
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixIData
import CFSG.ClassicalInvolution.Q3.Q3MFOU4F9
import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
import TauCeti.Algebra.Group.Subgroup.ModularLaw

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

private theorem mem_normalizer_of_starImg_le_centralizer {L W : Subgroup G}
    (hp : p.Prime) (hL : IsPComponentIn p L H) (hWH : W ≤ H)
    (hWL : starImg p H W ≤
      Subgroup.centralizer (starImg p H L : Set (StarGroup p H))) :
    W ≤ Subgroup.normalizer (L : Set G) := by
  intro w hw
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  let wH : ↥H := ⟨w, hWH hw⟩
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  have hwbar : π wH ∈ starImg p H W :=
    Subgroup.mem_map.mpr ⟨wH, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
  have hcomm : ∀ x ∈ starImg p H L, π wH * x = x * π wH := by
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hWL hwbar) x hx).symm
  have hfixmap : (starImg p H L).map (MulAut.conj (π wH)).toMonoidHom = starImg p H L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h := hcomm y hy
      have heq : π wH * y * (π wH)⁻¹ = y := by
        rw [h]; group
      have hfy : (MulAut.conj (π wH)) y = y := by
        simpa [MulAut.conj_apply] using heq
      simpa [hfy] using hy
    · intro hx
      refine ⟨x, hx, ?_⟩
      have h := hcomm x hx
      have heq : π wH * x * (π wH)⁻¹ = x := by
        rw [h]; group
      simpa [MulAut.conj_apply] using heq
  have hstar := starImg_map_conj p H L wH
  rw [hfixmap] at hstar
  exact eq_of_starImg_eq hp (isPComponentIn_conj hL wH.2) hL hstar

private theorem commutator_le_relPPrimeCore_of_starImg_le_centralizer_aux {L W : Subgroup G}
    (hp : p.Prime) (hL : IsPComponentIn p L H) (hWH : W ≤ H)
    (hWL : starImg p H W ≤
      Subgroup.centralizer (starImg p H L : Set (StarGroup p H))) :
    ⁅L, W⁆ ≤ CFSG.Open.relPPrimeCore p H := by
  rw [Subgroup.commutator_le]
  intro l hl w hw
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  let lH : ↥H := ⟨l, hL.1 hl⟩
  let wH : ↥H := ⟨w, hWH hw⟩
  have hwbar : π wH ∈ starImg p H W :=
    Subgroup.mem_map.mpr ⟨wH, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
  have hlbar : π lH ∈ starImg p H L :=
    Subgroup.mem_map.mpr ⟨lH, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have hc := (Subgroup.mem_centralizer_iff.mp (hWL hwbar)) (π lH) hlbar
  have hbar : π ⁅lH, wH⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hc
  have hker : ⁅lH, wH⁆ ∈ (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)).ker :=
    MonoidHom.mem_ker.mpr hbar
  rw [QuotientGroup.ker_mk'] at hker
  rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
    hp H]
  refine Subgroup.mem_map.mpr ⟨⁅lH, wH⁆, hker, ?_⟩
  simp only [Subgroup.coe_subtype, commutatorElement_def]
  rfl

private theorem commutator_le_relPPrimeCore_of_starImg_le_centralizer {L W : Subgroup G}
    (hp : p.Prime) (hL : IsPComponentIn p L H) (hWH : W ≤ H)
    (hWLnorm : W ≤ Subgroup.normalizer (L : Set G))
    (hWL : starImg p H W ≤
      Subgroup.centralizer (starImg p H L : Set (StarGroup p H))) :
    ⁅L, W⁆ ≤ CFSG.Open.relPPrimeCore p L := by
  have hcommH : ⁅L, W⁆ ≤ CFSG.Open.relPPrimeCore p H :=
    commutator_le_relPPrimeCore_of_starImg_le_centralizer_aux hp hL hWH hWL
  have hNL : ⁅L, W⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro l hl w hw
    have hconj : w * l * w⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hWLnorm hw) l).mp hl
    have hconj' : w * l * w⁻¹ * l⁻¹ ∈ L := L.mul_mem hconj (L.inv_mem hl)
    have heq : ⁅l, w⁆ = (w * l * w⁻¹ * l⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact L.inv_mem hconj'
  have hcop : Nat.Coprime p (Nat.card ↥(⁅L, W⁆)) :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      hp H).coprime_dvd_right (Subgroup.card_dvd_of_le hcommH)
  have hsupnorm : (⁅L, W⁆).subgroupOf (L ⊔ W) |>.Normal := CFSG.commutator_normal_in_sup L W
  have hLW : L ⊔ W ≤ Subgroup.normalizer ((⁅L, W⁆ : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.commutator_le_sup L W)).mp hsupnorm
  have hNnormal : ((⁅L, W⁆).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr (le_trans le_sup_left hLW)
  exact CFSG.GroupTheory.le_relPPrimeCore_of_normal_coprime hp hNL hNnormal hcop

theorem TwelveSixKCtx.le_M_of_starImg_le_centralizer
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃) (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {L W : Subgroup G} (hL : IsPComponentIn p L H) (hWV : W ≤ D.V) (hW : Nat.card W = 3)
    (hCW : Subgroup.centralizer (W : Set G) ≤ M)
    (hWL : starImg p H W ≤ Subgroup.centralizer (starImg p H L : Set (StarGroup p H))) :
    L ≤ M := by
  have : Fact p.Prime := ⟨hc.ctx.p_prime⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWH : W ≤ H := hWV.trans ((D.V_le.trans (D.sup_le hc.data)).trans inf_le_left)
  have hWLnorm : W ≤ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_of_starImg_le_centralizer hc.ctx.p_prime hL hWH hWL
  have hcomm : ⁅L, W⁆ ≤ CFSG.Open.relPPrimeCore p L :=
    commutator_le_relPPrimeCore_of_starImg_le_centralizer hc.ctx.p_prime hL hWH hWLnorm hWL
  have hsub : CFSG.Open.IsSubnormal L H :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hL.1).2 hL.2.choose_spec.2.1
  have hleH : CFSG.Open.relPPrimeCore p L ≤ CFSG.Open.relPPrimeCore p H := by
    have hGL := CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal
      hc.ctx.p_prime hsub
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      hc.ctx.p_prime L,
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
        hc.ctx.p_prime H]
    simpa [CFSG.Open.GLAPPrimeCoreOf, CFSG.Open.GLAPPrimeCore] using hGL
  have hO3H : ¬ 3 ∣ Nat.card (CFSG.Open.relPPrimeCore p H) :=
    hc.not_three_dvd_card_relPPrimeCore D
  have hO3L : ¬ 3 ∣ Nat.card (CFSG.Open.relPPrimeCore p L) := fun h =>
    hO3H (h.trans (Subgroup.card_dvd_of_le hleH))
  have hW3 : IsPGroup 3 W := IsPGroup.of_card (n := 1) (by rw [hW]; norm_num)
  have hRN : W ≤ Subgroup.normalizer (CFSG.Open.relPPrimeCore p L : Set G) := fun w hw =>
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi.normalizer_le_normalizer_relPPrimeCore
      p L (hWLnorm hw)
  have hcover := CFSG.GroupTheory.inf_centralizer_sup_eq_of_commutator_le
    (p := 3) (X := L) (N := CFSG.Open.relPPrimeCore p L) (R := W)
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le L)
    hWLnorm hRN hW3 hO3L hcomm
  have hNM : CFSG.Open.relPPrimeCore p L ≤ M :=
    hleH.trans (relPPrimeCore_le_M_of_twelveCtx hc.ctx)
  calc L = L ⊓ Subgroup.centralizer (W : Set G) ⊔ CFSG.Open.relPPrimeCore p L := hcover.symm
    _ ≤ M := sup_le (inf_le_right.trans hCW) hNM

private theorem eq_pair_of_ncard_le_two {L I : Subgroup G}
    (hLI : L ≠ I) (hL : IsPComponentIn p L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn p I H) (hIM : ¬ I ≤ M)
    (hcard : {J : Subgroup G | IsPComponentIn p J H ∧ ¬ J ≤ M}.ncard ≤ 2) :
    {J : Subgroup G | IsPComponentIn p J H ∧ ¬ J ≤ M} = {L, I} := by
  refine (Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)).symm
  · intro J hJ
    rcases hJ with rfl | rfl
    · exact ⟨hL, hLM⟩
    · exact ⟨hI, hIM⟩
  · rw [Set.ncard_pair hLI]
    exact hcard

private theorem map_conj_eq_left_or_right_of_pair
    {L I J : Subgroup G} (hS : {K : Subgroup G | IsPComponentIn p K H ∧ ¬ K ≤ M} = {L, I})
    (hJ : IsPComponentIn p J H) (hJM : ¬ J ≤ M) {t : G} (htH : t ∈ H) (htM : t ∈ M) :
    J.map (MulAut.conj t).toMonoidHom = L ∨ J.map (MulAut.conj t).toMonoidHom = I := by
  have hmem : J.map (MulAut.conj t).toMonoidHom ∈
      {K : Subgroup G | IsPComponentIn p K H ∧ ¬ K ≤ M} := by
    refine ⟨isPComponentIn_conj hJ htH, ?_⟩
    intro hle
    apply hJM
    have hconj : M.map (MulAut.conj t⁻¹).toMonoidHom = M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (M.inv_mem htM))
    have hJeq : J = (J.map (MulAut.conj t).toMonoidHom).map
        (MulAut.conj t⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      have hid : (MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
          MonoidHom.id G := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [hid, Subgroup.map_id]
    rw [hJeq]
    exact (Subgroup.map_mono hle).trans_eq hconj
  rw [hS] at hmem
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem

private theorem mem_normalizer_of_odd_orderOf_of_Kconjugates
    {K L I : Subgroup G} (hKleH : K ≤ H) (hKleM : K ≤ M)
    (hLI : L ≠ I) (hL : IsPComponentIn p L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn p I H) (hIM : ¬ I ≤ M)
    (hS : {J : Subgroup G | IsPComponentIn p J H ∧ ¬ J ≤ M} = {L, I})
    {v : G} (hvK : v ∈ K) (hodd : Odd (orderOf v)) :
    v ∈ Subgroup.normalizer (L : Set G) := by
  by_cases hv : v ∈ Subgroup.normalizer (L : Set G)
  · exact hv
  have hvH : v ∈ H := hKleH hvK
  have hvM : v ∈ M := hKleM hvK
  have hmemS : ∀ J : Subgroup G, IsPComponentIn p J H → ¬ J ≤ M →
      J.map (MulAut.conj v).toMonoidHom ∈
        {J' : Subgroup G | IsPComponentIn p J' H ∧ ¬ J' ≤ M} := by
    intro J hJ hJM
    rcases map_conj_eq_left_or_right_of_pair hS hJ hJM hvH hvM with h | h
    · rw [h]; exact ⟨hL, hLM⟩
    · rw [h]; exact ⟨hI, hIM⟩
  have hLv_mem := hmemS L hL hLM
  have hIv_mem := hmemS I hI hIM
  rw [hS] at hLv_mem hIv_mem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hLv_mem hIv_mem
  have hLv : L.map (MulAut.conj v).toMonoidHom = I := by
    rcases hLv_mem with h | h
    · exfalso
      exact hv (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
    · exact h
  have hIv : I.map (MulAut.conj v).toMonoidHom = L := by
    rcases hIv_mem with h | h
    · exact h
    · exfalso
      exact hLI ((Subgroup.map_injective (MulAut.conj v).injective) (hLv.trans h.symm))
  have hLv2 : L.map (MulAut.conj (v ^ 2)).toMonoidHom = L := by
    rw [pow_two, map_mul]
    rw [show (MulAut.conj v * MulAut.conj v : MulAut G).toMonoidHom =
      (MulAut.conj v).toMonoidHom.comp (MulAut.conj v).toMonoidHom from rfl]
    rw [← Subgroup.map_map, hLv, hIv]
  have hv2 : v ^ 2 ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hLv2
  obtain ⟨m, hm⟩ := hodd
  have hvpow : v = (v ^ 2) ^ (m + 1) := by
    rw [← pow_mul]
    have h2 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    rw [h2, pow_succ, ← hm, pow_orderOf_eq_one, one_mul]
  rw [hvpow]
  exact Subgroup.pow_mem _ hv2 (m + 1)

private theorem V_le_normalizer_of_pair
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn p L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn p I H) (hIM : ¬ I ≤ M)
    (hS : {J : Subgroup G | IsPComponentIn p J H ∧ ¬ J ≤ M} = {L, I}) :
    D.V ≤ Subgroup.normalizer (L : Set G) := by
  intro v hv
  have hvK : v ∈ H ⊓ M := (D.V_le.trans (D.sup_le hc.data)) hv
  have hodd : Odd (orderOf v) :=
    Odd.of_dvd_nat (by norm_num) (orderOf_dvd_of_pow_eq_one (D.cfg.elem.2 v hv))
  exact mem_normalizer_of_odd_orderOf_of_Kconjugates inf_le_left inf_le_right
    hLI hL hLM hI hIM hS hvK hodd

private noncomputable def centralizingInV (p : ℕ) (H V J : Subgroup G) : Subgroup G :=
  (Subgroup.comap (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
    (Subgroup.centralizer (starImg p H J : Set (StarGroup p H)))).map H.subtype ⊓ V

omit [Finite G] in
private theorem mem_centralizingInV_iff {p : ℕ} {H V J : Subgroup G} {v : G} (hvH : v ∈ H) :
    v ∈ centralizingInV p H V J ↔ v ∈ V ∧
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨v, hvH⟩) ∈
        Subgroup.centralizer (starImg p H J : Set (StarGroup p H)) := by
  constructor
  · intro hv
    obtain ⟨x, hx, hxv⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hv).1
    have hvV : v ∈ V := (Subgroup.mem_inf.mp hv).2
    have hx' : x = ⟨v, hvH⟩ := Subtype.ext hxv
    exact ⟨hvV, hx' ▸ (Subgroup.mem_comap.mp hx)⟩
  · rintro ⟨hvV, hcent⟩
    refine Subgroup.mem_inf.mpr ⟨?_, hvV⟩
    exact Subgroup.mem_map.mpr ⟨⟨v, hvH⟩, Subgroup.mem_comap.mpr hcent, rfl⟩

private theorem starImg_mem_normalizer_of_mem_normalizer {p : ℕ} {H J : Subgroup G} {t : G}
    (htH : t ∈ H) (hJ : t ∈ Subgroup.normalizer (J : Set G)) :
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨t, htH⟩) ∈
      Subgroup.normalizer (starImg p H J : Set (StarGroup p H)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hJmap : J.map (MulAut.conj t).toMonoidHom = J :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hJ
  have h := starImg_map_conj p H J ⟨t, htH⟩
  rw [hJmap] at h
  exact h.symm

private theorem map_conj_mem_centralizingInV_of_normalizer {p : ℕ} {H V J : Subgroup G} {t v : G}
    (hVH : V ≤ H) (htH : t ∈ H) (hV : t ∈ Subgroup.normalizer (V : Set G))
    (hJ : t ∈ Subgroup.normalizer (J : Set G))
    (hv : v ∈ centralizingInV p H V J) :
    t * v * t⁻¹ ∈ centralizingInV p H V J := by
  have hvV : v ∈ V := (Subgroup.mem_inf.mp hv).2
  have hvH : v ∈ H := hVH hvV
  have hvcent := (mem_centralizingInV_iff hvH).mp hv |>.2
  have htvtH : t * v * t⁻¹ ∈ H := H.mul_mem (H.mul_mem htH hvH) (H.inv_mem htH)
  have htvtV : t * v * t⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp hV v).mp hvV
  refine (mem_centralizingInV_iff htvtH).mpr ⟨htvtV, ?_⟩
  have htN : (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨t, htH⟩) ∈
      Subgroup.normalizer (starImg p H J : Set (StarGroup p H)) :=
    starImg_mem_normalizer_of_mem_normalizer htH hJ
  have hmap : (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
      ⟨t * v * t⁻¹, htvtH⟩) =
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨t, htH⟩) *
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨v, hvH⟩) *
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨t, htH⟩)⁻¹ := by
    have harg : (⟨t * v * t⁻¹, htvtH⟩ : ↥H) =
        ⟨t, htH⟩ * ⟨v, hvH⟩ * ⟨t, htH⟩⁻¹ := Subtype.ext rfl
    rw [harg, map_mul, map_mul, map_inv]
  rw [hmap]
  intro y hy
  have hty : (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨t, htH⟩)⁻¹ *
      y * (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨t, htH⟩) ∈
      starImg p H J := by
    simpa using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (starImg p H J : Set (StarGroup p H))).inv_mem htN) y).mp hy
  have hcomm := (Subgroup.mem_centralizer_iff.mp hvcent) _ hty
  have hconj := congrArg (fun z =>
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨t, htH⟩) * z *
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨t, htH⟩)⁻¹) hcomm
  simpa [mul_assoc] using hconj

private noncomputable def actionOnStar (p : ℕ) (H V J : Subgroup G) (hVH : V ≤ H)
    (hVJ : V ≤ Subgroup.normalizer (J : Set G)) : V →* MulAut ↥(starImg p H J) :=
  let N : Subgroup (StarGroup p H) :=
    Subgroup.normalizer (starImg p H J : Set (StarGroup p H))
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  let ψ : V →* N := (π.comp (Subgroup.inclusion hVH)).codRestrict N fun v =>
    starImg_mem_normalizer_of_mem_normalizer (hVH v.2) (hVJ v.2)
  (starImg p H J).normalizerMonoidHom.comp ψ

private theorem actionOnStar_apply (p : ℕ) (H V J : Subgroup G) (hVH : V ≤ H)
    (hVJ : V ≤ Subgroup.normalizer (J : Set G)) (v : V) (x : ↥(starImg p H J)) :
    ((actionOnStar p H V J hVH hVJ v) x : StarGroup p H) =
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨(v : G), hVH v.2⟩) * x *
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨(v : G), hVH v.2⟩)⁻¹ := by
  let N : Subgroup (StarGroup p H) :=
    Subgroup.normalizer (starImg p H J : Set (StarGroup p H))
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  let ψ : V →* N := (π.comp (Subgroup.inclusion hVH)).codRestrict N fun v =>
    starImg_mem_normalizer_of_mem_normalizer (hVH v.2) (hVJ v.2)
  change (((starImg p H J).normalizerMonoidHom (ψ v)) x : StarGroup p H) = _
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rfl

private theorem centralizingInV_eq_ker_map (p : ℕ) (H V J : Subgroup G) (hVH : V ≤ H)
    (hVJ : V ≤ Subgroup.normalizer (J : Set G)) :
    centralizingInV p H V J =
      (actionOnStar p H V J hVH hVJ).ker.map V.subtype := by
  ext v
  constructor
  · intro hv
    have hvV : v ∈ V := (Subgroup.mem_inf.mp hv).2
    have hvH : v ∈ H := hVH hvV
    have hvcent := (mem_centralizingInV_iff hvH).mp hv |>.2
    refine Subgroup.mem_map.mpr ⟨⟨v, hvV⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    ext x
    have hx := (Subgroup.mem_centralizer_iff.mp hvcent) (x : StarGroup p H) x.2
    calc (((actionOnStar p H V J hVH hVJ ⟨v, hvV⟩) x : StarGroup p H))
        = (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨v, hvH⟩) * x *
            (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨v, hvH⟩)⁻¹ :=
          actionOnStar_apply p H V J hVH hVJ ⟨v, hvV⟩ x
      _ = x := by rw [← hx]; group
      _ = (((1 : MulAut ↥(starImg p H J)) x) : StarGroup p H) := by simp
  · rintro ⟨w, hw, rfl⟩
    have hwV : (w : G) ∈ V := w.2
    have hwH : (w : G) ∈ H := hVH hwV
    have hker : actionOnStar p H V J hVH hVJ w = 1 := MonoidHom.mem_ker.mp hw
    refine (mem_centralizingInV_iff hwH).mpr ⟨hwV, ?_⟩
    intro x hx
    have h := congrArg (fun f : MulAut ↥(starImg p H J) => (f ⟨x, hx⟩ : StarGroup p H)) hker
    simp only [MulAut.one_apply] at h
    rw [actionOnStar_apply p H V J hVH hVJ w ⟨x, hx⟩] at h
    have h' : (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨(w : G), hwH⟩) *
        x * (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨(w : G), hwH⟩)⁻¹ = x := by
      simpa using h
    have h2 := congrArg (fun z => z * (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
      ⟨(w : G), hwH⟩)) h'
    simpa [mul_assoc] using h2.symm

private theorem centralizingInV_ne_bot_of_isPSLType {V I : Subgroup G} (hVH : V ≤ H)
    (hVI : V ≤ Subgroup.normalizer (I : Set G)) (hE : IsElemAbelian 3 V)
    (hVcard : Nat.card V = 27)
    (hL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H I)) :
    centralizingInV 3 H V I ≠ ⊥ := by
  intro hbot
  let φ := actionOnStar 3 H V I hVH hVI
  have hker : φ.ker = ⊥ := by
    refine (Subgroup.map_eq_bot_iff_of_injective φ.ker (f := V.subtype)
      V.subtype_injective).mp ?_
    rw [← centralizingInV_eq_ker_map 3 H V I hVH hVI]
    exact hbot
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  have hle := CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num) φ hinj
  have hEtop : IsElemAbelian 3 (⊤ : Subgroup V) := by
    simpa [Subgroup.subgroupOf_self] using hE.subgroupOf V
  have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup V) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hEtop
      (k := 3) (by rw [Subgroup.card_top, hVcard]; norm_num)
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥(starImg 3 H I))) ≤ 2 :=
    pRank_three_mulAut_le_two_of_kStarType (Or.inl hL2)
  omega

private theorem mulAut_eq_one_of_cube_eq_one_of_three_free {X : Type} [Group X] [Finite X]
    (hcard : ¬ 3 ∣ Nat.card (MulAut X)) {a : MulAut X} (ha : a ^ 3 = 1) : a = 1 := by
  have hdvd3 : orderOf a ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr ha
  have hdvdCard : orderOf a ∣ Nat.card (MulAut X) := orderOf_dvd_natCard a
  have hcop3 : Nat.Coprime 3 (Nat.card (MulAut X)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hcard
  have hcop : Nat.Coprime (orderOf a) (Nat.card (MulAut X)) :=
    hcop3.coprime_dvd_left hdvd3
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvdCard)

private theorem mem_centralizer_of_cube_eq_one_of_three_free {p : ℕ} {H : Subgroup G}
    {K : Subgroup (StarGroup p H)} (hcard : ¬ 3 ∣ Nat.card (MulAut ↥K))
    {v : G} (hvH : v ∈ H) (hv3 : v ^ 3 = 1)
    (hN : (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨v, hvH⟩) ∈
      Subgroup.normalizer (K : Set (StarGroup p H))) :
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨v, hvH⟩) ∈
      Subgroup.centralizer (K : Set (StarGroup p H)) := by
  let x : ↥(Subgroup.normalizer (K : Set (StarGroup p H))) :=
    ⟨QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨v, hvH⟩, hN⟩
  let a : MulAut ↥K := K.normalizerMonoidHom x
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    change (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨v, hvH⟩) ^ 3 = 1
    rw [← map_pow]
    have hcube : (⟨v, hvH⟩ : ↥H) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hv3
    rw [hcube, map_one]
  have ha3 : a ^ 3 = 1 := by
    rw [show a = K.normalizerMonoidHom x from rfl, ← map_pow, hx3, map_one]
  have ha1 : a = 1 := mulAut_eq_one_of_cube_eq_one_of_three_free hcard ha3
  intro y hy
  have happ : (K.normalizerMonoidHom x) ⟨y, hy⟩ = ⟨y, hy⟩ := by
    change a ⟨y, hy⟩ = ⟨y, hy⟩
    rw [ha1]
    rfl
  have hval := congrArg (fun z : ↥K => (z : StarGroup p H)) happ
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe K x ⟨y, hy⟩] at hval
  have h2 := congrArg (fun z => z * x.1) hval
  simpa [mul_assoc, x] using h2.symm

private theorem false_of_pair_of_p_ne_three
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M p E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : p ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M) (hp3 : p ≠ 3)
    (hpair : NineSixMoreoverPairFive) (hSz : KFactSz32MulAutThreeFree)
    {L I : Subgroup G} (hL : IsPComponentIn p L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn p I H) (hIM : ¬ I ≤ M) (hLI : L ≠ I) :
    False := by
  have hS : {J : Subgroup G | IsPComponentIn p J H ∧ ¬ J ≤ M} = {L, I} :=
    eq_pair_of_ncard_le_two hLI hL hLM hI hIM
      (nineSixTwoComp_holds G M E H E p h hH2 hpσ
        (fun hle => hLM (le_pLayerIn hL |>.trans hle)))
  obtain ⟨-, -, hIiso⟩ := hpair G M E H E p h hH2 hpσ hp3 L I hL hLM hI hIM hLI
  have hS' : {J : Subgroup G | IsPComponentIn p J H ∧ ¬ J ≤ M} = {I, L} := by
    rw [Set.pair_comm]
    exact hS
  have hVI : D.V ≤ Subgroup.normalizer (I : Set G) :=
    V_le_normalizer_of_pair (L := I) (I := L) hc D (Ne.symm hLI) hI hIM hL hLM hS'
  have hVH : D.V ≤ H := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_left
  have hW1V : D.W₁ ≤ D.V := by
    rw [D.cfg.join]
    exact le_sup_left.trans le_sup_left
  have hIcard : ¬ 3 ∣ Nat.card (MulAut ↥(starImg p H I)) := hSz _ hIiso
  have hcent : ∀ (v : G) (hv : v ∈ D.V),
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨v, hVH hv⟩) ∈
        Subgroup.centralizer (starImg p H I : Set (StarGroup p H)) := by
    intro v hv
    exact mem_centralizer_of_cube_eq_one_of_three_free hIcard (hVH hv) (D.cfg.elem.2 v hv)
      (starImg_mem_normalizer_of_mem_normalizer (hVH hv) (hVI hv))
  have hW1C : D.W₁ ≤ centralizingInV p H D.V I := by
    intro w hw
    have hwV : w ∈ D.V := hW1V hw
    refine (mem_centralizingInV_iff (hVH hwV)).mpr ⟨hwV, hcent w hwV⟩
  have hWL : starImg p H D.W₁ ≤
      Subgroup.centralizer (starImg p H I : Set (StarGroup p H)) := by
    intro x hx
    obtain ⟨wH, hwH, rfl⟩ := Subgroup.mem_map.mp hx
    have hw : (wH : G) ∈ D.W₁ := Subgroup.mem_subgroupOf.mp hwH
    have hmem := (mem_centralizingInV_iff (hVH (hW1V hw))).mp (hW1C hw) |>.2
    simpa using hmem
  exact hIM (hc.le_M_of_starImg_le_centralizer D hI hW1V D.cfg.card₁
    (D.centralizer_le₁ hc) hWL)

omit [Finite G] in
private theorem starImg_sup' {p : ℕ} {H A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H) :
    starImg p H (A ⊔ B) = starImg p H A ⊔ starImg p H B := by
  unfold starImg
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

omit [Finite G] in
private theorem not_dvd_card_starImg_of_not_dvd {p : ℕ} {X : Subgroup G} (hXH : X ≤ H)
    (hX3 : ¬ 3 ∣ Nat.card X) : ¬ 3 ∣ Nat.card (starImg p H X) := by
  intro hdvd
  apply hX3
  have hdvd1 : Nat.card (starImg p H X) ∣ Nat.card (X.subgroupOf H) := by
    unfold starImg
    exact Subgroup.card_map_dvd _ _
  have hcard : Nat.card (X.subgroupOf H) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
  exact hdvd.trans (hcard ▸ hdvd1)

private theorem center_eq_bot_of_isComponent_of_center_layer_map_le {p : ℕ}
    {K : Subgroup (StarGroup p H)} (hK : CFSG.IsComponent K)
    (hZlayer : (Subgroup.center (CFSG.layer (StarGroup p H))).map
      (CFSG.layer (StarGroup p H)).subtype ≤ CFSG.pCore p (StarGroup p H))
    (hRbot : CFSG.pCore p (StarGroup p H) = ⊥) : center ↥K = ⊥ := by
  have hmap : (Subgroup.center ↥K).map K.subtype = ⊥ := by
    refine le_bot_iff.mp ?_
    exact (CFSG.LocalCores.center_component_le_center_layer hK).trans
      (hZlayer.trans (le_of_eq hRbot))
  exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥K)
    K.subtype_injective).mp hmap

private theorem center_starImg_eq_bot_of_pair
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M p E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : p ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    (hXM : xSub p M H ≤ M) (hp3 : p = 3)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn p L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn p I H) (hIM : ¬ I ≤ M) :
    center ↥(starImg p H L) = ⊥ ∧ center ↥(starImg p H I) = ⊥ := by
  have : Fact p.Prime := ⟨hc.ctx.p_prime⟩
  have hnotlayer : ¬ pLayerIn p H ≤ M := fun hle => hLM ((le_pLayerIn hL).trans hle)
  have hS : {J : Subgroup G | IsPComponentIn p J H ∧ ¬ J ≤ M} = {L, I} :=
    eq_pair_of_ncard_le_two hLI hL hLM hI hIM
      (nineSixTwoComp_holds G M E H E p h hH2 hpσ hnotlayer)
  have hkSub : kSub p M H = L ⊔ I := by
    unfold kSub
    rw [if_neg hnotlayer, hS]
    simp [sSup_insert, sSup_singleton]
  have hkStar : kStar p M H = starImg p H L ⊔ starImg p H I := by
    rw [kStar_eq_starImg, hkSub, starImg_sup' hL.1 hI.1]
  have hKleLayer : kStar p M H ≤ CFSG.layer (StarGroup p H) := by
    rw [hkStar]
    exact sup_le (CFSG.LocalCores.component_le_layer (isComponent_starImg hL))
      (CFSG.LocalCores.component_le_layer (isComponent_starImg hI))
  have hRle : CFSG.pCore p (StarGroup p H) ≤ starImg p H (xSub p M H) := by
    rw [starImg_xSub p M H]
    exact (CFSG.WholeGroup.pCore_le_centralizer_layer (G := StarGroup p H) p).trans
      (Subgroup.centralizer_le hKleLayer)
  have hX3 : ¬ 3 ∣ Nat.card (xSub p M H) := hc.not_three_dvd_card_xSub D hXM
  have hXstar3 : ¬ 3 ∣ Nat.card (starImg p H (xSub p M H)) :=
    not_dvd_card_starImg_of_not_dvd (xSub_le_H p M H) hX3
  have hRbot : CFSG.pCore p (StarGroup p H) = ⊥ := by
    rcases (CFSG.pCore_isPGroup (p := p) (G := StarGroup p H)).card_eq_or_dvd with h1 | hdvd
    · exact Subgroup.card_eq_one.mp h1
    · exact absurd (hp3 ▸ hdvd.trans (Subgroup.card_dvd_of_le hRle)) hXstar3
  have hZlayer : (Subgroup.center (CFSG.layer (StarGroup p H))).map
      (CFSG.layer (StarGroup p H)).subtype ≤ CFSG.pCore p (StarGroup p H) :=
    CFSG.WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot p
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup hc.ctx.p_prime)
  exact ⟨center_eq_bot_of_isComponent_of_center_layer_map_le (isComponent_starImg hL)
      hZlayer hRbot,
    center_eq_bot_of_isComponent_of_center_layer_map_le (isComponent_starImg hI) hZlayer hRbot⟩

private theorem inf_eq_bot_of_distinct_components {X : Type} [Group X] [Finite X]
    {K L : Subgroup X} (hK : CFSG.IsComponent K) (hL : CFSG.IsComponent L)
    (hne : K ≠ L) (hZK : center K = ⊥) : K ⊓ L = ⊥ := by
  have hcomm := (CFSG.LocalCores.distinct_components_commute hK hL).resolve_left hne
  refine le_bot_iff.mp ?_
  intro x hx
  have hcommI : ⁅L, K⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hcomm
  have hleI : L ≤ Subgroup.centralizer (K : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommI
  have hleK : K ≤ Subgroup.centralizer (L : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hxZK : (⟨x, hx.1⟩ : ↥K) ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hleI hx.2) y y.2
  have hxZL : (⟨x, hx.2⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hleK hx.1) y y.2
  rw [hZK] at hxZK
  have hx1 : x = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hxZK)
  rw [hx1]
  exact Subgroup.mem_bot.mpr rfl

private theorem pRank_add_le_three_of_pair
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M p E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : p ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn p L H)
    (hI : IsPComponentIn p I H) (hZL : center ↥(starImg p H L) = ⊥) :
    CFSG.Open.pRank p (starImg p H L) + CFSG.Open.pRank p (starImg p H I) ≤ 3 := by
  have : Fact p.Prime := ⟨hc.ctx.p_prime⟩
  have hLc : CFSG.IsComponent (starImg p H L) := isComponent_starImg hL
  have hIc : CFSG.IsComponent (starImg p H I) := isComponent_starImg hI
  have hne : starImg p H L ≠ starImg p H I := fun heq =>
    hLI (eq_of_starImg_eq hc.ctx.p_prime hL hI heq)
  have hcomm := (CFSG.LocalCores.distinct_components_commute hLc hIc).resolve_left hne
  have hcomm' : ∀ x ∈ starImg p H L, ∀ y ∈ starImg p H I, x * y = y * x :=
    fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx) y hy).symm
  have hinf : starImg p H L ⊓ starImg p H I = ⊥ :=
    inf_eq_bot_of_distinct_components hLc hIc hne hZL
  have hcop : Nat.Coprime p (Nat.card ↥(starImg p H L ⊓ starImg p H I)) := by
    rw [hinf, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have hsum := CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime hc.ctx.p_prime hcomm' hcop
  have hmono : CFSG.Open.pRank p (starImg p H L ⊔ starImg p H I) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (StarGroup p H)) :=
    CFSG.SectionRank.pRank_mono hc.ctx.p_prime.one_lt le_top
  have h3 := h.pRank_star_le_three hH2 hpσ
  omega

private theorem isPSLType_of_pRank_one_three
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    (h35r : KFactThreeFiveRankOne) {J : Subgroup G} (hJ : IsPComponentIn 3 J H)
    (hJM : ¬ J ≤ M) (hrank : CFSG.Open.pRank 3 (starImg 3 H J) = 1) :
    IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJc : CFSG.IsComponent (starImg 3 H J) := isComponent_starImg hJ
  have hJM' : ¬ starImg 3 H J ≤ starImg 3 H M := fun hle =>
    hJM ((h.le_iff_starImg_le hJ.1).mpr hle)
  exact h35r (StarGroup 3 H) h.isKGroup_star
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup Nat.prime_three)
    (h.pRank_star_le_three hH2 hpσ) (starImg 3 H J) (starImg 3 H E) hJc hrank
    h.isElemAbelian_starImg_E_gen h.card_starImg_E_gen
    (h.starImg_E_le_normalizer_gen hJc hJM')
    (fun hle => hJM' (hle.trans h.rankThreeGamma_starImg_E_le_gen))

private theorem one_le_pRank_of_starImg_of_pComponent
    {J : Subgroup G} (hJ : IsPComponentIn 3 J H) :
    1 ≤ CFSG.Open.pRank 3 (starImg 3 H J) := by
  have hJc : CFSG.IsComponent (starImg 3 H J) := isComponent_starImg hJ
  have hdvd : 3 ∣ Nat.card (starImg 3 H J) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card (p := 3) Nat.prime_three
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup
        (H := H) Nat.prime_three) hJc
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  exact CFSG.one_le_pRank_of_dvd_card Nat.prime_three hdvd

omit [Finite G] in
private theorem eq_one_or_eq_or_eq_inv_of_mem_of_card_three {W : Subgroup G}
    (hW : Nat.card W = 3) {w : G} (hwW : w ∈ W) (hw1 : w ≠ 1) {x : G} (hxW : x ∈ W) :
    x = 1 ∨ x = w ∨ x = w⁻¹ := by
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  have hordw : orderOf w = 3 := by
    have hdvd := Subgroup.orderOf_dvd_natCard W hwW
    rw [hW] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · exact h
  have hwinv : w⁻¹ ≠ w := by
    intro h
    have h2 : w ^ 2 = 1 := by
      rw [pow_two]
      calc w * w = w⁻¹ * w := by rw [h]
        _ = 1 := inv_mul_cancel w
    have hdvd : orderOf w ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [hordw] at hdvd
    norm_num at hdvd
  have hset : ({1, w, w⁻¹} : Set G) = (W : Set G) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite (W : Set G))
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact W.one_mem
      · exact hwW
      · exact W.inv_mem hwW
    · have h1 : (W : Set G).ncard = 3 := by
        rw [← Nat.card_coe_set_eq]
        exact hW
      have h2 : ({1, w, w⁻¹} : Set G).ncard = 3 := by
        rw [Set.ncard_eq_three]
        refine ⟨1, w, w⁻¹, hw1.symm, ?_, hwinv.symm, rfl⟩
        intro h
        exact hw1 (by simpa using (congrArg Inv.inv h).symm)
      omega
  have hx : x ∈ ({1, w, w⁻¹} : Set G) := by
    rw [hset]
    exact hxW
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx

omit [Finite G] in
private theorem conj_mul_eq_mul_inv_of_fixes_of_inverts {F J : Subgroup G} {t f j : G}
    (hf : f ∈ F) (hj : j ∈ J)
    (hfix : ∀ x ∈ F, t * x * t⁻¹ = x)
    (hinv : ∀ x ∈ J, t * x * t⁻¹ = x⁻¹) :
    t * (f * j) * t⁻¹ = f * j⁻¹ := by
  calc t * (f * j) * t⁻¹ = (t * f * t⁻¹) * (t * j * t⁻¹) := by group
    _ = f * j⁻¹ := by rw [hfix f hf, hinv j hj]

omit [Finite G] in
private theorem mem_F_of_conj_eq_of_mul {F J : Subgroup G} {t f j d : G}
    (hf : f ∈ F) (hj : j ∈ J)
    (hfix : ∀ x ∈ F, t * x * t⁻¹ = x)
    (hinv : ∀ x ∈ J, t * x * t⁻¹ = x⁻¹)
    (hJ3 : ∀ x ∈ J, x ^ 3 = 1)
    (hd : f * j = d) (hfixd : t * d * t⁻¹ = d) : d ∈ F := by
  have hα : t * d * t⁻¹ = f * j⁻¹ := by
    rw [← hd]
    exact conj_mul_eq_mul_inv_of_fixes_of_inverts hf hj hfix hinv
  rw [hα] at hfixd
  have hfj : f * j⁻¹ = f * j := hfixd.trans hd.symm
  have hjinv : j⁻¹ = j := mul_left_cancel hfj
  have hj2 : j ^ 2 = 1 := by
    rw [pow_two]
    calc j * j = j⁻¹ * j := by rw [hjinv]
      _ = 1 := inv_mul_cancel j
  have hj1 : j = 1 := by
    have h := hJ3 j hj
    calc j = j ^ 3 := by rw [show (3 : ℕ) = 1 + 2 by norm_num, pow_add, pow_one, hj2,
          mul_one]
      _ = 1 := h
  rw [hj1, mul_one] at hd
  rw [← hd]
  exact hf

omit [Finite G] in
private theorem mem_J_of_conj_eq_inv_of_mul {F J : Subgroup G} {t f j d : G}
    (hf : f ∈ F) (hj : j ∈ J)
    (hcomm : ∀ f ∈ F, ∀ j ∈ J, f * j = j * f)
    (hfix : ∀ x ∈ F, t * x * t⁻¹ = x)
    (hinv : ∀ x ∈ J, t * x * t⁻¹ = x⁻¹)
    (hF3 : ∀ x ∈ F, x ^ 3 = 1)
    (hd : f * j = d) (hinvd : t * d * t⁻¹ = d⁻¹) : d ∈ J := by
  have hα : t * d * t⁻¹ = f * j⁻¹ := by
    rw [← hd]
    exact conj_mul_eq_mul_inv_of_fixes_of_inverts hf hj hfix hinv
  have hfj : f * j⁻¹ = d⁻¹ := by
    rw [← hα]
    exact hinvd
  have hfinv : f⁻¹ = f := by
    have hd' : f * j⁻¹ = (f * j)⁻¹ := by
      rw [hfj, hd]
    have hd'' : (f * j)⁻¹ = f⁻¹ * j⁻¹ := by
      calc (f * j)⁻¹ = (j * f)⁻¹ := by rw [hcomm f hf j hj]
        _ = f⁻¹ * j⁻¹ := mul_inv_rev j f
    rw [hd''] at hd'
    exact (mul_right_cancel hd').symm
  have hf2 : f ^ 2 = 1 := by
    rw [pow_two]
    calc f * f = f⁻¹ * f := by rw [hfinv]
      _ = 1 := inv_mul_cancel f
  have hf1 : f = 1 := by
    have h := hF3 f hf
    calc f = f ^ 3 := by rw [show (3 : ℕ) = 1 + 2 by norm_num, pow_add, pow_one, hf2,
          mul_one]
      _ = 1 := h
  rw [hf1, one_mul] at hd
  rw [← hd]
  exact hj

private theorem le_fixed_or_eq_inverted {V F J D : Subgroup G} {t : G}
    (hV : V = F ⊔ J) (hcomm : ∀ f ∈ F, ∀ j ∈ J, f * j = j * f)
    (hF3 : ∀ f ∈ F, f ^ 3 = 1) (hJ3 : ∀ j ∈ J, j ^ 3 = 1)
    (hfix : ∀ x ∈ F, t * x * t⁻¹ = x)
    (hinv : ∀ x ∈ J, t * x * t⁻¹ = x⁻¹)
    (hDV : D ≤ V) (hDcard : Nat.card D = 3)
    (hDt : ∀ x ∈ D, t * x * t⁻¹ ∈ D) : D ≤ F ∨ D ≤ J := by
  by_cases hDF : D ≤ F
  · exact Or.inl hDF
  right
  obtain ⟨d, hdD, hdF⟩ := Set.not_subset.mp hDF
  have hd1 : d ≠ 1 := fun h => hdF (h ▸ F.one_mem)
  have hd3 : d ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥D) (x := ⟨d, hdD⟩)
    simpa [hDcard] using congrArg Subtype.val h
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hDeq : D = Subgroup.zpowers d := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdD) ?_).symm
    rw [hDcard, Nat.card_zpowers, hord]
  obtain ⟨f, hf, j, hj, hd⟩ := (CFSG.mem_sup_of_commute
    (fun f hf j hj => hcomm f hf j hj)).mp (hV ▸ hDV hdD)
  have hαD : t * d * t⁻¹ ∈ D := hDt d hdD
  have hα1 : t * d * t⁻¹ ≠ 1 := by
    intro h
    apply hd1
    have := congrArg (fun z => t⁻¹ * z * t) h
    simpa [mul_assoc] using this
  rcases eq_one_or_eq_or_eq_inv_of_mem_of_card_three hDcard hdD hd1 hαD with h1 | hfixd | hinvd
  · exact absurd h1 hα1
  · exfalso
    exact hdF (mem_F_of_conj_eq_of_mul hf hj hfix hinv hJ3 hd hfixd)
  · have hdJ : d ∈ J := mem_J_of_conj_eq_inv_of_mul hf hj hcomm hfix hinv hF3 hd hinvd
    rw [hDeq]
    exact Subgroup.zpowers_le.mpr hdJ

private theorem map_conj_centralizingInV_le {p : ℕ} {H V J J' : Subgroup G} {t v : G}
    (hVH : V ≤ H) (htH : t ∈ H) (hV : t ∈ Subgroup.normalizer (V : Set G))
    (hJJ' : J.map (MulAut.conj t).toMonoidHom = J')
    (hv : v ∈ centralizingInV p H V J) :
    t * v * t⁻¹ ∈ centralizingInV p H V J' := by
  have hvV : v ∈ V := (Subgroup.mem_inf.mp hv).2
  have hvH : v ∈ H := hVH hvV
  have hvcent := (mem_centralizingInV_iff hvH).mp hv |>.2
  have htvtH : t * v * t⁻¹ ∈ H := H.mul_mem (H.mul_mem htH hvH) (H.inv_mem htH)
  have htvtV : t * v * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hV v).mp hvV
  refine (mem_centralizingInV_iff htvtH).mpr ⟨htvtV, ?_⟩
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  let wbar : StarGroup p H := π ⟨t, htH⟩
  let vbar : StarGroup p H := π ⟨v, hvH⟩
  have hmap : π ⟨t * v * t⁻¹, htvtH⟩ = wbar * vbar * wbar⁻¹ := by
    have harg : (⟨t * v * t⁻¹, htvtH⟩ : ↥H) =
        ⟨t, htH⟩ * ⟨v, hvH⟩ * ⟨t, htH⟩⁻¹ := Subtype.ext rfl
    rw [harg, map_mul, map_mul, map_inv]
  rw [hmap]
  have hJstar : (starImg p H J).map (MulAut.conj wbar).toMonoidHom = starImg p H J' := by
    have h := starImg_map_conj p H J ⟨t, htH⟩
    rw [hJJ'] at h
    simpa [wbar, π] using h.symm
  intro y hy
  have hy' : wbar⁻¹ * y * wbar ∈ starImg p H J := by
    have hmem : y ∈ (starImg p H J).map (MulAut.conj wbar).toMonoidHom := by
      rw [hJstar]
      exact hy
    obtain ⟨x, hx, hxy⟩ := hmem
    rw [← hxy]
    show wbar⁻¹ * (wbar * x * wbar⁻¹) * wbar ∈ starImg p H J
    rw [show wbar⁻¹ * (wbar * x * wbar⁻¹) * wbar = x by group]
    exact hx
  have hcomm : (wbar⁻¹ * y * wbar) * vbar = vbar * (wbar⁻¹ * y * wbar) :=
    Subgroup.mem_centralizer_iff.mp hvcent _ hy'
  calc y * (wbar * vbar * wbar⁻¹)
      = wbar * ((wbar⁻¹ * y * wbar) * vbar) * wbar⁻¹ := by group
    _ = wbar * (vbar * (wbar⁻¹ * y * wbar)) * wbar⁻¹ := by rw [hcomm]
    _ = (wbar * vbar * wbar⁻¹) * y := by group

private theorem mem_normalizer_right_of_fixes_left
    {L I : Subgroup G} (hS : {K : Subgroup G | IsPComponentIn p K H ∧ ¬ K ≤ M} = {L, I})
    (hLI : L ≠ I) (hI : IsPComponentIn p I H) (hIM : ¬ I ≤ M)
    {t : G} (htH : t ∈ H) (htM : t ∈ M)
    (hfix : L.map (MulAut.conj t).toMonoidHom = L) :
    t ∈ Subgroup.normalizer (I : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rcases map_conj_eq_left_or_right_of_pair hS hI hIM htH htM with hIL | hII
  · exfalso
    have hconj := Subgroup.map_injective (f := (MulAut.conj t).toMonoidHom)
      (MulAut.conj t).injective
    exact hLI (hconj (hfix.trans hIL.symm))
  · exact hII

private theorem false_of_invariant_centralizingInV
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {I W : Subgroup G} (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    (hVH : D.V ≤ H) (hWV : W ≤ D.V) (hcard : Nat.card W = 3)
    (hcent : Subgroup.centralizer (W : Set G) ≤ M)
    (hW : W ≤ centralizingInV 3 H D.V I) : False := by
  have hWL : starImg 3 H W ≤ Subgroup.centralizer (starImg 3 H I : Set (StarGroup 3 H)) := by
    intro x hx
    obtain ⟨wH, hwH, rfl⟩ := Subgroup.mem_map.mp hx
    have hw : (wH : G) ∈ W := Subgroup.mem_subgroupOf.mp hwH
    have hmem := (mem_centralizingInV_iff (hVH (hWV hw))).mp (hW hw) |>.2
    simpa using hmem
  exact hIM (hc.le_M_of_starImg_le_centralizer D hI hWV hcard hcent hWL)

private theorem centralizingInV_invariant_under_triple
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {I : Subgroup G}
    (hVH : D.V ≤ H)
    (hCV1 : D.t₁ ∈ Subgroup.normalizer (D.V : Set G))
    (hCV2 : D.t₂ ∈ Subgroup.normalizer (D.V : Set G))
    (hCV3 : D.t₃ ∈ Subgroup.normalizer (D.V : Set G))
    (hIH1 : D.t₁ ∈ H) (hIH2 : D.t₂ ∈ H) (hIH3 : D.t₃ ∈ H)
    (hNI1 : D.t₁ ∈ Subgroup.normalizer (I : Set G))
    (hNI2 : D.t₂ ∈ Subgroup.normalizer (I : Set G))
    (hNI3 : D.t₃ ∈ Subgroup.normalizer (I : Set G)) :
    ∀ t ∈ ({D.t₁, D.t₂, D.t₃} : Set G),
      ∀ x ∈ centralizingInV 3 H D.V I, t * x * t⁻¹ ∈ centralizingInV 3 H D.V I := by
  intro t ht x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl
  · exact map_conj_mem_centralizingInV_of_normalizer hVH hIH1 hCV1 hNI1 hx
  · exact map_conj_mem_centralizingInV_of_normalizer hVH hIH2 hCV2 hNI2 hx
  · exact map_conj_mem_centralizingInV_of_normalizer hVH hIH3 hCV3 hNI3 hx

private theorem false_of_invariant_centralizingInV_line
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {I : Subgroup G}
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M) (hVH : D.V ≤ H)
    (hCIne : centralizingInV 3 H D.V I ≠ ⊥)
    (hDt : ∀ t ∈ ({D.t₁, D.t₂, D.t₃} : Set G),
      ∀ x ∈ centralizingInV 3 H D.V I, t * x * t⁻¹ ∈ centralizingInV 3 H D.V I) : False := by
  rcases D.cfg.exists_le_of_invariant (inf_le_right : centralizingInV 3 H D.V I ≤ D.V)
      hCIne hDt with hW | hW | hW
  · exact false_of_invariant_centralizingInV hc D hI hIM hVH
      (by rw [D.cfg.join]; exact le_sup_left.trans le_sup_left) D.cfg.card₁
      (D.centralizer_le₁ hc) hW
  · exact false_of_invariant_centralizingInV hc D hI hIM hVH
      (by rw [D.cfg.join]; exact le_sup_right.trans le_sup_left) D.cfg.card₂
      (D.centralizer_le₂ hc) hW
  · exact false_of_invariant_centralizingInV hc D hI hIM hVH
      (by rw [D.cfg.join]; exact le_sup_right) D.cfg.card₃
      (D.centralizer_le₃ hc) hW

private theorem false_of_pair_no_swap
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    (hIL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H I))
    (hfix1 : L.map (MulAut.conj D.t₁).toMonoidHom = L)
    (hfix2 : L.map (MulAut.conj D.t₂).toMonoidHom = L)
    (hfix3 : L.map (MulAut.conj D.t₃).toMonoidHom = L) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS : {J : Subgroup G | IsPComponentIn 3 J H ∧ ¬ J ≤ M} = {L, I} :=
    eq_pair_of_ncard_le_two hLI hL hLM hI hIM
      (nineSixTwoComp_holds G M E H E 3 h hH2 hpσ (fun hle => hLM ((le_pLayerIn hL).trans hle)))
  have hVI : D.V ≤ Subgroup.normalizer (I : Set G) :=
    V_le_normalizer_of_pair (L := I) (I := L) hc D (Ne.symm hLI) hI hIM hL hLM
      (by rw [Set.pair_comm]; exact hS)
  have hVH : D.V ≤ H := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_left
  have hCIne : centralizingInV 3 H D.V I ≠ ⊥ :=
    centralizingInV_ne_bot_of_isPSLType hVH hVI D.cfg.elem D.cfg.card hIL2
  have hCV : D.t₁ ∈ Subgroup.normalizer (D.V : Set G) :=
    D.cfg.tripleNormalizer_le_normalizer D.cfg.t₁_mem_tripleNormalizer
  have hCV2 : D.t₂ ∈ Subgroup.normalizer (D.V : Set G) :=
    D.cfg.tripleNormalizer_le_normalizer D.cfg.t₂_mem_tripleNormalizer
  have hCV3 : D.t₃ ∈ Subgroup.normalizer (D.V : Set G) :=
    D.cfg.tripleNormalizer_le_normalizer D.cfg.t₃_mem_tripleNormalizer
  have hIH1 : D.t₁ ∈ H := (D.t₁_mem hc.data).1
  have hIH2 : D.t₂ ∈ H := (D.t₂_mem hc.data).1
  have hIH3 : D.t₃ ∈ H := (D.t₃_mem hc.data).1
  have hNI1 : D.t₁ ∈ Subgroup.normalizer (I : Set G) :=
    mem_normalizer_right_of_fixes_left hS hLI hI hIM
      (D.t₁_mem hc.data).1 (D.t₁_mem hc.data).2 hfix1
  have hNI2 : D.t₂ ∈ Subgroup.normalizer (I : Set G) :=
    mem_normalizer_right_of_fixes_left hS hLI hI hIM
      (D.t₂_mem hc.data).1 (D.t₂_mem hc.data).2 hfix2
  have hNI3 : D.t₃ ∈ Subgroup.normalizer (I : Set G) :=
    mem_normalizer_right_of_fixes_left hS hLI hI hIM
      (D.t₃_mem hc.data).1 (D.t₃_mem hc.data).2 hfix3
  have hDt : ∀ t ∈ ({D.t₁, D.t₂, D.t₃} : Set G),
      ∀ x ∈ centralizingInV 3 H D.V I, t * x * t⁻¹ ∈ centralizingInV 3 H D.V I :=
    centralizingInV_invariant_under_triple D hVH hCV hCV2 hCV3 hIH1 hIH2 hIH3 hNI1 hNI2 hNI3
  exact false_of_invariant_centralizingInV_line hc D hI hIM hVH hCIne hDt

private theorem le_sup_W2W3_or_le_W1_of_invariant_t1
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {D' : Subgroup G}
    (hDV : D' ≤ D.V) (hDcard : Nat.card D' = 3)
    (hDt : ∀ x ∈ D', D.t₁ * x * D.t₁⁻¹ ∈ D') :
    D' ≤ D.W₂ ⊔ D.W₃ ∨ D' ≤ D.W₁ := by
  have : IsMulCommutative ↥D.V := D.cfg.elem.1
  have hW1V : D.W₁ ≤ D.V := by rw [D.cfg.join]; exact le_sup_left.trans le_sup_left
  have hW2V : D.W₂ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right.trans le_sup_left
  have hW3V : D.W₃ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right
  have hFJ : (D.W₂ ⊔ D.W₃ : Subgroup G) ≤ D.V := sup_le hW2V hW3V
  have hV : D.V = (D.W₂ ⊔ D.W₃) ⊔ D.W₁ := by
    rw [D.cfg.join]
    ac_rfl
  refine le_fixed_or_eq_inverted hV ?_ ?_ ?_ ?_ ?_ hDV hDcard hDt
  · intro f hf j hj
    exact setLike_mul_comm (hFJ hf) (hW1V hj)
  · intro f hf
    exact D.cfg.elem.2 f (hFJ hf)
  · intro j hj
    exact D.cfg.elem.2 j (hW1V hj)
  · intro x hx
    rw [D.cfg.comm₁ x hx]
    group
  · intro x hx
    exact D.cfg.inv₁ x hx

private theorem le_sup_W1W3_or_le_W2_of_invariant_t2
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {D' : Subgroup G}
    (hDV : D' ≤ D.V) (hDcard : Nat.card D' = 3)
    (hDt : ∀ x ∈ D', D.t₂ * x * D.t₂⁻¹ ∈ D') :
    D' ≤ D.W₁ ⊔ D.W₃ ∨ D' ≤ D.W₂ := by
  have : IsMulCommutative ↥D.V := D.cfg.elem.1
  have hW1V : D.W₁ ≤ D.V := by rw [D.cfg.join]; exact le_sup_left.trans le_sup_left
  have hW2V : D.W₂ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right.trans le_sup_left
  have hW3V : D.W₃ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right
  have hFJ : (D.W₁ ⊔ D.W₃ : Subgroup G) ≤ D.V := sup_le hW1V hW3V
  have hV : D.V = (D.W₁ ⊔ D.W₃) ⊔ D.W₂ := by
    rw [D.cfg.join]
    ac_rfl
  refine le_fixed_or_eq_inverted hV ?_ ?_ ?_ ?_ ?_ hDV hDcard hDt
  · intro f hf j hj
    exact setLike_mul_comm (hFJ hf) (hW2V hj)
  · intro f hf
    exact D.cfg.elem.2 f (hFJ hf)
  · intro j hj
    exact D.cfg.elem.2 j (hW2V hj)
  · intro x hx
    rw [D.cfg.comm₂ x hx]
    group
  · intro x hx
    exact D.cfg.inv₂ x hx

private theorem le_sup_W1W2_or_le_W3_of_invariant_t3
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {D' : Subgroup G}
    (hDV : D' ≤ D.V) (hDcard : Nat.card D' = 3)
    (hDt : ∀ x ∈ D', D.t₃ * x * D.t₃⁻¹ ∈ D') :
    D' ≤ D.W₁ ⊔ D.W₂ ∨ D' ≤ D.W₃ := by
  have : IsMulCommutative ↥D.V := D.cfg.elem.1
  have hW1V : D.W₁ ≤ D.V := by rw [D.cfg.join]; exact le_sup_left.trans le_sup_left
  have hW2V : D.W₂ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right.trans le_sup_left
  have hW3V : D.W₃ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right
  have hFJ : (D.W₁ ⊔ D.W₂ : Subgroup G) ≤ D.V := sup_le hW1V hW2V
  have hV : D.V = (D.W₁ ⊔ D.W₂) ⊔ D.W₃ := by
    rw [D.cfg.join]
  refine le_fixed_or_eq_inverted hV ?_ ?_ ?_ ?_ ?_ hDV hDcard hDt
  · intro f hf j hj
    exact setLike_mul_comm (hFJ hf) (hW3V hj)
  · intro f hf
    exact D.cfg.elem.2 f (hFJ hf)
  · intro j hj
    exact D.cfg.elem.2 j (hW3V hj)
  · intro x hx
    rw [D.cfg.comm₃ x hx]
    group
  · intro x hx
    exact D.cfg.inv₃ x hx

omit [Finite G] in
private theorem t1_mul_t2_inv_W1 (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {x : G}
    (hx : x ∈ D.W₁) : D.t₁ * D.t₂ * x * (D.t₁ * D.t₂)⁻¹ = x⁻¹ := by
  have h2 : D.t₂ * x * D.t₂⁻¹ = x := by
    rw [D.cfg.comm₂ x (Subgroup.mem_sup_left hx)]
    group
  calc D.t₁ * D.t₂ * x * (D.t₁ * D.t₂)⁻¹
      = D.t₁ * (D.t₂ * x * D.t₂⁻¹) * D.t₁⁻¹ := by group
    _ = D.t₁ * x * D.t₁⁻¹ := by rw [h2]
    _ = x⁻¹ := D.cfg.inv₁ x hx

omit [Finite G] in
private theorem t1_mul_t2_inv_W2 (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {x : G}
    (hx : x ∈ D.W₂) : D.t₁ * D.t₂ * x * (D.t₁ * D.t₂)⁻¹ = x⁻¹ := by
  have h1 : D.t₁ * x * D.t₁⁻¹ = x := by
    rw [D.cfg.comm₁ x (Subgroup.mem_sup_left hx)]
    group
  have h1inv : D.t₁ * x⁻¹ * D.t₁⁻¹ = x⁻¹ := by
    have := congrArg Inv.inv h1
    simpa [mul_assoc] using this
  calc D.t₁ * D.t₂ * x * (D.t₁ * D.t₂)⁻¹
      = D.t₁ * (D.t₂ * x * D.t₂⁻¹) * D.t₁⁻¹ := by group
    _ = D.t₁ * x⁻¹ * D.t₁⁻¹ := by rw [D.cfg.inv₂ x hx]
    _ = x⁻¹ := h1inv

omit [Finite G] in
private theorem t1_mul_t2_fix_W3 (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {x : G}
    (hx : x ∈ D.W₃) : D.t₁ * D.t₂ * x * (D.t₁ * D.t₂)⁻¹ = x := by
  have h1 : D.t₁ * x * D.t₁⁻¹ = x := by
    rw [D.cfg.comm₁ x (Subgroup.mem_sup_right hx)]
    group
  have h2 : D.t₂ * x * D.t₂⁻¹ = x := by
    rw [D.cfg.comm₂ x (Subgroup.mem_sup_right hx)]
    group
  calc D.t₁ * D.t₂ * x * (D.t₁ * D.t₂)⁻¹
      = D.t₁ * (D.t₂ * x * D.t₂⁻¹) * D.t₁⁻¹ := by group
    _ = x := by rw [h2, h1]

omit [Finite G] in
private theorem t1_mul_t2_inv_sup_W1W2 (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {x : G}
    (hx : x ∈ D.W₁ ⊔ D.W₂) : D.t₁ * D.t₂ * x * (D.t₁ * D.t₂)⁻¹ = x⁻¹ := by
  have : IsMulCommutative ↥D.V := D.cfg.elem.1
  have hW1V : D.W₁ ≤ D.V := by rw [D.cfg.join]; exact le_sup_left.trans le_sup_left
  have hW2V : D.W₂ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right.trans le_sup_left
  obtain ⟨a, ha, b, hb, rfl⟩ := (CFSG.mem_sup_of_commute
    (fun a ha b hb => setLike_mul_comm (hW1V ha) (hW2V hb))).mp hx
  calc D.t₁ * D.t₂ * (a * b) * (D.t₁ * D.t₂)⁻¹
      = (D.t₁ * D.t₂ * a * (D.t₁ * D.t₂)⁻¹) *
          (D.t₁ * D.t₂ * b * (D.t₁ * D.t₂)⁻¹) := by group
    _ = a⁻¹ * b⁻¹ := by rw [t1_mul_t2_inv_W1 D ha, t1_mul_t2_inv_W2 D hb]
    _ = (a * b)⁻¹ := by
      rw [mul_inv_rev]
      exact setLike_mul_comm (hW1V (D.W₁.inv_mem ha)) (hW2V (D.W₂.inv_mem hb))

private theorem le_W3_or_le_sup_W1W2_of_invariant_t1t2
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {D' : Subgroup G}
    (hDV : D' ≤ D.V) (hDcard : Nat.card D' = 3)
    (hDt : ∀ x ∈ D', D.t₁ * D.t₂ * x * (D.t₁ * D.t₂)⁻¹ ∈ D') :
    D' ≤ D.W₃ ∨ D' ≤ D.W₁ ⊔ D.W₂ := by
  have : IsMulCommutative ↥D.V := D.cfg.elem.1
  have hW1V : D.W₁ ≤ D.V := by rw [D.cfg.join]; exact le_sup_left.trans le_sup_left
  have hW2V : D.W₂ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right.trans le_sup_left
  have hW3V : D.W₃ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right
  have hFJ : (D.W₁ ⊔ D.W₂ : Subgroup G) ≤ D.V := sup_le hW1V hW2V
  have hV : D.V = D.W₃ ⊔ (D.W₁ ⊔ D.W₂) := by
    rw [D.cfg.join, sup_comm (D.W₁ ⊔ D.W₂) D.W₃]
  refine le_fixed_or_eq_inverted hV ?_ ?_ ?_ ?_ ?_ hDV hDcard hDt
  · intro f hf j hj
    exact setLike_mul_comm (hW3V hf) (hFJ hj)
  · intro f hf
    exact D.cfg.elem.2 f (hW3V hf)
  · intro j hj
    exact D.cfg.elem.2 j (hFJ hj)
  · intro x hx
    exact t1_mul_t2_fix_W3 D hx
  · intro x hx
    exact t1_mul_t2_inv_sup_W1W2 D hx

omit [Finite G] in
private theorem mem_xSub_iff {p : ℕ} {M H : Subgroup G} {z : G} (hz : z ∈ H) :
    z ∈ xSub p M H ↔
      QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨z, hz⟩ ∈
        Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) := by
  have hsub : ((xSub p M H).subgroupOf H) =
      (Subgroup.centralizer (kStar p M H)).comap
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) := by
    rw [xSub]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have h1 : (⟨z, hz⟩ : ↥H) ∈ (xSub p M H).subgroupOf H ↔ z ∈ xSub p M H :=
    Subgroup.mem_subgroupOf
  have h2 : (⟨z, hz⟩ : ↥H) ∈ (Subgroup.centralizer (kStar p M H)).comap
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) ↔ z ∈ xSub p M H := by
    rw [← hsub]
    exact h1
  rw [Subgroup.mem_comap] at h2
  exact h2.symm

omit [Finite G] in
private theorem mem_centralizer_kStar_of_mem_centralizers {p : ℕ} {v : G}
    {L I : Subgroup G} (hvH : v ∈ H)
    (hkStar : kStar p M H = starImg p H L ⊔ starImg p H I)
    (hcomm : ∀ y ∈ starImg p H L, ∀ z ∈ starImg p H I, y * z = z * y)
    (hvcentL : (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨v, hvH⟩) ∈
      Subgroup.centralizer (starImg p H L : Set (StarGroup p H)))
    (hvcentI : (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨v, hvH⟩) ∈
      Subgroup.centralizer (starImg p H I : Set (StarGroup p H))) :
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨v, hvH⟩) ∈
      Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) := by
  let vbar : StarGroup p H :=
    QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨v, hvH⟩
  change vbar ∈ Subgroup.centralizer (kStar p M H : Set (StarGroup p H))
  rw [hkStar]
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hx
  have hyc := (Subgroup.mem_centralizer_iff.mp hvcentL) y hy
  have hzc := (Subgroup.mem_centralizer_iff.mp hvcentI) z hz
  calc (y * z) * vbar = y * (z * vbar) := by group
    _ = y * (vbar * z) := by rw [hzc]
    _ = (y * vbar) * z := by group
    _ = (vbar * y) * z := by rw [hyc]
    _ = vbar * (y * z) := by group

private theorem centralizingInV_inf_eq_bot
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M p E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : p ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn p L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn p I H) (hIM : ¬ I ≤ M) :
    centralizingInV p H D.V L ⊓ centralizingInV p H D.V I = ⊥ := by
  have : Fact p.Prime := ⟨hc.ctx.p_prime⟩
  have hnotlayer : ¬ pLayerIn p H ≤ M := fun hle => hLM ((le_pLayerIn hL).trans hle)
  have hS : {J : Subgroup G | IsPComponentIn p J H ∧ ¬ J ≤ M} = {L, I} :=
    eq_pair_of_ncard_le_two hLI hL hLM hI hIM
      (nineSixTwoComp_holds G M E H E p h hH2 hpσ hnotlayer)
  have hkSub : kSub p M H = L ⊔ I := by
    unfold kSub
    rw [if_neg hnotlayer, hS]
    simp [sSup_insert, sSup_singleton]
  have hkStar : kStar p M H = starImg p H L ⊔ starImg p H I := by
    rw [kStar_eq_starImg, hkSub, starImg_sup' hL.1 hI.1]
  have hLc : CFSG.IsComponent (starImg p H L) := isComponent_starImg hL
  have hIc : CFSG.IsComponent (starImg p H I) := isComponent_starImg hI
  have hne : starImg p H L ≠ starImg p H I := fun heq =>
    hLI (eq_of_starImg_eq hc.ctx.p_prime hL hI heq)
  have hcommC := (CFSG.LocalCores.distinct_components_commute hLc hIc).resolve_left hne
  have hcomm' : ∀ y ∈ starImg p H L, ∀ z ∈ starImg p H I, y * z = z * y :=
    fun y hy z hz =>
      (Subgroup.mem_centralizer_iff.mp
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommC) hy) z hz).symm
  refine le_bot_iff.mp ?_
  intro v hv
  obtain ⟨hvL, hvI⟩ := Subgroup.mem_inf.mp hv
  have hvV : v ∈ D.V := (Subgroup.mem_inf.mp hvL).2
  have hvH : v ∈ H := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_left hvV
  have hvcentL := (mem_centralizingInV_iff hvH).mp hvL |>.2
  have hvcentI := (mem_centralizingInV_iff hvH).mp hvI |>.2
  let vbar : StarGroup p H :=
    QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨v, hvH⟩
  have hvcentK : vbar ∈ Subgroup.centralizer (kStar p M H : Set (StarGroup p H)) :=
    mem_centralizer_kStar_of_mem_centralizers hvH hkStar hcomm' hvcentL hvcentI
  have hvX : v ∈ xSub p M H := (mem_xSub_iff hvH).mpr (by simpa [vbar] using hvcentK)
  have hVX : v ∈ D.V ⊓ xSub p M H := Subgroup.mem_inf.mpr ⟨hvV, hvX⟩
  have hbot := hc.inf_xSub_eq_bot D.cfg (D.centralizer_le₁ hc) (D.centralizer_le₂ hc)
    (D.centralizer_le₃ hc) (D.t₁_mem hc.data) (D.t₂_mem hc.data) (D.t₃_mem hc.data)
  rw [hbot] at hVX
  exact Subgroup.mem_bot.mp hVX

omit [Finite G] in
private theorem false_of_one_swap {Wi Wj Wk CL : Subgroup G}
    (hnotWi : ¬ CL ≤ Wi) (hnotPlane : ¬ CL ≤ Wj ⊔ Wk)
    (hfixj : CL ≤ Wj ∨ CL ≤ Wi ⊔ Wk) (hfixk : CL ≤ Wk ∨ CL ≤ Wi ⊔ Wj)
    (hinter : (Wi ⊔ Wk) ⊓ (Wi ⊔ Wj) = Wi) : False := by
  have hj : CL ≤ Wi ⊔ Wk := by
    rcases hfixj with h | h
    · exact absurd (h.trans le_sup_left) hnotPlane
    · exact h
  have hk : CL ≤ Wi ⊔ Wj := by
    rcases hfixk with h | h
    · exact absurd (h.trans le_sup_right) hnotPlane
    · exact h
  exact hnotWi (hinter ▸ le_inf hj hk)

omit [Finite G] in
private theorem false_of_three_swaps {Wi Wj Wk CL : Subgroup G}
    (hnotWk : ¬ CL ≤ Wk) (hnotPlane : ¬ CL ≤ Wi ⊔ Wj)
    (hfixPair : CL ≤ Wk ∨ CL ≤ Wi ⊔ Wj) : False := by
  rcases hfixPair with h | h
  · exact hnotWk h
  · exact hnotPlane h

private theorem inf_sup_eq_bot_of_isE27 {V A B C : Subgroup G}
    (hV : V = A ⊔ B ⊔ C) (hcardA : Nat.card A = 3) (hcardB : Nat.card B = 3)
    (hcardC : Nat.card C = 3) (hcardV : Nat.card V = 27)
    (hcommBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) : A ⊓ (B ⊔ C) = ⊥ := by
  have hBC9 : Nat.card ↥(B ⊔ C) ≤ 9 := by
    let f : ↥B × ↥C → ↥(B ⊔ C) := fun x =>
      ⟨(x.1 : G) * (x.2 : G), Subgroup.mul_mem_sup x.1.2 x.2.2⟩
    have hsurj : Function.Surjective f := by
      intro y
      obtain ⟨b, hb, c, hc, hbc⟩ := (CFSG.mem_sup_of_commute hcommBC).mp y.2
      exact ⟨(⟨b, hb⟩, ⟨c, hc⟩), Subtype.ext hbc⟩
    have hcard := Nat.card_le_card_of_surjective f hsurj
    rw [Nat.card_prod, hcardB, hcardC] at hcard
    simpa using hcard
  by_contra hne
  have hAle : A ≤ B ⊔ C := by
    have hle : A ⊓ (B ⊔ C) ≤ A := inf_le_left
    have hpos : 0 < Nat.card ↥(A ⊓ (B ⊔ C)) := Nat.card_pos
    have hdvdA : Nat.card ↥(A ⊓ (B ⊔ C)) ∣ 3 := by
      rw [← hcardA]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hcardInt : Nat.card ↥(A ⊓ (B ⊔ C)) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvdA with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hne
      · exact h
    have hEq : A ⊓ (B ⊔ C) = A := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardInt, hcardA])
    exact hEq ▸ inf_le_right
  have hVle : V ≤ B ⊔ C := by
    rw [hV]
    exact sup_le (sup_le hAle (le_sup_left : B ≤ B ⊔ C)) le_sup_right
  have hcardle : Nat.card V ≤ Nat.card ↥(B ⊔ C) :=
    Nat.le_of_dvd (Nat.card_pos) (Subgroup.card_dvd_of_le hVle)
  have h27 : 27 ≤ Nat.card ↥(B ⊔ C) := by
    rw [← hcardV]
    exact hcardle
  omega

omit [Finite G] in
private theorem sup_inf_sup_eq_left_of_direct {A B C : Subgroup G}
    (hCnorm : C ≤ Subgroup.normalizer (A : Set G))
    (hdir : C ⊓ (A ⊔ B) = ⊥) : (A ⊔ C) ⊓ (A ⊔ B) = A := by
  have h := Subgroup.inf_sup_assoc_of_le (H := C) (K := A ⊔ B) (N := A) hCnorm
    (le_sup_left : A ≤ A ⊔ B)
  have hdir' : (A ⊔ B) ⊓ C = ⊥ := by rw [inf_comm]; exact hdir
  rw [hdir', bot_sup_eq, sup_comm C A] at h
  rw [inf_comm]
  exact h.symm

private theorem W1_inf_sup_W2W3_eq_bot (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    D.W₁ ⊓ (D.W₂ ⊔ D.W₃) = ⊥ := by
  have : IsMulCommutative ↥D.V := D.cfg.elem.1
  have hW2V : D.W₂ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right.trans le_sup_left
  have hW3V : D.W₃ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right
  exact inf_sup_eq_bot_of_isE27 D.cfg.join D.cfg.card₁ D.cfg.card₂ D.cfg.card₃ D.cfg.card
    (fun b hb c hc => setLike_mul_comm (hW2V hb) (hW3V hc))

private theorem W2_inf_sup_W1W3_eq_bot (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    D.W₂ ⊓ (D.W₁ ⊔ D.W₃) = ⊥ := by
  have : IsMulCommutative ↥D.V := D.cfg.elem.1
  have hW1V : D.W₁ ≤ D.V := by rw [D.cfg.join]; exact le_sup_left.trans le_sup_left
  have hW3V : D.W₃ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right
  have hV : D.V = D.W₂ ⊔ D.W₁ ⊔ D.W₃ := by
    rw [D.cfg.join]
    ac_rfl
  exact inf_sup_eq_bot_of_isE27 hV D.cfg.card₂ D.cfg.card₁ D.cfg.card₃ D.cfg.card
    (fun b hb c hc => setLike_mul_comm (hW1V hb) (hW3V hc))

private theorem W3_inf_sup_W1W2_eq_bot (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    D.W₃ ⊓ (D.W₁ ⊔ D.W₂) = ⊥ := by
  have : IsMulCommutative ↥D.V := D.cfg.elem.1
  have hW1V : D.W₁ ≤ D.V := by rw [D.cfg.join]; exact le_sup_left.trans le_sup_left
  have hW2V : D.W₂ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right.trans le_sup_left
  have hV : D.V = D.W₃ ⊔ D.W₁ ⊔ D.W₂ := by
    rw [D.cfg.join]
    ac_rfl
  exact inf_sup_eq_bot_of_isE27 hV D.cfg.card₃ D.cfg.card₁ D.cfg.card₂ D.cfg.card
    (fun b hb c hc => setLike_mul_comm (hW1V hb) (hW2V hc))

private theorem W1W3_inf_W1W2_eq_W1 (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    (D.W₁ ⊔ D.W₃) ⊓ (D.W₁ ⊔ D.W₂) = D.W₁ := by
  have : IsMulCommutative ↥D.V := D.cfg.elem.1
  have hW1V : D.W₁ ≤ D.V := by rw [D.cfg.join]; exact le_sup_left.trans le_sup_left
  have hW3V : D.W₃ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right
  have hnorm : D.W₃ ≤ Subgroup.normalizer (D.W₁ : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hcomm : x * z = z * x := setLike_mul_comm (hW3V hx) (hW1V hz)
      have hconj : x * z * x⁻¹ = z := by rw [hcomm]; group
      simpa [MulAut.conj_apply, hconj] using hz
    · intro hy
      refine ⟨y, hy, ?_⟩
      have hcomm : x * y = y * x := setLike_mul_comm (hW3V hx) (hW1V hy)
      have hconj : x * y * x⁻¹ = y := by rw [hcomm]; group
      simp [MulAut.conj_apply, hconj]
  exact sup_inf_sup_eq_left_of_direct hnorm (W3_inf_sup_W1W2_eq_bot D)

private theorem W2W3_inf_W2W1_eq_W2 (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    (D.W₂ ⊔ D.W₃) ⊓ (D.W₂ ⊔ D.W₁) = D.W₂ := by
  have : IsMulCommutative ↥D.V := D.cfg.elem.1
  have hW2V : D.W₂ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right.trans le_sup_left
  have hW1V : D.W₁ ≤ D.V := by rw [D.cfg.join]; exact le_sup_left.trans le_sup_left
  have hnorm : D.W₁ ≤ Subgroup.normalizer (D.W₂ : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hcomm : x * z = z * x := setLike_mul_comm (hW1V hx) (hW2V hz)
      have hconj : x * z * x⁻¹ = z := by rw [hcomm]; group
      simpa [MulAut.conj_apply, hconj] using hz
    · intro hy
      refine ⟨y, hy, ?_⟩
      have hcomm : x * y = y * x := setLike_mul_comm (hW1V hx) (hW2V hy)
      have hconj : x * y * x⁻¹ = y := by rw [hcomm]; group
      simp [MulAut.conj_apply, hconj]
  have h := sup_inf_sup_eq_left_of_direct (A := D.W₂) (B := D.W₃) (C := D.W₁) hnorm
    (W1_inf_sup_W2W3_eq_bot D)
  rwa [inf_comm] at h

private theorem W3W2_inf_W3W1_eq_W3 (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    (D.W₃ ⊔ D.W₂) ⊓ (D.W₃ ⊔ D.W₁) = D.W₃ := by
  have : IsMulCommutative ↥D.V := D.cfg.elem.1
  have hW3V : D.W₃ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right
  have hW2V : D.W₂ ≤ D.V := by rw [D.cfg.join]; exact le_sup_right.trans le_sup_left
  have hnorm : D.W₂ ≤ Subgroup.normalizer (D.W₃ : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hcomm : x * z = z * x := setLike_mul_comm (hW2V hx) (hW3V hz)
      have hconj : x * z * x⁻¹ = z := by rw [hcomm]; group
      simpa [MulAut.conj_apply, hconj] using hz
    · intro hy
      refine ⟨y, hy, ?_⟩
      have hcomm : x * y = y * x := setLike_mul_comm (hW2V hx) (hW3V hy)
      have hconj : x * y * x⁻¹ = y := by rw [hcomm]; group
      simp [MulAut.conj_apply, hconj]
  have hdir : D.W₂ ⊓ (D.W₃ ⊔ D.W₁) = ⊥ := by
    rw [sup_comm D.W₃ D.W₁]
    exact W2_inf_sup_W1W3_eq_bot D
  exact sup_inf_sup_eq_left_of_direct (A := D.W₃) (B := D.W₁) (C := D.W₂) hnorm hdir

private theorem le_M_of_le_centralizingInV
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {L W : Subgroup G} (hL : IsPComponentIn 3 L H)
    (hWV : W ≤ D.V) (hW : Nat.card W = 3)
    (hCW : Subgroup.centralizer (W : Set G) ≤ M)
    (hWCL : W ≤ centralizingInV 3 H D.V L) :
    L ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hVH : D.V ≤ H := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_left
  have hWL : starImg 3 H W ≤ Subgroup.centralizer (starImg 3 H L : Set (StarGroup 3 H)) := by
    intro x hx
    obtain ⟨wH, hwH, rfl⟩ := Subgroup.mem_map.mp hx
    have hw : (wH : G) ∈ W := Subgroup.mem_subgroupOf.mp hwH
    have hmem := (mem_centralizingInV_iff (hVH (hWV hw))).mp (hWCL hw) |>.2
    simpa using hmem
  exact hc.le_M_of_starImg_le_centralizer D hL hWV hW hCW hWL

private theorem not_le_W_of_centralizingInV
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {L W : Subgroup G} (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hWV : W ≤ D.V) (hW : Nat.card W = 3)
    (hCW : Subgroup.centralizer (W : Set G) ≤ M)
    (hCLcard : Nat.card (centralizingInV 3 H D.V L) = 3) :
    ¬ centralizingInV 3 H D.V L ≤ W := by
  intro hle
  have heq : centralizingInV 3 H D.V L = W :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hW, hCLcard])
  have hWCL : W ≤ centralizingInV 3 H D.V L := heq ▸ le_rfl
  exact hLM (le_M_of_le_centralizingInV hc D hL hWV hW hCW hWCL)

private theorem card_centralizingInV_eq_of_swap {V L I : Subgroup G} {t : G}
    (hVH : V ≤ H) (htH : t ∈ H) (htV : t ∈ Subgroup.normalizer (V : Set G))
    (hswap : L.map (MulAut.conj t).toMonoidHom = I) :
    Nat.card (centralizingInV 3 H V L) = Nat.card (centralizingInV 3 H V I) := by
  let CL : Subgroup G := centralizingInV 3 H V L
  let CI : Subgroup G := centralizingInV 3 H V I
  change Nat.card CL = Nat.card CI
  have hmapL : CL.map (MulAut.conj t).toMonoidHom ≤ CI := by
    rintro x ⟨v, hv, rfl⟩
    exact map_conj_centralizingInV_le hVH htH htV hswap hv
  have hinj : Function.Injective (fun x : ↥CL => ((MulAut.conj t) x.1 : G)) := by
    intro x y hxy
    exact Subtype.ext ((MulAut.conj t).injective hxy)
  have hle1 : Nat.card CL ≤ Nat.card CI := by
    refine Nat.card_le_card_of_injective ?_ ?_
    · exact fun x : ↥CL => ⟨(MulAut.conj t) x.1, hmapL (Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩)⟩
    · intro x y hxy
      exact hinj (Subtype.ext_iff.mp hxy)
  have hmapI : CI.map (MulAut.conj t⁻¹).toMonoidHom ≤ CL := by
    rintro x ⟨v, hv, rfl⟩
    have hswapInv : I.map (MulAut.conj t⁻¹).toMonoidHom = L := by
      rw [← hswap, Subgroup.map_map]
      have hid : (MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
          MonoidHom.id G := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [hid, Subgroup.map_id]
    exact map_conj_centralizingInV_le hVH (H.inv_mem htH)
      (Subgroup.inv_mem _ htV) hswapInv hv
  have hinjI : Function.Injective (fun x : ↥CI => ((MulAut.conj t⁻¹) x.1 : G)) := by
    intro x y hxy
    exact Subtype.ext ((MulAut.conj t⁻¹).injective hxy)
  have hle2 : Nat.card CI ≤ Nat.card CL := by
    refine Nat.card_le_card_of_injective ?_ ?_
    · exact fun x : ↥CI => ⟨(MulAut.conj t⁻¹) x.1,
        hmapI (Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩)⟩
    · intro x y hxy
      exact hinjI (Subtype.ext_iff.mp hxy)
  omega

private theorem card_mul_card_centralizingInV_le_of_inf_eq_bot {V L I : Subgroup G}
    (hVcard : Nat.card V = 27)
    (hCLCI : centralizingInV 3 H V L ⊓ centralizingInV 3 H V I = ⊥) :
    Nat.card (centralizingInV 3 H V L) * Nat.card (centralizingInV 3 H V I) ≤ 27 := by
  let CL : Subgroup G := centralizingInV 3 H V L
  let CI : Subgroup G := centralizingInV 3 H V I
  change Nat.card CL * Nat.card CI ≤ 27
  have hCLle : CL ≤ V := fun x hx => (Subgroup.mem_inf.mp hx).2
  have hCIle : CI ≤ V := fun x hx => (Subgroup.mem_inf.mp hx).2
  let f : ↥CL × ↥CI → ↥V := fun x =>
    ⟨(x.1 : G) * (x.2 : G), V.mul_mem (hCLle x.1.2) (hCIle x.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ h_eq
    have h_eq' : (a : G) * (ha : G) = (b : G) * (hb : G) := congrArg Subtype.val h_eq
    have hprod : (b : G)⁻¹ * (a : G) = (hb : G) * (ha : G)⁻¹ := by
      calc (b : G)⁻¹ * (a : G)
          = (b : G)⁻¹ * ((a : G) * (ha : G)) * (ha : G)⁻¹ := by group
        _ = (b : G)⁻¹ * ((b : G) * (hb : G)) * (ha : G)⁻¹ := by rw [h_eq']
        _ = (hb : G) * (ha : G)⁻¹ := by group
    have hmemCL : (b : G)⁻¹ * (a : G) ∈ CL := CL.mul_mem (CL.inv_mem b.2) a.2
    have hmemCI : (hb : G) * (ha : G)⁻¹ ∈ CI := CI.mul_mem hb.2 (CI.inv_mem ha.2)
    have hone : (b : G)⁻¹ * (a : G) = 1 := by
      have hmem : (b : G)⁻¹ * (a : G) ∈ CL ⊓ CI :=
        Subgroup.mem_inf.mpr ⟨hmemCL, hprod ▸ hmemCI⟩
      rw [hCLCI] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hba : a = b := by
      have h := congrArg (fun z => (b : G) * z) hone
      simpa [mul_assoc] using h
    have hbb : ha = hb := by
      have h := congrArg (fun z => z * (ha : G)) (hprod.symm.trans hone)
      simpa [mul_assoc] using h.symm
    exact Prod.ext hba hbb
  have hcard := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, hVcard] at hcard
  exact hcard

private theorem eq_three_of_dvd_27_of_mul_self_le {n : ℕ} (hdvd : n ∣ 27) (hne1 : n ≠ 1)
    (hle : n * n ≤ 27) : n = 3 := by
  have hnle5 : n ≤ 5 := by
    by_contra h
    have h6 : 6 ≤ n := by omega
    have h36 : 36 ≤ n * n := Nat.mul_le_mul h6 h6
    exact absurd (le_trans h36 hle) (by norm_num)
  interval_cases n <;> simp_all

private theorem card_centralizingInV_eq_three_of_swap
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    (hVI : D.V ≤ Subgroup.normalizer (I : Set G))
    (hIL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H I))
    {t : G} (htH : t ∈ H) (htV : t ∈ Subgroup.normalizer (D.V : Set G))
    (hswap : L.map (MulAut.conj t).toMonoidHom = I) :
    Nat.card (centralizingInV 3 H D.V L) = 3 ∧
      Nat.card (centralizingInV 3 H D.V I) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hVH : D.V ≤ H := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_left
  let CL : Subgroup G := centralizingInV 3 H D.V L
  let CI : Subgroup G := centralizingInV 3 H D.V I
  have hCLCI : CL ⊓ CI = ⊥ :=
    centralizingInV_inf_eq_bot hc D h hH2 hpσ hLI hL hLM hI hIM
  have hCIne : CI ≠ ⊥ :=
    centralizingInV_ne_bot_of_isPSLType hVH hVI D.cfg.elem D.cfg.card hIL2
  have hcardEq : Nat.card CL = Nat.card CI := by
    change Nat.card (centralizingInV 3 H D.V L) = Nat.card (centralizingInV 3 H D.V I)
    exact card_centralizingInV_eq_of_swap hVH htH htV hswap
  have hcardLe : Nat.card CL * Nat.card CI ≤ 27 := by
    change Nat.card (centralizingInV 3 H D.V L) *
      Nat.card (centralizingInV 3 H D.V I) ≤ 27
    exact card_mul_card_centralizingInV_le_of_inf_eq_bot D.cfg.card hCLCI
  have hCIle : CI ≤ D.V := fun x hx => (Subgroup.mem_inf.mp hx).2
  have hCIdvd : Nat.card CI ∣ 27 := by
    have := Subgroup.card_dvd_of_le hCIle
    rwa [D.cfg.card] at this
  have hCIneCard : Nat.card CI ≠ 1 := fun h1 =>
    hCIne (Subgroup.card_eq_one.mp h1)
  have hcardLe' : Nat.card CI * Nat.card CI ≤ 27 := by
    rw [hcardEq] at hcardLe
    exact hcardLe
  have hCI3 : Nat.card CI = 3 :=
    eq_three_of_dvd_27_of_mul_self_le hCIdvd hCIneCard hcardLe'
  exact ⟨by rw [hcardEq, hCI3], hCI3⟩

private theorem conj_actionOnStar (p : ℕ) (H V J : Subgroup G) (hVH : V ≤ H)
    (hVJ : V ≤ Subgroup.normalizer (J : Set G))
    (t : G) (htH : t ∈ H) (htJ : t ∈ Subgroup.normalizer (J : Set G))
    (v : V) (hv : t * (v : G) * t⁻¹ ∈ V) :
    let τ : MulAut ↥(starImg p H J) :=
      (starImg p H J).normalizerMonoidHom
        ⟨(QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) ⟨t, htH⟩,
          starImg_mem_normalizer_of_mem_normalizer htH htJ⟩
    τ * actionOnStar p H V J hVH hVJ v * τ⁻¹ =
      actionOnStar p H V J hVH hVJ ⟨t * (v : G) * t⁻¹, hv⟩ := by
  dsimp only
  ext x
  rw [MulAut.mul_apply, MulAut.mul_apply]
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [actionOnStar_apply]
  rw [MulAut.inv_apply]
  rw [Subgroup.normalizerMonoidHom_apply_symm_apply_coe]
  rw [actionOnStar_apply]
  have harg : (⟨t * (v : G) * t⁻¹, hVH hv⟩ : ↥H) =
      ⟨t, htH⟩ * ⟨v, hVH v.2⟩ * ⟨t, htH⟩⁻¹ := Subtype.ext rfl
  rw [harg, map_mul, map_mul, map_inv]
  group

omit [Finite G] in
private theorem range_le_inn_of_sup
    {L : Subgroup G} (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (φ : ↥D.V →* MulAut ↥(starImg 3 H L))
    {CL CI Wk : Subgroup G}
    (hCLInn : (CL.subgroupOf D.V).map φ ≤
      (MulAut.conj : ↥(starImg 3 H L) →* MulAut ↥(starImg 3 H L)).range)
    (hCIInn : (CI.subgroupOf D.V).map φ ≤
      (MulAut.conj : ↥(starImg 3 H L) →* MulAut ↥(starImg 3 H L)).range)
    (hWkInn : (Wk.subgroupOf D.V).map φ ≤
      (MulAut.conj : ↥(starImg 3 H L) →* MulAut ↥(starImg 3 H L)).range)
    (hDV : D.V = CL ⊔ CI ⊔ Wk)
    (hCLle : CL ≤ D.V) (hCIle : CI ≤ D.V) (hWkV : Wk ≤ D.V) :
    φ.range ≤ (MulAut.conj : ↥(starImg 3 H L) →* MulAut ↥(starImg 3 H L)).range := by
  rw [← Subgroup.map_top (f := φ)]
  have htop : (⊤ : Subgroup ↥D.V) =
      (CL.subgroupOf D.V) ⊔ (CI.subgroupOf D.V) ⊔ (Wk.subgroupOf D.V) := by
    rw [← Subgroup.subgroupOf_self (D.V)]
    rw [← Subgroup.subgroupOf_sup hCLle hCIle,
      ← Subgroup.subgroupOf_sup (sup_le hCLle hCIle) hWkV]
    rw [hDV]
  rw [htop, Subgroup.map_sup, Subgroup.map_sup]
  exact sup_le (sup_le hCLInn hCIInn) hWkInn

omit [Finite G] in
private theorem mul_t_fix_of_centralizes {W : Subgroup G} {t s : G}
    (ht : ∀ x ∈ W, t * x * t⁻¹ = x)
    (hs : ∀ x ∈ W, s * x * s⁻¹ = x) :
    ∀ x ∈ W, t * s * x * (t * s)⁻¹ = x := by
  intro x hx
  calc t * s * x * (t * s)⁻¹ = t * (s * x * s⁻¹) * t⁻¹ := by group
    _ = t * x * t⁻¹ := by rw [hs x hx]
    _ = x := ht x hx

omit [Finite G] in
private theorem mul_t_inv_sup_of_isE27
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {Wi Wj : Subgroup G} {ti tj : G}
    (hWiV : Wi ≤ D.V) (hWjV : Wj ≤ D.V)
    (hinvi : ∀ x ∈ Wi, ti * x * ti⁻¹ = x⁻¹)
    (hinvj : ∀ x ∈ Wj, tj * x * tj⁻¹ = x⁻¹)
    (hcommjWi : ∀ x ∈ Wi, tj * x = x * tj)
    (hcommiWj : ∀ x ∈ Wj, ti * x = x * ti) :
    ∀ x ∈ Wi ⊔ Wj, ti * tj * x * (ti * tj)⁻¹ = x⁻¹ := by
  have : IsMulCommutative ↥D.V := D.cfg.elem.1
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (CFSG.mem_sup_of_commute
    (fun a ha b hb => setLike_mul_comm (hWiV ha) (hWjV hb))).mp hx
  have ha_inv : ti * tj * a * (ti * tj)⁻¹ = a⁻¹ := by
    have h2 : tj * a * tj⁻¹ = a := by
      rw [hcommjWi a ha]
      group
    calc ti * tj * a * (ti * tj)⁻¹
        = ti * (tj * a * tj⁻¹) * ti⁻¹ := by group
      _ = ti * a * ti⁻¹ := by rw [h2]
      _ = a⁻¹ := hinvi a ha
  have hb_inv : ti * tj * b * (ti * tj)⁻¹ = b⁻¹ := by
    have h1 : ti * b * ti⁻¹ = b := by
      rw [hcommiWj b hb]
      group
    have h1inv : ti * b⁻¹ * ti⁻¹ = b⁻¹ := by
      have := congrArg Inv.inv h1
      simpa [mul_assoc] using this
    calc ti * tj * b * (ti * tj)⁻¹
        = ti * (tj * b * tj⁻¹) * ti⁻¹ := by group
      _ = ti * b⁻¹ * ti⁻¹ := by rw [hinvj b hb]
      _ = b⁻¹ := h1inv
  calc ti * tj * (a * b) * (ti * tj)⁻¹
      = (ti * tj * a * (ti * tj)⁻¹) * (ti * tj * b * (ti * tj)⁻¹) := by group
    _ = a⁻¹ * b⁻¹ := by rw [ha_inv, hb_inv]
    _ = (a * b)⁻¹ := by
      rw [mul_inv_rev]
      exact setLike_mul_comm (hWiV (Wi.inv_mem ha)) (hWjV (Wj.inv_mem hb))

private theorem le_Wk_or_le_sup_WiWj_of_invariant
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {Wi Wj Wk D' : Subgroup G} {u : G}
    (hWiV : Wi ≤ D.V) (hWjV : Wj ≤ D.V) (hWkV : Wk ≤ D.V)
    (hV : D.V = Wk ⊔ (Wi ⊔ Wj))
    (hDV : D' ≤ D.V) (hDcard : Nat.card D' = 3)
    (hDt : ∀ x ∈ D', u * x * u⁻¹ ∈ D')
    (hfixWk : ∀ x ∈ Wk, u * x * u⁻¹ = x)
    (hinvWij : ∀ x ∈ Wi ⊔ Wj, u * x * u⁻¹ = x⁻¹) :
    D' ≤ Wk ∨ D' ≤ Wi ⊔ Wj := by
  have : IsMulCommutative ↥D.V := D.cfg.elem.1
  have hFJ : (Wi ⊔ Wj : Subgroup G) ≤ D.V := sup_le hWiV hWjV
  refine le_fixed_or_eq_inverted hV ?_ ?_ ?_ ?_ ?_ hDV hDcard hDt
  · intro f hf j hj
    exact setLike_mul_comm (hWkV hf) (hFJ hj)
  · intro f hf
    exact D.cfg.elem.2 f (hWkV hf)
  · intro j hj
    exact D.cfg.elem.2 j (hFJ hj)
  · intro x hx
    exact hfixWk x hx
  · intro x hx
    exact hinvWij x hx

omit [Finite G] in
private theorem map_mul_conj_eq_left_of_swaps {L I : Subgroup G} {t s : G}
    (hs : L.map (MulAut.conj s).toMonoidHom = I)
    (ht : I.map (MulAut.conj t).toMonoidHom = L) :
    L.map (MulAut.conj (t * s)).toMonoidHom = L := by
  have hcomp : (MulAut.conj (t * s)).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp (MulAut.conj s).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp, ← Subgroup.map_map, hs, ht]

private theorem map_conj_eq_left_of_swap
    {L I : Subgroup G} (hS : {J : Subgroup G | IsPComponentIn p J H ∧ ¬ J ≤ M} = {L, I})
    (hLI : L ≠ I) (hI : IsPComponentIn p I H) (hIM : ¬ I ≤ M)
    {t : G} (htH : t ∈ H) (htM : t ∈ M)
    (hs : L.map (MulAut.conj t).toMonoidHom = I) :
    I.map (MulAut.conj t).toMonoidHom = L := by
  rcases map_conj_eq_left_or_right_of_pair hS hI hIM htH htM with h | h
  · exact h
  · exfalso
    exact hLI (Subgroup.map_injective (MulAut.conj t).injective (hs.trans h.symm))

private theorem map_le_range_conj_of_psl28 {X V : Type} [Group X] [Finite X] [Group V]
    (eX : X ≃* CFSG.AGLEmbedding.PSL2GF 2 3) (φ : V →* MulAut X)
    {W : Subgroup V} (hcardW : Nat.card W = 3) {w : V} (hwW : w ∈ W) (hw1 : w ≠ 1)
    (hpow : ∀ x ∈ W, x ^ 3 = 1)
    {τ : MulAut X} (hτ : τ * φ w * τ⁻¹ = (φ w)⁻¹) :
    W.map φ ≤ (MulAut.conj : X →* MulAut X).range := by
  have hw3 : w ^ 3 = 1 := hpow w hwW
  have hworder : orderOf w = 3 := by
    have hdvd : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
    have hle : orderOf w ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have hne : orderOf w ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.mp h)
    interval_cases orderOf w <;> simp_all
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hcardW]; norm_num)
  have hz : Subgroup.zpowers w = W := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwW)
    rw [Nat.card_zpowers, hworder, hcardW]
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨v, hv, rfl⟩
  have hvz : v ∈ Subgroup.zpowers w := by rw [hz]; exact hv
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvz
  have hvEq : v = w ^ k := hk.symm
  rw [hvEq, map_zpow]
  have hφw3 : (φ w) ^ 3 = 1 := by rw [← map_pow, hw3, map_one]
  exact Subgroup.zpow_mem _ (mem_range_conj_of_inv_of_psl28 eX hφw3 hτ) k

private theorem Wk_map_le_range_conj_of_two_swap
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {L Wk CL : Subgroup G}
    (eL : ↥(starImg 3 H L) ≃* CFSG.AGLEmbedding.PSL2GF 2 3)
    (hVH : D.V ≤ H) (hVL : D.V ≤ Subgroup.normalizer (L : Set G))
    (hWkV : Wk ≤ D.V) (hcardWk : Nat.card Wk = 3)
    {tk : G} (hIHk : tk ∈ H) (hCVk : tk ∈ Subgroup.normalizer (D.V : Set G))
    (hfixK : L.map (MulAut.conj tk).toMonoidHom = L)
    (hinvWk : ∀ x ∈ Wk, tk * x * tk⁻¹ = x⁻¹)
    (hnotWkCL : ¬ Wk ≤ CL) :
    (Wk.subgroupOf D.V).map (actionOnStar 3 H D.V L hVH hVL) ≤
      (MulAut.conj : ↥(starImg 3 H L) →* MulAut ↥(starImg 3 H L)).range := by
  obtain ⟨w, hwWk, hwCL⟩ := Set.not_subset.mp hnotWkCL
  have hw1 : w ≠ 1 := fun h => hwCL (h ▸ CL.one_mem)
  let wV : ↥D.V := ⟨w, hWkV hwWk⟩
  have hwV1 : wV ≠ 1 := by
    intro h
    exact hw1 (Subtype.ext_iff.mp h)
  have hpow : ∀ x ∈ Wk.subgroupOf D.V, x ^ 3 = 1 := by
    intro x hx
    have hxW : (x : G) ∈ Wk := Subgroup.mem_subgroupOf.mp hx
    apply Subtype.ext
    simpa using D.cfg.elem.2 (x : G) (hWkV hxW)
  let τk : MulAut ↥(starImg 3 H L) :=
    (starImg 3 H L).normalizerMonoidHom
      ⟨(QuotientGroup.mk' (primeComplementCore (G := ↥H) 3)) ⟨tk, hIHk⟩,
        starImg_mem_normalizer_of_mem_normalizer hIHk
          (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfixK)⟩
  have hτk : τk * (actionOnStar 3 H D.V L hVH hVL) wV * τk⁻¹ =
      ((actionOnStar 3 H D.V L hVH hVL) wV)⁻¹ := by
    have hmem : tk * w * tk⁻¹ ∈ D.V :=
      (Subgroup.mem_normalizer_iff.mp hCVk w).mp (hWkV hwWk)
    have hform := conj_actionOnStar 3 H D.V L hVH hVL tk hIHk
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfixK) wV hmem
    dsimp only [τk]
    rw [hform]
    have hsub : (⟨tk * w * tk⁻¹, hmem⟩ : ↥D.V) = wV⁻¹ := by
      apply Subtype.ext
      simpa [wV] using hinvWk w hwWk
    rw [hsub, map_inv]
  have hcardWk' : Nat.card (Wk.subgroupOf D.V) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWkV).toEquiv, hcardWk]
  simpa using map_le_range_conj_of_psl28 eL (actionOnStar 3 H D.V L hVH hVL)
    hcardWk' (Subgroup.mem_subgroupOf.mpr hwWk) hwV1 hpow hτk

private theorem CI_map_le_range_conj_of_two_swap
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {L CL CI : Subgroup G}
    (eL : ↥(starImg 3 H L) ≃* CFSG.AGLEmbedding.PSL2GF 2 3)
    (hVH : D.V ≤ H) (hVL : D.V ≤ Subgroup.normalizer (L : Set G))
    (hCIle : CI ≤ D.V) (hcardCI : Nat.card CI = 3)
    {ti tj : G} (hIHi : ti ∈ H) (hIHj : tj ∈ H)
    (hCVi : ti ∈ Subgroup.normalizer (D.V : Set G))
    (hCVj : tj ∈ Subgroup.normalizer (D.V : Set G))
    (hfixIJ : L.map (MulAut.conj (ti * tj)).toMonoidHom = L)
    (hinvCI : ∀ x ∈ CI, ti * tj * x * (ti * tj)⁻¹ = x⁻¹)
    (hnotCICL : ¬ CI ≤ CL) :
    (CI.subgroupOf D.V).map (actionOnStar 3 H D.V L hVH hVL) ≤
      (MulAut.conj : ↥(starImg 3 H L) →* MulAut ↥(starImg 3 H L)).range := by
  obtain ⟨c, hcCI, hcCL⟩ := Set.not_subset.mp hnotCICL
  have hc1 : c ≠ 1 := fun h => hcCL (h ▸ CL.one_mem)
  let cV : ↥D.V := ⟨c, hCIle hcCI⟩
  have hcV1 : cV ≠ 1 := by
    intro h
    exact hc1 (Subtype.ext_iff.mp h)
  have hpow : ∀ x ∈ CI.subgroupOf D.V, x ^ 3 = 1 := by
    intro x hx
    have hxI : (x : G) ∈ CI := Subgroup.mem_subgroupOf.mp hx
    apply Subtype.ext
    simpa using D.cfg.elem.2 (x : G) (hCIle hxI)
  have hCVij : ti * tj ∈ Subgroup.normalizer (D.V : Set G) :=
    Subgroup.mul_mem _ hCVi hCVj
  let τij : MulAut ↥(starImg 3 H L) :=
    (starImg 3 H L).normalizerMonoidHom
      ⟨(QuotientGroup.mk' (primeComplementCore (G := ↥H) 3)) ⟨ti * tj, H.mul_mem hIHi hIHj⟩,
        starImg_mem_normalizer_of_mem_normalizer (H.mul_mem hIHi hIHj)
          (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfixIJ)⟩
  have hτij : τij * (actionOnStar 3 H D.V L hVH hVL) cV * τij⁻¹ =
      ((actionOnStar 3 H D.V L hVH hVL) cV)⁻¹ := by
    have hmem : ti * tj * c * (ti * tj)⁻¹ ∈ D.V :=
      (Subgroup.mem_normalizer_iff.mp hCVij c).mp (hCIle hcCI)
    have hform := conj_actionOnStar 3 H D.V L hVH hVL (ti * tj)
      (H.mul_mem hIHi hIHj) (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfixIJ) cV hmem
    dsimp only [τij]
    rw [hform]
    have hsub : (⟨ti * tj * c * (ti * tj)⁻¹, hmem⟩ : ↥D.V) = cV⁻¹ := by
      apply Subtype.ext
      simpa [cV] using hinvCI c hcCI
    rw [hsub, map_inv]
  have hcardCI' : Nat.card (CI.subgroupOf D.V) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCIle).toEquiv, hcardCI]
  simpa using map_le_range_conj_of_psl28 eL (actionOnStar 3 H D.V L hVH hVL)
    hcardCI' (Subgroup.mem_subgroupOf.mpr hcCI) hcV1 hpow hτij

private theorem sup_centralizingInV_eq_sup_of_two_swap
    {V Wi Wj Wk CL CI : Subgroup G}
    (hVeq : V = Wi ⊔ Wj ⊔ Wk)
    (hCLCI : CL ⊓ CI = ⊥)
    (hcardCL : Nat.card CL = 3) (hcardCI : Nat.card CI = 3)
    (hcommCLCI : ∀ a ∈ CL, ∀ b ∈ CI, Commute a b)
    (hcommWiWj : ∀ a ∈ Wi, ∀ b ∈ Wj, Commute a b)
    (hdisjWiWj : Wi ⊓ Wj = ⊥)
    (hcardWi : Nat.card Wi = 3) (hcardWj : Nat.card Wj = 3)
    (hfixCL : CL ≤ Wk ∨ CL ≤ Wi ⊔ Wj)
    (hfixCI : CI ≤ Wk ∨ CI ≤ Wi ⊔ Wj)
    (hnotCLWk : ¬ CL ≤ Wk) (hnotCIWk : ¬ CI ≤ Wk) :
    (CL ⊔ CI = Wi ⊔ Wj) ∧ V = CL ⊔ CI ⊔ Wk := by
  have hCLsub : CL ≤ Wi ⊔ Wj := by
    rcases hfixCL with h | h
    · exact absurd h hnotCLWk
    · exact h
  have hCIsub : CI ≤ Wi ⊔ Wj := by
    rcases hfixCI with h | h
    · exact absurd h hnotCIWk
    · exact h
  have hsupEq : CL ⊔ CI = Wi ⊔ Wj := by
    have hle : CL ⊔ CI ≤ Wi ⊔ Wj := sup_le hCLsub hCIsub
    have hcardCLCI : Nat.card ↥(CL ⊔ CI) = 9 := by
      rw [CFSG.card_sup_eq_mul_of_commute CL CI hcommCLCI hCLCI, hcardCL, hcardCI]
    have hcardWiWj : Nat.card ↥(Wi ⊔ Wj) = 9 := by
      rw [CFSG.card_sup_eq_mul_of_commute Wi Wj hcommWiWj hdisjWiWj, hcardWi, hcardWj]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardCLCI, hcardWiWj])
  exact ⟨hsupEq, by rw [hVeq, hsupEq]⟩

private theorem two_swap_kernel
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {L CL : Subgroup G}
    (hVH : D.V ≤ H) (hVL : D.V ≤ Subgroup.normalizer (L : Set G))
    (hCLle : CL ≤ D.V) (hCLker : CL = centralizingInV 3 H D.V L)
    (hcardCL : Nat.card CL = 3) :
    (CL.subgroupOf D.V).map (actionOnStar 3 H D.V L hVH hVL) = ⊥ ∧
      Nat.card (actionOnStar 3 H D.V L hVH hVL).ker = 3 := by
  let φ : ↥D.V →* MulAut ↥(starImg 3 H L) := actionOnStar 3 H D.V L hVH hVL
  have hkerMap : φ.ker.map D.V.subtype = CL := by
    rw [hCLker]
    simpa [φ] using (centralizingInV_eq_ker_map 3 H D.V L hVH hVL).symm
  have hCLmap : (CL.subgroupOf D.V).map D.V.subtype = CL := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCLle]
  have hkerSub : CL.subgroupOf D.V = φ.ker :=
    Subgroup.map_injective D.V.subtype_injective (by rw [hCLmap, hkerMap])
  have hCLInn : (CL.subgroupOf D.V).map φ = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr hkerSub.le
  have hkerCard : Nat.card φ.ker = 3 := by
    rw [← Subgroup.card_map_of_injective D.V.subtype_injective, hkerMap, hcardCL]
  exact ⟨hCLInn, hkerCard⟩

private theorem false_of_elemAbelian_subgroup_card_nine_of_psl28
    {X : Type} [Group X] [Finite X] (eX : X ≃* CFSG.AGLEmbedding.PSL2GF 2 3)
    {B : Subgroup (MulAut X)} (hB : IsElemAbelian 3 B) (hcard : Nat.card B = 9)
    (hInn : B ≤ (MulAut.conj : X →* MulAut X).range) (hZ : center X = ⊥) : False := by
  have hInj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have hker : (MulAut.conj : X →* MulAut X).ker = center X := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
      constructor
      · intro h y
        have hy : x * y * x⁻¹ = y := by
          have hc := congrArg (fun f : MulAut X => f y) h
          simpa [MulAut.conj_apply] using hc
        have hxy : x * y = y * x := by
          calc x * y = (x * y * x⁻¹) * x := by group
            _ = y * x := by rw [hy]
        exact hxy.symm
      · intro h
        ext y
        simp only [MulAut.conj_apply, MulAut.one_apply]
        rw [← h y]
        group
    rw [hker, hZ]
  let A : Subgroup X := B.comap (MulAut.conj : X →* MulAut X)
  have hAea : IsElemAbelian 3 A := hB.comap hInj
  have hAeq : A.map (MulAut.conj : X →* MulAut X) = B := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hInn
  have hAcard : Nat.card A = 9 := by
    rw [← Subgroup.card_map_of_injective hInj, hAeq, hcard]
  exact card_ne_nine_of_isElemAbelian_of_psl28 eX hAea hAcard

private theorem false_of_two_swap_range
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {L Wk CL CI : Subgroup G}
    (eL : ↥(starImg 3 H L) ≃* CFSG.AGLEmbedding.PSL2GF 2 3)
    (hVH : D.V ≤ H) (hVL : D.V ≤ Subgroup.normalizer (L : Set G))
    (hDV : D.V = CL ⊔ CI ⊔ Wk)
    (hCLInn : (CL.subgroupOf D.V).map (actionOnStar 3 H D.V L hVH hVL) = ⊥)
    (hkerCard : Nat.card (actionOnStar 3 H D.V L hVH hVL).ker = 3)
    (hWkInn : (Wk.subgroupOf D.V).map (actionOnStar 3 H D.V L hVH hVL) ≤
      (MulAut.conj : ↥(starImg 3 H L) →* MulAut ↥(starImg 3 H L)).range)
    (hCIInn : (CI.subgroupOf D.V).map (actionOnStar 3 H D.V L hVH hVL) ≤
      (MulAut.conj : ↥(starImg 3 H L) →* MulAut ↥(starImg 3 H L)).range)
    (hZL : center ↥(starImg 3 H L) = ⊥) : False := by
  let φ : ↥D.V →* MulAut ↥(starImg 3 H L) := actionOnStar 3 H D.V L hVH hVL
  let Inn : Subgroup (MulAut ↥(starImg 3 H L)) :=
    (MulAut.conj : ↥(starImg 3 H L) →* MulAut ↥(starImg 3 H L)).range
  have hCLle : CL ≤ D.V := by
    rw [hDV]
    exact le_trans le_sup_left le_sup_left
  have hCIle : CI ≤ D.V := by
    rw [hDV]
    exact le_trans le_sup_right le_sup_left
  have hWkV : Wk ≤ D.V := by rw [hDV]; exact le_sup_right
  have hrange : φ.range ≤ Inn := by
    simpa [Inn, φ] using range_le_inn_of_sup D φ (by rw [hCLInn]; exact bot_le)
      hCIInn hWkInn hDV hCLle hCIle hWkV
  have hEtop : IsElemAbelian 3 (⊤ : Subgroup ↥D.V) := by
    simpa [Subgroup.subgroupOf_self] using D.cfg.elem.subgroupOf D.V
  have hEa : IsElemAbelian 3 φ.range := by
    simpa [Subgroup.map_top] using hEtop.map φ
  have hcardRange : Nat.card φ.range = 9 := by
    have hmul := Subgroup.card_ker_mul_card_range φ
    rw [hkerCard, D.cfg.card] at hmul
    omega
  exact false_of_elemAbelian_subgroup_card_nine_of_psl28 eL hEa hcardRange hrange hZL

private theorem false_of_two_swaps
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {L : Subgroup G} (hZL : center ↥(starImg 3 H L) = ⊥)
    (hLL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H L))
    {Wi Wj Wk CL CI : Subgroup G} {ti tj tk : G}
    (hWkV : Wk ≤ D.V) (hcardWi : Nat.card Wi = 3) (hcardWj : Nat.card Wj = 3)
    (hcardWk : Nat.card Wk = 3)
    (hVeq : D.V = Wi ⊔ Wj ⊔ Wk)
    (hCLle : CL ≤ D.V) (hCIle : CI ≤ D.V)
    (hCLCI : CL ⊓ CI = ⊥) (hCIne : CI ≠ ⊥) (hcardCL : Nat.card CL = 3)
    (hCLker : CL = centralizingInV 3 H D.V L) (hcardCI : Nat.card CI = 3)
    (hcommCLCI : ∀ a ∈ CL, ∀ b ∈ CI, Commute a b)
    (hcommWiWj : ∀ a ∈ Wi, ∀ b ∈ Wj, Commute a b)
    (hdisjWiWj : Wi ⊓ Wj = ⊥) (hfixCL : CL ≤ Wk ∨ CL ≤ Wi ⊔ Wj)
    (hfixCI : CI ≤ Wk ∨ CI ≤ Wi ⊔ Wj)
    (hnotCLWk : ¬ CL ≤ Wk) (hnotCIWk : ¬ CI ≤ Wk)
    (hfixK : L.map (MulAut.conj tk).toMonoidHom = L)
    (hfixIJ : L.map (MulAut.conj (ti * tj)).toMonoidHom = L)
    (hinvWk : ∀ x ∈ Wk, tk * x * tk⁻¹ = x⁻¹)
    (hinvWij : ∀ x ∈ Wi ⊔ Wj, ti * tj * x * (ti * tj)⁻¹ = x⁻¹)
    (hIHk : tk ∈ H) (hCVk : tk ∈ Subgroup.normalizer (D.V : Set G))
    (hIHi : ti ∈ H) (hCVi : ti ∈ Subgroup.normalizer (D.V : Set G))
    (hIHj : tj ∈ H) (hCVj : tj ∈ Subgroup.normalizer (D.V : Set G))
    (hVH : D.V ≤ H) (hVL : D.V ≤ Subgroup.normalizer (L : Set G)) :
    False := by
  obtain ⟨eL⟩ := hLL2
  obtain ⟨hsupEq, hDV⟩ := sup_centralizingInV_eq_sup_of_two_swap hVeq hCLCI hcardCL hcardCI
    hcommCLCI hcommWiWj hdisjWiWj hcardWi hcardWj hfixCL hfixCI hnotCLWk hnotCIWk
  obtain ⟨hCLInn, hkerCard⟩ := two_swap_kernel D hVH hVL hCLle hCLker hcardCL
  have hnotWkCL : ¬ Wk ≤ CL := by
    intro hle
    have hEq : Wk = CL := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardWk, hcardCL])
    exact hnotCLWk (hEq ▸ le_rfl)
  have hWkInn := Wk_map_le_range_conj_of_two_swap D eL hVH hVL hWkV hcardWk
    hIHk hCVk hfixK hinvWk hnotWkCL
  have hCIsub : CI ≤ Wi ⊔ Wj := by
    rcases hfixCI with h | h
    · exact absurd h hnotCIWk
    · exact h
  have hinvCI : ∀ x ∈ CI, ti * tj * x * (ti * tj)⁻¹ = x⁻¹ :=
    fun x hx => hinvWij x (hCIsub hx)
  have hnotCICL : ¬ CI ≤ CL := by
    intro hle
    have hbot : CI ≤ ⊥ := by rw [← hCLCI]; exact le_inf hle le_rfl
    exact hCIne (le_bot_iff.mp hbot)
  have hCIInn := CI_map_le_range_conj_of_two_swap D eL hVH hVL hCIle hcardCI
    hIHi hIHj hCVi hCVj hfixIJ hinvCI hnotCICL
  exact false_of_two_swap_range D eL hVH hVL hDV hCLInn hkerCard hWkInn hCIInn hZL

private theorem pair_three_setup₁
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    (hS : {J : Subgroup G | IsPComponentIn 3 J H ∧ ¬ J ≤ M} = {L, I}) :
    D.V ≤ H ∧ D.V ≤ Subgroup.normalizer (L : Set G) ∧
      D.V ≤ Subgroup.normalizer (I : Set G) ∧
      D.t₁ ∈ Subgroup.normalizer (D.V : Set G) ∧
      D.t₂ ∈ Subgroup.normalizer (D.V : Set G) ∧
      D.t₃ ∈ Subgroup.normalizer (D.V : Set G) ∧
      D.t₁ ∈ H ∧ D.t₂ ∈ H ∧ D.t₃ ∈ H ∧
      D.W₁ ≤ D.V ∧ D.W₂ ≤ D.V ∧ D.W₃ ≤ D.V := by
  have hVH : D.V ≤ H := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_left
  have hVL : D.V ≤ Subgroup.normalizer (L : Set G) :=
    V_le_normalizer_of_pair hc D hLI hL hLM hI hIM hS
  have hVI : D.V ≤ Subgroup.normalizer (I : Set G) :=
    V_le_normalizer_of_pair (L := I) (I := L) hc D (Ne.symm hLI) hI hIM hL hLM
      (by rw [Set.pair_comm]; exact hS)
  refine ⟨hVH, hVL, hVI, ?_, ?_, ?_, (D.t₁_mem hc.data).1, (D.t₂_mem hc.data).1,
    (D.t₃_mem hc.data).1, ?_, ?_, ?_⟩
  · exact D.cfg.tripleNormalizer_le_normalizer D.cfg.t₁_mem_tripleNormalizer
  · exact D.cfg.tripleNormalizer_le_normalizer D.cfg.t₂_mem_tripleNormalizer
  · exact D.cfg.tripleNormalizer_le_normalizer D.cfg.t₃_mem_tripleNormalizer
  · rw [D.cfg.join]; exact le_sup_left.trans le_sup_left
  · rw [D.cfg.join]; exact le_sup_right.trans le_sup_left
  · rw [D.cfg.join]; exact le_sup_right

private theorem pair_three_setup₂
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    {CL CI : Subgroup G} (hCLker : CL = centralizingInV 3 H D.V L)
    (hCIker : CI = centralizingInV 3 H D.V I)
    (hVI : D.V ≤ Subgroup.normalizer (I : Set G))
    (hIL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H I)) :
    CL ⊓ CI = ⊥ ∧ CI ≠ ⊥ ∧
      (∀ a ∈ CL, ∀ b ∈ CI, Commute a b) ∧
      D.W₁ ⊓ D.W₂ = ⊥ ∧ D.W₁ ⊓ D.W₃ = ⊥ ∧ D.W₂ ⊓ D.W₃ = ⊥ := by
  have : IsMulCommutative ↥D.V := D.cfg.elem.1
  have hVH : D.V ≤ H := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_left
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hCLker, hCIker]
    exact centralizingInV_inf_eq_bot hc D h hH2 hpσ hLI hL hLM hI hIM
  · rw [hCIker]
    exact centralizingInV_ne_bot_of_isPSLType hVH hVI D.cfg.elem D.cfg.card hIL2
  · intro a ha b hb
    rw [hCLker] at ha
    rw [hCIker] at hb
    exact setLike_mul_comm (Subgroup.mem_inf.mp ha).2 (Subgroup.mem_inf.mp hb).2
  · have hle : D.W₁ ⊓ D.W₂ ≤ D.W₁ ⊓ (D.W₂ ⊔ D.W₃) :=
      inf_le_inf_left D.W₁ le_sup_left
    exact le_bot_iff.mp (hle.trans_eq (W1_inf_sup_W2W3_eq_bot D))
  · have hle : D.W₁ ⊓ D.W₃ ≤ D.W₁ ⊓ (D.W₂ ⊔ D.W₃) :=
      inf_le_inf_left D.W₁ le_sup_right
    exact le_bot_iff.mp (hle.trans_eq (W1_inf_sup_W2W3_eq_bot D))
  · have hle : D.W₂ ⊓ D.W₃ ≤ D.W₂ ⊓ (D.W₁ ⊔ D.W₃) :=
      inf_le_inf_left D.W₂ le_sup_right
    exact le_bot_iff.mp (hle.trans_eq (W2_inf_sup_W1W3_eq_bot D))

private theorem two_swap_case_C
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {L Wi Wj Wk C : Subgroup G} {ti tj tk : G}
    (hVH : D.V ≤ H)
    (hWiV : Wi ≤ D.V) (hWjV : Wj ≤ D.V) (hWkV : Wk ≤ D.V)
    (hV : D.V = Wk ⊔ (Wi ⊔ Wj))
    (hCle : C ≤ D.V) (hCker : C = centralizingInV 3 H D.V L) (hcardC : Nat.card C = 3)
    (hIHk : tk ∈ H) (hCVk : tk ∈ Subgroup.normalizer (D.V : Set G))
    (hIHi : ti ∈ H) (hCVi : ti ∈ Subgroup.normalizer (D.V : Set G))
    (hIHj : tj ∈ H) (hCVj : tj ∈ Subgroup.normalizer (D.V : Set G))
    (hfixK : L.map (MulAut.conj tk).toMonoidHom = L)
    (hfixIJ : L.map (MulAut.conj (ti * tj)).toMonoidHom = L)
    (hfixWk : ∀ x ∈ Wk, ti * tj * x * (ti * tj)⁻¹ = x)
    (hinvWij : ∀ x ∈ Wi ⊔ Wj, ti * tj * x * (ti * tj)⁻¹ = x⁻¹) :
    C ≤ Wk ∨ C ≤ Wi ⊔ Wj := by
  have hCinvK : ∀ x ∈ C, tk * x * tk⁻¹ ∈ C := by
    intro x hx
    rw [hCker] at hx ⊢
    exact map_conj_centralizingInV_le hVH hIHk hCVk hfixK hx
  have hCinvIJ : ∀ x ∈ C, ti * tj * x * (ti * tj)⁻¹ ∈ C := by
    intro x hx
    rw [hCker] at hx ⊢
    exact map_conj_centralizingInV_le hVH (H.mul_mem hIHi hIHj)
      (Subgroup.mul_mem _ hCVi hCVj) hfixIJ hx
  exact le_Wk_or_le_sup_WiWj_of_invariant D hWiV hWjV hWkV hV hCle hcardC
    hCinvIJ hfixWk hinvWij

private theorem not_le_sup_of_centralizingInV
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {L I Wj Wk CL CI : Subgroup G} {ti : G}
    (hVH : D.V ≤ H) (hIHi : ti ∈ H)
    (hCVi : ti ∈ Subgroup.normalizer (D.V : Set G))
    (hCLker : CL = centralizingInV 3 H D.V L)
    (hCIker : CI = centralizingInV 3 H D.V I)
    (hCLCI : CL ⊓ CI = ⊥) (hcardCL : Nat.card CL = 3)
    (hswap : L.map (MulAut.conj ti).toMonoidHom = I)
    (hcomm : ∀ x ∈ Wj ⊔ Wk, ti * x = x * ti)
    (hle : CL ≤ Wj ⊔ Wk) : False := by
  have hleCI : CL ≤ CI := by
    intro x hx
    have hx' : x ∈ centralizingInV 3 H D.V L := by rw [← hCLker]; exact hx
    have hmem := map_conj_centralizingInV_le hVH hIHi hCVi hswap hx'
    rw [← hCIker] at hmem
    have hxeq : ti * x * ti⁻¹ = x := by
      rw [hcomm x (hle hx)]
      group
    rwa [hxeq] at hmem
  have hbot : CL = ⊥ := by
    have hleBot : CL ≤ ⊥ := by rw [← hCLCI]; exact le_inf le_rfl hleCI
    exact le_bot_iff.mp hleBot
  rw [hbot] at hcardCL
  simp at hcardCL

private theorem false_of_two_swaps_case
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {L I Wi Wj Wk CL CI : Subgroup G} {ti tj tk : G}
    (hZL : center ↥(starImg 3 H L) = ⊥)
    (hLL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H L))
    (hWiV : Wi ≤ D.V) (hWjV : Wj ≤ D.V) (hWkV : Wk ≤ D.V)
    (hcardWi : Nat.card Wi = 3) (hcardWj : Nat.card Wj = 3) (hcardWk : Nat.card Wk = 3)
    (hVeq : D.V = Wi ⊔ Wj ⊔ Wk)
    (hCLle : CL ≤ D.V) (hCIle : CI ≤ D.V)
    (hCLCI : CL ⊓ CI = ⊥) (hCIne : CI ≠ ⊥) (hcardCL : Nat.card (centralizingInV 3 H D.V L) = 3)
    (hCLker : CL = centralizingInV 3 H D.V L)
    (hCIker : CI = centralizingInV 3 H D.V I)
    (hcardCI : Nat.card (centralizingInV 3 H D.V I) = 3)
    (hcommCLCI : ∀ a ∈ CL, ∀ b ∈ CI, Commute a b)
    (hcommWiWj : ∀ a ∈ Wi, ∀ b ∈ Wj, Commute a b)
    (hdisjWiWj : Wi ⊓ Wj = ⊥)
    (hfixK : L.map (MulAut.conj tk).toMonoidHom = L)
    (hfixIK : I.map (MulAut.conj tk).toMonoidHom = I)
    (hfixIJ : L.map (MulAut.conj (ti * tj)).toMonoidHom = L)
    (hfixIJI : I.map (MulAut.conj (ti * tj)).toMonoidHom = I)
    (hfixWk : ∀ x ∈ Wk, ti * tj * x * (ti * tj)⁻¹ = x)
    (hinvWk : ∀ x ∈ Wk, tk * x * tk⁻¹ = x⁻¹)
    (hinvWij : ∀ x ∈ Wi ⊔ Wj, ti * tj * x * (ti * tj)⁻¹ = x⁻¹)
    (hnotCLWk : ¬ CL ≤ Wk) (hnotCIWk : ¬ CI ≤ Wk)
    (hIHk : tk ∈ H) (hCVk : tk ∈ Subgroup.normalizer (D.V : Set G))
    (hIHi : ti ∈ H) (hCVi : ti ∈ Subgroup.normalizer (D.V : Set G))
    (hIHj : tj ∈ H) (hCVj : tj ∈ Subgroup.normalizer (D.V : Set G))
    (hVH : D.V ≤ H) (hVL : D.V ≤ Subgroup.normalizer (L : Set G))
    (hV : D.V = Wk ⊔ (Wi ⊔ Wj)) : False := by
  have hcardCL' : Nat.card CL = 3 := by rw [hCLker]; exact hcardCL
  have hcardCI' : Nat.card CI = 3 := by rw [hCIker]; exact hcardCI
  have hfixCL : CL ≤ Wk ∨ CL ≤ Wi ⊔ Wj :=
    two_swap_case_C D hVH hWiV hWjV hWkV hV hCLle hCLker hcardCL' hIHk hCVk hIHi hCVi
      hIHj hCVj hfixK hfixIJ hfixWk hinvWij
  have hfixCI : CI ≤ Wk ∨ CI ≤ Wi ⊔ Wj :=
    two_swap_case_C D hVH hWiV hWjV hWkV hV hCIle hCIker hcardCI' hIHk hCVk hIHi hCVi
      hIHj hCVj hfixIK hfixIJI hfixWk hinvWij
  exact false_of_two_swaps D hZL hLL2 hWkV hcardWi hcardWj hcardWk hVeq
    hCLle hCIle hCLCI hCIne hcardCL' hCLker hcardCI' hcommCLCI hcommWiWj hdisjWiWj
    hfixCL hfixCI hnotCLWk hnotCIWk hfixK hfixIJ hinvWk hinvWij
    hIHk hCVk hIHi hCVi hIHj hCVj hVH hVL

private theorem false_of_one_swap_case
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {L I Wi Wj Wk CL CI : Subgroup G} {ti : G}
    (hVH : D.V ≤ H) (hIHi : ti ∈ H)
    (hCVi : ti ∈ Subgroup.normalizer (D.V : Set G))
    (hswapI : L.map (MulAut.conj ti).toMonoidHom = I)
    (hCLker : CL = centralizingInV 3 H D.V L)
    (hCIker : CI = centralizingInV 3 H D.V I)
    (hCLCI : CL ⊓ CI = ⊥) (hcardCL : Nat.card CL = 3)
    (hcommPlane : ∀ x ∈ Wj ⊔ Wk, ti * x = x * ti)
    (hnotWi : ¬ CL ≤ Wi)
    (hfixj : CL ≤ Wj ∨ CL ≤ Wi ⊔ Wk)
    (hfixk : CL ≤ Wk ∨ CL ≤ Wi ⊔ Wj)
    (hinter : (Wi ⊔ Wk) ⊓ (Wi ⊔ Wj) = Wi) : False := by
  have hnotPlane : ¬ CL ≤ Wj ⊔ Wk := fun hle =>
    not_le_sup_of_centralizingInV D hVH hIHi hCVi hCLker hCIker hCLCI hcardCL
      hswapI hcommPlane hle
  exact false_of_one_swap hnotWi hnotPlane hfixj hfixk hinter

private theorem pair_three_cards
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    (hVI : D.V ≤ Subgroup.normalizer (I : Set G))
    (hIL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H I))
    {t : G} (htH : t ∈ H) (htV : t ∈ Subgroup.normalizer (D.V : Set G))
    (hswap : L.map (MulAut.conj t).toMonoidHom = I) :
    Nat.card (centralizingInV 3 H D.V L) = 3 ∧
      Nat.card (centralizingInV 3 H D.V I) = 3 :=
  card_centralizingInV_eq_three_of_swap hc D h hH2 hpσ hLI hL hLM hI hIM hVI hIL2 htH htV hswap

private theorem fix_I_of_fix_L {L I : Subgroup G}
    (hS : {J : Subgroup G | IsPComponentIn 3 J H ∧ ¬ J ≤ M} = {L, I})
    (hLI : L ≠ I) (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    {t : G} (htH : t ∈ H) (htM : t ∈ M)
    (hfixL : L.map (MulAut.conj t).toMonoidHom = L) :
    I.map (MulAut.conj t).toMonoidHom = I := by
  rcases map_conj_eq_left_or_right_of_pair hS hI hIM htH htM with h | h
  · exfalso
    exact hLI (Subgroup.map_injective (MulAut.conj t).injective (hfixL.trans h.symm))
  · exact h

private theorem not_le_W_of_centralizingInV_CL
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {L W CL : Subgroup G}
    (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M) (hWV : W ≤ D.V)
    (hW : Nat.card W = 3) (hCW : Subgroup.centralizer (W : Set G) ≤ M)
    (hCLker : CL = centralizingInV 3 H D.V L)
    (hcardCL : Nat.card (centralizingInV 3 H D.V L) = 3) : ¬ CL ≤ W := by
  rw [hCLker]
  exact not_le_W_of_centralizingInV hc D hL hLM hWV hW hCW hcardCL

private theorem false_of_three_swaps_case
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    (hIL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H I))
    (hS : {J : Subgroup G | IsPComponentIn 3 J H ∧ ¬ J ≤ M} = {L, I})
    {CL CI : Subgroup G} (hCLker : CL = centralizingInV 3 H D.V L)
    (hCIker : CI = centralizingInV 3 H D.V I)
    (s1 : L.map (MulAut.conj D.t₁).toMonoidHom = I)
    (s2 : L.map (MulAut.conj D.t₂).toMonoidHom = I)
    (s3 : L.map (MulAut.conj D.t₃).toMonoidHom = I) : False := by
  obtain ⟨hVH, hVL, hVI, hCV1, hCV2, hCV3, hIH1, hIH2, hIH3, hW1V, hW2V, hW3V⟩ :=
    pair_three_setup₁ hc D hLI hL hLM hI hIM hS
  obtain ⟨hCLCI, hCIne, hcommCLCI, hdisjW1W2, hdisjW1W3, hdisjW2W3⟩ :=
    pair_three_setup₂ hc D h hH2 hpσ hLI hL hLM hI hIM hCLker hCIker hVI hIL2
  have hCLle : CL ≤ D.V := by rw [hCLker]; exact inf_le_right
  have hcardCL : Nat.card (centralizingInV 3 H D.V L) = 3 :=
    (pair_three_cards hc D h hH2 hpσ hLI hL hLM hI hIM hVI hIL2
      (D.t₁_mem hc.data).1 hCV1 s1).1
  have hmapI1 : I.map (MulAut.conj D.t₁).toMonoidHom = L :=
    map_conj_eq_left_of_swap hS hLI hI hIM hIH1 (D.t₁_mem hc.data).2 s1
  have hfix12 : L.map (MulAut.conj (D.t₁ * D.t₂)).toMonoidHom = L :=
    map_mul_conj_eq_left_of_swaps s2 hmapI1
  have hCLinv12 : ∀ x ∈ CL, D.t₁ * D.t₂ * x * (D.t₁ * D.t₂)⁻¹ ∈ CL := by
    intro x hx
    rw [hCLker] at hx ⊢
    exact map_conj_centralizingInV_le hVH (H.mul_mem hIH1 hIH2)
      (Subgroup.mul_mem _ hCV1 hCV2) hfix12 hx
  have hfix12' : CL ≤ D.W₃ ∨ CL ≤ D.W₁ ⊔ D.W₂ :=
    le_W3_or_le_sup_W1W2_of_invariant_t1t2 D hCLle (by rw [hCLker]; exact hcardCL) hCLinv12
  have hnotW3 : ¬ CL ≤ D.W₃ :=
    not_le_W_of_centralizingInV_CL hc D hL hLM hW3V D.cfg.card₃ (D.centralizer_le₃ hc)
      hCLker hcardCL
  have hnotPlane : ¬ CL ≤ D.W₁ ⊔ D.W₂ := fun hle =>
    not_le_sup_of_centralizingInV D hVH hIH3 hCV3 hCLker hCIker hCLCI
      (by rw [hCLker]; exact hcardCL) s3
      (fun x hx => D.cfg.comm₃ x hx) hle
  exact false_of_three_swaps hnotW3 hnotPlane hfix12'

private theorem two_swap_branch_facts
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    (hS : {J : Subgroup G | IsPComponentIn 3 J H ∧ ¬ J ≤ M} = {L, I})
    {Wk CL CI : Subgroup G} {ti tj tk : G}
    (hWkV : Wk ≤ D.V) (hcardWk : Nat.card Wk = 3)
    (hCLker : CL = centralizingInV 3 H D.V L) (hCIker : CI = centralizingInV 3 H D.V I)
    (hVI : D.V ≤ Subgroup.normalizer (I : Set G))
    (hIL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H I))
    (si : L.map (MulAut.conj ti).toMonoidHom = I) (sj : L.map (MulAut.conj tj).toMonoidHom = I)
    (hsk : ¬ L.map (MulAut.conj tk).toMonoidHom = I)
    (hMi : ti ∈ M) (hMj : tj ∈ M) (hMk : tk ∈ M)
    (hIHi : ti ∈ H) (hCVi : ti ∈ Subgroup.normalizer (D.V : Set G))
    (hIHj : tj ∈ H) (hIHk : tk ∈ H)
    (hcentk : Subgroup.centralizer (Wk : Set G) ≤ M) :
    L.map (MulAut.conj tk).toMonoidHom = L ∧
      I.map (MulAut.conj tk).toMonoidHom = I ∧
      L.map (MulAut.conj (ti * tj)).toMonoidHom = L ∧
      I.map (MulAut.conj (ti * tj)).toMonoidHom = I ∧
      ¬ CL ≤ Wk ∧ ¬ CI ≤ Wk ∧
      Nat.card (centralizingInV 3 H D.V L) = 3 ∧
      Nat.card (centralizingInV 3 H D.V I) = 3 := by
  obtain ⟨hcardCL, hcardCI⟩ := pair_three_cards hc D h hH2 hpσ hLI hL hLM hI hIM hVI hIL2
    hIHi hCVi si
  have hfixK : L.map (MulAut.conj tk).toMonoidHom = L := by
    rcases map_conj_eq_left_or_right_of_pair hS hL hLM hIHk hMk with h | h
    · exact h
    · exact absurd h hsk
  have hfixIK : I.map (MulAut.conj tk).toMonoidHom = I :=
    fix_I_of_fix_L hS hLI hI hIM hIHk hMk hfixK
  have hmapIi : I.map (MulAut.conj ti).toMonoidHom = L :=
    map_conj_eq_left_of_swap hS hLI hI hIM hIHi hMi si
  have hfixIJ : L.map (MulAut.conj (ti * tj)).toMonoidHom = L :=
    map_mul_conj_eq_left_of_swaps sj hmapIi
  have hfixIJI : I.map (MulAut.conj (ti * tj)).toMonoidHom = I :=
    fix_I_of_fix_L hS hLI hI hIM (H.mul_mem hIHi hIHj) (M.mul_mem hMi hMj) hfixIJ
  have hnotCLWk : ¬ CL ≤ Wk :=
    not_le_W_of_centralizingInV_CL hc D hL hLM hWkV hcardWk hcentk hCLker hcardCL
  have hnotCIWk : ¬ CI ≤ Wk :=
    not_le_W_of_centralizingInV_CL hc D hI hIM hWkV hcardWk hcentk hCIker hcardCI
  exact ⟨hfixK, hfixIK, hfixIJ, hfixIJI, hnotCLWk, hnotCIWk, hcardCL, hcardCI⟩

private theorem not_le_W_triple_CL
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {L CL : Subgroup G}
    (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hCLker : CL = centralizingInV 3 H D.V L)
    (hcardCL : Nat.card (centralizingInV 3 H D.V L) = 3)
    (hW1V : D.W₁ ≤ D.V) (hW2V : D.W₂ ≤ D.V) (hW3V : D.W₃ ≤ D.V) :
    ¬ CL ≤ D.W₁ ∧ ¬ CL ≤ D.W₂ ∧ ¬ CL ≤ D.W₃ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hCLker]
    exact not_le_W_of_centralizingInV hc D hL hLM hW1V D.cfg.card₁ (D.centralizer_le₁ hc) hcardCL
  · rw [hCLker]
    exact not_le_W_of_centralizingInV hc D hL hLM hW2V D.cfg.card₂ (D.centralizer_le₂ hc) hcardCL
  · rw [hCLker]
    exact not_le_W_of_centralizingInV hc D hL hLM hW3V D.cfg.card₃ (D.centralizer_le₃ hc) hcardCL

private theorem false_of_two_swaps_t1t2
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    (hZL : center ↥(starImg 3 H L) = ⊥)
    (hLL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H L))
    (hIL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H I))
    (hS : {J : Subgroup G | IsPComponentIn 3 J H ∧ ¬ J ≤ M} = {L, I})
    {CL CI : Subgroup G} (hCLker : CL = centralizingInV 3 H D.V L)
    (hCIker : CI = centralizingInV 3 H D.V I)
    (s1 : L.map (MulAut.conj D.t₁).toMonoidHom = I)
    (s2 : L.map (MulAut.conj D.t₂).toMonoidHom = I)
    (s3 : ¬ L.map (MulAut.conj D.t₃).toMonoidHom = I) : False := by
  have : IsMulCommutative ↥D.V := D.cfg.elem.1
  obtain ⟨hVH, hVL, hVI, hCV1, hCV2, hCV3, hIH1, hIH2, hIH3, hW1V, hW2V, hW3V⟩ :=
    pair_three_setup₁ hc D hLI hL hLM hI hIM hS
  obtain ⟨hCLCI, hCIne, hcommCLCI, hdisjW1W2, hdisjW1W3, hdisjW2W3⟩ :=
    pair_three_setup₂ hc D h hH2 hpσ hLI hL hLM hI hIM hCLker hCIker hVI hIL2
  have hCLle : CL ≤ D.V := by rw [hCLker]; exact inf_le_right
  have hCIle : CI ≤ D.V := by rw [hCIker]; exact inf_le_right
  have hV : D.V = D.W₃ ⊔ (D.W₁ ⊔ D.W₂) := by
    rw [D.cfg.join, sup_comm (D.W₁ ⊔ D.W₂) D.W₃]
  obtain ⟨hfix3, hfixI3, hfix12, hfixI12, hnotCLW3, hnotCIW3, hcardCL, hcardCI⟩ :=
    two_swap_branch_facts hc D h hH2 hpσ hLI hL hLM hI hIM hS hW3V D.cfg.card₃
      hCLker hCIker hVI hIL2 s1 s2 s3 (D.t₁_mem hc.data).2 (D.t₂_mem hc.data).2
      (D.t₃_mem hc.data).2 hIH1 hCV1 hIH2 hIH3 (D.centralizer_le₃ hc)
  exact false_of_two_swaps_case D hZL hLL2 hW1V hW2V hW3V D.cfg.card₁ D.cfg.card₂ D.cfg.card₃
    D.cfg.join hCLle hCIle hCLCI hCIne hcardCL hCLker hCIker hcardCI hcommCLCI
    (fun a ha b hb => setLike_mul_comm (hW1V ha) (hW2V hb)) hdisjW1W2
    hfix3 hfixI3 hfix12 hfixI12 (fun x hx => t1_mul_t2_fix_W3 D hx) D.cfg.inv₃
    (fun x hx => t1_mul_t2_inv_sup_W1W2 D hx) hnotCLW3 hnotCIW3
    hIH3 hCV3 hIH1 hCV1 hIH2 hCV2 hVH hVL hV

private theorem false_of_two_swaps_t1t3
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    (hZL : center ↥(starImg 3 H L) = ⊥)
    (hLL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H L))
    (hIL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H I))
    (hS : {J : Subgroup G | IsPComponentIn 3 J H ∧ ¬ J ≤ M} = {L, I})
    {CL CI : Subgroup G} (hCLker : CL = centralizingInV 3 H D.V L)
    (hCIker : CI = centralizingInV 3 H D.V I)
    (s1 : L.map (MulAut.conj D.t₁).toMonoidHom = I)
    (s3 : L.map (MulAut.conj D.t₃).toMonoidHom = I)
    (s2 : ¬ L.map (MulAut.conj D.t₂).toMonoidHom = I) : False := by
  have : IsMulCommutative ↥D.V := D.cfg.elem.1
  obtain ⟨hVH, hVL, hVI, hCV1, hCV2, hCV3, hIH1, hIH2, hIH3, hW1V, hW2V, hW3V⟩ :=
    pair_three_setup₁ hc D hLI hL hLM hI hIM hS
  obtain ⟨hCLCI, hCIne, hcommCLCI, hdisjW1W2, hdisjW1W3, hdisjW2W3⟩ :=
    pair_three_setup₂ hc D h hH2 hpσ hLI hL hLM hI hIM hCLker hCIker hVI hIL2
  have hCLle : CL ≤ D.V := by rw [hCLker]; exact inf_le_right
  have hCIle : CI ≤ D.V := by rw [hCIker]; exact inf_le_right
  have hVeq : D.V = D.W₁ ⊔ D.W₃ ⊔ D.W₂ := by rw [D.cfg.join]; ac_rfl
  have hV : D.V = D.W₂ ⊔ (D.W₁ ⊔ D.W₃) := by rw [D.cfg.join]; ac_rfl
  obtain ⟨hfix2, hfixI2, hfix13, hfixI13, hnotCLW2, hnotCIW2, hcardCL, hcardCI⟩ :=
    two_swap_branch_facts hc D h hH2 hpσ hLI hL hLM hI hIM hS hW2V D.cfg.card₂
      hCLker hCIker hVI hIL2 s1 s3 s2 (D.t₁_mem hc.data).2 (D.t₃_mem hc.data).2
      (D.t₂_mem hc.data).2 hIH1 hCV1 hIH3 hIH2 (D.centralizer_le₂ hc)
  exact false_of_two_swaps_case D hZL hLL2 hW1V hW3V hW2V D.cfg.card₁ D.cfg.card₃ D.cfg.card₂
    hVeq hCLle hCIle hCLCI hCIne hcardCL hCLker hCIker hcardCI hcommCLCI
    (fun a ha c hc => setLike_mul_comm (hW1V ha) (hW3V hc)) hdisjW1W3
    hfix2 hfixI2 hfix13 hfixI13
    (mul_t_fix_of_centralizes
      (fun x hx => by rw [D.cfg.comm₁ x (Subgroup.mem_sup_left hx)]; group)
      (fun x hx => by rw [D.cfg.comm₃ x (Subgroup.mem_sup_right hx)]; group))
    D.cfg.inv₂
    (mul_t_inv_sup_of_isE27 D hW1V hW3V D.cfg.inv₁ D.cfg.inv₃
      (fun x hx => D.cfg.comm₃ x (Subgroup.mem_sup_left hx))
      (fun x hx => D.cfg.comm₁ x (Subgroup.mem_sup_right hx)))
    hnotCLW2 hnotCIW2
    hIH2 hCV2 hIH1 hCV1 hIH3 hCV3 hVH hVL hV

private theorem false_of_two_swaps_t2t3
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    (hZL : center ↥(starImg 3 H L) = ⊥)
    (hLL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H L))
    (hIL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H I))
    (hS : {J : Subgroup G | IsPComponentIn 3 J H ∧ ¬ J ≤ M} = {L, I})
    {CL CI : Subgroup G} (hCLker : CL = centralizingInV 3 H D.V L)
    (hCIker : CI = centralizingInV 3 H D.V I)
    (s2 : L.map (MulAut.conj D.t₂).toMonoidHom = I)
    (s3 : L.map (MulAut.conj D.t₃).toMonoidHom = I)
    (s1 : ¬ L.map (MulAut.conj D.t₁).toMonoidHom = I) : False := by
  have : IsMulCommutative ↥D.V := D.cfg.elem.1
  obtain ⟨hVH, hVL, hVI, hCV1, hCV2, hCV3, hIH1, hIH2, hIH3, hW1V, hW2V, hW3V⟩ :=
    pair_three_setup₁ hc D hLI hL hLM hI hIM hS
  obtain ⟨hCLCI, hCIne, hcommCLCI, hdisjW1W2, hdisjW1W3, hdisjW2W3⟩ :=
    pair_three_setup₂ hc D h hH2 hpσ hLI hL hLM hI hIM hCLker hCIker hVI hIL2
  have hCLle : CL ≤ D.V := by rw [hCLker]; exact inf_le_right
  have hCIle : CI ≤ D.V := by rw [hCIker]; exact inf_le_right
  have hVeq : D.V = D.W₂ ⊔ D.W₃ ⊔ D.W₁ := by rw [D.cfg.join]; ac_rfl
  have hV : D.V = D.W₁ ⊔ (D.W₂ ⊔ D.W₃) := by rw [D.cfg.join]; ac_rfl
  obtain ⟨hfix1, hfixI1, hfix23, hfixI23, hnotCLW1, hnotCIW1, hcardCL, hcardCI⟩ :=
    two_swap_branch_facts hc D h hH2 hpσ hLI hL hLM hI hIM hS hW1V D.cfg.card₁
      hCLker hCIker hVI hIL2 s2 s3 s1 (D.t₂_mem hc.data).2 (D.t₃_mem hc.data).2
      (D.t₁_mem hc.data).2 hIH2 hCV2 hIH3 hIH1 (D.centralizer_le₁ hc)
  exact false_of_two_swaps_case D hZL hLL2 hW2V hW3V hW1V D.cfg.card₂ D.cfg.card₃ D.cfg.card₁
    hVeq hCLle hCIle hCLCI hCIne hcardCL hCLker hCIker hcardCI hcommCLCI
    (fun b hb c hc => setLike_mul_comm (hW2V hb) (hW3V hc)) hdisjW2W3
    hfix1 hfixI1 hfix23 hfixI23
    (mul_t_fix_of_centralizes
      (fun x hx => by rw [D.cfg.comm₂ x (Subgroup.mem_sup_left hx)]; group)
      (fun x hx => by rw [D.cfg.comm₃ x (Subgroup.mem_sup_left hx)]; group))
    D.cfg.inv₁
    (mul_t_inv_sup_of_isE27 D hW2V hW3V D.cfg.inv₂ D.cfg.inv₃
      (fun x hx => D.cfg.comm₃ x (Subgroup.mem_sup_right hx))
      (fun x hx => D.cfg.comm₂ x (Subgroup.mem_sup_right hx)))
    hnotCLW1 hnotCIW1
    hIH1 hCV1 hIH2 hCV2 hIH3 hCV3 hVH hVL hV

private theorem false_of_one_swap_t1
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    (hIL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H I))
    (hS : {J : Subgroup G | IsPComponentIn 3 J H ∧ ¬ J ≤ M} = {L, I})
    {CL CI : Subgroup G} (hCLker : CL = centralizingInV 3 H D.V L)
    (hCIker : CI = centralizingInV 3 H D.V I)
    (s1 : L.map (MulAut.conj D.t₁).toMonoidHom = I)
    (s2 : ¬ L.map (MulAut.conj D.t₂).toMonoidHom = I)
    (s3 : ¬ L.map (MulAut.conj D.t₃).toMonoidHom = I) : False := by
  obtain ⟨hVH, hVL, hVI, hCV1, hCV2, hCV3, hIH1, hIH2, hIH3, hW1V, hW2V, hW3V⟩ :=
    pair_three_setup₁ hc D hLI hL hLM hI hIM hS
  obtain ⟨hCLCI, hCIne, hcommCLCI, hdisjW1W2, hdisjW1W3, hdisjW2W3⟩ :=
    pair_three_setup₂ hc D h hH2 hpσ hLI hL hLM hI hIM hCLker hCIker hVI hIL2
  have hCLle : CL ≤ D.V := by rw [hCLker]; exact inf_le_right
  have hcardCL : Nat.card (centralizingInV 3 H D.V L) = 3 :=
    (pair_three_cards hc D h hH2 hpσ hLI hL hLM hI hIM hVI hIL2
      (D.t₁_mem hc.data).1 hCV1 s1).1
  obtain ⟨hnotW1, hnotW2, hnotW3⟩ := not_le_W_triple_CL hc D hL hLM hCLker hcardCL hW1V hW2V hW3V
  have hfix2 : L.map (MulAut.conj D.t₂).toMonoidHom = L := by
    rcases map_conj_eq_left_or_right_of_pair hS hL hLM hIH2 (D.t₂_mem hc.data).2 with h | h
    · exact h
    · exact absurd h s2
  have hfix3 : L.map (MulAut.conj D.t₃).toMonoidHom = L := by
    rcases map_conj_eq_left_or_right_of_pair hS hL hLM hIH3 (D.t₃_mem hc.data).2 with h | h
    · exact h
    · exact absurd h s3
  have hCLinv2 : ∀ x ∈ CL, D.t₂ * x * D.t₂⁻¹ ∈ CL := by
    intro x hx
    rw [hCLker] at hx ⊢
    exact map_conj_centralizingInV_le hVH hIH2 hCV2 hfix2 hx
  have hCLinv3 : ∀ x ∈ CL, D.t₃ * x * D.t₃⁻¹ ∈ CL := by
    intro x hx
    rw [hCLker] at hx ⊢
    exact map_conj_centralizingInV_le hVH hIH3 hCV3 hfix3 hx
  have hfix2' : CL ≤ D.W₁ ⊔ D.W₃ ∨ CL ≤ D.W₂ :=
    le_sup_W1W3_or_le_W2_of_invariant_t2 D hCLle (by rw [hCLker]; exact hcardCL) hCLinv2
  have hfix3' : CL ≤ D.W₁ ⊔ D.W₂ ∨ CL ≤ D.W₃ :=
    le_sup_W1W2_or_le_W3_of_invariant_t3 D hCLle (by rw [hCLker]; exact hcardCL) hCLinv3
  exact false_of_one_swap_case D hVH hIH1 hCV1 s1 hCLker hCIker hCLCI
    (by rw [hCLker]; exact hcardCL)
    (fun x hx => D.cfg.comm₁ x hx) hnotW1 hfix2'.symm hfix3'.symm
    (W1W3_inf_W1W2_eq_W1 D)

private theorem false_of_one_swap_t2
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    (hIL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H I))
    (hS : {J : Subgroup G | IsPComponentIn 3 J H ∧ ¬ J ≤ M} = {L, I})
    {CL CI : Subgroup G} (hCLker : CL = centralizingInV 3 H D.V L)
    (hCIker : CI = centralizingInV 3 H D.V I)
    (s2 : L.map (MulAut.conj D.t₂).toMonoidHom = I)
    (s1 : ¬ L.map (MulAut.conj D.t₁).toMonoidHom = I)
    (s3 : ¬ L.map (MulAut.conj D.t₃).toMonoidHom = I) : False := by
  obtain ⟨hVH, hVL, hVI, hCV1, hCV2, hCV3, hIH1, hIH2, hIH3, hW1V, hW2V, hW3V⟩ :=
    pair_three_setup₁ hc D hLI hL hLM hI hIM hS
  obtain ⟨hCLCI, hCIne, hcommCLCI, hdisjW1W2, hdisjW1W3, hdisjW2W3⟩ :=
    pair_three_setup₂ hc D h hH2 hpσ hLI hL hLM hI hIM hCLker hCIker hVI hIL2
  have hCLle : CL ≤ D.V := by rw [hCLker]; exact inf_le_right
  have hcardCL : Nat.card (centralizingInV 3 H D.V L) = 3 :=
    (pair_three_cards hc D h hH2 hpσ hLI hL hLM hI hIM hVI hIL2
      (D.t₂_mem hc.data).1 hCV2 s2).1
  obtain ⟨hnotW1, hnotW2, hnotW3⟩ := not_le_W_triple_CL hc D hL hLM hCLker hcardCL hW1V hW2V hW3V
  have hfix1 : L.map (MulAut.conj D.t₁).toMonoidHom = L := by
    rcases map_conj_eq_left_or_right_of_pair hS hL hLM hIH1 (D.t₁_mem hc.data).2 with h | h
    · exact h
    · exact absurd h s1
  have hfix3 : L.map (MulAut.conj D.t₃).toMonoidHom = L := by
    rcases map_conj_eq_left_or_right_of_pair hS hL hLM hIH3 (D.t₃_mem hc.data).2 with h | h
    · exact h
    · exact absurd h s3
  have hCLinv1 : ∀ x ∈ CL, D.t₁ * x * D.t₁⁻¹ ∈ CL := by
    intro x hx
    rw [hCLker] at hx ⊢
    exact map_conj_centralizingInV_le hVH hIH1 hCV1 hfix1 hx
  have hCLinv3 : ∀ x ∈ CL, D.t₃ * x * D.t₃⁻¹ ∈ CL := by
    intro x hx
    rw [hCLker] at hx ⊢
    exact map_conj_centralizingInV_le hVH hIH3 hCV3 hfix3 hx
  have hfix1' : CL ≤ D.W₂ ⊔ D.W₃ ∨ CL ≤ D.W₁ :=
    le_sup_W2W3_or_le_W1_of_invariant_t1 D hCLle (by rw [hCLker]; exact hcardCL) hCLinv1
  have hfix3' : CL ≤ D.W₁ ⊔ D.W₂ ∨ CL ≤ D.W₃ :=
    le_sup_W1W2_or_le_W3_of_invariant_t3 D hCLle (by rw [hCLker]; exact hcardCL) hCLinv3
  exact false_of_one_swap_case D hVH hIH2 hCV2 s2 hCLker hCIker hCLCI
    (by rw [hCLker]; exact hcardCL)
    (fun x hx => D.cfg.comm₂ x hx) hnotW2 hfix1'.symm
    (Or.imp_right (fun h => h.trans_eq (sup_comm _ _)) hfix3'.symm)
    (W2W3_inf_W2W1_eq_W2 D)

private theorem false_of_one_swap_t3
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    (hIL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H I))
    (hS : {J : Subgroup G | IsPComponentIn 3 J H ∧ ¬ J ≤ M} = {L, I})
    {CL CI : Subgroup G} (hCLker : CL = centralizingInV 3 H D.V L)
    (hCIker : CI = centralizingInV 3 H D.V I)
    (s3 : L.map (MulAut.conj D.t₃).toMonoidHom = I)
    (s1 : ¬ L.map (MulAut.conj D.t₁).toMonoidHom = I)
    (s2 : ¬ L.map (MulAut.conj D.t₂).toMonoidHom = I) : False := by
  obtain ⟨hVH, hVL, hVI, hCV1, hCV2, hCV3, hIH1, hIH2, hIH3, hW1V, hW2V, hW3V⟩ :=
    pair_three_setup₁ hc D hLI hL hLM hI hIM hS
  obtain ⟨hCLCI, hCIne, hcommCLCI, hdisjW1W2, hdisjW1W3, hdisjW2W3⟩ :=
    pair_three_setup₂ hc D h hH2 hpσ hLI hL hLM hI hIM hCLker hCIker hVI hIL2
  have hCLle : CL ≤ D.V := by rw [hCLker]; exact inf_le_right
  have hcardCL : Nat.card (centralizingInV 3 H D.V L) = 3 :=
    (pair_three_cards hc D h hH2 hpσ hLI hL hLM hI hIM hVI hIL2
      (D.t₃_mem hc.data).1 hCV3 s3).1
  obtain ⟨hnotW1, hnotW2, hnotW3⟩ := not_le_W_triple_CL hc D hL hLM hCLker hcardCL hW1V hW2V hW3V
  have hfix1 : L.map (MulAut.conj D.t₁).toMonoidHom = L := by
    rcases map_conj_eq_left_or_right_of_pair hS hL hLM hIH1 (D.t₁_mem hc.data).2 with h | h
    · exact h
    · exact absurd h s1
  have hfix2 : L.map (MulAut.conj D.t₂).toMonoidHom = L := by
    rcases map_conj_eq_left_or_right_of_pair hS hL hLM hIH2 (D.t₂_mem hc.data).2 with h | h
    · exact h
    · exact absurd h s2
  have hCLinv1 : ∀ x ∈ CL, D.t₁ * x * D.t₁⁻¹ ∈ CL := by
    intro x hx
    rw [hCLker] at hx ⊢
    exact map_conj_centralizingInV_le hVH hIH1 hCV1 hfix1 hx
  have hCLinv2 : ∀ x ∈ CL, D.t₂ * x * D.t₂⁻¹ ∈ CL := by
    intro x hx
    rw [hCLker] at hx ⊢
    exact map_conj_centralizingInV_le hVH hIH2 hCV2 hfix2 hx
  have hfix1' : CL ≤ D.W₂ ⊔ D.W₃ ∨ CL ≤ D.W₁ :=
    le_sup_W2W3_or_le_W1_of_invariant_t1 D hCLle (by rw [hCLker]; exact hcardCL) hCLinv1
  have hfix2' : CL ≤ D.W₁ ⊔ D.W₃ ∨ CL ≤ D.W₂ :=
    le_sup_W1W3_or_le_W2_of_invariant_t2 D hCLle (by rw [hCLker]; exact hcardCL) hCLinv2
  exact false_of_one_swap_case D hVH hIH3 hCV3 s3 hCLker hCIker hCLCI
    (by rw [hCLker]; exact hcardCL)
    (fun x hx => D.cfg.comm₃ x hx) hnotW3
    (Or.imp_right (fun h => h.trans_eq (sup_comm _ _)) hfix1'.symm)
    (Or.imp_right (fun h => h.trans_eq (sup_comm _ _)) hfix2'.symm)
    (W3W2_inf_W3W1_eq_W3 D)

private theorem false_of_pair_p_eq_three_swap
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    (hZL : center ↥(starImg 3 H L) = ⊥)
    (hLL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H L))
    (hIL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H I))
    (hS : {J : Subgroup G | IsPComponentIn 3 J H ∧ ¬ J ≤ M} = {L, I})
    (hswap : L.map (MulAut.conj D.t₁).toMonoidHom = I ∨
             L.map (MulAut.conj D.t₂).toMonoidHom = I ∨
             L.map (MulAut.conj D.t₃).toMonoidHom = I) :
    False := by
  let CL : Subgroup G := centralizingInV 3 H D.V L
  let CI : Subgroup G := centralizingInV 3 H D.V I
  have hCLker : CL = centralizingInV 3 H D.V L := rfl
  have hCIker : CI = centralizingInV 3 H D.V I := rfl
  by_cases s1 : L.map (MulAut.conj D.t₁).toMonoidHom = I
  · by_cases s2 : L.map (MulAut.conj D.t₂).toMonoidHom = I
    · by_cases s3 : L.map (MulAut.conj D.t₃).toMonoidHom = I
      · exact false_of_three_swaps_case hc D h hH2 hpσ hLI hL hLM hI hIM hIL2
          hS hCLker hCIker s1 s2 s3
      · exact false_of_two_swaps_t1t2 hc D h hH2 hpσ hLI hL hLM hI hIM hZL hLL2 hIL2
          hS hCLker hCIker s1 s2 s3
    · by_cases s3 : L.map (MulAut.conj D.t₃).toMonoidHom = I
      · exact false_of_two_swaps_t1t3 hc D h hH2 hpσ hLI hL hLM hI hIM hZL hLL2 hIL2
          hS hCLker hCIker s1 s3 s2
      · exact false_of_one_swap_t1 hc D h hH2 hpσ hLI hL hLM hI hIM hIL2
          hS hCLker hCIker s1 s2 s3
  · by_cases s2 : L.map (MulAut.conj D.t₂).toMonoidHom = I
    · by_cases s3 : L.map (MulAut.conj D.t₃).toMonoidHom = I
      · exact false_of_two_swaps_t2t3 hc D h hH2 hpσ hLI hL hLM hI hIM hZL hLL2 hIL2
          hS hCLker hCIker s2 s3 s1
      · exact false_of_one_swap_t2 hc D h hH2 hpσ hLI hL hLM hI hIM hIL2
          hS hCLker hCIker s2 s1 s3
    · by_cases s3 : L.map (MulAut.conj D.t₃).toMonoidHom = I
      · exact false_of_one_swap_t3 hc D h hH2 hpσ hLI hL hLM hI hIM hIL2
          hS hCLker hCIker s3 s1 s2
      · rcases hswap with s | s | s
        · exact absurd s s1
        · exact absurd s s2
        · exact absurd s s3

private theorem fixes_of_not_swap
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {L I : Subgroup G} (hS : {J : Subgroup G | IsPComponentIn 3 J H ∧ ¬ J ≤ M} = {L, I})
    (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hs1 : ¬ L.map (MulAut.conj D.t₁).toMonoidHom = I)
    (hs2 : ¬ L.map (MulAut.conj D.t₂).toMonoidHom = I)
    (hs3 : ¬ L.map (MulAut.conj D.t₃).toMonoidHom = I) :
    L.map (MulAut.conj D.t₁).toMonoidHom = L ∧
      L.map (MulAut.conj D.t₂).toMonoidHom = L ∧
      L.map (MulAut.conj D.t₃).toMonoidHom = L := by
  refine ⟨?_, ?_, ?_⟩
  · rcases map_conj_eq_left_or_right_of_pair hS hL hLM
      (D.t₁_mem hc.data).1 (D.t₁_mem hc.data).2 with h | h
    · exact h
    · exact absurd h hs1
  · rcases map_conj_eq_left_or_right_of_pair hS hL hLM
      (D.t₂_mem hc.data).1 (D.t₂_mem hc.data).2 with h | h
    · exact h
    · exact absurd h hs2
  · rcases map_conj_eq_left_or_right_of_pair hS hL hLM
      (D.t₃_mem hc.data).1 (D.t₃_mem hc.data).2 with h | h
    · exact h
    · exact absurd h hs3

private noncomputable def mkEquiv_of_swap {L I : Subgroup G} {t : G} (htH : t ∈ H)
    (htmap : L.map (MulAut.conj t).toMonoidHom = I) :
    ↥(starImg 3 H L) ≃* ↥(starImg 3 H I) := by
  let wbar : StarGroup 3 H :=
    QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) ⟨t, htH⟩
  have heq := starImg_map_conj 3 H L ⟨t, htH⟩
  rw [htmap] at heq
  exact (Subgroup.equivMapOfInjective (starImg 3 H L)
    (MulAut.conj wbar).toMonoidHom (MulAut.conj wbar).injective).trans
    (MulEquiv.subgroupCongr heq.symm)

private theorem false_of_pair_p_three_swap_index
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    (hXM : xSub 3 M H ≤ M) (h35r : KFactThreeFiveRankOne)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    {ti : G} (hIHi : ti ∈ H)
    (hswapI : L.map (MulAut.conj ti).toMonoidHom = I)
    (hswap : L.map (MulAut.conj D.t₁).toMonoidHom = I ∨
             L.map (MulAut.conj D.t₂).toMonoidHom = I ∨
             L.map (MulAut.conj D.t₃).toMonoidHom = I) :
    False := by
  have hnotlayer : ¬ pLayerIn 3 H ≤ M := fun hle => hLM ((le_pLayerIn hL).trans hle)
  have hS : {J : Subgroup G | IsPComponentIn 3 J H ∧ ¬ J ≤ M} = {L, I} :=
    eq_pair_of_ncard_le_two hLI hL hLM hI hIM
      (nineSixTwoComp_holds G M E H E 3 h hH2 hpσ hnotlayer)
  have hZ := center_starImg_eq_bot_of_pair hc D h hH2 hpσ hXM rfl hLI hL hLM hI hIM
  have hZL : center ↥(starImg 3 H L) = ⊥ := hZ.1
  have hsum : CFSG.Open.pRank 3 (starImg 3 H L) + CFSG.Open.pRank 3 (starImg 3 H I) ≤ 3 :=
    pRank_add_le_three_of_pair hc h hH2 hpσ hLI hL hI hZL
  have hL1 : 1 ≤ CFSG.Open.pRank 3 (starImg 3 H L) :=
    one_le_pRank_of_starImg_of_pComponent hL
  have hI1 : 1 ≤ CFSG.Open.pRank 3 (starImg 3 H I) :=
    one_le_pRank_of_starImg_of_pComponent hI
  have e := mkEquiv_of_swap hIHi hswapI
  by_cases hLrank : CFSG.Open.pRank 3 (starImg 3 H L) = 1
  · have hLL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H L) :=
      isPSLType_of_pRank_one_three h hH2 hpσ h35r hL hLM hLrank
    have hIL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H I) :=
      CFSG.LocalAnalysis.AGL81I.Section3.isPSLType_of_mulEquiv e hLL2
    exact false_of_pair_p_eq_three_swap hc D h hH2 hpσ hLI hL hLM hI hIM hZL
      hLL2 hIL2 hS hswap
  · have hIrank : CFSG.Open.pRank 3 (starImg 3 H I) = 1 := by omega
    have hIL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H I) :=
      isPSLType_of_pRank_one_three h hH2 hpσ h35r hI hIM hIrank
    have hLL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H L) :=
      CFSG.LocalAnalysis.AGL81I.Section3.isPSLType_of_mulEquiv e.symm hIL2
    exact false_of_pair_p_eq_three_swap hc D h hH2 hpσ hLI hL hLM hI hIM hZL
      hLL2 hIL2 hS hswap

private theorem false_of_pair_p_three_swap_true
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    (hXM : xSub 3 M H ≤ M) (h35r : KFactThreeFiveRankOne)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    (hswap : L.map (MulAut.conj D.t₁).toMonoidHom = I ∨
             L.map (MulAut.conj D.t₂).toMonoidHom = I ∨
             L.map (MulAut.conj D.t₃).toMonoidHom = I) : False := by
  rcases hswap with s1 | s2 | s3
  · exact false_of_pair_p_three_swap_index hc D h hH2 hpσ hXM h35r hLI hL hLM hI hIM
      (D.t₁_mem hc.data).1 s1 (Or.inl s1)
  · exact false_of_pair_p_three_swap_index hc D h hH2 hpσ hXM h35r hLI hL hLM hI hIM
      (D.t₂_mem hc.data).1 s2 (Or.inr (Or.inl s2))
  · exact false_of_pair_p_three_swap_index hc D h hH2 hpσ hXM h35r hLI hL hLM hI hIM
      (D.t₃_mem hc.data).1 s3 (Or.inr (Or.inr s3))

private theorem false_of_pair_p_three_no_swap
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    (h35r : KFactThreeFiveRankOne)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M)
    (hS : {J : Subgroup G | IsPComponentIn 3 J H ∧ ¬ J ≤ M} = {L, I})
    (hsum : CFSG.Open.pRank 3 (starImg 3 H L) + CFSG.Open.pRank 3 (starImg 3 H I) ≤ 3)
    (hL1 : 1 ≤ CFSG.Open.pRank 3 (starImg 3 H L))
    (hI1 : 1 ≤ CFSG.Open.pRank 3 (starImg 3 H I))
    (hs1 : ¬ L.map (MulAut.conj D.t₁).toMonoidHom = I)
    (hs2 : ¬ L.map (MulAut.conj D.t₂).toMonoidHom = I)
    (hs3 : ¬ L.map (MulAut.conj D.t₃).toMonoidHom = I) : False := by
  obtain ⟨hfix1, hfix2, hfix3⟩ := fixes_of_not_swap hc D hS hL hLM hs1 hs2 hs3
  by_cases hIrank : CFSG.Open.pRank 3 (starImg 3 H I) = 1
  · have hIL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H I) :=
      isPSLType_of_pRank_one_three h hH2 hpσ h35r hI hIM hIrank
    exact false_of_pair_no_swap hc D h hH2 hpσ hLI hL hLM hI hIM hIL2 hfix1 hfix2 hfix3
  · have hLrank : CFSG.Open.pRank 3 (starImg 3 H L) = 1 := by omega
    have hLL2 : IsPSLType 2 (GaloisField 2 3) ↥(starImg 3 H L) :=
      isPSLType_of_pRank_one_three h hH2 hpσ h35r hL hLM hLrank
    have hNI1 : D.t₁ ∈ Subgroup.normalizer (I : Set G) :=
      mem_normalizer_right_of_fixes_left hS hLI hI hIM
        (D.t₁_mem hc.data).1 (D.t₁_mem hc.data).2 hfix1
    have hNI2 : D.t₂ ∈ Subgroup.normalizer (I : Set G) :=
      mem_normalizer_right_of_fixes_left hS hLI hI hIM
        (D.t₂_mem hc.data).1 (D.t₂_mem hc.data).2 hfix2
    have hNI3 : D.t₃ ∈ Subgroup.normalizer (I : Set G) :=
      mem_normalizer_right_of_fixes_left hS hLI hI hIM
        (D.t₃_mem hc.data).1 (D.t₃_mem hc.data).2 hfix3
    have hIfix1 : I.map (MulAut.conj D.t₁).toMonoidHom = I :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hNI1
    have hIfix2 : I.map (MulAut.conj D.t₂).toMonoidHom = I :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hNI2
    have hIfix3 : I.map (MulAut.conj D.t₃).toMonoidHom = I :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hNI3
    exact false_of_pair_no_swap hc D h hH2 hpσ (L := I) (I := L)
      (Ne.symm hLI) hI hIM hL hLM hLL2 hIfix1 hIfix2 hIfix3

private theorem false_of_pair_p_three
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {E : Subgroup G} (h : NineSettingGen G M 3 E H E 2) (hH2 : H ∈ H2Fam M E)
    (hpσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    (hXM : xSub 3 M H ≤ M) (h35r : KFactThreeFiveRankOne)
    {L I : Subgroup G} (hLI : L ≠ I) (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hI : IsPComponentIn 3 I H) (hIM : ¬ I ≤ M) : False := by
  have hnotlayer : ¬ pLayerIn 3 H ≤ M := fun hle => hLM ((le_pLayerIn hL).trans hle)
  have hS : {J : Subgroup G | IsPComponentIn 3 J H ∧ ¬ J ≤ M} = {L, I} :=
    eq_pair_of_ncard_le_two hLI hL hLM hI hIM
      (nineSixTwoComp_holds G M E H E 3 h hH2 hpσ hnotlayer)
  have hZ := center_starImg_eq_bot_of_pair hc D h hH2 hpσ hXM rfl hLI hL hLM hI hIM
  have hZL : center ↥(starImg 3 H L) = ⊥ := hZ.1
  have hsum : CFSG.Open.pRank 3 (starImg 3 H L) + CFSG.Open.pRank 3 (starImg 3 H I) ≤ 3 :=
    pRank_add_le_three_of_pair hc h hH2 hpσ hLI hL hI hZL
  have hL1 : 1 ≤ CFSG.Open.pRank 3 (starImg 3 H L) :=
    one_le_pRank_of_starImg_of_pComponent hL
  have hI1 : 1 ≤ CFSG.Open.pRank 3 (starImg 3 H I) :=
    one_le_pRank_of_starImg_of_pComponent hI
  by_cases hswap : L.map (MulAut.conj D.t₁).toMonoidHom = I ∨
      L.map (MulAut.conj D.t₂).toMonoidHom = I ∨
      L.map (MulAut.conj D.t₃).toMonoidHom = I
  · exact false_of_pair_p_three_swap_true hc D h hH2 hpσ hXM h35r hLI hL hLM hI hIM hswap
  · have hs1 : ¬ L.map (MulAut.conj D.t₁).toMonoidHom = I := fun h1 => hswap (Or.inl h1)
    have hs2 : ¬ L.map (MulAut.conj D.t₂).toMonoidHom = I :=
      fun h2 => hswap (Or.inr (Or.inl h2))
    have hs3 : ¬ L.map (MulAut.conj D.t₃).toMonoidHom = I :=
      fun h3 => hswap (Or.inr (Or.inr h3))
    exact false_of_pair_p_three_no_swap hc D h hH2 hpσ h35r hLI hL hLM hI hIM hS
      hsum hL1 hI1 hs1 hs2 hs3

theorem TwelveSixKCtx.false_of_two_pComponents_not_le
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃) (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hXM : xSub p M H ≤ M) (h35r : KFactThreeFiveRankOne) (hpair : NineSixMoreoverPairFive)
    (hSz : KFactSz32MulAutThreeFree) {L I : Subgroup G} (hL : IsPComponentIn p L H)
    (hLM : ¬ L ≤ M) (hI : IsPComponentIn p I H) (hIM : ¬ I ≤ M) (hLI : L ≠ I) : False := by
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := hc.ctx.exists_E_sq
  have hC := hc.ctx.hypCGen hEQ hE hEc hΓ
  have h : NineSettingGen G M p E H E 2 := hC.toNineSettingGen
  by_cases hp3 : p = 3
  · subst p
    exact false_of_pair_p_three hc D h hC.mem_H2Fam hC.not_mem_sigmaM hXM h35r
      hLI hL hLM hI hIM
  · exact false_of_pair_of_p_ne_three hc D h hC.mem_H2Fam hC.not_mem_sigmaM hp3
      hpair hSz hL hLM hI hIM hLI

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
