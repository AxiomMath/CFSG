module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.Quasithin.EmptyFaithful.S14111
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NaturalSectionOn
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.S11Parabolic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.S11Setup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NaturalSectionOfOffender
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NaturalSectionBlock
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
import CFSG.Quasithin.Background.C118NoOuter
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.C126Over
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FiveThreeBridge
import CFSG.LocalAnalysis.QuasithinUnique.SteinbergBYTwoCoreResidual
import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourSylow
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.LemmaF

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.AGLEmbeddingD2.GN

variable {X : Type} [Group X] [Finite X]

theorem gnC_eq_pCoreOf {n : ℕ} (hn : 5 ≤ n) {L R : Subgroup X} (φ : X →* Equiv.Perm (Fin n))
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hL : L.map φ = alternatingGroup (Fin n)) (hQR : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ R)
    (hLW : ¬ L ≤ gnC R) : gnC R = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) := by
  set C : Subgroup X := gnC R
  have hQC : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ C :=
    CFSG.AGLEmbeddingD2.GN.pCoreOf_le_gnC_of_le (T := R) hQR
  have hbot : C.map φ = ⊥ := by
    by_contra hne
    haveI : (C.map φ).Normal := (gnC_normal R).map φ hφ
    have hnt : Nontrivial ↥(C.map φ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have halt : alternatingGroup (Fin n) ≤ C.map φ :=
      Equiv.Perm.alternatingGroup_le_of_normal (α := Fin n) (by simpa using hn) hnt
    apply hLW
    intro l hl
    have hmem : φ l ∈ C.map φ := halt (hL ▸ Subgroup.mem_map_of_mem φ hl)
    obtain ⟨k, hk, hkφ⟩ := Subgroup.mem_map.mp hmem
    have hker_mem : l * k⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkφ, mul_inv_cancel]
    have hQmem : l * k⁻¹ ∈ CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) := by
      rw [← hker]; exact hker_mem
    have : l = (l * k⁻¹) * k := by group
    rw [this]
    exact C.mul_mem (hQC hQmem) hk
  refine le_antisymm ?_ hQC
  rw [← hker]
  exact (Subgroup.map_eq_bot_iff C).mp hbot

theorem le_of_map_le_map_of_closure_odd {Y : Type*} [Group Y] {L D : Subgroup X} [D.Normal]
    (hLodd : L = Subgroup.closure {x : X | x ∈ L ∧ Odd (orderOf x)}) (φ : X →* Y)
    (hker : IsPGroup 2 φ.ker) (hLD : L.map φ ≤ D.map φ) : L ≤ D := by
  have hno := CFSG.QuasithinUnique.SteinbergBY.hasNoTwoQuotient_of_le_oddOrderSubgroup
    (Z := L) (by rw [CFSG.QuasithinUnique.Setup.oddOrderSubgroup]; exact hLodd.le)
  let π : X →* X ⧸ D := QuotientGroup.mk' D
  have hLπ : L.map π ≤ φ.ker.map π := by
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨d, hdD, hdφ⟩ := Subgroup.mem_map.mp (hLD (Subgroup.mem_map_of_mem φ hl))
    refine Subgroup.mem_map.mpr ⟨l * d⁻¹, ?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, hdφ, mul_inv_cancel]
    · show π (l * d⁻¹) = π l
      rw [map_mul, map_inv]
      have hd : π d = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hdD
      rw [hd, inv_one, mul_one]
  let ψ : ↥L →* X ⧸ D := π.comp L.subtype
  have hψker : ψ.ker = (L ⊓ D).subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show π (l : X) = 1 ↔ (l : X) ∈ L ⊓ D
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨fun h => ⟨l.2, h⟩, fun h => h.2⟩
  have hrange : ψ.range = L.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  haveI : ((L ⊓ D).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (CFSG.QuasithinUnique.SteinbergBY.inf_le_normalizer Subgroup.le_normalizer
        (Subgroup.le_normalizer_of_normal))
  have h2 : IsPGroup 2 (L ⧸ (L ⊓ D).subgroupOf L) := by
    have hP : IsPGroup 2 ↥(L.map π) := (hker.map π).to_le hLπ
    have he : (L ⧸ (L ⊓ D).subgroupOf L) ≃* ↥(L.map π) :=
      ((QuotientGroup.quotientMulEquivOfEq hψker).symm.trans
        (QuotientGroup.quotientKerEquivRange ψ)).trans (MulEquiv.subgroupCongr hrange)
    exact hP.of_equiv he.symm
  have htop := hno ((L ⊓ D).subgroupOf L) h2
  intro l hl
  have hmem : (⟨l, hl⟩ : ↥L) ∈ (L ⊓ D).subgroupOf L := htop.symm ▸ Subgroup.mem_top _
  exact (Subgroup.mem_subgroupOf.mp hmem).2

theorem normal_of_subgroupOf_characteristic_of_sup_eq_top {C R P : Subgroup X}
    (hCR : C ≤ R) (hchar : (C.subgroupOf R).Characteristic)
    (hsup : Subgroup.normalizer (R : Set X) ⊔ P = ⊤)
    (hPC : P ≤ Subgroup.normalizer (C : Set X)) : C.Normal := by
  have hNR : Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (C : Set X) := by
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (C.subgroupOf R)
    rwa [Subgroup.map_subgroupOf_eq_of_le hCR] at h
  refine Subgroup.normalizer_eq_top_iff.mp ?_
  rw [eq_top_iff, ← hsup]
  exact sup_le hNR hPC

theorem inClassXBlock_of_isChiBlock {L R P K : Subgroup X} (hLn : L.Normal)
    (hLodd : L = Subgroup.closure {x : X | x ∈ L ∧ Odd (orderOf x)})
    {φ : X →* Equiv.Perm (Fin 11)} (hφ : Function.Surjective φ)
    (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hL : L.map φ = alternatingGroup (Fin 11))
    (hCeq : gnC R = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hW : CFSG.Open.IsElemAbelian 2 (gnV R))
    (hWQ : gnV R ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hQR : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ R)
    (hQP : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ P) (hKchi : IsChiBlock P K)
    (hnat : NaturalSectionOn (gnV R) L ⊤ 11) :
    CFSG.AGLEmbedding.InClassXBlock L := by
  have hKshort : IsShort2 K := hKchi.1.1
  have hKnotP : ¬ IsPGroup 2 K := CFSG.QuasithinUnique.L238.not_isPGroup_two_of_isShort2 hKshort
  have hKnotQ : ¬ K ≤ pCoreOf 2 (⊤ : Subgroup X) := fun hKQ =>
    hKnotP ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup X)).to_le hKQ)
  have hKC' : ¬ K ≤ gnC R := by
    rw [hCeq]
    exact hKnotQ
  have hKC : ¬ K ≤ Subgroup.centralizer (gnV R : Set X) := hKC'
  have hQK : ⁅pCoreOf 2 (⊤ : Subgroup X), K⁆ ≤ gnV R :=
    commutator_pCoreOf_le_of_le_pCoreOf hWQ hQP hKchi.1 hKC
  have hKD : K ≤ gnD R := (le_gnD_iff (T := R) (A := K)).mpr hQK
  haveI hLn' : L.Normal := hLn
  haveI hWn : (gnV R).Normal := normal_gnV R
  haveI hDn : (gnD R).Normal := normal_gnD R
  haveI hDmapN : ((gnD R).map φ).Normal := hDn.map φ hφ
  have hDmap_ne : (gnD R).map φ ≠ ⊥ := by
    intro hbot
    have hKle : K ≤ φ.ker := by
      rw [← Subgroup.map_eq_bot_iff K, eq_bot_iff]
      calc K.map φ ≤ (gnD R).map φ := Subgroup.map_mono hKD
        _ = ⊥ := hbot
    exact hKnotQ (by rw [hker] at hKle; exact hKle)
  have hAltle : alternatingGroup (Fin 11) ≤ (gnD R).map φ :=
    Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 11) (by simp)
      ((Subgroup.nontrivial_iff_ne_bot _).mpr hDmap_ne)
  have hLD : L ≤ gnD R :=
    le_of_map_le_map_of_closure_odd hLodd φ
      (by rw [hker]; exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup X))
      (by rw [hL]; exact hAltle)
  have hQL : ⁅pCoreOf 2 (⊤ : Subgroup X), L⁆ ≤ gnV R :=
    (le_gnD_iff (T := R) (A := L)).mp hLD
  have hQW : pCoreOf 2 (⊤ : Subgroup X) ≤ gnC R := pCoreOf_le_gnC_of_le (T := R) hQR
  have hPL : pCoreOf 2 L ≤ pCoreOf 2 (⊤ : Subgroup X) := by
    have hchar : ((pCoreOf 2 L).subgroupOf L).Characteristic := by
      have h : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
        rw [CFSG.Open.pCoreOf, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
      rw [h]; exact CFSG.pCore_characteristic
    have hN : (pCoreOf 2 L).Normal :=
      CFSG.RankThree.PartOne.OddCore37.normal_of_characteristic
        (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hchar
    rw [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore 2]
    exact CFSG.LieType.BorelTits.le_pCore 2 hN
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hQW' : ⁅pCoreOf 2 L, L⁆ ≤ gnV R :=
    (Subgroup.commutator_mono hPL le_rfl).trans hQL
  have hQC' : pCoreOf 2 L ≤ Subgroup.centralizer (gnV R : Set X) := hPL.trans hQW
  have hLC' : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (gnV R : Set X)) := by
    have hEq : L ⊓ Subgroup.centralizer (gnV R : Set X) =
        L ⊓ pCoreOf 2 (⊤ : Subgroup X) := by
      rw [← hCeq]
      rfl
    rw [hEq]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup X)).to_le inf_le_right
  exact inClassXBlock_of_naturalSectionOn (W := gnV R) (L := L) (M := ⊤) (n := 11)
    ⟨5, by norm_num⟩ (by norm_num) hW le_top
    (Subgroup.le_normalizer_of_normal) (Subgroup.le_normalizer_of_normal)
    hLodd hQW' hQC' hLC' hnat

theorem exists_char_normal_of_s11
    {L R : Subgroup X} (hC : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup X)) (hLn : L.Normal)
    (hLodd : L = Subgroup.closure {x : X | x ∈ L ∧ Odd (orderOf x)})
    (φ : X →* Equiv.Perm (Fin 11)) (hφ : Function.Surjective φ)
    (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)) (hLker : ¬ L ≤ φ.ker)
    (hQR : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ R) (hR2 : IsPGroup 2 R)
    {i j : Fin 11} (hij : i ≠ j)
    (hNR : (Subgroup.normalizer (R : Set X)).map φ =
      Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 11))))
    (hnoX : ¬ CFSG.AGLEmbedding.InClassXBlock L) :
    ∃ T₀ : Subgroup X, T₀ ≠ ⊥ ∧ T₀ ≤ R ∧ (T₀.subgroupOf R).Characteristic ∧ T₀.Normal := by
  classical
  haveI hQn : (pCoreOf 2 (⊤ : Subgroup X)).Normal := normal_pCoreOf_top
  have hL : L.map φ = alternatingGroup (Fin 11) :=
    map_eq_alternatingGroup_of_closure_odd (n := 11) (by norm_num) hLn hLodd φ hφ hLker
  have hRmap : R.map φ = Subgroup.zpowers (Equiv.swap i j) :=
    map_eq_zpowers_swap (n := 11) (by norm_num) φ hφ hker hQR hR2 hij hNR
  have hsup : L ⊔ R = ⊤ :=
    sup_eq_top_of_map_eq φ (by rw [hker]; exact hQR) hL hij hRmap
  have hRne : R ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (R.map φ) = 1 := by
      rw [hbot, Subgroup.map_bot, Subgroup.card_bot]
    have h2 : Nat.card (Subgroup.zpowers (Equiv.swap i j)) = 2 := by
      rw [Nat.card_zpowers,
        Equiv.Perm.IsSwap.orderOf (Equiv.Perm.swap_isSwap_iff.mpr hij)]
    rw [hRmap] at h1
    omega
  have hW : CFSG.Open.IsElemAbelian 2 (gnV R) :=
    CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.isElemAbelian_gnV_of_le hC hQR
  have hWle : gnV R ≤ R :=
    CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.gnV_le_of_le hC hQR
  have hWQ : gnV R ≤ pCoreOf 2 (⊤ : Subgroup X) := gnV_le_pCoreOf_of_le hC hQR
  have hQW : pCoreOf 2 (⊤ : Subgroup X) ≤ gnC R := pCoreOf_le_gnC_of_le (T := R) hQR
  by_cases hLW : L ≤ gnC R
  · exact ⟨omegaOneCenterOf R, CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hR2 hRne,
      CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le R,
      CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf R,
      normal_omegaOneCenterOf_of_le_gnC hLn hsup hLW⟩
  · have hCeq : gnC R = pCoreOf 2 (⊤ : Subgroup X) :=
      gnC_eq_pCoreOf (n := 11) (by norm_num) φ hφ hker hL hQR hLW
    by_cases hJ : thompsonJ R ≤ pCoreOf 2 (⊤ : Subgroup X)
    · exact ⟨thompsonJ R, CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hR2 hRne,
        CFSG.Quasithin.B6.thompsonJ_le R,
        CFSG.QuasithinUnique.Setup.characteristic_thompsonJ R,
        normal_thompsonJ_of_le_pCoreOf hQR hJ⟩
    ·
      have hJ' : ¬ thompsonJ R ≤ Subgroup.centralizer (gnV R : Set X) := by
        intro h
        apply hJ
        rwa [← hCeq]
      obtain ⟨A, hA, hAR, hAW, hoff⟩ :=
        exists_offender_of_not_thompsonJ_le (R := R) (W := gnV R) hW hWle hJ'
      haveI hWn : (gnV R).Normal := normal_gnV R
      have hnat : NaturalSectionOn (gnV R) L ⊤ 11 :=
        naturalSectionOn_top_of_offender (W := gnV R) (L := L) (A := A) (n := 11)
          hW hWn hLn (by norm_num) φ (hker.trans hCeq.symm) hL hA hAW hoff
      obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by norm_num)
      let P : Subgroup X :=
        (fixingSubgroup (Equiv.Perm (Fin 11)) ({i, j, k}ᶜ : Set (Fin 11))).comap φ
      have hRP : R ≤ P := le_comap_fixingSubgroup φ hRmap
      have hQP : pCoreOf 2 (⊤ : Subgroup X) ≤ P := hQR.trans hRP
      have hmin : MinParabolic P R R :=
        minParabolic_comap_fixingSubgroup φ hφ hker hQR hR2 hij hki.symm hkj.symm hRmap
      have hcharP : CFSG.QuasithinUnique.CharTwo P :=
        charTwo_comap_fixingSubgroup φ hC hQR hRmap
      have hperfP : perfectCore P = ⊥ :=
        perfectCore_comap_fixingSubgroup_eq_bot φ hker hQR hRmap
      have hsupNP : Subgroup.normalizer (R : Set X) ⊔ P = ⊤ :=
        normalizer_sup_comap_fixingSubgroup_eq_top φ hφ hker hQR hij hki.symm hkj.symm hRmap hNR
      obtain ⟨C₁, C₂, hpair⟩ := CFSG.Quasithin.theoremC118 X R hR2 hRne
      have hconcl : Concl1Gen C₁ C₂ P R :=
        CFSG.AGLEmbeddingD2.McLaughlin.A7Six.concl1_over hpair rfl hpair.2.1 hmin hcharP
          (by rw [hperfP]; exact bot_le)
      have hC₁R : C₁ ≤ R := hpair.2.1.trans (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le R)
      have hC₂R : C₂ ≤ R := hpair.2.2.2.2.1.trans (CFSG.Quasithin.C1GN.baum_le R)
      have hC₂char : (C₂.subgroupOf R).Characteristic :=
        CFSG.Quasithin.C1GN.characteristic_subgroupOf_trans (CFSG.Quasithin.C1GN.baum_le R)
          hpair.2.2.2.2.1 (CFSG.Quasithin.C1GN.characteristic_baum R) hpair.2.2.2.2.2.1
      rcases hconcl with hC₁Z | hPC₂ | hblock
      · refine ⟨C₁, hpair.1, hC₁R, hpair.2.2.1,
          normal_of_subgroupOf_characteristic_of_sup_eq_top hC₁R hpair.2.2.1 hsupNP
            ((Subgroup.le_centralizer_iff.mpr
              (hC₁Z.trans (inf_le_right : centerOf _ ≤ Subgroup.centralizer _))).trans
              (Subgroup.centralizer_le_normalizer _))⟩
      · refine ⟨C₂, hpair.2.2.2.1, hC₂R, hC₂char,
          normal_of_subgroupOf_characteristic_of_sup_eq_top hC₂R hC₂char hsupNP hPC₂⟩
      ·
        exfalso
        obtain ⟨K, hKchi, -, -⟩ := hblock
        exact hnoX (inClassXBlock_of_isChiBlock hLn hLodd hφ hker hL hCeq hW hWQ hQR hQP hKchi hnat)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
