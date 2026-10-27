module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.S11CharNormal
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.S11Setup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.S11Parabolic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NaturalSectionOfOffender
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.LemmaF
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.S11BaumSwap
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ParabolicComap
import CFSG.Permutation.FivePairs
import CFSG.Quasithin.Background.C118NoOuter
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.C126Over
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FiveThreeBridge
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderSwaps
import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalBasic
import CFSG.RankThree.PartOne.FIS.PermFacts

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.AGLEmbeddingD2.GN
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

private theorem isSwap_pairSwap (k : Fin 5) : (CFSG.Permutation.FivePairs.pairSwap k).IsSwap := by
  refine Equiv.Perm.swap_isSwap_iff.mpr ?_
  intro h
  have h2 : 2 * (k : ℕ) = 2 * (k : ℕ) + 1 := congrArg Fin.val h
  omega

private theorem map_baum_le_pairGroup {T : Subgroup X} {θ : X →* Equiv.Perm (Fin 11)}
    (hT2 : IsPGroup 2 T)
    {S : Set (Equiv.Perm (Fin 11))} (hS : ∀ t ∈ S, t.IsSwap)
    (hST : CFSG.Permutation.FivePairs.pairGroup ≤ T.map θ)
    (hbaum : (CFSG.Quasithin.baum T).map θ = Subgroup.closure S) :
    (CFSG.Quasithin.baum T).map θ ≤ CFSG.Permutation.FivePairs.pairGroup := by
  rw [hbaum]
  refine (Subgroup.closure_le _).mpr ?_
  intro t ht
  have hT2map : IsPGroup 2 (T.map θ) := hT2.map θ
  have htB : t ∈ (CFSG.Quasithin.baum T).map θ := by
    rw [hbaum]; exact Subgroup.subset_closure ht
  have htT : t ∈ T.map θ := Subgroup.map_mono (CFSG.Quasithin.C1GN.baum_le T) htB
  have hcomm : ∀ k : Fin 5, Commute t (CFSG.Permutation.FivePairs.pairSwap k) := fun k =>
    CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender.commute_swap_of_pGroup
      hT2map htT (hST (Subgroup.subset_closure (Set.mem_range_self k)))
      (hS t ht) (isSwap_pairSwap k)
  exact CFSG.Permutation.FivePairs.swap_mem_pairGroup_of_commute (hS t ht) hcomm

private theorem exists_conj_pairGroup_le_map {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) {θ : X →* Equiv.Perm (Fin 11)}
    (hθ : Function.Surjective θ) (hθker : θ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    {S : Set (Equiv.Perm (Fin 11))} (hS : ∀ t ∈ S, t.IsSwap)
    (hbaum : (CFSG.Quasithin.baum T).map θ = Subgroup.closure S) :
    ∃ θ' : X →* Equiv.Perm (Fin 11), Function.Surjective θ' ∧
      θ'.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ∧
      CFSG.Permutation.FivePairs.pairGroup ≤ T.map θ' ∧
      (CFSG.Quasithin.baum T).map θ' ≤ CFSG.Permutation.FivePairs.pairGroup := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQT : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ T := hT.pCoreOf_le
  have hT2 : IsPGroup 2 T := hT.2.1
  have hidx : ¬ 2 ∣ (T.map θ).index := by
    rw [Subgroup.index_map_eq T hθ (by rw [hθker]; exact hQT)]
    have h := hT.2.2
    rwa [CFSG.QuasithinUnique.index_subgroupOf_top T] at h
  let P : Sylow 2 (Equiv.Perm (Fin 11)) := (hT2.map θ).toSylow hidx
  obtain ⟨Q, hQ⟩ := CFSG.Permutation.FivePairs.isPGroup_pairGroup.exists_le_sylow
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 11)) P Q
  let θ' : X →* Equiv.Perm (Fin 11) := (MulAut.conj σ).toMonoidHom.comp θ
  have hθ' : Function.Surjective θ' := (MulAut.conj σ).surjective.comp hθ
  have hθ'ker : θ'.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) := by
    have hker : θ'.ker = θ.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      change (MulAut.conj σ) (θ x) = 1 ↔ θ x = 1
      constructor
      · intro hx
        exact (MulAut.conj σ).injective (by simpa using hx)
      · intro hx
        rw [hx]; simp
    rw [hker, hθker]
  have hQcoe : (Q : Subgroup (Equiv.Perm (Fin 11))) =
      (T.map θ).map (MulAut.conj σ).toMonoidHom := by
    rw [← hσ, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hpair_le : CFSG.Permutation.FivePairs.pairGroup ≤ T.map θ' := by
    calc CFSG.Permutation.FivePairs.pairGroup ≤ (Q : Subgroup _) := hQ
      _ = (T.map θ).map (MulAut.conj σ).toMonoidHom := hQcoe
      _ = T.map θ' := by rw [Subgroup.map_map]
  have hbaum' : (CFSG.Quasithin.baum T).map θ' =
      Subgroup.closure (((MulAut.conj σ).toMonoidHom) '' S) := by
    rw [show θ' = (MulAut.conj σ).toMonoidHom.comp θ from rfl,
      ← Subgroup.map_map, hbaum, MonoidHom.map_closure]
  refine ⟨θ', hθ', hθ'ker, hpair_le, ?_⟩
  exact map_baum_le_pairGroup hT2
    (fun t ht => by
      obtain ⟨s, hs, rfl⟩ := ht
      exact CFSG.RankThree.PartOne.FIS.PermFacts.isSwap_conj (hS s hs) σ) hpair_le hbaum'

private theorem sup_eq_top_of_isSylowTwoOf {L T : Subgroup X}
    {φ : X →* Equiv.Perm (Fin 11)} (hφ : Function.Surjective φ)
    (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hL : L.map φ = alternatingGroup (Fin 11)) (hT : IsSylowTwoOf T ⊤) : L ⊔ T = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQT : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ T := hT.pCoreOf_le
  have hidx : ¬ 2 ∣ (T.map φ).index := by
    rw [Subgroup.index_map_eq T hφ (by rw [hker]; exact hQT)]
    have h := hT.2.2
    rwa [CFSG.QuasithinUnique.index_subgroupOf_top T] at h
  have hnotle : ¬ T.map φ ≤ alternatingGroup (Fin 11) := by
    intro hle
    apply hidx
    have hrel := Subgroup.relIndex_mul_index hle
    rw [alternatingGroup.index_eq_two] at hrel
    exact ⟨_, by rw [hrel.symm, Nat.mul_comm]⟩
  have hsup : alternatingGroup (Fin 11) ⊔ T.map φ = ⊤ := by
    rcases CFSG.ComponentClassification.SymmetricLocal.eq_alternatingGroup_or_eq_top
      (le_sup_left : alternatingGroup (Fin 11) ≤ _) with h | h
    · exfalso
      exact hnotle (h ▸ le_sup_right)
    · exact h
  have hmap : (L ⊔ T).map φ = ⊤ := by
    rw [Subgroup.map_sup, hL, hsup]
  have hcomap := Subgroup.comap_map_eq φ (L ⊔ T)
  rw [hmap, Subgroup.comap_top,
    sup_eq_left.mpr (by rw [hker]; exact hQT.trans le_sup_right)] at hcomap
  exact hcomap.symm

private theorem exists_char_normal_of_le_centerOf {C₁ T R₀ : Subgroup X}
    {θ' : X →* Equiv.Perm (Fin 11)} {H : Fin 5 → Subgroup X}
    (hθ' : Function.Surjective θ')
    (hθ'ker : θ'.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hQR₀ : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ R₀)
    (hC₁R₀ : C₁ ≤ omegaOneCenterOf R₀) (hC₁ne : C₁ ≠ ⊥) (hC₁T : C₁ ≤ T)
    (hC₁char : (C₁.subgroupOf T).Characteristic)
    (hHmap : ∀ k, H k = (CFSG.Permutation.FivePairs.pairParabolic k).comap θ')
    (hcent : ∀ k, C₁ ≤ centerOf (H k)) :
    ∃ C : Subgroup X, C ≠ ⊥ ∧ C ≤ T ∧ (C.subgroupOf T).Characteristic ∧ C.Normal := by
  let Q : Subgroup X := CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)
  let D : Subgroup X := Subgroup.centralizer (C₁ : Set X)
  have hQD : Q ≤ D := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcR : c ∈ centerOf R₀ :=
      CFSG.Quasithin.C1GN.omegaOneCenterOf_le_centerOf R₀ (hC₁R₀ hc)
    exact (Subgroup.mem_centralizer_iff.mp hcR.2 q (hQR₀ hq)).symm
  have hHD : ∀ k, H k ≤ D := by
    intro k h hh
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcH : c ∈ centerOf (H k) := hcent k hc
    exact (Subgroup.mem_centralizer_iff.mp hcH.2 h hh).symm
  have hDmap : D.map θ' = ⊤ := by
    rw [eq_top_iff]
    calc ⊤ = ⨆ k, CFSG.Permutation.FivePairs.pairParabolic k :=
          CFSG.Permutation.FivePairs.iSup_pairParabolic.symm
      _ ≤ D.map θ' := by
          refine iSup_le fun k => ?_
          rw [← Subgroup.map_comap_eq_self_of_surjective hθ'
            (CFSG.Permutation.FivePairs.pairParabolic k), ← hHmap k]
          exact Subgroup.map_mono (hHD k)
  have hDtop : D = ⊤ := by
    apply top_unique
    intro x hx
    have hxmap : θ' x ∈ D.map θ' := by
      rw [hDmap]; exact Subgroup.mem_top _
    obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp hxmap
    have hmem : d⁻¹ * x ∈ θ'.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdx, inv_mul_cancel]
    have hmemD : d⁻¹ * x ∈ D := by
      rw [hθ'ker] at hmem
      exact hQD hmem
    have hx' : x = d * (d⁻¹ * x) := by group
    rw [hx']
    exact D.mul_mem hd hmemD
  refine ⟨C₁, hC₁ne, hC₁T, hC₁char, ?_⟩
  refine ⟨fun c hc g => ?_⟩
  have hg : g ∈ D := hDtop ▸ Subgroup.mem_top g
  have hcomm : c * g = g * c := Subgroup.mem_centralizer_iff.mp hg c hc
  have h : g * c * g⁻¹ = c := by
    calc g * c * g⁻¹ = c * g * g⁻¹ := by rw [hcomm.symm]
      _ = c := by group
  rwa [h]

private theorem exists_char_normal_of_s11_dichotomy
    {L T R₀ C₁ C₂ : Subgroup X}
    {θ' : X →* Equiv.Perm (Fin 11)} {H : Fin 5 → Subgroup X}
    (hLn : L.Normal)
    (hLodd : L = Subgroup.closure {x : X | x ∈ L ∧ Odd (orderOf x)})
    (φ : X →* Equiv.Perm (Fin 11)) (hφ : Function.Surjective φ)
    (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hL : L.map φ = alternatingGroup (Fin 11))
    (hCeq : gnC T = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hW : CFSG.Open.IsElemAbelian 2 (gnV T))
    (hWQ : gnV T ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hQT : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ T)
    (hnat : NaturalSectionOn (gnV T) L ⊤ 11)
    (hnoX : ¬ CFSG.AGLEmbedding.InClassXBlock L)
    (hθ' : Function.Surjective θ')
    (hθ'ker : θ'.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hQR₀ : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ R₀)
    (hpair : IsC118Pair T C₁ C₂)
    (hC₁R₀ : C₁ ≤ omegaOneCenterOf R₀)
    (hC₁T : C₁ ≤ T) (hC₁char : (C₁.subgroupOf T).Characteristic)
    (hC₂T : C₂ ≤ T) (hC₂charT : (C₂.subgroupOf T).Characteristic)
    (hC₂R₀ : C₂ ≤ R₀) (hC₂charR₀ : (C₂.subgroupOf R₀).Characteristic)
    (hHmap : ∀ k, H k = (CFSG.Permutation.FivePairs.pairParabolic k).comap θ')
    (hQR₀H : ∀ k, CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ H k)
    (hsupH : ∀ k, Subgroup.normalizer (R₀ : Set X) ⊔ H k = ⊤)
    (hconcl : ∀ k, Concl1Gen C₁ C₂ (H k) R₀) :
    ∃ C : Subgroup X, C ≠ ⊥ ∧ C ≤ T ∧ (C.subgroupOf T).Characteristic ∧ C.Normal := by
  by_cases hex : ∃ k, H k ≤ Subgroup.normalizer (C₂ : Set X)
  · obtain ⟨k, hk⟩ := hex
    exact ⟨C₂, hpair.2.2.2.1, hC₂T, hC₂charT,
      normal_of_subgroupOf_characteristic_of_sup_eq_top (C := C₂) (R := R₀) (P := H k)
        hC₂R₀ hC₂charR₀ (hsupH k) hk⟩
  · have hcent : ∀ k, C₁ ≤ centerOf (H k) := by
      intro k
      rcases hconcl k with hZ | hN | hblock
      · exact hZ
      · exact absurd hN (by
          intro h; exact hex ⟨k, h⟩)
      · exfalso
        obtain ⟨K, hKchi, -, -⟩ := hblock
        exact hnoX (inClassXBlock_of_isChiBlock hLn hLodd hφ hker hL hCeq hW hWQ hQT
          (hQR₀H k) hKchi hnat)
    exact exists_char_normal_of_le_centerOf hθ' hθ'ker hQR₀ hC₁R₀ hpair.1 hC₁T hC₁char
      hHmap hcent

private theorem exists_s11_conj_setup
    {L T : Subgroup X}
    (hC : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup X)) (hLn : L.Normal)
    (hLodd : L = Subgroup.closure {x : X | x ∈ L ∧ Odd (orderOf x)})
    (φ : X →* Equiv.Perm (Fin 11)) (hφ : Function.Surjective φ)
    (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    (hL : L.map φ = alternatingGroup (Fin 11))
    (hLW : ¬ L ≤ gnC T)
    (hJ : ¬ thompsonJ T ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)) :
    ∃ (θ' : X →* Equiv.Perm (Fin 11)) (R₀ : Subgroup X),
      R₀ = CFSG.Permutation.FivePairs.pairGroup.comap θ' ∧
      Function.Surjective θ' ∧ θ'.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ∧
      CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ R₀ ∧ baum T ≤ R₀ ∧ R₀ ≤ T ∧
      baum R₀ = baum T ∧ NaturalSectionOn (gnV T) L ⊤ 11 ∧
      gnC T = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ∧
      CFSG.Open.IsElemAbelian 2 (gnV T) ∧
      gnV T ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) := by
  classical
  let Q : Subgroup X := CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)
  have hQT : Q ≤ T := hT.pCoreOf_le
  have hCeq : gnC T = Q :=
    gnC_eq_pCoreOf (n := 11) (by norm_num) φ hφ hker hL hQT hLW
  have hW : CFSG.Open.IsElemAbelian 2 (gnV T) :=
    CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.isElemAbelian_gnV_of_le hC hQT
  have hWle : gnV T ≤ T :=
    CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.gnV_le_of_le hC hQT
  have hWQ : gnV T ≤ Q := gnV_le_pCoreOf_of_le hC hQT
  have hJ' : ¬ thompsonJ T ≤ Subgroup.centralizer (gnV T : Set X) := by
    intro h
    apply hJ
    have h2 : thompsonJ T ≤ gnC T := h
    rwa [hCeq] at h2
  obtain ⟨A, hA, hAT, hAW, hoff⟩ :=
    exists_offender_of_not_thompsonJ_le (R := T) (W := gnV T) hW hWle hJ'
  haveI hWn : (gnV T).Normal := normal_gnV T
  have hnat : NaturalSectionOn (gnV T) L ⊤ 11 :=
    naturalSectionOn_top_of_offender (W := gnV T) (L := L) (A := A) (n := 11)
      hW hWn hLn (by norm_num) φ (hker.trans hCeq.symm) hL hA hAW hoff
  obtain ⟨θ, hθ, hθker, S, hS, hbaum⟩ :=
    exists_map_baum_eq_closure_swaps hC hLn hLodd φ hφ hker hT hCeq hJ hnat
  obtain ⟨θ', hθ', hθ'ker, hpair_le, hbaum_le⟩ :=
    exists_conj_pairGroup_le_map hT hθ hθker hS hbaum
  let R₀ : Subgroup X := CFSG.Permutation.FivePairs.pairGroup.comap θ'
  have hQR₀ : Q ≤ R₀ := by
    intro q hq
    rw [Subgroup.mem_comap]
    have hq' : θ' q = 1 := by
      rw [← MonoidHom.mem_ker, hθ'ker]; exact hq
    rw [hq']
    exact CFSG.Permutation.FivePairs.pairGroup.one_mem
  have hBR₀ : baum T ≤ R₀ := by
    intro x hx
    rw [Subgroup.mem_comap]
    exact hbaum_le (Subgroup.mem_map_of_mem θ' hx)
  have hR₀T : R₀ ≤ T := by
    have hmono : R₀ ≤ (T.map θ').comap θ' := Subgroup.comap_mono hpair_le
    rwa [Subgroup.comap_map_eq θ' T,
      sup_eq_left.mpr (by rw [hθ'ker]; exact hQT)] at hmono
  have hbaum_eq : baum R₀ = baum T := (baum_eq_of_le hBR₀ hR₀T).symm
  exact ⟨θ', R₀, rfl, hθ', hθ'ker, hQR₀, hBR₀, hR₀T, hbaum_eq, hnat, hCeq, hW, hWQ⟩

private theorem exists_char_normal_of_s11_offender
    {L T : Subgroup X}
    (hC : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup X)) (hLn : L.Normal)
    (hLodd : L = Subgroup.closure {x : X | x ∈ L ∧ Odd (orderOf x)})
    (φ : X →* Equiv.Perm (Fin 11)) (hφ : Function.Surjective φ)
    (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) (hTne : T ≠ ⊥)
    (hnoX : ¬ CFSG.AGLEmbedding.InClassXBlock L)
    (hL : L.map φ = alternatingGroup (Fin 11))
    (hLW : ¬ L ≤ gnC T) (hJ : ¬ thompsonJ T ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)) :
    ∃ C : Subgroup X, C ≠ ⊥ ∧ C ≤ T ∧ (C.subgroupOf T).Characteristic ∧ C.Normal := by
  classical
  let Q : Subgroup X := CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)
  obtain ⟨θ', R₀, hR₀def, hθ', hθ'ker, hQR₀, hBR₀, hR₀T, hbaum_eq, hnat, hCeq, hW, hWQ⟩ :=
    exists_s11_conj_setup hC hLn hLodd φ hφ hker hT hL hLW hJ
  have hQT : Q ≤ T := hT.pCoreOf_le
  have hT2 : IsPGroup 2 T := hT.2.1
  have hθ'ker2 : IsPGroup 2 θ'.ker := by
    rw [hθ'ker]; exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤
  obtain ⟨C₁, C₂, hpair⟩ := CFSG.Quasithin.theoremC118 X T hT2 hTne
  have hZTQ : centerOf T ≤ Q := by
    intro z hz
    exact hC ⟨Subgroup.mem_top z, Subgroup.centralizer_le hQT hz.2⟩
  have hcenterTR₀ : centerOf T ≤ centerOf R₀ := by
    refine le_inf (hZTQ.trans hQR₀) ?_
    exact inf_le_right.trans (Subgroup.centralizer_le hR₀T)
  have hC₁R₀ : C₁ ≤ omegaOneCenterOf R₀ := by
    refine hpair.2.1.trans ?_
    exact Subgroup.closure_mono (fun x hx => ⟨hcenterTR₀ hx.1, hx.2⟩)
  have hC₁T : C₁ ≤ T :=
    (hC₁R₀.trans (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_self R₀)).trans hR₀T
  have hC₂T : C₂ ≤ T := hpair.2.2.2.2.1.trans (CFSG.Quasithin.C1GN.baum_le T)
  have hC₂charT : (C₂.subgroupOf T).Characteristic :=
    CFSG.Quasithin.C1GN.characteristic_subgroupOf_trans (CFSG.Quasithin.C1GN.baum_le T)
      hpair.2.2.2.2.1 (CFSG.Quasithin.C1GN.characteristic_baum T) hpair.2.2.2.2.2.1
  have hC₂BR₀ : C₂ ≤ baum R₀ := by
    rw [hbaum_eq]
    exact hpair.2.2.2.2.1
  have hC₂charBaumR₀ : (C₂.subgroupOf (baum R₀)).Characteristic := by
    rw [hbaum_eq]
    exact hpair.2.2.2.2.2.1
  have hC₂charR₀ : (C₂.subgroupOf R₀).Characteristic :=
    CFSG.Quasithin.C1GN.characteristic_subgroupOf_trans (CFSG.Quasithin.C1GN.baum_le R₀)
      hC₂BR₀ (CFSG.Quasithin.C1GN.characteristic_baum R₀) hC₂charBaumR₀
  have hC₂R₀ : C₂ ≤ R₀ := hC₂BR₀.trans (CFSG.Quasithin.C1GN.baum_le R₀)
  let H : Fin 5 → Subgroup X := fun k => (CFSG.Permutation.FivePairs.pairParabolic k).comap θ'
  have hQR₀H : ∀ k, Q ≤ H k := fun k => by
    change Q ≤ (CFSG.Permutation.FivePairs.pairParabolic k).comap θ'
    exact (hR₀def ▸ hQR₀).trans
      (Subgroup.comap_mono (f := θ') (CFSG.Permutation.FivePairs.pairGroup_le_pairParabolic k))
  have hHmap : ∀ k, H k = (CFSG.Permutation.FivePairs.pairParabolic k).comap θ' := fun k => rfl
  have hHmin : ∀ k, MinParabolic (H k) R₀ R₀ := fun k => by
    rw [hHmap k, hR₀def]
    exact minParabolic_comap_of_relIndex_eq_three θ' hθ' hθ'ker2
      CFSG.Permutation.FivePairs.isPGroup_pairGroup
      (CFSG.Permutation.FivePairs.pairGroup_le_pairParabolic k)
      (CFSG.Permutation.FivePairs.relIndex_pairGroup_pairParabolic k)
      (CFSG.Permutation.FivePairs.pairParabolic_not_le_normalizer k)
  have hHchar : ∀ k, CFSG.QuasithinUnique.CharTwo (H k) := fun k =>
    CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hC le_top (hQR₀H k)
  have hkerSolv : IsSolvable ↥θ'.ker := by
    haveI : Group.IsNilpotent ↥θ'.ker := hθ'ker2.isNilpotent
    exact IsNilpotent.to_isSolvable
  have hHperf : ∀ k, perfectCore (H k) = ⊥ := fun k =>
    perfectCore_comap_eq_bot θ' hkerSolv
      (CFSG.Permutation.FivePairs.isSolvable_pairParabolic k)
  have hHconcl : ∀ k, Concl1Gen C₁ C₂ (H k) R₀ := fun k =>
    CFSG.AGLEmbeddingD2.McLaughlin.A7Six.concl1_over hpair hbaum_eq hC₁R₀
      (hHmin k) (hHchar k) (by rw [hHperf k]; exact bot_le)
  have hNR₀ : Subgroup.normalizer (R₀ : Set X) =
      (Subgroup.normalizer
        (CFSG.Permutation.FivePairs.pairGroup : Set (Equiv.Perm (Fin 11)))).comap θ' := by
    rw [hR₀def]
    exact (Subgroup.comap_normalizer_eq_of_surjective
      (CFSG.Permutation.FivePairs.pairGroup) hθ').symm
  have hsupH : ∀ k, Subgroup.normalizer (R₀ : Set X) ⊔ H k = ⊤ := fun k => by
    rw [hNR₀]
    change (Subgroup.normalizer
        (CFSG.Permutation.FivePairs.pairGroup : Set (Equiv.Perm (Fin 11)))).comap θ' ⊔
      (CFSG.Permutation.FivePairs.pairParabolic k).comap θ' = ⊤
    rw [Subgroup.comap_sup_eq θ' _ _ hθ',
      CFSG.Permutation.FivePairs.normalizer_pairGroup_sup_pairParabolic k,
      Subgroup.comap_top]
  exact exists_char_normal_of_s11_dichotomy hLn hLodd φ hφ hker hL hCeq hW hWQ hQT hnat hnoX
    hθ' hθ'ker hQR₀ hpair hC₁R₀ hC₁T hpair.2.2.1 hC₂T hC₂charT hC₂R₀ hC₂charR₀ hHmap hQR₀H
    hsupH hHconcl

theorem exists_char_normal_of_s11_sylow
    {L T : Subgroup X}
    (hC : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup X)) (hLn : L.Normal)
    (hLodd : L = Subgroup.closure {x : X | x ∈ L ∧ Odd (orderOf x)})
    (φ : X →* Equiv.Perm (Fin 11)) (hφ : Function.Surjective φ)
    (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)) (hLker : ¬ L ≤ φ.ker)
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    (hnoX : ¬ CFSG.AGLEmbedding.InClassXBlock L) :
    ∃ C : Subgroup X, C ≠ ⊥ ∧ C ≤ T ∧ (C.subgroupOf T).Characteristic ∧ C.Normal := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup X := CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)
  have hQT : Q ≤ T := hT.pCoreOf_le
  have hT2 : IsPGroup 2 T := hT.2.1
  have hidxT : ¬ 2 ∣ (T.map φ).index := by
    rw [Subgroup.index_map_eq T hφ (by rw [hker]; exact hQT)]
    have h := hT.2.2
    rwa [CFSG.QuasithinUnique.index_subgroupOf_top T] at h
  have hTne : T ≠ ⊥ := by
    intro hbot
    apply hidxT
    rw [hbot, Subgroup.map_bot, Subgroup.index_bot, Nat.card_perm]
    exact Nat.dvd_factorial (by norm_num) (by norm_num)
  have hL : L.map φ = alternatingGroup (Fin 11) :=
    map_eq_alternatingGroup_of_closure_odd (n := 11) (by norm_num) hLn hLodd φ hφ hLker
  have hsupLT : L ⊔ T = ⊤ := sup_eq_top_of_isSylowTwoOf hφ hker hL hT
  by_cases hLW : L ≤ gnC T
  · exact ⟨omegaOneCenterOf T, CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hT2 hTne,
      CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le T,
      CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf T,
      normal_omegaOneCenterOf_of_le_gnC hLn hsupLT hLW⟩
  · by_cases hJ : thompsonJ T ≤ Q
    · exact ⟨thompsonJ T, CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hT2 hTne,
        CFSG.Quasithin.B6.thompsonJ_le T,
        CFSG.QuasithinUnique.Setup.characteristic_thompsonJ T,
        normal_thompsonJ_of_le_pCoreOf hQT hJ⟩
    · exact exists_char_normal_of_s11_offender hC hLn hLodd φ hφ hker hT hTne hnoX hL hLW hJ

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
