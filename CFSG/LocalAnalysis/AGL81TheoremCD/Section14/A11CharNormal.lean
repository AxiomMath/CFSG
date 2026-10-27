module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.S11Setup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NaturalSectionOfOffender
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.LemmaF
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FiveThreeBridge
import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClCells
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Permutation.TranspositionCentralizer
public import CFSG.LieType.BorelTits.Basic
import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderOfNatural

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.AGLEmbeddingD2.GN
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {X : Type} [Group X] [Finite X]

theorem map_eq_alternatingGroup_of_range_eq {n : ℕ} (hn : 5 ≤ n) {L : Subgroup X}
    (hLn : L.Normal) (φ : X →* Equiv.Perm (Fin n))
    (hrange : φ.range = alternatingGroup (Fin n)) (hLker : ¬ L ≤ φ.ker) :
    L.map φ = alternatingGroup (Fin n) := by
  classical
  have hle : L.map φ ≤ alternatingGroup (Fin n) := by
    rw [← hrange]
    exact Subgroup.map_le_range φ L
  let N : Subgroup (alternatingGroup (Fin n)) := (L.map φ).subgroupOf (alternatingGroup (Fin n))
  have hNmap : N.map (alternatingGroup (Fin n)).subtype = L.map φ :=
    Subgroup.map_subgroupOf_eq_of_le hle
  have hNnormal : N.Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle, Subgroup.le_normalizer_iff]
    intro σ hσ k hk
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact hσ)
    obtain ⟨l, hlL, rfl⟩ := Subgroup.mem_map.mp hk
    rw [← hg]
    have hmul : φ g * φ l * (φ g)⁻¹ = φ (g * l * g⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [hmul]
    exact Subgroup.mem_map_of_mem φ (hLn.conj_mem l hlL g)
  haveI : N.Normal := hNnormal
  haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  have hNne : N ≠ ⊥ := by
    intro hbot
    apply hLker
    rw [← Subgroup.map_eq_bot_iff L, ← hNmap, hbot, Subgroup.map_bot]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · exact absurd hbot hNne
  · rw [← hNmap, htop, Subgroup.map_top, Subgroup.range_subtype]

private theorem not_isPGroup_two_alternatingGroup_fin_eleven :
    ¬ IsPGroup 2 (alternatingGroup (Fin 11)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h
  have hcard : Nat.card (alternatingGroup (Fin 11)) = 19958400 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have h3 : 3 ∣ 2 ^ n := by
    rw [← hn, hcard]
    norm_num
  have h2 := Nat.prime_three.dvd_of_dvd_pow h3
  norm_num at h2

theorem false_of_range_eq_alternatingGroup_of_range_eq_top
    {φ θ : X →* Equiv.Perm (Fin 11)} (hker : φ.ker = θ.ker)
    (hφ : φ.range = alternatingGroup (Fin 11)) (hθ : θ.range = ⊤) : False := by
  classical
  have h1 : Nat.card (X ⧸ φ.ker) = Nat.card (alternatingGroup (Fin 11)) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hφ]
  have h2 : Nat.card (X ⧸ θ.ker) =
      Nat.card (⊤ : Subgroup (Equiv.Perm (Fin 11))) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv, hθ]
  rw [hker] at h1
  rw [h2, Subgroup.card_top] at h1
  have h3 := two_mul_nat_card_alternatingGroup (α := Fin 11)
  have hpos : 0 < Nat.card (alternatingGroup (Fin 11)) := Nat.card_pos
  omega

private theorem exists_swap_mem_of_offenderShape {E : Subgroup (Equiv.Perm (Fin 11))}
    (hE2 : IsPGroup 2 E) (hEne : E ≠ ⊥) (hshape : Offender.OffenderShapeConcl E) :
    ∃ i j : Fin 11, i ≠ j ∧ Equiv.swap i j ∈ E := by
  classical
  have hfix : ∃ p, ∀ g ∈ E, g p = p := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨p, hp⟩ := hE2.nonempty_fixed_point_of_prime_not_dvd_card (Fin 11)
      (by rw [Nat.card_fin]; norm_num)
    exact ⟨p, fun g hg => by
      have h := (MulAction.mem_fixedPoints.mp hp) ⟨g, hg⟩
      simpa using h⟩
  have hEeq : E = Offender.orbitStab E := (hshape.1 hfix).2
  have hmove : ∃ g ∈ E, ∃ i : Fin 11, g i ≠ i := by
    by_contra h
    push Not at h
    apply hEne
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    exact Equiv.ext (fun i => h g hg i)
  obtain ⟨g, hgE, i, hi⟩ := hmove
  refine ⟨i, g i, hi.symm, ?_⟩
  have hswap : Equiv.swap i (g i) ∈ Offender.orbitStab E :=
    Classif.swap_mem_orbitStab hgE i
  rwa [← hEeq] at hswap

private theorem false_of_surjective_theta_of_a11 {T : Subgroup X}
    (φ : X →* Equiv.Perm (Fin 11))
    (θ : ↥(⊤ : Subgroup X) →* Equiv.Perm (Fin 11))
    (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hrange : φ.range = alternatingGroup (Fin 11))
    (hCeq : gnC T = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hθtop : θ.range = ⊤)
    (hθker : ∀ m : ↥(⊤ : Subgroup X), θ m = 1 →
      (m : X) ∈ Subgroup.centralizer (gnV T : Set X)) :
    False := by
  classical
  let θ' : X →* Equiv.Perm (Fin 11) := θ.comp (Subgroup.topEquiv (G := X)).symm.toMonoidHom
  have hθ'apply : ∀ x : X, θ' x = θ ⟨x, Subgroup.mem_top x⟩ := by
    intro x
    change θ ((Subgroup.topEquiv (G := X)).symm x) = θ ⟨x, Subgroup.mem_top x⟩
    exact congrArg θ (Subtype.ext (Subgroup.topEquiv_symm_apply_coe x))
  have hθ'top : θ'.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro σ
    obtain ⟨m, hm⟩ := MonoidHom.range_eq_top.mp hθtop σ
    refine ⟨Subgroup.topEquiv m, ?_⟩
    change θ ((Subgroup.topEquiv (G := X)).symm (Subgroup.topEquiv m)) = σ
    rw [MulEquiv.symm_apply_apply]
    exact hm
  have hQn : (CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)).Normal := normal_pCoreOf_top
  have hQ2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup X)
  let N : Subgroup (Equiv.Perm (Fin 11)) :=
    ((CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)).subgroupOf ⊤).map θ
  have hN2 : IsPGroup 2 N := by
    have hQsub2 : IsPGroup 2 ((CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)).subgroupOf ⊤) :=
      hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe (le_top : _ ≤ ⊤)).symm
    exact hQsub2.map θ
  have hNn : N.Normal :=
    (hQn.subgroupOf ⊤).map θ (MonoidHom.range_eq_top.mp hθtop)
  have hNbot : N = ⊥ := by
    by_contra hNne
    haveI : N.Normal := hNn
    have hnt : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNne
    have hAltN : alternatingGroup (Fin 11) ≤ N :=
      Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 11) (by norm_num) hnt
    exact not_isPGroup_two_alternatingGroup_fin_eleven (hN2.to_le hAltN)
  have hQker : (CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)).subgroupOf ⊤ ≤ θ.ker :=
    (Subgroup.map_eq_bot_iff _).mp hNbot
  have hQle : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ θ'.ker := by
    intro q hq
    rw [MonoidHom.mem_ker, hθ'apply]
    exact MonoidHom.mem_ker.mp (hQker (Subgroup.mem_subgroupOf.mpr hq))
  have hkerle : θ'.ker ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) := by
    intro x hx
    have hx1 : θ' x = 1 := hx
    have hxW : x ∈ Subgroup.centralizer (gnV T : Set X) :=
      hθker ⟨x, Subgroup.mem_top x⟩ (by rwa [← hθ'apply x])
    have hxW' : x ∈ gnC T := hxW
    rwa [hCeq] at hxW'
  exact false_of_range_eq_alternatingGroup_of_range_eq_top
    (φ := φ) (θ := θ') (hker.trans (le_antisymm hkerle hQle).symm) hrange hθ'top

private theorem false_of_offender_of_a11
    {L T A : Subgroup X} (hLn : L.Normal)
    (φ : X →* Equiv.Perm (Fin 11))
    (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hrange : φ.range = alternatingGroup (Fin 11))
    (hL : L.map φ = alternatingGroup (Fin 11))
    (hCeq : gnC T = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hW : CFSG.Open.IsElemAbelian 2 (gnV T)) (hWle : gnV T ≤ T)
    (hAmax : CFSG.Quasithin.IsMaxElemAbelian T A) (hAW : ¬ A ≤ gnC T)
    (hoff : Nat.card (gnV T) ≤ (gnC T).relIndex A *
      Nat.card ↥(gnV T ⊓ Subgroup.centralizer (A : Set X))) :
    False := by
  classical
  have hWn : (gnV T).Normal := normal_gnV T
  have hnat : NaturalSectionOn (gnV T) L ⊤ 11 :=
    naturalSectionOn_top_of_offender (W := gnV T) (L := L) (A := A) (n := 11)
      hW hWn hLn (by norm_num) φ (hker.trans hCeq.symm) hL hAmax.2.1 hAW hoff
  obtain ⟨π, θ, hπ, -, hLθ, hequiv, hθker⟩ := hnat
  have hU : ⁅gnV T, L⁆ ≤ gnV T := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_right (H := L)
      (K := gnV T)).mp Subgroup.le_normalizer_of_normal
  have hshape : Offender.OffenderShapeConcl ((A.subgroupOf ⊤).map θ) :=
    offender_shape_of_section (d := 11) (Or.inr (by norm_num)) hπ hequiv
      (isElemAb2_of_isElemAbelian hW) hWle hU
      (isElemAb2_of_isElemAbelian hAmax.2.1) hAmax.1 le_top
      (fun B hBT hB => hAmax.2.2 B hBT (isElemAbelian_of_isElemAb2 hB)) hθker
  let E : Subgroup (Equiv.Perm (Fin 11)) := (A.subgroupOf ⊤).map θ
  have hE2 : IsPGroup 2 E := by
    have hAp : IsPGroup 2 (A.subgroupOf ⊤) :=
      hAmax.2.1.isPGroup.of_equiv
        (Subgroup.subgroupOfEquivOfLe (le_top : A ≤ ⊤)).symm
    exact hAp.map θ
  have hEne : E ≠ ⊥ := by
    intro hbot
    apply hAW
    intro a ha
    have hmem : θ ⟨a, Subgroup.mem_top a⟩ ∈ E := by
      rw [show E = (A.subgroupOf ⊤).map θ from rfl]
      exact Subgroup.mem_map_of_mem θ (Subgroup.mem_subgroupOf.mpr ha)
    rw [hbot] at hmem
    exact hθker ⟨a, Subgroup.mem_top a⟩ (by simpa using hmem)
  obtain ⟨i, j, hij, hswapE⟩ := exists_swap_mem_of_offenderShape hE2 hEne hshape
  have hswap : Equiv.swap i j ∈ θ.range :=
    Subgroup.map_le_range θ (A.subgroupOf ⊤) (by
      rw [show E = (A.subgroupOf ⊤).map θ from rfl] at hswapE
      exact hswapE)
  have hAlt : alternatingGroup (Fin 11) ≤ θ.range := by
    intro σ hσ
    obtain ⟨l, hlL, hlM, hval⟩ := hLθ σ hσ
    exact MonoidHom.mem_range.mpr ⟨⟨l, hlM⟩, hval⟩
  have hθtop : θ.range = ⊤ := by
    rw [eq_top_iff, ← CFSG.Permutation.TranspositionCentralizer.alternatingGroup_sup_zpowers_swap
      (α := Fin 11) hij]
    exact sup_le hAlt (Subgroup.zpowers_le.mpr hswap)
  exact false_of_surjective_theta_of_a11 φ θ hker hrange hCeq hθtop hθker

private theorem ne_bot_of_pCoreOf_le_of_range_eq {T : Subgroup X}
    (hC : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup X)) (φ : X →* Equiv.Perm (Fin 11))
    (hrange : φ.range = alternatingGroup (Fin 11))
    (hQT : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ T) : T ≠ ⊥ := by
  intro hT
  have hQbot : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) = ⊥ :=
    le_bot_iff.mp (hQT.trans (le_of_eq hT))
  have htop : (⊤ : Subgroup X) = ⊥ := by
    have hcent : Subgroup.centralizer
        ((⊥ : Subgroup X) : Set X) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy1 : y = 1 := by simpa using hy
      simp [hy1]
    have h := hC
    change (⊤ : Subgroup X) ⊓ Subgroup.centralizer
      ((CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)) : Set X) ≤
        CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) at h
    rw [hQbot, hcent, inf_top_eq] at h
    exact le_bot_iff.mp h
  have hx1 : ∀ x : X, x = 1 := by
    intro x
    have hxbot : x ∈ (⊥ : Subgroup X) := by rw [← htop]; exact Subgroup.mem_top x
    simpa using hxbot
  obtain ⟨σ, hσne⟩ := exists_ne (1 : alternatingGroup (Fin 11))
  have hσmem : (σ : Equiv.Perm (Fin 11)) ∈ alternatingGroup (Fin 11) := σ.2
  have hσrange : (σ : Equiv.Perm (Fin 11)) ∈ φ.range := by
    rw [hrange]
    exact hσmem
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hσrange
  refine hσne (Subtype.ext ?_)
  rw [← hx, hx1 x, map_one]
  simp

theorem exists_char_normal_of_a11
    {L T : Subgroup X} (hC : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup X)) (hLn : L.Normal)
    (φ : X →* Equiv.Perm (Fin 11)) (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hrange : φ.range = alternatingGroup (Fin 11)) (hLker : ¬ L ≤ φ.ker)
    (hQT : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ T) (hT2 : IsPGroup 2 T) :
    ∃ C : Subgroup X, C ≠ ⊥ ∧ C ≤ T ∧ (C.subgroupOf T).Characteristic ∧ C.Normal := by
  classical
  have hL : L.map φ = alternatingGroup (Fin 11) :=
    map_eq_alternatingGroup_of_range_eq (by norm_num) hLn φ hrange hLker
  have hsup : L ⊔ T = ⊤ := by
    have hmap : (L ⊔ T).map φ = φ.range := by
      rw [Subgroup.map_sup, hL, hrange]
      exact sup_eq_left.mpr (by rw [← hrange]; exact Subgroup.map_le_range φ T)
    have hcomap := Subgroup.comap_map_eq φ (L ⊔ T)
    rw [hmap] at hcomap
    have hrangecomap : (φ.range).comap φ = ⊤ := by
      have h := Subgroup.comap_map_eq φ (⊤ : Subgroup X)
      rwa [Subgroup.map_top, top_sup_eq] at h
    rw [hrangecomap] at hcomap
    have hkerle : φ.ker ≤ L ⊔ T := by
      rw [hker]
      exact hQT.trans le_sup_right
    rw [sup_eq_left.mpr hkerle] at hcomap
    exact hcomap.symm
  have hTne : T ≠ ⊥ := ne_bot_of_pCoreOf_le_of_range_eq hC φ hrange hQT
  have hW : CFSG.Open.IsElemAbelian 2 (gnV T) :=
    CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.isElemAbelian_gnV_of_le hC hQT
  have hWle : gnV T ≤ T :=
    CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.gnV_le_of_le hC hQT
  by_cases hLW : L ≤ gnC T
  · exact ⟨CFSG.Quasithin.omegaOneCenterOf T,
      CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hT2 hTne,
      CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le T,
      CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf T,
      normal_omegaOneCenterOf_of_le_gnC hLn hsup hLW⟩
  · have hKz := center_quotient_pCore_eq_bot_of_map (n := 11) (by norm_num) hLn φ hker hL
    have hKsimple := isSimpleGroup_quotient_pCore_of_map (n := 11) (by norm_num) hLn φ hker hL
    have hCeq : gnC T = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) :=
      (gnC_eq_pCoreOf_or_le_gnC (K := L) (S := T) hC hT2 hQT hLn hsup hKz hKsimple).resolve_left hLW
    by_cases hJ : CFSG.Quasithin.thompsonJ T ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)
    · exact ⟨CFSG.Quasithin.thompsonJ T,
        CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hT2 hTne,
        CFSG.Quasithin.B6.thompsonJ_le T,
        CFSG.QuasithinUnique.Setup.characteristic_thompsonJ T,
        normal_thompsonJ_of_le_pCoreOf hQT hJ⟩
    · exfalso
      have hJ' : ¬ CFSG.Quasithin.thompsonJ T ≤
          Subgroup.centralizer (gnV T : Set X) := by
        intro h
        apply hJ
        have h' : CFSG.Quasithin.thompsonJ T ≤ gnC T := h
        rwa [hCeq] at h'
      obtain ⟨A, hAmax, hAW, hoff⟩ :=
        exists_maxElemAbelian_offender_of_not_thompsonJ_le (R := T) (W := gnV T) hW hWle hJ'
      exact false_of_offender_of_a11 hLn φ hker hrange hL hCeq hW hWle hAmax hAW hoff

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
