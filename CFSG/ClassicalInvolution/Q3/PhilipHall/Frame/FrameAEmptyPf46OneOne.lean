module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43Fac
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf44Block
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf23AViolA

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge.Fam
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_normalizer_of_mem_normalizer_tightCore (hΩ : HypOmegaGen Ω) {X P R : Subgroup G}
    (hP : P ∈ Ω) (hR : IsSylow2In R P) (hRX : R ≤ X) {u : G}
    (hu : u ∈ Subgroup.normalizer (tightCore (P ⊓ X) : Set G)) :
    u ∈ Subgroup.normalizer (P : Set G) := by
  have h1 : conjSub u (tightCore (P ⊓ X)) = tightCore (P ⊓ X) :=
    mem_normalizer_iff_conjSub_eq.mp hu
  have h2 : tightCore (P ⊓ X) ≤ conjSub u P := by
    rw [← h1]
    exact conjSub_mono ((tightCore_le _).trans inf_le_left)
  exact mem_normalizer_iff_conjSub_eq.mpr
    (eq_of_tightCore_inf_le hΩ hP (hΩ.conjInvariant u P hP) hR hRX h2).symm

theorem map_mem_USet_omegaAFam (hΩ : HypOmegaGen Ω) {X : Subgroup G} {U' : Subgroup ↥X}
    (hU : U' ∈ USet (omegaAFam Ω X)) : U'.map X.subtype ∈ USet Ω := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := map_mem_USet_restrict (Ω := omegaACore Ω X) hU
  obtain ⟨L, ⟨M, hM, ⟨P₀, hP₀, hP₀X⟩, rfl⟩, hRL⟩ := exists_isSylow2In_of_mem_RSet hR
  exact ⟨R, mem_RSet_of_isSylow2In hM (isSylow2In_of_core hΩ hM hP₀ hP₀X hRL), hUR, hcyc,
    hidx⟩

theorem mem_omegaStarNbr_of_omegaAFam (hΩ : HypOmegaGen Ω) {X P Q R : Subgroup G} (hP : P ∈ Ω)
    (hQ : Q ∈ Ω) (hR : IsSylow2In R P) (hRX : R ≤ X)
    (h : (tightCore (Q ⊓ X)).subgroupOf X ∈
      omegaStarNbr (omegaAFam Ω X) ((tightCore (P ⊓ X)).subgroupOf X)) :
    Q ∈ omegaStarNbr Ω P := by
  obtain ⟨-, hne, U', hU', hU'Q, hU'N⟩ := h
  have hPX : tightCore (P ⊓ X) ≤ X := (tightCore_le _).trans inf_le_right
  have hQX : tightCore (Q ⊓ X) ≤ X := (tightCore_le _).trans inf_le_right
  refine ⟨hQ, fun hQP => hne (by rw [hQP]), U'.map X.subtype, map_mem_USet_omegaAFam hΩ hU', ?_,
    ?_⟩
  · calc U'.map X.subtype ≤ ((tightCore (Q ⊓ X)).subgroupOf X).map X.subtype :=
          Subgroup.map_mono hU'Q
      _ = tightCore (Q ⊓ X) := Subgroup.map_subgroupOf_eq_of_le hQX
      _ ≤ Q := (tightCore_le _).trans inf_le_left
  · rintro _ ⟨u, hu, rfl⟩
    exact mem_normalizer_of_mem_normalizer_tightCore hΩ hP hR hRX
      ((mem_normalizer_subgroupOf_iff hPX).mpr (hU'N hu))

theorem exists_mem_dstarComp_of_omegaAFam (hΩ : HypOmegaGen Ω) {X P R : Subgroup G} (hP : P ∈ Ω)
    (hR : IsSylow2In R P) (hRX : R ≤ X) {Q' : Subgroup ↥X}
    (hQ' : Q' ∈ dstarComp (omegaAFam Ω X) ((tightCore (P ⊓ X)).subgroupOf X)) :
    ∃ Q ∈ Ω, (∃ R' : Subgroup G, IsSylow2In R' Q ∧ R' ≤ X) ∧
      Q' = (tightCore (Q ⊓ X)).subgroupOf X ∧ Q ∈ dstarComp Ω P := by
  induction hQ' with
  | refl => exact ⟨P, hP, ⟨R, hR, hRX⟩, rfl, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨Q, hQ, ⟨RQ, hRQ, hRQX⟩, rfl, hQd⟩ := ih
    obtain ⟨hcΦ, h | h⟩ := hbc
    · obtain ⟨Q₂, hQ₂, ⟨R₂, hR₂, hR₂X⟩, rfl⟩ := exists_of_mem_omegaAFam hcΦ
      exact ⟨Q₂, hQ₂, ⟨R₂, hR₂, hR₂X⟩, rfl,
        hQd.tail ⟨hQ₂, Or.inl (mem_omegaStarNbr_of_omegaAFam hΩ hQ hQ₂ hRQ hRQX h)⟩⟩
    · obtain ⟨Q₂, hQ₂, ⟨R₂, hR₂, hR₂X⟩, rfl⟩ := exists_of_mem_omegaAFam hcΦ
      exact ⟨Q₂, hQ₂, ⟨R₂, hR₂, hR₂X⟩, rfl,
        hQd.tail ⟨hQ₂, Or.inr (mem_omegaStarNbr_of_omegaAFam hΩ hQ₂ hQ hR₂ hR₂X h)⟩⟩

theorem oddCoreOf_le_conjStab_dstarComp_of_core (hΩ : HypOmegaGen Ω) {X L P : Subgroup G}
    (hΦ : HypOmegaGen (omegaAFam Ω X)) (hL : L ∈ Ω) (hP : IsSylow2In P L) (hPX : P ≤ X)
    (hnA : ¬ AEmpty (omegaAFam Ω X) ((tightCore (L ⊓ X)).subgroupOf X)) :
    oddCoreOf X ≤ conjStab (dstarComp Ω L) := by
  have hΩc : ConjInvariant Ω := hΩ.conjInvariant
  obtain ⟨Ja, zL, zJ, hv⟩ := not_aEmpty_iff.mp hnA
  have hLX : tightCore (L ⊓ X) ≤ X := (tightCore_le _).trans inf_le_right
  have hLaΦ : (tightCore (L ⊓ X)).subgroupOf X ∈ omegaAFam Ω X :=
    tightCore_inf_subgroupOf_mem_omegaAFam hL hP hPX
  obtain ⟨J, hJ, -, rfl, hJd⟩ := exists_mem_dstarComp_of_omegaAFam hΩ hL hP hPX
    (Relation.ReflTransGen.single ⟨hv.mem, Or.inl hv.star⟩ :
      Ja ∈ dstarComp (omegaAFam Ω X) ((tightCore (L ⊓ X)).subgroupOf X))
  have hJX : tightCore (J ⊓ X) ≤ X := (tightCore_le _).trans inf_le_right
  have hzL : IsUniqueInvolution L (zL : G) :=
    Q3T7.isUniqueInvolution_of_le_member3 hΩ hL ((tightCore_le _).trans inf_le_left)
      (isUniqueInvolution_of_subgroupOf hv.hzK hLX)
  have hzJ : IsUniqueInvolution J (zJ : G) :=
    Q3T7.isUniqueInvolution_of_le_member3 hΩ hJ ((tightCore_le _).trans inf_le_left)
      (isUniqueInvolution_of_subgroupOf hv.hzJ hJX)
  obtain ⟨t, htJ, ht⟩ := Thm3Quot.exists_conj_mul_involution hΦ hLaΦ hv
  have htJ' : (t : G) ∈ J :=
    ((tightCore_le _).trans inf_le_left) (Subgroup.mem_subgroupOf.mp htJ)
  have hLt : conjSub (t : G) L ∈ dstarComp Ω L :=
    (mem_conjStab_iff.mp (mem_conjStab_dstarComp hΩc hL hJd (conjSub_eq_self_of_mem htJ')) L).mpr
      Relation.ReflTransGen.refl
  have hzLt : IsUniqueInvolution (conjSub (t : G) L) ((zL : G) * (zJ : G)) := by
    rw [conjSub_subgroupOf] at ht
    have hle : conjSub (t : G) (tightCore (L ⊓ X)) ≤ X :=
      (conjSub_mono hLX).trans (conjSub_eq_self_of_mem t.2).le
    exact Q3T7.isUniqueInvolution_of_le_member3 hΩ (hΩc _ L hL)
      (conjSub_mono ((tightCore_le _).trans inf_le_left)) (isUniqueInvolution_of_subgroupOf ht hle)
  have hnorm : ∀ x : X, (x : G) ∈ Subgroup.normalizer (oddCoreOf X : Set G) := fun x =>
    mem_normalizer_iff_conjSub_eq.mpr
      (Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer (Subgroup.le_normalizer x.2))
  exact Thm3Quot.le_of_four hzL.sq hzJ.sq
    (congrArg Subtype.val (Thm3Quot.aViol_involution_comm hΦ hv)) hzL.ne_one hzJ.ne_one
    (fun h => Thm3Quot.aViol_involution_ne hΦ hLaΦ hv (Subtype.ext h)) (oddCoreOf_odd_natCard X)
    (hnorm zL) (hnorm zJ)
    (Thm3Quot.centralizer_le_conjStab_dstarComp_of_mem hΩ hL Relation.ReflTransGen.refl hzL)
    (Thm3Quot.centralizer_le_conjStab_dstarComp_of_mem hΩ hL hJd hzJ)
    (Thm3Quot.centralizer_le_conjStab_dstarComp_of_mem hΩ hL hLt hzLt)

theorem le_sigmaStarNorm_of_core (hΩ : HypOmegaGen Ω) {X : Subgroup G}
    (hΦ : TypeRHyp (omegaAFam Ω X)) (hQ : Thm3A.Thm3RGroupQuotG ↥X) {L P : Subgroup G}
    (hL : L ∈ Ω) (hP : IsSylow2In P L) (hPX : P ≤ X)
    (hnA : ¬ AEmpty (omegaAFam Ω X) ((tightCore (L ⊓ X)).subgroupOf X)) :
    X ≤ sigmaStarNorm Ω L := by
  have hΩc : ConjInvariant Ω := hΩ.conjInvariant
  have hLX : tightCore (L ⊓ X) ≤ X := (tightCore_le _).trans inf_le_right
  have hLaΦ : (tightCore (L ⊓ X)).subgroupOf X ∈ omegaAFam Ω X :=
    tightCore_inf_subgroupOf_mem_omegaAFam hL hP hPX
  have hOX := oddCoreOf_le_conjStab_dstarComp_of_core hΩ hΦ.hyp hL hP hPX hnA
  have hkey : ∀ c ∈ X, conjSub c L ∈ dstarComp Ω L := by
    intro c hc
    have hcL : conjSub c L ∈ Ω := hΩc c L hL
    have hPcX : conjSub c P ≤ X := by
      have := conjSub_mono (n := c) hPX
      rwa [conjSub_eq_self_of_mem hc] at this
    have hPc : IsSylow2In (conjSub c P) (conjSub c L) := hP.conj c
    have hcX : tightCore (conjSub c L ⊓ X) ≤ X := (tightCore_le _).trans inf_le_right
    have hL'Φ : (tightCore (conjSub c L ⊓ X)).subgroupOf X ∈ omegaAFam Ω X :=
      tightCore_inf_subgroupOf_mem_omegaAFam hcL hPc hPcX
    by_cases hA : (tightCore (conjSub c L ⊓ X)).subgroupOf X ∈
        aStar (omegaAFam Ω X) ((tightCore (L ⊓ X)).subgroupOf X)
    ·
      obtain ⟨M, hM, ⟨RM, hRM, hRMX⟩, hMe, hMd⟩ := exists_mem_dstarComp_of_omegaAFam hΩ hL
        hP hPX (aStar_subset_dstarComp_gen hΦ.hyp hLaΦ hA).2
      have hMX : tightCore (M ⊓ X) ≤ X := (tightCore_le _).trans inf_le_right
      have hcore : tightCore (conjSub c L ⊓ X) = tightCore (M ⊓ X) := by
        have h1 := Subgroup.subgroupOf_inj.mp hMe
        rwa [inf_eq_left.mpr hcX, inf_eq_left.mpr hMX] at h1
      have hMeq : M = conjSub c L := by
        refine eq_of_tightCore_inf_le hΩ hM hcL hRM hRMX ?_
        rw [← hcore]
        exact (tightCore_le _).trans inf_le_left
      rw [← hMeq]
      exact hMd
    ·
      have hPcS : IsSylow2In ((conjSub c P).subgroupOf X)
          ((tightCore (conjSub c L ⊓ X)).subgroupOf X) :=
        (T8.isSylow2In_of_le_of_le hPc (le_tightCore_of_isPGroup (le_inf hPc.1 hPcX) hPc.2.1)
          ((tightCore_le _).trans inf_le_left)).subgroupOf hcX
      obtain ⟨n, hn, hRn, -⟩ :=
        (Thm3A.thm3R_lift_stab hQ hΦ hLaΦ hnA hL'Φ hA Relation.ReflTransGen.refl).2 _ hPcS
      have hXn : conjSub (n : G) X = X := conjSub_eq_self_of_mem n.2
      rw [conjSub_subgroupOf, conjSub_tightCore, Asc77.conjSub_inf, hXn] at hRn
      have hLnΩ : conjSub (n : G) L ∈ Ω := hΩc _ L hL
      have hPnX : conjSub (n : G) P ≤ X := (conjSub_mono hPX).trans hXn.le
      have hLnX : tightCore (conjSub (n : G) L ⊓ X) ≤ X := (tightCore_le _).trans inf_le_right
      have hRN : conjSub c P ≤ Subgroup.normalizer (conjSub (n : G) L : Set G) := fun r hr =>
        mem_normalizer_of_mem_normalizer_tightCore hΩ hLnΩ (hP.conj (n : G)) hPnX
          ((mem_normalizer_subgroupOf_iff (y := ⟨r, hPcX hr⟩) hLnX).mpr
            (hRn (Subgroup.mem_subgroupOf.mpr hr)))
      have h1 : conjSub c L ∈ dstarComp Ω (conjSub (n : G) L) := by
        by_cases hcn : conjSub c L = conjSub (n : G) L
        · rw [hcn]
          exact Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.single ⟨hcL, Or.inl (omegaNbr_subset_omegaStarNbr_gen hΩ _
            ⟨hcL, hcn, conjSub c P, mem_RSet_of_isSylow2In hcL hPc, hPc.1, hRN⟩)⟩
      have h2 : conjSub (n : G) L ∈ dstarComp Ω L :=
        (mem_conjStab_iff.mp (hOX (Subgroup.mem_map_of_mem X.subtype hn)) L).mpr
          Relation.ReflTransGen.refl
      exact h2.trans h1
  intro c hc
  exact T7A.mem_sigmaStarNorm_of_conj hΩc hL (hkey c hc)

end Lift

section Cent

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {S : Subgroup T}

theorem FrameStd.card_centralizer_lt [CaseIAmbient T] (_hs : FrameStd K z J zJ) {a : T}
    (ha1 : a ≠ 1) : Nat.card ↥(Subgroup.centralizer ({a} : Set T)) < Nat.card T := by
  set X : Subgroup T := Subgroup.centralizer ({a} : Set T) with hX
  have hXtop : X ≠ ⊤ := by
    intro htop
    have hcen : a ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ X := by
        rw [htop]
        exact Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    exact CaseIAmbient.not_mem_center ha1 hcen
  exact lt_of_le_of_ne (Subgroup.card_le_card_group X)
    (fun h => hXtop ((Subgroup.card_eq_iff_eq_top X).mp h))

theorem FrameStd.cent_le_sigmaStarNorm_of_aViol [CaseIAmbient T] (hs : FrameStd K z J zJ)
    {a : T} (ha : IsPGroup 2 (Subgroup.zpowers a)) (ha1 : a ≠ 1) {K' J' : Subgroup T}
    {zK zJ' : T} (hK' : K' ∈ sigmaOf K) (hv : AViol (CoreAssembly.conjClass K) K' J' zK zJ')
    (hK'a : a ∈ trivialOnQuot K') (hJ'a : a ∈ trivialOnQuot J') :
    Subgroup.centralizer ({a} : Set T) ≤ sigmaStarNorm (CoreAssembly.conjClass K) K := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K) := hs.hyp
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hK'd : K' ∈ dstarComp (CoreAssembly.conjClass K) K := hK'
  have hK'Ω : K' ∈ CoreAssembly.conjClass K := (mem_dstarComp_symm hKΩ hK'd).1
  obtain ⟨S', hS', hS'X⟩ := TwinADescent.exists_sylow_centralizer_of_tq ha hK'a
  obtain ⟨zK₀, zL₀, hvX⟩ := aViol_omegaAFam hΩ ha hK'Ω hv hK'a hJ'a
  have h := le_sigmaStarNorm_of_core hΩ (typeRHyp_omegaAFam hs.typeRHyp _)
    (Thm3A.thm3RGroupQuotG_of_belowG hs.below (hs.card_centralizer_lt ha1)) hK'Ω hS' hS'X
    (not_aEmpty_iff.mpr ⟨_, zK₀, zL₀, hvX⟩)
  rwa [sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hKΩ hK'd)] at h

theorem FrameCfg.exists_aViol_trivialOnQuot (cfg : FrameCfg K z J zJ S) {n : T}
    (hn : n ∈ sigmaNorm K) {a : T} (ha : IsPGroup 2 (Subgroup.zpowers a))
    (haN : a ∈ Subgroup.normalizer (conjSub n (firstFactor K) : Set T))
    (hac : ∀ x ∈ conjSub n (firstFactor K), a * x * a⁻¹ * x⁻¹ ∈ oddCoreOf (sigmaGen K)) :
    ∃ K' ∈ sigmaOf K, ∃ (J' : Subgroup T) (zK zJ' : T),
      AViol (CoreAssembly.conjClass K) K' J' zK zJ' ∧ a ∈ trivialOnQuot K' ∧
        a ∈ trivialOnQuot J' := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K) := cfg.datum.hyp
  have hΩc : ConjInvariant (CoreAssembly.conjClass K) := hΩ.conjInvariant
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hBHs : conjSub n (firstFactor K) ≤ sigmaGen K := cfg.conjSub_firstFactor_le hn
  have hBN : conjSub n (firstFactor K) ≤
      Subgroup.normalizer (oddCoreOf (sigmaGen K) : Set T) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr
      (Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer (Subgroup.le_normalizer (hBHs hx)))
  have htq : ∀ M : Subgroup T, M ≤ conjSub n (firstFactor K) →
      a ∈ Subgroup.normalizer (M : Set T) → a ∈ trivialOnQuot M := by
    intro M hMB haM
    refine ⟨haM, fun x hx => ?_⟩
    have hle : oddCoreOf (sigmaGen K) ⊓ M ≤ oddCoreOf M :=
      Sec6Gen.le_oddCoreOf_of_normal inf_le_right
        (fun y hy => Balance.Bootstrap.mem_normalizer_inf (hBN (hMB hy))
          (Subgroup.le_normalizer hy))
        ((oddCoreOf_odd_natCard _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    rw [commutatorElement_def]
    exact hle ⟨hac x (hMB hx),
      M.mul_mem ((Subgroup.mem_normalizer_iff.mp haM x).mp hx) (M.inv_mem hx)⟩
  have hnorm : ∀ M ∈ CoreAssembly.conjClass K, ∀ P : Subgroup T, IsSylow2In P M →
      P ≤ Subgroup.centralizer ({a} : Set T) → a ∈ Subgroup.normalizer (M : Set T) := by
    intro M hM P hP hPX
    have hPa : conjSub a P = P := by
      refine T7A.conjSub_eq_self_of_mem_centralizer ?_
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (hPX hx)
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hM hP)
    have hle : P ≤ conjSub a M := by
      rw [← hPa]
      exact conjSub_mono hP.1
    exact mem_normalizer_iff_conjSub_eq.mpr
      (Sec6Gen.eq_of_le_of_le hΩ (hΩc a M hM) hM hP.2.1 (by omega) hle hP.1)
  have haB : a ∈ trivialOnQuot (conjSub n (firstFactor K)) := htq _ le_rfl haN
  have hv₁ := cfg.viol.conj hΩc n
  have hKHt : K ≤ firstFactor K :=
    (le_omegaGen (Relation.ReflTransGen.refl : K ∈ aStar (CoreAssembly.conjClass K) K)).trans
      le_sup_left
  have hJHt : J ≤ firstFactor K :=
    (le_omegaGen (mem_aStar_of_aViol cfg.viol)).trans le_sup_left
  have hK₁B : conjSub n K ≤ conjSub n (firstFactor K) := conjSub_mono hKHt
  have hJ₁B : conjSub n J ≤ conjSub n (firstFactor K) := conjSub_mono hJHt
  obtain ⟨-, -, V, hV, hVJ₁, hVN⟩ := hv₁.star
  have hV2 : IsPGroup 2 V := Sec6Gen.isPGroup_of_mem_USet hΩ hV
  obtain ⟨P₀, hP₀, hVP₀⟩ := IsSylow2In.exists_ge hV2 (le_sup_right : V ≤ conjSub n K ⊔ V)
  have hS₁ : IsSylow2In (P₀ ⊓ conjSub n K) (conjSub n K) :=
    isSylow2In_inf_of_le_normalizer hP₀ le_sup_left (sup_le Subgroup.le_normalizer hVN)
  have hP₀B : P₀ ≤ conjSub n (firstFactor K) :=
    hP₀.1.trans (sup_le hK₁B (hVJ₁.trans hJ₁B))
  obtain ⟨x₁, hx₁, hx₁c⟩ := AscAET.exists_conj_centralized ha haB haN hP₀.2.1 hP₀B
    (hP₀B.trans Subgroup.le_normalizer)
  have hBx₁ : conjSub x₁ (conjSub n (firstFactor K)) = conjSub n (firstFactor K) :=
    conjSub_eq_self_of_mem hx₁.1
  have hv' := hv₁.conj hΩc x₁
  have hK'Ω : conjSub x₁ (conjSub n K) ∈ CoreAssembly.conjClass K := hΩc x₁ _ (hΩc n K hKΩ)
  have hJ'Ω : conjSub x₁ (conjSub n J) ∈ CoreAssembly.conjClass K := hv'.mem
  have hK'B : conjSub x₁ (conjSub n K) ≤ conjSub n (firstFactor K) :=
    (conjSub_mono hK₁B).trans hBx₁.le
  have hJ'B : conjSub x₁ (conjSub n J) ≤ conjSub n (firstFactor K) :=
    (conjSub_mono hJ₁B).trans hBx₁.le
  have hS' : IsSylow2In (conjSub x₁ (P₀ ⊓ conjSub n K)) (conjSub x₁ (conjSub n K)) :=
    hS₁.conj x₁
  have hS'X : conjSub x₁ (P₀ ⊓ conjSub n K) ≤ Subgroup.centralizer ({a} : Set T) :=
    (conjSub_mono inf_le_left).trans hx₁c
  have hV'X : conjSub x₁ V ≤ Subgroup.centralizer ({a} : Set T) :=
    (conjSub_mono hVP₀).trans hx₁c
  have hV'J' : conjSub x₁ V ≤ conjSub x₁ (conjSub n J) := conjSub_mono hVJ₁
  have hV'U : conjSub x₁ V ∈ USet (CoreAssembly.conjClass K) :=
    S19B.conjSub_mem_USet hΩc hV x₁
  obtain ⟨R₀, hR₀rs, hV'R₀, -, hidx⟩ := id hV'U
  obtain ⟨J₀, hJ₀, hR₀J₀⟩ := exists_isSylow2In_of_mem_RSet hR₀rs
  have hJ₀J' : J₀ = conjSub x₁ (conjSub n J) :=
    Sec6Gen.eq_of_mem_USet hΩ hV'U hJ₀ hJ'Ω (hV'R₀.trans hR₀J₀.1) hV'J'
  rw [hJ₀J'] at hR₀J₀
  have haV' : a ∈ Subgroup.normalizer (conjSub x₁ V : Set T) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hV'X hx)
  obtain ⟨x₂, hx₂, hx₂c⟩ := AscAET.exists_conj_centralized ha haB haV' hR₀J₀.2.1
    (hR₀J₀.1.trans hJ'B) (AscAET.le_normalizer_of_relIndex_two hV'R₀ hidx)
  have hx₂V : conjSub x₂ (conjSub x₁ V) = conjSub x₁ V :=
    mem_normalizer_iff_conjSub_eq.mp hx₂.2
  have hV'R : conjSub x₁ V ≤ conjSub x₂ R₀ := hx₂V.symm.le.trans (conjSub_mono hV'R₀)
  have hJ'x : conjSub x₂ (conjSub x₁ (conjSub n J)) = conjSub x₁ (conjSub n J) :=
    Sec6Gen.eq_of_mem_USet hΩ hV'U (hΩc x₂ _ hJ'Ω) hJ'Ω (hV'R.trans (conjSub_mono hR₀J₀.1))
      hV'J'
  have hRJ' : IsSylow2In (conjSub x₂ R₀) (conjSub x₁ (conjSub n J)) := by
    have := hR₀J₀.conj x₂
    rwa [hJ'x] at this
  have hK'sig : conjSub x₁ (conjSub n K) ∈ sigmaOf K := by
    have hg : x₁ * n ∈ sigmaStarNorm (CoreAssembly.conjClass K) K :=
      (sigmaStarNorm _ K).mul_mem (sigmaGen_le_sigmaStarNorm hΩc (hBHs hx₁.1))
        (cfg.sigmaNorm_le_sigmaStarNorm hn)
    rw [← conjSub_mul]
    exact (mem_sigmaStarNorm_iff.mp hg K).mp Relation.ReflTransGen.refl
  exact ⟨_, hK'sig, _, _, _, hv', htq _ hK'B (hnorm _ hK'Ω _ hS' hS'X),
    htq _ hJ'B (hnorm _ hJ'Ω _ hRJ' hx₂c)⟩

theorem FrameCfg.cent_le_of_factor [CaseIAmbient T] (cfg : FrameCfg K z J zJ S) {n : T}
    (hn : n ∈ sigmaNorm K) {a : T} (ha : IsPGroup 2 (Subgroup.zpowers a)) (ha1 : a ≠ 1)
    (haN : a ∈ Subgroup.normalizer (conjSub n (firstFactor K) : Set T))
    (hac : ∀ x ∈ conjSub n (firstFactor K), a * x * a⁻¹ * x⁻¹ ∈ oddCoreOf (sigmaGen K)) :
    Subgroup.centralizer ({a} : Set T) ≤ sigmaNorm K := by
  obtain ⟨K', hK', J', zK, zJ', hv, hK'a, hJ'a⟩ := cfg.exists_aViol_trivialOnQuot hn ha haN hac
  exact (cfg.toFrameStd.cent_le_sigmaStarNorm_of_aViol ha ha1 hK' hv hK'a hJ'a).trans
    (sigmaStarNorm_le_sigmaNorm K)

end Cent

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
