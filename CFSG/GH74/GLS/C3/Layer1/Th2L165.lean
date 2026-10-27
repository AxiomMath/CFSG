module

public import CFSG.GH74.AS16.Standard
public import CFSG.LocalAnalysis.GH72.Sec4Basic
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_PartIIExists
public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreShape
public import CFSG.GH74.GLS.Stage1.Main.P49XA
public import CFSG.GH74.GLS.C3.Layer1.PU3Cover
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Lemma51B
public import CFSG.LocalAnalysis.ComponentClassification.Foote47L216DualEightLift
public import CFSG.LocalAnalysis.ComponentClassification.GS82P10Centre
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CoverCore
public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32G

public section
namespace CFSG.GH74.GLS.Th2.L165

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec4
open CFSG.GH74.GLS.Th2.P85
open CFSG.GH74.GLS.Th2.P812A7
open CFSG.GH74.GLS.TwoThin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pGroup_le_of_centralizer_le {p : ℕ} [Fact p.Prime] {R M : Subgroup G}
    (hR : IsPGroup p ↥R) (hne : R ⊓ M ≠ ⊥)
    (hcent : ∀ t ∈ R ⊓ M, orderOf t = p → centralizer ({t} : Set G) ≤ M) :
    R ≤ M := by
  have hRne : R ≠ ⊥ := by
    intro hbot
    apply hne
    rw [hbot, bot_inf_eq]
  have hR0 : IsPGroup p ↥(R ⊓ M) :=
    (hR.to_subgroup ((R ⊓ M).subgroupOf R)).of_equiv
      (Subgroup.subgroupOfEquivOfLe inf_le_left)
  obtain ⟨t, htR0, htord, -⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i116e_exists_central
      (p := p) hR0 le_rfl (Subgroup.le_normalizer) hne
  obtain ⟨z, hzR, hzord, hzcent⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i116e_exists_central
      (p := p) hR le_rfl (Subgroup.le_normalizer) hRne
  have htz : t * z = z * t := hzcent t htR0.1
  have hzCt : z ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact htz.symm
  have hzM : z ∈ M := hcent t htR0 htord hzCt
  have hzR0 : z ∈ R ⊓ M := ⟨hzR, hzM⟩
  refine le_trans ?_ (hcent z hzR0 hzord)
  intro r hr
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hzcent r hr

theorem mem_CMK_of_cover {M K K0 : Subgroup G} {x : G}
    (hxM : x ∈ M) (hxK : x ∈ normalizer (K : Set G))
    (hxO : x ∈ normalizer (pPrimeCoreOf 2 K : Set G))
    (hK0K : K0 ≤ K)
    (hcover : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o)
    (hact : ∀ k0 ∈ K0, ⁅k0, x⁆ ∈ pPrimeCoreOf 2 K)
    (hactO : ∀ o ∈ pPrimeCoreOf 2 K, ⁅o, x⁆ ∈ pPrimeCoreOf 2 K) :
    x ∈ CMK M K := by
  rw [CFSG.GH74.GLS.C3.Layer1.U1a.mem_CMK_iff]
  refine ⟨hxM, hxK, hxO, ?_⟩
  intro k hk
  obtain ⟨k0, hk0, o, ho, hko⟩ := hcover k hk
  rw [hko]
  have hKO : K ≤ normalizer (pPrimeCoreOf 2 K : Set G) :=
    fun y hy => CFSG.GH74.GLS.TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hy)
  have hk0K : k0 ∈ K := hK0K hk0
  have hconjO : k0 * ⁅o, x⁆ * k0⁻¹ ∈ pPrimeCoreOf 2 K :=
    (Subgroup.mem_normalizer_iff.mp (hKO hk0K) ⁅o, x⁆).mp (hactO o ho)
  have h1 : ⁅k0 * o, x⁆ = k0 * ⁅o, x⁆ * k0⁻¹ * ⁅k0, x⁆ := by
    simp only [commutatorElement_def]
    group
  rw [h1]
  exact Subgroup.mul_mem _ hconjO (hact k0 hk0)

theorem centralizerSylow_le_of_comparison
    {M N K I R : Subgroup G}
    (hRsyl : IsSylowOf 2 R (CMK N I))
    {y : G} (hyR : y ∈ R) (hyM : y ∈ M) (hy2 : orderOf y = 2)
    (hpreM : ∀ t ∈ CMK M K, orderOf t = 2 → centralizer ({t} : Set G) ≤ M)
    (hcomp : R ⊓ M ≤ CMK M K) :
    R ≤ M ∧ R ≤ CMK M K := by
  have hyne : y ≠ 1 := by
    intro hy1
    have : orderOf y = 1 := by rw [hy1, orderOf_one]
    omega
  have hne : R ⊓ M ≠ ⊥ := by
    intro hbot
    have hybot : y ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact ⟨hyR, hyM⟩
    exact hyne (by simpa using hybot)
  have hcent : ∀ t ∈ R ⊓ M, orderOf t = 2 → centralizer ({t} : Set G) ≤ M := by
    intro t ht ht2
    exact hpreM t (hcomp ht) ht2
  obtain ⟨Q, hQ⟩ := hRsyl
  have hR2 : IsPGroup 2 ↥R := by
    rw [← hQ]
    exact (Q.isPGroup').map (CMK N I).subtype
  have hRM : R ≤ M :=
    pGroup_le_of_centralizer_le (p := 2) hR2 hne hcent
  exact ⟨hRM, fun r hr => hcomp ⟨hr, hRM hr⟩⟩
theorem oddCore_le_of_fourCentralizers {M N E : Subgroup G}
    (hE4 : Nat.card E = 4) (hE2 : ∀ e ∈ E, e * e = 1)
    (hEM : E ≤ M)
    (hpreN : ∀ e ∈ E, e ≠ 1 → centralizer ({e} : Set G) ≤ N) :
    pPrimeCoreOf 2 M ≤ N := by
  have hNodd : Odd (Nat.card ↥(pPrimeCoreOf 2 M)) :=
    CFSG.GH74.GLS.TwoThin.card_pPrimeCoreOf_odd M
  have hMN : M ≤ normalizer (pPrimeCoreOf 2 M : Set G) :=
    fun m hm => CFSG.GH74.GLS.TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hm)
  have hWN : E ≤ normalizer (pPrimeCoreOf 2 M : Set G) := hEM.trans hMN
  have hK : ∀ e ∈ E, e ≠ 1 →
      centralizer ({e} : Set G) ⊓ pPrimeCoreOf 2 M ≤ N := by
    intro e he he1
    exact (inf_le_left : centralizer ({e} : Set G) ⊓ pPrimeCoreOf 2 M ≤
      centralizer ({e} : Set G)).trans (hpreN e he he1)
  exact CFSG.GH74.Uniqueness.le_of_inf_centralizer_le_of_four hNodd hE4 hE2 hWN hK

theorem K_le_of_oddCore_cover {N K K0 : Subgroup G}
    (hK0N : K0 ≤ N) (hOKN : pPrimeCoreOf 2 K ≤ N)
    (hcover : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o) :
    K ≤ N := by
  intro k hk
  obtain ⟨k0, hk0, o, ho, hko⟩ := hcover k hk
  rw [hko]
  exact N.mul_mem (hK0N hk0) (hOKN ho)

theorem oddCore_and_K_le_of_fourCentralizers {M N K K0 E : Subgroup G}
    (hE4 : Nat.card E = 4) (hE2 : ∀ e ∈ E, e * e = 1)
    (hEM : E ≤ M)
    (hpreN : ∀ e ∈ E, e ≠ 1 → centralizer ({e} : Set G) ≤ N)
    (hK0N : K0 ≤ N) (hOKN : pPrimeCoreOf 2 K ≤ N)
    (hcover : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o) :
    pPrimeCoreOf 2 M ≤ N ∧ K ≤ N :=
  ⟨oddCore_le_of_fourCentralizers hE4 hE2 hEM hpreN,
    K_le_of_oddCore_cover hK0N hOKN hcover⟩

theorem coreAction_of_mem_CMK {N I K K0 : Subgroup G} {x : G}
    (hxI : x ∈ CMK N I) (hK0I : K0 ≤ I)
    (hxK0 : x ∈ normalizer (K0 : Set G))
    (hOdd : pPrimeCoreOf 2 I ⊓ K0 ≤ pPrimeCoreOf 2 K) :
    ∀ k0 ∈ K0, ⁅k0, x⁆ ∈ pPrimeCoreOf 2 K := by
  have hxIcomm : ∀ k ∈ I, ⁅k, x⁆ ∈ pPrimeCoreOf 2 I :=
    (CFSG.GH74.GLS.C3.Layer1.U1a.mem_CMK_iff.mp hxI).2.2.2
  intro k0 hk0
  have hk0I : k0 ∈ I := hK0I hk0
  have hcommI : ⁅k0, x⁆ ∈ pPrimeCoreOf 2 I := hxIcomm k0 hk0I
  have hconjK0 : x * k0 * x⁻¹ ∈ K0 :=
    (Subgroup.mem_normalizer_iff.mp hxK0 k0).mp hk0
  have hxcommK0 : ⁅x, k0⁆ ∈ K0 := by
    rw [commutatorElement_def]
    exact K0.mul_mem hconjK0 (K0.inv_mem hk0)
  have hcommK0 : ⁅k0, x⁆ ∈ K0 := by
    have h1 : ⁅k0, x⁆ = ⁅x, k0⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact K0.inv_mem hxcommK0
  exact hOdd ⟨hcommI, hcommK0⟩
theorem oddCore_le_of_sectionSylow_rank {M N Q : Subgroup G}
    (hQM : Q ≤ M) (hQN : Q ≤ N) (hrank : 2 ≤ CFSG.Open.pRank 2 Q)
    (hpreN : ∀ e ∈ Q, e ≠ 1 → centralizer ({e} : Set G) ≤ N) :
    pPrimeCoreOf 2 M ≤ N := by
  obtain ⟨E, hEQ, hEab, hE4⟩ :=
    CFSG.OddStandard.Solomon75.CoreAux.exists_fourSub_of_two_le_pRank hrank
  have hE2 : ∀ e ∈ E, e * e = 1 := by
    intro e he
    have h : e ^ 2 = 1 := hEab.2 e he
    rw [pow_two] at h
    exact h
  exact oddCore_le_of_fourCentralizers (E := E) hE4 hE2 (hEQ.trans hQM)
    (fun e he he1 => hpreN e (hEQ he) he1)

theorem oddCore_and_K_le_of_sectionSylow_rank {M N K K0 Q : Subgroup G}
    (hQM : Q ≤ M) (hQN : Q ≤ N) (hrank : 2 ≤ CFSG.Open.pRank 2 Q)
    (hpreN : ∀ e ∈ Q, e ≠ 1 → centralizer ({e} : Set G) ≤ N)
    (hK0N : K0 ≤ N) (hOKN : pPrimeCoreOf 2 K ≤ N)
    (hcover : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o) :
    pPrimeCoreOf 2 M ≤ N ∧ K ≤ N :=
  ⟨oddCore_le_of_sectionSylow_rank hQM hQN hrank hpreN,
    K_le_of_oddCore_cover hK0N hOKN hcover⟩
theorem K_le_of_oddCore_of_isPCompIn {M N K K0 : Subgroup G}
    (hK : IsPCompIn 2 M K) (hOMN : pPrimeCoreOf 2 M ≤ N) (hK0N : K0 ≤ N)
    (hcover : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o) :
    K ≤ N :=
  K_le_of_oddCore_cover hK0N ((oddCore_K_le_of_isPCompIn hK).trans hOMN) hcover

theorem oddCore_and_K_le_of_sectionSylow_rank_of_isPCompIn {M N K K0 Q : Subgroup G}
    (hK : IsPCompIn 2 M K)
    (hQM : Q ≤ M) (hQN : Q ≤ N) (hrank : 2 ≤ CFSG.Open.pRank 2 Q)
    (hpreN : ∀ e ∈ Q, e ≠ 1 → centralizer ({e} : Set G) ≤ N)
    (hK0N : K0 ≤ N)
    (hcover : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o) :
    pPrimeCoreOf 2 M ≤ N ∧ K ≤ N :=
  ⟨oddCore_le_of_sectionSylow_rank hQM hQN hrank hpreN,
    K_le_of_oddCore_of_isPCompIn hK
      (oddCore_le_of_sectionSylow_rank hQM hQN hrank hpreN) hK0N hcover⟩

theorem centralizerSylow_le_of_isPCompIn_cover
    {M N K I R K0 : Subgroup G}
    (hK : IsPCompIn 2 M K)
    (hRsyl : IsSylowOf 2 R (CMK N I))
    {y : G} (hyR : y ∈ R) (hyM : y ∈ M) (hy2 : orderOf y = 2)
    (hpreM : ∀ t ∈ CMK M K, orderOf t = 2 → centralizer ({t} : Set G) ≤ M)
    (hK0K : K0 ≤ K) (hK0I : K0 ≤ I)
    (hcover : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o) :
    R ≤ M ∧ R ≤ CMK M K := by
  have hRle : R ≤ CMK N I := by
    obtain ⟨Q, hQ⟩ := hRsyl
    rw [← hQ]
    exact Subgroup.map_subtype_le _
  have hcomp : R ⊓ M ≤ CMK M K := by
    intro r hr
    have hCMKr : r ∈ CMK N I := hRle hr.1
    have hCMKdata := CFSG.GH74.GLS.C3.Layer1.U1a.mem_CMK_iff.mp hCMKr
    have hrI : r ∈ centralizerSection I (pPrimeCoreOf 2 I) :=
      ⟨hCMKdata.2.1, hCMKdata.2.2.1, hCMKdata.2.2.2⟩
    exact mem_CMK_of_isPCompIn_cover hK hK0K hK0I hcover hr.2 hrI
  exact centralizerSylow_le_of_comparison hRsyl hyR hyM hy2 hpreM hcomp
theorem oddCore_both_le_of_fourCentralizers {M N E F : Subgroup G}
    (hE4 : Nat.card E = 4) (hE2 : ∀ e ∈ E, e * e = 1)
    (hEM : E ≤ M)
    (hpreN : ∀ e ∈ E, e ≠ 1 → centralizer ({e} : Set G) ≤ N)
    (hF4 : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hFN : F ≤ N)
    (hpreM : ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set G) ≤ M) :
    pPrimeCoreOf 2 M ≤ N ∧ pPrimeCoreOf 2 N ≤ M :=
  ⟨oddCore_le_of_fourCentralizers hE4 hE2 hEM hpreN,
    oddCore_le_of_fourCentralizers hF4 hF2 hFN hpreM⟩

theorem K_and_I_le_of_oddCores {M N K I K0 : Subgroup G}
    (hK : IsPCompIn 2 M K) (hI : IsPCompIn 2 N I)
    (hK0M : K0 ≤ M) (hK0N : K0 ≤ N)
    (hOMN : pPrimeCoreOf 2 M ≤ N) (hONM : pPrimeCoreOf 2 N ≤ M)
    (hcoverK : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o)
    (hcoverI : ∀ i ∈ I, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 I, i = k0 * o) :
    K ≤ N ∧ I ≤ M :=
  ⟨K_le_of_oddCore_of_isPCompIn hK hOMN hK0N hcoverK,
    K_le_of_oddCore_of_isPCompIn hI hONM hK0M hcoverI⟩

theorem isSubnormalIn_inf_of_isSubnormalIn {M0 K I : Subgroup G}
    (hK : IsSubnormalIn K M0) (hI : IsSubnormalIn I M0) :
    IsSubnormalIn (K ⊓ I) M0 := by
  have hKrel : CFSG.Open.IsSubnormal K M0 :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hK.1).2 hK.2
  have hIrel : CFSG.Open.IsSubnormal I M0 :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hI.1).2 hI.2
  have hKI_I : CFSG.Open.IsSubnormal (K ⊓ I) I := by
    have h := hKrel.inf I
    rwa [inf_eq_right.mpr hI.1] at h
  have hKI_M0 : CFSG.Open.IsSubnormal (K ⊓ I) M0 :=
    hKI_I.trans hIrel
  refine ⟨inf_le_left.trans hK.1, ?_⟩
  exact (CFSG.Open.IsSubnormal.iff_subgroupOf (inf_le_left.trans hK.1)).1 hKI_M0

theorem isSubnormalIn_inf_of_isPCompIn {M K I : Subgroup G}
    (hK : IsPCompIn 2 M K) (hI : IsPCompIn 2 M I) :
    IsSubnormalIn (K ⊓ I) M :=
  isSubnormalIn_inf_of_isSubnormalIn
    (CFSG.GH74.GLS.PU3.isSubnormalIn_of_comp hK)
    (CFSG.GH74.GLS.PU3.isSubnormalIn_of_comp hI)

theorem eq_of_isPCompIn_common_cover {M N K I K0 : Subgroup G}
    (hK : IsPCompIn 2 (M ⊓ N) K) (hI : IsPCompIn 2 (M ⊓ N) I)
    (hK0K : K0 ≤ K) (hK0I : K0 ≤ I)
    (hcoverK : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o)
    (hcoverI : ∀ i ∈ I, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 I, i = k0 * o) :
    K = I := by
  have hsub : IsSubnormalIn (K ⊓ I) (M ⊓ N) :=
    isSubnormalIn_inf_of_isPCompIn hK hI
  have himgK : imgM (M ⊓ N) K = imgM (M ⊓ N) K0 :=
    imgM_eq_of_cover hK hK0K hcoverK
  have himgI : imgM (M ⊓ N) I = imgM (M ⊓ N) K0 :=
    imgM_eq_of_cover hI hK0I hcoverI
  have himgKI : imgM (M ⊓ N) (K ⊓ I) = imgM (M ⊓ N) K := by
    apply le_antisymm (imgM_mono inf_le_left)
    rw [himgK]
    exact imgM_mono (le_inf hK0K hK0I)
  have hKcapI : K ⊓ I = K :=
    CFSG.GH74.GLS.PU3.eq_of_imgM_eq hK inf_le_left hsub himgKI
  have hIcapK : K ⊓ I = I := by
    refine CFSG.GH74.GLS.PU3.eq_of_imgM_eq hI inf_le_right hsub ?_
    calc imgM (M ⊓ N) (K ⊓ I) = imgM (M ⊓ N) K := himgKI
      _ = imgM (M ⊓ N) K0 := himgK
      _ = imgM (M ⊓ N) I := himgI.symm
  calc K = K ⊓ I := hKcapI.symm
    _ = I := hIcapK
theorem K_eq_I_of_fourCentralizers_and_oddCores {M N K I K0 E F : Subgroup G}
    (hE4 : Nat.card E = 4) (hE2 : ∀ e ∈ E, e * e = 1)
    (hEM : E ≤ M)
    (hpreN : ∀ e ∈ E, e ≠ 1 → centralizer ({e} : Set G) ≤ N)
    (hF4 : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hFN : F ≤ N)
    (hpreM : ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set G) ≤ M)
    (hK : IsPCompIn 2 M K) (hI : IsPCompIn 2 N I)
    (hK0K : K0 ≤ K) (hK0I : K0 ≤ I)
    (hcoverK : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o)
    (hcoverI : ∀ i ∈ I, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 I, i = k0 * o) :
    K = I := by
  have hK0M : K0 ≤ M := hK0K.trans hK.1
  have hK0N : K0 ≤ N := hK0I.trans hI.1
  obtain ⟨hOMN, hONM⟩ :=
    oddCore_both_le_of_fourCentralizers hE4 hE2 hEM hpreN
      hF4 hF2 hFN hpreM
  obtain ⟨hKN, hIM⟩ :=
    K_and_I_le_of_oddCores hK hI hK0M hK0N hOMN hONM hcoverK hcoverI
  have hK0comp : IsPCompIn 2 (M ⊓ N) K :=
    CFSG.GH74.GLS.C3.Layer1.Bk.isPCompIn_of_le hK (fun x hx => ⟨hK.1 hx, hKN hx⟩) inf_le_left
  have hI0comp : IsPCompIn 2 (M ⊓ N) I :=
    CFSG.GH74.GLS.C3.Layer1.Bk.isPCompIn_of_le hI (fun x hx => ⟨hIM hx, hI.1 hx⟩) inf_le_right
  exact eq_of_isPCompIn_common_cover hK0comp hI0comp hK0K hK0I hcoverK hcoverI
theorem le_CMK_of_isPCompIn_ne {N I L : Subgroup G}
    (hI : IsPCompIn 2 N I) (hL : IsPCompIn 2 N L) (hne : I ≠ L) :
    L ≤ CMK N I := by
  have hP10 := CFSG.ComponentClassification.GS82PumpInputs.P10.normalizer_and_commutator_of_isPComponent
    (X := N) (L := I) (L' := L) hI.1 hL.1 hI.2 hL.2 hne
  intro l hl
  rw [CFSG.GH74.GLS.C3.Layer1.U1a.mem_CMK_iff]
  refine ⟨hL.1 hl, hP10.1 hl, ?_, ?_⟩
  · exact CFSG.GH74.GLS.TwoThin.mem_normalizer_pPrimeCoreOf (hP10.1 hl)
  · intro i hi
    simpa [CFSG.ComponentClassification.GS82PumpInputs.P10.oL, pPrimeCoreOf] using
      hP10.2 (Subgroup.commutator_mem_commutator hi hl)

theorem isSylowOf_inf_of_isPCompIn_ne {N I L R : Subgroup G}
    (hI : IsPCompIn 2 N I) (hL : IsPCompIn 2 N L) (hne : I ≠ L)
    (hRsyl : IsSylowOf 2 R (CMK N I)) :
    IsSylowOf 2 (R ⊓ L) L := by
  let H : Subgroup G := CMK N I
  have hLleH : L ≤ H := le_CMK_of_isPCompIn_ne hI hL hne
  have hHleN : H ≤ N := by
    dsimp [H, CMK]
    exact inf_le_left
  have hLsubN : (L.subgroupOf N).IsSubnormal := by
    obtain ⟨K', _hcomp', hsub', _hmap', _hmin'⟩ := hL.2
    exact hsub'
  have hLsubH : (L.subgroupOf H).IsSubnormal :=
    CFSG.GH74.GLS.PU3.isSubnormal_restrict (S := L) (H := N) (K := H) hLsubN hHleN
  obtain ⟨Q, hQmap⟩ := hRsyl
  have hQtop : IsSylowOf 2 (Q : Subgroup H) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, Q.isPGroup', by rw [Subgroup.relIndex_top_right]; exact Q.not_dvd_index⟩
  have hInter := CFSG.GH74.GLS.Stage1.Thm3.Sec6.isSylowOf_inf_subnormal49 hQtop hLsubH
  have hQmapR : (Q : Subgroup H).map H.subtype = R := by
    simpa [H] using hQmap
  have hmap : ((Q : Subgroup H) ⊓ L.subgroupOf H).map H.subtype = R ⊓ L := by
    rw [Subgroup.map_inf (Q : Subgroup H) (L.subgroupOf H) H.subtype H.subtype_injective,
      hQmapR, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLleH]
  have hmapL : (L.subgroupOf H).map H.subtype = L := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLleH]
  have hInterMap : IsSylowOf 2
      (((Q : Subgroup H) ⊓ L.subgroupOf H).map H.subtype)
      ((L.subgroupOf H).map H.subtype) :=
    (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H).2 hInter
  simpa [hmap, hmapL] using hInterMap

theorem ne_bot_of_isSylowOf_of_even {L S : Subgroup G}
    (hSyl : IsSylowOf 2 S L) (hLeven : Even (Nat.card ↥L)) : S ≠ ⊥ := by
  intro hbot
  obtain ⟨Q, hQmap⟩ := hSyl
  have hQne : (Q : Subgroup L) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card Q (even_iff_two_dvd.mp hLeven)
  have hQcard : Nat.card ↥(Q : Subgroup L) = Nat.card ↥S := by
    rw [← hQmap, Subgroup.card_map_of_injective L.subtype_injective]
  have hScard : Nat.card ↥S = 1 := by rw [hbot]; exact Subgroup.card_bot
  exact hQne ((Subgroup.card_eq_one).1 (by rw [hQcard, hScard]))

theorem exists_sylow_cmk_le_M_of_ne {M N K I L R : Subgroup G}
    (hI : IsPCompIn 2 N I) (hL : IsPCompIn 2 N L) (hILne : I ≠ L)
    (hRsyl : IsSylowOf 2 R (CMK N I))
    (hRleCMK : R ≤ CMK M K)
    (hpreM : ∀ t ∈ CMK M K, orderOf t = 2 → centralizer ({t} : Set G) ≤ M) :
    ∃ V : Subgroup G, IsSylowOf 2 V (CMK N L) ∧ V ≤ M := by
  let S : Subgroup G := R ⊓ L
  let H : Subgroup G := CMK N L
  have hSyl : IsSylowOf 2 S L := isSylowOf_inf_of_isPCompIn_ne hI hL hILne hRsyl
  have hLevenSub : Even (Nat.card ↥(L.subgroupOf N)) :=
    CFSG.ComponentClassification.CatFactsSp4.even_card_of_isPComponent hL.2
  have hLeven : Even (Nat.card ↥L) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL.1).toEquiv]
    exact hLevenSub
  have hSne : S ≠ ⊥ := ne_bot_of_isSylowOf_of_even hSyl hLeven
  have hSleCMK : S ≤ CMK M K := fun x hx => hRleCMK hx.1
  obtain ⟨s, hsS, hs2, -⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i116e_exists_central
      (p := 2) hSyl.isPGroup le_rfl (Subgroup.le_normalizer) hSne
  have hHleCS : H ≤ centralizerSection L (pPrimeCoreOf 2 L) := by
    dsimp [H, CMK]
    exact inf_le_right
  have hLnormH : L ≤ normalizer (H : Set G) := by
    intro l hl
    have hlN : l ∈ N := hL.1 hl
    have hlNnorm : l ∈ normalizer (N : Set G) := Subgroup.le_normalizer hlN
    have hlLnorm : l ∈ normalizer (L : Set G) := Subgroup.le_normalizer hl
    have hlOnorm : l ∈ normalizer (pPrimeCoreOf 2 L : Set G) :=
      CFSG.GH74.GLS.TwoThin.mem_normalizer_pPrimeCoreOf hlLnorm
    have hlCS : l ∈ normalizer (centralizerSection L (pPrimeCoreOf 2 L) : Set G) :=
      CFSG.OddStandard.Solomon75.Sec6L51B.mem_normalizer_centralizerSection hlLnorm hlOnorm
    have : l ∈ normalizer
        ((N ⊓ centralizerSection L (pPrimeCoreOf 2 L) : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hlNnorm, hlCS⟩
    simpa [H, CMK] using this
  have hSH : S ≤ normalizer (H : Set G) := hSyl.le.trans hLnormH
  have hcommOH : ∀ w ∈ S, ∀ h ∈ H, w * h * w⁻¹ * h⁻¹ ∈ pPrimeCoreOf 2 L := by
    intro w hw h hh
    have hwL : w ∈ L := hSyl.le hw
    have hc := hHleCS hh
    have h1 : ⁅w, h⁆ ∈ pPrimeCoreOf 2 L := hc.2.2 w hwL
    have h2 : w * h * w⁻¹ * h⁻¹ = ⁅w, h⁆ := rfl
    rw [h2]
    exact h1
  obtain ⟨V, hVsyl, hVcent⟩ :=
    CFSG.ComponentClassification.Foote47L216.exists_isSylowOf_le_centralizer_l216
      (O := pPrimeCoreOf 2 L) (H := H) (W := S)
      (CFSG.GH74.GLS.TwoThin.card_pPrimeCoreOf_odd L) hSH hSyl.isPGroup hcommOH
  refine ⟨V, hVsyl, ?_⟩
  have hsCMK : s ∈ CMK M K := hSleCMK hsS
  have hCsM : centralizer ({s} : Set G) ≤ M := hpreM s hsCMK hs2
  exact hVcent.trans ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hsS)).trans hCsM)
theorem exists_fourSub_of_isSylow_rank {H V : Subgroup G}
    (hVsyl : IsSylowOf 2 V H) (hrank : 2 ≤ CFSG.Open.pRank 2 H) :
    ∃ E : Subgroup G, E ≤ V ∧ Nat.card E = 4 ∧ ∀ e ∈ E, e * e = 1 := by
  have hVrank : 2 ≤ CFSG.Open.pRank 2 V := by
    rwa [CFSG.GH72.pRank_eq_of_isSylowOf_two hVsyl]
  obtain ⟨E, hEV, hEab, hE4⟩ :=
    CFSG.OddStandard.Solomon75.CoreAux.exists_fourSub_of_two_le_pRank hVrank
  refine ⟨E, hEV, hE4, ?_⟩
  intro e he
  have h : e ^ 2 = 1 := hEab.2 e he
  rw [pow_two] at h
  exact h

theorem oddCore_M_le_N_of_rank_two {M N K I L R : Subgroup G}
    (hI : IsPCompIn 2 N I) (hL : IsPCompIn 2 N L) (hILne : I ≠ L)
    (hRsyl : IsSylowOf 2 R (CMK N I))
    (hRleCMK : R ≤ CMK M K)
    (hpreM : ∀ t ∈ CMK M K, orderOf t = 2 → centralizer ({t} : Set G) ≤ M)
    (hpreN : ∀ t ∈ CMK N L, orderOf t = 2 → centralizer ({t} : Set G) ≤ N)
    (hrank : 2 ≤ CFSG.Open.pRank 2 (CMK N L)) :
    pPrimeCoreOf 2 M ≤ N := by
  obtain ⟨V, hVsyl, hVM⟩ :=
    exists_sylow_cmk_le_M_of_ne hI hL hILne hRsyl hRleCMK hpreM
  obtain ⟨E, hEV, hE4, hE2⟩ := exists_fourSub_of_isSylow_rank hVsyl hrank
  have hHleN : CMK N L ≤ N := by
    dsimp [CMK]
    exact inf_le_left
  have hEM : E ≤ M := hEV.trans hVM
  have hpreEN : ∀ e ∈ E, e ≠ 1 → centralizer ({e} : Set G) ≤ N := by
    intro e he he1
    have heH : e ∈ CMK N L := hEV.trans hVsyl.le he
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have heord : orderOf e = 2 := by
      exact orderOf_eq_prime (by rw [pow_two]; exact hE2 e he) he1
    exact hpreN e heH heord
  exact oddCore_le_of_fourCentralizers hE4 hE2 hEM hpreEN

theorem K_eq_I_of_rank_two {M N K I L R K0 : Subgroup G}
    (hK : IsPCompIn 2 M K) (hI : IsPCompIn 2 N I) (hL : IsPCompIn 2 N L)
    (hILne : I ≠ L)
    (hRsyl : IsSylowOf 2 R (CMK N I))
    (hRleCMK : R ≤ CMK M K)
    (hpreM : ∀ t ∈ CMK M K, orderOf t = 2 → centralizer ({t} : Set G) ≤ M)
    (hpreN : ∀ t ∈ CMK N L, orderOf t = 2 → centralizer ({t} : Set G) ≤ N)
    (hrankI : 2 ≤ CFSG.Open.pRank 2 (CMK N I))
    (hrankL : 2 ≤ CFSG.Open.pRank 2 (CMK N L))
    (hK0K : K0 ≤ K) (hK0I : K0 ≤ I)
    (hcoverK : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o)
    (hcoverI : ∀ i ∈ I, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 I, i = k0 * o) :
    K = I := by
  obtain ⟨V, hVsyl, hVM⟩ :=
    exists_sylow_cmk_le_M_of_ne hI hL hILne hRsyl hRleCMK hpreM
  obtain ⟨E, hEV, hE4, hE2⟩ := exists_fourSub_of_isSylow_rank hVsyl hrankL
  obtain ⟨F, hFR, hF4, hF2⟩ := exists_fourSub_of_isSylow_rank hRsyl hrankI
  have hEM : E ≤ M := hEV.trans hVM
  have hFN : F ≤ N := hFR.trans (hRsyl.le.trans (by dsimp [CMK]; exact inf_le_left))
  have hpreEN : ∀ e ∈ E, e ≠ 1 → centralizer ({e} : Set G) ≤ N := by
    intro e he he1
    have heH : e ∈ CMK N L := hEV.trans hVsyl.le he
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have heord : orderOf e = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hE2 e he) he1
    exact hpreN e heH heord
  have hpreFM : ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set G) ≤ M := by
    intro f hf hf1
    have hfK : f ∈ CMK M K := hFR.trans hRleCMK hf
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hford : orderOf f = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hF2 f hf) hf1
    exact hpreM f hfK hford
  exact K_eq_I_of_fourCentralizers_and_oddCores hE4 hE2 hEM hpreEN hF4 hF2 hFN hpreFM
    hK hI hK0K hK0I hcoverK hcoverI
theorem isSylowOf_inf_cmk_of_normal {M K S1 : Subgroup G}
    (hKnormal : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hS1 : IsSylowOf 2 S1 M) :
    IsSylowOf 2 (S1 ⊓ CMK M K) (CMK M K) := by
  have hCMKleM : CMK M K ≤ M := by
    dsimp [CMK]
    exact inf_le_left
  have hMnorm : M ≤ normalizer (CMK M K : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · exact CFSG.GH74.GLS.Th2.cmk_normal hKnormal m hm c
    · intro hc
      have h := CFSG.GH74.GLS.Th2.cmk_normal hKnormal m⁻¹ (M.inv_mem hm)
        (m * c * m⁻¹) hc
      simpa [mul_assoc] using h
  exact hS1.inf_of_le_normalizer hCMKleM hMnorm

theorem exists_fourSub_of_normal_component {M N K I L R : Subgroup G}
    (hK : IsPCompIn 2 M K) (hI : IsPCompIn 2 N I) (hL : IsPCompIn 2 N L)
    (hILne : I ≠ L) (hLnormal : (L.subgroupOf N).Normal)
    (hKnormal : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hRsyl : IsSylowOf 2 R (CMK N I))
    (hRleCMK : R ≤ CMK M K)
    (hpreM : ∀ t ∈ CMK M K, orderOf t = 2 → centralizer ({t} : Set G) ≤ M)
    (hcardMN : Nat.card M = Nat.card N)
    (hrankCMKM : 2 ≤ CFSG.Open.pRank 2 (CMK M K)) :
    ∃ S1 F : Subgroup G, IsSylowOf 2 S1 N ∧ S1 ≤ M ∧
      IsSylowOf 2 (S1 ⊓ CMK M K) (CMK M K) ∧
      F ≤ S1 ⊓ CMK M K ∧ Nat.card F = 4 ∧ ∀ f ∈ F, f * f = 1 := by
  let S : Subgroup G := R ⊓ L
  have hS : IsSylowOf 2 S L := isSylowOf_inf_of_isPCompIn_ne hI hL hILne hRsyl
  have hLevenSub : Even (Nat.card ↥(L.subgroupOf N)) :=
    CFSG.ComponentClassification.CatFactsSp4.even_card_of_isPComponent hL.2
  have hLeven : Even (Nat.card ↥L) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL.1).toEquiv]
    exact hLevenSub
  have hSne : S ≠ ⊥ := ne_bot_of_isSylowOf_of_even hS hLeven
  have hSleCMK : S ≤ CMK M K := fun x hx => hRleCMK hx.1
  obtain ⟨Q, hSQ⟩ := (hS.isPGroup.comap_subtype (K := N)).exists_le_sylow
  let S1 : Subgroup G := Q.map N.subtype
  have hS1 : IsSylowOf 2 S1 N := ⟨Q, rfl⟩
  have hSS1 : S ≤ S1 := by
    intro x hx
    exact ⟨⟨x, hL.1 (hS.le hx)⟩, hSQ hx, rfl⟩
  have hNL : N ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1).1 hLnormal
  have hS1L : IsSylowOf 2 (S1 ⊓ L) L :=
    hS1.inf_of_le_normalizer hL.1 hNL
  have hSeq : S1 ⊓ L = S :=
    hS.eq_of_le (le_inf hSS1 hS.le) inf_le_right hS1.isPGroup.to_inf_left
  have hS1normS : S1 ≤ normalizer (S : Set G) := by
    rw [← hSeq]
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, hS1.le.trans hNL hg⟩
  let Ssub : Subgroup ↥S1 := S.subgroupOf S1
  have hSsubNormal : Ssub.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSS1).2 hS1normS
  have hSsubNe : Ssub ≠ ⊥ := by
    intro hbot
    have hdis : Disjoint S S1 := (Subgroup.subgroupOf_eq_bot).1 hbot
    exact hSne (by simpa [disjoint_iff, inf_eq_left.mpr hSS1] using hdis)
  haveI : Group.IsNilpotent ↥S1 := hS1.isPGroup.isNilpotent
  have hcenterNe : Ssub ⊓ center ↥S1 ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hSsubNe
  obtain ⟨t, ht, htord⟩ :=
    CFSG.GroupTheory.SuzukiTwoGroup.exists_mem_orderOf_eq_two hS1.isPGroup hcenterNe
  let z : G := (t : ↥S1)
  have hzS : z ∈ S := ht.1
  have hzCenter : t ∈ center ↥S1 := ht.2
  have hzord : orderOf z = 2 := by
    simpa [z] using htord
  have hzCMK : z ∈ CMK M K := hSleCMK hzS
  have hzCent : S1 ≤ centralizer ({z} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := (Subgroup.mem_center_iff.1 hzCenter) (⟨g, hg⟩ : ↥S1)
    have h' := congrArg (fun u : ↥S1 => (u : G)) h
    simpa [z] using h'
  have hS1M : S1 ≤ M := hzCent.trans (hpreM z hzCMK hzord)
  have hS1sylM : IsSylowOf 2 S1 M := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hS1M ?_
    rw [hS1.card_eq, hcardMN]
  have hS1cmkSyl : IsSylowOf 2 (S1 ⊓ CMK M K) (CMK M K) :=
    isSylowOf_inf_cmk_of_normal hKnormal hS1sylM
  have hrank : 2 ≤ CFSG.Open.pRank 2 (S1 ⊓ CMK M K) := by
    rwa [CFSG.GH72.pRank_eq_of_isSylowOf_two hS1cmkSyl]
  obtain ⟨F, hFle, hF4, hF2⟩ :=
    exists_fourSub_of_isSylow_rank hS1cmkSyl (by simpa using hrankCMKM)
  exact ⟨S1, F, hS1, hS1M, hS1cmkSyl, hFle, hF4, hF2⟩
theorem K_eq_I_of_normal_component {M N K I L R K0 : Subgroup G}
    (hK : IsPCompIn 2 M K) (hI : IsPCompIn 2 N I) (hL : IsPCompIn 2 N L)
    (hILne : I ≠ L) (hLnormal : (L.subgroupOf N).Normal)
    (hKnormal : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hRsyl : IsSylowOf 2 R (CMK N I))
    (hRleCMK : R ≤ CMK M K)
    (hpreM : ∀ t ∈ CMK M K, orderOf t = 2 → centralizer ({t} : Set G) ≤ M)
    (hpreN : ∀ t ∈ CMK N L, orderOf t = 2 → centralizer ({t} : Set G) ≤ N)
    (hcardMN : Nat.card M = Nat.card N)
    (hrankCMKM : 2 ≤ CFSG.Open.pRank 2 (CMK M K))
    (hrankL : 2 ≤ CFSG.Open.pRank 2 (CMK N L))
    (hK0K : K0 ≤ K) (hK0I : K0 ≤ I)
    (hcoverK : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o)
    (hcoverI : ∀ i ∈ I, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 I, i = k0 * o) :
    K = I := by
  obtain ⟨V, hVsyl, hVM⟩ :=
    exists_sylow_cmk_le_M_of_ne hI hL hILne hRsyl hRleCMK hpreM
  obtain ⟨E, hEV, hE4, hE2⟩ := exists_fourSub_of_isSylow_rank hVsyl hrankL
  have hEM : E ≤ M := hEV.trans hVM
  have hpreEN : ∀ e ∈ E, e ≠ 1 → centralizer ({e} : Set G) ≤ N := by
    intro e he he1
    have heH : e ∈ CMK N L := hEV.trans hVsyl.le he
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have heord : orderOf e = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hE2 e he) he1
    exact hpreN e heH heord
  obtain ⟨S1, F, hS1, hS1M, -, hFle, hF4, hF2⟩ :=
    exists_fourSub_of_normal_component hK hI hL hILne hLnormal hKnormal hRsyl hRleCMK
      hpreM hcardMN hrankCMKM
  have hFN : F ≤ N := (hFle.trans inf_le_left).trans hS1.le
  have hpreFM : ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set G) ≤ M := by
    intro f hf hf1
    have hfCMK : f ∈ CMK M K := hFle.trans inf_le_right hf
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hford : orderOf f = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hF2 f hf) hf1
    exact hpreM f hfCMK hford
  exact K_eq_I_of_fourCentralizers_and_oddCores hE4 hE2 hEM hpreEN
    hF4 hF2 hFN hpreFM hK hI hK0K hK0I hcoverK hcoverI
theorem false_of_two_distinct_isPCompIn_of_pRank_le_one {H I L : Subgroup G}
    (hI : IsPCompIn 2 H I) (hL : IsPCompIn 2 H L) (hne : I ≠ L)
    (hrank : CFSG.Open.pRank 2 H ≤ 1) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Y := CFSG.GH74.GLS.Th2.P85.Mb H
  let Ib : Subgroup Y := CFSG.GH74.GLS.Th2.P85.imgM H I
  let Lb : Subgroup Y := CFSG.GH74.GLS.Th2.P85.imgM H L
  have hIcomp : CFSG.IsComponent Ib := by
    dsimp [Ib]
    simpa [CFSG.GH74.GLS.Th2.P85.imgM] using
      CFSG.GH74.GLS.TwoThin.isComponent_map_barMk
        (Y := ↥H) (K := I.subgroupOf H)
        (CFSG.GH74.GLS.TwoThin.isPCompIn_two_iff.mp hI).2
  have hLcomp : CFSG.IsComponent Lb := by
    dsimp [Lb]
    simpa [CFSG.GH74.GLS.Th2.P85.imgM] using
      CFSG.GH74.GLS.TwoThin.isComponent_map_barMk
        (Y := ↥H) (K := L.subgroupOf H)
        (CFSG.GH74.GLS.TwoThin.isPCompIn_two_iff.mp hL).2
  have hIopen : CFSG.Open.IsComponentOf Ib ⊤ :=
    (CFSG.isComponent_iff_open Ib).mp hIcomp
  have hLopen : CFSG.Open.IsComponentOf Lb ⊤ :=
    (CFSG.isComponent_iff_open Lb).mp hLcomp
  have himg_ne : Ib ≠ Lb := by
    intro heq
    have hsubEq : I.subgroupOf H = L.subgroupOf H :=
      CFSG.ComponentClassification.OddKernelTwoComponents.lift_unique
        (CFSG.GH74.GLS.TwoThin.barMk ↥H)
        CFSG.GH74.GLS.TwoThin.barMk_surjective
        CFSG.GH74.GLS.TwoThin.odd_card_ker_barMk
        (I.subgroupOf H) (L.subgroupOf H)
        (CFSG.GH74.GLS.TwoThin.isPCompIn_two_iff.mp hI).2
        (CFSG.GH74.GLS.TwoThin.isPCompIn_two_iff.mp hL).2
        (by simpa [Ib, Lb, CFSG.GH74.GLS.Th2.P85.imgM] using heq)
    have hIL : I = L := by
      have hmap := congrArg (Subgroup.map H.subtype) hsubEq
      rwa [Subgroup.map_subgroupOf_eq_of_le hI.1,
        Subgroup.map_subgroupOf_eq_of_le hL.1] at hmap
    exact hne hIL
  have htypeEq : CFSG.pRank 2 ↥H = CFSG.Open.pRank 2 H :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥H).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup H).symm
  have hrankType : CFSG.pRank 2 ↥H ≤ 1 := by rwa [htypeEq]
  have hodd : ¬ 2 ∣ Nat.card (CFSG.pPrimeCore 2 ↥H) :=
    (Nat.prime_two.coprime_iff_not_dvd).1 CFSG.pPrimeCore_coprime_card
  have hquot : CFSG.pRank 2 Y = CFSG.pRank 2 ↥H :=
    CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd
      Nat.prime_two (CFSG.pPrimeCore 2 ↥H) hodd
  have h2I : 2 ∣ Nat.card ↥I :=
    even_iff_two_dvd.mp (CFSG.GH74.GLS.C3.Layer1.Bk.even_card_of_isPCompIn hI)
  have h2H : 2 ∣ Nat.card ↥H :=
    dvd_trans h2I (Subgroup.card_dvd_of_le hI.1)
  have hquotLe : CFSG.pRank 2 Y ≤ 1 := by
    rw [hquot]
    exact hrankType
  have hquotGe : 1 ≤ CFSG.pRank 2 Y := by
    rw [hquot, CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥H]
    exact CFSG.one_le_pRank_of_dvd_card Nat.prime_two h2H
  have hquotEq : CFSG.pRank 2 Y = 1 := le_antisymm hquotLe hquotGe
  let P : Sylow 2 Y := default
  have hPtop : IsSylowOf 2 (P : Subgroup Y) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, P.isPGroup', by rw [Subgroup.relIndex_top_right]; exact P.not_dvd_index⟩
  have hRtype : IsCyclic (P : Subgroup Y) ∨
      CFSG.ComponentClassification.AschbacherTheorem3.IsDihedralTwoGroup (P : Subgroup Y) ∨
      CFSG.ComponentClassification.AschbacherTheorem3.IsQuaternionTwoGroup (P : Subgroup Y) := by
    rcases CFSG.ComponentClassification.GSLit.sylow_cyclic_or_quaternion_of_pRank_eq_one
      hquotEq P with hcyc | ⟨r, hr3, he⟩
    · exact Or.inl hcyc
    · exact Or.inr (Or.inr ⟨r, hr3, he⟩)
  let K : Fin 2 → Subgroup Y := fun i => if i = 0 then Ib else Lb
  have hK : ∀ i, CFSG.Open.IsComponentOf (K i) ⊤ := by
    intro i
    fin_cases i
    · simpa [K, Ib] using hIopen
    · simpa [K, Lb] using hLopen
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x := by
    intro i j hij x hx y hy
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · have hc : ⁅Ib, Lb⁆ = ⊥ :=
        (CFSG.LocalCores.distinct_components_commute hIcomp hLcomp).resolve_left himg_ne
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
      have hx' : x ∈ Ib := by simpa [K, Ib] using hx
      have hy' : y ∈ Lb := by simpa [K, Lb] using hy
      exact (Subgroup.mem_centralizer_iff.1 (hle hx') y hy').symm
    · have hc : ⁅Lb, Ib⁆ = ⊥ :=
        (CFSG.LocalCores.distinct_components_commute hLcomp hIcomp).resolve_left
          (Ne.symm himg_ne)
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
      have hxL : x ∈ Lb := by simpa [K, Lb] using hx
      have hyI : y ∈ Ib := by simpa [K, Ib] using hy
      exact (Subgroup.mem_centralizer_iff.1 (hle hxL) y hyI).symm
    · exact (hij rfl).elim
  have huniq := CFSG.ComponentClassification.AschbacherTheorem5.SectionSix.components_subsingleton_of_sylow
    (X := Y) (K := K) (Q := ⊤) (R := (P : Subgroup Y))
    hK (fun _ => le_top) hcomm hPtop hRtype
  exact absurd (huniq 0 1) (by decide)
theorem cmk_cmap {N L : Subgroup G} {u : G} (hu : u ∈ N) :
    cmap u (CMK N L) = CMK N (cmap u L) := by
  have hN : cmap u N = N :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hu)
  unfold CMK
  rw [CFSG.GH74.GLS.C3.Layer1.PumpL42.cmap_inf,
    CFSG.GH74.GLS.C3.Layer1.PumpL42.cmap_centralizerSection,
    pPrimeCoreOf_cmap, hN]

theorem pRank_CMK_cmap {N L : Subgroup G} {u : G} (hu : u ∈ N) :
    CFSG.pRank 2 ↥(CMK N (cmap u L)) = CFSG.pRank 2 ↥(CMK N L) := by
  rw [← cmk_cmap hu]
  exact CFSG.GH74.GLS.Th2.pRank_cj u (CMK N L)

theorem cmk_rank_ne_of_conj {N I L : Subgroup G}
    (hrankI : CFSG.Open.pRank 2 (CMK N I) ≤ 1)
    (hrankL : 2 ≤ CFSG.Open.pRank 2 (CMK N L)) :
    ∀ u ∈ N, cmap u L ≠ I := by
  intro u hu heq
  have htypeI : CFSG.pRank 2 ↥(CMK N I) = CFSG.Open.pRank 2 (CMK N I) :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥(CMK N I)).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (CMK N I)).symm
  have htypeL : CFSG.pRank 2 ↥(CMK N L) = CFSG.Open.pRank 2 (CMK N L) :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥(CMK N L)).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (CMK N L)).symm
  have hrankIType : CFSG.pRank 2 ↥(CMK N I) ≤ 1 := by rwa [htypeI]
  have hrankLType : 2 ≤ CFSG.pRank 2 ↥(CMK N L) := by rwa [htypeL]
  have hEqRank : CFSG.pRank 2 ↥(CMK N I) = CFSG.pRank 2 ↥(CMK N L) := by
    rw [← heq]
    exact pRank_CMK_cmap (N := N) (L := L) hu
  omega
theorem normal_of_not_normal_of_pRank_le_one {N I L : Subgroup G}
    (hI : IsPCompIn 2 N I) (hL : IsPCompIn 2 N L) (hILne : I ≠ L)
    (hrankI : CFSG.Open.pRank 2 (CMK N I) ≤ 1)
    (hnotconj : ∀ u ∈ N, cmap u L ≠ I) :
    (L.subgroupOf N).Normal := by
  by_contra hnotnormal
  have hnotnorm : ¬ N ≤ normalizer (L : Set G) := by
    intro h
    exact hnotnormal ((Subgroup.normal_subgroupOf_iff_le_normalizer hL.1).2 h)
  rw [SetLike.le_def] at hnotnorm
  push Not at hnotnorm
  obtain ⟨u, huN, huNotNorm⟩ := hnotnorm
  have hLune : cmap u L ≠ L := by
    intro heq
    apply huNotNorm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [cmap] using heq
  have hLuP : IsPCompIn 2 N (cmap u L) := by
    have h := CFSG.ComponentClassification.GS82PumpInputs.P10.isPComponent_cj_subgroupOf
      (X := N) (K := L) hL.1 hL.2 (g := u) (Subgroup.le_normalizer huN)
    simpa [IsPCompIn, CFSG.ComponentClassification.GSThmB.HConfig.cj, cmap] using h
  let H : Subgroup G := CMK N I
  have hHleN : H ≤ N := by
    dsimp [H, CMK]
    exact inf_le_left
  have hLleH : L ≤ H := le_CMK_of_isPCompIn_ne hI hL hILne
  have hLuleH : cmap u L ≤ H := le_CMK_of_isPCompIn_ne hI hLuP (Ne.symm (hnotconj u huN))
  have hLcompH : IsPCompIn 2 H L :=
    CFSG.GH74.GLS.C3.Layer1.Bk.isPCompIn_of_le hL hLleH hHleN
  have hLucompH : IsPCompIn 2 H (cmap u L) :=
    CFSG.GH74.GLS.C3.Layer1.Bk.isPCompIn_of_le hLuP hLuleH hHleN
  exact false_of_two_distinct_isPCompIn_of_pRank_le_one hLcompH hLucompH
    (Ne.symm hLune) (by simpa [H] using hrankI)

theorem normal_and_card_of_conj {M N K L : Subgroup G} {g : G}
    (hN : N = cmap g M) (hK : L = cmap g K) (hLN : L ≤ N)
    (hLnormal : (L.subgroupOf N).Normal) :
    (∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) ∧ Nat.card M = Nat.card N := by
  have hNL : N ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).1 hLnormal
  have hKnormal : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K := by
    intro m hm k hk
    have hmN : g * m * g⁻¹ ∈ N := by
      rw [hN]
      exact ⟨m, hm, rfl⟩
    have hkL : g * k * g⁻¹ ∈ L := by
      rw [hK]
      exact ⟨k, hk, rfl⟩
    have h1 : (g * m * g⁻¹) * (g * k * g⁻¹) * (g * m * g⁻¹)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hNL hmN) (g * k * g⁻¹)).mp hkL
    have h2 : (g * m * g⁻¹) * (g * k * g⁻¹) * (g * m * g⁻¹)⁻¹ =
        g * (m * k * m⁻¹) * g⁻¹ := by group
    have h3L : g * (m * k * m⁻¹) * g⁻¹ ∈ L := by
      rw [← h2]
      exact h1
    have h3 : g * (m * k * m⁻¹) * g⁻¹ ∈ cmap g K := by
      rw [← hK]
      exact h3L
    have h4 := (CFSG.GH74.GLS.Stage1.Thm3.Sec4.mem_cmap).1 h3
    have h5 : g⁻¹ * (g * (m * k * m⁻¹) * g⁻¹) * g = m * k * m⁻¹ := by group
    rwa [h5] at h4
  refine ⟨hKnormal, ?_⟩
  rw [hN, cmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem K_eq_I_of_rank_one {M N K I L R K0 : Subgroup G} {g : G}
    (hK : IsPCompIn 2 M K) (hI : IsPCompIn 2 N I) (hL : IsPCompIn 2 N L)
    (hILne : I ≠ L)
    (hRsyl : IsSylowOf 2 R (CMK N I))
    (hRleCMK : R ≤ CMK M K)
    (hpreM : ∀ t ∈ CMK M K, orderOf t = 2 → centralizer ({t} : Set G) ≤ M)
    (hpreN : ∀ t ∈ CMK N L, orderOf t = 2 → centralizer ({t} : Set G) ≤ N)
    (hrankI : CFSG.Open.pRank 2 (CMK N I) ≤ 1)
    (hrankL : 2 ≤ CFSG.Open.pRank 2 (CMK N L))
    (hrankCMKM : 2 ≤ CFSG.Open.pRank 2 (CMK M K))
    (hNconj : N = cmap g M) (hKconj : L = cmap g K)
    (hK0K : K0 ≤ K) (hK0I : K0 ≤ I)
    (hcoverK : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o)
    (hcoverI : ∀ i ∈ I, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 I, i = k0 * o) :
    K = I := by
  have hnotconj : ∀ u ∈ N, cmap u L ≠ I := cmk_rank_ne_of_conj hrankI hrankL
  have hLnormal : (L.subgroupOf N).Normal :=
    normal_of_not_normal_of_pRank_le_one hI hL hILne hrankI hnotconj
  obtain ⟨hKnormal, hcardMN⟩ := normal_and_card_of_conj hNconj hKconj hL.1 hLnormal
  exact K_eq_I_of_normal_component hK hI hL hILne hLnormal hKnormal
    hRsyl hRleCMK hpreM hpreN hcardMN hrankCMKM hrankL
    hK0K hK0I hcoverK hcoverI
theorem K_eq_I_of_source16_6 {M N K I L R K0 : Subgroup G} {g : G}
    (hK : IsPCompIn 2 M K) (hI : IsPCompIn 2 N I) (hL : IsPCompIn 2 N L)
    (hRsyl : IsSylowOf 2 R (CMK N I))
    (hRleCMK : R ≤ CMK M K)
    (hpreM : ∀ t ∈ CMK M K, orderOf t = 2 → centralizer ({t} : Set G) ≤ M)
    (hpreN : ∀ t ∈ CMK N L, orderOf t = 2 → centralizer ({t} : Set G) ≤ N)
    (hrankL : 2 ≤ CFSG.Open.pRank 2 (CMK N L))
    (hrankCMKM : 2 ≤ CFSG.Open.pRank 2 (CMK M K))
    (hNconj : N = cmap g M) (hKconj : L = cmap g K)
    (hK0K : K0 ≤ K) (hK0I : K0 ≤ I)
    (hcoverK : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o)
    (hcoverI : ∀ i ∈ I, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 I, i = k0 * o) :
    K = I := by
  by_cases hIL : I = L
  ·
    subst I
    obtain ⟨E, hER, hE4, hE2⟩ := exists_fourSub_of_isSylow_rank hRsyl hrankL
    have hRleN : R ≤ N := hRsyl.le.trans (by dsimp [CMK]; exact inf_le_left)
    have hRleM : R ≤ M := hRleCMK.trans (by dsimp [CMK]; exact inf_le_left)
    have hpreEN : ∀ e ∈ E, e ≠ 1 → centralizer ({e} : Set G) ≤ N := by
      intro e he he1
      have heN : e ∈ CMK N L := hRsyl.le (hER he)
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have heord : orderOf e = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact hE2 e he) he1
      exact hpreN e heN heord
    have hpreEM : ∀ e ∈ E, e ≠ 1 → centralizer ({e} : Set G) ≤ M := by
      intro e he he1
      have heM : e ∈ CMK M K := hRleCMK (hER he)
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have heord : orderOf e = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact hE2 e he) he1
      exact hpreM e heM heord
    exact K_eq_I_of_fourCentralizers_and_oddCores hE4 hE2 (hER.trans hRleM) hpreEN
      hE4 hE2 (hER.trans hRleN) hpreEM hK hI hK0K hK0I hcoverK hcoverI
  · by_cases hrankI : 2 ≤ CFSG.Open.pRank 2 (CMK N I)
    · exact K_eq_I_of_rank_two hK hI hL hIL hRsyl hRleCMK hpreM hpreN
        hrankI hrankL hK0K hK0I hcoverK hcoverI
    · have hIle : CFSG.Open.pRank 2 (CMK N I) ≤ 1 := by omega
      exact K_eq_I_of_rank_one hK hI hL hIL hRsyl hRleCMK hpreM hpreN
        hIle hrankL hrankCMKM hNconj hKconj hK0K hK0I hcoverK hcoverI
theorem pLayerOf_le_M_of_isPCompIn [IsSimpleGroup G] {M N K : Subgroup G}
    (hM : IsCoatom M) (hKM : IsPCompIn 2 M K) (hKN : IsPCompIn 2 N K)
    (hpreM : ∀ t ∈ CMK M K, orderOf t = 2 → centralizer ({t} : Set G) ≤ M) :
    pLayerOf 2 N ≤ M := by
  have hlayerNorm : pLayerOf 2 N ≤ normalizer (K : Set G) :=
    CFSG.GH74.GLS.Stage1.Thm2.Recip.pLayerOf_le_normalizer hKN
  exact hlayerNorm.trans (CFSG.GH74.GLS.Th2.L163.normalizer_le hM hKM hpreM)

set_option maxHeartbeats 1000000 in
theorem isPCompIn_le_pLayerOf_of_cover {M N I1 I0 : Subgroup G}
    (hI1 : IsPCompIn 2 N I1) (hI1M : I1 ≤ M)
    (hI0I1 : I0 ≤ I1) (hI0le : I0 ≤ pLayerOf 2 M)
    (hcover : I1 ≤ I0 ⊔ pPrimeCoreOf 2 I1) :
    I1 ≤ pLayerOf 2 M := by
  let D := ↥I1
  let O : Subgroup D := (pPrimeCoreOf 2 I1).subgroupOf I1
  let N0 : Subgroup D := Subgroup.normalClosure ((I0.subgroupOf I1 : Subgroup D) : Set D)
  have hOodd : Odd (Nat.card ↥O) := by
    have hcard : Nat.card ↥O = Nat.card ↥(pPrimeCoreOf 2 I1) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (TwoThin.pPrimeCoreOf_le I1)).toEquiv
    simpa [hcard] using TwoThin.card_pPrimeCoreOf_odd I1
  have hres : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 2 ↥I1 = ⊤ :=
    CFSG.ComponentClassification.SolMax.primeResidual_eq_top_of_isPComponent hI1.1 hI1.2
  have hLtop : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 2 ↥(⊤ : Subgroup D) = ⊤ := by
    let e : ↥(⊤ : Subgroup D) ≃* D := Subgroup.topEquiv
    have hmap := CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_map_equiv 2 e
    rw [hres] at hmap
    ext y
    constructor
    · intro _; exact Subgroup.mem_top _
    · intro _
      have hy : e y ∈ (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 2
          ↥(⊤ : Subgroup D)).map e.toMonoidHom := by
        rw [hmap]
        exact Subgroup.mem_top _
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
      rwa [e.injective hzy] at hz
  have hsup : (⊤ : Subgroup D) ≤ N0 ⊔ O := by
    have hsupI : (I0.subgroupOf I1 : Subgroup D) ⊔ O = ⊤ := by
      apply Subgroup.map_injective I1.subtype_injective
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hI0I1,
        Subgroup.map_subgroupOf_eq_of_le (TwoThin.pPrimeCoreOf_le I1)]
      have hsupG : I0 ⊔ pPrimeCoreOf 2 I1 = I1 :=
        le_antisymm (sup_le hI0I1 (TwoThin.pPrimeCoreOf_le I1)) hcover
      rw [hsupG]
      simpa using (Subgroup.map_subgroupOf_eq_of_le (le_rfl : I1 ≤ I1)).symm
    rw [← hsupI]
    exact sup_le_sup (Subgroup.le_normalClosure) le_rfl
  have hPLnormM : M ≤ normalizer ((pLayerOf 2 M : Subgroup G) : Set G) :=
    fun m hm => CFSG.GH74.GLS.Stage1.Thm2.Recip.mem_normalizer_pLayerOf hm
  have hnormal : ((pLayerOf 2 M).subgroupOf I1).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
    intro i hi
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxPL, hxI⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hPLnormM (hI1M hi)) x).mp hxPL,
        I1.mul_mem (I1.mul_mem hi hxI) (I1.inv_mem hi)⟩
    · rintro ⟨hxPL, hxI⟩
      have hxPL' : x ∈ pLayerOf 2 M :=
        (Subgroup.mem_normalizer_iff.mp (hPLnormM (hI1M hi)) x).mpr hxPL
      have hxI' : x ∈ I1 := by
        have h1 : i⁻¹ * (i * x * i⁻¹) * i ∈ I1 :=
          I1.mul_mem (I1.mul_mem (I1.inv_mem hi) hxI) hi
        simpa [mul_assoc] using h1
      exact ⟨hxPL', hxI'⟩
  have hI0sub : (I0.subgroupOf I1 : Subgroup D) ≤ (pLayerOf 2 M).subgroupOf I1 := by
    intro z hz
    exact hI0le hz
  have hN0le : N0 ≤ (pLayerOf 2 M).subgroupOf I1 :=
    Subgroup.normalClosure_le_normal hI0sub
  have htop : (⊤ : Subgroup D) ≤ (pLayerOf 2 M).subgroupOf I1 :=
    (CFSG.OddStandard.Solomon75.le_of_le_sup_odd_of_primeResidual hOodd hLtop hsup).trans hN0le
  intro x hx
  have hx' : (⟨x, hx⟩ : D) ∈ (pLayerOf 2 M).subgroupOf I1 := htop (Subgroup.mem_top _)
  exact hx'

theorem pLayerOf_le_pLayerOf_of_capture {M N K : Subgroup G} [IsSimpleGroup G]
    (hKM : IsPCompIn 2 M K) (hKN : IsPCompIn 2 N K)
    (hLayerM : pLayerOf 2 N ≤ M)
    (hcapture : ∀ I1 : Subgroup G, IsPCompIn 2 N I1 → I1 ≠ K →
      ∃ I0 : Subgroup G, I0 ≤ I1 ∧ I0 ≤ pLayerOf 2 M ∧
        I1 ≤ I0 ⊔ pPrimeCoreOf 2 I1) :
    pLayerOf 2 N ≤ pLayerOf 2 M := by
  refine sSup_le ?_
  intro I1 hI1
  by_cases h : I1 = K
  · subst I1
    exact le_sSup hKM
  · obtain ⟨I0, hI0I1, hI0le, hcover⟩ := hcapture I1 hI1 h
    exact isPCompIn_le_pLayerOf_of_cover hI1 ((le_sSup hI1).trans hLayerM)
      hI0I1 hI0le hcover


theorem pLayerOf_eq_of_conj {M N : Subgroup G} {g : G}
    (hN : N = cmap g M) (hle : pLayerOf 2 N ≤ pLayerOf 2 M) :
    pLayerOf 2 N = pLayerOf 2 M := by
  subst N
  rw [CFSG.GH74.GLS.Stage1.Thm3.Sec4.pLayerOf_cmap] at hle ⊢
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]


theorem mem_of_pLayerOf_eq {M N K : Subgroup G} {g : G} [IsSimpleGroup G]
    (hM : IsCoatom M) (hKM : IsPCompIn 2 M K)
    (hN : N = cmap g M)
    (hEq : pLayerOf 2 N = pLayerOf 2 M) :
    g ∈ M := by
  let H := pLayerOf 2 M
  have hKne : K ≠ ⊥ := by
    intro hbot
    have hne := CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_ne_bot hKM.2
    exact hne (by simpa [hbot] using hne)
  have hKle : K ≤ H := le_sSup hKM
  have hHne : H ≠ ⊥ := by
    intro hbot
    exact hKne (le_bot_iff.mp (hKle.trans (le_of_eq hbot)))
  have hHleM : H ≤ M := TwoThin.pLayerOf_le 2 M
  have hHM : M ≤ normalizer (H : Set G) :=
    fun m hm => CFSG.GH74.GLS.Stage1.Thm2.Recip.mem_normalizer_pLayerOf hm
  have hNle : normalizer (H : Set G) ≤ M := by
    have hLn : ∀ m ∈ M, ∀ l ∈ H, m * l * m⁻¹ ∈ H :=
      fun m hm l hl => (Subgroup.mem_normalizer_iff.mp (hHM hm) l).1 hl
    have hEqN := CFSG.GH74.GLS.C3.Layer1.Bk.normalizer_eq_of_coatom
      (G := G) inferInstance hM hHleM hLn hHne
    exact hEqN.le
  apply hNle
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmap : pLayerOf 2 N = cmap g H := by
    rw [hN, CFSG.GH74.GLS.Stage1.Thm3.Sec4.pLayerOf_cmap]
  rw [hEq] at hmap
  exact hmap.symm




theorem le_pLayerOf_of_isPComponent_centralizer {M : Subgroup G} {x : G} {T : Subgroup G}
    (hxM : x ∈ M) (hx2 : orderOf x = 2)
    (hTM : T ≤ M) (hTC : T ≤ Subgroup.centralizer ({x} : Set G))
    (hpc : IsPComponent 2 (T.subgroupOf (M ⊓ Subgroup.centralizer ({x} : Set G))))
    (hLB : CFSG.Open.LBalanceStatement)
    (hbridge : CFSG.Assembly.CatalogImp CFSG.Blueprint.Catalog CFSG.Assembly.InCatalog)
    (hKgroupM : SectionRank.IsKGroupCat ↥M) :
    T ≤ pLayerOf 2 M := by
  let xM : ↥M := ⟨x, hxM⟩
  let CM : Subgroup ↥M := Subgroup.centralizer ({xM} : Set ↥M)
  let TM : Subgroup ↥M := T.subgroupOf M
  have hTMmap : TM.map M.subtype = T :=
    Subgroup.map_subgroupOf_eq_of_le hTM
  have hCMmap : CM.map M.subtype = M ⊓ Subgroup.centralizer ({x} : Set G) := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c.2, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc))
    · intro hy
      refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hy.2))
  have hpcMap : IsPComponent 2 ((TM.map M.subtype).subgroupOf (CM.map M.subtype)) := by
    rw [hTMmap, hCMmap]
    exact hpc
  have hpcTM : IsPComponent 2 (TM.subgroupOf CM) :=
    (CFSG.ComponentClassification.Burgoyne.isPComponent_subgroupOf_map_iff
      (X := ↥M) (G := G) 2 Nat.prime_two (f := M.subtype) M.subtype_injective
      (S := TM) (H := CM)).mpr hpcMap
  have hTMleCM : TM ≤ CM := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hTC ht))
  have hJl : CFSG.Open.lBalanceIsPComponent 2 CM TM :=
    (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance
      2 CM TM hTMleCM).1 hpcTM
  have hXbar : CFSG.Open.lBalanceIsKGroup ↥M :=
    CFSG.GH74.GLS.Th2.IV26.lBalanceIsKGroup_of_isKGroupNative hbridge hKgroupM
  have hxM2 : orderOf xM = 2 := (Subgroup.orderOf_mk x hxM).trans hx2
  have hTwo : IsPGroup 2 (Subgroup.zpowers xM) :=
    CFSG.GH74.L5U5.isPGroup_zpowers_of_orderOf_eq_two hxM2
  have hclause := (hLB ↥M hXbar 2 Nat.prime_two (Subgroup.zpowers xM) hTwo).2.1
  have hcent : Subgroup.centralizer (Subgroup.zpowers xM : Set ↥M) =
      Subgroup.centralizer ({xM} : Set ↥M) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hTMle : TM ≤ CFSG.pLayer ↥M 2 := by
    calc TM ≤ CFSG.Open.lBalancePLayer 2 CM := le_sSup hJl
      _ ≤ CFSG.Open.lBalancePLayer 2 ⊤ := by
        rw [hcent] at hclause
        exact hclause
      _ = CFSG.pLayer ↥M 2 :=
        CFSG.ComponentClassification.LBalance.Asm.lBalancePLayer_top ↥M 2
  calc T = TM.map M.subtype := hTMmap.symm
    _ ≤ (CFSG.pLayer ↥M 2).map M.subtype := Subgroup.map_mono hTMle
    _ = pLayerOf 2 M :=
      (CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B.pLayerOf_eq_map' 2 M).symm

theorem gsFixedLayer_capture {M N K I1 : Subgroup G} {x : G}
    (hKM : IsPCompIn 2 M K) (hI1 : IsPCompIn 2 N I1)
    (hI1M : I1 ≤ M) (hxK : x ∈ K) (hxN : x ∈ N)
    (hx2 : orderOf x = 2)
    (hLB : CFSG.Open.LBalanceStatement)
    (hbridge : CFSG.Assembly.CatalogImp CFSG.Blueprint.Catalog CFSG.Assembly.InCatalog)
    (hKgroupM : SectionRank.IsKGroupCat ↥M)
    (hxNorm : x ∈ normalizer (I1 : Set G))
    (hcomm : ∀ j ∈ I1, j⁻¹ * x⁻¹ * j * x ∈ (pPrimeCore 2 I1).map I1.subtype)
    (hCxN : centralizer ({(x : G)} : Set G) ≤ N) :
    ∃ I0 : Subgroup G, I0 ≤ I1 ∧ I0 ≤ pLayerOf 2 M ∧
      I1 ≤ I0 ⊔ pPrimeCoreOf 2 I1 := by
  have hxM : x ∈ M := hKM.1 hxK
  have hI1sub : (I1.subgroupOf N).IsSubnormal := by
    obtain ⟨K', _hcomp', hsub', _hmap', _hmin'⟩ := hI1.2
    exact hsub'
  have hI1q : IsQuasisimple (↥I1 ⧸ pPrimeCore 2 ↥I1) := TwoThin.isQuasisimple_hat hI1
  let I0 : Subgroup G := CFSG.ComponentClassification.UnbalancedGS.gsFixedLayer I1 x
  have hI0I1 : I0 ≤ I1 :=
    (CFSG.ComponentClassification.UnbalancedGS.gsFixedLayer_le_inf I1 x).trans inf_le_left
  have hI0C : I0 ≤ centralizer ({(x : G)} : Set G) :=
    (CFSG.ComponentClassification.UnbalancedGS.gsFixedLayer_le_inf I1 x).trans inf_le_right
  have hlocal : IsPComponent 2 (I0.subgroupOf (N ⊓ centralizer ({(x : G)} : Set G))) :=
    CFSG.ComponentClassification.UnbalancedCorr.gsFixedLayer_isPComponent
      hI1.1 hI1sub hxN hx2 hxNorm hI1q hcomm
  have hpcC : IsPComponent 2 (I0.subgroupOf (centralizer ({(x : G)} : Set G))) :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_of_le
      hI0C (le_inf hCxN le_rfl) hlocal
  have hpcM : IsPComponent 2 (I0.subgroupOf (M ⊓ centralizer ({(x : G)} : Set G))) :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_of_le
      (le_inf (hI0I1.trans hI1M) hI0C) inf_le_right hpcC
  have hI0le : I0 ≤ pLayerOf 2 M :=
    le_pLayerOf_of_isPComponent_centralizer hxM hx2 (hI0I1.trans hI1M) hI0C hpcM
      hLB hbridge hKgroupM
  have hsup : I0 ⊔ (pPrimeCore 2 I1).map I1.subtype = I1 :=
    CFSG.ComponentClassification.UnbalancedLayer.gsFixedLayer_sup_map_pPrimeCore
      hx2 hI1q hxNorm hcomm
  refine ⟨I0, hI0I1, hI0le, ?_⟩
  simpa [pPrimeCoreOf] using hsup.ge


set_option maxHeartbeats 1000000 in
theorem commonComponent_mem_of_isPCompIn {M N J L : Subgroup G} {g : G} [IsSimpleGroup G]
    (hM : IsCoatom M) (hJM : IsPCompIn 2 M J)
    (hpreM : ∀ t ∈ CMK M J, orderOf t = 2 → centralizer ({t} : Set G) ≤ M)
    (hN : N = cmap g M) (hL : L = cmap g J)
    (hJN : IsPCompIn 2 N J)
    (hLB : CFSG.Open.LBalanceStatement)
    (hbridge : CFSG.Assembly.CatalogImp CFSG.Blueprint.Catalog CFSG.Assembly.InCatalog)
    (hKgroupM : SectionRank.IsKGroupCat ↥M) :
    g ∈ M := by
  have hNleJ : normalizer (J : Set G) ≤ M :=
    CFSG.GH74.GLS.Th2.L163.normalizer_le hM hJM hpreM
  by_cases hLJ : L = J
  · have hmapJ : cmap g J = J := by rw [← hL, hLJ]
    have hgNorm : g ∈ normalizer (J : Set G) :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).2 (by simpa [cmap] using hmapJ)
    exact hNleJ hgNorm
  · have hLN : IsPCompIn 2 N L := by
      rw [hN, hL]
      exact CFSG.GH74.GLS.Stage1.Thm3.Sec4.isPCompIn_cmap hJM g
    have hJleCMK_L : J ≤ CMK N L :=
      le_CMK_of_isPCompIn_ne hLN hJN hLJ
    have hcmk_map : cmap g (CMK M J) = CMK N L := by
      rw [hN, hL]
      unfold CMK
      rw [CFSG.GH74.GLS.C3.Layer1.PumpL42.cmap_inf,
        CFSG.GH74.GLS.C3.Layer1.PumpL42.cmap_centralizerSection,
        CFSG.GH74.GLS.Stage1.Thm3.Sec4.pPrimeCoreOf_cmap]
    have hpreN : ∀ t ∈ CMK N L, orderOf t = 2 →
        centralizer ({t} : Set G) ≤ N := by
      intro t ht ht2
      have htmap : t ∈ cmap g (CMK M J) := by rwa [hcmk_map]
      rcases Subgroup.mem_map.mp htmap with ⟨u, hu, hut⟩
      have hut' : g * u * g⁻¹ = t := by simpa [MulAut.conj_apply] using hut
      have hu2 : orderOf u = 2 := by
        rw [← CFSG.GH74.GLS.orderOf_conj' g u, hut']
        exact ht2
      have hCuM : centralizer ({u} : Set G) ≤ M := hpreM u hu hu2
      intro z hz
      have hz' : g⁻¹ * z * g ∈ centralizer ({u} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
        have hzu : z * (g * u * g⁻¹) = (g * u * g⁻¹) * z := by
          simpa [hut'] using hz
        calc
          (g⁻¹ * z * g) * u = g⁻¹ * (z * (g * u * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * u * g⁻¹) * z) * g := by rw [hzu]
          _ = u * (g⁻¹ * z * g) := by group
      have hz'M : g⁻¹ * z * g ∈ M := hCuM hz'
      have hzN : g * (g⁻¹ * z * g) * g⁻¹ ∈ N := by
        rw [hN]
        exact ⟨g⁻¹ * z * g, hz'M, rfl⟩
      have hz_eq : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
      rwa [hz_eq] at hzN
    have hLayerM : pLayerOf 2 N ≤ M :=
      pLayerOf_le_M_of_isPCompIn hM hJM hJN hpreM
    obtain ⟨x, hxJ, hx2⟩ :=
      CFSG.GH74.AS16.exists_involution_of_even
        (CFSG.GH74.GLS.C3.Layer1.Bk.even_card_of_isPCompIn hJM)
    have hxM : x ∈ M := hJM.1 hxJ
    have hxN : x ∈ N := hJN.1 hxJ
    have hxCMK_L : x ∈ CMK N L := hJleCMK_L hxJ
    have hCxN : centralizer ({(x : G)} : Set G) ≤ N := hpreN x hxCMK_L hx2
    have hcapture : ∀ I1 : Subgroup G, IsPCompIn 2 N I1 → I1 ≠ J →
        ∃ I0 : Subgroup G, I0 ≤ I1 ∧ I0 ≤ pLayerOf 2 M ∧
          I1 ≤ I0 ⊔ pPrimeCoreOf 2 I1 := by
      intro I1 hI1 hI1ne
      have hI1le : I1 ≤ pLayerOf 2 N :=
        le_sSup (show I1 ∈ {L : Subgroup G | IsPCompIn 2 N L} from hI1)
      have hI1M : I1 ≤ M := hI1le.trans hLayerM
      have hJleCMK : J ≤ CMK N I1 :=
        le_CMK_of_isPCompIn_ne hI1 hJN hI1ne
      have hxCMK : x ∈ CMK N I1 := hJleCMK hxJ
      have hxNorm : x ∈ normalizer (I1 : Set G) := (CFSG.GH74.GLS.C3.Layer1.U1a.mem_CMK_iff.mp hxCMK).2.1
      have hcomm : ∀ j ∈ I1, j⁻¹ * x⁻¹ * j * x ∈ (pPrimeCore 2 I1).map I1.subtype := by
        intro j hj
        have hxNormP : x ∈ normalizer (pPrimeCoreOf 2 I1 : Set G) :=
          (CFSG.GH74.GLS.C3.Layer1.U1a.mem_CMK_iff.mp hxCMK).2.2.1
        have hc : ⁅j, x⁆ ∈ pPrimeCoreOf 2 I1 :=
          (CFSG.GH74.GLS.C3.Layer1.U1a.mem_CMK_iff.mp hxCMK).2.2.2 j hj
        have hc1 : x⁻¹ * ⁅j, x⁆ * x ∈ pPrimeCoreOf 2 I1 := by
          simpa using (Subgroup.mem_normalizer_iff.mp
            (Subgroup.inv_mem _ hxNormP) ⁅j, x⁆).1 hc
        have hc2 : j⁻¹ * (x⁻¹ * ⁅j, x⁆ * x) * j ∈ pPrimeCoreOf 2 I1 := by
          simpa using TwoThin.pPrimeCoreOf_normalized I1 (Subgroup.inv_mem _ hj) hc1
        have heq : j⁻¹ * (x⁻¹ * ⁅j, x⁆ * x) * j = j⁻¹ * x⁻¹ * j * x := by
          rw [commutatorElement_def]
          group
        rw [← heq]
        simpa [pPrimeCoreOf] using hc2
      exact gsFixedLayer_capture hJM hI1 hI1M hxJ hxN hx2 hLB hbridge hKgroupM
        hxNorm hcomm hCxN
    have hle : pLayerOf 2 N ≤ pLayerOf 2 M :=
      pLayerOf_le_pLayerOf_of_capture hJM hJN hLayerM hcapture
    have hEq : pLayerOf 2 N = pLayerOf 2 M := pLayerOf_eq_of_conj hN hle
    exact mem_of_pLayerOf_eq hM hJM hN hEq


theorem commonComponent_mem_of_source16_6 {M N K I L R K0 : Subgroup G} {g : G}
    [IsSimpleGroup G]
    (hM : IsCoatom M) (hK : IsPCompIn 2 M K) (hI : IsPCompIn 2 N I)
    (hL : IsPCompIn 2 N L)
    (hRsyl : IsSylowOf 2 R (CMK N I)) (hRleCMK : R ≤ CMK M K)
    (hpreM : ∀ t ∈ CMK M K, orderOf t = 2 → centralizer ({t} : Set G) ≤ M)
    (hpreN : ∀ t ∈ CMK N L, orderOf t = 2 → centralizer ({t} : Set G) ≤ N)
    (hrankL : 2 ≤ CFSG.Open.pRank 2 (CMK N L))
    (hrankCMKM : 2 ≤ CFSG.Open.pRank 2 (CMK M K))
    (hNconj : N = cmap g M) (hKconj : L = cmap g K)
    (hK0K : K0 ≤ K) (hK0I : K0 ≤ I)
    (hcoverK : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o)
    (hcoverI : ∀ i ∈ I, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 I, i = k0 * o)
    (hLB : CFSG.Open.LBalanceStatement)
    (hbridge : CFSG.Assembly.CatalogImp CFSG.Blueprint.Catalog CFSG.Assembly.InCatalog)
    (hKgroupM : SectionRank.IsKGroupCat ↥M) :
    g ∈ M := by
  have hKI : K = I :=
    K_eq_I_of_source16_6 hK hI hL hRsyl hRleCMK hpreM hpreN hrankL hrankCMKM
      hNconj hKconj hK0K hK0I hcoverK hcoverI
  have hKN : IsPCompIn 2 N K := by
    rw [hKI]
    exact hI
  exact commonComponent_mem_of_isPCompIn hM hK hpreM hNconj hKconj hKN hLB hbridge hKgroupM



theorem commonComponent_mem_of_kproper {M N J L : Subgroup G} {g : G} [Finite G]
    (hG : CFSG.GH74.GLS.IsKProperSimple G) (hM : IsCoatom M)
    (hJM : IsPCompIn 2 M J)
    (hpreM : ∀ t ∈ CMK M J, orderOf t = 2 → centralizer ({t} : Set G) ≤ M)
    (hN : N = cmap g M) (hL : L = cmap g J)
    (hJN : IsPCompIn 2 N J)
    (hLB : CFSG.Open.LBalanceStatement)
    (hbridge : CFSG.Assembly.CatalogImp CFSG.Blueprint.Catalog CFSG.Assembly.InCatalog) :
    g ∈ M := by
  haveI : IsSimpleGroup G := hG.1
  exact commonComponent_mem_of_isPCompIn hM hJM hpreM hN hL hJN hLB hbridge
    (CFSG.GH74.GLS.isKGroupNative_of_kProper hG.2.2 hM.lt_top.ne)

theorem commonComponent_mem_of_source16_6_kproper {M N K I L R K0 : Subgroup G} {g : G}
    [Finite G]
    (hG : CFSG.GH74.GLS.IsKProperSimple G) (hM : IsCoatom M)
    (hK : IsPCompIn 2 M K) (hI : IsPCompIn 2 N I) (hL : IsPCompIn 2 N L)
    (hRsyl : IsSylowOf 2 R (CMK N I)) (hRleCMK : R ≤ CMK M K)
    (hpreM : ∀ t ∈ CMK M K, orderOf t = 2 → centralizer ({t} : Set G) ≤ M)
    (hpreN : ∀ t ∈ CMK N L, orderOf t = 2 → centralizer ({t} : Set G) ≤ N)
    (hrankL : 2 ≤ CFSG.Open.pRank 2 (CMK N L))
    (hrankCMKM : 2 ≤ CFSG.Open.pRank 2 (CMK M K))
    (hNconj : N = cmap g M) (hKconj : L = cmap g K)
    (hK0K : K0 ≤ K) (hK0I : K0 ≤ I)
    (hcoverK : ∀ k ∈ K, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 K, k = k0 * o)
    (hcoverI : ∀ i ∈ I, ∃ k0 ∈ K0, ∃ o ∈ pPrimeCoreOf 2 I, i = k0 * o)
    (hLB : CFSG.Open.LBalanceStatement)
    (hbridge : CFSG.Assembly.CatalogImp CFSG.Blueprint.Catalog CFSG.Assembly.InCatalog) :
    g ∈ M := by
  haveI : IsSimpleGroup G := hG.1
  exact commonComponent_mem_of_source16_6 hM hK hI hL hRsyl hRleCMK hpreM hpreN
    hrankL hrankCMKM hNconj hKconj hK0K hK0I hcoverK hcoverI hLB hbridge
    (CFSG.GH74.GLS.isKGroupNative_of_kProper hG.2.2 hM.lt_top.ne)


end CFSG.GH74.GLS.Th2.L165
