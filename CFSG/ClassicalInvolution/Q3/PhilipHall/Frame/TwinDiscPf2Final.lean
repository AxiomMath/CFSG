module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf2Wyl
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPfExc
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf2Mu
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscThmE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinGraph
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FStarNormal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

namespace TwinDisc

namespace Pf2


structure TwinDiscInputsPf2 (n : ℕ) : Prop where
  thmE : TwinThmE n
  base : TwinDiscBase n
  c13Exc : Disc13NExc n
  c14Exc : Disc14NExc n
  c14AltExc : Disc14AltExc n
  c15 : Disc15 n
  tqTz : DiscTqTz n
  tqU : DiscTqU n

namespace TwinDiscInputsPf2

variable {n : ℕ}

theorem c13N (I : TwinDiscInputsPf2 n) : Disc13N n := disc13N_of_exc I.base I.c13Exc
theorem c14N (I : TwinDiscInputsPf2 n) : Disc14N n := disc14N_of_exc I.base I.c14Exc
theorem c14Alt (I : TwinDiscInputsPf2 n) : Disc14Alt n := disc14Alt_of_exc I.c14AltExc
theorem c17tz (I : TwinDiscInputsPf2 n) : Disc17tz n := disc17tz_of_tq I.tqTz
theorem ySigma (I : TwinDiscInputsPf2 n) : DiscYSigma n := discYSigma_of_tq I.tqU
theorem centInStar (I : TwinDiscInputsPf2 n) : DiscCentInStar n := discCentInStar_of_tq I.tqTz
theorem c13Wyl (I : TwinDiscInputsPf2 n) : Disc13Wyl n := disc13Wyl_of_tq (disc12 n) I.tqTz

end TwinDiscInputsPf2

section Steps

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem rLayer_tz_le_sigmaGen_of_eq (hT : DiscTqTz n) (s : Setting n R S t₀ K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥)
    (heq : dComp (CoreAssembly.conjClass (tightCore R)) K =
      dstarComp (CoreAssembly.conjClass (tightCore R)) K) :
    rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
      sigmaGen (CoreAssembly.conjClass (tightCore R)) K := by
  refine iSup₂_le fun R' hR' => iSup_le fun hRc => ?_
  obtain ⟨J', hJ'Ω, hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR'
  have hdst := hT Y R S t₀ K K' z u J t W s hα J' ⟨hJ'Ω, R', hRJ', hRc⟩
  rw [← heq] at hdst
  exact hRJ'.1.trans (le_iSup₂_of_le J' hdst le_rfl)

theorem stdCent_normalizer_alpha (I : TwinDiscInputsPf2 n) (s : Setting n R S t₀ K K' z u J t W) :
    StdCent (CoreAssembly.conjClass (tightCore R)) K
      (Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y)) z := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hs : AlphaSteps Ω := alphaStepsBase I.base s
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hK : K ∈ Ω := hf.mem
  have hzK' := isUniqueInvolution_of_mem_twinSet hf.hz hf.hK'
  have hQα := hs.sup_le_normalizer hf
  have hz_le := hs.centralizer_le hf
  refine ⟨hz_le, ?_, ?_⟩
  · intro L hL J'' hJ'' z'' hz'' hzz
    have hKL := A7Q.Gen.kPerp_eq_of_twin hΩ hK hL
    have hJperp : J'' ∈ KPerp Ω K := hKL ▸ Set.mem_insert_of_mem _ hJ''
    have hnot : J'' ∉ twinSet Ω K := by
      rintro ⟨-, z₀, hz₀K, hz₀J⟩
      exact hzz ((hz₀J.eq hz'').symm.trans (hf.hz.eq hz₀K).symm)
    have hJmem : J'' ∈ omegaOfSet Ω (twinSet Ω K) :=
      A7Q.Gen.mem_omegaOfSet_of_mem_kPerp hΩ hK hJperp hnot
    refine ⟨?_, ?_⟩
    · obtain ⟨y, hyN, hy⟩ := hs.exists_mem_normalizer hf (T7A.mem_dComp_of_mem_kPerp hJperp)
      have hzy : IsUniqueInvolution J'' (y * z * y⁻¹) := hy ▸ hf.hz.conj y
      exact T7A.centralizer_conj_le hyN (hz''.eq hzy) hz_le
    · obtain ⟨g, hgQ, W₁, hfr, hW₁, hzW₁, htW₁⟩ :=
        Hat2A7S.exists_twinFrameData_at hΩ hK hf.hz hf.hK' hf.hne hf.hu hf.hu2 hf.hu1 hf.huz
          hJmem hz''
      have h' : Setting n R S t₀ K K' z u (conjSub g J'') (g * z'' * g⁻¹) W₁ :=
        ⟨s.core, s.disc, ⟨hfr, hW₁, hzW₁, htW₁⟩⟩
      have h13' := I.c13N Y R S t₀ K K' z u (conjSub g J'') (g * z'' * g⁻¹) W₁ h'
      have hcomm : z * (g * z'' * g⁻¹) = (g * z'' * g⁻¹) * z := A7Q.Gen.comm_zt hΩ hfr
      have hgN := hQα hgQ
      have hzQ : g * z * g⁻¹ = z := by
        have := T7A.z_comm_of_mem_sup hf.hz hzK' hgQ
        calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
          _ = (z * g) * g⁻¹ := by rw [← this]
          _ = z := by group
      intro c hc
      have hc' : g * c * g⁻¹ ∈ Subgroup.centralizer ({(g * z'' * g⁻¹) * z} : Set Y) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
        have e1 : (g * z'' * g⁻¹) * z = g * (z * z'') * g⁻¹ := by
          calc (g * z'' * g⁻¹) * z = z * (g * z'' * g⁻¹) := hcomm.symm
            _ = (g * z * g⁻¹) * (g * z'' * g⁻¹) := by rw [hzQ]
            _ = g * (z * z'') * g⁻¹ := by group
        rw [e1]
        calc (g * c * g⁻¹) * (g * (z * z'') * g⁻¹) = g * (c * (z * z'')) * g⁻¹ := by group
          _ = g * ((z * z'') * c) * g⁻¹ := by rw [hc]
          _ = (g * (z * z'') * g⁻¹) * (g * c * g⁻¹) := by group
      exact T7A.mem_of_conj_mem hgN (h13' hc')
  · intro L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy hx4 hy4
    have hLΩ : L ∈ Ω := hL.1
    have hzL := isUniqueInvolution_of_mem_twinSet hf.hz hL
    have hzL' := isUniqueInvolution_of_mem_twinSet hf.hz hL'
    have htwL : twinSet Ω L = twinSet Ω K := twinSet_eq_of_mem_twinSet hf.hz hL
    have hL'L : L' ∈ twinSet Ω L := by rw [htwL]; exact hL'
    have hJL : J ∈ omegaOfSet Ω (twinSet Ω L) := by rw [htwL]; exact hf.hJ
    obtain ⟨g, hgQ, W₂, hJg, htg, hW₂, hzW₂, htW₂, hfr⟩ :=
      Hat2A7S.exists_twinFrameData_of_sylows hΩ hLΩ hzL hL'L hne hJL hf.ht hR₁ hR₂ hc
    have hfr' := hfr x hx y hy hx4 hy4
    have h' : Setting n R S t₀ L L' z (x * y) (conjSub g J) (g * t * g⁻¹) W₂ :=
      ⟨s.core, s.disc, ⟨hfr', hW₂, hzW₂, htW₂⟩⟩
    have h14' := I.c14N Y R S t₀ L L' z (x * y) (conjSub g J) (g * t * g⁻¹) W₂ h'
    have hα1 := hs.alpha_zt hfr'
    have hgz : g * z * g⁻¹ = z := by
      have := T7A.z_comm_of_mem_sup hzL hzL' hgQ
      calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
        _ = (z * g) * g⁻¹ := by rw [← this]
        _ = z := by group
    have h2 : conjSub g (Subgroup.closure ({z, t} : Set Y)) =
        Subgroup.closure ({z, g * t * g⁻¹} : Set Y) := by
      rw [T7A.conjSub_closure_pair, hgz]
    have hαz := hs.alpha_zt hf
    have hgN : g ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) :=
      sup_le (hs.twin_le hf hL) (hs.twin_le hf hL') hgQ
    have hαeq : alphaOf (Subgroup.closure ({x * y, z} : Set Y)) =
        alphaOf (Subgroup.closure ({u, z} : Set Y)) := by
      rw [← hα1, ← h2, alphaOf_conjSub, hαz]
      exact mem_normalizer_iff_conjSub_eq.mp hgN
    rw [hαeq] at h14'
    exact h14'

theorem c21_16 (I : TwinDiscInputsPf2 n) (s : Setting n R S t₀ K K' z u J t W) :
    alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  by_contra hα
  have hs : AlphaSteps Ω := alphaStepsBase I.base s
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hstd := stdCent_normalizer_alpha I s
  have hD : rLayer Ω (t * z) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) :=
    (rLayer_le_centralizer Ω (t * z)).trans (I.c13N Y R S t₀ K K' z u J t W s)
  have hS : sigmaGen Ω K ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) :=
    iSup₂_le fun M hM =>
      dComp_le_normalizer_alpha hΩ hs.trans hs.hyp51 hf (hs.alpha_eq hf).2 hM
  have htrans : ∀ M ∈ dstarComp Ω K, ∃ x ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y), conjSub x K = M := by
    by_cases heq : dComp Ω K = dstarComp Ω K
    · intro M hM
      rw [← heq] at hM
      exact hs.exists_mem_normalizer hf hM
    · have hP : Q3CL.PartIHypG Ω := TwinPerp.partIHypG s.core
      refine exists_mem_conj_of_dstarComp hP s.data heq
        ((mGrp_le_rLayer_tz hP s.data heq).trans hD) ?_
      intro g hg
      refine mem_normalizer_alpha_of_mem_dComp hΩ hs.trans hs.hyp51 hf ?_
      rw [mem_normalizer_iff_conjSub_eq.mp hg]
      exact Relation.ReflTransGen.refl
  have htop := thmE_apply I.thmE s.core hf.mem hf.hz hstd htrans
  have hnormal : (alphaOf (Subgroup.closure ({u, z} : Set Y))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp htop
  have hodd := (hs.alpha_eq hf).1
  have hle : alphaOf (Subgroup.closure ({u, z} : Set Y)) ≤ classicalInvolutionOddCore Y :=
    le_sSup ⟨hnormal, hodd⟩
  have hbot : classicalInvolutionOddCore Y = ⊥ := s.core.oddFree
  exact hα (le_bot_iff.mp (hbot ▸ hle))

theorem centralizer_u_le_sigmaStarNorm (I : TwinDiscInputsPf2 n)
    (s : Setting n R S t₀ K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥)
    (htz : Subgroup.centralizer ({t * z} : Set Y) ≤
      sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K) :
    Subgroup.centralizer ({u} : Set Y) ≤ sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K := by
  rcases I.c14Alt Y R S t₀ K K' z u J t W s hα with h1 | h3
  · exact I.ySigma Y R S t₀ K K' z u J t W s hα h1 htz
  · exact h3.trans htz

theorem eStar_of (I : TwinDiscInputsPf2 n) (s : Setting n R S t₀ K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥)
    (hD : ¬ rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
      sigmaGen (CoreAssembly.conjClass (tightCore R)) K)
    (hSigC : ∀ M ∈ dComp (CoreAssembly.conjClass (tightCore R)) K,
      M ≤ Subgroup.centralizer ({t * z} : Set Y))
    (hmu : MuIsoWylD4 (CoreAssembly.conjClass (tightCore R)) W) (M : Subgroup Y) :
    M ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K ↔
      M ∈ CoreAssembly.conjClass (tightCore R) ∧ M ≤ Subgroup.centralizer ({t * z} : Set Y) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hK : K ∈ Ω := s.data.frame.mem
  constructor
  · intro hM
    refine ⟨(T3.mem_dstarComp_symm hK hM).1, ?_⟩
    have hSig : sigmaGen Ω K ≤ Subgroup.centralizer ({t * z} : Set Y) :=
      iSup₂_le fun N hN => hSigC N hN
    have hP : Q3CL.PartIHypG Ω := TwinPerp.partIHypG s.core
    have hne : dComp Ω K ≠ dstarComp Ω K := fun heq =>
      hD (rLayer_tz_le_sigmaGen_of_eq I.tqTz s hα heq)
    obtain ⟨c, hc, rfl⟩ := exists_mem_conj_of_dstarComp hP s.data hne
      ((mGrp_le_rLayer_tz hP s.data hne).trans (rLayer_le_centralizer Ω (t * z)))
      (normalizer_le_centralizer_tz hP s.data hne hSigC) M hM
    have hKc : K ≤ Subgroup.centralizer ({t * z} : Set Y) := hSigC K Relation.ReflTransGen.refl
    have hcc : c * (t * z) = (t * z) * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : (c⁻¹ * x * c) * (t * z) = (t * z) * (c⁻¹ * x * c) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hKc hx)
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hcinv : c⁻¹ * (t * z) = (t * z) * c⁻¹ := by
      calc c⁻¹ * (t * z) = c⁻¹ * ((t * z) * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * (t * z)) * c⁻¹ := by rw [hcc]
        _ = (t * z) * c⁻¹ := by group
    calc x * (t * z) = (c * (c⁻¹ * x * c) * c⁻¹) * (t * z) := by group
      _ = c * ((c⁻¹ * x * c) * (c⁻¹ * (t * z))) := by group
      _ = c * (((c⁻¹ * x * c) * (t * z)) * c⁻¹) := by rw [hcinv]; group
      _ = c * (((t * z) * (c⁻¹ * x * c)) * c⁻¹) := by rw [h1]
      _ = (c * (t * z)) * (c⁻¹ * x * c * c⁻¹) := by group
      _ = ((t * z) * c) * (c⁻¹ * x * c * c⁻¹) := by rw [hcc]
      _ = (t * z) * x := by group
  · rintro ⟨hMΩ, hMc⟩
    exact I.centInStar Y R S t₀ K K' z u J t W s hα hD hSigC hmu M hMΩ hMc

theorem frame_cent_sigmaStarNorm (I : TwinDiscInputsPf2 n) (s : Setting n R S t₀ K K' z u J t W) :
    Subgroup.centralizer ({t * z} : Set Y) ≤
        sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K ∧
      Subgroup.centralizer ({u} : Set Y) ≤
        sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K := by
  have hα := c21_16 I s
  by_cases hD : rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
      sigmaGen (CoreAssembly.conjClass (tightCore R)) K
  · have htz := I.c17tz Y R S t₀ K K' z u J t W s hα hD (dComp_eq_dstarComp_of_rLayer_le (TwinPerp.partIHypG s.core) s.data hD)
    exact ⟨htz, centralizer_u_le_sigmaStarNorm I s hα htz⟩
  · have hSigC := I.c15 Y R S t₀ K K' z u J t W s hα hD
    have hmu := I.c13Wyl Y R S t₀ K K' z u J t W s hα hD
    have hstar := eStar_of I s hα hD hSigC hmu
    have htz := T7A.centralizer_le_sigmaStarNorm_of_eq s.core.hyp.conjInvariant hstar
    exact ⟨htz, centralizer_u_le_sigmaStarNorm I s hα htz⟩

theorem sigmaStarNorm_eq_top (I : TwinDiscInputsPf2 n) (s : Setting n R S t₀ K K' z u J t W) :
    sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K = ⊤ := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hf := s.data.frame
  have hK : K ∈ Ω := hf.mem
  have hs : AlphaSteps Ω := alphaStepsBase I.base s
  have htail : StdCentTail Ω K (sigmaStarNorm Ω K) z :=
    stdCentTail_of_frames_gen hΩ s.data fun {L L' J₁ W₁ u₁ t₁} _ h₁ =>
      frame_cent_sigmaStarNorm I (⟨s.core, s.disc, h₁⟩ : Setting n R S t₀ L L' z u₁ J₁ t₁ W₁)
  have hstd := stdCent_sigmaStarNorm_gen hΩ hK hf.hz 
    (fun M hM => hs.trans K hK M hM) htail
  have htrans : ∀ M ∈ dstarComp Ω K, ∃ x ∈ sigmaStarNorm Ω K, conjSub x K = M := by
    intro M hM
    obtain ⟨x, hx⟩ := hs.trans K hK M (T3.mem_dstarComp_symm hK hM).1
    exact ⟨x, T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (hx ▸ hM), hx⟩
  exact thmE_apply I.thmE s.core hK hf.hz hstd htrans

theorem c21_17 (I : TwinDiscInputsPf2 n) (s : Setting n R S t₀ K K' z u J t W) :
    ¬ rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
      sigmaGen (CoreAssembly.conjClass (tightCore R)) K := by
  intro hD
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hs : AlphaSteps Ω := alphaStepsBase I.base s
  have htop := sigmaStarNorm_eq_top I s
  have hSig := dComp_eq_dstarComp_of_rLayer_le (TwinPerp.partIHypG s.core) s.data hD
  have hsn : sigmaNorm Ω K = ⊤ := by
    rw [← htop]
    ext g
    exact forall_congr' fun M => by rw [hSig]
  exact s.disc (dConnected_of_sigmaNorm_eq_top s.data.frame.mem
    (fun J hJ => hs.trans K s.data.frame.mem J hJ) hsn)

theorem c21_E (I : TwinDiscInputsPf2 n) (s : Setting n R S t₀ K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥)
    (hD : ¬ rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
      sigmaGen (CoreAssembly.conjClass (tightCore R)) K)
    (hSigC : ∀ M ∈ dComp (CoreAssembly.conjClass (tightCore R)) K,
      M ≤ Subgroup.centralizer ({t * z} : Set Y))
    (hmu : MuIsoWylD4 (CoreAssembly.conjClass (tightCore R)) W) : False := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hs : AlphaSteps Ω := alphaStepsBase I.base s
  have hf := s.data.frame
  have hK : K ∈ Ω := hf.mem
  have htop := sigmaStarNorm_eq_top I s
  have hstar := eStar_of I s hα hD hSigC hmu
  have hall : ∀ M ∈ Ω, M ≤ Subgroup.centralizer ({t * z} : Set Y) := by
    intro M hM
    obtain ⟨x, hx⟩ := hs.trans K hK M hM
    have hxH : x ∈ sigmaStarNorm Ω K := by rw [htop]; exact Subgroup.mem_top x
    have hMS : M ∈ dstarComp Ω K := by
      have := (mem_sigmaStarNorm_iff.mp hxH K).mp Relation.ReflTransGen.refl
      rwa [hx] at this
    exact ((hstar M).mp hMS).2
  have hcent : Subgroup.centralizer ({t * z} : Set Y) = ⊤ := by
    rw [eq_top_iff, ← iSup_conjClass_eq_top s.core.gen]
    exact iSup₂_le fun M hM => hall M hM
  have hZ : Subgroup.center Y = ⊥ :=
    InductionBridge.center_eq_bot_of_fstar_simple s.core.simple s.core.nonab
  have hzc : t * z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcent ▸ Subgroup.mem_top g)
  rw [hZ, Subgroup.mem_bot] at hzc
  have h2 : t = z⁻¹ := eq_inv_of_mul_eq_one_left hzc
  have h3 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hf.hz.sq
  exact hf.t_ne_z (h2.trans h3)

theorem false_of_setting (I : TwinDiscInputsPf2 n) (s : Setting n R S t₀ K K' z u J t W) : False := by
  have hα := c21_16 I s
  have hD := c21_17 I s
  exact c21_E I s hα hD (I.c15 Y R S t₀ K K' z u J t W s hα hD)
    (I.c13Wyl Y R S t₀ K K' z u J t W s hα hD)

end Steps

end Pf2

end TwinDisc


theorem twinCoreDiscPerp_of_inputsPf2 {n : ℕ} (I : TwinDisc.Pf2.TwinDiscInputsPf2 n) :
    TwinCoreDiscPerp n := by
  intro Y _ _ R S t h hdisc hperp
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Q8Datum.isUniqueInvolution_core h.datum
  obtain ⟨K', hK', hne'⟩ := h.twin
  obtain ⟨u, J, t', W, d⟩ := TwinDisc.exists_data h.hyp hK hz hK' hne' hperp
  exact TwinDisc.Pf2.false_of_setting I ⟨h, hdisc, d⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
