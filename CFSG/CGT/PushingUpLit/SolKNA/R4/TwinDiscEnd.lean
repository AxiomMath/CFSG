module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscFinal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf4Conn

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame


section Steps

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem rLayer_tz_le_sigmaGen_of_eqR (hT : DiscTqTzR r n) (s : SettingR r n R S t₀ K K' z u J t W)
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

theorem eStar_ofR (I : TwinDiscInputsR r n) (s : SettingR r n R S t₀ K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥)
    (hD : ¬ rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
      sigmaGen (CoreAssembly.conjClass (tightCore R)) K)
    (hSigC : ∀ M ∈ dComp (CoreAssembly.conjClass (tightCore R)) K,
      M ≤ Subgroup.centralizer ({t * z} : Set Y)) (M : Subgroup Y) :
    M ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K ↔
      M ∈ CoreAssembly.conjClass (tightCore R) ∧ M ≤ Subgroup.centralizer ({t * z} : Set Y) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hK : K ∈ Ω := s.data.frame.mem
  constructor
  · intro hM
    refine ⟨(T3.mem_dstarComp_symm hK hM).1, ?_⟩
    have hSig : sigmaGen Ω K ≤ Subgroup.centralizer ({t * z} : Set Y) :=
      iSup₂_le fun N hN => hSigC N hN
    have hP : Q3CL.PartIHypG Ω := partIHypGR s.core
    have hne : dComp Ω K ≠ dstarComp Ω K := fun heq =>
      hD (rLayer_tz_le_sigmaGen_of_eqR I.tqTz s hα heq)
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
    exact centInStarR I.tqTz s hα hMΩ hMc

theorem frame_cent_sigmaStarNormR (I : TwinDiscInputsR r n) (s : SettingR r n R S t₀ K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥) :
    Subgroup.centralizer ({t * z} : Set Y) ≤
        sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K ∧
      Subgroup.centralizer ({u} : Set Y) ≤
        sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K :=
  ⟨c17tzR I.tqTz s hα, ySigmaR I.tqU s hα⟩

theorem sigmaStarNorm_eq_topR (I : TwinDiscInputsR r n) (h : TwinCoreHypR r n Y R S t₀)
    (s : SettingR r n R S t₀ K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥)
    (hP : TwinThmEW.PrintedWT (CoreAssembly.conjClass (tightCore R)) K W) :
    sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K = ⊤ := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hf := s.data.frame
  have hK : K ∈ Ω := hf.mem
  have hs : AlphaSteps Ω := alphaStepsR I.base s
  have hstar : ∀ {L : Subgroup Y}, L ∈ twinSet Ω K → sigmaStarNorm Ω L = sigmaStarNorm Ω K :=
    fun {L} hL => sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hK
      (mem_dstarComp_of_twin_gen hΩ hK hL))
  have hz_le : Subgroup.centralizer ({z} : Set Y) ≤ sigmaStarNorm Ω K :=
    centralizer_le_sigmaStarNorm_z hΩ hK hf.hz
  have hstd : StdCentW Ω K W (sigmaStarNorm Ω K) z := by
    refine ⟨hz_le, ?_, ?_⟩
    · intro L hL J'' hJ'' z'' hz'' hzz hz''W
      have hKL := A7Q.Gen.kPerp_eq_of_twin hΩ hK hL
      have hJperp : J'' ∈ KPerp Ω K := hKL ▸ Set.mem_insert_of_mem _ hJ''
      have hnot : J'' ∉ twinSet Ω K := by
        rintro ⟨-, z₀, hz₀K, hz₀J⟩
        exact hzz ((hz₀J.eq hz'').symm.trans (hf.hz.eq hz₀K).symm)
      have hJmem : J'' ∈ omegaOfSet Ω (twinSet Ω K) :=
        A7Q.Gen.mem_omegaOfSet_of_mem_kPerp hΩ hK hJperp hnot
      refine ⟨?_, ?_⟩
      · have hJd : J'' ∈ dstarComp Ω K := by
          rcases Set.mem_insert_iff.mp hJperp with h' | h'
          · exact absurd (by rw [h']; exact mem_twinSet_self hK hf.hz) hnot
          · exact Relation.ReflTransGen.single ⟨hJ''.1, Or.inl
              (omegaNbr_subset_omegaStarNbr_gen hΩ K h')⟩
        obtain ⟨y, hy⟩ := hs.trans K hK J'' hJ''.1
        have hyH : y ∈ sigmaStarNorm Ω K :=
          T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (hy ▸ hJd)
        have hzy : IsUniqueInvolution J'' (y * z * y⁻¹) := hy ▸ hf.hz.conj y
        exact T7A.centralizer_conj_le hyH (hz''.eq hzy) hz_le
      · have s'' := settingR_nonTwin s hJmem hz'' hz''W
        have hcomm : z * z'' = z'' * z := A7Q.Gen.comm_zt hΩ s''.data.frame
        rw [hcomm]
        exact (frame_cent_sigmaStarNormR I s'' hα).1
    · intro L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy hx4 hy4 hxyW
      have s' := settingR_twin s hL hL' hne hR₁ hR₂ hc hx hy hx4 hy4 hxyW
      have hαeq : alphaOf (Subgroup.closure ({x * y, z} : Set Y)) =
          alphaOf (Subgroup.closure ({u, z} : Set Y)) :=
        (hs.alpha_zt s'.data.frame).symm.trans (hs.alpha_zt hf)
      have := (frame_cent_sigmaStarNormR I s' (hαeq.trans hα)).2
      rwa [hstar hL] at this
  have htrans : ∀ M ∈ dstarComp Ω K, ∃ x ∈ sigmaStarNorm Ω K, conjSub x K = M := by
    intro M hM
    obtain ⟨x, hx⟩ := hs.trans K hK M (T3.mem_dstarComp_symm hK hM).1
    exact ⟨x, T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (hx ▸ hM), hx⟩
  exact I.thmE Y R S t₀ h K _ W hK hP ⟨htrans,
    centralizersSylowPairsW_of_stdCentW hΩ hf.hz s.data.hzW hstd⟩

theorem c21_17R (I : TwinDiscInputsR r n) (h : TwinCoreHypR r n Y R S t₀)
    (s : SettingR r n R S t₀ K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥)
    (hP : TwinThmEW.PrintedWT (CoreAssembly.conjClass (tightCore R)) K W) :
    ¬ rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
      sigmaGen (CoreAssembly.conjClass (tightCore R)) K := by
  intro hD
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hs : AlphaSteps Ω := alphaStepsR I.base s
  have htop := sigmaStarNorm_eq_topR I h s hα hP
  have hSig := dComp_eq_dstarComp_of_rLayer_le (partIHypGR s.core) s.data hD
  have hsn : sigmaNorm Ω K = ⊤ := by
    rw [← htop]
    ext g
    exact forall_congr' fun M => by rw [hSig]
  exact s.disc (dConnected_of_sigmaNorm_eq_top s.data.frame.mem
    (fun J hJ => hs.trans K s.data.frame.mem J hJ) hsn)

theorem c21_ER (I : TwinDiscInputsR r n) (h : TwinCoreHypR r n Y R S t₀)
    (s : SettingR r n R S t₀ K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥)
    (hD : ¬ rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
      sigmaGen (CoreAssembly.conjClass (tightCore R)) K)
    (hSigC : ∀ M ∈ dComp (CoreAssembly.conjClass (tightCore R)) K,
      M ≤ Subgroup.centralizer ({t * z} : Set Y))
    (hP : TwinThmEW.PrintedWT (CoreAssembly.conjClass (tightCore R)) K W) : False := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hs : AlphaSteps Ω := alphaStepsR I.base s
  have hf := s.data.frame
  have hK : K ∈ Ω := hf.mem
  have htop := sigmaStarNorm_eq_topR I h s hα hP
  have hstar := eStar_ofR I s hα hD hSigC
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
  have hZ : Subgroup.center Y = ⊥ := center_eq_bot_R s.core
  have hzc : t * z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcent ▸ Subgroup.mem_top g)
  rw [hZ, Subgroup.mem_bot] at hzc
  have h2 : t = z⁻¹ := eq_inv_of_mul_eq_one_left hzc
  have h3 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hf.hz.sq
  exact hf.t_ne_z (h2.trans h3)

theorem false_of_settingR (I : TwinDiscInputsR r n) (h : TwinCoreHypR r n Y R S t₀)
    (s : SettingR r n R S t₀ K K' z u J t W)
    (hP : TwinThmEW.PrintedWT (CoreAssembly.conjClass (tightCore R)) K W) : False := by
  have hα := c21_16R I h s hP
  have hD := c21_17R I h s hα hP
  exact c21_ER I h s hα hD (I.c15 Y R S t₀ h s.disc K K' z u J t W s.data s.huW hα hD) hP

end Steps

end CFSG.CGT.PushingUpLit.SolKNA.R4
