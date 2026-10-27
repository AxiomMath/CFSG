module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscClaims
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscThmE
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinFusion
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf2Wyl

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame


structure TwinDiscInputsR (r n : ℕ) : Prop where
  thmE : TwinThmER r n
  base : TwinDiscBaseR r n
  c13N : Disc13NR r n
  c14N : Disc14NR r n
  c15 : Disc15R r n
  tqTz : DiscTqTzR r n
  tqU : DiscTqUR r n

section Frames

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem settingR_nonTwin (s : SettingR r n R S t₀ K K' z u J t W) {J'' : Subgroup Y} {z'' : Y}
    (hJ'' : J'' ∈ omegaOfSet (CoreAssembly.conjClass (tightCore R)) (twinSet (CoreAssembly.conjClass (tightCore R)) K))
    (hz'' : IsUniqueInvolution J'' z'') (hz''W : z'' ∈ W) : SettingR r n R S t₀ K K' z u J'' z'' W := by
  have hf := s.data.frame
  have hΩ := s.core.hyp
  refine ⟨s.core, s.disc, ⟨{ hf with hJ := hJ'', ht := hz'', htu := ?_ }, s.data.hW, s.data.hzW,
    hz''W⟩, s.huW⟩
  exact wSet_comm hΩ s.data.hW z'' hz''W u s.huW

theorem settingR_twin (s : SettingR r n R S t₀ K K' z u J t W) {L L' R₁ R₂ : Subgroup Y}
    (hL : L ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K)
    (hL' : L' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) (hne : L' ≠ L)
    (hR₁ : IsSylow2In R₁ L) (hR₂ : IsSylow2In R₂ L') (hc : Commutes R₁ R₂) {x y : Y}
    (hx : x ∈ R₁) (hy : y ∈ R₂) (hx4 : orderOf x = 4) (hy4 : orderOf y = 4) (hxyW : x * y ∈ W) :
    SettingR r n R S t₀ L L' z (x * y) J t W := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hzL : IsUniqueInvolution L z := isUniqueInvolution_of_mem_twinSet hf.hz hL
  have hzL' : IsUniqueInvolution L' z := isUniqueInvolution_of_mem_twinSet hf.hz hL'
  have htwL : twinSet Ω L = twinSet Ω K := twinSet_eq_of_mem_twinSet hf.hz hL
  have hL'L : L' ∈ twinSet Ω L := by rw [htwL]; exact hL'
  have hJL : J ∈ omegaOfSet Ω (twinSet Ω L) := by rw [htwL]; exact hf.hJ
  have hxL : x ∈ L := hR₁.1 hx
  have hyL' : y ∈ L' := hR₂.1 hy
  have hxx : x * x = z := T7A.sq_eq_of_orderOf_four hzL hxL hx4
  have hyy : y * y = z := T7A.sq_eq_of_orderOf_four hzL' hyL' hy4
  have hcxy : x * y = y * x := hc x hx y hy
  have hxyxy : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hcxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hxx, hyy, hzL.sq]
  have hxL' : x ∉ L' := fun h => hne (eq_of_mem_inf_of_four_dvd hΩ hL.1 hL'.1 hxL h
    (by rw [hx4])).symm
  have hu1 : x * y ≠ 1 := by
    intro h
    apply hxL'
    have : x = y⁻¹ := by rw [eq_inv_iff_mul_eq_one]; exact h
    rw [this]
    exact L'.inv_mem hyL'
  have huz : x * y ≠ z := by
    intro h
    apply hxL'
    have : x = z * y⁻¹ := by rw [← h]; group
    rw [this]
    exact L'.mul_mem hzL'.mem (L'.inv_mem hyL')
  have hfr : TwinFrameData Ω L L' z (x * y) J t :=
    { mem := hL.1
      hz := hzL
      hK' := hL'L
      hne := hne
      hu := Subgroup.mul_mem _ (Subgroup.mem_sup_left hxL) (Subgroup.mem_sup_right hyL')
      hu2 := hxyxy
      hu1 := hu1
      huz := huz
      hJ := hJL
      ht := hf.ht
      htu := wSet_comm hΩ s.data.hW t s.data.htW (x * y) hxyW }
  exact ⟨s.core, s.disc, ⟨hfr, s.data.hW, s.data.hzW, s.data.htW⟩, hxyW⟩

end Frames

section Alpha

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem stdCentW_normalizer_alpha (I : TwinDiscInputsR r n)
    (s : SettingR r n R S t₀ K K' z u J t W) :
    StdCentW (CoreAssembly.conjClass (tightCore R)) K W
      (Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y)) z := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hs : AlphaSteps Ω := alphaStepsR I.base s
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hK : K ∈ Ω := hf.mem
  have hz_le := hs.centralizer_le hf
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
    · obtain ⟨y, hyN, hy⟩ := hs.exists_mem_normalizer hf (T7A.mem_dComp_of_mem_kPerp hJperp)
      have hzy : IsUniqueInvolution J'' (y * z * y⁻¹) := hy ▸ hf.hz.conj y
      exact T7A.centralizer_conj_le hyN (hz''.eq hzy) hz_le
    · have s'' := settingR_nonTwin s hJmem hz'' hz''W
      have h13 := I.c13N Y R S t₀ K K' z u J'' z'' W s''
      have hcomm : z * z'' = z'' * z := A7Q.Gen.comm_zt hΩ s''.data.frame
      rw [hcomm]
      exact h13
  · intro L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy hx4 hy4 hxyW
    have s' := settingR_twin s hL hL' hne hR₁ hR₂ hc hx hy hx4 hy4 hxyW
    have h14 := I.c14N Y R S t₀ L L' z (x * y) J t W s'
    have hαeq : alphaOf (Subgroup.closure ({x * y, z} : Set Y)) =
        alphaOf (Subgroup.closure ({u, z} : Set Y)) :=
      (hs.alpha_zt s'.data.frame).symm.trans (hs.alpha_zt hf)
    rw [hαeq] at h14
    exact h14

theorem c21_16R (I : TwinDiscInputsR r n) (h : TwinCoreHypR r n Y R S t₀)
    (s : SettingR r n R S t₀ K K' z u J t W)
    (hP : TwinThmEW.PrintedWT (CoreAssembly.conjClass (tightCore R)) K W) :
    alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  by_contra hα
  have hs : AlphaSteps Ω := alphaStepsR I.base s
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hstd := stdCentW_normalizer_alpha I s
  have hD : rLayer Ω (t * z) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) :=
    (rLayer_le_centralizer Ω (t * z)).trans (I.c13N Y R S t₀ K K' z u J t W s)
  have htrans : ∀ M ∈ dstarComp Ω K, ∃ x ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y), conjSub x K = M := by
    by_cases heq : dComp Ω K = dstarComp Ω K
    · intro M hM
      rw [← heq] at hM
      exact hs.exists_mem_normalizer hf hM
    · have hP' : Q3CL.PartIHypG Ω := partIHypGR s.core
      refine exists_mem_conj_of_dstarComp hP' s.data heq
        ((mGrp_le_rLayer_tz hP' s.data heq).trans hD) ?_
      intro g hg
      refine mem_normalizer_alpha_of_mem_dComp hΩ hs.trans hs.hyp51 hf ?_
      rw [mem_normalizer_iff_conjSub_eq.mp hg]
      exact Relation.ReflTransGen.refl
  have htop := I.thmE Y R S t₀ h K _ W hf.mem hP ⟨htrans,
    centralizersSylowPairsW_of_stdCentW hΩ hf.hz s.data.hzW hstd⟩
  have hnormal : (alphaOf (Subgroup.closure ({u, z} : Set Y))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp htop
  have hodd := (hs.alpha_eq hf).1
  have hle : alphaOf (Subgroup.closure ({u, z} : Set Y)) ≤ classicalInvolutionOddCore Y :=
    le_sSup ⟨hnormal, hodd⟩
  have hbot : classicalInvolutionOddCore Y = ⊥ := s.core.oddFree
  exact hα (le_bot_iff.mp (hbot ▸ hle))

end Alpha


end CFSG.CGT.PushingUpLit.SolKNA.R4
