module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9M
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Tz

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc


section Tz

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem closure_tz_eq (hz2 : z * z = 1) :
    Subgroup.closure ({t * z, z} : Set Y) = Subgroup.closure ({z, t} : Set Y) := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with h | h
    · rw [h]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro x hx
    have h1 : t * z ∈ Subgroup.closure ({t * z, z} : Set Y) := Subgroup.subset_closure (by simp)
    have h2 : z ∈ Subgroup.closure ({t * z, z} : Set Y) := Subgroup.subset_closure (by simp)
    rcases hx with h | h
    · rw [h]
      exact h2
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      have h3 : (t * z) * z⁻¹ ∈ Subgroup.closure ({t * z, z} : Set Y) :=
        Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
      rwa [show (t * z) * z⁻¹ = t by group] at h3

theorem tz_section_connected {n : ℕ} (hT4 : Thm4RTwinBelow 3 n) (hMF : DStarConnectedTwinQ8Below n)
    (s : Setting n R S t₀ K K' z u J t W) {B : Subgroup Y}
    (hB : B ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (t * z)) :
    ∀ M' ∈ secFam (CoreAssembly.conjClass (tightCore R)) (t * z),
      M' ∈ dstarComp (secFam (CoreAssembly.conjClass (tightCore R)) (t * z))
        (secImg (CoreAssembly.conjClass (tightCore R)) (t * z) B) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hf.hz hf.hK'
  obtain ⟨S₀, R₀, R₀', T₀, hR₀, hR₀', hT₀, -, -, -, hRR', hRT, hR'T⟩ :=
    A7Q.Gen.exists_twinSylow hΩ hf.mem hf.hz hf.hK' hf.hne hf.hJ
  have h8R : 8 ≤ Nat.card R₀ := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hf.mem hR₀)
  have h8T : 8 ≤ Nat.card T₀ :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hf.hJ.1 hT₀)
  have hzR : z ∈ R₀ := mem_of_isUniqueInvolution_of_isPGroup hf.hz hR₀.1 hR₀.2.1 (by omega)
  have htT : t ∈ T₀ := mem_of_isUniqueInvolution_of_isPGroup hf.ht hT₀.1 hT₀.2.1 (by omega)
  have hzt : z * t = t * z := hRT z hzR t htT
  have hcsq : (t * z) * (t * z) = 1 := by
    calc (t * z) * (t * z) = t * (z * t) * z := by group
      _ = t * (t * z) * z := by rw [hzt]
      _ = (t * t) * (z * z) := by group
      _ = 1 := by rw [hf.ht.sq, hf.hz.sq, one_mul]
  have hc2 : IsPGroup 2 (Subgroup.zpowers (t * z)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hcsq
  have hcomm : ∀ x : Y, x * t = t * x → x * z = z * x → x * (t * z) = (t * z) * x := by
    intro x hxt hxz
    calc x * (t * z) = (x * t) * z := by group
      _ = (t * x) * z := by rw [hxt]
      _ = t * (x * z) := by group
      _ = t * (z * x) := by rw [hxz]
      _ = (t * z) * x := by group
  have hRc : R₀ ≤ Subgroup.centralizer ({t * z} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      have := hcomm x (hRT x hx t htT) (hf.hz.commute_of_mem (hR₀.1 hx)).symm
      exact this)
  have hR'c : R₀' ≤ Subgroup.centralizer ({t * z} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      have := hcomm x (hR'T x hx t htT) (hK'.commute_of_mem (hR₀'.1 hx)).symm
      exact this)
  have hTc : T₀ ≤ Subgroup.centralizer ({t * z} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      have := hcomm x (hf.ht.commute_of_mem (hT₀.1 hx)).symm (hRT z hzR x hx).symm
      exact this)
  have hKtq : K ∈ tqMembers3 Ω (t * z) :=
    ⟨hf.mem, TwinADescent3.mem_tq_of_sylCent hΩ h2 hf.mem ⟨R₀, hR₀, hRc⟩⟩
  have hK'tq : K' ∈ tqMembers3 Ω (t * z) :=
    ⟨hf.hK'.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hf.hK'.1 ⟨R₀', hR₀', hR'c⟩⟩
  have hJtq : J ∈ tqMembers3 Ω (t * z) :=
    ⟨hf.hJ.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hf.hJ.1 ⟨T₀, hT₀, hTc⟩⟩
  have hJK : J ≠ K := (hf.hJ.2 K (mem_twinSet_self hf.mem hf.hz)).2.1
  have hJK' : J ≠ K' := (hf.hJ.2 K' hf.hK').2.1
  have hTz : T₀ ≤ Subgroup.centralizer ({z} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hRT z hzR x hx).symm
  have hTK : T₀ ≤ Subgroup.normalizer (K : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hf.mem hf.hJ.1 hJK.symm hf.hz hT₀.1 hT₀.2.1
      (by omega) hTz
  have hTK' : T₀ ≤ Subgroup.normalizer (K' : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hf.hK'.1 hf.hJ.1 hJK'.symm hK' hT₀.1 hT₀.2.1
      (by omega) hTz
  have htt : TwinTriple (secFam Ω (t * z)) :=
    twinTriple_secFam hΩ hc2 hKtq hK'tq hJtq hf.hz hf.hK' hR₀ hR₀' hT₀ hRc hR'c hTc hRR' hRT hR'T
      hTK hTK'
  have htz1 : t * z ≠ 1 := by
    intro e
    apply hf.t_ne_z
    have h2' : t = z⁻¹ := eq_inv_of_mul_eq_one_left e
    rw [h2']; exact inv_eq_of_mul_eq_one_right hf.hz.sq
  have hlt : Nat.card (↥(coreHull Ω (t * z)) ⧸
      classicalInvolutionOddCore ↥(coreHull Ω (t * z))) < n :=
    s.core.card ▸ card_secQuot_lt (not_mem_center_of_ne_one s htz1)
  rcases dichotomy_secFam hT4 hlt hΩ hc2 h2 hq hA hB with hconn | horb
  · exact hconn
  · have htrans : ∀ K₁ ∈ secFam Ω (t * z), ∀ L ∈ secFam Ω (t * z),
        ∃ g : ↥(coreHull Ω (t * z)) ⧸ classicalInvolutionOddCore ↥(coreHull Ω (t * z)),
          conjSub g K₁ = L := by
      intro K₁ hK₁ L hL
      obtain ⟨y₁, hy₁⟩ := horb K₁ hK₁
      obtain ⟨y₂, hy₂⟩ := horb L hL
      exact ⟨y₂ * y₁⁻¹, by rw [conjSub_mul, ← hy₁, conjSub_inv_conjSub, hy₂]⟩
    have hgen : omegaGen (secFam Ω (t * z)) = ⊤ :=
      omegaGen_quotFamily_eq_top _ _
        (omegaGen_restrictFamily_eq_top (cFam Ω (t * z)) (coreHull Ω (t * z)) rfl)
    have hD := hMF _ hlt (secFam Ω (t * z)) (hypOmegaGen_secFam hΩ hc2) (secFam_twoGroup h2)
      (secFam_q8 hc2 hq) oddCore_quot_eq_bot (secFam_aEmpty hΩ hA hc2) hgen htrans htt
    intro M' hM'
    exact hD _ (secImg_mem_secFam hB) M' hM'

theorem disc13N_of_thm4 (I : TwinDiscBase n) (hT4 : Thm4RTwinBelow 3 n)
    (hMF : DStarConnectedTwinQ8Below n) : Disc13N n := by
  intro Y _ _ R S t₀ K K' z u J t W s c' hc'
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hs := alphaStepsBase I s
  have hP : Q3CL.PartIHypG Ω := TwinPerp.partIHypG s.core
  have hΩ : HypOmegaGen Ω := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hzt : z * t = t * z := comm_zt hΩ hf
  have hcsq : (t * z) * (t * z) = 1 := by
    calc (t * z) * (t * z) = t * (z * t) * z := by group
      _ = t * (t * z) * z := by rw [hzt]
      _ = (t * t) * (z * z) := by group
      _ = 1 := by rw [hf.ht.sq, hf.hz.sq, one_mul]
  have hc2 : IsPGroup 2 (Subgroup.zpowers (t * z)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hcsq
  have htz1 : t * z ≠ 1 := by
    intro e
    apply hf.t_ne_z
    have h2' : t = z⁻¹ := eq_inv_of_mul_eq_one_left e
    rw [h2']; exact inv_eq_of_mul_eq_one_right hf.hz.sq
  have hKtq : K ∈ tqMembers3 Ω (t * z) :=
    ⟨hf.mem, TwinADescent3.mem_tq_of_sylCent hΩ h2 hf.mem (mem_sylCent_tz_K' hΩ hf).2⟩
  have hconn := tz_section_connected hT4 hMF s hKtq
  have h1 : conjSub c' K ∈ tqMembers3 Ω (t * z) :=
    conjSub_mem_tqMembers3 hΩ.conjInvariant hc' hKtq
  obtain ⟨m, hm, J', -, hJ'd, hMeq⟩ := exists_conj_tq_of_connected hΩ hc2 hKtq hconn _ h1
  have hcz : (t * z) * z = z * (t * z) := by
    calc (t * z) * z = (z * t) * z := by rw [hzt]
      _ = z * (t * z) := by group
  have hmα : m ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) := by
    have h3 := oddCoreOf_centralizer_le_normalizer_alphaOf (c := t * z) (z := z) hf.hz.sq htz1 hcz hm
    rwa [closure_tz_eq hf.hz.sq, hs.alpha_zt hf] at h3
  have hNK : Subgroup.normalizer (K : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) := fun g hg =>
    hs.centralizer_le hf
      (T7A.mem_centralizer_of_conj_eq (hf.hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp hg)))
  obtain ⟨x, hxN, hx⟩ : ∃ x ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y), conjSub x K = J' := by
    by_cases hne : dComp Ω K = dstarComp Ω K
    · exact hs.exists_mem_normalizer hf (hne ▸ hJ'd)
    · exact exists_mem_conj_of_dstarComp hP s.data hne (mGrp_le_normalizer_alpha hP hs s.data) hNK
        J' hJ'd
  have hc'eq : conjSub c' K = conjSub (m * x) K := by rw [hMeq, ← hx, conjSub_mul]
  have hmm : conjSub ((m * x)⁻¹ * c') K = K := by
    rw [conjSub_mul, hc'eq, conjSub_inv_conjSub]
  have hmN : (m * x)⁻¹ * c' ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) :=
    hNK (mem_normalizer_iff_conjSub_eq.mpr hmm)
  have e : c' = (m * x) * ((m * x)⁻¹ * c') := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmα hxN) hmN

end Tz

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
