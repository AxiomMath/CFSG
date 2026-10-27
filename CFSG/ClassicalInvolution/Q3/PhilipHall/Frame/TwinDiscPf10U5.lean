module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10U2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10U3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc


section Mem

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem mem_dComp_of_le_centralizer_z (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    {K : Subgroup G} {z : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hY : coreLayer Ω c ≤ Subgroup.centralizer ({z} : Set G)) :
    ∀ M ∈ SylCent Ω c, M ∈ dComp Ω K := by
  rintro J ⟨hJΩ, R, hR, hRc⟩
  have hJ : J ∈ tqMembers3 Ω c := ⟨hJΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJΩ ⟨R, hR, hRc⟩⟩
  have hRK : R ≤ TwinADescent.coreAt c J :=
    ((TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mpr ⟨hR, hRc⟩).1
  have hRz : R ≤ Subgroup.centralizer ({z} : Set G) := hRK.trans ((coreAt_le_coreLayer hJ).trans hY)
  by_cases hJK : J = K
  · rw [hJK]
    exact Relation.ReflTransGen.refl
  · have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ hR
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
    have hRN : R ≤ Subgroup.normalizer (K : Set G) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hJΩ (Ne.symm hJK) hz hR.1 hR.2.1
        (by omega) hRz
    exact T7A.mem_dComp_of_mem_omegaNbr ⟨hJΩ, hJK, R, hRset, hR.1, hRN⟩

theorem mem_dComp_of_le_centralizer_w (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) {K : Subgroup G} {w : G}
    (heq : dComp Ω K = dstarComp Ω K) (hTq : ∀ M ∈ SylCent Ω w, M ∈ dstarComp Ω K)
    (hY : coreLayer Ω c ≤ Subgroup.centralizer ({w} : Set G)) :
    ∀ M ∈ SylCent Ω c, M ∈ dComp Ω K := by
  rintro J ⟨hJΩ, R, hR, hRc⟩
  have hJ : J ∈ tqMembers3 Ω c := ⟨hJΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJΩ ⟨R, hR, hRc⟩⟩
  have hRK : R ≤ TwinADescent.coreAt c J :=
    ((TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mpr ⟨hR, hRc⟩).1
  have hRw : R ≤ Subgroup.centralizer ({w} : Set G) := hRK.trans ((coreAt_le_coreLayer hJ).trans hY)
  rw [heq]
  exact hTq J ⟨hJΩ, R, hR, hRw⟩

end Mem

section Conn

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem mem_dComp_of_conn (s : Setting n R S t₀ K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥)
    (heq : dComp (CoreAssembly.conjClass (tightCore R)) K =
      dstarComp (CoreAssembly.conjClass (tightCore R)) K)
    (hconnU : SecConnU (CoreAssembly.conjClass (tightCore R)) u) :
    ∀ M ∈ SylCent (CoreAssembly.conjClass (tightCore R)) u,
      M ∈ dComp (CoreAssembly.conjClass (tightCore R)) K := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  obtain ⟨g₀, -, hJ₀nbr, hJ₀⟩ := exists_sylCent_u hΩ hf
  have hJ₀tq : conjSub g₀ J ∈ tqMembers3 Ω u :=
    ⟨hJ₀.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₀.1 hJ₀.2⟩
  have hJ₀d : conjSub g₀ J ∈ dComp Ω K :=
    T7A.mem_dComp_of_mem_omegaNbr (hJ₀nbr.2 K (mem_twinSet_self hf.mem hf.hz))
  have hJ₀ds : conjSub g₀ J ∈ dstarComp Ω K := mem_dstarComp_of_mem_dComp_gen hΩ hJ₀d
  intro M hM'
  have hMtq : M ∈ tqMembers3 Ω u :=
    ⟨hM'.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hM'.1 hM'.2⟩
  obtain ⟨m, hm, J', -, hJ'd, hMeq⟩ := exists_conj_tq_of_connected hΩ hc2 hJ₀tq
    (fun M' hM'' => hconnU _ (secImg_mem_secFam hJ₀tq) M' hM'') M hMtq
  have hmz : m * z = z * m :=
    oddCore_comm_of_alpha hα (Subgroup.subset_closure (by simp)) hf.hu1
      (Subgroup.subset_closure (by simp)) hm
  have hmσ : m ∈ sigmaStarNorm Ω K :=
    centralizer_le_sigmaStarNorm_z hΩ hf.mem hf.hz (Subgroup.mem_centralizer_singleton_iff.mpr hmz)
  have hJ'ds : J' ∈ dstarComp Ω K := by
    rw [T7A.dstarComp_eq_of_mem hf.mem hJ₀ds] at hJ'd
    exact hJ'd
  rw [heq, hMeq]
  exact ((mem_sigmaStarNorm_iff.mp hmσ) J').mp hJ'ds

theorem disc14AltExc_of_zt (I : TwinDiscBase n) (hT4 : Thm4RTwinBelow 3 n) (hZT : DiscZT n)
    (hN : DiscNormCent n) (hTq : DiscTqTz n) : Disc14AltExc n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα hexc
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hs := alphaStepsBase I s
  have hP : Q3CL.PartIHypG Ω := TwinPerp.partIHypG s.core
  have hΩ : HypOmegaGen Ω := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  have hNK : dComp Ω K ≠ dstarComp Ω K →
      Subgroup.normalizer (K : Set Y) ≤ Subgroup.centralizer ({t * z} : Set Y) := fun hne =>
    hN Y R S t₀ K K' z u J t W s hα (not_rLayer_le_sigmaGen hP s.data hne)
  have htr : dComp Ω K ≠ dstarComp Ω K →
      ∀ L ∈ dstarComp Ω K, ∃ x ∈ Subgroup.centralizer ({t * z} : Set Y), conjSub x K = L := by
    intro hne
    exact exists_mem_conj_of_dstarComp hP s.data hne
      ((mGrp_le_rLayer_tz hP s.data hne).trans (rLayer_le_centralizer Ω (t * z))) (hNK hne)
  by_cases hconn : SecConnU Ω u
  · have hne : dComp Ω K ≠ dstarComp Ω K := fun heq => hexc (mem_dComp_of_conn s hα heq hconn)
    exact centralizer_u_le_of_conn s hconn (fun m hm =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (oddCore_centralizer_u_comm_tz hs hf hα hm)) (hNK hne) (htr hne)
  · rcases hZT Y R S t₀ K K' z u J t W s hconn with hzt | htz
    · exact absurd (mem_dComp_of_le_centralizer_z hΩ hc2 h2 hf.mem hf.hz
        (coreLayer_le_centralizer_of_trivial hs hf hc2 hα (Or.inl rfl) hzt)) hexc
    · have hY : coreLayer Ω u ≤ Subgroup.centralizer ({t * z} : Set Y) :=
        coreLayer_le_centralizer_of_trivial hs hf hc2 hα (Or.inr rfl) htz
      by_cases heq : dComp Ω K = dstarComp Ω K
      · exact absurd (mem_dComp_of_le_centralizer_w hΩ hc2 h2 heq
          (hTq Y R S t₀ K K' z u J t W s hα) hY) hexc
      · refine centralizer_u_le_of_disc hT4 s hconn hY fun J₀ hJ₀ m hm => ?_
        obtain ⟨x₀, hx₀H, hx₀⟩ := htr heq J₀ (mem_dstarComp_of_mem_dComp_gen hΩ hJ₀)
        have hmK : x₀⁻¹ * m * x₀ ∈ Subgroup.normalizer (K : Set Y) := by
          rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, conjSub_mul, hx₀,
            mem_normalizer_iff_conjSub_eq.mp hm, ← hx₀, conjSub_inv_conjSub]
        have e : m = x₀ * (x₀⁻¹ * m * x₀) * x₀⁻¹ := by group
        rw [e]
        exact (Subgroup.centralizer ({t * z} : Set Y)).mul_mem
          ((Subgroup.centralizer ({t * z} : Set Y)).mul_mem hx₀H (hNK heq hmK))
          ((Subgroup.centralizer ({t * z} : Set Y)).inv_mem hx₀H)

end Conn

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
