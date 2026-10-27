module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Conn
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9M

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc

section U

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

@[expose] def SecConnU (Ω : Set (Subgroup Y)) (u : Y) : Prop := T3.DStarConnected (secFam Ω u)

theorem u_comm_z (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t) : u * z = z * u := by
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hf.hz hf.hK'
  have hle : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set Y) :=
    sup_le (le_centralizer_of_unique hf.hz) (le_centralizer_of_unique hzK')
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hf.hu)

theorem disc14N_of_conn (I : TwinDiscBase n) (s : Setting n R S t₀ K K' z u J t W)
    (hconnU : SecConnU (CoreAssembly.conjClass (tightCore R)) u) :
    Subgroup.centralizer ({u} : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) := by
  intro c' hc'
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hs := alphaStepsBase I s
  have hP : Q3CL.PartIHypG Ω := TwinPerp.partIHypG s.core
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
  have h1 : conjSub c' (conjSub g₀ J) ∈ tqMembers3 Ω u :=
    conjSub_mem_tqMembers3 hΩ.conjInvariant hc' hJ₀tq
  obtain ⟨m, hm, J', -, hJ'd, hMeq⟩ := exists_conj_tq_of_connected hΩ hc2 hJ₀tq
    (fun M hM => hconnU _ (secImg_mem_secFam hJ₀tq) M hM) _ h1
  have hmα : m ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) :=
    oddCoreOf_centralizer_le_normalizer_alphaOf (c := u) (z := z) hf.hz.sq hf.hu1
      (u_comm_z hΩ hf) hm
  have hJ'ds : J' ∈ dstarComp Ω K := by
    rw [T7A.dstarComp_eq_of_mem hf.mem hJ₀ds] at hJ'd
    exact hJ'd
  have hNK : Subgroup.normalizer (K : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) := fun g hg =>
    hs.centralizer_le hf
      (T7A.mem_centralizer_of_conj_eq (hf.hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp hg)))
  obtain ⟨x, hxN, hx⟩ : ∃ x ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y), conjSub x K = J' := by
    by_cases hne : dComp Ω K = dstarComp Ω K
    · have hJ'dd : J' ∈ dComp Ω K := by rw [hne]; exact hJ'ds
      exact hs.exists_mem_normalizer hf hJ'dd
    · exact exists_mem_conj_of_dstarComp hP s.data hne (mGrp_le_normalizer_alpha hP hs s.data) hNK
        J' hJ'ds
  obtain ⟨x₀, hx₀N, hx₀⟩ := hs.exists_mem_normalizer hf hJ₀d
  have hc'eq : conjSub (c' * x₀) K = conjSub (m * x) K := by
    rw [conjSub_mul, hx₀, hMeq, ← hx, conjSub_mul]
  have hmm : conjSub ((m * x)⁻¹ * (c' * x₀)) K = K := by
    rw [conjSub_mul, hc'eq, conjSub_inv_conjSub]
  have hmN : (m * x)⁻¹ * (c' * x₀) ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) :=
    hNK (mem_normalizer_iff_conjSub_eq.mpr hmm)
  have e : c' = ((m * x) * ((m * x)⁻¹ * (c' * x₀))) * x₀⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hmα hxN) hmN)
    (Subgroup.inv_mem _ hx₀N)

end U

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
