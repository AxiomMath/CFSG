module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf3Out
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecEdge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtxSecFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open scoped commutatorElement

section Nbr

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t₀ : G} {n : ℕ}

theorem nbr_cm (h : TwinCoreHyp n G R S t₀) (hRc : tightCore R = R)
    {N J : Subgroup G} {z t : G} (hN : N ∈ CoreAssembly.conjClass (tightCore R))
    (hz : IsUniqueInvolution N z)
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) N) (ht : IsUniqueInvolution J t)
    (htz : t ≠ z) (hzt : z * t = t * z) {c : G} (hc : c = t ∨ c = z * t) :
    c ∈ centralizerModOdd ⊤ N ∧ c * c = 1 ∧ c ≠ 1 := by
  obtain ⟨SK, hK⟩ := exists_datum_at h hRc hN hz
  have hRcK : tightCore N = N := tightCore_eq_of_mem hRc hN
  have hJe : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore N)) (tightCore N) := by
    rw [hRcK, conjClass_eq_of_mem hN]
    exact hJ
  obtain ⟨ht2, -, htm⟩ := edge_involution hK.datum hRcK hK.hyp hJe ht htz
  have hzm : z ∈ centralizerModOdd ⊤ N :=
    mem_centralizerModOdd_of_commutator hz.sq fun r hr => by
      have : r * z = z * r := Subgroup.mem_centralizer_singleton_iff.mp (hK.datum.cent hr)
      have h1 : ⁅z, r⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact this.symm
      rw [h1]
      exact Subgroup.one_mem _
  refine ⟨?_, ?_, ?_⟩
  · rcases hc with rfl | rfl
    · exact htm
    · exact Subgroup.mul_mem _ hzm htm
  · rcases hc with rfl | rfl
    · exact ht2
    · calc z * t * (z * t) = z * (t * z) * t := by group
        _ = z * (z * t) * t := by rw [← hzt]
        _ = (z * z) * (t * t) := by group
        _ = 1 := by rw [hz.sq, ht2, one_mul]
  · rcases hc with rfl | rfl
    · exact ht.ne_one
    · intro e
      have h1 : t = z⁻¹ := eq_inv_of_mul_eq_one_right e
      rw [inv_eq_of_mul_eq_one_right hz.sq] at h1
      exact htz h1

theorem nbr_cent_gen3 (hSp : ModelFactSp62) (hD4 : ModelFactD42) (h4 : Thm4RTwinBelow 3 n)
    (h : TwinCoreHyp n G R S t₀) (hRc : tightCore R = R) (hZ : Subgroup.center G = ⊥)
    {M M'' J : Subgroup G} {z t : G} (hM : M ∈ CoreAssembly.conjClass (tightCore R))
    (hz : IsUniqueInvolution M z)
    (hM'' : M'' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) M) (hne : M'' ≠ M)
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M)
    (hJ'' : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M'')
    (ht : IsUniqueInvolution J t) (htz : t ≠ z) (hzt : z * t = t * z) {c : G}
    (hc : c = t ∨ c = z * t) (hzc : z ∈ Subgroup.centralizer ({c} : Set G)) :
    Quiet c z hzc ∨ LiftedAt M c z ∨ (ExitAt M c z hzc ∧ MovedOddFreeAt c z hzc) := by
  obtain ⟨SK, hK⟩ := exists_datum_at h hRc hM hz
  have hRcK : tightCore M = M := tightCore_eq_of_mem hRc hM
  have hz'' : IsUniqueInvolution M'' z := isUniqueInvolution_of_mem_twinSet hz hM''
  have hM''Ω : M'' ∈ CoreAssembly.conjClass (tightCore R) := hM''.1
  obtain ⟨hcm, hc2, hc1⟩ := nbr_cm h hRc hM hz hJ ht htz hzt hc
  obtain ⟨hcm'', -, -⟩ := nbr_cm h hRc hM''Ω hz'' hJ'' ht htz hzt hc
  have hcK'' : c ∈ Balance.Bootstrap.trivialOnQuot M'' := ⟨hcm''.2.1, fun x hx => hcm''.2.2.2 x hx⟩
  have hM''tw : M'' ∈ twinSet (CoreAssembly.conjClass (tightCore M)) (tightCore M) := by
    rw [hRcK, conjClass_eq_of_mem hM]
    exact hM''
  have hne' : M'' ≠ tightCore M := by rw [hRcK]; exact hne
  exact quietLiftedExit_of_twin hSp hD4 h4 hK hRcK hZ hc2 hc1 hcm hzc hM''tw hne' hcK''

theorem nbr_out3 (hSp : ModelFactSp62) (hD4 : ModelFactD42) (h4 : Thm4RTwinBelow 3 n)
    {K K' J : Subgroup G} {z u t : G} (h : TwinCoreHyp n G R S t₀) (hRc : tightCore R = R)
    (hZ : Subgroup.center G = ⊥)
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t) {c : G}
    (hc : c = t ∨ c = z * t) (hzc : z ∈ Subgroup.centralizer ({c} : Set G)) :
    Quiet c z hzc ∨ (LiftedAt K c z ∧ LiftedAt K' c z) ∨
      (ExitAt K c z hzc ∧ MovedOddFreeAt c z hzc) ∨
      (ExitAt K' c z hzc ∧ MovedOddFreeAt c z hzc) := by
  have hzt : z * t = t * z := A7Q.Gen.comm_zt h.hyp hf
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hf.hz hf.hK'
  have hJK := hf.hJ.2 K (mem_twinSet_self hf.mem hf.hz)
  have hJK' := hf.hJ.2 K' hf.hK'
  have hKK' : K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K' := ⟨hf.mem, z, hzK', hf.hz⟩
  have h2 := nbr_cent_gen3 hSp hD4 h4 h hRc hZ hf.mem hf.hz hf.hK' hf.hne hJK hJK'
    hf.ht hf.t_ne_z hzt hc hzc
  have h4' := nbr_cent_gen3 hSp hD4 h4 h hRc hZ hf.hK'.1 hzK' hKK' (Ne.symm hf.hne) hJK' hJK
    hf.ht hf.t_ne_z hzt hc hzc
  rcases h2 with q | l | e
  · exact Or.inl q
  · rcases h4' with q | l' | e'
    · exact Or.inl q
    · exact Or.inr (Or.inl ⟨l, l'⟩)
    · exact Or.inr (Or.inr (Or.inr e'))
  · exact Or.inr (Or.inr (Or.inl e))

end Nbr

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf3
