module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

section Base

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem isPGroup_zpowers_of_uniqueInvolution (hz : IsUniqueInvolution K z) : IsPGroup 2 (Subgroup.zpowers z) :=
  CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hz.sq

theorem tq_of_mem_omegaOfSet (s : SettingR r n R S t₀ K K' z u J t W) {M : Subgroup Y}
    (hM : M ∈ omegaOfSet (CoreAssembly.conjClass (tightCore R))
      (twinSet (CoreAssembly.conjClass (tightCore R)) K)) :
    M ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) z := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hf := s.data.frame
  obtain ⟨h2, -, -⟩ := setup_membersR s
  obtain ⟨-, -, R₀, hR₀, hR₀M, hR₀N⟩ := hM.2 K (mem_twinSet_self hf.mem hf.hz)
  have hRs : IsSylow2In R₀ M := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hM.1 hR₀ hR₀M
  have hRz : R₀ ≤ Subgroup.centralizer ({z} : Set Y) :=
    T3.le_centralizer_of_le_normalizer' hf.hz hR₀N
  exact ⟨hM.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hM.1 ⟨R₀, hRs, hRz⟩⟩

theorem mem_omegaOfSet_of_tq_z (s : SettingR r n R S t₀ K K' z u J t W) {M : Subgroup Y}
    (hM : M ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) z)
    (hnot : M ∉ twinSet (CoreAssembly.conjClass (tightCore R)) K) :
    M ∈ omegaOfSet (CoreAssembly.conjClass (tightCore R))
      (twinSet (CoreAssembly.conjClass (tightCore R)) K) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hf := s.data.frame
  have hK : K ∈ Ω := hf.mem
  have hz : IsUniqueInvolution K z := hf.hz
  have hc2 := isPGroup_zpowers_of_uniqueInvolution hz
  obtain ⟨P, hP, hPc⟩ := TwinADescent.exists_sylow_centralizer_of_tq hc2 hM.2
  have hMK : M ≠ K := by
    intro h
    apply hnot
    rw [h]
    exact mem_twinSet_self hK hz
  have h8 : 8 ≤ Nat.card P := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hM.1 hP)
  have hPN : P ≤ Subgroup.normalizer (K : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hM.1 hMK.symm hz hP.1 hP.2.1 (by omega) hPc
  have hnbr : M ∈ omegaNbr Ω K :=
    ⟨hM.1, hMK, P, mem_RSet_of_isSylow2In hM.1 hP, hP.1, hPN⟩
  exact A7Q.Gen.mem_omegaOfSet_of_mem_kPerp hΩ hK (Set.mem_insert_of_mem _ hnbr) hnot

theorem oddCore_comm_of_alpha_zt {t' : Y} (hz : IsUniqueInvolution K z)
    (hα : alphaOf (Subgroup.closure ({z, t'} : Set Y)) = ⊥) :
    ∀ x ∈ oddCoreOf (Subgroup.centralizer ({z} : Set Y)), x * t' = t' * x :=
  T8.oddCoreOf_centralizer_commutes hα (Subgroup.subset_closure (by simp)) hz.ne_one
    (Subgroup.subset_closure (by simp))

theorem conjSub_mem_omegaOfSet_of_cent {Ω : Set (Subgroup Y)} (hΩ : ConjInvariant Ω)
    (hz : IsUniqueInvolution K z) {J₁ : Subgroup Y} (hJ : J₁ ∈ omegaOfSet Ω (twinSet Ω K)) {g : Y}
    (hg : g ∈ Subgroup.centralizer ({z} : Set Y)) :
    conjSub g J₁ ∈ omegaOfSet Ω (twinSet Ω K) := by
  refine ⟨hΩ g J₁ hJ.1, fun L hL => ?_⟩
  have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hL' : conjSub g⁻¹ L ∈ twinSet Ω K := by
    obtain ⟨hLΩ, z', hzK, hzL⟩ := hL
    have hzz : z' = z := hzK.eq hz
    subst hzz
    refine ⟨hΩ g⁻¹ L hLΩ, z', hzK, ?_⟩
    have h1 := hzL.conj g⁻¹
    have e : g⁻¹ * z' * g⁻¹⁻¹ = z' := by
      calc g⁻¹ * z' * g⁻¹⁻¹ = g⁻¹ * (z' * g) := by rw [inv_inv, mul_assoc]
        _ = g⁻¹ * (g * z') := by rw [hgz]
        _ = z' := by group
    rwa [e] at h1
  have h := omegaNbr_conj hΩ (hJ.2 _ hL') g
  rwa [conjSub_conjSub_inv] at h

theorem isUniqueInvolution_conj_of_comm {J₁ : Subgroup Y} {t' o : Y}
    (ht' : IsUniqueInvolution J₁ t') (ho : o * t' = t' * o) :
    IsUniqueInvolution (conjSub o J₁) t' := by
  have h := ht'.conj o
  have e : o * t' * o⁻¹ = t' := by
    calc o * t' * o⁻¹ = (t' * o) * o⁻¹ := by rw [ho]
      _ = t' := by group
  rwa [e] at h

end Base

end CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15
