module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConn
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscEnd

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc


@[expose] def NormCentR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    SettingR r n R S t₀ K K' z u J t W →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        ¬ rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
            sigmaGen (CoreAssembly.conjClass (tightCore R)) K →
          Subgroup.normalizer (K : Set Y) ≤ Subgroup.centralizer ({t * z} : Set Y)

theorem disc15R_of_normCent {r n : ℕ} (hT : DiscTqTzR r n) (hN : NormCentR r n) : Disc15R r n := by
  intro Y _ _ R S t₀ h hdisc K K' z u J t W d huW hα hD M hM
  have s : SettingR r n R S t₀ K K' z u J t W := ⟨h.toStd, hdisc, d, huW⟩
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hP : Q3CL.PartIHypG Ω := partIHypGR s.core
  have hΩ : HypOmegaGen Ω := hP.hyp
  have hne : dComp Ω K ≠ dstarComp Ω K := fun heq =>
    hD (rLayer_tz_le_sigmaGen_of_eqR hT s hα heq)
  have hNK := hN Y R S t₀ K K' z u J t W s hα hD
  have hMW : MGrp Ω W ≤ Subgroup.centralizer ({t * z} : Set Y) :=
    (mGrp_le_rLayer_tz hP s.data hne).trans (rLayer_le_centralizer Ω (t * z))
  have hMd : M ∈ dstarComp Ω K := mem_dstarComp_of_mem_dComp_gen hΩ hM
  obtain ⟨x, hx, rfl⟩ := exists_mem_conj_of_dstarComp hP s.data hne hMW hNK M hMd
  have hKc : K ≤ Subgroup.centralizer ({t * z} : Set Y) := le_trans Subgroup.le_normalizer hNK
  intro y hy
  rw [mem_conjSub_iff] at hy
  have hy' := hKc hy
  have hyx : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
  rw [hyx]
  exact (Subgroup.centralizer ({t * z} : Set Y)).mul_mem
    ((Subgroup.centralizer ({t * z} : Set Y)).mul_mem hx hy')
    ((Subgroup.centralizer ({t * z} : Set Y)).inv_mem hx)

theorem normalizer_le_centralizer_tz_of_conj {Y : Type} [Group Y] {K : Subgroup Y} {z t : Y}
    (hz : IsUniqueInvolution K z) (h : ∀ n ∈ Subgroup.normalizer (K : Set Y), n * t * n⁻¹ = t) :
    Subgroup.normalizer (K : Set Y) ≤ Subgroup.centralizer ({t * z} : Set Y) := by
  intro n hn
  have hnK : conjSub n K = K := mem_normalizer_iff_conjSub_eq.mp hn
  have hnz : n * z = z * n := commute_involution_of_conjSub_eq hz hnK
  have hnt : n * t = t * n := mul_inv_eq_iff_eq_mul.mp (h n hn)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * (t * z) = (n * t) * z := by rw [mul_assoc]
    _ = (t * n) * z := by rw [hnt]
    _ = t * (n * z) := by rw [mul_assoc]
    _ = t * (z * n) := by rw [hnz]
    _ = (t * z) * n := by rw [mul_assoc]

end CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15
