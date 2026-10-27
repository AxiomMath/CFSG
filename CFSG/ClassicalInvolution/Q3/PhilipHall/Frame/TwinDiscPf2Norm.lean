module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf2Final

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinDisc



@[expose] def DiscNormCent (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        ¬ rLayer (CoreAssembly.conjClass (tightCore R)) (t * z) ≤
            sigmaGen (CoreAssembly.conjClass (tightCore R)) K →
          Subgroup.normalizer (K : Set Y) ≤ Subgroup.centralizer ({t * z} : Set Y)

theorem disc15_of_normCent {n : ℕ} (hN : DiscNormCent n) (hT : DiscTqTz n) : Disc15 n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα hD M hM
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hP : Q3CL.PartIHypG Ω := TwinPerp.partIHypG s.core
  have hΩ : HypOmegaGen Ω := hP.hyp
  have hne : dComp Ω K ≠ dstarComp Ω K := fun heq =>
    hD (Pf2.rLayer_tz_le_sigmaGen_of_eq hT s hα heq)
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

namespace Pf2

structure TwinDiscInputsPf3 (n : ℕ) : Prop where
  thmE : TwinThmE n
  base : TwinDiscBase n
  c13Exc : Disc13NExc n
  c14Exc : Disc14NExc n
  c14AltExc : Disc14AltExc n
  normCent : DiscNormCent n
  tqTz : DiscTqTz n
  tqU : DiscTqU n

theorem TwinDiscInputsPf3.toPf2 {n : ℕ} (I : TwinDiscInputsPf3 n) : TwinDiscInputsPf2 n where
  thmE := I.thmE
  base := I.base
  c13Exc := I.c13Exc
  c14Exc := I.c14Exc
  c14AltExc := I.c14AltExc
  c15 := disc15_of_normCent I.normCent I.tqTz
  tqTz := I.tqTz
  tqU := I.tqU

end Pf2

end TwinDisc


theorem twinCoreDiscPerp_of_inputsPf3 {n : ℕ} (I : TwinDisc.Pf2.TwinDiscInputsPf3 n) :
    TwinCoreDiscPerp n :=
  twinCoreDiscPerp_of_inputsPf2 I.toPf2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
