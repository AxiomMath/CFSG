module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRMat
import CFSG.LocalAnalysis.GLTheoremA.CatA.FRLift
import CFSG.GroupTheory.PLayer.CentralQuotient
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Component
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.MI
open scoped commutatorElement

section Lift


theorem t263_layer_ne_bot_of_simple_fixed {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} (hSp : GLAPPrimeCore p ↥S = ⊥) {b : Ω} (hb : b ∈ Subgroup.normalizer (S : Set Ω))
    (hbp : b ^ p = 1) {D : Subgroup (PSimple p S)} (hD : FR.SubfieldGrp (indAut p S b hb) D)
    [IsSimpleGroup ↥D] (hDn : ∃ x y : ↥D, x * y ≠ y * x) (hpD : p ∣ Nat.card ↥D) :
    GLAPLayer p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Xs : Subgroup ↥S := (S ⊓ Subgroup.centralizer ({b} : Set Ω)).subgroupOf S with hXs
  set Xb : Subgroup (PSimple p S) := Xs.map (chevQuotHom p S) with hXb
  have hX : FR.SubfieldGrp (indAut p S b hb) Xb := FR.fieldOn_lift hp hp2 hb hbp
  have hperfD : Group.IsPerfect ↥D :=
    Group.isPerfect_def.mpr (GL83.PiGen.isQuasisimple_of_simple_nonabelian hDn).1
  have hDperf : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.1 hperfD
  have hDXb : D ≤ Xb :=
    calc D = ⁅D, D⁆ := hDperf.symm
      _ ≤ ⁅FP.fixSub (indAut p S b hb), FP.fixSub (indAut p S b hb)⁆ :=
        Subgroup.commutator_mono hD.1 hD.1
      _ ≤ Xb := hX.2.1
  have hnormal : (D.subgroupOf Xb).Normal := by
    refine ⟨fun d hd x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hd ⊢
    have hxC : (x : PSimple p S) ∈ FP.fixSub (indAut p S b hb) := hX.1 x.2
    have hdC : (d : PSimple p S) ∈ FP.fixSub (indAut p S b hb) := hD.1 hd
    have hcomm : ⁅(x : PSimple p S), (d : PSimple p S)⁆ ∈ D :=
      hD.2.1 (Subgroup.commutator_mem_commutator hxC hdC)
    have e : ((x * d * x⁻¹ : ↥Xb) : PSimple p S) = ⁅(x : PSimple p S), (d : PSimple p S)⁆ * (d : PSimple p S) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact D.mul_mem hcomm hd
  have hcomp : GLAPComponent p Xb D := GL83.PiGen.glaPComponent_of_normal_simple hp hDXb hnormal hDn hpD
  have hlayer : GLAPLayer p Xb ≠ ⊥ := by
    intro h
    have hle : D ≤ GLAPLayer p Xb := by
      unfold GLAPLayer
      exact le_sSup hcomp
    rw [h, le_bot_iff] at hle
    obtain ⟨x, y, hxy⟩ := hDn
    have hx : x = 1 := Subtype.ext (by simpa using (hle ▸ x.2 : (x : PSimple p S) ∈ (⊥ : Subgroup _)))
    exact hxy (by rw [hx, one_mul, mul_one])
  have hcenter : ∀ y ∈ Xs ⊓ (chevQuotHom p S).ker, ∀ x ∈ Xs, x * y = y * x := by
    intro y hy x _
    have h1 : QuotientGroup.mk y = (1 : ↥S ⧸ Subgroup.center ↥S) := by
      rw [← pSimpleEquiv_chevQuotHom hSp y, MonoidHom.mem_ker.1 hy.2, map_one]
    exact (Subgroup.mem_center_iff.1 ((QuotientGroup.eq_one_iff y).1 h1) x)
  have hS : GLAPLayer p Xs ≠ ⊥ := (CFSG.glaPLayer_ne_bot_iff_map_ne_bot hp (chevQuotHom p S) hcenter).2 hlayer
  have hinj : ∀ y ∈ Xs ⊓ S.subtype.ker, ∀ x ∈ Xs, x * y = y * x := by
    intro y hy x _
    have : y = 1 := (MonoidHom.ker_eq_bot_iff _ |>.2 S.subtype_injective ▸ hy.2 : y ∈ (⊥ : Subgroup ↥S)) |> Subgroup.mem_bot.1
    rw [this, one_mul, mul_one]
  have hmap : Xs.map S.subtype = S ⊓ Subgroup.centralizer ({b} : Set Ω) :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_left
  have := (CFSG.glaPLayer_ne_bot_iff_map_ne_bot hp S.subtype hinj).1 hS
  rwa [hmap] at this

end Lift

end CFSG.LocalAnalysis.GLTheoremA.T263

end
