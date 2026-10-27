module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B6
public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.TwE6Core
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Arith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.Mathlib.RingTheory.UnitOrderOf
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE6.Phi3A2
public import CFSG.RankThree.PartOne.KE6.Phi3A2b
public import CFSG.RankThree.PartOne.KE6.Phi3Frame
public import CFSG.RankThree.PartOne.KE6.Phi3Lattice
public import CFSG.RankThree.PartOne.KE6.Phi3Orbit
public import CFSG.RankThree.PartOne.KE6.Phi3Torsion
public import CFSG.RankThree.PartOne.KE6.Phi3Transport
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp
public import CFSG.RankThree.PartOne.KE6.Phi6Frame
public import CFSG.RankThree.PartOne.KE6.Phi6Shape
public import CFSG.RankThree.PartOne.KE6.Phi6Torsion
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.RankThree.PartOne.KLCE.A2Family
public import CFSG.RankThree.PartOne.KLCE.Descent
public import CFSG.RankThree.PartOne.KLCE.EngineGroup
public import CFSG.RankThree.PartOne.KLCE.TypeSL
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartOne.SLB4A.ClassExcRest
public import CFSG.RankThree.PartOne.TCX.F4.LayerClaims
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.Statements

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix
open CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Malle.E27Lie.ExcCross

section Certs


variable {Ω : Type} [Field Ω] [CharP Ω 2]

namespace TwE6B

theorem weylElt_mem_thetaFixed (Fr : Ω →+* Ω) (i : Fin Tag.E6.rank) :
    weylElt Tag.E6 Ω i 1 ∈ TwistedDiag.thetaFixed Fr := by
  rw [TwistedDiag.mem_thetaFixed]
  refine ⟨weylElt_mem_adjointGroup i 1, ?_⟩
  rw [TwistedDiag.theta_apply]
  exact weylElt_twistFixed6 (L := Ω) Fr (fun u => twE6W0_smul u) i

theorem theta_torusElt_eq {Fr : Ω →+* Ω} {t : Ωˣ} {n : ℕ}
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) (ht : t ^ (2 ^ n + 1) = 1) (i : Fin Tag.E6.rank) :
    TwistedDiag.theta Fr (torusElt Tag.E6 Ω i t) = torusElt Tag.E6 Ω i t := by
  rw [torusElt_eq_rootDiagUnit, (TwistedDiag.theta_rootDiagUnit_eq_iff Fr hFr _).2]
  intro j
  have hstep : (t ^ Tag.E6.cartan i j) ^ (2 ^ n + 1) =
      (t ^ (2 ^ n + 1 : ℕ)) ^ Tag.E6.cartan i j := by
    rw [← zpow_natCast (t ^ Tag.E6.cartan i j) (2 ^ n + 1),
      ← zpow_natCast t (2 ^ n + 1), ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  rw [hstep, ht]
  simp

theorem torusElt_mem_twE6Block {Fr : Ω →+* Ω} {n : ℕ} (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {t : Ωˣ} (ht : t ^ (2 ^ n + 1) = 1) {i : Fin Tag.E6.rank} (hi : i ∈ support56) :
    torusElt Tag.E6 Ω i t ∈ twE6Block Fr := by
  rw [mem_twE6Block]
  refine ⟨subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hi t), ?_⟩
  rw [TwistedDiag.mem_thetaFixed]
  exact ⟨torusElt_mem_adjointGroup i t, theta_torusElt_eq hFr ht i⟩

theorem pow_two_pow_add_one_eq_one {ω : Ωˣ} {n : ℕ} (hω3 : ω ^ 3 = 1) (hn : Odd n) :
    ω ^ (2 ^ n + 1) = 1 := by
  obtain ⟨k, hk⟩ := Odd.nat_add_dvd_pow_add_pow 2 1 hn
  rw [one_pow] at hk
  rw [hk, pow_mul, hω3, one_pow]

theorem torusElt_four_mem_twE6C {Fr : Ω →+* Ω} {ω : Ωˣ} {n : ℕ} {K : Type} [Field K]
    [Algebra K Ω] [IsAlgClosure K Ω] (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 3 ≤ n) (hod : Odd n) (hω3 : ω ^ 3 = 1) :
    torusElt Tag.E6 Ω 4 ω ∈ twE6C Fr :=
  twE6Block_le_C (Ω := Ω) hFr hK hn hod
    (torusElt_mem_twE6Block hFr (pow_two_pow_add_one_eq_one hω3 hod)
      (by rw [mem_support56]; left; rfl))

private theorem conj_mem_commutator {G : Type*} [Group G] {S : Subgroup G} {n : G} (hn : n ∈ S)
    {x : G} (hx : x ∈ ⁅S, S⁆) : n * x * n⁻¹ ∈ ⁅S, S⁆ := by
  have hmem : ∀ z ∈ S, (MulAut.conj n) z ∈ S := fun z hz => by
    simpa only [MulAut.conj_apply] using mul_mem (mul_mem hn hz) (inv_mem hn)
  have hmapS : Subgroup.map (MulAut.conj n).toMonoidHom S = S := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.2 hmem) ?_
    intro y hy
    exact ⟨n⁻¹ * y * n, mul_mem (mul_mem (inv_mem hn) hy) hn, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have hmap : Subgroup.map (MulAut.conj n).toMonoidHom ⁅S, S⁆ = ⁅S, S⁆ := by
    calc Subgroup.map (MulAut.conj n).toMonoidHom ⁅S, S⁆
        = ⁅Subgroup.map (MulAut.conj n).toMonoidHom S,
            Subgroup.map (MulAut.conj n).toMonoidHom S⁆ := Subgroup.map_commutator S S _
      _ = ⁅S, S⁆ := by rw [hmapS]
  have h := Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hx
  rw [hmap] at h
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

private theorem torusElt_conj_step (t : Ωˣ) (i j : Fin Tag.E6.rank) :
    (torusElt Tag.E6 Ω i t * torusElt Tag.E6 Ω i (t ^ (-2 : ℤ))) *
        (torusElt Tag.E6 Ω j t * torusElt Tag.E6 Ω i t) = torusElt Tag.E6 Ω j t := by
  have hti : t * t ^ (-2 : ℤ) = t⁻¹ := by
    rw [_root_.zpow_neg, _root_.zpow_ofNat, pow_two, _root_.mul_inv_rev]
    group
  calc (torusElt Tag.E6 Ω i t * torusElt Tag.E6 Ω i (t ^ (-2 : ℤ))) *
        (torusElt Tag.E6 Ω j t * torusElt Tag.E6 Ω i t)
      = torusElt Tag.E6 Ω i (t⁻¹) * (torusElt Tag.E6 Ω j t * torusElt Tag.E6 Ω i t) := by
        rw [← torusElt_mul, hti]
    _ = torusElt Tag.E6 Ω i (t⁻¹) * torusElt Tag.E6 Ω j t * torusElt Tag.E6 Ω i t := by
        rw [mul_assoc]
    _ = torusElt Tag.E6 Ω j t * torusElt Tag.E6 Ω i (t⁻¹) * torusElt Tag.E6 Ω i t := by
        rw [torusElt_mul_comm (i := i) (j := j) (t := t⁻¹) (u := t)]
    _ = torusElt Tag.E6 Ω j t * (torusElt Tag.E6 Ω i (t⁻¹) * torusElt Tag.E6 Ω i t) := by
        rw [mul_assoc]
    _ = torusElt Tag.E6 Ω j t * torusElt Tag.E6 Ω i (t⁻¹ * t) := by rw [← torusElt_mul]
    _ = torusElt Tag.E6 Ω j t * torusElt Tag.E6 Ω i 1 := by rw [inv_mul_cancel]
    _ = torusElt Tag.E6 Ω j t := by rw [torusElt_one, mul_one]

theorem weylElt_four_conj_torusElt (t : Ωˣ) :
    (weylElt Tag.E6 Ω 3 1 * weylElt Tag.E6 Ω 2 1 * weylElt Tag.E6 Ω 4 1 *
        weylElt Tag.E6 Ω 3 1) * torusElt Tag.E6 Ω 4 t *
        (weylElt Tag.E6 Ω 3 1 * weylElt Tag.E6 Ω 2 1 * weylElt Tag.E6 Ω 4 1 *
          weylElt Tag.E6 Ω 3 1)⁻¹ = torusElt Tag.E6 Ω 2 t := by
  have h43 : Tag.E6.cartan 4 3 = -1 := by decide
  have h44 : Tag.E6.cartan 4 4 = 2 := by decide
  have h34 : Tag.E6.cartan 3 4 = -1 := by decide
  have h33 : Tag.E6.cartan 3 3 = 2 := by decide
  have h32 : Tag.E6.cartan 3 2 = -1 := by decide
  have h23 : Tag.E6.cartan 2 3 = -1 := by decide
  have e44 : t ^ (-Tag.E6.cartan 4 4) = t ^ (-2 : ℤ) := by rw [h44]
  have e34 : t ^ (-Tag.E6.cartan 3 4) = t := by rw [h34, neg_neg, zpow_one]
  have e33 : t ^ (-Tag.E6.cartan 3 3) = t ^ (-2 : ℤ) := by rw [h33]
  have e23 : t ^ (-Tag.E6.cartan 2 3) = t := by rw [h23, neg_neg, zpow_one]
  have e43 : t ^ (-Tag.E6.cartan 4 3) = t := by rw [h43, neg_neg, zpow_one]
  have e32 : t ^ (-Tag.E6.cartan 3 2) = t := by rw [h32, neg_neg, zpow_one]
  have h1 : (weylElt Tag.E6 Ω 3 1) * torusElt Tag.E6 Ω 4 t *
      (weylElt Tag.E6 Ω 3 1)⁻¹ = torusElt Tag.E6 Ω 4 t * torusElt Tag.E6 Ω 3 t := by
    rw [weylElt_one_mul_torusElt_mul_inv Tag.E6 Ω 3 4 t, e43]
  have h2 : (weylElt Tag.E6 Ω 4 1) * (torusElt Tag.E6 Ω 4 t * torusElt Tag.E6 Ω 3 t) *
      (weylElt Tag.E6 Ω 4 1)⁻¹ = torusElt Tag.E6 Ω 3 t := by
    rw [show (weylElt Tag.E6 Ω 4 1) * (torusElt Tag.E6 Ω 4 t * torusElt Tag.E6 Ω 3 t) *
        (weylElt Tag.E6 Ω 4 1)⁻¹ =
        ((weylElt Tag.E6 Ω 4 1) * torusElt Tag.E6 Ω 4 t * (weylElt Tag.E6 Ω 4 1)⁻¹) *
          ((weylElt Tag.E6 Ω 4 1) * torusElt Tag.E6 Ω 3 t * (weylElt Tag.E6 Ω 4 1)⁻¹) from by
      group]
    rw [weylElt_one_mul_torusElt_mul_inv Tag.E6 Ω 4 4 t,
      weylElt_one_mul_torusElt_mul_inv Tag.E6 Ω 4 3 t, e44, e34]
    exact torusElt_conj_step t 4 3
  have h3 : (weylElt Tag.E6 Ω 2 1) * torusElt Tag.E6 Ω 3 t * (weylElt Tag.E6 Ω 2 1)⁻¹ =
      torusElt Tag.E6 Ω 3 t * torusElt Tag.E6 Ω 2 t := by
    rw [weylElt_one_mul_torusElt_mul_inv Tag.E6 Ω 2 3 t, e32]
  have h4 : (weylElt Tag.E6 Ω 3 1) * (torusElt Tag.E6 Ω 3 t * torusElt Tag.E6 Ω 2 t) *
      (weylElt Tag.E6 Ω 3 1)⁻¹ = torusElt Tag.E6 Ω 2 t := by
    rw [show (weylElt Tag.E6 Ω 3 1) * (torusElt Tag.E6 Ω 3 t * torusElt Tag.E6 Ω 2 t) *
        (weylElt Tag.E6 Ω 3 1)⁻¹ =
        ((weylElt Tag.E6 Ω 3 1) * torusElt Tag.E6 Ω 3 t * (weylElt Tag.E6 Ω 3 1)⁻¹) *
          ((weylElt Tag.E6 Ω 3 1) * torusElt Tag.E6 Ω 2 t * (weylElt Tag.E6 Ω 3 1)⁻¹) from by
      group]
    rw [weylElt_one_mul_torusElt_mul_inv Tag.E6 Ω 3 3 t,
      weylElt_one_mul_torusElt_mul_inv Tag.E6 Ω 3 2 t, e33, e23]
    exact torusElt_conj_step t 3 2
  calc (weylElt Tag.E6 Ω 3 1 * weylElt Tag.E6 Ω 2 1 * weylElt Tag.E6 Ω 4 1 *
        weylElt Tag.E6 Ω 3 1) * torusElt Tag.E6 Ω 4 t *
        (weylElt Tag.E6 Ω 3 1 * weylElt Tag.E6 Ω 2 1 * weylElt Tag.E6 Ω 4 1 *
          weylElt Tag.E6 Ω 3 1)⁻¹
      = (weylElt Tag.E6 Ω 3 1) * ((weylElt Tag.E6 Ω 2 1) * ((weylElt Tag.E6 Ω 4 1) *
          ((weylElt Tag.E6 Ω 3 1) * torusElt Tag.E6 Ω 4 t * (weylElt Tag.E6 Ω 3 1)⁻¹) *
            (weylElt Tag.E6 Ω 4 1)⁻¹) * (weylElt Tag.E6 Ω 2 1)⁻¹) *
          (weylElt Tag.E6 Ω 3 1)⁻¹ := by group
    _ = (weylElt Tag.E6 Ω 3 1) * ((weylElt Tag.E6 Ω 2 1) * ((weylElt Tag.E6 Ω 4 1) *
          (torusElt Tag.E6 Ω 4 t * torusElt Tag.E6 Ω 3 t) *
            (weylElt Tag.E6 Ω 4 1)⁻¹) * (weylElt Tag.E6 Ω 2 1)⁻¹) *
          (weylElt Tag.E6 Ω 3 1)⁻¹ := by rw [h1]
    _ = (weylElt Tag.E6 Ω 3 1) * ((weylElt Tag.E6 Ω 2 1) * torusElt Tag.E6 Ω 3 t *
          (weylElt Tag.E6 Ω 2 1)⁻¹) * (weylElt Tag.E6 Ω 3 1)⁻¹ := by rw [h2]
    _ = (weylElt Tag.E6 Ω 3 1) *
          (torusElt Tag.E6 Ω 3 t * torusElt Tag.E6 Ω 2 t) * (weylElt Tag.E6 Ω 3 1)⁻¹ := by
        rw [h3]
    _ = torusElt Tag.E6 Ω 2 t := h4

theorem fBar_mem_C {Fr : Ω →+* Ω} {ω : Ωˣ} {n : ℕ} {K : Type} [Field K]
    [Algebra K Ω] [IsAlgClosure K Ω] (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 3 ≤ n) (hod : Odd n) (hω3 : ω ^ 3 = 1) :
    fBar (Ω := Ω) ω ∈ twE6C Fr := by
  have hnmem : (weylElt Tag.E6 Ω 3 1 * weylElt Tag.E6 Ω 2 1 * weylElt Tag.E6 Ω 4 1 *
      weylElt Tag.E6 Ω 3 1) ∈ TwistedDiag.thetaFixed Fr :=
    mul_mem (mul_mem (mul_mem (weylElt_mem_thetaFixed Fr 3) (weylElt_mem_thetaFixed Fr 2))
      (weylElt_mem_thetaFixed Fr 4)) (weylElt_mem_thetaFixed Fr 3)
  have hconj : (weylElt Tag.E6 Ω 3 1 * weylElt Tag.E6 Ω 2 1 * weylElt Tag.E6 Ω 4 1 *
      weylElt Tag.E6 Ω 3 1) * torusElt Tag.E6 Ω 4 ω *
      (weylElt Tag.E6 Ω 3 1 * weylElt Tag.E6 Ω 2 1 * weylElt Tag.E6 Ω 4 1 *
        weylElt Tag.E6 Ω 3 1)⁻¹ ∈ twE6C Fr :=
    mem_twE6C.2 (conj_mem_commutator hnmem
      (mem_twE6C.1 (torusElt_four_mem_twE6C (Ω := Ω) hFr hK hn hod hω3)))
  rw [fBar_eq_torusElt hω3, ← weylElt_four_conj_torusElt (Ω := Ω) ω]
  exact hconj

theorem orderOf_sq_of_orderOf_eq_three {ω : Ωˣ} (hω : orderOf ω = 3) : orderOf (ω ^ 2) = 3 := by
  have h : ω ^ 2 * ω = 1 := by
    rw [show ω ^ 2 * ω = ω ^ 3 by group, ← hω, pow_orderOf_eq_one]
  have hω2 : ω ^ 2 = ω⁻¹ := by
    calc ω ^ 2 = ω ^ 2 * ω * ω⁻¹ := by group
      _ = 1 * ω⁻¹ := by rw [h]
      _ = ω⁻¹ := by rw [one_mul]
  rw [hω2, orderOf_inv, hω]

theorem eBarTuple_eq {ω : Ωˣ} (hω3 : ω ^ 3 = 1) :
    eBarTuple ω = (fun j => ω ^ Tag.E6.cartan 4 j) *
      (fun j => (ω ^ 2) ^ Tag.E6.cartan 5 j) := by
  apply rootDiagUnit_injective (τ := Tag.E6)
  rw [rootDiagUnit_mul, ← torusElt_eq_rootDiagUnit, ← torusElt_eq_rootDiagUnit]
  exact eBar_eq_torusElt hω3

theorem fBarTuple_eq {ω : Ωˣ} (hω3 : ω ^ 3 = 1) :
    fBarTuple ω = fun j => ω ^ Tag.E6.cartan 2 j := by
  apply rootDiagUnit_injective (τ := Tag.E6)
  rw [← torusElt_eq_rootDiagUnit]
  exact fBar_eq_torusElt hω3

private theorem eBar_pow_coord {ω : Ωˣ} {k : ℤ} :
    (eBar (Ω := Ω) ω ^ k : ModGL Tag.E6 Ω) =
      rootDiagUnit Tag.E6 (eBarTuple ω ^ k) := by
  rw [eBar]
  exact (map_zpow (rootDiagUnitHom Tag.E6 Ω) (eBarTuple ω) k).symm

private theorem fBar_pow_coord {ω : Ωˣ} {m : ℤ} :
    (fBar (Ω := Ω) ω ^ m : ModGL Tag.E6 Ω) =
      rootDiagUnit Tag.E6 (fBarTuple ω ^ m) := by
  rw [fBar]
  exact (map_zpow (rootDiagUnitHom Tag.E6 Ω) (fBarTuple ω) m).symm

theorem disjoint_zpowers_eBar_fBar {ω : Ωˣ} (hω3 : ω ^ 3 = 1) (hω : orderOf ω = 3) :
    Subgroup.zpowers (eBar (Ω := Ω) ω) ⊓ Subgroup.zpowers (fBar (Ω := Ω) ω) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxA
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hxB
  have htup : eBarTuple ω ^ k = fBarTuple ω ^ m := by
    apply rootDiagUnit_injective (τ := Tag.E6)
    rw [← eBar_pow_coord, ← fBar_pow_coord, hm]
  have hωinv : ω⁻¹ = ω ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, show ω * ω ^ 2 = ω ^ 3 by group, hω3]
  have h1 : eBarTuple ω (0 : Fin Tag.E6.rank) = 1 := by
    rw [eBarTuple_eq hω3]
    simp only [Pi.mul_apply]
    rw [show Tag.E6.cartan 4 (0 : Fin Tag.E6.rank) = 0 by decide,
      show Tag.E6.cartan 5 (0 : Fin Tag.E6.rank) = 0 by decide]
    simp
  have h2 : fBarTuple ω (0 : Fin Tag.E6.rank) = ω ^ 2 := by
    rw [fBarTuple_eq hω3]
    show ω ^ Tag.E6.cartan 2 (0 : Fin Tag.E6.rank) = ω ^ 2
    rw [show Tag.E6.cartan 2 (0 : Fin Tag.E6.rank) = -1 by decide, _root_.zpow_neg,
      _root_.zpow_one, hωinv]
  have h0 : (1 : Ωˣ) = (ω ^ 2) ^ m := by
    have h := congrFun htup (0 : Fin Tag.E6.rank)
    rw [Pi.pow_apply, Pi.pow_apply, h1, h2, _root_.one_zpow] at h
    exact h
  have h3m : (3 : ℤ) ∣ m := by
    have h : (ω ^ 2) ^ m = 1 := h0.symm
    have := (orderOf_dvd_iff_zpow_eq_one (x := ω ^ 2) (i := m)).2 h
    rwa [orderOf_sq_of_orderOf_eq_three hω] at this
  have h3m' : (orderOf (fBar (Ω := Ω) ω) : ℤ) ∣ m := by
    rw [orderOf_fBar hω3 hω]
    exact h3m
  have hpow : fBar (Ω := Ω) ω ^ m = 1 :=
    (orderOf_dvd_iff_zpow_eq_one (x := fBar (Ω := Ω) ω) (i := m)).1 h3m'
  rw [Subgroup.mem_bot, ← hm, hpow]

private theorem card_sup_of_disjoint {G : Type*} [Group G] {A B : Subgroup G}
    (hdisj : A ⊓ B = ⊥) (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hc' : ∀ m : A, ∀ n : B, Commute (m : G) (n : G) := fun m n => hc m.1 m.2 n.1 n.2
  set f : A × B →* G := MonoidHom.noncommCoprod A.subtype B.subtype hc' with hf
  have hfval : ∀ x : A × B, f x = (x.1 : G) * (x.2 : G) := fun _ => rfl
  have hker : ∀ x : A × B, f x = 1 → x = 1 := by
    intro x hx
    have hmul : (x.1 : G) * (x.2 : G) = 1 := by rw [← hfval]; exact hx
    have h1 : (x.1 : G) = (x.2 : G)⁻¹ := by
      calc (x.1 : G) = (x.1 : G) * (x.2 : G) * (x.2 : G)⁻¹ := by group
        _ = 1 * (x.2 : G)⁻¹ := by rw [hmul]
        _ = (x.2 : G)⁻¹ := by rw [one_mul]
    have hB : (x.2 : G)⁻¹ ∈ B := inv_mem x.2.2
    have hxA : (x.1 : G) ∈ A ⊓ B := ⟨x.1.2, by rw [h1]; exact hB⟩
    rw [hdisj] at hxA
    have hx1 : (x.1 : G) = 1 := by simpa using hxA
    have hx2 : (x.2 : G) = 1 := by
      have h2 : (x.2 : G)⁻¹ = 1 := by rw [← h1, hx1]
      calc (x.2 : G) = ((x.2 : G)⁻¹)⁻¹ := (inv_inv _).symm
        _ = 1 := by rw [h2, inv_one]
    exact Prod.ext (Subtype.ext hx1) (Subtype.ext hx2)
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : f (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 := hker (x * y⁻¹) h1
    rwa [mul_inv_eq_one] at h2
  have hrange : f.range = A ⊔ B := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · rintro _ ⟨x, rfl⟩
      rw [hfval]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · intro x hx
      exact ⟨(⟨x, hx⟩, 1), by rw [hfval]; simp⟩
    · intro y hy
      exact ⟨(1, ⟨y, hy⟩), by rw [hfval]; simp⟩
  let F : A × B → ↥(A ⊔ B) := fun x =>
    ⟨f x, by rw [← hrange]; exact MonoidHom.mem_range.2 ⟨x, rfl⟩⟩
  have hF : Function.Bijective F := by
    refine ⟨fun x y h => hinj (congrArg Subtype.val h), ?_⟩
    intro z
    have hz : (z : G) ∈ f.range := by rw [hrange]; exact z.2
    obtain ⟨x, hx⟩ := hz
    exact ⟨x, Subtype.ext hx⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_prod]

private theorem closure_pair_eq_sup {G : Type*} [Group G] (a b : G) :
    Subgroup.closure ({a, b} : Set G) = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  rw [Subgroup.sup_eq_closure]
  refine le_antisymm ?_ ?_
  · refine Subgroup.closure_mono ?_
    rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨Set.mem_union_left _ (Subgroup.mem_zpowers_iff.2 ⟨1, zpow_one a⟩),
      Set.mem_union_right _ (Subgroup.mem_zpowers_iff.2 ⟨1, zpow_one b⟩)⟩
  · refine (Subgroup.closure_le _).2 ?_
    rw [Set.union_subset_iff]
    exact ⟨Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_insert _ _)),
      Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))⟩

theorem card_closure_eBar_fBar {ω : Ωˣ} (hω3 : ω ^ 3 = 1) (hω : orderOf ω = 3) :
    Nat.card (Subgroup.closure
      ({eBar (Ω := Ω) ω, fBar (Ω := Ω) ω} : Set (ModGL Tag.E6 Ω))) = 9 := by
  have hpair := closure_pair_eq_sup (eBar (Ω := Ω) ω) (fBar (Ω := Ω) ω)
  have hcomm : ∀ x ∈ Subgroup.zpowers (eBar (Ω := Ω) ω),
      ∀ y ∈ Subgroup.zpowers (fBar (Ω := Ω) ω), x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (commute_eBar_fBar (Ω := Ω) (ω := ω)).zpow_zpow k m
  rw [hpair, card_sup_of_disjoint (disjoint_zpowers_eBar_fBar hω3 hω) hcomm,
    Nat.card_zpowers, Nat.card_zpowers, orderOf_eBar hω3 hω, orderOf_fBar hω3 hω]


end TwE6B

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
