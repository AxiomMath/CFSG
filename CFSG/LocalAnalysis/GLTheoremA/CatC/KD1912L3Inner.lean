module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912L3InnerDiag
public import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofRigid

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Sec14
open CFSG.Assembly.RankThreeEven
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.Open
open Matrix

variable {K : Type} [Field K] {n : ℕ} {π : Bool}

theorem odd_card_gLAPPrimeCoreOf_fixSub_conjM' (hK : PiField π 2 n K)
    (hq : ModThree π (2 ^ n)) (hn : 2 ≤ n)
    {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (2 ^ n) K)
    (hgZ : g ∉ zPi π 3 (2 ^ n) K) (hg3 : g ^ 3 ∈ zPi π 3 (2 ^ n) K) :
    Odd (Nat.card (GLAPPrimeCoreOf 3
      (((Res8Hess.conjM' (p := 2) (f := n)
          (fun h => by subst h; exact hK.unitary) hg :
        MulAut (projImage (slPi π 3 (2 ^ n) K))) :
      projImage (slPi π 3 (2 ^ n) K) →*
        projImage (slPi π 3 (2 ^ n) K)).eqLocus (MonoidHom.id _)))) := by
  classical
  haveI hKfin : Finite K := hK.finite
  let L := slPi π 3 (2 ^ n) K
  change Odd (Nat.card (GLAPPrimeCoreOf 3
    (((Res8Hess.conjM' (p := 2) (f := n)
        (fun h => by subst h; exact hK.unitary) hg :
      MulAut (projImage L)) : projImage L →* projImage L).eqLocus (MonoidHom.id _))))
  have hπ : π = false → UnitaryFieldData 2 n K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨y, ⟨z, hz, hyz⟩, hcases⟩ := rank3II_4_10_one hK hq hτ hτ1 hg hgZ hg3
  have hzS : z ∈ StatedScalars (Fin 3) K := by
    have hπ' : π = false → UnitaryFieldData 2 n K := fun h => by subst h; exact hK.unitary
    have hq' : π = false → ModThree false (2 ^ n) := fun h => by subst h; exact hq
    rw [zPi_eq hπ' hq' hτ hτ1] at hz
    exact (Subgroup.mem_inf.1 hz).2
  have hzgl : z ∈ glPi π 3 (2 ^ n) K := Subgroup.map_subtype_le _ hz
  have hyg : y ∈ glPi π 3 (2 ^ n) K := by
    rw [hyz]
    exact mul_mem hg hzgl
  have hmkz : ProjGenLinGroup.mk z = 1 := mk_eq_one_iff_mem_statedScalars.2 hzS
  have hconjEq : Res8Hess.conjM' (p := 2) (f := n)
      (fun h => by subst h; exact hK.unitary) hyg =
      Res8Hess.conjM' (p := 2) (f := n)
        (fun h => by subst h; exact hK.unitary) hg := by
    ext m
    rw [Res8Hess.coe_conjM', Res8Hess.coe_conjM']
    simp [hyz, map_mul, map_inv, hmkz]
  have hfix : (((Res8Hess.conjM' (p := 2) (f := n)
        (fun h => by subst h; exact hK.unitary) hg :
      MulAut (projImage L)) : projImage L →* projImage L).eqLocus (MonoidHom.id _)) =
      ((centMod L y).subgroupOf L).map (projOf L) := by
    rw [← hconjEq]
    exact eqLocus_conjM'_eq_map_centMod (π := π) (n := n) hK hyg
  rw [hfix]
  rcases hcases with ⟨-, hCL, hrel⟩ | ⟨-, hCL, hcen⟩ |
    ⟨-, -, -, hcyc, hcardCL, w, hwL, hwo, hwC, hcent, -⟩
  · exact odd_card_core_map_centMod_of_regular (π := π) (n := n) hK hq hn hCL hrel
  · exact odd_card_core_map_centMod_of_glTwo (π := π) (n := n) hK hq hn hcen hCL
  · exact odd_card_core_map_centMod_of_singer (π := π) (n := n) hK hq hn hcyc hcardCL hcent hwL hwo hwC

theorem odd_card_core_of_mem_linearAutGroup [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : Even n) (hn0 : n ≠ 0)
    {x : MulAut (projectiveSL 3 K)} (hx : x ∈ linearAutGroup 3 K) (hx3 : orderOf x = 3) :
    Odd (Nat.card (GLAPPrimeCoreOf 3
      (CFSG.HardMathSupport.Solomon.LocalBalance.innerAut (projectiveSL 3 K) ⊓
        Subgroup.centralizer ({x} : Set (MulAut (projectiveSL 3 K)))))) := by
  classical
  have hn2 : 2 ≤ n := by
    obtain ⟨m, hm⟩ := hn
    omega
  have hK' : PiField true 2 n K :=
    ⟨Nat.prime_two, by omega, by simpa [piCard] using hK⟩
  have hq : ModThree true (2 ^ n) := CFSG.LocalAnalysis.GLTheoremA.KD1912.modThree_two_pow_even hK hn
  have hn2' : 2 < 2 ^ n := by
    calc 2 < 4 := by norm_num
      _ = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hrange : linearAutGroup 3 K = (conjAut 3 K).range := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup,
      ← MonoidHom.coe_range, Subgroup.closure_eq]
  rw [hrange] at hx
  obtain ⟨A, rfl⟩ := hx
  have hxne : conjAut 3 K A ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx3
    omega
  have hx3pow : (conjAut 3 K A) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (conjAut 3 K A)
    rwa [hx3] at this
  have hπ0 : true = false → UnitaryFieldData 2 n K := fun h => absurd h (by decide)
  have hq0 : true = false → ModThree false (2 ^ n) := fun h => absurd h (by decide)
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK' hq
  have hA3 : A ^ 3 ∈ zPi true 3 (2 ^ n) K := by
    have hconj1 : conjAut 3 K (A ^ 3) = 1 := by
      rw [map_pow]
      exact hx3pow
    obtain ⟨c, hc⟩ := (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conjAut_eq_one_iff
      (F := K) (n := 3) (by norm_num) (A ^ 3)).1 hconj1
    rw [zPi_eq hπ0 hq0 hτ hτ1]
    refine Subgroup.mem_inf.2 ⟨mem_glPi_true _ _, ?_⟩
    exact ⟨c, hc.symm⟩
  have hAZ : A ∉ zPi true 3 (2 ^ n) K := by
    intro hz
    rw [zPi_eq hπ0 hq0 hτ hτ1] at hz
    obtain ⟨-, c, hc⟩ := Subgroup.mem_inf.1 hz
    exact hxne (by rw [← hc]; exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_scalar c)
  have hmain := odd_card_gLAPPrimeCoreOf_fixSub_conjM' (π := true) (n := n)
    hK' hq hn2 (mem_glPi_true _ A) hAZ hA3
  let e := pslEquivProjective (2 ^ n) K
  have hxeq : MulAut.congr e
      (Res8Hess.conjM' (p := 2) (f := n) (fun h => absurd h (by decide))
        (mem_glPi_true _ A)) = conjAut 3 K A :=
    L3PGL.congr_conjM'_true (p := 2) (f := n) (fun h => absurd h (by decide))
      (mem_glPi_true _ A)
  have hZmodel : Subgroup.center (projImage (slPi true 3 (2 ^ n) K)) = ⊥ :=
    CFSG.RankThree.PartTwo.Sec13.center_projImage_slPi hK' hq hn2'
  have hZ : Subgroup.center (projectiveSL 3 K) = ⊥ := by
    rw [← Subgroup.map_center_eq e, hZmodel, Subgroup.map_bot]
  have hcore : Odd (Nat.card (GLAPPrimeCoreOf 3
      (((conjAut 3 K A : MulAut (projectiveSL 3 K)) :
        projectiveSL 3 K →* projectiveSL 3 K).eqLocus (MonoidHom.id _)))) := by
    have hfix := CFSG.eqLocus_congr_map e
      (Res8Hess.conjM' (p := 2) (f := n) (fun h => absurd h (by decide))
        (mem_glPi_true _ A))
    rw [hxeq] at hfix
    rw [hfix]
    rw [CFSG.gLAPPrimeCoreOf_map_mulEquiv]
    rw [(Nat.card_congr (MulEquiv.subgroupMap e _).toEquiv).symm]
    exact hmain
  exact (CFSG.odd_card_gLAPPrimeCoreOf_innerAut_inf_centralizer_iff hZ 3
    (conjAut 3 K A)).mpr hcore

theorem odd_card_core_of_mem_psuConj_range {n : ℕ}
    (h : UnitaryFieldData 2 n K) (hn : Odd n) (hn1 : 1 < n)
    {x : MulAut (unitaryPSU h 3)} (hx : x ∈ (psuConj h).range) (hx3 : orderOf x = 3) :
    Odd (Nat.card (GLAPPrimeCoreOf 3
      (CFSG.HardMathSupport.Solomon.LocalBalance.innerAut (unitaryPSU h 3) ⊓
        Subgroup.centralizer ({x} : Set (MulAut (unitaryPSU h 3)))))) := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hK' : PiField false 2 n K :=
    ⟨Nat.prime_two, by omega, by
      show Nat.card K = (2 ^ n) ^ 2
      rw [h.card, show 2 * n = n * 2 by ring, ← pow_mul]⟩
  have hq : ModThree false (2 ^ n) := CFSG.LocalAnalysis.GLTheoremA.KD1912.modThree_two_pow_odd hn
  have hn2' : 2 < 2 ^ n := by
    calc 2 < 4 := by norm_num
      _ = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  rw [MonoidHom.mem_range] at hx
  obtain ⟨A, rfl⟩ := hx
  have hπ0 : false = false → UnitaryFieldData 2 n K := fun _ => h
  have hq0 : false = false → ModThree false (2 ^ n) := fun _ => hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK' hq
  have hxne : psuConj h A ≠ 1 := by
    intro hh
    rw [hh, orderOf_one] at hx3
    omega
  have hx3pow : (psuConj h A) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (psuConj h A)
    rwa [hx3] at this
  have hA : (A : GL (Fin 3) K) ∈ glPi false 3 (2 ^ n) K :=
    (mem_glPi_false h).2 (mem_unitaryIsom3.mp A.2)
  have hA3 : (A : GL (Fin 3) K) ^ 3 ∈ zPi false 3 (2 ^ n) K := by
    have hconj1 : psuConj h (A ^ 3) = 1 := by
      rw [map_pow]
      exact hx3pow
    have hscal : ((A ^ 3 : ↥(unitaryIsom3 h)) : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K :=
      (CFSG.RankThree.PartTwo.Sec4.psuConj_eq_one_iff (h := h) (A ^ 3)).1 hconj1
    rw [zPi_eq hπ0 hq0 hτ hτ1]
    exact Subgroup.mem_inf.2 ⟨pow_mem hA 3, hscal⟩
  have hAZ : (A : GL (Fin 3) K) ∉ zPi false 3 (2 ^ n) K := by
    intro hz
    rw [zPi_eq hπ0 hq0 hτ hτ1] at hz
    obtain ⟨-, c, hc⟩ := Subgroup.mem_inf.1 hz
    exact hxne (CFSG.RankThree.PartTwo.KFacts.psuConj_eq_one_of_coe_eq_scalar (A := A) hc.symm)
  have hmain := odd_card_gLAPPrimeCoreOf_fixSub_conjM' (π := false) (n := n)
    hK' hq hn2 hA hAZ hA3
  let e := psuEquivUnitary h
  have hxeq : MulAut.congr e
      (Res8Hess.conjM' (p := 2) (f := n) hπ0 hA) = psuConj h A := by
    simpa using L3PGL.congr_conjM'_false (h := h) (p := 2) (f := n) hπ0 hA
  have hZmodel : Subgroup.center (projImage (slPi false 3 (2 ^ n) K)) = ⊥ :=
    CFSG.RankThree.PartTwo.Sec13.center_projImage_slPi hK' hq hn2'
  have hZ : Subgroup.center (unitaryPSU h 3) = ⊥ := by
    rw [← Subgroup.map_center_eq e, hZmodel, Subgroup.map_bot]
  have hcore : Odd (Nat.card (GLAPPrimeCoreOf 3
      (((psuConj h A : MulAut (unitaryPSU h 3)) :
        unitaryPSU h 3 →* unitaryPSU h 3).eqLocus (MonoidHom.id _)))) := by
    have hfix := CFSG.eqLocus_congr_map e
      (Res8Hess.conjM' (p := 2) (f := n) hπ0 hA)
    rw [hxeq] at hfix
    rw [hfix]
    rw [CFSG.gLAPPrimeCoreOf_map_mulEquiv]
    rw [(Nat.card_congr (MulEquiv.subgroupMap e _).toEquiv).symm]
    exact hmain
  exact (CFSG.odd_card_gLAPPrimeCoreOf_innerAut_inf_centralizer_iff hZ 3
    (psuConj h A)).mpr hcore

end CFSG.LocalAnalysis.GLTheoremA.KD1912