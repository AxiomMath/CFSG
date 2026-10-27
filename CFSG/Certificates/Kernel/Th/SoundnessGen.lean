module

public import CFSG.Certificates.Kernel.Th.SoundnessGenBase
import all CFSG.Certificates.Kernel.Th.SoundnessGenBase

public import CFSG.Certificates.Kernel.Th.Gen.Seed
public import CFSG.Certificates.Kernel.Th.Gen.Dce
public import CFSG.Certificates.Kernel.Th.Gen.Sylow2
public import CFSG.Certificates.Kernel.Th.Gen.Sylow3
public import CFSG.Certificates.Kernel.Th.Gen.Sylow5
public import CFSG.Certificates.Kernel.Th.Gen.Sylow7
public import CFSG.Certificates.Kernel.Th.Gen.Orders
public import CFSG.Certificates.Kernel.Th.Gen.Fwd
public import CFSG.Certificates.Kernel.Th.Gen.Gen
public import CFSG.Certificates.Kernel.Th.Gen.DceStruct
public import CFSG.Sporadic.Th.KernelInputs
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Common.Generalize
import CFSG.Certificates.Kernel.Th.Spec.Big
import CFSG.Certificates.Kernel.Th.Spec.Dce
import CFSG.Certificates.Kernel.Th.Spec.DceHsw
import CFSG.Certificates.Kernel.Th.Spec.Seed
import CFSG.Certificates.Kernel.Th.Spec.Orders
import CFSG.Certificates.Kernel.Th.Spec.GenS
import CFSG.Certificates.Kernel.Th.Spec.Fwd
import CFSG.Certificates.Kernel.Th.Spec.SylowAsm
import CFSG.Certificates.Kernel.Th.Spec.SylowOrbit
import CFSG.Certificates.Kernel.Th.Spec.DceStrMain
import CFSG.Certificates.Kernel.Th.Spec.Sylow2
import all CFSG.Sporadic.Th.Max3.AllConjBase1
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.ThSchreier.LocalData

public section

namespace CFSG.KC.Th.Soundness

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Kernel CFSG.Sporadic.Bridge CFSG.Sporadic.ThSchreier
  Pointwise CFSG.KC.Th.Gen

@[expose] def codeN (l : ℕ × Bool) : ℕ := 2 * l.1 + (if l.2 then 0 else 1)

@[expose] def wordNatN : List (ℕ × Bool) → ℕ
  | [] => 0
  | l :: w => codeN l + 256 * wordNatN w

@[expose] def entN (w : List (ℕ × Bool)) : ℕ := 4 * w.length + 4096 * wordNatN w

@[expose] def IsHsw (p : TauCeti.GroupPresentation) : Prop :=
  p.generatorCount = 8 ∧ (∀ r ∈ p.relatorLetters, r.length < 1024) ∧
    p.relatorLetters.map entN = Hsw.list

theorem wordNatN_map (w : List (Fin 8 × Bool)) :
    wordNatN (w.map fun l => (l.1.val, l.2)) = Hsw.wordNat w := by
  induction w with
  | nil => rfl
  | cons l w ih => simp only [List.map_cons, wordNatN, Hsw.wordNat, ih, codeN, Hsw.code]

theorem entN_map (w : List (Fin 8 × Bool)) : entN (w.map fun l => (l.1.val, l.2)) = Hsw.ent w := by
  simp only [entN, Hsw.ent, List.length_map, wordNatN_map]

open TauCeti in
theorem th_relator_lengths :
    (Sporadic.Thompson.relatorList.map fun r => r.toWord.length).all (· < 1024) = true := by
  simp only [Sporadic.Thompson.relatorList, Sporadic.Thompson.relatorsOne,
    Sporadic.Thompson.relatorsTwo, Sporadic.Thompson.relatorsThree, Sporadic.Thompson.relatorsFour,
    Sporadic.Thompson.relatorsFive, Sporadic.Thompson.relatorsSix, Relator.commInvInv, Relator.conj,
    Relator.div, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append,
    Relator.toWord_gen, Relator.toWord_inv, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_comm]
  decide

theorem isHsw_th : IsHsw TauCeti.SporadicName.Th.presentation := by
  have hp : TauCeti.SporadicName.Th.presentation = TauCeti.Sporadic.Thompson.presentation := rfl
  rw [hp]
  refine ⟨rfl, ?_, ?_⟩
  · intro r hr
    rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
      List.map_map, List.mem_map] at hr
    obtain ⟨t, ht, rfl⟩ := hr
    have h := List.all_eq_true.mp th_relator_lengths _
      (List.mem_map_of_mem (f := fun r => r.toWord.length) ht)
    simpa using h
  rw [TauCeti.GroupPresentation.relatorLetters_def, List.map_map, ← Hsw.relators_eq]
  congr 1
  funext w
  exact entN_map w

private theorem entN_eq_enT : entN = CFSG.KC.Th.Spec.Dce.enT := by
  have hw : ∀ w : List (ℕ × Bool), wordNatN w = CFSG.KC.Th.Spec.Dce.wdN w := by
    intro w
    induction w with
    | nil => rfl
    | cons l w ih => simp only [wordNatN, CFSG.KC.Th.Spec.Dce.wdN, ih, codeN,
        CFSG.KC.Th.Spec.Dce.cdL]
  funext w
  simp only [entN, CFSG.KC.Th.Spec.Dce.enT, hw]

theorem dce_sound_gen (p : TauCeti.GroupPresentation) (_hp : IsHsw p) (D : DceData)
    (_h : dceChk D = true) : Finite p.Group ∧ Nat.card p.Group ≤ thOrder := by
  obtain ⟨h1, h2, h3⟩ := _hp
  rw [entN_eq_enT] at h3
  exact CFSG.KC.Th.Spec.Dce.dce_sound_of_pres p h1 h2 h3 D _h

set_option maxRecDepth 100000 in
private theorem sylow3_conjs (D : Sylow3Data) (h : sylow3Chk D = true) :
    CFSG.KC.Th.BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4
        D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true ∧
      CFSG.KC.Th.SeedS.decOK D.ThSeed_SA D.ThSeed_LA = true ∧
      CFSG.KC.Th.SeedS.decOK D.ThSeed_SB D.ThSeed_LB = true ∧
      eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SA D.ThSeed_SA) D.ThS_ONE = true ∧
      eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SB D.ThSeed_SB) D.ThSeed_SB) D.ThS_ONE = true ∧
      eqN (D.ThS_RBf 1) D.ThSeed_SA = true ∧ eqN (D.ThS_RBf 2) D.ThSeed_SB = true ∧
      eqN (D.ThS_RBp3 1) (D.ThS_RBf 1) = true ∧ eqN (D.ThS_RBp3 2) (D.ThS_RBf 2) = true ∧
      eqN (CFSG.KC.Th.BigS.runSlp D.ThS_RBp3 D.ThS_c D.ThS_rm D.ThS_ONE D.cs1 3) D.sf1 = true ∧
      eqN (CFSG.KC.Th.BigS.runPc D.ThS_RBp3 D.ThS_PW3 D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_PR3
        10 3 2 D.cs2 1) D.sf2 = true ∧
      CFSG.KC.Th.BigS.pwOK D.ThS_RBp3 D.ThS_PW3 D.ThS_c D.ThS_rm D.ThS_PR3 D.sf5 3 = true ∧
      CFSG.KC.Th.BigS.regsIn D.ThS_PR3 D.ThS_n3 D.sf1 = true ∧
      eqN D.ThS_n3 10 = true ∧ eqN D.sf1 67 = true ∧ eqN D.sf2 11 = true ∧ eqN D.sf5 10 = true := by
  simp only [sylow3Chk, sylow3ChkGen, sylow3Pins, CFSG.KC.Th.Spec.SylowPc.sylow_andB_iff] at h
  tauto

private theorem sylow3_of_orbit (sA sB : String) (D : Sylow3Data)
    (_hA : sA = String.ofList D.ThSeed_LA) (_hB : sB = String.ofList D.ThSeed_LB)
    (_h : sylow3Chk D = true)
    (hlow : ∀ g : ℕ → (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1 sA sB)ˣ,
      (∀ k < 10, CFSG.KC.Th.Spec.SylowPc.unitsHom _ (g k) =
        CFSG.KC.Th.Spec.pkMat (D.ThS_RBp3 (CFSG.KC.Th.BigS.regAt D.ThS_PR3 k))) →
      3 ^ 10 ≤ Nat.card (CFSG.KC.Th.Spec.SylowPc.pcSub g 10 0)) :
    3 ^ 10 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1 sA sB)ˣ := by
  obtain ⟨hk, hdA, hdB, hAA, hBBB, hf1, hf2, hp1, hp2, hrun1, hrun2, hpw, hregs, hn, hs1,
    hs2, hs5⟩ := sylow3_conjs D _h
  have e1 := Nat.eq_of_beq_eq_true hrun1
  have e2 := Nat.eq_of_beq_eq_true hrun2
  have en : D.ThS_n3 = 10 := Nat.eq_of_beq_eq_true hn
  have es1 : D.sf1 = 67 := Nat.eq_of_beq_eq_true hs1
  have es2 : D.sf2 = 11 := Nat.eq_of_beq_eq_true hs2
  have es5 : D.sf5 = 10 := Nat.eq_of_beq_eq_true hs5
  have hpos : 0 < CFSG.KC.Th.BigS.runSlp D.ThS_RBp3 D.ThS_c D.ThS_rm D.ThS_ONE D.cs1 3 := by
    rw [e1, es1]
    norm_num
  rw [en, ← e1] at hregs
  rw [es5] at hpw
  have hrun2' : CFSG.KC.Th.BigS.runPc D.ThS_RBp3 D.ThS_PW3 D.ThS_c D.ThS_rm D.ThS_ONE
      D.ThS_PR3 10 3 2 D.cs2 1 = 10 + 1 := by
    rw [e2, es2]
  subst _hA _hB
  exact CFSG.KC.Th.Spec.SylowPc.sylow_sound_of_orbit hk (CFSG.KC.Th.Spec.SylowPc.pkMat_seed hdA)
    (CFSG.KC.Th.Spec.SylowPc.pkMat_seed hdB) (Nat.eq_of_beq_eq_true hAA)
    (Nat.eq_of_beq_eq_true hBBB)
    ((Nat.eq_of_beq_eq_true hp1).trans (Nat.eq_of_beq_eq_true hf1))
    ((Nat.eq_of_beq_eq_true hp2).trans (Nat.eq_of_beq_eq_true hf2)) hpos hregs (by norm_num)
    (by norm_num) hpw hrun2' hlow

set_option maxRecDepth 100000 in
private theorem sylow5_conjs (D : Sylow5Data) (h : sylow5Chk D = true) :
    CFSG.KC.Th.BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4
        D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true ∧
      CFSG.KC.Th.SeedS.decOK D.ThSeed_SA D.ThSeed_LA = true ∧
      CFSG.KC.Th.SeedS.decOK D.ThSeed_SB D.ThSeed_LB = true ∧
      eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SA D.ThSeed_SA) D.ThS_ONE = true ∧
      eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SB D.ThSeed_SB) D.ThSeed_SB) D.ThS_ONE = true ∧
      eqN (D.ThS_RBf 1) D.ThSeed_SA = true ∧ eqN (D.ThS_RBf 2) D.ThSeed_SB = true ∧
      eqN (D.ThS_RBp5 1) (D.ThS_RBf 1) = true ∧ eqN (D.ThS_RBp5 2) (D.ThS_RBf 2) = true ∧
      eqN (CFSG.KC.Th.BigS.runSlp D.ThS_RBp5 D.ThS_c D.ThS_rm D.ThS_ONE D.cs1 3) D.sf1 = true ∧
      eqN (CFSG.KC.Th.BigS.runPc D.ThS_RBp5 D.ThS_PW5 D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_PR5
        3 5 3 D.cs2 1) D.sf2 = true ∧
      CFSG.KC.Th.BigS.pwOK D.ThS_RBp5 D.ThS_PW5 D.ThS_c D.ThS_rm D.ThS_PR5 3 5 = true ∧
      CFSG.KC.Th.BigS.regsIn D.ThS_PR5 D.ThS_n5 D.sf1 = true ∧
      eqN D.ThS_n5 3 = true ∧ eqN D.sf1 39 = true ∧ eqN D.sf2 4 = true := by
  simp only [sylow5Chk, sylow5ChkGen, sylow5Pins, CFSG.KC.Th.Spec.SylowPc.sylow_andB_iff] at h
  tauto

private theorem sylow5_of_orbit (sA sB : String) (D : Sylow5Data)
    (_hA : sA = String.ofList D.ThSeed_LA) (_hB : sB = String.ofList D.ThSeed_LB)
    (_h : sylow5Chk D = true)
    (hlow : ∀ g : ℕ → (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1 sA sB)ˣ,
      (∀ k < 3, CFSG.KC.Th.Spec.SylowPc.unitsHom _ (g k) =
        CFSG.KC.Th.Spec.pkMat (D.ThS_RBp5 (CFSG.KC.Th.BigS.regAt D.ThS_PR5 k))) →
      5 ^ 3 ≤ Nat.card (CFSG.KC.Th.Spec.SylowPc.pcSub g 3 0)) :
    5 ^ 3 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1 sA sB)ˣ := by
  obtain ⟨hk, hdA, hdB, hAA, hBBB, hf1, hf2, hp1, hp2, hrun1, hrun2, hpw, hregs, hn, hs1,
    hs2⟩ := sylow5_conjs D _h
  have e1 := Nat.eq_of_beq_eq_true hrun1
  have e2 := Nat.eq_of_beq_eq_true hrun2
  have en : D.ThS_n5 = 3 := Nat.eq_of_beq_eq_true hn
  have es1 : D.sf1 = 39 := Nat.eq_of_beq_eq_true hs1
  have es2 : D.sf2 = 4 := Nat.eq_of_beq_eq_true hs2
  have hpos : 0 < CFSG.KC.Th.BigS.runSlp D.ThS_RBp5 D.ThS_c D.ThS_rm D.ThS_ONE D.cs1 3 := by
    rw [e1, es1]
    norm_num
  rw [en, ← e1] at hregs
  have hrun2' : CFSG.KC.Th.BigS.runPc D.ThS_RBp5 D.ThS_PW5 D.ThS_c D.ThS_rm D.ThS_ONE
      D.ThS_PR5 3 5 3 D.cs2 1 = 3 + 1 := by
    rw [e2, es2]
  subst _hA _hB
  exact CFSG.KC.Th.Spec.SylowPc.sylow_sound_of_orbit hk (CFSG.KC.Th.Spec.SylowPc.pkMat_seed hdA)
    (CFSG.KC.Th.Spec.SylowPc.pkMat_seed hdB) (Nat.eq_of_beq_eq_true hAA)
    (Nat.eq_of_beq_eq_true hBBB)
    ((Nat.eq_of_beq_eq_true hp1).trans (Nat.eq_of_beq_eq_true hf1))
    ((Nat.eq_of_beq_eq_true hp2).trans (Nat.eq_of_beq_eq_true hf2)) hpos hregs (by norm_num)
    (by norm_num) hpw hrun2' hlow

set_option maxRecDepth 100000 in
private theorem sylow7_conjs (D : Sylow7Data) (h : sylow7Chk D = true) :
    CFSG.KC.Th.BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4
        D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true ∧
      CFSG.KC.Th.SeedS.decOK D.ThSeed_SA D.ThSeed_LA = true ∧
      CFSG.KC.Th.SeedS.decOK D.ThSeed_SB D.ThSeed_LB = true ∧
      eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SA D.ThSeed_SA) D.ThS_ONE = true ∧
      eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm
        (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SB D.ThSeed_SB) D.ThSeed_SB) D.ThS_ONE = true ∧
      eqN (D.ThS_RBf 1) D.ThSeed_SA = true ∧ eqN (D.ThS_RBf 2) D.ThSeed_SB = true ∧
      eqN (D.ThS_RBp7 1) (D.ThS_RBf 1) = true ∧ eqN (D.ThS_RBp7 2) (D.ThS_RBf 2) = true ∧
      eqN (CFSG.KC.Th.BigS.runSlp D.ThS_RBp7 D.ThS_c D.ThS_rm D.ThS_ONE D.cs1 3) D.sf1 = true ∧
      eqN (CFSG.KC.Th.BigS.runPc D.ThS_RBp7 D.ThS_PW7 D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_PR7
        2 7 3 D.cs2 1) D.sf2 = true ∧
      CFSG.KC.Th.BigS.pwOK D.ThS_RBp7 D.ThS_PW7 D.ThS_c D.ThS_rm D.ThS_PR7 2 7 = true ∧
      CFSG.KC.Th.BigS.regsIn D.ThS_PR7 D.ThS_n7 D.sf1 = true ∧
      eqN D.ThS_n7 2 = true ∧ eqN D.sf1 36 = true ∧ eqN D.sf2 3 = true := by
  simp only [sylow7Chk, sylow7ChkGen, sylow7Pins, CFSG.KC.Th.Spec.SylowPc.sylow_andB_iff] at h
  tauto

private theorem sylow7_of_orbit (sA sB : String) (D : Sylow7Data)
    (_hA : sA = String.ofList D.ThSeed_LA) (_hB : sB = String.ofList D.ThSeed_LB)
    (_h : sylow7Chk D = true)
    (hlow : ∀ g : ℕ → (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1 sA sB)ˣ,
      (∀ k < 2, CFSG.KC.Th.Spec.SylowPc.unitsHom _ (g k) =
        CFSG.KC.Th.Spec.pkMat (D.ThS_RBp7 (CFSG.KC.Th.BigS.regAt D.ThS_PR7 k))) →
      7 ^ 2 ≤ Nat.card (CFSG.KC.Th.Spec.SylowPc.pcSub g 2 0)) :
    7 ^ 2 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1 sA sB)ˣ := by
  obtain ⟨hk, hdA, hdB, hAA, hBBB, hf1, hf2, hp1, hp2, hrun1, hrun2, hpw, hregs, hn, hs1,
    hs2⟩ := sylow7_conjs D _h
  have e1 := Nat.eq_of_beq_eq_true hrun1
  have e2 := Nat.eq_of_beq_eq_true hrun2
  have en : D.ThS_n7 = 2 := Nat.eq_of_beq_eq_true hn
  have es1 : D.sf1 = 36 := Nat.eq_of_beq_eq_true hs1
  have es2 : D.sf2 = 3 := Nat.eq_of_beq_eq_true hs2
  have hpos : 0 < CFSG.KC.Th.BigS.runSlp D.ThS_RBp7 D.ThS_c D.ThS_rm D.ThS_ONE D.cs1 3 := by
    rw [e1, es1]
    norm_num
  rw [en, ← e1] at hregs
  have hrun2' : CFSG.KC.Th.BigS.runPc D.ThS_RBp7 D.ThS_PW7 D.ThS_c D.ThS_rm D.ThS_ONE
      D.ThS_PR7 2 7 3 D.cs2 1 = 2 + 1 := by
    rw [e2, es2]
  subst _hA _hB
  exact CFSG.KC.Th.Spec.SylowPc.sylow_sound_of_orbit hk (CFSG.KC.Th.Spec.SylowPc.pkMat_seed hdA)
    (CFSG.KC.Th.Spec.SylowPc.pkMat_seed hdB) (Nat.eq_of_beq_eq_true hAA)
    (Nat.eq_of_beq_eq_true hBBB)
    ((Nat.eq_of_beq_eq_true hp1).trans (Nat.eq_of_beq_eq_true hf1))
    ((Nat.eq_of_beq_eq_true hp2).trans (Nat.eq_of_beq_eq_true hf2)) hpos hregs (by norm_num)
    (by norm_num) hpw hrun2' hlow

#kc_generalize OrdersGen (sA sB tA tB : String)
    using [CFSG.Sporadic.Th.Native.seedA ↦ sA, CFSG.Sporadic.Th.Native.seedB ↦ sB,
      CFSG.Blueprint.NativeSporadic.ThSeed1 ↦ tA, CFSG.Blueprint.NativeSporadic.ThSeed2 ↦ tB] :
  13 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Th ∧
    19 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Th ∧
    31 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Th ∧
    (a * b) ^ 19 = 1

theorem orders_sound_gen (sA sB : String) (D : OrdersData) (_hA : sA = String.ofList D.ThSeed_LA)
    (_hB : sB = String.ofList D.ThSeed_LB) (_h : ordersChk D = true) : OrdersGen sA sB sA sB := by
  subst _hA _hB
  intro _ _ _ _
  obtain ⟨h13, h19, h31, hab⟩ := CFSG.KC.Th.Spec.Orders.orders_facts D _h
  refine ⟨h13, h19, h31, ?_⟩
  apply Subtype.ext
  apply Units.ext
  simpa using hab

#kc_generalize FwdGen (sA sB tA tB : String) (p : TauCeti.GroupPresentation)
    using [CFSG.Sporadic.Th.Native.seedA ↦ sA, CFSG.Sporadic.Th.Native.seedB ↦ sB,
      CFSG.Blueprint.NativeSporadic.ThSeed1 ↦ tA, CFSG.Blueprint.NativeSporadic.ThSeed2 ↦ tB,
      TauCeti.SporadicName.presentation TauCeti.SporadicName.Th ↦ p]
    from [TauCeti.Sporadic.Thompson.presentation] :
  
    (∃ ψ : P →* J, (∀ i < 7, ψ (gen i) ∈ H ∧ ψ (gen i) • Wset = Wset) ∧
      ψ (gen 0) ^ 2 = 1 ∧ a ∈ ψ.range ∧ b ∈ ψ.range) ∧
    xJ • Wset = Wset ∧ yJ • Wset = Wset ∧ b • Wset ≠ Wset

#kc_generalize GenGen (sA sB tA tB : String)
    using [CFSG.Sporadic.Th.Native.seedA ↦ sA, CFSG.Sporadic.Th.Native.seedB ↦ sB,
      CFSG.Blueprint.NativeSporadic.ThSeed1 ↦ tA, CFSG.Blueprint.NativeSporadic.ThSeed2 ↦ tB] :
  
    GenFact fusionWord0' (Max3.q 0) ∧ GenFact fusionWord1' Max3.x

theorem dceStruct_sound_gen (p : TauCeti.GroupPresentation) (_hp : IsHsw p) (D : DceStructData)
    (_h : dceStructChk D = true) : DceStructGen p := by
  obtain ⟨h1, h2, h3⟩ := _hp
  rw [entN_eq_enT] at h3
  intro hcard
  have hK7 : Set.range (fun i : Fin 7 => presGen p ↑i) = presGen p '' {g | g < 7} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [hK7]
  exact CFSG.KC.Th.Spec.DceStr.struct_core (presGen p)
    (CFSG.KC.Th.Spec.Dce.hsw_rel_of_pres p h1 h2 h3) (CFSG.KC.Th.Spec.Dce.presGen_closure p h1) D
    _h hcard

theorem thSeeds_subst {G : String → String → Prop} (h : G Native.seedA Native.seedB) :
    G CFSG.Blueprint.NativeSporadic.ThSeed1 CFSG.Blueprint.NativeSporadic.ThSeed2 :=
  Eq.subst (motive := fun t => G t CFSG.Blueprint.NativeSporadic.ThSeed2) seedA_eq
    (Eq.subst (motive := fun t => G Native.seedA t) seedB_eq h)

theorem sylow2_sound_gen (sA sB : String) (D : Sylow2Data) (_hA : sA = String.ofList D.ThSeed_LA)
    (_hB : sB = String.ofList D.ThSeed_LB) (_h : sylow2Chk D = true) :
    2 ^ 15 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1 sA sB)ˣ := by
  subst _hA _hB
  exact CFSG.KC.Th.Spec.Sylow2.sylow2_facts D _h

set_option maxRecDepth 100000 in
private theorem sylow3_orbit_bound (D : Sylow3Data) (h : sylow3Chk D = true)
    (S : Submonoid (Matrix (Fin 248) (Fin 248) (ZMod 2))) :
    ∀ g : ℕ → Sˣ, (∀ k < 10, CFSG.KC.Th.Spec.SylowPc.unitsHom S (g k) =
      CFSG.KC.Th.Spec.pkMat (D.ThS_RBp3 (CFSG.KC.Th.BigS.regAt D.ThS_PR3 k))) →
      3 ^ 10 ≤ Nat.card (CFSG.KC.Th.Spec.SylowPc.pcSub g 10 0) := by
  simp only [sylow3Chk, sylow3ChkGen, sylow3Pins, CFSG.KC.Th.Spec.SylowPc.sylow_andB_iff] at h
  have hk := h.1.1.2.1.2.1
  have hbl := h.1.2.2.2.2.2.2
  have hn := h.2.1
  have hnb := h.2.2.1
  have pl0 := h.2.2.2.2.2.2.2.2.2.1
  have ph0 := h.2.2.2.2.2.2.2.2.2.2.1
  have pl1 := h.2.2.2.2.2.2.2.2.2.2.2.1
  have ph1 := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  have pl2 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ph2 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have pl3 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ph3 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ts0 := h.2.2.2.2.2.1
  have ts1 := h.2.2.2.2.2.2.1
  have ts2 := h.2.2.2.2.2.2.2.1
  have ts3 := h.2.2.2.2.2.2.2.2.1
  have pt0 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have pt1 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have pt2 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have pt3 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have bf0 := h.1.2.2.1.1.2
  have tr0 := h.1.1.1.1.2.2
  have so0 := h.1.1.1.2.1.1
  have co0 := h.1.2.2.1.2.1
  have bf1 := h.1.2.2.1.2.2.1
  have tr1 := h.1.1.1.2.1.2
  have so1 := h.1.1.1.2.2.1
  have co1 := h.1.2.2.1.2.2.2
  have bf2 := h.1.2.2.2.1.1
  have tr2 := h.1.1.1.2.2.2.1
  have so2 := h.1.1.1.2.2.2.2
  have co2 := h.1.2.2.2.1.2
  have bf3 := h.1.2.2.2.2.1
  have tr3 := h.1.1.2.1.1.1
  have so3 := h.1.1.2.1.1.2
  have co3 := h.1.2.2.2.2.2.1
  have en : D.ThS_n3 = 10 := Nat.eq_of_beq_eq_true hn
  have enb : D.ThS_nb3 = 4 := Nat.eq_of_beq_eq_true hnb
  have es5 : D.sf5 = 10 := Nat.eq_of_beq_eq_true ts1
  rw [en] at hbl
  have hblk : ∀ b < D.ThS_nb3, CFSG.KC.Th.Spec.SylowOrbit.BlockOK D.ThS_RBp3 D.ThS_rm D.ThS_PR3 10 3 D.ThS_BL3 b := by
    intro b hb
    rw [enb] at hb
    interval_cases b
    · unfold CFSG.KC.Th.Spec.SylowOrbit.BlockOK
      refine ⟨D.ThS_PT3_0, D.cs3, D.cs4, D.sf4, ?_, ?_, ?_, ?_, ?_⟩
      · exact Nat.le_of_ble_eq_true pt0
      · have h' := bf0
        rw [es5] at h'
        exact h'
      · have h1 : CFSG.KC.Th.Spec.SylowOrbit.blkFr D.ThS_BL3 0 = 0 := Nat.eq_of_beq_eq_true pl0
        have h2 : CFSG.KC.Th.Spec.SylowOrbit.blkTo D.ThS_BL3 0 = 6 := Nat.eq_of_beq_eq_true ph0
        refine (Nat.eq_of_beq_eq_true tr0).trans ?_
        rw [Nat.eq_of_beq_eq_true ts0, h1, h2] <;> norm_num
      · exact Nat.eq_of_beq_eq_true so0
      · exact Nat.eq_of_beq_eq_true co0
    · unfold CFSG.KC.Th.Spec.SylowOrbit.BlockOK
      refine ⟨D.ThS_PT3_1, D.cs5, D.cs6, D.sf6, ?_, ?_, ?_, ?_, ?_⟩
      · exact Nat.le_of_ble_eq_true pt1
      · have h' := bf1
        rw [es5] at h'
        exact h'
      · have h1 : CFSG.KC.Th.Spec.SylowOrbit.blkFr D.ThS_BL3 1 = 6 := Nat.eq_of_beq_eq_true pl1
        have h2 : CFSG.KC.Th.Spec.SylowOrbit.blkTo D.ThS_BL3 1 = 8 := Nat.eq_of_beq_eq_true ph1
        refine (Nat.eq_of_beq_eq_true tr1).trans ?_
        rw [Nat.eq_of_beq_eq_true ts1, h1, h2] <;> norm_num
      · exact Nat.eq_of_beq_eq_true so1
      · have h' := Nat.eq_of_beq_eq_true co1
        rw [es5] at h'
        exact h'
    · unfold CFSG.KC.Th.Spec.SylowOrbit.BlockOK
      refine ⟨D.ThS_PT3_2, D.cs7, D.cs8, D.sf8, ?_, ?_, ?_, ?_, ?_⟩
      · exact Nat.le_of_ble_eq_true pt2
      · have h' := bf2
        rw [es5] at h'
        exact h'
      · have h1 : CFSG.KC.Th.Spec.SylowOrbit.blkFr D.ThS_BL3 2 = 8 := Nat.eq_of_beq_eq_true pl2
        have h2 : CFSG.KC.Th.Spec.SylowOrbit.blkTo D.ThS_BL3 2 = 9 := Nat.eq_of_beq_eq_true ph2
        refine (Nat.eq_of_beq_eq_true tr2).trans ?_
        rw [Nat.eq_of_beq_eq_true ts2, h1, h2] <;> norm_num
      · exact Nat.eq_of_beq_eq_true so2
      · exact Nat.eq_of_beq_eq_true co2
    · unfold CFSG.KC.Th.Spec.SylowOrbit.BlockOK
      refine ⟨D.ThS_PT3_3, D.cs9, D.cs10, D.sf10, ?_, ?_, ?_, ?_, ?_⟩
      · exact Nat.le_of_ble_eq_true pt3
      · have h' := bf3
        rw [es5] at h'
        exact h'
      · have h1 : CFSG.KC.Th.Spec.SylowOrbit.blkFr D.ThS_BL3 3 = 9 := Nat.eq_of_beq_eq_true pl3
        have h2 : CFSG.KC.Th.Spec.SylowOrbit.blkTo D.ThS_BL3 3 = 10 := Nat.eq_of_beq_eq_true ph3
        refine (Nat.eq_of_beq_eq_true tr3).trans ?_
        rw [Nat.eq_of_beq_eq_true ts3, h1, h2] <;> norm_num
      · exact Nat.eq_of_beq_eq_true so3
      · exact Nat.eq_of_beq_eq_true co3
  intro g hg
  exact CFSG.KC.Th.Spec.SylowOrbit.pow_le_card_closure hk (CFSG.KC.Th.Spec.SylowPc.unitsHom_injective S) hg hbl hblk

theorem sylow3_sound_gen (sA sB : String) (D : Sylow3Data) (_hA : sA = String.ofList D.ThSeed_LA)
    (_hB : sB = String.ofList D.ThSeed_LB) (_h : sylow3Chk D = true) :
    3 ^ 10 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1 sA sB)ˣ := by
  exact sylow3_of_orbit sA sB D _hA _hB _h (sylow3_orbit_bound D _h _)

set_option maxRecDepth 100000 in
private theorem sylow5_orbit_bound (D : Sylow5Data) (h : sylow5Chk D = true)
    (S : Submonoid (Matrix (Fin 248) (Fin 248) (ZMod 2))) :
    ∀ g : ℕ → Sˣ, (∀ k < 3, CFSG.KC.Th.Spec.SylowPc.unitsHom S (g k) =
      CFSG.KC.Th.Spec.pkMat (D.ThS_RBp5 (CFSG.KC.Th.BigS.regAt D.ThS_PR5 k))) →
      5 ^ 3 ≤ Nat.card (CFSG.KC.Th.Spec.SylowPc.pcSub g 3 0) := by
  simp only [sylow5Chk, sylow5ChkGen, sylow5Pins, CFSG.KC.Th.Spec.SylowPc.sylow_andB_iff] at h
  have hk := h.1.1.2.1.1.2
  have hbl := h.1.2.2.2.2.2.2
  have hn := h.2.1
  have hnb := h.2.2.1
  have pl0 := h.2.2.2.2.2.2.2.2.1
  have ph0 := h.2.2.2.2.2.2.2.2.2.1
  have pl1 := h.2.2.2.2.2.2.2.2.2.2.1
  have ph1 := h.2.2.2.2.2.2.2.2.2.2.2.1
  have pl2 := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ph2 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ts0 := h.2.2.2.2.2.1
  have ts1 := h.2.2.2.2.2.2.1
  have ts2 := h.2.2.2.2.2.2.2.1
  have pt0 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have pt1 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have pt2 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have bf0 := h.1.2.2.1.2.1
  have tr0 := h.1.1.1.1.2.2
  have so0 := h.1.1.1.2.1.1
  have co0 := h.1.2.2.1.2.2
  have bf1 := h.1.2.2.2.1.1
  have tr1 := h.1.1.1.2.1.2
  have so1 := h.1.1.1.2.2.1
  have co1 := h.1.2.2.2.1.2
  have bf2 := h.1.2.2.2.2.1
  have tr2 := h.1.1.1.2.2.2
  have so2 := h.1.1.2.1.1.1
  have co2 := h.1.2.2.2.2.2.1
  have en : D.ThS_n5 = 3 := Nat.eq_of_beq_eq_true hn
  have enb : D.ThS_nb5 = 3 := Nat.eq_of_beq_eq_true hnb
  rw [en] at hbl
  have hblk : ∀ b < D.ThS_nb5, CFSG.KC.Th.Spec.SylowOrbit.BlockOK D.ThS_RBp5 D.ThS_rm D.ThS_PR5 3 5 D.ThS_BL5 b := by
    intro b hb
    rw [enb] at hb
    interval_cases b
    · unfold CFSG.KC.Th.Spec.SylowOrbit.BlockOK
      refine ⟨D.ThS_PT5_0, D.cs3, D.cs4, D.sf4, ?_, ?_, ?_, ?_, ?_⟩
      · exact Nat.le_of_ble_eq_true pt0
      · exact bf0
      · have h1 : CFSG.KC.Th.Spec.SylowOrbit.blkFr D.ThS_BL5 0 = 0 := Nat.eq_of_beq_eq_true pl0
        have h2 : CFSG.KC.Th.Spec.SylowOrbit.blkTo D.ThS_BL5 0 = 1 := Nat.eq_of_beq_eq_true ph0
        refine (Nat.eq_of_beq_eq_true tr0).trans ?_
        rw [Nat.eq_of_beq_eq_true ts0, h1, h2] <;> norm_num
      · exact Nat.eq_of_beq_eq_true so0
      · exact Nat.eq_of_beq_eq_true co0
    · unfold CFSG.KC.Th.Spec.SylowOrbit.BlockOK
      refine ⟨D.ThS_PT5_1, D.cs5, D.cs6, D.sf6, ?_, ?_, ?_, ?_, ?_⟩
      · exact Nat.le_of_ble_eq_true pt1
      · exact bf1
      · have h1 : CFSG.KC.Th.Spec.SylowOrbit.blkFr D.ThS_BL5 1 = 1 := Nat.eq_of_beq_eq_true pl1
        have h2 : CFSG.KC.Th.Spec.SylowOrbit.blkTo D.ThS_BL5 1 = 2 := Nat.eq_of_beq_eq_true ph1
        refine (Nat.eq_of_beq_eq_true tr1).trans ?_
        rw [Nat.eq_of_beq_eq_true ts1, h1, h2] <;> norm_num
      · exact Nat.eq_of_beq_eq_true so1
      · exact Nat.eq_of_beq_eq_true co1
    · unfold CFSG.KC.Th.Spec.SylowOrbit.BlockOK
      refine ⟨D.ThS_PT5_2, D.cs7, D.cs8, D.sf8, ?_, ?_, ?_, ?_, ?_⟩
      · exact Nat.le_of_ble_eq_true pt2
      · exact bf2
      · have h1 : CFSG.KC.Th.Spec.SylowOrbit.blkFr D.ThS_BL5 2 = 2 := Nat.eq_of_beq_eq_true pl2
        have h2 : CFSG.KC.Th.Spec.SylowOrbit.blkTo D.ThS_BL5 2 = 3 := Nat.eq_of_beq_eq_true ph2
        refine (Nat.eq_of_beq_eq_true tr2).trans ?_
        rw [Nat.eq_of_beq_eq_true ts2, h1, h2] <;> norm_num
      · exact Nat.eq_of_beq_eq_true so2
      · exact Nat.eq_of_beq_eq_true co2
  intro g hg
  exact CFSG.KC.Th.Spec.SylowOrbit.pow_le_card_closure hk (CFSG.KC.Th.Spec.SylowPc.unitsHom_injective S) hg hbl hblk

theorem sylow5_sound_gen (sA sB : String) (D : Sylow5Data) (_hA : sA = String.ofList D.ThSeed_LA)
    (_hB : sB = String.ofList D.ThSeed_LB) (_h : sylow5Chk D = true) :
    5 ^ 3 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1 sA sB)ˣ := by
  exact sylow5_of_orbit sA sB D _hA _hB _h (sylow5_orbit_bound D _h _)

set_option maxRecDepth 100000 in
private theorem sylow7_orbit_bound (D : Sylow7Data) (h : sylow7Chk D = true)
    (S : Submonoid (Matrix (Fin 248) (Fin 248) (ZMod 2))) :
    ∀ g : ℕ → Sˣ, (∀ k < 2, CFSG.KC.Th.Spec.SylowPc.unitsHom S (g k) =
      CFSG.KC.Th.Spec.pkMat (D.ThS_RBp7 (CFSG.KC.Th.BigS.regAt D.ThS_PR7 k))) →
      7 ^ 2 ≤ Nat.card (CFSG.KC.Th.Spec.SylowPc.pcSub g 2 0) := by
  simp only [sylow7Chk, sylow7ChkGen, sylow7Pins, CFSG.KC.Th.Spec.SylowPc.sylow_andB_iff] at h
  have hk := h.1.1.2.1.1.1
  have hbl := h.1.2.2.2.2.2
  have hn := h.2.1
  have hnb := h.2.2.1
  have pl0 := h.2.2.2.2.2.2.2.1
  have ph0 := h.2.2.2.2.2.2.2.2.1
  have pl1 := h.2.2.2.2.2.2.2.2.2.1
  have ph1 := h.2.2.2.2.2.2.2.2.2.2.1
  have ts0 := h.2.2.2.2.2.1
  have ts1 := h.2.2.2.2.2.2.1
  have pt0 := h.2.2.2.2.2.2.2.2.2.2.2.1
  have pt1 := h.2.2.2.2.2.2.2.2.2.2.2.2
  have bf0 := h.1.2.2.1.2.2
  have tr0 := h.1.1.1.2.1.1
  have so0 := h.1.1.1.2.1.2
  have co0 := h.1.2.2.2.1.1
  have bf1 := h.1.2.2.2.1.2
  have tr1 := h.1.1.1.2.2.1
  have so1 := h.1.1.1.2.2.2
  have co1 := h.1.2.2.2.2.1
  have en : D.ThS_n7 = 2 := Nat.eq_of_beq_eq_true hn
  have enb : D.ThS_nb7 = 2 := Nat.eq_of_beq_eq_true hnb
  rw [en] at hbl
  have hblk : ∀ b < D.ThS_nb7, CFSG.KC.Th.Spec.SylowOrbit.BlockOK D.ThS_RBp7 D.ThS_rm D.ThS_PR7 2 7 D.ThS_BL7 b := by
    intro b hb
    rw [enb] at hb
    interval_cases b
    · unfold CFSG.KC.Th.Spec.SylowOrbit.BlockOK
      refine ⟨D.ThS_PT7_0, D.cs3, D.cs4, D.sf4, ?_, ?_, ?_, ?_, ?_⟩
      · exact Nat.le_of_ble_eq_true pt0
      · exact bf0
      · have h1 : CFSG.KC.Th.Spec.SylowOrbit.blkFr D.ThS_BL7 0 = 0 := Nat.eq_of_beq_eq_true pl0
        have h2 : CFSG.KC.Th.Spec.SylowOrbit.blkTo D.ThS_BL7 0 = 1 := Nat.eq_of_beq_eq_true ph0
        refine (Nat.eq_of_beq_eq_true tr0).trans ?_
        rw [Nat.eq_of_beq_eq_true ts0, h1, h2] <;> norm_num
      · exact Nat.eq_of_beq_eq_true so0
      · exact Nat.eq_of_beq_eq_true co0
    · unfold CFSG.KC.Th.Spec.SylowOrbit.BlockOK
      refine ⟨D.ThS_PT7_1, D.cs5, D.cs6, D.sf6, ?_, ?_, ?_, ?_, ?_⟩
      · exact Nat.le_of_ble_eq_true pt1
      · exact bf1
      · have h1 : CFSG.KC.Th.Spec.SylowOrbit.blkFr D.ThS_BL7 1 = 1 := Nat.eq_of_beq_eq_true pl1
        have h2 : CFSG.KC.Th.Spec.SylowOrbit.blkTo D.ThS_BL7 1 = 2 := Nat.eq_of_beq_eq_true ph1
        refine (Nat.eq_of_beq_eq_true tr1).trans ?_
        rw [Nat.eq_of_beq_eq_true ts1, h1, h2] <;> norm_num
      · exact Nat.eq_of_beq_eq_true so1
      · exact Nat.eq_of_beq_eq_true co1
  intro g hg
  exact CFSG.KC.Th.Spec.SylowOrbit.pow_le_card_closure hk (CFSG.KC.Th.Spec.SylowPc.unitsHom_injective S) hg hbl hblk

theorem sylow7_sound_gen (sA sB : String) (D : Sylow7Data) (_hA : sA = String.ofList D.ThSeed_LA)
    (_hB : sB = String.ofList D.ThSeed_LB) (_h : sylow7Chk D = true) :
    7 ^ 2 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1 sA sB)ˣ := by
  exact sylow7_of_orbit sA sB D _hA _hB _h (sylow7_orbit_bound D _h _)

theorem fwd_sound_gen (sA sB : String) (p : TauCeti.GroupPresentation) (_hp : IsHsw p)
    (D : FwdData) (_hA : sA = String.ofList D.ThSeed_LA) (_hB : sB = String.ofList D.ThSeed_LB)
    (_h : fwdChk D = true) : FwdGen sA sB sA sB p := by
  subst _hA _hB
  obtain ⟨h1, h2, h3⟩ := _hp
  rw [entN_eq_enT] at h3
  intro _ _ _ _ _ _
  refine CFSG.KC.Th.Spec.Fwd.fwd_facts p h1 h2 h3 D _h _ _ ?_ ?_ ?_
  · rfl
  · rfl
  · intro _ _
    rfl

theorem gen_sound_gen (sA sB : String) (D : GenData) (_hA : sA = String.ofList D.ThSeed_LA)
    (_hB : sB = String.ofList D.ThSeed_LB) (_h : genChk D = true) : GenGen sA sB sA sB := by
  subst _hA _hB
  intro _ _ _ _
  exact CFSG.KC.Th.Spec.GenS.cGen_of_GL _ _ D _h rfl rfl

end CFSG.KC.Th.Soundness

end
