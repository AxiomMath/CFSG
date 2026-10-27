
module

public import CFSG.Certificates.Kernel.Th.Spec.Sylow2Base
import all CFSG.Certificates.Kernel.Th.Spec.Sylow2Base

public import CFSG.Certificates.Kernel.Th.Gen.Sylow2
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Th.Spec.SylowOrbit
import CFSG.Certificates.Kernel.Th.Spec.FwdSlp
import CFSG.Certificates.Kernel.Th.Spec.Big
import CFSG.Certificates.Kernel.Th.Spec.DceMat
import CFSG.Certificates.Kernel.Th.Max3S.Basic
import CFSG.Certificates.Kernel.J4Hub.FlagSound
import CFSG.Sporadic.Th.Max3.AllConjBase1
import CFSG.Sporadic.Th.Max3.AllConjInputs
import CFSG.Sporadic.Th.Max3.CoreBase1
import CFSG.Sporadic.Th.Max3.InvolutionsBase1
import CFSG.Sporadic.Th.Max3.QuotientBase1
import CFSG.Sporadic.Th.Max3.QuotientInputs
import CFSG.Sporadic.ThSchreier.WordsBase1

public section

namespace CFSG.KC.Th.Spec.Sylow2

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Gen CFSG.KC.Th.Max3S CFSG.KC.Th.Spec
  CFSG.KC.Th.Spec.SylowOrbit CFSG.KC.Th.Spec.FwdRel CFSG.KC.Th.Spec.FwdSlp

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

private theorem pcSub_le_U (D : Sylow2Data) {J : Subgroup (GL (Fin 248) (ZMod 2))}
    {U : Subgroup J}
    (hU : U = Subgroup.closure {g : J | ∃ j < 11,
      𝕄 g = pkMat (D.ThS_RBp2 (regAt D.ThS_GL2 j))})
    (hmark : ∀ k < 15, RegIn U D.ThS_RBp2 (regAt D.ThS_PR2 k)) :
    pcSub J D.ThS_RBp2 D.ThS_PR2 0 15 ≤ U := by
  rw [hU] at hmark ⊢
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨k, -, hk15, eg⟩
  obtain ⟨u, hu, eu⟩ := hmark k hk15
  have hgu : u = g := mat_injective (eu.trans eg.symm)
  rw [← hgu]
  exact hu

private theorem regIn_pcSub (D : Sylow2Data) {J : Subgroup (GL (Fin 248) (ZMod 2))}
    (hslp : ∀ r, 0 < r → r < D.sf1 → RegIn (⊤ : Subgroup J) D.ThS_RBp2 r)
    (hpr2 : regsIn D.ThS_PR2 D.ThS_n2 D.sf1 = true) (hn2 : D.ThS_n2 = 15) :
    ∀ k < 15, RegIn (⊤ : Subgroup J) D.ThS_RBp2 (regAt D.ThS_PR2 k) := by
  intro k hk15
  have hk' : k < D.ThS_n2 := by omega
  have h := regsIn_spec hpr2 k hk'
  exact hslp _ h.1 h.2

private theorem mark_pcSub (D : Sylow2Data)
    (hk : constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4
      D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true)
    {J : Subgroup (GL (Fin 248) (ZMod 2))}
    (hslp : ∀ r, 0 < r → r < D.sf1 → RegIn (⊤ : Subgroup J) D.ThS_RBp2 r)
    (hslp1 : runSlp D.ThS_RBp2 D.ThS_c D.ThS_rm D.ThS_ONE D.cs1 3 = D.sf1)
    (hpos : 0 < runSlp D.ThS_RBp2 D.ThS_c D.ThS_rm D.ThS_ONE D.cs1 3)
    (hlt : runSlp D.ThS_RBp2 D.ThS_c D.ThS_rm D.ThS_ONE D.cs1 3 < 2048)
    (hprGL : regsIn D.ThS_GL2 11 D.sf1 = true) (hl0 : D.l0 = D.cs1)
    (hrmark : runMarked D.l0 9922901054488310019520462851 =
      356811923176489960380431918284599405230162057)
    (hall : allMarked D.ThS_PR2 15 174224571863520488467007772599902053335040 = true)
    (hGL2 : D.ThS_GL2 = 106488374662378949350121827748335640) :
    ∀ k < 15, RegIn (Subgroup.closure {g : J | ∃ j < 11,
      𝕄 g = pkMat (D.ThS_RBp2 (regAt D.ThS_GL2 j))}) D.ThS_RBp2
        (regAt D.ThS_PR2 k) := by
  let U : Subgroup J := Subgroup.closure {g : J | ∃ j < 11,
    𝕄 g = pkMat (D.ThS_RBp2 (regAt D.ThS_GL2 j))}
  have hUgen : ∀ j < 11, RegIn U D.ThS_RBp2 (regAt D.ThS_GL2 j) := by
    intro j hj
    have h := regsIn_spec hprGL j hj
    obtain ⟨g, -, eg⟩ := hslp _ h.1 h.2
    exact ⟨g, Subgroup.subset_closure ⟨j, hj, eg⟩, eg⟩
  rw [hGL2] at hUgen
  have hstart : ∀ k, marked 4845166530511870126718976 k = true →
      RegIn U D.ThS_RBp2 k := by
    intro k hkmark
    rw [marked_iff] at hkmark
    have hk83 : k < 83 := by
      by_contra hge
      have hle : 2 ^ 83 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hlt' : 4845166530511870126718976 < 2 ^ 83 := by norm_num
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt' hle)] at hkmark
      exact absurd hkmark (by decide)
    obtain ⟨j, hj, rfl⟩ := marked_GL2 k hk83 hkmark
    exact hUgen j hj
  have hrunEq : runMarked D.cs1 (3 + 2048 * 4845166530511870126718976) =
      356811923176489960380431918284599405230162057 := by
    rw [show 3 + 2048 * 4845166530511870126718976 = 9922901054488310019520462851
      from by norm_num, ← hl0]
    exact hrmark
  obtain ⟨-, hend⟩ := runMarked_induct (RB := D.ThS_RBp2) (c := D.ThS_c)
    (rm := D.ThS_rm) (ONE := D.ThS_ONE) (Q := fun r => RegIn U D.ThS_RBp2 r)
    (fun r a b ha hb e => regIn_mul hk ha hb e)
    (fun r a e ha _ he e' => regIn_pow hk ha he e')
    (fun r a ha e => regIn_inv hk ha e)
    D.cs1 3 4845166530511870126718976 hstart hpos hlt
  intro k hk15
  refine hend _ ?_
  rw [hrunEq]
  have hy := allMarked_of hall hk15
  rw [show 356811923176489960380431918284599405230162057 / 2048 =
    174224571863520488467007772599902053335040 from by norm_num]
  exact hy

private theorem pgroup_pcSub (D : Sylow2Data) {J : Subgroup (GL (Fin 248) (ZMod 2))}
    (hk : constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4
      D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true)
    (hcc : mulB D.ThS_c D.ThS_rm D.ThS_Cm2 D.ThS_Ci2 = D.ThS_ONE)
    (huni : uniOK D.ThS_RBp2 D.ThS_c D.ThS_rm D.ThS_up D.ThS_dg D.ThS_Cm2 D.ThS_Ci2
      D.ThS_GL2 11 = true)
    (hmark : ∀ k < 15, RegIn (Subgroup.closure {g : J | ∃ j < 11,
      𝕄 g = pkMat (D.ThS_RBp2 (regAt D.ThS_GL2 j))}) D.ThS_RBp2
        (regAt D.ThS_PR2 k)) :
    IsPGroup 2 (pcSub J D.ThS_RBp2 D.ThS_PR2 0 15) := by
  let U : Subgroup J := Subgroup.closure {g : J | ∃ j < 11,
    𝕄 g = pkMat (D.ThS_RBp2 (regAt D.ThS_GL2 j))}
  have hPleU : pcSub J D.ThS_RBp2 D.ThS_PR2 0 15 ≤ U := pcSub_le_U D rfl hmark
  exact (isPGroup_closure D hk hcc huni).to_le hPleU

private theorem div_seedMonoid (D : Sylow2Data) {J : Subgroup (GL (Fin 248) (ZMod 2))}
    (hJ : Nat.card J = Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1
      (String.ofList D.ThSeed_LA) (String.ofList D.ThSeed_LB))ˣ)
    (hlow : 2 ^ 15 ≤ Nat.card (pcSub J D.ThS_RBp2 D.ThS_PR2 0 15))
    (hpg : IsPGroup 2 (pcSub J D.ThS_RBp2 D.ThS_PR2 0 15)) :
    2 ^ 15 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1
      (String.ofList D.ThSeed_LA) (String.ofList D.ThSeed_LB))ˣ := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Finite (GL (Fin 248) (ZMod 2)) :=
    CFSG.KS.J4Hub.finite_GL (d := 248) (p := 2) (by norm_num)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hpg
  rw [hm] at hlow
  have h15m : 15 ≤ m := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hlow
  calc
    2 ^ 15 ∣ 2 ^ m := Nat.pow_dvd_pow 2 h15m
    _ = Nat.card (pcSub J D.ThS_RBp2 D.ThS_PR2 0 15) := hm.symm
    _ ∣ Nat.card J := Subgroup.card_subgroup_dvd_card _
    _ = Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1
          (String.ofList D.ThSeed_LA) (String.ofList D.ThSeed_LB))ˣ := hJ

theorem sylow2_facts (D : Sylow2Data) (h : sylow2Chk D = true) :
    2 ^ 15 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1
      (String.ofList D.ThSeed_LA) (String.ofList D.ThSeed_LB))ˣ := by
  have hk := constsOK_of D h
  obtain ⟨hdA, hdB, hA2, hB3, hrbf1, hrbf2⟩ := seeds_of D h
  obtain ⟨hslp1, hpr2, hprGL, hrbp1, hrbp2⟩ := slp_of D h
  obtain ⟨hrmark, hall⟩ := mark_of D h
  obtain ⟨hcc, huni⟩ := uni_of D h
  obtain ⟨hl0, hsf1lt, hGL2, hn2, hnb2⟩ := pinHead D h
  have hbl : blocksOK D.ThS_BL2 12 15 = true := by
    rw [← hnb2, ← hn2]
    exact blocks_of D h
  have hblk : ∀ b < 12, BlockOK D.ThS_RBp2 D.ThS_rm D.ThS_PR2 15 2 D.ThS_BL2 b := by
    intro b hb
    rcases Nat.lt_or_ge b 6 with h6 | h6
    · exact pins_blocks_lo D h b h6
    · exact pins_blocks_hi D h b h6 hb
  obtain ⟨J, hJ, a, b, ha, hb⟩ := exists_seedGroup hk hdA hdB hA2 hB3
  have ha' : 𝕄 a = pkMat (D.ThS_RBp2 1) := by
    rw [hrbp1, hrbf1]
    exact ha
  have hb' : 𝕄 b = pkMat (D.ThS_RBp2 2) := by
    rw [hrbp2, hrbf2]
    exact hb
  have hpos1 : 0 < D.sf1 := by
    have h0 := regsIn_spec hpr2 0 (by omega)
    exact lt_trans h0.1 h0.2
  have hpos : 0 < runSlp D.ThS_RBp2 D.ThS_c D.ThS_rm D.ThS_ONE D.cs1 3 := by
    rw [hslp1]
    exact hpos1
  have hlt : runSlp D.ThS_RBp2 D.ThS_c D.ThS_rm D.ThS_ONE D.cs1 3 < 2048 := by
    rw [hslp1]
    exact hsf1lt
  have hslp := regIn_of_runSlp hk ha' hb' hpos
  have hslp' : ∀ r, 0 < r → r < D.sf1 → RegIn (⊤ : Subgroup J) D.ThS_RBp2 r := by
    intro r hr hrs
    exact hslp r hr (by rw [hslp1]; exact hrs)
  have hR := regIn_pcSub D hslp' hpr2 hn2
  have hlow := pow_le_card_pcSub hk hR hbl hblk
  have hmark := mark_pcSub D hk hslp' hslp1 hpos hlt hprGL hl0 hrmark hall hGL2
  have hpg := pgroup_pcSub D hk hcc huni hmark
  exact div_seedMonoid D hJ hlow hpg

end CFSG.KC.Th.Spec.Sylow2

end
