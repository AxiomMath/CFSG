module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B6Mod
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0Norm
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B5Inv
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace B89

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}

theorem induces_of_mem_B (hE : Sec8E G t L S z g B E) {c : G} (hc : c ∈ B) : Induces B c 1 := by
  intro b
  rw [MulAut.one_apply]
  have h1 : c * (b : G) = (b : G) * c := E_comm hE (B_le_E hE hc) (B_le_E hE b.2)
  calc (b : G) = ((b : G) * c) * c⁻¹ := by group
    _ = (c * (b : G)) * c⁻¹ := by rw [h1]

theorem card_cent_E (hE : Sec8E G t L S z g B E) {y : G}
    (hy : y ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G)) :
    Nat.card ↥(E ⊓ centralizer ({y} : Set G)) = Nat.card {e : ↥E // rhoG hE y e = e} := by
  have key : ∀ e : ↥E, rhoG hE y e = e ↔ (e : G) ∈ centralizer ({y} : Set G) := by
    intro e
    have h1 := rhoG_apply_X hE (XCt_le_N hE hy) (Subgroup.mem_inf.mp hy).1 e
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h2 : y * (e : G) * y⁻¹ = e := by rw [← h1, h]
      calc (e : G) * y = (y * (e : G) * y⁻¹) * y := by rw [h2]
        _ = y * e := by group
    · intro h
      apply Subtype.ext
      rw [h1]
      calc y * (e : G) * y⁻¹ = ((e : G) * y) * y⁻¹ := by rw [h]
        _ = e := by group
  exact Nat.card_congr
    { toFun := fun e =>
        ⟨⟨e.1, (Subgroup.mem_inf.mp e.2).1⟩, (key _).mpr (Subgroup.mem_inf.mp e.2).2⟩
      invFun := fun e => ⟨e.1.1, Subgroup.mem_inf.mpr ⟨e.1.2, (key e.1).mp e.2⟩⟩
      left_inv := fun e => rfl
      right_inv := fun e => rfl }

theorem false_of_S6 (F : Sec8T84Base) (hE : Sec8E G t L S z g B E) (hMod : Sec8T84FactModB)
    (hS6 : Sec8T84FactS6)
    (hH0 : Nonempty (↥(autIn (centralizer ({t} : Set G)) B) ≃* Equiv.Perm (Fin 6))) : False := by
  have hctx := hE.ctx
  have hLt : L ≤ centralizer ({t} : Set G) := hctx.toSec3SettingLB.component.le
  have hle : autIn L B ≤ autIn (centralizer ({t} : Set G)) B := autIn_mono hLt
  have hH1 : Nonempty (↥(autIn L B) ≃* alternatingGroup (Fin 6)) := (A3.aut_B_of F hctx).1
  have c1 : Nat.card ↥(autIn L B) = 360 := by
    obtain ⟨ψ⟩ := hH1
    rw [Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have c0 : Nat.card ↥(autIn (centralizer ({t} : Set G)) B) = 720 := by
    obtain ⟨φ⟩ := hH0
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hnorm := T84Co.normal_of_orders hle c1 c0
  obtain ⟨x0, hx0H0, hx0H1, hx0sq, hx0card, w0, hw0H1, hw0cube, -, hxw, himg, hinter⟩ :=
    hS6 G B hctx.B_e16 (autIn L B) (autIn (centralizer ({t} : Set G)) B) hle hH1 hH0
  obtain ⟨x, hx, hxB⟩ := exists_lift F.h8A hE hx0H0
  obtain ⟨y, hy, hyB, hysq, hycard, hycomm⟩ := exists_y F hE hMod hnorm hx0sq hx0card hx hxB
  obtain ⟨w, hw, hwB⟩ := exists_lift F.h8A hE (hle hw0H1)
  have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
  have hyN : y ∈ Nsub8 t B := XCt_le_N hE hy
  have hρyy : rhoG hE (y * y) = 1 := by
    rw [rhoG_mul hE hyN hyN]
    exact hysq
  have hyc : y * y ∈ centralizer (E : Set G) :=
    mem_cent_of_rhoG_eq_one hE (mul_mem hy hy) hρyy
  obtain ⟨m, hm, hjj⟩ := exists_odd_pow_sq_mem_B F hE hyt hyc
  obtain ⟨k, hk⟩ := hm
  have hx0pow : x0 ^ m = x0 := by
    rw [hk, pow_succ, pow_mul, sq, hx0sq, one_pow, one_mul]
  have hρpow : rhoG hE y ^ m = rhoG hE y := by
    rw [hk, pow_succ, pow_mul, sq, hysq, one_pow, one_mul]
  have hj : y ^ m ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G) := pow_mem hy m
  have hjN : y ^ m ∈ Nsub8 t B := XCt_le_N hE hj
  have hjB : Induces B (y ^ m) x0 := by
    have h1 := hyB.pow m
    rwa [hx0pow] at h1
  have hρj : rhoG hE (y ^ m) = rhoG hE y := by
    rw [rhoG_pow hE hyN, hρpow]
  have hcomm_j : rhoG hE w * rhoG hE (y ^ m) = rhoG hE (y ^ m) * rhoG hE w := by
    rw [hρj]
    exact hycomm hxw w hw hwB
  obtain ⟨c, hcB, hinv⟩ := exists_inv F hE ⟨hw0cube, himg, hinter⟩ hj hw hjB hwB hjj hcomm_j
  have hcE : c ∈ E := B_le_E hE hcB
  have hy'X : y ^ m * c ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G) :=
    mul_mem hj (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hcE, B_le_Ct hE hcB⟩)
  have hy'B : Induces B (y ^ m * c) x0 := by
    have h1 := hjB.mul (induces_of_mem_B hE hcB)
    rwa [mul_one] at h1
  have hy'L : y ^ m * c ∉ L := fun h => hx0H1 (mem_autIn_of_induces h hy'B)
  have hy'ne : y ^ m * c ≠ 1 := fun h => hy'L (by rw [h]; exact one_mem L)
  have hord : orderOf (y ^ m * c) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hinv) hy'ne
  have hzL : z ∈ L := IsI4PlusIn.mem hctx.pocket
  have hy'z : y ^ m * c ∉ conjClassIn L z := by
    rintro ⟨l, hl, h⟩
    apply hy'L
    rw [h]
    exact mul_mem (mul_mem hl hzL) (inv_mem hl)
  have hρy' : rhoG hE (y ^ m * c) = rhoG hE y := by
    rw [rhoG_mul hE hjN (hE.le_N hcE), rhoG_of_mem_E hE hcE, mul_one, hρj]
  have hcard : Nat.card ↥(E ⊓ centralizer ({y ^ m * c} : Set G)) = 2 ^ 6 := by
    rw [card_cent_E hE hy'X, hρy']
    exact hycard
  have hrank := F.h88a G t L S z g B E hE (y ^ m * c) hord hy'X.2 hy'z
  have hel : CFSG.Open.IsElemAbelian 2 (E ⊓ centralizer ({y ^ m * c} : Set G)) :=
    CFSG.Open.IsElemAbelian.mono hE.elem.1 inf_le_left
  have hge := CFSG.SectionRank.le_pRank (p := 2) (by norm_num) (le_refl _) hel hcard
  omega

end B89

theorem asc82Lemma89_of (F : Sec8T84Base) (hE : Asc82FinkE) (hMod : Sec8T84FactModB)
    (hS6 : Sec8T84FactS6) : Asc82Lemma89 := by
  intro G _ _ t L S z g B hctx
  obtain ⟨E, hE'⟩ := hE G t L S z g B hctx
  obtain ⟨-, hH0⟩ := F.hAut G t L S z g B E hE'
  rcases hH0 with hA6 | hS6'
  · exact hA6
  · exact (B89.false_of_S6 F hE' hMod hS6 hS6').elim

end CFSG.OddStandard.SmallF3.Omega
