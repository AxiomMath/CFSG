module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3XSpec
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDSetting
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaCTwo
import all CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeParabolic

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Sporadic.Schreier

section Native


theorem rep_letterArr {k : ℕ} (hk : k < 46) : Rep 693 letterArrs[k]! (letter k hk) := by
  have h := co2Rep_of_rep (rep_letter k hk)
  have e1 : letterArrs[k]! = (letterT k).map UInt32.toNat := by
    rw [getElem!_pos letterArrs k (by simp [letterArrs, hk])]
    simp [letterArrs]
  rwa [e1]

theorem letter_inv {k : ℕ} (hk : k < 46) : (letter k hk)⁻¹ = letter k hk := by
  refine inv_eq_of_mul_eq_one_right (Equiv.ext fun i => ?_)
  simp only [letter, tab_eq, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  exact tableFun_tableFun (letterT_ok k hk) i

theorem u62Letters_getD {m : ℕ} (hm : m < 46) : u62Letters.getD m 1 = letter m hm := by
  rw [u62Letters, List.getD_eq_getElem _ _ (by simpa using hm)]
  simp

theorem rep_nativeWord : ∀ w : List ℤ, (∀ c ∈ w, 1 ≤ c.natAbs ∧ c.natAbs ≤ 46) →
    Rep 693 (w.foldr (fun c acc => compA 693 (letterArrs[c.natAbs - 1]!) acc) (idA 693))
      (evalCodes u62Letters w)
  | [], _ => by simpa [evalCodes] using (rep_idA (n := 693))
  | c :: w, hw => by
    have hc := hw c List.mem_cons_self
    have hw' : ∀ c' ∈ w, 1 ≤ c'.natAbs ∧ c'.natAbs ≤ 46 := fun c' h' =>
      hw c' (List.mem_cons_of_mem c h')
    have hlt : c.natAbs - 1 < 46 := by omega
    have hlet : (if 0 < c then u62Letters.getD (c.toNat - 1) 1
        else (u62Letters.getD ((-c).toNat - 1) 1)⁻¹) = letter (c.natAbs - 1) hlt := by
      split_ifs with hpos
      · have e1 : c.toNat - 1 = c.natAbs - 1 := by omega
        rw [u62Letters_getD (by omega)]
        congr 1
      · have e1 : (-c).toNat - 1 = c.natAbs - 1 := by omega
        rw [u62Letters_getD (by omega), letter_inv]
        congr 1
    rw [List.foldr_cons, evalCodes, hlet]
    exact rep_compA (rep_letterArr hlt) (rep_nativeWord w hw')


theorem uA_le_chA2 : uA ≤ chA2.grp := by
  rw [uA_eq]
  refine closure_le_of_mem fun g hg => ?_
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
  have hall : ∀ w' ∈ aWords, ∀ c ∈ w', 1 ≤ c.natAbs ∧ c.natAbs ≤ 46 := by decide
  have hcodes := hall w hw
  have hrep : Rep 693 (w.foldr (fun c acc => compA 693 (letterArrs[c.natAbs - 1]!) acc)
      (idA 693)) (u62W w) := by
    rw [u62W, tab_eq]
    exact rep_nativeWord w hcodes
  have hsift := (uA_valid.2.2.2.2.2.2.2 _ (List.mem_map.2 ⟨w, hw, rfl⟩)).2
  exact (mem_chA2_iff hrep).2 hsift

theorem uA_eq_chA2 : uA = chA2.grp :=
  Subgroup.eq_of_le_of_card_ge uA_le_chA2 (by rw [card_uA, card_chA2])

end Native

section Data

variable {G : Type} [Group G] {L : Subgroup G}

theorem toddA_eq_sA₂ (e : L ≃* T46) : Yamada.toddA (ToddParabolic.ofMulEquivT46 e) = sA₂ e := by
  ext x
  rw [Yamada.mem_toddA, sA₂, mem_toG]
  constructor
  · rintro ⟨hx, hA⟩
    refine ⟨e ⟨x, hx⟩, ?_, by simp [iotaG]⟩
    rw [← uA_eq_chA2]
    exact hA
  · rintro ⟨g, hg, rfl⟩
    refine ⟨iotaG_mem g, ?_⟩
    show embT46 e _ ∈ uA
    rw [uA_eq_chA2]
    have e1 : (⟨iotaG e g, iotaG_mem g⟩ : L) = e.symm g := rfl
    rw [e1]
    simpa [embT46] using hg

variable (e : L ≃* T46) (t : G)

@[expose] noncomputable def sec3DData : YamadaD.Data G where
  t := t
  L := L
  S := sS e
  z := gw e [14]
  A₁ := sA₁ e
  A₂ := sA₂ e
  A₃ := toG e chA3.grp
  A₄ := toG e chA4.grp
  X₁ := sX₁ e
  X₈ := toG e chX8.grp
  Λ := toG e chLam.grp
  Sig := toG e chSig.grp
  K₁ := sK₁ e
  K₂ := sK₂ e
  J := sJ e
  e := gw e [4, 17]
  w₂ := sw e 1
  w₂₃₂ := gw e [16, 17, 16]
  C₂ := Yamada.yamadaC2 (ToddParabolic.ofMulEquivT46 e) t
  u₁ := gw e [0]
  u₂ := gw e [1]
  a₀ := gw e [11]
  j₀ := sj₀ e
  x₃ := gw e [4]

end Data

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
