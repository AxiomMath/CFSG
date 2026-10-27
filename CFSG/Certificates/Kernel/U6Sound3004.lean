
module

public import CFSG.Certificates.Kernel.U6Sound3000
import all CFSG.Certificates.Kernel.U6Sound3010S
import all CFSG.Certificates.Kernel.U6Sound3000

namespace CFSG.KC.U6.Tk

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.U6.Snd CFSG.KC.U6.Pk

set_option exponentiation.threshold 70000

theorem sumN_eq_sum (f : ℕ → ℕ) : ∀ n, sumN n f = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← sumN_eq_sum f n]
    exact Nat.add_comm _ _

theorem tvP_spec (UP POS p : ℕ) : tvP UP POS p >>> 6930 = 0 ∧
    ∀ q < 693, ap10 (tvP UP POS p) q = tabK UP POS (up UP p) q := by
  have hc : ∀ q < 693, tabK UP POS (up UP p) q < 2 ^ 10 := fun q _ => fget_lt _ _ 10
  have e : tvP UP POS p = sumN 693 fun q => Nat.shiftLeft (tabK UP POS (up UP p) q) (Nat.mul 10 q) := by
    rw [tvP, strictN_eq, sumBelow_eq 693 11 _ (by norm_num), sumN_eq_sum]
  rw [e]
  exact ⟨shr_of_lt (sumN_fld 10 _ 693 hc).2, fun q hq => sumN_get hc hq⟩

end CFSG.KC.U6.Tk

public section

namespace CFSG.KC.U6

open CFSG.KC.S23 CFSG.KLie.CT CFSG.KC.M1F2 CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Th.Native

set_option exponentiation.threshold 70000

theorem sound3004 {UP POS LT BT : Nat} {L : List (Equiv.Perm (Fin 693))} {aw : List (List ℤ)}
    {aW : List (List Nat)} {bt pts pos : Array ℕ} (hL : LetsBind L LT) (hu : decA UP 12 693 = pts)
    (hp : decA POS 10 4096 = pos) (haW : aw = aW.map (List.map decZ))
    (hb : bindA BT 10 42 bt = true) (hlen : aW.length = 9) (hbt : ∀ i < 21, bt[i]! < 693)
    (hc : ∀ w ∈ aW, ∀ c ∈ w, c < 92) (hk : check3004 UP POS LT BT aW = true) :
    check3004G L aw bt pts pos := by
  open Pk Snd Tk in
  obtain ⟨hlenA, hA, hj1, -, -⟩ := rep_A hL haW hlen hc
  obtain ⟨-, hbtv⟩ := bindA_get hb
  have hT : ∀ i < 21, elt (orN 21 fun i => Nat.shiftLeft (tvP UP POS (fget BT i 10))
      (Nat.mul 6930 i)) i = tvP UP POS (fget BT i 10) :=
    fun i hi => elt_orN (fun i _ => (tvP_spec UP POS _).1) hi
  have htab : ∀ {P : ℕ} {g : Equiv.Perm (Fin 693)} {i : ℕ}, Rep P g → i < 21 →
      P = tvP UP POS (fget BT i 10) → tblEq 693 (toTable g) (tvTabsG pts pos)[bt[i]!]! = true := by
    intro P g i hg hi e
    rw [tblEq_iff]
    intro q hq
    have hb' : bt[i]! = fget BT i 10 := hbtv i (by omega)
    have hlt : fget BT i 10 < 693 := hb' ▸ hbt i hi
    rw [ap_toTable g hq, hb', (tab_ap hu hp hlt hq).2, ← (tvP_spec UP POS _).2 q hq, ← e,
      ap10_eq hg hq]
  unfold check3004 at hk
  simp only [strictB_eq, andB_iff, allN_iff, beq_iff] at hk
  obtain ⟨hall, h0⟩ := hk
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_getD hg
    rw [hlenA] at hj
    obtain ⟨i, hi, e⟩ := anyN_iff.1 (hall j hj)
    rw [beq_iff, hT i hi] at e
    rw [List.any_eq_true]
    exact ⟨i, List.mem_range.2 hi, htab (hA j hj) hi e⟩
  · rw [hT 5 (by norm_num)] at h0
    exact htab hj1 (by norm_num) h0

end CFSG.KC.U6

end
