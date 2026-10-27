module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.OctadY
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.OctadLiftG

public section

namespace CFSG.EvenSporadicStandard.M24Std.Octad

open Subgroup

variable {G : Type} [Group G] [Finite G] {L B : Subgroup G} {z : G}

theorem Y_mul_self (hs : LocalSetting G L z) (hBL : B ≤ L) (hb : OctadBasics L B)
    (hl : LiftDataB L B) (hcase : ¬ egM B z ≤ centralizer ({z} : Set G)) {Y : Subgroup G}
    (hY : YStructB L B z Y) : ∀ y ∈ Y, y * y = 1 := by
  have hF := yFactsB_of hs hBL hb hY hcase
  rcases Y_sq_dichotomy hb hF with h | h
  · exact h
  · exfalso
    have : IsAbelianSub Y := ⟨abelian_of_sq_eq hF.phi_mul h⟩
    obtain ⟨e, s, t, heB, hinj, hsH, htH, hss, htt, hst, hse, hte⟩ := hl
    exact false_of_abelian_subgroup Y B hF.B_le (phiB z) hF.phi_mul hF.phi_mem
      (fun u hu => phiB_eq_one_of_mem hs hBL hu) hF.phi_ker hF.phi_surj hb.elem.2 hF.sq_mem
      (fun y hy hy2 => hF.phi_ker y hy (by rw [← h y hy]; exact hy2))
      (hb.card_B.trans (by norm_num)) e heB hinj s t
      (fun y hy => (hF.phi_conj s hsH y hy).1) (fun y hy => (hF.phi_conj t htH y hy).1)
      hss htt hst (fun y hy => (hF.phi_conj s hsH y hy).2)
      (fun y hy => (hF.phi_conj t htH y hy).2) hse hte

end CFSG.EvenSporadicStandard.M24Std.Octad
