
module

public import Certificates.Data.Kernel.L5.Sh0Gam
public import CFSG.Certificates.Kernel.L5.Sh0TSound

public section

namespace CFSG.Certificates.Kernel.L5S

open CFSG.Certificates.Kernel.PkCV CFSG.GH74.GLS.C3.Layer2.L5

theorem invArr_toArray (t : List Nat) : invArr t.toArray = (invTabL t).toArray := by
  unfold invArr invTabL
  simp only [KT.getD_toArray]

theorem getD_map_invArr (l : List (Array Nat)) {m : Nat} (hm : m < l.length) :
    (l.map invArr).getD m #[] = invArr (l.getD m #[]) := by
  induction l generalizing m with
  | nil => simp at hm
  | cons a l ih =>
    cases m with
    | zero => simp only [List.map_cons, List.getD_cons_zero]
    | succ m =>
      simp only [List.map_cons, List.getD_cons_succ]
      exact ih (by simpa using hm)

theorem gamInvTabs_getD_eq {m : Nat} (hm : m < 4) :
    gamInvTabs.getD m #[] = invArr (gamTabs.getD m #[]) := by
  have hx : xsData.length = 4 := rfl
  have hl : gamTabs.toList.length = 4 := by
    unfold gamTabs
    rw [List.toList_toArray, List.length_map, hx]
  unfold gamInvTabs
  rw [KT.getD_toArray, getD_map_invArr _ (by rw [hl]; exact hm), getD_toList]

section

variable (hc : sh0Chk = true) (hn : ((sh0C.map ev).map pcode).Nodup)
include hc hn

theorem evI_eq (x w : List Nat) : evI x w = evFromT tF x 0 w := by
  unfold evI evFrom evFromT
  simp only [mt0_getD_eq hc hn]

theorem wdChk_of (h : wdChkK = true) : wdChk = true := by
  rw [← h]
  unfold wdChk wdChkK
  simp only [evI_eq hc hn, Wd_getD_eq hc hn]
  rfl

theorem relsChk_of (hm : relK ∈ relsK) (h : relsChkK = true) : relsChk = true := by
  rw [← h]
  unfold relsChk relsChkK
  rw [relsL_all hc hn hm]
  simp only [evI_eq hc hn]
  rfl

theorem gamTabs_getD_eq {m : Nat} (hm : m < 4) : gamTabs.getD m #[] = (gamL m).toArray := by
  have h1 : gamTabs.getD m #[] = gamArr (xsData.getD m []) := by
    unfold gamTabs
    rw [KT.getD_toArray]
    interval_cases m <;> rfl
  have hx : xsData = xsK := rfl
  rw [h1, hx]
  unfold gamArr gamL
  refine congrArg List.toArray (List.map_congr_left fun j _ => ?_)
  rw [evI_eq hc hn, Wd_getD_eq hc hn]

theorem gamChk_eq {m : Nat} (hm : m < 4) : gamChk m = gamK m := by
  have hs : ssData = ssK := rfl
  simp only [gamChk, gamK, gamChkT, gamInvTabs_getD_eq hm, gamTabs_getD_eq hc hn hm,
    invArr_toArray, hs, conjI, conjIT, KT.getD_toArray, mt0_getD_eq hc hn, inv0_getD_eq hc hn]
  rfl

theorem gamChk_of (hk : ∀ m < 4, gamK m = true) : (List.range 4).all gamChk = true := by
  rw [List.all_eq_true]
  intro m hm
  rw [List.mem_range] at hm
  rw [gamChk_eq hc hn hm]
  exact hk m hm

end

end CFSG.Certificates.Kernel.L5S

end
