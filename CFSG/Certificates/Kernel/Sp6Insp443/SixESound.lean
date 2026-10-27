module

public import CFSG.Certificates.Kernel.Sp6Insp443.SubSound
public import CFSG.Certificates.Kernel.Sp6Insp443.SixSound

public section

namespace CFSG.KS.Sp6I

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.HeGlueK CFSG.KC.KGC31P
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.KGC31.Native CFSG.SectionRank.QTK.Insp443.PermKit.Native
open CFSG.KC.Child3 (tabP)

variable {n w : Nat}

theorem getD_mapL {α β : Type} (f : α → β) (ds : List (List α)) (r : Nat) :
    (ds.map (List.map f)).getD r [] = (ds.getD r []).map f := by
  rw [← List.map_nil (f := f), List.getD_map]

theorem map_toNat_of_tabPK {T : Table} {p : Nat} (hs : T.size = n)
    (ht : tabPK n w (mask w) p T = true) : T.map UInt32.toNat = unpack n w p := by
  apply Array.ext
  · rw [Array.size_map, hs]
    exact (Array.size_ofFn).symm
  · intro i h1 h2
    have hi : i < n := by rw [Array.size_map, hs] at h1; exact h1
    have e1 := Orb.unpack_get (n := n) (w := w) (P := p) hi
    rw [getElem!_pos (unpack n w p) i h2] at e1
    rw [Array.getElem_map, e1, Nat.eq_of_beq_eq_true (Orb.allN_iff.1 ht i hi)]
    unfold CFSG.Sporadic.Th.Native.ap
    rw [getElem!_pos T i (by rw [hs]; exact hi)]

theorem PP_getD {ds : List (List Nat)} (hd : ∀ D ∈ ds, ∀ b ∈ D, PP n w b) (r : Nat) :
    ∀ b ∈ ds.getD r [], PP n w b := by
  intro b hb
  by_cases hr : r < ds.length
  · rw [List.getD_eq_getElem _ _ hr] at hb
    exact hd _ (List.getElem_mem hr) b hb
  · rw [List.getD_eq_default _ _ (by omega)] at hb
    exact absurd hb List.not_mem_nil

theorem swap01_lt {r : Nat} (hr : r < 6) : swap01 r < 6 := by
  unfold swap01
  split_ifs <;> omega

theorem sixCheckE_tabP (hsz : szOK n w = true) {ws hs : List Nat} {ds : List (List Nat)}
    {a g h : Nat} (hw : ∀ b ∈ ws, PP n w b) (hd : ∀ D ∈ ds, ∀ b ∈ D, PP n w b)
    (hh : ∀ b ∈ hs, PP n w b) (ha : PP n w a) (hg : PP n w g) (hh' : PP n w h)
    (hl : ds.length = 6) :
    sixCheckE n (ws.map (tabP n w)) (ds.map (List.map (tabP n w))) (hs.map (tabP n w))
      (tabP n w a) (tabP n w g) (tabP n w h) = psixE n w ws ds hs a g h := by
  have hn : n < 2 ^ 32 := by have := (szOK_facts' hsz).1; omega
  have hl' : (ds.map (List.map (tabP n w))).length = 6 := by rw [List.length_map, hl]
  have e3 : tabsOK n [tabP n w a, tabP n w g, tabP n w h] = true :=
    tabsOK_tabP (bs := [a, g, h]) (fun b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> assumption) hn
  have eD : ((ds.map (List.map (tabP n w))).all fun D => tabsOK n D && ebasisOK n D &&
      D.length == 4 && D.all fun b => inSp n (spanTabs n (ws.map (tabP n w))) b) =
      ds.all fun D => pebasis n w D && D.length == 4 && D.all fun b => pinSp n w ws b := by
    rw [List.all_map]
    refine all_congr' fun D hD => ?_
    simp only [Function.comp_apply]
    rw [tabsOK_tabP (hd D hD) hn, ebasisOK_tabP hsz (hd D hD), List.length_map, Bool.true_and,
      List.all_map]
    congr 1
    exact all_congr' fun b hb => inSp_tabP hsz hw (hd D hD b hb)
  have eH : (hs.map (tabP n w)).all (fun b => inSp n (spanTabs n (ws.map (tabP n w))) b) =
      hs.all fun b => pinSp n w ws b := by
    rw [List.all_map]
    exact all_congr' fun b hb => inSp_tabP hsz hw (hh b hb)
  have eR : ((List.range 6).all fun r => (List.range 6).all fun s =>
      r == s || !(spanEq n ((ds.map (List.map (tabP n w))).getD r [])
        ((ds.map (List.map (tabP n w))).getD s []))) =
      ((List.range 6).all fun r => (List.range 6).all fun s =>
        r == s || !(pspanEq n w (ds.getD r []) (ds.getD s []))) :=
    all_congr' fun r _ => all_congr' fun s _ => by
      rw [getD_mapL, getD_mapL, spanEq_tabP hsz (PP_getD hd r) (PP_getD hd s)]
  have eG : ((List.range 6).all fun r => conjIn n ((ds.map (List.map (tabP n w))).getD r [])
      (((ds.map (List.map (tabP n w))).map (spanTabs n)).getD (swap01 r) []) (tabP n w g)) =
      ((List.range 6).all fun r => pconjL n w (ds.getD r []) (ds.getD (swapR r) []) g) :=
    all_congr' fun r hr => by
      rw [getD_map_spanTabs hl' (swap01_lt (List.mem_range.mp hr)), getD_mapL, getD_mapL,
        conjIn_tabP hsz (PP_getD hd r) (PP_getD hd _) hg]
      rfl
  have eK : ((List.range 6).all fun r => conjIn n ((ds.map (List.map (tabP n w))).getD r [])
      (((ds.map (List.map (tabP n w))).map (spanTabs n)).getD ((r + 1) % 6) []) (tabP n w h)) =
      ((List.range 6).all fun r => pconjL n w (ds.getD r []) (ds.getD ((r + 1) % 6) []) h) :=
    all_congr' fun r _ => by
      rw [getD_map_spanTabs hl' (Nat.mod_lt _ (by norm_num)), getD_mapL, getD_mapL,
        conjIn_tabP hsz (PP_getD hd r) (PP_getD hd _) hh']
  unfold sixCheckE psixE
  simp only []
  rw [eD, eH, eR, eG, eK, e3, tabsOK_tabP hw hn, tabsOK_tabP hh hn, ebasisOK_tabP hsz hw,
    ebasisOK_tabP hsz hh, List.length_map, List.length_map, List.length_map, invoOK_tabP hsz ha,
    conjIn_tabP hsz hw hw ha, conjIn_tabP hsz hw hw hg, conjIn_tabP hsz hw hw hh',
    commAllT_tabP hh ha, commAllT_tabP hw ha]
  simp only [Bool.true_and, Bool.and_true]

end CFSG.KS.Sp6I

end
