module

public import Certificates.Data.Kernel.Odd87CCK
public import CFSG.Certificates.Kernel.KGC31PBSound
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
public import Certificates.Data.CFSGNative.SmallOddCore.Check

public section

namespace CFSG.KC.Odd87CCK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.KGC31P CFSG.KC.Misc.ArrEnum CFSG.KC.BfsPin
open CFSG.Sporadic.Th.Native Certificates.Odd87F3
open CFSG.KC.Child3 (tabP)

variable {n w : Nat}

theorem PP_getD {G : List Nat} (hsz : szOK n w = true) (hG : ∀ g ∈ G, PP n w g) (i : Nat) :
    PP n w (G.getD i (pidn n w)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : G[i]? with
  | none => exact PP.id hsz
  | some g => exact hG g (List.mem_of_getElem? h)

theorem getD_map_tabP (hsz : szOK n w = true) (G : List Nat) (i : Nat) :
    (G.map (tabP n w)).getD i (idT n) = tabP n w (G.getD i (pidn n w)) := by
  rw [idT_tabP hsz, List.getD_map]

theorem PP_pevK {G GI : List Nat} (hsz : szOK n w = true) (hG : ∀ g ∈ G, PP n w g)
    (hGI : ∀ g ∈ GI, PP n w g) : ∀ wd, PP n w (pevK n w G GI wd)
  | [] => PP.id hsz
  | z :: wd => by
    rw [pevK]
    refine PP.pc ?_ (PP_pevK hsz hG hGI wd)
    split
    · exact PP_getD hsz hG _
    · exact PP_getD hsz hGI _

theorem evalT_tabP {G : List Nat} (hsz : szOK n w = true) (hG : ∀ g ∈ G, PP n w g) :
    ∀ wd, evalT n (G.map (tabP n w)) ((G.map (tabP n w)).map (invT n)) wd =
      tabP n w (pevK n w G (G.map (pinv n w)) wd) := by
  have hGI : ∀ g ∈ G.map (pinv n w), PP n w g := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
    exact (hG a ha).pinv
  have hinv : (G.map (tabP n w)).map (invT n) = (G.map (pinv n w)).map (tabP n w) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun g hg => invT_tabP (hG g hg)
  intro wd
  induction wd with
  | nil => exact idT_tabP hsz
  | cons z wd ih =>
    rw [evalT, ih, pevK, hinv]
    split
    · rw [getD_map_tabP hsz, compT_tabP' (PP_getD hsz hG _) (PP_pevK hsz hG hGI wd)]
    · rw [getD_map_tabP hsz, compT_tabP' (PP_getD hsz hGI _) (PP_pevK hsz hG hGI wd)]

theorem table_eq_tabP {T : Table} {X : Nat}
    (h : CFSG.Sporadic.SmallOddCore.Native.natArr T = CFSG.KS.Raw.unpack n w X) : T = tabP n w X := by
  have hs : T.size = n := by
    have := congrArg Array.size h
    simpa [CFSG.Sporadic.SmallOddCore.Native.natArr, CFSG.KS.Raw.unpack] using this
  apply Array.ext
  · rw [hs, CFSG.KC.Child3.tabP_size]
  · intro i h1 h2
    have hi : i < n := hs ▸ h1
    have e := congrArg (fun a => a[i]!) h
    simp only [CFSG.Sporadic.SmallOddCore.Native.natArr] at e
    rw [getElem!_pos _ i (by simpa using h1), Array.getElem_map] at e
    simp only [CFSG.KC.Child3.tabP, CFSG.ComponentClassification.J2Cover.arrTable,
      Array.getElem_ofFn]
    rw [← e]
    simp

theorem ccOK_of_ccK {G : List Nat} {orbs : List Orb} {cov : List (ℕ × List ℤ)}
    (hsz : szOK n w = true) (h : ccK n w G orbs cov = true) :
    ccOK n (G.map (tabP n w)) orbs cov = true := by
  unfold ccK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hperm, horbs⟩, hcov⟩ := h
  have hG : ∀ g ∈ G, PP n w g := fun g hg => pp_of_permB hsz (hperm g hg)
  have hGI : ∀ g ∈ G.map (pinv n w), PP n w g := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
    exact (hG a ha).pinv
  have hPv := PP_pevK hsz hG hGI
  have hev := evalT_tabP hsz hG
  have hap : ∀ wd, ∀ i < n, ap (evalT n (G.map (tabP n w)) ((G.map (tabP n w)).map (invT n)) wd) i =
      papK w (pevK n w G (G.map (pinv n w)) wd) i := fun wd i hi => by
    rw [hev, ap_tabP' (hPv wd) hi, papK]
  unfold ccOK
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
    exact invOK_tabP (hG a ha)
  · intro o ho
    have h1 := horbs o ho
    unfold orbK at h1
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_map] at h1
    obtain ⟨⟨⟨⟨hb, hy0⟩, hSG⟩, hNS⟩, hall⟩ := h1
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_map]
    refine ⟨⟨⟨⟨hb, hy0⟩, ?_⟩, ?_⟩, ?_⟩
    · rintro T ⟨wd, hwd, rfl⟩
      rw [hap wd _ hb]
      exact hSG _ ⟨wd, hwd, rfl⟩
    · rintro T ⟨wd, hwd, rfl⟩
      rw [hap wd _ hb]
      exact hNS _ ⟨wd, hwd, rfl⟩
    · intro y hy
      have hyn : y < n := List.mem_range.1 hy
      have e1 : (o.sg.map (evalT n (G.map (tabP n w)) ((G.map (tabP n w)).map (invT n)))).all
          (fun T => ap T y == y) =
          (o.sg.map (pevK n w G (G.map (pinv n w)))).all (fun T => papK w T y == y) := by
        rw [List.all_map, List.all_map]
        exact all_congr' fun wd _ => by simp only [Function.comp, hap wd y hyn]
      have e2 : (o.ns.map (evalT n (G.map (tabP n w)) ((G.map (tabP n w)).map (invT n)))).all
          (fun T => ap T y != y) =
          (o.ns.map (pevK n w G (G.map (pinv n w)))).all (fun T => papK w T y != y) := by
        rw [List.all_map, List.all_map]
        exact all_congr' fun wd _ => by simp only [Function.comp, hap wd y hyn]
      have := hall y hy
      rw [e1, e2]
      exact this
  · intro v hv
    have h1 := hcov v hv
    rcases hc : cov[v]? with _ | ⟨i, wd⟩
    · simp only [hc] at h1
      exact absurd h1 Bool.false_ne_true
    · rcases ho : orbs[i]? with _ | o
      · simp only [hc, ho] at h1
        exact absurd h1 Bool.false_ne_true
      · simp only [hc, ho, Bool.and_eq_true, decide_eq_true_eq] at h1 ⊢
        rw [hap wd _ h1.1]
        exact h1.2
