module

public import Certificates.Data.Kernel.S63K.GeoK
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Certificates.Kernel.SporSch.Co1MatLemmas
public import CFSG.Certificates.Kernel.S63K.PtLSound

public section

namespace CFSG.KC.S63K

open CFSG.D4Hex CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem allLt_eq_allN (n : ℕ) (f : ℕ → Bool) : allLt n f = allN n f := by
  rw [Bool.eq_iff_iff, allLt_iff, MatL.allN_iff]

variable {pts ptL : Array ℕ} {P L : ℕ → ℕ}

theorem hexPtsOK_eq (hP : ∀ i, pts[i]! = P i) (hs : pts.size = 7371) :
    hexPtsOK pts = ptsOKF P := by
  unfold hexPtsOK ptsOKF
  simp only [hP, hs, allLt_eq_allN]
  rfl

theorem hexIncOK_eq (hP : ∀ i, pts[i]! = P i) (hL : ∀ i, ptL[i]! = L i) :
    hexIncOK pts ptL = incOKF P L := by
  unfold hexIncOK incOKF hexOnLine onLineF
  simp only [hP, hL, allLt_eq_allN]

theorem hexMeetOK_eq (hP : ∀ i, pts[i]! = P i) (hL : ∀ i, ptL[i]! = L i) :
    hexMeetOK pts ptL = meetOKF P L := by
  unfold hexMeetOK meetOKF
  simp only [hP, hL, allLt_eq_allN]

theorem hexNbr_eq (hP : ∀ i, pts[i]! = P i) (hL : ∀ i, ptL[i]! = L i) (x : ℕ) :
    hexNbr pts ptL x = nbrF P L x := by
  unfold hexNbr nbrF
  simp only [hP, hL]

theorem hexLayOK_eq (hP : ∀ i, pts[i]! = P i) (hL : ∀ i, ptL[i]! = L i) {lay par : Array ℕ}
    {Ly Pr : ℕ → ℕ} (hly : ∀ i, lay[i]! = Ly i) (hpr : ∀ i, par[i]! = Pr i) (b : ℕ) :
    hexLayOK pts ptL b lay par = layOKF P L b Ly Pr := by
  unfold hexLayOK layOKF
  simp only [hly, hpr, hexNbr_eq hP hL, allLt_eq_allN]

theorem hexActOK_eq (hP : ∀ i, pts[i]! = P i) {g : Array ℕ} {G : ℕ → ℕ} (hg : ∀ i, g[i]! = G i)
    (y x : ℕ) : hexActOK pts g y x = actOKF P G y x := by
  unfold hexActOK actOKF hexLineMaps lineMapsF hexOnLine onLineF
  simp only [hP, hg]

theorem hexCycleOK_eq (hP : ∀ i, pts[i]! = P i) (hL : ∀ i, ptL[i]! = L i) {cy : Array ℕ}
    {C : ℕ → ℕ} (hc : ∀ i, cy[i]! = C i) (hs : cy.size = 12) :
    hexCycleOK pts ptL cy = cycleOKF P L C := by
  unfold hexCycleOK cycleOKF
  simp only [hc, hs, hexNbr_eq hP hL, allLt_eq_allN]
  rfl

theorem orbOKR_eq {N k root cnt : ℕ} {act : ℕ → ℕ → ℕ → Bool} {items : ℕ → Bool} {r : OrbRec}
    {O Pa La Ps : ℕ → ℕ} (hO : ∀ i, r.ord[i]! = O i) (hPa : ∀ i, r.par[i]! = Pa i)
    (hLa : ∀ i, r.lab[i]! = La i) (hPs : ∀ i, r.pos[i]! = Ps i) (h1 : r.ord.size = cnt)
    (h2 : r.par.size = cnt) (h3 : r.lab.size = cnt) :
    orbOKR N k act root cnt items r = orbOKRF N k act root cnt items O Pa La Ps := by
  unfold orbOKR orbOKRF
  simp only [hO, hPa, hLa, hPs, h1, h2, h3, allLt_eq_allN, beq_self_eq_true, Bool.true_and]

theorem lineKey_eq (hP : ∀ i, pts[i]! = P i) (v : ℕ) : lineKey pts v = keyF P v := by
  unfold lineKey keyF
  simp only [hP]

theorem hexActS_of (hP : ∀ i, pts[i]! = P i)
    (hinj : ∀ a < 2457, ∀ b < 2457, keyF P a = keyF P b → a = b) {A : Array (Array ℕ)}
    {j : ℕ} {G : ℕ → ℕ} (hg : ∀ i, (A[j]!)[i]! = G i) {x y : ℕ}
    (h : actSOKF P G x y = true) : hexActS pts (hexLineKeyMap pts) A j x = y := by
  unfold hexActS
  unfold actSOKF at h
  by_cases hx : x < 819
  · rw [if_pos hx] at h ⊢
    rw [hg]
    exact beq_iff_eq.1 h
  · rw [if_neg hx] at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hinj' : ∀ a < 2457, ∀ b < 2457, lineKey pts a = lineKey pts b → a = b := by
      intro a ha b hb e
      rw [lineKey_eq hP, lineKey_eq hP] at e
      exact hinj a ha b hb e
    have hk := keyMap_getD hinj' 3276 (v := y - 819) (by omega)
    rw [lineKey_eq hP] at hk
    rw [← h3] at hk
    unfold sortKeyF at hk
    simp only [hP, hg]
    rw [hk]
    omega

end CFSG.KC.S63K

end
