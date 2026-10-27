
module

public import Certificates.Data.Kernel.L34K
import CFSG.Certificates.Kernel.L34KSnd.Run
import CFSG.Certificates.Kernel.L34KSnd.Class
import CFSG.Certificates.Kernel.L34KSnd.Der
import CFSG.Certificates.Kernel.L34KSnd.DerData
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.HeSylKSound

public section

namespace CFSG.KC.L34K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.PSL3Four.Native
open CFSG.KLie.CT (fget)

@[expose] noncomputable def pts (n w N : Nat) (T : Nat → Nat) : Array Tab :=
  Array.ofFn (n := N) fun i => unpack n w (T i.val)

structure PinE (n w : Nat) (gs : Array Tab) (cap ng N L K ew : Nat) (G T E C S SI : Nat → Nat) :
    Prop where
  size : gs.size = ng
  bind : ∀ k < ng, gs[k]! = unpack n w (G k)
  perm : ∀ k < ng, permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k)) = true
  head : headK n w ng G T C K N (pidn n w) = true
  hN : N = L * K
  hL : 0 < L
  cap : N ≤ cap
  sl : ∀ s < K, pinSl n w ng G T E C S SI N L ew s = true

theorem enum_sound {n w : Nat} {gs : Array Tab} {cap ng N L K ew : Nat}
    {G T E C S SI : Nat → Nat} (P : PinE n w gs cap ng N L K ew G T E C S SI) :
    (enumBFS n gs cap).tabs = pts n w N T ∧ enumOK n gs (enumBFS n gs cap) = true := by
  have hh := P.head
  unfold headK at hh
  obtain ⟨hsz, hh⟩ := CFSG.KC.L34KSnd.andB_iff.1 hh
  obtain ⟨hG, hh⟩ := CFSG.KC.L34KSnd.andB_iff.1 hh
  obtain ⟨hT0, hh⟩ := CFSG.KC.L34KSnd.andB_iff.1 hh
  obtain ⟨hC0, hCK⟩ := CFSG.KC.L34KSnd.andB_iff.1 hh
  have hT0' : T 0 = pidn n w := Nat.eq_of_beq_eq_true hT0
  have hC0' : C 0 = 1 := Nat.eq_of_beq_eq_true hC0
  have hCK' : C K = N := Nat.eq_of_beq_eq_true hCK
  have hcan : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true :=
    CFSG.KC.L34KSnd.canon_of_canonSl P.hN P.hL fun s hs =>
      (CFSG.KC.L34KSnd.andB_iff.1 (P.sl s hs)).1
  have hinj := CFSG.KC.L34KSnd.inj_of_distSl P.hN P.hL fun s hs =>
    (CFSG.KC.L34KSnd.andB_iff.1 (CFSG.KC.L34KSnd.andB_iff.1 (P.sl s hs)).2).2
  have hrun : runFW ng (lstep n w G) T E ew N 0 1 = N := by
    have := CFSG.KC.L34KSnd.runFW_blocks L C K fun s hs =>
      (CFSG.KC.L34KSnd.andB_iff.1 (CFSG.KC.L34KSnd.andB_iff.1 (P.sl s hs)).2).1
    rw [hC0', hCK', ← P.hN] at this
    exact this
  have hGc : ∀ k < ng, canonK n w (mask w) (n * w) (G k) = true := fun k hk =>
    CFSG.KS.Raw.Orb.allN_iff.1 hG k hk
  have PW : CFSG.KC.L34KSnd.PinW n w ng N (lstep n w G) (leftStep n gs) T :=
    { canT := hcan
      inj := hinj
      step := fun j hj h hh => by
        unfold leftStep lstep
        rw [P.bind j hj]
        exact CFSG.KC.L34KSnd.comp_unpack' (hGc j hj) (hcan h hh) }
  have hroot : idTab n = unpack n w (T 0) := by
    rw [hT0']
    exact CFSG.KC.L34KSnd.idTab_unpack' hsz
  obtain ⟨h1, h2⟩ := CFSG.KC.L34KSnd.bfs_of_runW PW hrun hroot P.cap
  unfold enumBFS enumOK pts
  rw [P.size]
  exact ⟨h1, h2⟩

structure PinO (n w : Nat) (gs : Array Tab) (x : Tab) (cap ng N ew P0 : Nat)
    (G GI T E S SI : Nat → Nat) : Prop where
  size : gs.size = ng
  bind : ∀ k < ng, gs[k]! = unpack n w (G k)
  root : x = unpack n w P0
  ok : orbK n w ng G GI T E S SI N ew P0 = true
  cap : N ≤ cap

theorem orbit_sound {n w : Nat} {gs : Array Tab} {x : Tab} {cap ng N ew P0 : Nat}
    {G GI T E S SI : Nat → Nat} (P : PinO n w gs x cap ng N ew P0 G GI T E S SI) :
    (orbitBFS n gs (gs.map (invTab n)) x cap).tabs = pts n w N T ∧
      orbitOK n gs (gs.map (invTab n)) x (orbitBFS n gs (gs.map (invTab n)) x cap) = true := by
  have hh := P.ok
  unfold orbK at hh
  obtain ⟨-, hh⟩ := CFSG.KC.L34KSnd.andB_iff.1 hh
  obtain ⟨hG, hh⟩ := CFSG.KC.L34KSnd.andB_iff.1 hh
  obtain ⟨hGI, hh⟩ := CFSG.KC.L34KSnd.andB_iff.1 hh
  obtain ⟨hT0, hh⟩ := CFSG.KC.L34KSnd.andB_iff.1 hh
  obtain ⟨hcan, hh⟩ := CFSG.KC.L34KSnd.andB_iff.1 hh
  obtain ⟨hrun, hdist⟩ := CFSG.KC.L34KSnd.andB_iff.1 hh
  have hT0' : T 0 = P0 := Nat.eq_of_beq_eq_true hT0
  have hgen : ∀ k < ng, canonK n w (mask w) (n * w) (G k) = true ∧
      canonK n w (mask w) (n * w) (GI k) = true ∧ pcomp n w (mask w) (G k) (GI k) = pidn n w :=
    fun k hk => by
      obtain ⟨a, b⟩ := CFSG.KC.L34KSnd.andB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 hG k hk)
      exact ⟨a, CFSG.KS.Raw.Orb.allN_iff.1 hGI k hk, Nat.eq_of_beq_eq_true b⟩
  obtain ⟨hinv, hok⟩ := CFSG.KC.L34KSnd.invsOK_of_pcomp P.size P.bind hgen
  have hcan' : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true := fun i hi =>
    CFSG.KS.Raw.Orb.allN_iff.1 hcan i hi
  have hrun' : runFW ng (cstep n w G GI) T E ew N 0 1 = N := Nat.eq_of_beq_eq_true hrun
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      have e1 : runFW ng (cstep n w G GI) T E ew 0 0 1 = 1 := rfl
      omega
    · exact h0
  have hinj := CFSG.KC.L34KSnd.inj_of_distSl (L := N) (K := 1) (Nat.mul_one N).symm hN0
    fun s hs => by
      have e : s = 0 := by omega
      subst e
      exact hdist
  have PW : CFSG.KC.L34KSnd.PinW n w ng N (cstep n w G GI)
      (conjStep n gs (gs.map (invTab n))) T :=
    { canT := hcan'
      inj := hinj
      step := fun j hj h hh => by
        obtain ⟨hGj, hGIj, -⟩ := hgen j hj
        unfold conjStep conjTab cstep
        rw [P.bind j hj, hinv j hj, CFSG.KC.L34KSnd.comp_unpack' hGj (hcan' h hh),
          CFSG.KC.L34KSnd.comp_unpack' (canonK_pcomp hGj (hcan' h hh)) hGIj,
          CFSG.KC.L34KSnd.pcomp_assoc' hGj (hcan' h hh) hGIj] }
  have hroot : x = unpack n w (T 0) := by
    rw [P.root, hT0']
  obtain ⟨h1, h2⟩ := CFSG.KC.L34KSnd.bfs_of_runW PW hrun' hroot P.cap
  unfold orbitBFS orbitOK pts
  rw [P.size, Bool.and_eq_true]
  exact ⟨h1, hok, h2⟩

theorem normal_sound {n w ng ngS N NW : Nat} {gs gsS : Array Tab} {G GI GS T : Nat → Nat}
    (hg : gs.size = ng ∧ ∀ k < ng, gs[k]! = unpack n w (G k))
    (hs : gsS.size = ngS ∧ ∀ k < ngS, gsS[k]! = unpack n w (GS k))
    (h : normK n w ng G GI ngS GS N T NW = true) :
    normalOK n (pts n w N T) gs (gs.map (invTab n)) gsS = true := by
  unfold normK at h
  obtain ⟨h1, h23⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  obtain ⟨h2, h3⟩ := CFSG.KC.L34KSnd.andB_iff.1 h23
  have hgen : ∀ k < ng, canonK n w (mask w) (n * w) (G k) = true ∧
      canonK n w (mask w) (n * w) (GI k) = true ∧ pcomp n w (mask w) (G k) (GI k) = pidn n w :=
    fun k hk => by
      obtain ⟨a, b⟩ := CFSG.KC.L34KSnd.andB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h1 k hk)
      obtain ⟨c, d⟩ := CFSG.KC.L34KSnd.andB_iff.1 a
      exact ⟨c, d, Nat.eq_of_beq_eq_true b⟩
  have hS : ∀ i < ngS, canonK n w (mask w) (n * w) (GS i) = true := fun i hi =>
    CFSG.KS.Raw.Orb.allN_iff.1 h2 i hi
  obtain ⟨hinv, hok⟩ := CFSG.KC.L34KSnd.invsOK_of_pcomp hg.1 hg.2 hgen
  unfold normalOK pts
  simp only [Bool.and_eq_true]
  refine ⟨hok, CFSG.KS.BfsReplay.allBelow_iff.2 fun j hj =>
    CFSG.KS.BfsReplay.allBelow_iff.2 fun i hi => ?_⟩
  rw [hg.1] at hj
  rw [hs.1] at hi
  have hw := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h3 j hj) i hi
  rw [CFSG.KC.BfsPin.strictB_app, CFSG.KC.BfsPin.strictB_app] at hw
  obtain ⟨hpq, he⟩ := CFSG.KC.L34KSnd.andB_iff.1 hw
  obtain ⟨hp, hq⟩ := CFSG.KC.L34KSnd.andB_iff.1 hpq
  obtain ⟨e1, e2⟩ := CFSG.KC.L34KSnd.andB_iff.1 he
  obtain ⟨hGj, hGIj, -⟩ := hgen j hj
  have hGSi := hS i hi
  have c1 : conjTab n (unpack n w (G j)) (unpack n w (GI j)) (unpack n w (GS i)) =
      unpack n w (pcomp n w (mask w) (G j) (pcomp n w (mask w) (GS i) (GI j))) := by
    unfold conjTab
    rw [CFSG.KC.L34KSnd.comp_unpack' hGj hGSi,
      CFSG.KC.L34KSnd.comp_unpack' (canonK_pcomp hGj hGSi) hGIj,
      CFSG.KC.L34KSnd.pcomp_assoc' hGj hGSi hGIj]
  have c2 : conjTab n (unpack n w (GI j)) (unpack n w (G j)) (unpack n w (GS i)) =
      unpack n w (pcomp n w (mask w) (GI j) (pcomp n w (mask w) (GS i) (G j))) := by
    unfold conjTab
    rw [CFSG.KC.L34KSnd.comp_unpack' hGIj hGSi,
      CFSG.KC.L34KSnd.comp_unpack' (canonK_pcomp hGIj hGSi) hGj,
      CFSG.KC.L34KSnd.pcomp_assoc' hGIj hGSi hGj]
  rw [hinv j hj, hg.2 j hj, hs.2 i hi, Bool.and_eq_true, c1, c2]
  exact ⟨CFSG.KC.L34KSnd.found_pts (Nat.blt_eq.mp hp) (Nat.eq_of_beq_eq_true e1),
    CFSG.KC.L34KSnd.found_pts (Nat.blt_eq.mp hq) (Nat.eq_of_beq_eq_true e2)⟩

theorem rpass_sound {n w N L K : Nat} {gsS : Array Tab} {OA : Array (Array Tab)}
    {G T ON W : Nat → Nat} {OT : Nat → Nat → Nat}
    (hs : gsS.size = 3 ∧ ∀ k < 3, gsS[k]! = unpack n w (G k))
    (hGc : ∀ k < 3, canonK n w (mask w) (n * w) (G k) = true)
    (hO : OA.size = 4 ∧ ∀ o < 4, OA[o]! = pts n w (ON o) (OT o))
    (hc : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true) (hN : N = L * K)
    (h : ∀ s < K, rPassSl n w G T OT ON W L s = true) :
    centralOK n (pts n w N T) gsS = true ∧ coverOK n (pts n w N T) OA = true := by
  have key : ∀ k < N, ((allN 3 fun j => commPt n w (T k) (G j)) = true → T k = pidn n w) ∧
      (T k = pidn n w ∨ invPt n w (T k) = false ∨ ∃ o < 4, ∃ j < ON o, OT o j = T k) := by
    intro k hk
    have hL : 0 < L := by
      rcases Nat.eq_zero_or_pos L with h0 | h0
      · rw [hN, h0, Nat.zero_mul] at hk
        exact absurd hk (Nat.not_lt_zero _)
      · exact h0
    have hs' : k / L < K := by
      rw [hN] at hk
      exact Nat.div_lt_of_lt_mul hk
    have h1 := h (k / L) hs'
    unfold rPassSl at h1
    rw [CFSG.KC.BfsPin.strictB_app] at h1
    have h2 := CFSG.KS.Raw.Orb.allN_iff.1 h1 (k % L) (Nat.mod_lt _ hL)
    have e : Nat.add (Nat.mul L (k / L)) (k % L) = k := Nat.div_add_mod k L
    rw [e, CFSG.KC.BfsPin.strictB_app, CFSG.KC.BfsPin.strictB_app] at h2
    obtain ⟨h3, h4⟩ := CFSG.KC.L34KSnd.andB_iff.1 h2
    refine ⟨fun hcomm => ?_, ?_⟩
    · rcases CFSG.KC.L34KSnd.orB_iff.1 h3 with h5 | h5
      · cases hcomm.symm.trans (CFSG.KC.L34KSnd.notB_iff.1 h5)
      · exact Nat.eq_of_beq_eq_true h5
    · rcases CFSG.KC.L34KSnd.orB_iff.1 h4 with h5 | h5
      · exact Or.inl (Nat.eq_of_beq_eq_true h5)
      · rcases CFSG.KC.L34KSnd.orB_iff.1 h5 with h6 | h6
        · exact Or.inr (Or.inl (CFSG.KC.L34KSnd.notB_iff.1 h6))
        · rw [CFSG.KC.BfsPin.strictB_app, CFSG.KC.BfsPin.strictB_app,
            CFSG.KC.BfsPin.strictB_app] at h6
          obtain ⟨h7, h8⟩ := CFSG.KC.L34KSnd.andB_iff.1 h6
          obtain ⟨h9, h10⟩ := CFSG.KC.L34KSnd.andB_iff.1 h8
          exact Or.inr (Or.inr ⟨_, Nat.blt_eq.mp h7, _, Nat.blt_eq.mp h9,
            Nat.eq_of_beq_eq_true h10⟩)
  refine ⟨?_, ?_⟩
  · unfold centralOK pts
    refine CFSG.KS.BfsReplay.allBelow_iff.2 fun k hk => ?_
    rw [Array.size_ofFn] at hk
    rw [CFSG.KC.L34KSnd.pts_get hk, hs.1]
    have hab : (allBelow 3 fun i => comp n (unpack n w (T k)) gsS[i]! ==
        comp n gsS[i]! (unpack n w (T k))) = allN 3 (fun j => commPt n w (T k) (G j)) := by
      rw [Bool.eq_iff_iff, CFSG.KS.BfsReplay.allBelow_iff, CFSG.KS.Raw.Orb.allN_iff]
      refine forall_congr' fun i => imp_congr_right fun hi => ?_
      rw [hs.2 i hi, beq_iff_eq, CFSG.KC.L34KSnd.commPt_iff (hc k hk) (hGc i hi)]
    rw [hab]
    cases hb : allN 3 (fun j => commPt n w (T k) (G j))
    · rfl
    · rw [(key k hk).1 hb, ← CFSG.KC.L34KSnd.idTab_unpack' (CFSG.KC.L34KSnd.canon_sz (hc k hk))]
      simp
  · unfold coverOK pts
    refine CFSG.KS.BfsReplay.allBelow_iff.2 fun k hk => ?_
    rw [Array.size_ofFn] at hk
    rw [CFSG.KC.L34KSnd.pts_get hk]
    have hsz := CFSG.KC.L34KSnd.canon_sz (hc k hk)
    simp only [Bool.or_eq_true]
    rcases (key k hk).2 with h1 | h1 | ⟨o, ho, j, hj, e⟩
    · left; left
      rw [h1, ← CFSG.KC.L34KSnd.idTab_unpack' hsz]
      exact beq_self_eq_true _
    · left; right
      cases hb : (comp n (unpack n w (T k)) (unpack n w (T k)) == idTab n)
      · rfl
      · have h2 := (CFSG.KC.L34KSnd.invPt_iff (hc k hk)).2 (beq_iff_eq.1 hb)
        rw [h1] at h2
        cases h2
    · right
      rw [CFSG.KC.L34KSnd.anyBelow_iff]
      have ho' : o < OA.size := by
        rw [hO.1]
        exact ho
      refine ⟨o, ho', ?_⟩
      rw [CFSG.KC.L34KSnd.map_get indexOf ho', hO.2 o ho]
      unfold pts
      exact CFSG.KC.L34KSnd.found_pts hj e

theorem notIn_sound {n w N r : Nat} {T : Nat → Nat} {x : Tab} (hx : x = unpack n w r)
    (hr : canonK n w (mask w) (n * w) r = true)
    (hc : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true) (h : notInK N T r = true) :
    notInOK (pts n w N T) x = true := by
  subst hx
  unfold notInK at h
  rw [CFSG.KC.BfsPin.strictB_app] at h
  unfold notInOK pts
  refine CFSG.KS.BfsReplay.allBelow_iff.2 fun k hk => ?_
  rw [Array.size_ofFn] at hk
  rw [CFSG.KC.L34KSnd.pts_get hk, CFSG.KC.L34KSnd.beq_unpack (hc k hk) hr,
    CFSG.KC.L34KSnd.notB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h k hk)]
  rfl

theorem disjoint_sound {n w : Nat} {OA : Array (Array Tab)} {rs : Array Tab}
    {ON R : Nat → Nat} {OT : Nat → Nat → Nat}
    (hO : OA.size = 4 ∧ ∀ o < 4, OA[o]! = pts n w (ON o) (OT o))
    (hr : rs.size = 4 ∧ ∀ j < 4, rs[j]! = unpack n w (R j) ∧
      canonK n w (mask w) (n * w) (R j) = true)
    (hc : ∀ o < 4, ∀ i < ON o, canonK n w (mask w) (n * w) (OT o i) = true)
    (h : allN 4 (fun i => allN 4 fun j =>
      CFSG.KLie.CT.orB (Nat.beq i j) (notInK (ON i) (OT i) (R j))) = true) :
    (allBelow 4 fun i => allBelow 4 fun j => i == j || notInOK OA[i]! rs[j]!) = true := by
  refine CFSG.KS.BfsReplay.allBelow_iff.2 fun i hi =>
    CFSG.KS.BfsReplay.allBelow_iff.2 fun j hj => ?_
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h i hi) j hj
  rcases CFSG.KC.L34KSnd.orB_iff.1 h1 with h2 | h2
  · rw [Nat.eq_of_beq_eq_true h2]
    simp
  · rw [hO.2 i hi, (hr.2 j hj).1, notIn_sound (r := R j) rfl (hr.2 j hj).2 (hc i hi) h2,
      Bool.or_true]

theorem involution_sound {n w : Nat} {rs : Array Tab} {R : Nat → Nat}
    (hr : rs.size = 4 ∧ ∀ j < 4, rs[j]! = unpack n w (R j) ∧
      canonK n w (mask w) (n * w) (R j) = true)
    (h : allN 4 (fun i => CFSG.KLie.CT.andB
      (Nat.beq (pcomp n w (mask w) (R i) (R i)) (pidn n w))
      (CFSG.KLie.CT.notB (Nat.beq (R i) (pidn n w)))) = true) :
    (allBelow 4 fun i => comp n rs[i]! rs[i]! == idTab n && !(rs[i]! == idTab n)) = true := by
  refine CFSG.KS.BfsReplay.allBelow_iff.2 fun i hi => ?_
  obtain ⟨e, hR⟩ := hr.2 i hi
  obtain ⟨h2, h3⟩ := CFSG.KC.L34KSnd.andB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h i hi)
  have hsz := CFSG.KC.L34KSnd.canon_sz hR
  have h2' : pcomp n w (mask w) (R i) (R i) = pidn n w := Nat.eq_of_beq_eq_true h2
  rw [e, CFSG.KC.L34KSnd.comp_unpack' hR hR, h2', CFSG.KC.L34KSnd.idTab_unpack' hsz,
    CFSG.KC.L34KSnd.beq_unpack hR (CFSG.KC.L34KSnd.canon_pidn hsz),
    CFSG.KC.L34KSnd.notB_iff.1 h3]
  simp

theorem cent_sound {n w N r m : Nat} {T I CT : Nat → Nat} {x : Tab} (hx : x = unpack n w r)
    (hr : canonK n w (mask w) (n * w) r = true)
    (hc : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true) (h : centK n w N T r m I CT = true) :
    centTabs n (pts n w N T) x = pts n w m CT := by
  subst hx
  unfold centK at h
  rw [CFSG.KC.BfsPin.strictB_app] at h
  obtain ⟨hm, hI⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  have hIk : ∀ k < m, I k < N ∧ (k + 1 < m → I k < I (k + 1)) ∧
      commPt n w (T (I k)) r = true ∧ CT k = T (I k) := by
    intro k hk
    have h1 := CFSG.KS.Raw.Orb.allN_iff.1 hI k hk
    rw [CFSG.KC.BfsPin.strictB_app] at h1
    obtain ⟨h2, h3⟩ := CFSG.KC.L34KSnd.andB_iff.1 h1
    obtain ⟨h4, h5⟩ := CFSG.KC.L34KSnd.andB_iff.1 h3
    obtain ⟨h6, h7⟩ := CFSG.KC.L34KSnd.andB_iff.1 h5
    refine ⟨Nat.blt_eq.mp h2, fun hk1 => ?_, h6, Nat.eq_of_beq_eq_true h7⟩
    rcases CFSG.KC.L34KSnd.orB_iff.1 h4 with h8 | h8
    · exact absurd (Nat.eq_of_beq_eq_true h8) (by omega)
    · exact Nat.blt_eq.mp h8
  have hcnt : ((List.range N).filter fun i => commPt n w (T i) r).length = m := by
    rw [← CFSG.KC.HeAutK.cntR_eq]
    exact Nat.eq_of_beq_eq_true hm
  have hlist := CFSG.KC.L34KSnd.filter_range_eq_map (p := fun i => commPt n w (T i) r)
    (fun k hk => ⟨(hIk k hk).1, (hIk k hk).2.1, (hIk k hk).2.2.1⟩) hcnt
  have key : ∀ i ∈ List.range N,
      ((fun t => comp n t (unpack n w r) == comp n (unpack n w r) t) ∘
        fun i => unpack n w (T i)) i = (fun i => commPt n w (T i) r) i := fun i hi => by
    have hi' := List.mem_range.1 hi
    simp only [Function.comp_apply]
    rw [Bool.eq_iff_iff, beq_iff_eq, CFSG.KC.L34KSnd.commPt_iff (hc i hi') hr]
  unfold centTabs pts
  apply Array.ext'
  rw [Array.toList_filter, CFSG.KC.BfsPin.pts_toList (fun i => unpack n w (T i)),
    CFSG.KC.BfsPin.pts_toList (fun i => unpack n w (CT i)), List.filter_map,
    List.filter_congr key, hlist, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  simp only [Function.comp_apply]
  rw [(hIk k (List.mem_range.1 hk)).2.2.2]

theorem class_sound {n w m ns lab rep wit SZ : Nat} {CT CI Q P : Nat → Nat} {sizes : Array Nat}
    (hz : sizes.size = ns ∧ ∀ l < ns, sizes[l]! = fget SZ l 8)
    (hg : groupK n w m CT CI Q = true) (h : classK n w m CT CI P lab rep wit SZ ns = true) :
    classOK n (pts n w m CT) ((pts n w m CT).map (invTab n))
      (classData n (pts n w m CT) sizes) sizes = true :=
  CFSG.KC.L34KSnd.classOK_of_checks hz hg h

theorem der_sound {n w m m' IW W : Nat} {TT TI D PW CW : Nat → Nat} {A : Array Tab}
    (hA : ∀ x, x ∈ A.toList ↔ x ∈ (pts n w m TT).toList)
    (h : derK n w m TT TI m' D PW CW IW W = true) :
    derivedOK n A (A.map (invTab n)) (derivedData n A (A.map (invTab n))).1
        (derivedData n A (A.map (invTab n))).2 = true ∧
      (derivedData n A (A.map (invTab n))).1.size = m' ∧
      ∀ x, x ∈ (derivedData n A (A.map (invTab n))).1.toList ↔ x ∈ (pts n w m' D).toList :=
  CFSG.KC.L34KSnd.derivedOK_of_derK hA h (CFSG.KC.L34KSnd.derivedData_nodup n A _)
    (CFSG.KC.L34KSnd.derivedData_size n A _) (CFSG.KC.L34KSnd.derivedData_wit n A _)
    (CFSG.KC.L34KSnd.derivedData_complete n A _)

theorem size_pts (n w N : Nat) (T : Nat → Nat) : (pts n w N T).size = N := Array.size_ofFn

theorem andT {a b : Bool} (h : CFSG.KLie.CT.andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [CFSG.KLie.CT.andB]

theorem PinE.canon {n w : Nat} {gs : Array Tab} {cap ng N L K ew : Nat}
    {G T E C S SI : Nat → Nat} (P : PinE n w gs cap ng N L K ew G T E C S SI) :
    ∀ i < N, canonK n w (mask w) (n * w) (T i) = true := by
  intro i hi
  have hs : i / L < K := by
    rw [P.hN] at hi
    exact Nat.div_lt_of_lt_mul hi
  have h := (andT (P.sl _ hs)).1
  unfold canonSl at h
  have e : Nat.add (Nat.mul L (i / L)) (i % L) = i := Nat.div_add_mod i L
  have := allN_spec h (i % L) (Nat.mod_lt _ P.hL)
  rw [e] at this
  exact this

theorem PinE.canonG {n w : Nat} {gs : Array Tab} {cap ng N L K ew : Nat}
    {G T E C S SI : Nat → Nat} (P : PinE n w gs cap ng N L K ew G T E C S SI) :
    ∀ k < ng, canonK n w (mask w) (n * w) (G k) = true := by
  have h := P.head
  unfold headK at h
  exact allN_spec (andT (andT h).2).1

theorem PinO.canon {n w : Nat} {gs : Array Tab} {x : Tab} {cap ng N ew P0 : Nat}
    {G GI T E S SI : Nat → Nat} (P : PinO n w gs x cap ng N ew P0 G GI T E S SI) :
    ∀ i < N, canonK n w (mask w) (n * w) (T i) = true := by
  have h := P.ok
  unfold orbK at h
  exact allN_spec (andT (andT (andT (andT (andT h).2).2).2).2).1

end CFSG.KC.L34K

end
