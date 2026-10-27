module

public import Certificates.Data.Kernel.Sp6Insp443.Sub
public import CFSG.Certificates.Kernel.KGC31PSound
public import CFSG.Certificates.Kernel.Sp6Insp443.CentSound
public import CFSG.Sporadic.Recognition.LyonsAmalgamInv

public section

namespace CFSG.KS.Sp6I

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.HeGlueK CFSG.KC.KGC31P
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.KGC31.Native CFSG.SectionRank.QTK.Insp443.PermKit.Native
open CFSG.KC.Child3 (tabP ap_tabP tabP_size)

variable {n w : Nat}

theorem rep_tabP {a : Nat} (ha : PP n w a) : Rep n (tabP n w a) (sg n w a) := by
  rw [tabP_eq ha]
  exact rep_toTable ha.lt32 _

theorem tabK_spec (hsz : szOK n w = true) {T : Table} (h : tabK n w T = true) :
    T = tabP n w (packT w T) ∧ PP n w (packT w T) := by
  unfold tabK at h
  rw [Orb.strictB_eq, Orb.bAnd_eq, Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hs, ht, hp⟩ := h
  have hn : n < 2 ^ 32 := by have := (szOK_facts' hsz).1; omega
  obtain ⟨g, hg⟩ := SporSch.MOC.exists_prep hp
  exact ⟨eq_tabP_of_rep hn (Nat.eq_of_beq_eq_true hs) (rep_of_tabPK hg ht) (imageList_of_prep hg),
    PP_of_permOK hsz hp⟩

theorem tabsK_spec (hsz : szOK n w = true) : ∀ {Ts : List Table}, tabsK n w Ts = true →
    Ts = (Ts.map (packT w)).map (tabP n w) ∧ ∀ a ∈ Ts.map (packT w), PP n w a
  | [], _ => ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
  | T :: Ts, h => by
    have h' : bAnd(tabK n w T, tabsK n w Ts) = true := h
    rw [Orb.bAnd_eq, Bool.and_eq_true] at h'
    obtain ⟨h1, h2⟩ := h'
    obtain ⟨e1, p1⟩ := tabK_spec hsz h1
    obtain ⟨e2, p2⟩ := tabsK_spec hsz h2
    refine ⟨?_, fun a ha => ?_⟩
    · rw [List.map_cons, List.map_cons, ← e1, ← e2]
    · rw [List.map_cons, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact p1
      · exact p2 a ha

theorem tabsOK_of_reps (hn : n < 2 ^ 32) {Ts : List Table}
    (h : ∀ T ∈ Ts, ∃ g : Equiv.Perm (Fin n), Rep n T g) : tabsOK n Ts = true := by
  unfold tabsOK
  rw [List.all_eq_true]
  intro T hT
  obtain ⟨g, hg⟩ := h T hT
  have hR := rep_invT_of_rep hn hg
  unfold tabOK
  refine allIn_eq_true.mpr fun i _ hi => ?_
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hg i hi]
  refine ⟨idx_lt _ hi, ?_⟩
  rw [hR _ (idx_lt _ hi), idx_inv_idx]

theorem tabsOK_tabP {bs : List Nat} (hb : ∀ b ∈ bs, PP n w b) (hn : n < 2 ^ 32) :
    tabsOK n (bs.map (tabP n w)) = true := by
  refine tabsOK_of_reps hn fun T hT => ?_
  obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hT
  exact ⟨_, rep_tabP (hb b hbm)⟩

theorem inSp_tabP (hsz : szOK n w = true) {bs : List Nat} (hb : ∀ b ∈ bs, PP n w b) {t : Nat}
    (ht : PP n w t) : inSp n (spanTabs n (bs.map (tabP n w))) (tabP n w t) = pinSp n w bs t := by
  rw [inSp, spanTabs_tabP hsz hb, pinSp]
  exact any_map_congr fun s hs => tblEq_tabP (PP_pspan hsz hb s hs) ht

theorem commAllT_tabP {bs : List Nat} (hb : ∀ b ∈ bs, PP n w b) {t : Nat} (ht : PP n w t) :
    commAllT n (bs.map (tabP n w)) (tabP n w t) = pcommL n w bs t := by
  rw [commAllT, pcommL]
  refine all_map_congr fun b hbb => ?_
  change tblEq n (compT n (tabP n w t) (tabP n w b)) (compT n (tabP n w b) (tabP n w t)) = _
  rw [compT_tabP' ht (hb b hbb), compT_tabP' (hb b hbb) ht,
    tblEq_tabP (ht.pc (hb b hbb)) ((hb b hbb).pc ht)]

theorem compEqN_tabP {t b u : Nat} (ht : PP n w t) (hb : PP n w b) (hu : PP n w u) :
    compEqN n (tabP n w t) (tabP n w b) (tabP n w u) = Nat.beq (pc n w t b) (pc n w u t) := by
  have e : compEqN n (tabP n w t) (tabP n w b) (tabP n w u) =
      compEq n (tabP n w t) (tabP n w b) (tabP n w u) := rfl
  rw [e, beq_PP (ht.pc hb) (hu.pc ht), pc, pc, sg_pcomp ht hb, sg_pcomp hu ht, Bool.eq_iff_iff,
    decide_eq_true_iff]
  exact CFSG.Quasithin.KGC31.compEq_iff (rep_tabP ht) (rep_tabP hb) (rep_tabP hu)

theorem conjIn_tabP (hsz : szOK n w = true) {bs cs : List Nat} (hb : ∀ b ∈ bs, PP n w b)
    (hc : ∀ c ∈ cs, PP n w c) {t : Nat} (ht : PP n w t) :
    conjIn n (bs.map (tabP n w)) (spanTabs n (cs.map (tabP n w))) (tabP n w t) =
      pconjL n w bs cs t := by
  rw [conjIn, pconjL, spanTabs_tabP hsz hc]
  exact all_map_congr fun b hbb => any_map_congr fun u hu =>
    compEqN_tabP ht (hb b hbb) (PP_pspan hsz hc u hu)

theorem spanEq_tabP (hsz : szOK n w = true) {bs cs : List Nat} (hb : ∀ b ∈ bs, PP n w b)
    (hc : ∀ c ∈ cs, PP n w c) :
    spanEq n (bs.map (tabP n w)) (cs.map (tabP n w)) = pspanEq n w bs cs := by
  rw [spanEq, pspanEq]
  congr 1
  · exact all_map_congr fun b hbb => inSp_tabP hsz hc (hb b hbb)
  · exact all_map_congr fun c hcc => inSp_tabP hsz hb (hc c hcc)

theorem invoOK_tabP (hsz : szOK n w = true) {a : Nat} (ha : PP n w a) :
    Native.invoOK n (tabP n w a) = Nat.beq (pc n w a a) (pidn n w) := by
  have hn := ha.lt32
  have hR := rep_tabP ha
  have e : Native.invoOK n (tabP n w a) =
      tblEq n (compT n (tabP n w a) (tabP n w a)) (idT n) := by
    rw [Bool.eq_iff_iff, Native.invoOK, tblEq, allIn_eq_true, allIn_eq_true]
    refine forall_congr' fun i => forall_congr' fun _ => forall_congr' fun hi => ?_
    rw [beq_iff_eq, beq_iff_eq, Rep.compT hR hR i hi, (Rep.idT hn : Rep n (idT n) (1 : Equiv.Perm (Fin n))) i hi,
      hR i hi, hR _ (idx_lt _ hi), idx_mul, idx_one]
  rw [e, compT_tabP' ha ha, idT_tabP hsz, tblEq_tabP (ha.pc ha) (PP.id hsz)]

theorem subOK_tabP (hsz : szOK n w = true) {us ws : List Nat} (hu : ∀ b ∈ us, PP n w b)
    (hw : ∀ b ∈ ws, PP n w b) :
    subOK n (us.map (tabP n w)) (ws.map (tabP n w)) = psubOK n w us ws := by
  have hn : n < 2 ^ 32 := by have := (szOK_facts' hsz).1; omega
  rw [subOK, psubOK, tabsOK_tabP hu hn, tabsOK_tabP hw hn, ebasisOK_tabP hsz hu,
    ebasisOK_tabP hsz hw, Bool.true_and, Bool.and_true]
  congr 1
  · congr 1
    exact all_map_congr fun b hbb => inSp_tabP hsz hw (hu b hbb)
  · exact all_map_congr fun b hbb => commAllT_tabP hu (hw b hbb)

theorem pinSp_of_hits {L ws rs : List Nat} (h : hitsL n w L ws rs = true) :
    ∀ b ∈ ws, pinSp n w L b = true := by
  unfold hitsL at h
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hl, h⟩ := h
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  have hi' : i < rs.length := by rw [← hl]; exact hi
  have hz : (ws[i], rs[i]) ∈ ws.zip rs := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [hl, hi'], by simp⟩
  have h1 := h _ hz
  rw [Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨hr, he⟩ := h1
  rw [pinSp, List.any_eq_true]
  refine ⟨pmask n w L rs[i], List.mem_map.mpr ⟨rs[i], List.mem_range.mpr hr, rfl⟩, he⟩

theorem PP_porb {m x xi t : Nat} (hx : PP n w x) (hxi : PP n w xi) (ht : PP n w t) :
    ∀ s ∈ porbTabs n w m x xi t, PP n w s := PP_porbTabs hx hxi ht

theorem irrOK_of_pirrW (hsz : szOK n w = true) {m x : Nat} {us ws : List Nat}
    {R : List (List Nat)} (hx : PP n w x) (hu : ∀ b ∈ us, PP n w b) (hw : ∀ b ∈ ws, PP n w b)
    (h : pirrW n w m x (pinv n w x) us ws R = true) :
    irrOK n m (tabP n w x) (invT n (tabP n w x)) (us.map (tabP n w)) (ws.map (tabP n w)) =
      true := by
  rw [invT_tabP hx]
  have hxi : PP n w (pinv n w x) := hx.pinv
  unfold irrOK
  simp only []
  rw [spanTabs_tabP hsz hw, List.all_map, List.all_eq_true]
  intro v hv
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
  have hpv := PP_pmask hsz ws hw k
  have hk' := List.all_eq_true.mp h k hk
  simp only [Function.comp_apply]
  rw [inSp_tabP hsz hu hpv, orbTabs_tabP hx hxi hpv, ← List.map_append]
  have hL : ∀ b ∈ us ++ porbTabs n w m x (pinv n w x) (pmask n w ws k), PP n w b := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hu b hb
    · exact PP_porb hx hxi hpv b hb
  rw [Bool.or_eq_true] at hk' ⊢
  rcases hk' with h1 | h1
  · exact Or.inl h1
  · refine Or.inr ?_
    rw [List.all_map, List.all_eq_true]
    intro b hb
    simp only [Function.comp_apply]
    rw [inSp_tabP hsz hL (hw b hb)]
    exact pinSp_of_hits h1 b hb

end CFSG.KS.Sp6I

end
