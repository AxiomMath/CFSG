module

public import Certificates.Data.CFSGNative.ExcCensus.InLCommon
public import Certificates.Data.CFSGNative.ExcCensus.Nbr
public import Certificates.Data.Kernel.ExcExt.InLNbrTwin
public import CFSG.Certificates.Kernel.ExcExt.CensusSound
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtExcRefl
public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrFrameAut

public section

noncomputable section

namespace CFSG.ExcExtK

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw

@[expose] def decRefI : KRefI → Option Chk.RefL
  | .none => none
  | .zero => some .zero
  | .disc S => some (.disc S)
  | .cent w => some (.cent w)
  | .label => some .label
  | .q2 => some .q2
  | .outs φ => some (.outs φ)

@[expose] def isearchOf (m : Fin 6) (L : KILine) : Chk.ICSearch where
  S :=
    { line := fun cv => if cv = L.cv then decRefI L.ref else none
      plane := fun cv cy => (pickC (dim m) cv (3 ^ dim m) L.planes cy).bind fun P => decRefP P.ref
      cand := fun _ _ => none }
  common cv cy := (pickC (dim m) cv (3 ^ dim m) L.planes cy).bind fun P => decCommon P.body

theorem inl_refLIK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat}
    (hT : TabsOK m K fx hx fx' hx') {cv : Nat} {e : KRefI} (h : refLIK K cv e = true) :
    ∃ e', decRefI e = some e' ∧ Chk.refLOK (tabsK m K) m false true cv e' = true := by
  cases e with
  | none => exact Bool.noConfusion h
  | zero =>
    obtain ⟨e', he, hok⟩ := refLK_sound hT (e := .zero) h
    simp only [decRefL, Option.some.injEq] at he
    subst he
    exact ⟨_, rfl, hok⟩
  | disc S =>
    obtain ⟨e', he, hok⟩ := refLK_sound hT (e := .disc S) h
    simp only [decRefL, Option.some.injEq] at he
    subst he
    exact ⟨_, rfl, hok⟩
  | cent w =>
    obtain ⟨e', he, hok⟩ := refLK_sound hT (e := .cent w) h
    simp only [decRefL, Option.some.injEq] at he
    subst he
    exact ⟨_, rfl, hok⟩
  | label =>
    obtain ⟨e', he, hok⟩ := refLK_sound hT (e := .label) h
    simp only [decRefL, Option.some.injEq] at he
    subst he
    exact ⟨_, rfl, hok⟩
  | q2 =>
    obtain ⟨e', he, hok⟩ := refLK_sound hT (e := .q2) h
    simp only [decRefL, Option.some.injEq] at he
    subst he
    exact ⟨_, rfl, hok⟩
  | outs φ =>
    refine ⟨.outs φ, rfl, ?_⟩
    have h' : outK K (zmK K cv) φ cv = true := h
    rw [zmK_eq hT] at h'
    simp only [Chk.refLOK, Bool.not_false, Bool.true_and]
    exact cen_outK_sound hT h'

theorem inl_ibody_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat}
    (hT : TabsOK m K fx hx fx' hx') {L : KILine} {cy : Nat} {P : KCPlane}
    (hP : pickC (dim m) L.cv (3 ^ dim m) L.planes cy = some P)
    (h : ibodyK K L.cv cy P.body = true) :
    Chk.bodyIC (tabsK m K) m (isearchOf m L) L.cv cy = true := by
  cases hb : P.body with
  | common a b rows B n w Ll Lk Bl Bk =>
    rw [hb] at h
    have e : (isearchOf m L).common L.cv cy = some (a, b, decRows rows, decMat B,
        { w := decLin w, Lℓ := decDer Ll, Lk := decDer Lk, Bℓ := decMat Bl, Bk := decMat Bk }) := by
      simp only [isearchOf, hP, Option.bind_some, hb, decCommon]
    unfold Chk.bodyIC
    simp only [e]
    exact cen_cand_common hT h
  | twoL =>
    rw [hb] at h
    exact Bool.noConfusion h
  | twoNode _ _ _ _ _ _ =>
    rw [hb] at h
    exact Bool.noConfusion h
  | cands _ =>
    rw [hb] at h
    exact Bool.noConfusion h

theorem scanLineIK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat}
    (hT : TabsOK m K fx hx fx' hx') {L : KILine} (hcv : L.cv < 3 ^ dim m)
    (hL : scanLineIK K L = true) :
    Chk.scanLineN (tabsK m K) m false true (isearchOf m L).S
      (Chk.bodyIC (tabsK m K) m (isearchOf m L)) L.cv = true := by
  have hd := hT.hd
  have hL' : bor (refLIK K L.cv L.ref) (iwalkK K L.cv (Nat.pow 3 K.d) L.planes) = true := hL
  rw [bor_iff] at hL'
  rw [Chk.scanLineN, Bool.or_eq_true]
  rcases hL' with hL' | hL'
  · left
    obtain ⟨e, he, hok⟩ := inl_refLIK_sound hT hL'
    simp only [isearchOf, if_pos rfl, he]
    exact hok
  · right
    have hW : ∀ n ps, iwalkK K L.cv (n + 1) ps = Bool.rec (motive := fun _ => Bool)
        (iwalkK K L.cv n ps) (List.rec (motive := fun _ => Bool) false
          (fun P tl _ => band (Nat.beq P.cy n) (band (iplaneK K L.cv P) (iwalkK K L.cv n tl))) ps)
        (canonK (dim m) L.cv n) := by
      intro n ps
      rw [← hd]
      rfl
    rw [hd] at hL'
    rw [nat_all_iff]
    intro cy hcy
    rw [Bool.or_eq_true, Bool.or_eq_true]
    by_cases hc : Chk.canonN (dim m) L.cv cy = true
    · obtain ⟨P, hP, hPcy, hpl⟩ := cen_walk_sound hW hL' cy hcy hc
      have hP' : pickC (dim m) L.cv (3 ^ dim m) L.planes cy = some P := hP
      have hpl' : bor (refPK K L.cv P.cy P.ref) (ibodyK K L.cv P.cy P.body) = true := hpl
      rw [bor_iff, hPcy] at hpl'
      rcases hpl' with hr | hr
      · left
        right
        obtain ⟨e, he, hok⟩ := refPK_sound hT hr
        simp only [isearchOf, hP', Option.bind_some, he]
        exact hok
      · right
        exact inl_ibody_sound hT hP' hr
    · left
      left
      simp [hc]

@[expose] def decNbr : KNbr → Chk.NbrW
  | .small g L => .small g (decDer L)
  | .weyl w L => .weyl (decLin w) (decDer L)

@[expose] def nsearchOf (cs : List KComp) : Chk.NSearch where
  comps _ := cs.map fun C => (C.k, decNbr C.W)

theorem nbr_nbrWK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat}
    (hT : TabsOK m K fx hx fx' hx') {k : Nat} {W : KNbr} (h : nbrWK K k W = true) :
    Chk.nbrWOK (tabsK m K) m k (decNbr W) = true := by
  cases W with
  | small g L =>
    have h' : band (Nat.ble (cardK K.r g) 2) (genK K g k L) = true := h
    rw [band_eq_true, Nat.ble_eq, cardK_eq, hT.hr] at h'
    simp only [decNbr, Chk.nbrWOK]
    exact cen_and (decide_eq_true h'.1) (wk_gen hT h'.2)
  | weyl w L =>
    have h' : band (linK K w) (band (genK K (nodeMaskK w fun _ => true) k L) (notB2K K k)) =
        true := h
    simp only [band_eq_true] at h'
    obtain ⟨h1, h2, h3⟩ := h'
    simp only [decNbr, Chk.nbrWOK]
    refine cen_and (cen_and (wk_lin hT h1).1 ?_) ?_
    · rw [← wk_nodeMask w (p := fun _ => true) (q := fun _ => true) (fun _ => rfl)]
      exact wk_gen hT h2
    · rw [← wk_notB2 hT]
      exact h3

theorem nbr_compsK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat}
    (hT : TabsOK m K fx hx fx' hx') {z : Nat} :
    ∀ {cs : List KComp}, compsK K z cs = true → ∀ C ∈ cs,
      Chk.connN (tabsK m K) (nroots m) C.k = true ∧
      Chk.subN (Chk.trunc (nroots m) C.k) z = true ∧
      (Nat.all (nroots m) fun i _ => !C.k.testBit i || Chk.subN ((tabsK m K).adj[i]! &&& z) C.k) =
        true ∧
      Chk.nbrWOK (tabsK m K) m C.k (decNbr C.W) = true := by
  intro cs
  induction cs with
  | nil =>
    intro _ C hC
    simp at hC
  | cons D tl ih =>
    intro h C hC
    have h' : band (connK K D.k D.n) (band (subK (truncK K.r D.k) z)
        (band (allN K.r fun i => bor (bnot (bit D.k i)) (subK (Nat.land (adjK K i) z) D.k))
          (band (nbrWK K D.k D.W) (compsK K z tl)))) = true := h
    simp only [band_eq_true] at h'
    obtain ⟨h1, h2, h3, h4, h5⟩ := h'
    rcases List.mem_cons.mp hC with rfl | hC
    · refine ⟨cen_connK_sound hT h1, ?_, ?_, nbr_nbrWK_sound hT h4⟩
      · rw [subK_eq, truncK_eq, hT.hr] at h2
        exact h2
      · rw [hT.hr] at h3
        have e : allN (nroots m) (fun i => bor (bnot (bit C.k i)) (subK (Nat.land (adjK K i) z) C.k)) =
            Nat.all (nroots m) (fun i _ => !C.k.testBit i ||
              Chk.subN ((tabsK m K).adj[i]! &&& z) C.k) := by
          apply allN_eq_all
          intro i hi
          rw [bor_eq_or, bnot_eq, bit_eq, subK_eq, adjK_eq hT hi]
          rfl
        rw [e] at h3
        exact h3
    · exact ih h5 C hC

theorem nbr_coverK {t : Nat} :
    ∀ {cs : List KComp}, coverK t cs = true → ∃ C ∈ cs, C.k.testBit t = true := by
  intro cs
  induction cs with
  | nil =>
    intro h
    exact Bool.noConfusion h
  | cons D tl ih =>
    intro h
    have h' : bor (bit D.k t) (coverK t tl) = true := h
    rcases bor_iff.mp h' with h1 | h1
    · rw [bit_eq] at h1
      exact ⟨D, by simp, h1⟩
    · obtain ⟨C, hC, hb⟩ := ih h1
      exact ⟨C, List.mem_cons_of_mem _ hC, hb⟩

theorem nbrLineK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat}
    (hT : TabsOK m K fx hx fx' hx') {cv : Nat} (hcv : cv < 3 ^ dim m) {cs : List KComp}
    (h : nbrLineK K cv cs = true) : Chk.nbrLineOK (tabsK m K) m (nsearchOf cs) cv = true := by
  have h' : band (compsK K (zmK K cv) cs)
      (allN K.r fun t => bor (bnot (bit (zmK K cv) t)) (coverK t cs)) = true := h
  rw [band_eq_true] at h'
  obtain ⟨hc, hcov⟩ := h'
  have hc' := nbr_compsK_sound hT hc
  unfold Chk.nbrLineOK Chk.compsOK
  rw [← zmK_eq hT]
  simp only [nsearchOf, List.map_map]
  refine cen_and (cen_and ?_ ?_) ?_
  · rw [List.all_eq_true]
    intro k hk
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hk
    obtain ⟨h1, h2, h3, -⟩ := hc' C hC
    exact cen_and (cen_and h1 h2) h3
  · rw [nat_all_iff]
    intro t ht
    have := allN_iff.mp hcov t (by rw [hT.hr]; exact ht)
    rw [bor_iff, bnot_eq, bit_eq] at this
    rcases this with h1 | h1
    · exact cen_orL h1
    · refine cen_orR ?_
      rw [List.any_eq_true]
      obtain ⟨C, hC, hb⟩ := nbr_coverK h1
      exact ⟨_, List.mem_map.mpr ⟨C, hC, rfl⟩, hb⟩
  · rw [List.all_eq_true]
    intro e he
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp he
    exact (hc' C hC).2.2.2

theorem nbrWeylDataVx_reflection {m : Fin 6} {T : Chk.Tabs} (hT : Chk.tabsOK m T = true)
    (u : Root m) {v : V m} (h : NbrWeylDataVx (excRaw m) v) :
    NbrWeylDataVx (excRaw m) (reflection m u v) :=
  (reflFrameAut hT u).nbrWeylDataVx_map h

end CFSG.ExcExtK

end

end
