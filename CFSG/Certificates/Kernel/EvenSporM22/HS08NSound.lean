module

public import Certificates.Data.Kernel.EvenSporM22.HS08NDefs
public import CFSG.Certificates.Kernel.EvenSporM22.HS08DSound

public section

namespace CFSG.KC.EvenSporM22

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.EvenSporadicStandard.M22Std.HS08Check

theorem hs08idTab_valid : hs08TabV idTab = true := by
  decide

theorem hs08idTab_tmul {a : Tab} (ha : hs08TabV a = true) : tmul idTab a = a := by
  obtain ⟨A, rfl⟩ := hs08exists_tabF ha
  rw [← hs08TabF_id, ← hs08TabF_comp]
  rfl

theorem hs08span_pred (Q : Tab → Prop) (hid : Q idTab)
    (hmul : ∀ a b, hs08TabV a = true → hs08TabV b = true → Q a → Q b → Q (tmul a b)) :
    ∀ {gs : List Tab}, (∀ g ∈ gs, hs08TabV g = true ∧ Q g) →
      ∀ t ∈ span gs, hs08TabV t = true ∧ Q t
  | [], _, t, ht => by
    rw [span, List.mem_singleton] at ht
    rw [ht]
    exact ⟨hs08idTab_valid, hid⟩
  | g :: gs, hg, t, ht => by
    have hgs : ∀ g' ∈ gs, hs08TabV g' = true ∧ Q g' := fun g' h => hg g' (List.mem_cons_of_mem _ h)
    rw [span, ext, List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨t', ht', rfl⟩
    · exact hs08span_pred Q hid hmul hgs t ht
    · have h0 := hg g List.mem_cons_self
      have h1 := hs08span_pred Q hid hmul hgs t' ht'
      exact ⟨hs08tmul_valid h0.1 h1.1, hmul _ _ h0.1 h1.1 h0.2 h1.2⟩

theorem hs08dTabs_pred (Q : Tab → Prop) (hid : Q idTab)
    (hmul : ∀ a b, hs08TabV a = true → hs08TabV b = true → Q a → Q b → Q (tmul a b))
    (hgv : ∀ g ∈ dGens, hs08TabV g = true) (hrv : ∀ r ∈ dReps, hs08TabV r = true)
    (hg : ∀ g ∈ s0Gens ++ dReps, Q g) : ∀ d ∈ dTabs, Q d := by
  intro d hd
  rw [dTabs, List.mem_flatMap] at hd
  obtain ⟨r, hr, hd⟩ := hd
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hd
  have h1 := hs08span_pred Q hid hmul (gs := s0Gens)
    (fun g h => ⟨hgv g (List.mem_append_left _ h), hg g (List.mem_append_left _ h)⟩) s hs
  exact hmul _ _ h1.1 (hrv r hr) h1.2 (hg r (List.mem_append_right _ hr))

theorem hs08norms_id {O : List Tab} (hO : ∀ z ∈ O, hs08TabV z = true) : HS08Norms O idTab := by
  intro z hz
  exact ⟨z, hz, by rw [hs08idTab_tmul (hO z hz), hs08tmul_idTab (hO z hz)]⟩

theorem hs08norms_mul {O : List Tab} (hO : ∀ z ∈ O, hs08TabV z = true) {a b : Tab}
    (ha : hs08TabV a = true) (hb : hs08TabV b = true) (hA : HS08Norms O a) (hB : HS08Norms O b) :
    HS08Norms O (tmul a b) := by
  intro z hz
  obtain ⟨w, hw, hbw⟩ := hB z hz
  obtain ⟨w', hw', haw⟩ := hA w hw
  refine ⟨w', hw', ?_⟩
  rw [hs08tmul_assoc ha hb (hO z hz), hbw, ← hs08tmul_assoc ha (hO w hw) hb, haw,
    hs08tmul_assoc (hO w' hw') ha hb]

def hs08Surj (t : Tab) : Prop := ∃ F : Fin 22 → Fin 22, hs08TabF F = t ∧ Function.Surjective F

theorem hs08surj_id : hs08Surj idTab := ⟨id, hs08TabF_id, Function.surjective_id⟩

theorem hs08surj_mul {a b : Tab} (ha : hs08Surj a) (hb : hs08Surj b) : hs08Surj (tmul a b) := by
  obtain ⟨A, rfl, hA⟩ := ha
  obtain ⟨B, rfl, hB⟩ := hb
  exact ⟨A ∘ B, hs08TabF_comp A B, hA.comp hB⟩

theorem hs08surj_of_inv {t u : Tab} (ht : hs08TabV t = true) (hu : hs08TabV u = true)
    (h : tmul t u = idTab) : hs08Surj t := by
  obtain ⟨T, rfl⟩ := hs08exists_tabF ht
  obtain ⟨U, rfl⟩ := hs08exists_tabF hu
  refine ⟨T, rfl, fun x => ⟨U x, ?_⟩⟩
  rw [← hs08TabF_comp, ← hs08TabF_id] at h
  exact congrFun (hs08TabF_injective h) x

theorem hs08cancel {y z d : Tab} (hy : hs08TabV y = true) (hz : hs08TabV z = true)
    (hd : hs08Surj d) (h : tmul y d = tmul z d) : y = z := by
  obtain ⟨Y, rfl⟩ := hs08exists_tabF hy
  obtain ⟨Z, rfl⟩ := hs08exists_tabF hz
  obtain ⟨D, rfl, hD⟩ := hd
  rw [← hs08TabF_comp, ← hs08TabF_comp] at h
  have h' := hs08TabF_injective h
  congr 1
  funext x
  obtain ⟨a, rfl⟩ := hD x
  exact congrFun h' a

theorem hs08getD_tmul {a b : Tab} {p : Nat} (hp : p < b.length) :
    (tmul a b).getD p 0 = a.getD (b.getD p 0) 0 := by
  rw [tmul, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hp),
    List.getD_eq_getElem _ _ hp, List.getElem_map]

theorem hs08DW_mem {a j : Nat} (hs0 : s0Tabs.length = 256) (hr : dReps.length = 15)
    (ha : a < 256) (hj : j < 15) : hs08DW a j ∈ dTabs := by
  rw [hs08DW, dTabs, List.mem_flatMap, List.getD_eq_getElem _ _ (by omega),
    List.getD_eq_getElem _ _ (by omega)]
  exact ⟨_, List.getElem_mem _, List.mem_map.2 ⟨_, List.getElem_mem _, rfl⟩⟩

theorem hs08wit {x : Tab} {Ys : List Tab} {R : List (Nat × Nat)} (hs0 : s0Tabs.length = 256)
    (hr : dReps.length = 15) (h : HS08WitOK x Ys R) :
    ∀ y ∈ Ys, ∃ d ∈ dTabs, tmul d x = tmul y d := by
  intro y hy
  obtain ⟨p, -, h1, h2, he⟩ := h y hy
  exact ⟨_, hs08DW_mem hs0 hr h1 h2, he⟩

theorem hs08jOrb_eq {J O : List Tab} {x : Tab} (hJ : ∀ y ∈ jOutJ J, hs08TabV y = true)
    (hOv : ∀ z ∈ O, hs08TabV z = true) (hN : ∀ d ∈ dTabs, HS08Norms O d)
    (hS : ∀ d ∈ dTabs, hs08Surj d) (hx : x ∈ O) (hW : ∀ y ∈ O, ∃ d ∈ dTabs, tmul d x = tmul y d) :
    jOrbJ J x = (jOutJ J).filter fun y => decide (y ∈ O) := by
  unfold jOrbJ
  apply List.filter_congr
  intro y hy
  rw [Bool.eq_iff_iff, List.any_eq_true]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨d, hd, he⟩
    obtain ⟨w, hw, hdw⟩ := hN d hd x hx
    rw [hs08cancel (hJ y hy) (hOv w hw) (hS d hd) (he.symm.trans hdw)]
    exact hw
  · exact hW y

theorem hs08normPropJ (hs0 : s0Tabs.length = 256) (hr : dReps.length = 15)
    (hgv : ∀ g ∈ dGens, hs08TabV g = true) (hrv : ∀ r ∈ dReps, hs08TabV r = true)
    (hL : (jInnJ jLit).length = 16 ∧ (jOutJ jLit).length = 16)
    (hCent : HS08CentOK hs08CentT)
    (h4 : HS08WitOK (x4J jLit) ((jInnJ jLit).filter fun l => decide (l ≠ idTab)) hs08W4)
    (h6 : HS08WitOK (x6J jLit) hs08O6 hs08W6) (h10 : HS08WitOK (x10J jLit) hs08O10 hs08W10)
    (hM : x4J jLit ∈ jLit ∧ x6J jLit ∈ jLit ∧ x10J jLit ∈ jLit)
    (hO : (jOutJ jLit).filter (fun y => decide (y ∈ hs08O6)) = hs08O6 ∧
      (jOutJ jLit).filter (fun y => decide (y ∈ hs08O10)) = hs08O10 ∧
      hs08O6.length = 6 ∧ hs08O10.length = 10 ∧
      (∀ y ∈ jOutJ jLit, y ∈ hs08O6 ∨ y ∈ hs08O10) ∧ (∀ y ∈ hs08O6, y ∉ hs08O10) ∧
      x6J jLit ∈ hs08O6 ∧ x10J jLit ∈ hs08O10 ∧ (∀ y ∈ hs08O6, hs08TabV y = true) ∧
      (∀ y ∈ hs08O10, hs08TabV y = true) ∧ ∀ y ∈ jOutJ jLit, hs08TabV y = true)
    (hN : ∀ g ∈ s0Gens ++ dReps, HS08Norms hs08O6 g ∧ HS08Norms hs08O10 g)
    (hI : ∀ g ∈ s0Gens ++ dReps, hs08TabV (tinv g) = true ∧ tmul g (tinv g) = idTab) :
    NormPropJ jLit := by
  obtain ⟨e6, e10, hl6, hl10, hcov, hdisj, hx6, hx10, hv6, hv10, hvJ⟩ := hO
  have hgr : ∀ g ∈ s0Gens ++ dReps, hs08TabV g = true := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hgv g (List.mem_append_left _ hg)
    · exact hrv g hg
  have hv : ∀ d ∈ dTabs, hs08TabV d = true :=
    hs08dTabs_pred (fun t => hs08TabV t = true) hs08idTab_valid
      (fun _ _ ha hb _ _ => hs08tmul_valid ha hb) hgv hrv hgr
  have hC : ∀ l ∈ dTabs, (∀ j ∈ jLit, tmul l j = tmul j l) → l ∈ jLit := by
    intro l hl hc
    refine hCent.2 l hl fun q hq => ?_
    obtain ⟨hqj, hql, hqp⟩ := hCent.1 q hq
    have hlen : l.length = 22 := by
      have h := hv l hl
      simp only [hs08TabV, Bool.and_eq_true, beq_iff_eq] at h
      exact h.1
    have e := congrArg (fun t => t.getD q.2 0) (hc q.1 hqj)
    have h1 : q.2 < q.1.length := by
      rw [hql]
      exact hqp
    have h2 : q.2 < l.length := by
      rw [hlen]
      exact hqp
    rw [hs08getD_tmul h1, hs08getD_tmul h2] at e
    exact e
  have hS : ∀ d ∈ dTabs, hs08Surj d :=
    hs08dTabs_pred hs08Surj hs08surj_id (fun _ _ _ _ => hs08surj_mul) hgv hrv
      fun g hg => hs08surj_of_inv (hgr g hg) (hI g hg).1 (hI g hg).2
  have hN6 : ∀ d ∈ dTabs, HS08Norms hs08O6 d :=
    hs08dTabs_pred _ (hs08norms_id hv6) (fun _ _ ha hb => hs08norms_mul hv6 ha hb) hgv hrv
      fun g hg => (hN g hg).1
  have hN10 : ∀ d ∈ dTabs, HS08Norms hs08O10 d :=
    hs08dTabs_pred _ (hs08norms_id hv10) (fun _ _ ha hb => hs08norms_mul hv10 ha hb) hgv hrv
      fun g hg => (hN g hg).2
  have o6 : jOrbJ jLit (x6J jLit) = hs08O6 :=
    (hs08jOrb_eq hvJ hv6 hN6 hS hx6 (hs08wit hs0 hr h6)).trans e6
  have o10 : jOrbJ jLit (x10J jLit) = hs08O10 :=
    (hs08jOrb_eq hvJ hv10 hN10 hS hx10 (hs08wit hs0 hr h10)).trans e10
  unfold NormPropJ
  rw [o6, o10]
  exact ⟨hL.1, hL.2, hC, hs08wit hs0 hr h4, hM.1, hM.2.1, hM.2.2, hl6, hl10, hcov, hdisj,
    fun d hd x hx => hN6 d hd x hx, fun d hd x hx => hN10 d hd x hx⟩

end CFSG.KC.EvenSporM22
