module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCoords
public import Certificates.Data.Holder1711.Om1Facts

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check

set_option linter.unusedSectionVars false

abbrev WP : Type := ↥wPlus

theorem allWords_ok : allWords.all wordOK = true := by decide +kernel

theorem wordOK_of_allWords {w : List ℕ} (hw : w ∈ allWords) : wordOK w = true :=
  List.all_eq_true.1 allWords_ok w hw

theorem reflTab_get {r : ℕ} (hr : r < 240) : (reflTab ())[r]! = reflArr r := by
  simp [reflTab, hr]

theorem wA_eq : ∀ w : List ℕ, (∀ r ∈ w, r < 240) → wA (reflTab ()) w = wordArr w
  | [], _ => rfl
  | r :: w, h => by
    simp only [wA, wordArr]
    rw [reflTab_get (h r List.mem_cons_self),
      wA_eq w fun s hs => h s (List.mem_cons_of_mem _ hs)]


theorem rep_wA {w : List ℕ} (h : ∀ r ∈ w, r < 240) :
    Rep 240 (wA (reflTab ()) w) (wordPerm w) := by
  rw [wA_eq w h]
  exact rep_wordArr w h

theorem wordOK_spec {w : List ℕ} (h : wordOK w = true) :
    (∀ r ∈ w, r < 240) ∧ Even w.length := by
  simp only [wordOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1, Nat.even_iff.2 h.2⟩

theorem permOfArr_wA {w : List ℕ} (h : ∀ r ∈ w, r < 240) :
    permOfArr 240 (wA (reflTab ()) w) = wordPerm w :=
  CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_wA h)

@[expose] noncomputable def wpE (w : List ℕ) : WP :=
  if h : wordOK w = true then ⟨wordPerm w, wordPerm_mem_wPlus (wordOK_spec h).1 (wordOK_spec h).2⟩
  else 1

theorem coe_wpE {w : List ℕ} (h : wordOK w = true) : ((wpE w : WP) : Equiv.Perm (Fin 240)) = wordPerm w := by
  rw [wpE, dif_pos h]

theorem rep_wpE {w : List ℕ} (h : wordOK w = true) :
    Rep 240 (wA (reflTab ()) w) ((wpE w : WP) : Equiv.Perm (Fin 240)) := by
  rw [coe_wpE h]
  exact rep_wA (wordOK_spec h).1

@[expose] noncomputable def closureW (ws : List (List ℕ)) : Subgroup WP :=
  Subgroup.closure (wpE '' {w | w ∈ ws})

theorem wpE_mem_closureW {ws : List (List ℕ)} {w : List ℕ} (hw : w ∈ ws) : wpE w ∈ closureW ws :=
  Subgroup.subset_closure ⟨w, hw, rfl⟩

theorem coe_wpE_eq_E {w : List ℕ} (h : wordOK w = true) :
    ((wpE w : WP) : Equiv.Perm (Fin 240)) = Om1Facts.E w := by
  rw [coe_wpE h, Om1Facts.E, permOfArr_wA (wordOK_spec h).1]

theorem map_closureW {ws : List (List ℕ)} (hws : ∀ w ∈ ws, wordOK w = true) :
    (closureW ws).map wPlus.subtype = Om1Facts.G ws := by
  rw [closureW, MonoidHom.map_closure, Om1Facts.G, ← Set.image_comp]
  exact congrArg Subgroup.closure (Set.image_congr fun w hw => coe_wpE_eq_E (hws w hw))

theorem mem_iff_of_map {H : Subgroup WP} {K : Subgroup (Equiv.Perm (Fin 240))}
    (h : H.map wPlus.subtype = K) {x : WP} : x ∈ H ↔ (x : Equiv.Perm (Fin 240)) ∈ K := by
  subst h
  exact (Subgroup.mem_map_iff_mem wPlus.subtype_injective).symm

theorem card_eq_of_map {H : Subgroup WP} {K : Subgroup (Equiv.Perm (Fin 240))}
    (h : H.map wPlus.subtype = K) : Nat.card H = Nat.card K := by
  rw [← h, Subgroup.card_map_of_injective wPlus.subtype_injective]

theorem exists_of_map {H : Subgroup WP} {K : Subgroup (Equiv.Perm (Fin 240))}
    (h : H.map wPlus.subtype = K) {s : Equiv.Perm (Fin 240)} (hs : s ∈ K) :
    ∃ s' ∈ H, (s' : Equiv.Perm (Fin 240)) = s := by
  rw [← h] at hs
  obtain ⟨s', hs', e⟩ := hs
  exact ⟨s', hs', e⟩

theorem mem_closureW_iff {ws : List (List ℕ)} (hws : ∀ w ∈ ws, wordOK w = true) {x : WP} :
    x ∈ closureW ws ↔ (x : Equiv.Perm (Fin 240)) ∈ Om1Facts.G ws :=
  mem_iff_of_map (map_closureW hws)

theorem card_closureW {ws : List (List ℕ)} (hws : ∀ w ∈ ws, wordOK w = true) :
    Nat.card (closureW ws) = Nat.card (Om1Facts.G ws) :=
  card_eq_of_map (map_closureW hws)

theorem exists_of_mem_G {ws : List (List ℕ)} (hws : ∀ w ∈ ws, wordOK w = true)
    {s : Equiv.Perm (Fin 240)} (hs : s ∈ Om1Facts.G ws) :
    ∃ s' ∈ closureW ws, (s' : Equiv.Perm (Fin 240)) = s :=
  exists_of_map (map_closureW hws) hs

theorem Wp_le : Om1Facts.Wp ≤ wPlus := by
  rw [Om1Facts.Wp, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  have hw' := wordOK_spec hw
  rw [SetLike.mem_coe, Om1Facts.E, permOfArr_wA hw'.1]
  exact wordPerm_mem_wPlus hw'.1 hw'.2

theorem evenSub_mask {m : ℕ} (hm : m < 256) (he : framePop m % 2 = 0) :
    frameDecode m ∈ evenSub := by
  rw [mem_evenSub_iff_frameWt, frameWt_frameDecode m hm]
  exact he

@[expose] noncomputable def eW (m : ℕ) : WP :=
  if h : m < 256 ∧ framePop m % 2 = 0 then
    ⟨frameElt (frameDecode m), (frameElt_mem_wPlus_iff _).2 (evenSub_mask h.1 h.2)⟩
  else 1

theorem coe_eW {m : ℕ} (h : m < 256 ∧ framePop m % 2 = 0) :
    ((eW m : WP) : Equiv.Perm (Fin 240)) = frameElt (frameDecode m) := by
  rw [eW, dif_pos h]

theorem rep_eW {m : ℕ} (h : m < 256 ∧ framePop m % 2 = 0) :
    Rep 240 (eA m) ((eW m : WP) : Equiv.Perm (Fin 240)) := by
  rw [coe_eW h, eA]
  exact rep_frameArr _

theorem coe_eW_eq_e {m : ℕ} (h : m < 256 ∧ framePop m % 2 = 0) :
    ((eW m : WP) : Equiv.Perm (Fin 240)) = Om1Facts.e m :=
  (CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_eW h)).symm

noncomputable abbrev t0 : WP := eW 15
noncomputable abbrev ta : WP := eW 3
noncomputable abbrev tb : WP := eW 252
noncomputable abbrev tc : WP := eW 23

@[expose] noncomputable def zW : WP := ⟨zPerm, zPerm_mem_wPlus⟩

noncomputable abbrev i0 : WP := wpE wI0
noncomputable abbrev j0 : WP := wpE wJ0
noncomputable abbrev s1 : WP := wpE wS1
noncomputable abbrev g1 : WP := wpE wG1

@[expose] noncomputable def R0 : Subgroup WP := Subgroup.closure {i0, j0}

@[expose] noncomputable def R0' : Subgroup WP := CFSG.ClassicalInvolution.Generic.conjSub s1 R0

noncomputable abbrev T0 : Subgroup WP := Subgroup.centralizer {t0}

theorem zPerm_eq_z : zPerm = Om1Facts.z :=
  (CFSG.RankThree.Native.permOfArr_eq_of_rep rep_negArr).symm

theorem coe_zW_eq_z : ((zW : WP) : Equiv.Perm (Fin 240)) = Om1Facts.z := zPerm_eq_z

theorem coe_t0 : ((t0 : WP) : Equiv.Perm (Fin 240)) = Om1Facts.t :=
  coe_eW_eq_e ⟨by norm_num, by decide⟩

theorem coe_ta : ((ta : WP) : Equiv.Perm (Fin 240)) = Om1Facts.ta :=
  coe_eW_eq_e ⟨by norm_num, by decide⟩

theorem coe_tb : ((tb : WP) : Equiv.Perm (Fin 240)) = Om1Facts.tb :=
  coe_eW_eq_e ⟨by norm_num, by decide⟩

theorem coe_tc : ((tc : WP) : Equiv.Perm (Fin 240)) = Om1Facts.tc :=
  coe_eW_eq_e ⟨by norm_num, by decide⟩

theorem coe_i0 : ((i0 : WP) : Equiv.Perm (Fin 240)) = Om1Facts.E wI0 := coe_wpE_eq_E (by decide)

theorem coe_j0 : ((j0 : WP) : Equiv.Perm (Fin 240)) = Om1Facts.E wJ0 := coe_wpE_eq_E (by decide)

theorem coe_s1 : ((s1 : WP) : Equiv.Perm (Fin 240)) = Om1Facts.E wS1 := coe_wpE_eq_E (by decide)

theorem coe_g1 : ((g1 : WP) : Equiv.Perm (Fin 240)) = Om1Facts.E wG1 := coe_wpE_eq_E (by decide)

theorem map_R0 : R0.map wPlus.subtype = Om1Facts.R := by
  rw [R0, MonoidHom.map_closure, Set.image_pair, Om1Facts.R, Subgroup.coe_subtype, coe_i0, coe_j0]

theorem map_conjSub (g : WP) (H : Subgroup WP) :
    (CFSG.ClassicalInvolution.Generic.conjSub g H).map wPlus.subtype =
      CFSG.ClassicalInvolution.Generic.conjSub (g : Equiv.Perm (Fin 240)) (H.map wPlus.subtype) := by
  rw [CFSG.ClassicalInvolution.Generic.conjSub, CFSG.ClassicalInvolution.Generic.conjSub,
    Subgroup.map_map, Subgroup.map_map]
  exact congrArg (fun f => H.map f) (MonoidHom.ext fun _ => rfl)

theorem R'_eq : Om1Facts.R' =
    CFSG.ClassicalInvolution.Generic.conjSub (Om1Facts.E wS1) Om1Facts.R := by
  rw [Om1Facts.R', CFSG.ClassicalInvolution.Generic.conjSub, Om1Facts.R, MonoidHom.map_closure,
    Set.image_pair]
  rfl

theorem map_R0' : R0'.map wPlus.subtype = Om1Facts.R' := by
  rw [R0', map_conjSub, map_R0, R'_eq, coe_s1]

theorem mem_R0_iff {x : WP} : x ∈ R0 ↔ (x : Equiv.Perm (Fin 240)) ∈ Om1Facts.R :=
  mem_iff_of_map map_R0

theorem mem_R0'_iff {x : WP} : x ∈ R0' ↔ (x : Equiv.Perm (Fin 240)) ∈ Om1Facts.R' :=
  mem_iff_of_map map_R0'

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1
