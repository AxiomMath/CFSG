module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.Basic
public import Certificates.Certificate197002
public import Certificates.Data.Holder1711.Om2Facts

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab wA wordOK eA)

set_option linter.unusedSectionVars false

theorem om2A_parts :
    genCheck (reflTab ()) = true ∧ wordsCheckY (reflTab ()) = true ∧
      relCheckY (reflTab ()) = true ∧ enumCheckY (reflTab ()) = true ∧
      orbitCheckY (reflTab ()) = true ∧ subCheckY (reflTab ()) = true ∧
      r0CheckY (reflTab ()) = true := by
  have h := (Certificates.certificate197002 : om2CheckA () = true)
  simp only [om2CheckA, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

@[expose] noncomputable def phiP (x y : Equiv.Perm (Fin 240)) : Equiv.Perm (Fin 480) :=
  (finSumFinEquiv (m := 240) (n := 240)).permCongr (Equiv.sumCongr x y)

private theorem bo2_phiP_castAdd (x y : Equiv.Perm (Fin 240)) (i : Fin 240) :
    (phiP x y (Fin.castAdd 240 i) : ℕ) = x i := by
  unfold phiP
  rw [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply,
    Sum.map_inl, finSumFinEquiv_apply_left]
  rfl

private theorem bo2_phiP_natAdd (x y : Equiv.Perm (Fin 240)) (i : Fin 240) :
    (phiP x y (Fin.natAdd 240 i) : ℕ) = 240 + y i := by
  unfold phiP
  rw [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply,
    Sum.map_inr, finSumFinEquiv_apply_right]
  rfl

private theorem bo2_phiP_injective {x y x' y' : Equiv.Perm (Fin 240)} (h : phiP x y = phiP x' y') :
    x = x' ∧ y = y' := by
  constructor
  · ext i
    have := congrArg (fun g : Equiv.Perm (Fin 480) => ((g (Fin.castAdd 240 i) : Fin 480) : ℕ)) h
    simpa only [bo2_phiP_castAdd] using this
  · ext i
    have := congrArg (fun g : Equiv.Perm (Fin 480) => ((g (Fin.natAdd 240 i) : Fin 480) : ℕ)) h
    simp only [bo2_phiP_natAdd] at this
    omega

private theorem bo2_getElem!_append_left {α : Type} [Inhabited α] {xs ys : Array α} {i : ℕ}
    (h : i < xs.size) : (xs ++ ys)[i]! = xs[i]! := by
  rw [getElem!_pos (xs ++ ys) i (by simp only [Array.size_append]; omega), getElem!_pos xs i h,
    Array.getElem_append_left h]

private theorem bo2_getElem!_append_right {α : Type} [Inhabited α] {xs ys : Array α} {i : ℕ}
    (h : xs.size ≤ i) (h2 : i - xs.size < ys.size) : (xs ++ ys)[i]! = ys[i - xs.size]! := by
  rw [getElem!_pos (xs ++ ys) i (by simp only [Array.size_append]; omega), getElem!_pos ys _ h2,
    Array.getElem_append_right h]

private theorem bo2_getElem!_map {α β : Type} [Inhabited α] [Inhabited β] {xs : Array α}
    {f : α → β} {i : ℕ} (h : i < xs.size) : (xs.map f)[i]! = f xs[i]! := by
  rw [getElem!_pos (xs.map f) i (by simpa using h), Array.getElem_map, getElem!_pos xs i h]

theorem rep_phiP {a b : Array ℕ} {x y : Equiv.Perm (Fin 240)} (ha : Rep 240 a x)
    (hb : Rep 240 b y) (sa : a.size = 240) (sb : b.size = 240) :
    Rep 480 (pairA a b) (phiP x y) := by
  intro i
  obtain ⟨i, hi⟩ := i
  by_cases h : i < 240
  · have e : (⟨i, hi⟩ : Fin 480) = Fin.castAdd 240 ⟨i, h⟩ := rfl
    change (a ++ b.map (· + 240))[i]! = ((phiP x y ⟨i, hi⟩ : Fin 480) : ℕ)
    rw [e, bo2_phiP_castAdd, bo2_getElem!_append_left (by omega)]
    exact ha ⟨i, h⟩
  · have hj : i - 240 < 240 := by omega
    have e : (⟨i, hi⟩ : Fin 480) = Fin.natAdd 240 ⟨i - 240, hj⟩ := Fin.ext (by simp; omega)
    change (a ++ b.map (· + 240))[i]! = ((phiP x y ⟨i, hi⟩ : Fin 480) : ℕ)
    rw [e, bo2_phiP_natAdd, bo2_getElem!_append_right (by omega) (by simp [sa, sb]; omega)]
    have := hb ⟨i - 240, hj⟩
    simp only [sa]
    rw [bo2_getElem!_map (by omega)]
    change b[i - 240]! + 240 = 240 + ((y ⟨i - 240, hj⟩ : Fin 240) : ℕ)
    rw [this]
    omega

@[expose] noncomputable def phi : HY →* Equiv.Perm (Fin 480) where
  toFun u := phiP ((u : WP × WP).1 : Equiv.Perm (Fin 240)) ((u : WP × WP).2 : Equiv.Perm (Fin 240))
  map_one' := by
    change phiP 1 1 = 1
    unfold phiP
    have h : Equiv.sumCongr (1 : Equiv.Perm (Fin 240)) (1 : Equiv.Perm (Fin 240)) = 1 :=
      Equiv.Perm.sumCongr_one
    rw [h]
    exact map_one (Equiv.permCongrHom (finSumFinEquiv (m := 240) (n := 240)))
  map_mul' u v := by
    have h := map_mul (Equiv.permCongrHom (finSumFinEquiv (m := 240) (n := 240)))
      (Equiv.sumCongr ((u : WP × WP).1 : Equiv.Perm (Fin 240))
        ((u : WP × WP).2 : Equiv.Perm (Fin 240)))
      (Equiv.sumCongr ((v : WP × WP).1 : Equiv.Perm (Fin 240))
        ((v : WP × WP).2 : Equiv.Perm (Fin 240)))
    rw [Equiv.Perm.sumCongr_mul] at h
    exact h

theorem phi_injective : Function.Injective phi := by
  intro u v h
  have h' : phiP ((u : WP × WP).1 : Equiv.Perm (Fin 240)) ((u : WP × WP).2 : Equiv.Perm (Fin 240)) =
      phiP ((v : WP × WP).1 : Equiv.Perm (Fin 240)) ((v : WP × WP).2 : Equiv.Perm (Fin 240)) := h
  obtain ⟨h1, h2⟩ := bo2_phiP_injective h'
  exact Subtype.ext (Prod.ext (Subtype.ext h1) (Subtype.ext h2))

@[expose] noncomputable def yE (i : ℕ) : WP := Om1.wpE (yW.getD i [])

private theorem bo2_size_wA (RT : Array (Array ℕ)) : ∀ w : List ℕ, (wA RT w).size = 240
  | [] => by simp [wA, idA]
  | r :: l => by simp [wA, compA]

private theorem bo2_yW_ok {i : ℕ} (hi : i < 8) : wordOK (yW.getD i []) = true := by
  interval_cases i <;> decide

theorem gen_mem {i : ℕ} (hi : i < 8) : ((⟨omLift i, omLift_mem hi⟩ : WP), yE i) ∈ YP := by
  rw [mem_YP, pHat_omLift hi]
  apply omegaRestrictEquiv.injective
  rw [omegaRestrictEquiv_pHat]
  apply Subtype.ext
  have hcheck := om2A_parts.1
  simp only [genCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hcheck
  have hi' := hcheck.2 i hi
  have hR : Rep 120 (pArr (wA (reflTab ()) (yW.getD i []))) (pPlus (yE i)) :=
    rep_pArr (g := ⟨(yE i : Equiv.Perm (Fin 240)), wPlus_le (yE i).2⟩)
      (Om1.rep_wpE (bo2_yW_ok hi))
  have hC : Rep 360 (CFSG.RankThree.Native.conjA 360 genArrs[8]! genArrs[i]!)
      (gen 8 * (gen i * (gen 8)⁻¹)) :=
    rep_compA (rep_gen (by norm_num)) (rep_compA (rep_gen (by omega)) (rep_gen_inv (by norm_num)))
  have hL : Rep 120 (res120 (CFSG.RankThree.Native.conjA 360 genArrs[8]! genArrs[i]!))
      ((omegaRestrictEquiv (sigmaO ⟨gen i, gen_mem_omegaT hi⟩) : omega1T) :
        Equiv.Perm (Fin 120)) := by
    intro j
    unfold res120
    rw [getElem!_ofFn_nat _ j.2, hC.apply (by omega : (j : ℕ) < 360), omegaRestrictEquiv_apply,
      omegaRes_apply_val, sigmaO, autEquiv_apply, mul_assoc]
    rfl
  exact eq_of_eqA hL hR hi'

@[expose] noncomputable def genE (i : ℕ) : HY :=
  if h : i < 8 then ⟨(⟨omLift i, omLift_mem h⟩, yE i), gen_mem h⟩ else 1

theorem rep_genE {i : ℕ} (hi : i < 8) : Rep 480 (genY (reflTab ()))[i]! (phi (genE i)) := by
  have hg : (genY (reflTab ()))[i]! = pairA (wA (reflTab ()) (omWords.getD i []))
      (wA (reflTab ()) (yW.getD i [])) := by
    unfold genY
    rw [getElem!_pos _ i (by simpa using hi), List.getElem_toArray, List.getElem_map,
      List.getElem_range]
  have e : phi (genE i) = phiP (omLift i) ((yE i : WP) : Equiv.Perm (Fin 240)) := by
    unfold genE
    rw [dif_pos hi]
    rfl
  rw [hg, e]
  exact rep_phiP (Om1.rep_wA (omWords_lt hi)) (Om1.rep_wpE (bo2_yW_ok hi)) (bo2_size_wA _ _)
    (bo2_size_wA _ _)

@[expose] noncomputable def letE (l : ℕ) : HY := if l < 8 then genE l else (genE (l - 8))⁻¹

@[expose] noncomputable def wordE (w : List ℕ) : HY := (w.map letE).prod

private theorem bo2_genY_valid {k : ℕ} (hk : k < 8) :
    validA 480 (genY (reflTab ()))[k]! = true := by
  have h := om2A_parts.2.1
  simp only [wordsCheckY, Bool.and_eq_true] at h
  have hsz : (genY (reflTab ())).size = 8 := by simp [genY]
  have := Array.all_eq_true.1 h.1.1 k (by omega)
  rwa [← getElem!_pos (genY (reflTab ())) k (by omega)] at this

private theorem bo2_rep_letter {l : ℕ} (hl : l < 16) :
    Rep 480 (lettersY (reflTab ()))[l]! (phi (letE l)) := by
  have hsz : (genY (reflTab ())).size = 8 := by simp [genY]
  by_cases h : l < 8
  · rw [letE, if_pos h]
    unfold lettersY
    rw [bo2_getElem!_append_left (by omega)]
    exact rep_genE h
  · have hl8 : l - 8 < 8 := by omega
    rw [letE, if_neg h, map_inv]
    have hperm : permOfArr 480 (genY (reflTab ()))[l - 8]! = phi (genE (l - 8)) :=
      CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_genE hl8)
    have hinv := CFSG.RankThree.Native.rep_inv_of_validA (bo2_genY_valid hl8)
    rw [hperm] at hinv
    unfold lettersY
    rw [bo2_getElem!_append_right (by omega) (by simp [hsz]; omega), hsz,
      bo2_getElem!_map (by omega)]
    exact hinv

theorem rep_wordE {w : List ℕ} (hw : wordYOK w = true) :
    Rep 480 (wY (lettersY (reflTab ())) w) (phi (wordE w)) := by
  induction w with
  | nil =>
    rw [wordE, List.map_nil, List.prod_nil, map_one]
    exact rep_idA
  | cons l w ih =>
    simp only [wordYOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    have ih' := ih (by simpa [wordYOK] using hw.2)
    have hl := bo2_rep_letter hw.1
    have e : wordE (l :: w) = letE l * wordE w := by simp [wordE]
    rw [e, map_mul]
    exact rep_compA hl ih'

@[expose] noncomputable def closureY (ws : List (List ℕ)) : Subgroup HY :=
  Subgroup.closure (wordE '' {w | w ∈ ws})

theorem wordE_mem_closureY {ws : List (List ℕ)} {w : List ℕ} (hw : w ∈ ws) :
    wordE w ∈ closureY ws :=
  Subgroup.subset_closure ⟨w, hw, rfl⟩

theorem wordsCheckY_spec {w : List ℕ} (hw : w ∈ allWordsY) :
    wordYOK w = true ∧ validA 480 (wY (lettersY (reflTab ())) w) = true := by
  have h := om2A_parts.2.1
  simp only [wordsCheckY, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 w hw

theorem enumSizeY_spec {ws : List (List ℕ)} (hws : ∀ w ∈ ws, wordYOK w = true) {sz : ℕ}
    (h : enumSizeY (lettersY (reflTab ())) ws sz = true) :
    Nat.card (closureY ws) = sz ∧
      (∀ x : HY, x ∈ closureY ws ↔
        ∃ i < (enumOfY (lettersY (reflTab ())) ws (sz + 1)).pts.size,
          permOfArr 480 (enumOfY (lettersY (reflTab ())) ws (sz + 1)).pts[i]! = phi x) ∧
      (∀ i < (enumOfY (lettersY (reflTab ())) ws (sz + 1)).pts.size,
        validA 480 (enumOfY (lettersY (reflTab ())) ws (sz + 1)).pts[i]! = true) := by
  simp only [enumSizeY, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hok, hsz⟩ := h
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec (fun p hp => by
    simp only [keyPtsY, keyPts, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hp
    omega) hok
  have hmap : (closureY ws).map phi =
      Subgroup.closure (permsA 480 (ws.map (wY (lettersY (reflTab ())))).toArray) := by
    rw [closureY, MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_setOf_eq, permsA, List.size_toArray, List.length_map]
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
      refine ⟨k, hk, ?_⟩
      rw [getElem!_pos _ k (by simpa using hk), List.getElem_toArray, List.getElem_map,
        CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_wordE (hws _ (List.getElem_mem hk)))]
    · rintro ⟨k, hk, rfl⟩
      refine ⟨wordE ws[k], ⟨ws[k], List.getElem_mem hk, rfl⟩, ?_⟩
      rw [getElem!_pos _ k (by simpa using hk), List.getElem_toArray, List.getElem_map,
        CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_wordE (hws _ (List.getElem_mem hk)))]
  have hcl : ∀ x : HY, x ∈ closureY ws ↔ phi x ∈ Subgroup.closure
      (permsA 480 (ws.map (wY (lettersY (reflTab ())))).toArray) := by
    intro x
    rw [← hmap]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, e⟩
      rwa [phi_injective e] at hy
  refine ⟨?_, fun x => ?_, hval⟩
  · rw [← hsz, ← hcard, ← hmap, Subgroup.card_map_of_injective phi_injective]
  · rw [hcl x, hmem]

private theorem bo2_pHat_zPlus : pHat zPlus = 1 := by
  have h := pHat_eq_iff (x := 1) (y := zPlus)
  rw [map_one, one_mul] at h
  exact (h.2 (Or.inr rfl)).symm

theorem cK_mem (k : ℕ) :
    ((if k = 1 then 1 else zPlus : WP), (if k = 0 then 1 else zPlus : WP)) ∈ YP := by
  rw [mem_YP]
  have h1 : ∀ a : WP, a = 1 ∨ a = zPlus → pHat a = 1 := by
    rintro a (rfl | rfl)
    · exact map_one _
    · exact bo2_pHat_zPlus
  have e1 : pHat (if k = 1 then 1 else zPlus : WP) = 1 := h1 _ (by split_ifs <;> simp)
  have e2 : pHat (if k = 0 then 1 else zPlus : WP) = 1 := h1 _ (by split_ifs <;> simp)
  rw [e1, e2, map_one]

@[expose] noncomputable def cK (k : ℕ) : HY :=
  ⟨((if k = 1 then 1 else zPlus : WP), (if k = 0 then 1 else zPlus : WP)), cK_mem k⟩

theorem rep_cK {k : ℕ} (hk : k < 3) : Rep 480 (cA k) (phi (cK k)) := by
  have hneg : Rep 240 negArr (zPlus : Equiv.Perm (Fin 240)) := rep_negArr
  have hid : Rep 240 (idA 240) ((1 : WP) : Equiv.Perm (Fin 240)) := rep_idA
  have sneg : negArr.size = 240 := by simp [negArr]
  have sid : (idA 240).size = 240 := by simp [idA]
  interval_cases k
  · exact rep_phiP hneg hid sneg sid
  · exact rep_phiP hid hneg sid sneg
  · exact rep_phiP hneg hneg sneg sneg

noncomputable abbrev t0Y : HY := wordE wT0
noncomputable abbrev i0Y : HY := wordE wI0
noncomputable abbrev j0Y : HY := wordE wJ0
noncomputable abbrev tcY : HY := wordE wTc
noncomputable abbrev fuse0 (k : ℕ) : HY := wordE (wFuse0.getD k [])
noncomputable abbrev fuseC : HY := wordE wFuseC
noncomputable abbrev liftA : HY := wordE wLiftA
noncomputable abbrev liftB : HY := wordE wLiftB

@[expose] noncomputable def R0Y : Subgroup HY := Subgroup.closure {i0Y, j0Y}

noncomputable abbrev T0Y : Subgroup HY := Subgroup.centralizer {t0Y}

theorem phi_wordE {w : List ℕ} (hw : wordYOK w = true) : phi (wordE w) = Om2Facts.E w :=
  (CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_wordE hw)).symm

theorem map_closureY {ws : List (List ℕ)} (hws : ∀ w ∈ ws, wordYOK w = true) :
    (closureY ws).map phi = Om2Facts.G ws := by
  rw [closureY, MonoidHom.map_closure, Om2Facts.G, ← Set.image_comp]
  exact congrArg Subgroup.closure (Set.image_congr fun w hw => phi_wordE (hws w hw))

theorem mem_closureY_iff {ws : List (List ℕ)} (hws : ∀ w ∈ ws, wordYOK w = true) {x : HY} :
    x ∈ closureY ws ↔ phi x ∈ Om2Facts.G ws := by
  rw [← map_closureY hws]
  constructor
  · exact fun hx => ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, e⟩
    rwa [phi_injective e] at hy

theorem exists_of_mem_G {ws : List (List ℕ)} (hws : ∀ w ∈ ws, wordYOK w = true)
    {s : Equiv.Perm (Fin 480)} (hs : s ∈ Om2Facts.G ws) : ∃ s' ∈ closureY ws, phi s' = s := by
  rw [← map_closureY hws] at hs
  exact hs

theorem phi_t0Y : phi t0Y = Om2Facts.t :=
  phi_wordE (wordsCheckY_spec (w := wT0) (by simp [allWordsY])).1

theorem phi_tcY : phi tcY = Om2Facts.tc :=
  phi_wordE (wordsCheckY_spec (w := wTc) (by simp [allWordsY])).1

theorem phi_cK {k : ℕ} (hk : k < 3) : phi (cK k) = Om2Facts.cP k :=
  (CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_cK hk)).symm

theorem map_R0Y : R0Y.map phi = Om2Facts.R := by
  rw [R0Y, MonoidHom.map_closure, Set.image_pair, Om2Facts.R,
    phi_wordE (wordsCheckY_spec (w := wI0) (by simp [allWordsY])).1,
    phi_wordE (wordsCheckY_spec (w := wJ0) (by simp [allWordsY])).1]

theorem mem_R0Y_iff {x : HY} : x ∈ R0Y ↔ phi x ∈ Om2Facts.R := by
  rw [← map_R0Y]
  constructor
  · exact fun hx => ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, e⟩
    rwa [phi_injective e] at hy

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2
