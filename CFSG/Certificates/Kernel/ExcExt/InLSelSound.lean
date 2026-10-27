module

public import Certificates.Data.Kernel.ExcExt.InLSelTwin
public import CFSG.Certificates.Kernel.ExcExt.InLNbrSound
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtExcLine
public import CFSG.LocalAnalysis.StandardType.GGQ2InLSelFrameAut

public section

noncomputable section

namespace CFSG.ExcExtK

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw

open Classical in
@[expose] def ilsBody (T : Chk.Tabs) (m : Fin 6) (E6 : List Nat) (cv cy a b : Nat) : Bool :=
  decide (∃ W, Chk.leafModelOK T m cv (Chk.combN (dim m) cv cy a b) (T.zm[cv]!)
      (T.zm[Chk.combN (dim m) cv cy a b]!) W = true) ||
    decide (∃ w L L', Chk.selD6OK T m (T.zm[cv]! &&& T.zm[cy]!)
      (T.zm[Chk.combN (dim m) cv cy a b]!) w L L' = true) ||
    E6.contains (T.zm[Chk.combN (dim m) cv cy a b]!)

@[expose] def SelP (m : Fin 6) (E6 : List Nat) (j k : Finset (Root m)) : Prop :=
  InLSelD6Raw (excRaw m) j k ∨ ∃ n ∈ E6, k = ofMask m n

theorem inLSelVx_of_scanLineN {m : Fin 6} {T : Chk.Tabs} (hT : Chk.tabsOK m T = true)
    {S : Chk.Search} {E6 : List Nat} {vx : V m}
    (h : Chk.scanLineN T m false true S
      (fun cv cy => Chk.candScanN T m S cv cy (ilsBody T m E6 cv cy)) (code m vx) = true) :
    InLSelVx (excRaw m) (SelP m E6) vx := by
  intro hvx ℓ hℓ hq hocc hcent hin U hU hxU j hj hjocc hjcent _ _ z hz hzx k hk _
  have hL : LineHyp m false true vx ℓ :=
    ⟨hvx, hℓ, fun _ => hq, hocc, hcent, iff_of_true hin rfl⟩
  obtain ⟨cv, cy, hcv, hcy, rfl, -, rfl, rfl, rfl, hbody⟩ :=
    scanLineN_sound hT h hL hU hxU ⟨hj, hjocc, hjcent⟩
  obtain ⟨a, b, -, -, rfl, rfl, hab⟩ :=
    candScanN_sound hT hbody hcv hcy hz hzx (candHyp_of_candidate hk)
  simp only [ilsBody, Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hab
  rcases hab with (⟨W, hW⟩ | ⟨w, L, L', hd⟩) | he
  · exact Or.inl (inLLeafAt_of_leafModelOK hT hW)
  · exact Or.inr (Or.inl (inLSelD6Raw_of_selD6OK hT hd))
  · exact Or.inr (Or.inr ⟨_, he, rfl⟩)

@[expose] def lpick (d cv : Nat) : Nat → List KLPlane → Nat → Option KLPlane
  | 0, _, _ => none
  | n + 1, ps, cy =>
    if Chk.canonN d cv n then
      match ps with
      | [] => none
      | P :: tl => if cy = n then some P else lpick d cv n tl cy
    else lpick d cv n ps cy

@[expose] def lsearchOf (m : Fin 6) (L : KLLine) : Chk.Search where
  line cv := if cv = L.cv then decRefI L.ref else none
  plane cv cy := (lpick (dim m) cv (3 ^ dim m) L.planes cy).bind fun P => decRefP P.ref
  cand _ cz := decRefC (ln128 L.cref cz)

@[expose] def e6Masks (Es : List KE6) : List Nat := Es.map fun E => E.k

theorem ls_pick_succ (d cv n : Nat) (ps : List KLPlane) (cy : Nat) :
    lpick d cv (n + 1) ps cy = if Chk.canonN d cv n then
      (match ps with
        | [] => none
        | P :: tl => if cy = n then some P else lpick d cv n tl cy)
    else lpick d cv n ps cy := rfl

theorem ls_walk_sound {d cv : Nat} {pl : KLPlane → Bool} {W : Nat → List KLPlane → Bool}
    (hW : ∀ n ps, W (n + 1) ps = Bool.rec (motive := fun _ => Bool) (W n ps)
      (List.rec (motive := fun _ => Bool) false
        (fun P tl _ => band (Nat.beq P.cy n) (band (pl P) (W n tl))) ps) (canonK d cv n)) :
    ∀ {n : Nat} {ps : List KLPlane}, W n ps = true → ∀ cy < n, Chk.canonN d cv cy = true →
      ∃ P, lpick d cv n ps cy = some P ∧ P.cy = cy ∧ pl P = true := by
  intro n
  induction n with
  | zero =>
    intro ps _ cy hcy
    exact absurd hcy (Nat.not_lt_zero cy)
  | succ n ih =>
    intro ps hw cy hcy hc
    rw [hW, canonK_eq] at hw
    rw [ls_pick_succ]
    cases hcn : Chk.canonN d cv n
    · rw [hcn] at hw
      have hne : cy ≠ n := by
        rintro rfl
        rw [hc] at hcn
        exact Bool.noConfusion hcn
      rw [if_neg (by simp)]
      exact ih hw cy (by omega) hc
    · rw [hcn] at hw
      rw [if_pos rfl]
      cases ps with
      | nil => exact Bool.noConfusion hw
      | cons P tl =>
        have hw' : band (Nat.beq P.cy n) (band (pl P) (W n tl)) = true := hw
        simp only [band_eq_true, Nat.beq_eq] at hw'
        obtain ⟨h1, h2, h3⟩ := hw'
        by_cases hcn' : cy = n
        · subst hcn'
          exact ⟨P, by simp, h1, h2⟩
        · obtain ⟨Q, hQ, hQ1, hQ2⟩ := ih h3 cy (by omega) hc
          exact ⟨Q, by simp [hcn', hQ], hQ1, hQ2⟩

theorem ls_cands_sound {K : KT} {Es : List KE6} {cv cy cref : Nat} :
    ∀ {ws : List KLW} {i : Nat}, lcandsK K Es cv cy cref ws i = true →
      ∀ j, i ≤ j → j < 6 →
        bor (refCK K cv (combK K.d cv cy (j / 2) (j % 2 + 1))
            (ln128 cref (combK K.d cv cy (j / 2) (j % 2 + 1))))
          (lwK K Es cv cy (combK K.d cv cy (j / 2) (j % 2 + 1)) (ws.getD (j - i) .ref)) =
          true := by
  intro ws
  induction ws with
  | nil =>
    intro i h j hij hj
    have h' : Nat.beq i 6 = true := h
    rw [Nat.beq_eq] at h'
    omega
  | cons X tl ih =>
    intro i h j hij hj
    have h' : band (bor (refCK K cv (combK K.d cv cy (i / 2) (i % 2 + 1))
          (ln128 cref (combK K.d cv cy (i / 2) (i % 2 + 1))))
        (lwK K Es cv cy (combK K.d cv cy (i / 2) (i % 2 + 1)) X))
        (lcandsK K Es cv cy cref tl (i + 1)) = true := h
    rw [band_eq_true] at h'
    by_cases hji : j = i
    · subst hji
      rw [Nat.sub_self]
      exact h'.1
    · have := ih h'.2 j (by omega) hj
      have e : j - i = (j - (i + 1)) + 1 := by omega
      rw [e]
      exact this

theorem ls_memE6 {k : Nat} :
    ∀ {Es : List KE6}, memE6K k Es = true → ∃ E ∈ Es, E.k = k := by
  intro Es
  induction Es with
  | nil =>
    intro h
    exact Bool.noConfusion h
  | cons E tl ih =>
    intro h
    have h' : bor (Nat.beq E.k k) (memE6K k tl) = true := h
    rcases bor_iff.mp h' with h1 | h1
    · rw [Nat.beq_eq] at h1
      exact ⟨E, List.mem_cons_self, h1⟩
    · obtain ⟨F, hF, hF'⟩ := ih h1
      exact ⟨F, List.mem_cons_of_mem _ hF, hF'⟩

theorem ls_unsigned (w : KLin) (h : unsignedK w = true) : Chk.unsignedN (decLin w) = true := by
  unfold Chk.unsignedN
  change ((List.range w.nodes.len).map (bit w.neg)).all _ = true
  rw [all_map_range]
  exact h

theorem selE6K_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {k : Nat} {w : KLin} {L : KL} (h : selE6K K k w L = true) :
    Chk.selE6OK (tabsK m K) m k (decLin w) (decDer L) = true := by
  simp only [selE6K, band_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold Chk.selE6OK
  refine cen_and (cen_and (cen_and (cen_and ?_ (ls_unsigned w h2)) (wk_type hT h3).1) ?_) ?_
  · rw [wk_dl_tc, beq_iff_eq]
    exact Nat.eq_of_beq_eq_true h1
  · rw [← wk_nodeMask w (p := fun _ => true) (q := fun _ => true) (fun _ => rfl)]
    exact wk_gen hT h4
  · rw [← wk_notB2 hT]
    exact h5

theorem selD6K_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {j k : Nat} {w : KLin} {L L' : KL} (h : selD6K K j k w L L' = true) :
    Chk.selD6OK (tabsK m K) m j k (decLin w) (decDer L) (decDer L') = true := by
  simp only [selD6K, band_eq_true, bor_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold Chk.selD6OK
  refine cen_and (cen_and (cen_and (cen_and (cen_and (cen_and (cen_and ?_ ?_) ?_)
    (wk_type hT h4).1) ?_) ?_) ?_) ?_
  · rw [wk_dl_tc, beq_iff_eq]
    exact Nat.eq_of_beq_eq_true h1
  · rw [wk_dl_n, beq_iff_eq]
    exact Nat.eq_of_beq_eq_true h2
  · rw [wk_dl_b, Bool.or_eq_true, beq_iff_eq, beq_iff_eq]
    rcases h3 with h3 | h3
    · exact Or.inl (Nat.eq_of_beq_eq_true h3)
    · exact Or.inr (Nat.eq_of_beq_eq_true h3)
  · rw [← wk_nodeMask w (p := fun _ => true) (q := fun _ => true) (fun _ => rfl)]
    exact wk_gen hT h5
  · rw [wk_dl_b, ← wk_nodeMask w (p := fun i => bnot (Nat.beq i w.b)) (q := fun i => i != w.b)
      (fun i => by rw [bnot_eq, nbeq_eq]; rfl)]
    exact wk_gen hT h6
  · rw [← wk_notB2 hT]
    exact h7
  · rw [← wk_notB2 hT]
    exact h8

theorem ls_lw_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {Es : List KE6} {cv cy a b : Nat} {X : KLW}
    (h : lwK K Es cv cy (Chk.combN (dim m) cv cy a b) X = true) :
    ilsBody (tabsK m K) m (e6Masks Es) cv cy a b = true := by
  simp only [ilsBody, Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem]
  cases X with
  | ref => exact Bool.noConfusion h
  | leaf w Ll Lk Bl Bk =>
    have h' : band (commonK K cv (Chk.combN (dim m) cv cy a b) (zmK K cv)
        (zmK K (Chk.combN (dim m) cv cy a b)) w Ll Lk Bl Bk) (leafK w.tc w.n w.b) = true := h
    rw [band_eq_true, zmK_eq hT, zmK_eq hT] at h'
    let W : Chk.CommonW :=
      { w := decLin w, Lℓ := decDer Ll, Lk := decDer Lk, Bℓ := decMat Bl, Bk := decMat Bk }
    refine Or.inl (Or.inl ⟨W, ?_⟩)
    simp only [W, Chk.leafModelOK, Bool.and_eq_true]
    refine ⟨wk_common hT h'.1, ?_⟩
    rw [← wk_leaf]
    exact h'.2
  | d6 w L L' =>
    have h' : selD6K K (Nat.land (zmK K cv) (zmK K cy)) (zmK K (Chk.combN (dim m) cv cy a b)) w L
        L' = true := h
    rw [zmK_eq hT, zmK_eq hT, zmK_eq hT, xk_land] at h'
    exact Or.inl (Or.inr ⟨_, _, _, selD6K_sound hT h'⟩)
  | e6 =>
    have h' : memE6K (zmK K (Chk.combN (dim m) cv cy a b)) Es = true := h
    rw [zmK_eq hT] at h'
    obtain ⟨E, hE, h1⟩ := ls_memE6 h'
    refine Or.inr ?_
    rw [← h1]
    exact List.mem_map.mpr ⟨E, hE, rfl⟩

theorem ls_cands_scan {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (hT : TabsOK m K fx hx fx' hx')
    {Es : List KE6} {L : KLLine} {cy : Nat} {ws : List KLW}
    (h : lcandsK K Es L.cv cy L.cref ws 0 = true) :
    Chk.candScanN (tabsK m K) m (lsearchOf m L) L.cv cy
      (ilsBody (tabsK m K) m (e6Masks Es) L.cv cy) = true := by
  rw [Chk.candScanN, nat_all_iff]
  intro a ha
  rw [nat_all_iff]
  intro b' hb'
  have hj := ls_cands_sound h (2 * a + b') (Nat.zero_le _) (by omega)
  have e1 : (2 * a + b') / 2 = a := by omega
  have e2 : (2 * a + b') % 2 = b' := by omega
  rw [Nat.sub_zero, e1, e2, bor_iff, hT.hd, combK_eq] at hj
  rcases hj with hr | hw
  · obtain ⟨e, he, hok⟩ := refCK_sound hT hr
    refine cen_orL ?_
    simp only [lsearchOf, he]
    exact hok
  · exact cen_orR (ls_lw_sound hT hw)

theorem scanLineLK_sound {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat}
    (hT : TabsOK m K fx hx fx' hx') {Es : List KE6} {L : KLLine}
    (hL : scanLineLK K Es L = true) :
    Chk.scanLineN (tabsK m K) m false true (lsearchOf m L)
      (fun cv cy => Chk.candScanN (tabsK m K) m (lsearchOf m L) cv cy
        (ilsBody (tabsK m K) m (e6Masks Es) cv cy)) L.cv = true := by
  have hd := hT.hd
  have hL' : bor (refLIK K L.cv L.ref) (lwalkK K Es L.cv L.cref (Nat.pow 3 K.d) L.planes) =
      true := hL
  rw [bor_iff] at hL'
  rw [Chk.scanLineN, Bool.or_eq_true]
  rcases hL' with hL' | hL'
  · left
    obtain ⟨e, he, hok⟩ := inl_refLIK_sound hT hL'
    simp only [lsearchOf, if_pos rfl, he]
    exact hok
  · right
    have hW : ∀ n ps, lwalkK K Es L.cv L.cref (n + 1) ps = Bool.rec (motive := fun _ => Bool)
        (lwalkK K Es L.cv L.cref n ps) (List.rec (motive := fun _ => Bool) false
          (fun P tl _ => band (Nat.beq P.cy n) (band (lplaneK K Es L.cv L.cref P)
            (lwalkK K Es L.cv L.cref n tl))) ps) (canonK (dim m) L.cv n) := by
      intro n ps
      rw [← hd]
      rfl
    rw [hd] at hL'
    rw [nat_all_iff]
    intro cy hcy
    rw [Bool.or_eq_true, Bool.or_eq_true]
    by_cases hc : Chk.canonN (dim m) L.cv cy = true
    · obtain ⟨P, hP, hPcy, hpl⟩ := ls_walk_sound hW hL' cy hcy hc
      have hP' : lpick (dim m) L.cv (3 ^ dim m) L.planes cy = some P := hP
      have hpl' : bor (refPK K L.cv P.cy P.ref) (lcandsK K Es L.cv P.cy L.cref P.wits 0) =
          true := hpl
      rw [bor_iff, hPcy] at hpl'
      rcases hpl' with hr | hr
      · left
        right
        obtain ⟨e, he, hok⟩ := refPK_sound hT hr
        simp only [lsearchOf, hP', Option.bind_some, he]
        exact hok
      · right
        exact ls_cands_scan hT hr
    · left
      left
      simp [hc]

variable {m : Fin 6} {T : Chk.Tabs}

@[expose] def sgnR (hT : Chk.tabsOK m T = true) (u t : Root m) : ℤˣ :=
  if Classical.choose (rtR_spec hT u t) = 1 then 1 else -1

theorem sgnR_spec (hT : Chk.tabsOK m T = true) (u t : Root m) :
    (∀ v, root m (rtR hT u t) v = (((sgnR hT u t : ℤˣ) : ℤ) : ZMod 3) * root m t (reflection m u v)) ∧
      coroot m (rtR hT u t) = (((sgnR hT u t : ℤˣ) : ℤ) : ZMod 3) • reflection m u (coroot m t) := by
  obtain ⟨hε, h1, h2⟩ := Classical.choose_spec (rtR_spec hT u t)
  have e : ((sgnR hT u t : ℤˣ) : ℤ) = Classical.choose (rtR_spec hT u t) := by
    unfold sgnR
    rcases hε with h | h <;> simp [h]
  rw [e]
  exact ⟨h1, h2⟩

theorem ls_refl_refl (u : Root m) (v : V m) : reflection m u (reflection m u v) = v :=
  Module.involutive_reflection (root_coroot m u) v

theorem pairing_rtR_mod (hT : Chk.tabsOK m T = true) (u a b : Root m) :
    ((pairing m (rtR hT u a) (rtR hT u b) : ℤ) : ZMod 3) =
      (((sgnR hT u a : ℤˣ) : ℤ) * ((sgnR hT u b : ℤˣ) : ℤ) * pairing m a b : ℤ) := by
  obtain ⟨ha, -⟩ := sgnR_spec hT u a
  obtain ⟨-, hb⟩ := sgnR_spec hT u b
  rw [← pairing_eq, ha, hb, map_smul, ls_refl_refl, map_smul, smul_eq_mul, pairing_eq]
  push_cast
  ring

theorem pairing_rtR (hT : Chk.tabsOK m T = true) (hdiag : ∀ a : Root m, pairing m a a = 2)
    (hoff : ∀ a b : Root m, a ≠ b → -1 ≤ pairing m a b ∧ pairing m a b ≤ 1) (u a b : Root m) :
    pairing m (rtR hT u a) (rtR hT u b) =
      ((sgnR hT u a : ℤˣ) : ℤ) * ((sgnR hT u b : ℤˣ) : ℤ) * pairing m a b := by
  have hs : ∀ x : ℤˣ, (x : ℤ) = 1 ∨ (x : ℤ) = -1 := fun x => by
    rcases Int.units_eq_one_or x with h | h <;> simp [h]
  by_cases hab : a = b
  · subst hab
    rw [hdiag, hdiag]
    rcases hs (sgnR hT u a) with h | h <;> rw [h] <;> norm_num
  · have hne : rtR hT u a ≠ rtR hT u b := fun h => hab (rtR_injective hT u h)
    have h1 := hoff _ _ hne
    have h2 := hoff a b hab
    have hmod := pairing_rtR_mod hT u a b
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hmod
    rcases hs (sgnR hT u a) with ha | ha <;> rcases hs (sgnR hT u b) with hb | hb <;>
      rw [ha, hb] at hmod ⊢ <;> push_cast at hmod ⊢ <;> omega

theorem ls_refl_inv (u : Root m) : (reflection m u)⁻¹ = reflection m u :=
  inv_eq_of_mul_eq_one_right (LinearEquiv.ext fun v => ls_refl_refl u v)

theorem ls_conj_refl (hT : Chk.tabsOK m T = true) (u t : Root m) :
    (MulAut.conj (reflection m u)).toMonoidHom (reflection m t) = reflection m (rtR hT u t) := by
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ls_refl_inv]
  exact (reflection_rt hT u t).symm

theorem inLSelD6Raw_reflection (hT : Chk.tabsOK m T = true)
    (hdiag : ∀ a : Root m, pairing m a a = 2)
    (hoff : ∀ a b : Root m, a ≠ b → -1 ≤ pairing m a b ∧ pairing m a b ≤ 1) (u : Root m)
    {j k : Finset (Root m)} (h : InLSelD6Raw (excRaw m) j k) :
    InLSelD6Raw (excRaw m) (reflCode hT u j) (reflCode hT u k) := by
  have h' : ∃ (e : Fin 6 → Root m) (ε : Fin 6 → ℤˣ) (b : Fin 6), (b = 4 ∨ b = 5) ∧
      (∀ i i', ((ε i : ℤ) * ε i') * pairing m (e i) (e i') = CartanMatrix.D 6 i i') ∧
      normalizerGroup m k = Subgroup.closure (reflection m '' Set.range e) ∧
      normalizerGroup m j = Subgroup.closure (reflection m '' (e '' {i | i ≠ b})) := h
  change ∃ (e : Fin 6 → Root m) (ε : Fin 6 → ℤˣ) (b : Fin 6), (b = 4 ∨ b = 5) ∧
      (∀ i i', ((ε i : ℤ) * ε i') * pairing m (e i) (e i') = CartanMatrix.D 6 i i') ∧
      normalizerGroup m (reflCode hT u k) = Subgroup.closure (reflection m '' Set.range e) ∧
      normalizerGroup m (reflCode hT u j) =
        Subgroup.closure (reflection m '' (e '' {i | i ≠ b}))
  obtain ⟨e, ε, b, hb, hC, hk, hj⟩ := h'
  refine ⟨fun i => rtR hT u (e i), fun i => ε i * sgnR hT u (e i), b, hb, ?_, ?_, ?_⟩
  · intro i i'
    rw [pairing_rtR hT hdiag hoff, Units.val_mul, Units.val_mul, ← hC i i']
    rcases Int.units_eq_one_or (sgnR hT u (e i)) with h1 | h1 <;>
      rcases Int.units_eq_one_or (sgnR hT u (e i')) with h2 | h2 <;>
      simp only [h1, h2, Units.val_one, Units.val_neg] <;> ring
  · rw [normalizerGroup_reflCode, hk, MonoidHom.map_closure, Set.image_image,
      ← Set.range_comp, ← Set.range_comp]
    congr 2
    funext i
    exact ls_conj_refl hT u (e i)
  · rw [normalizerGroup_reflCode, hj, MonoidHom.map_closure]
    simp only [Set.image_image]
    congr 1
    exact Set.image_congr fun i _ => ls_conj_refl hT u (e i)

theorem pairRange_sound {K : KT} {fx hx fx' hx' : Nat} (hK : TabsOK m K fx hx fx' hx')
    (h : pairRangeK K = true) :
    (∀ a : Root m, pairing m a a = 2) ∧
      ∀ a b : Root m, a ≠ b → -1 ≤ pairing m a b ∧ pairing m a b ≤ 1 := by
  have key : ∀ a b : Root m, Bool.rec (motive := fun _ => Bool)
      (band (Nat.ble 7 (prK K a.val b.val)) (Nat.ble (prK K a.val b.val) 9))
      (Nat.beq (prK K a.val b.val) 10) (Nat.beq a.val b.val) = true := by
    intro a b
    exact allN_iff.mp (allN_iff.mp h a.val (by rw [hK.hr]; exact a.isLt)) b.val
      (by rw [hK.hr]; exact b.isLt)
  have hp : ∀ a b : Root m, (prK K a.val b.val : ℤ) = pairing m a b + 8 := by
    intro a b
    rw [prK_eq hK a.isLt b.isLt, ← tabsOK_pair (tabsOK_tabsK hK) a b, tabsK_pair a.isLt b.isLt]
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · have h1 := key a a
    rw [show Nat.beq a.val a.val = true from Nat.beq_eq.mpr rfl] at h1
    have h2 : prK K a.val a.val = 10 := Nat.eq_of_beq_eq_true h1
    have := hp a a
    rw [h2] at this
    omega
  · have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
    have h1 := key a b
    rw [nbeq_false hne] at h1
    have h1' : band (Nat.ble 7 (prK K a.val b.val)) (Nat.ble (prK K a.val b.val) 9) = true := h1
    rw [band_eq_true, Nat.ble_eq, Nat.ble_eq] at h1'
    have := hp a b
    omega

theorem ls_reflMask_rec {K : KT} {u n x : Nat} :
    ∀ {s : Nat}, (Nat.rec (motive := fun _ => Nat) 0
      (fun t acc => nif (bit n t) (Nat.lor acc (Nat.shiftLeft 1 (rtK K u t))) acc) s :
        Nat).testBit x = true ↔ ∃ t < s, n.testBit t = true ∧ rtK K u t = x := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    have e : (Nat.rec (motive := fun _ => Nat) 0
        (fun t acc => nif (bit n t) (Nat.lor acc (Nat.shiftLeft 1 (rtK K u t))) acc) (s + 1) :
          Nat) =
        nif (bit n s) (Nat.lor (Nat.rec (motive := fun _ => Nat) 0
          (fun t acc => nif (bit n t) (Nat.lor acc (Nat.shiftLeft 1 (rtK K u t))) acc) s)
          (Nat.shiftLeft 1 (rtK K u s))) (Nat.rec (motive := fun _ => Nat) 0
          (fun t acc => nif (bit n t) (Nat.lor acc (Nat.shiftLeft 1 (rtK K u t))) acc) s) := rfl
    rw [e, nif_eq, bit_eq]
    cases hb : n.testBit s
    · simp only [Bool.false_eq_true, if_false]
      rw [ih]
      constructor
      · rintro ⟨t, ht, h1, h2⟩
        exact ⟨t, by omega, h1, h2⟩
      · rintro ⟨t, ht, h1, h2⟩
        have hts : t ≠ s := by
          rintro rfl
          rw [hb] at h1
          exact Bool.noConfusion h1
        exact ⟨t, by omega, h1, h2⟩
    · simp only [if_true]
      change (_ ||| 1 <<< rtK K u s).testBit x = true ↔ _
      rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.one_shiftLeft,
        Nat.testBit_two_pow, decide_eq_true_eq]
      constructor
      · rintro (⟨t, ht, h1, h2⟩ | h)
        · exact ⟨t, by omega, h1, h2⟩
        · exact ⟨s, by omega, hb, h⟩
      · rintro ⟨t, ht, h1, h2⟩
        by_cases hts : t = s
        · subst hts
          exact Or.inr h2
        · exact Or.inl ⟨t, by omega, h1, h2⟩

theorem ofMask_reflMaskK {K : KT} {fx hx fx' hx' : Nat} (hK : TabsOK m K fx hx fx' hx')
    (u : Root m) (n : Nat) :
    ofMask m (reflMaskK K u.val n) = reflCode (tabsOK_tabsK hK) u (ofMask m n) := by
  ext x
  rw [mem_ofMask, reflCode_apply, Finset.mem_map]
  have e : reflMaskK K u.val n = (Nat.rec (motive := fun _ => Nat) 0
      (fun t acc => nif (bit n t) (Nat.lor acc (Nat.shiftLeft 1 (rtK K u.val t))) acc)
      (nroots m) : Nat) := by
    unfold reflMaskK
    rw [hK.hr]
  rw [e, ls_reflMask_rec]
  constructor
  · rintro ⟨t, ht, h1, h2⟩
    refine ⟨⟨t, ht⟩, mem_ofMask.mpr h1, ?_⟩
    apply Fin.ext
    have e2 : ((tabsK m K).rt[u.val]!)[t]! = rtK K u.val t := tabsK_rt u.isLt ht
    rw [← h2, ← e2]
    rfl
  · rintro ⟨t, ht, h⟩
    refine ⟨t.val, t.isLt, mem_ofMask.mp ht, ?_⟩
    have h' := congrArg Fin.val h
    have e2 : ((tabsK m K).rt[u.val]!)[t.val]! = rtK K u.val t.val := tabsK_rt u.isLt t.isLt
    rw [← e2, ← h']
    rfl

theorem ls_e6All {K : KT} {Es : List KE6} :
    ∀ {Fs : List KE6}, e6AllK K Es Fs = true → ∀ E ∈ Fs, e6OKK K Es E = true := by
  intro Fs
  induction Fs with
  | nil =>
    intro _ E hE
    simp at hE
  | cons F tl ih =>
    intro h E hE
    have h' : band (e6OKK K Es F) (e6AllK K Es tl) = true := h
    rw [band_eq_true] at h'
    rcases List.mem_cons.mp hE with rfl | hE
    · exact h'.1
    · exact ih h'.2 E hE

theorem selP_reflection {K : KT} {fx hx fx' hx' : Nat} (hK : TabsOK m K fx hx fx' hx')
    (hpr : pairRangeK K = true) {Es : List KE6} (hE : e6AllK K Es Es = true) (u : Root m)
    (j k : Finset (Root m)) (h : SelP m (e6Masks Es) j k) :
    SelP m (e6Masks Es) (reflCode (tabsOK_tabsK hK) u j) (reflCode (tabsOK_tabsK hK) u k) := by
  rcases h with h | ⟨n, hn, rfl⟩
  · obtain ⟨hdiag, hoff⟩ := pairRange_sound hK hpr
    exact Or.inl (inLSelD6Raw_reflection (tabsOK_tabsK hK) hdiag hoff u h)
  · obtain ⟨E, hE', rfl⟩ := List.mem_map.mp hn
    have h1 := ls_e6All hE E hE'
    simp only [e6OKK, band_eq_true] at h1
    have h2 := allN_iff.mp h1.2 u.val (by rw [hK.hr]; exact u.isLt)
    obtain ⟨E', hE'', e1⟩ := ls_memE6 h2
    refine Or.inr ⟨E'.k, List.mem_map.mpr ⟨E', hE'', rfl⟩, ?_⟩
    rw [← ofMask_reflMaskK hK, ← e1]

theorem selP_sound {K : KT} {fx hx fx' hx' : Nat} (hK : TabsOK m K fx hx fx' hx')
    {Es : List KE6} (hE : e6AllK K Es Es = true) (j k : Finset (Root m))
    (h : SelP m (e6Masks Es) j k) : InLSelD6Raw (excRaw m) j k ∨ InLSelDetRaw (excRaw m) k := by
  rcases h with h | ⟨n, hn, rfl⟩
  · exact Or.inl h
  · obtain ⟨E, hE', rfl⟩ := List.mem_map.mp hn
    have h1 := ls_e6All hE E hE'
    simp only [e6OKK, band_eq_true] at h1
    exact Or.inr (inLSelDetRaw_of_selE6OK (tabsOK_tabsK hK) (selE6K_sound hK h1.1))

end CFSG.ExcExtK

end

end
