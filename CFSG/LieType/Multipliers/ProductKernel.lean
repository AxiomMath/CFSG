module

public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.Certificates.CosetTableRelations

public section

namespace CFSG.LieType.Multipliers

open Subgroup CFSG.CosetTable CFSG.Open CFSG.Certificates.CosetEnumeration

variable {m : ℕ}

theorem pow_mem_genSub_of_orderCheck {ws : List (List (Fin m × Bool))} {S : List ℕ}
    {k cap n : ℕ} {words : List (List (Fin m × Bool) × ℕ)} {fuel : ℕ}
    (h : orderCheck ws S k cap n words fuel = true) {u : List (Fin m × Bool)} {ℓ : ℕ}
    (hmem : (u, ℓ) ∈ words) (hℓ : 0 < ℓ) :
    PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk u) ^ ℓ ∈
      genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S) := by
  unfold orderCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨-, hc⟩, -⟩, -⟩, -⟩, hwords⟩ := h
  set P := colParamsShort ws ((subsetOf m S).map fun x => [(x, true)]) k with hPdef
  set st := enumerateHLT P cap with hst
  set H := genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)
  have hgood : Good (colLetter ws) H P :=
    goodColParamsShort ws _ k H (genSub_words_mem ws (subsetOf m S))
  have hinv : SInv P.L (colLetter ws) H st := enumerateHLT_inv hgood cap
  have hc' := hc
  unfold St.complete at hc'
  rw [Bool.and_eq_true, allBelow_iff] at hc'
  obtain ⟨h1, hrow⟩ := hc'
  have hlive : ∀ c, st.live c = true → 0 < c ∧ c < st.next := fun c hc => St.live_lt hc
  have hstep : ∀ c, st.live c = true → ∀ x < P.L,
      st.live (st.tab.getD (c * P.L + x) 0) = true ∧
        Rel P.L (colLetter ws) H st.par c (colLetter ws x) (st.tab.getD (c * P.L + x) 0) := by
    intro c hc x hx
    have hr := hrow c (hlive c hc).2
    simp only [hc, Bool.not_true, Bool.false_or, allBelow_iff] at hr
    have hl := hr x hx
    refine ⟨hl, ?_⟩
    have hne : st.tab.getD (c * P.L + x) 0 ≠ 0 := by
      have := (hlive _ hl).1; omega
    have := hinv.tab_rel _ hne
    obtain ⟨dd, mm⟩ := div_mod_letter (c := c) hx
    rwa [dd, mm] at this
  set δ : ℕ → ℕ → ℕ := fun c x => st.tab.getD (c * P.L + x) 0
  have hwalk : ∀ w : List ℕ, (∀ y ∈ w, y < P.L) → ∀ c, st.live c = true →
      st.live (w.foldl δ c) = true ∧
        Rel P.L (colLetter ws) H st.par c (evalWord (colLetter ws) w) (w.foldl δ c) := by
    intro w
    induction w with
    | nil => intro _ c hc; exact ⟨hc, Rel.refl _ _⟩
    | cons y w ih =>
      intro hw c hc
      obtain ⟨hl, hr⟩ := hstep c hc y (hw y (by simp))
      obtain ⟨hl', hr'⟩ := ih (fun z hz => hw z (by simp [hz])) _ hl
      refine ⟨hl', ?_⟩
      rw [evalWord_cons]
      exact hr.trans hr'
  set w := u.map (colCode ws)
  have hw : ∀ y ∈ w, y < P.L := fun y hy => by
    simp only [w, List.mem_map] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact colCode_lt ws x
  set f : ℕ → ℕ := fun d => w.foldl δ d
  have hiter : ∀ j c, st.live c = true → st.live (f^[j] c) = true ∧
      Rel P.L (colLetter ws) H st.par c (evalWord (colLetter ws) w ^ j) (f^[j] c) := by
    intro j
    induction j with
    | zero => intro c hc; exact ⟨hc, by simpa using Rel.refl st.par c⟩
    | succ j ih =>
      intro c hc
      obtain ⟨hl, hr⟩ := hwalk w hw c hc
      obtain ⟨hl', hr'⟩ := ih _ hl
      refine ⟨by rw [Function.iterate_succ_apply]; exact hl', ?_⟩
      rw [Function.iterate_succ_apply, pow_succ']
      exact hr.trans hr'
  have hcyc := (cycleLength_spec P.L st.tab w 1 fuel ℓ (hwords _ hmem) hℓ).1
  obtain ⟨-, hrel⟩ := hiter ℓ 1 h1
  have hf : f^[ℓ] 1 = 1 := hcyc
  rw [hf, rel_iff, hinv.rep_one, one_mul, inv_one, mul_one] at hrel
  rw [← evalWord_colCode ws u]
  exact hrel

@[expose] def relCheckShort (ws : List (List (Fin m × Bool))) (k cap : ℕ)
    (us : List (List (Fin m × Bool))) : Bool :=
  let P := colParamsShort ws [] k
  let st := enumerateHLT P cap
  (colCodes ws us).all fun w => walk P.L st.tab w.length 0 1 w == (w.length, 1)

theorem eq_one_of_relCheckShort {ws : List (List (Fin m × Bool))} {k cap : ℕ}
    {us : List (List (Fin m × Bool))} (h : relCheckShort ws k cap us = true) :
    ∀ u ∈ us, PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk u) = 1 := by
  intro u hu
  have hg : Good (colLetter ws) (⊥ : Subgroup (PG m ws)) (colParamsShort ws [] k) :=
    goodColParamsShort ws [] k ⊥ (by simp)
  have hinv := enumerateHLT_inv hg cap
  set st := enumerateHLT (colParamsShort ws [] k) cap
  have hcode : u.map (colCode ws) ∈ colCodes ws us := List.mem_map_of_mem hu
  simp only [relCheckShort, List.all_eq_true, beq_iff_eq] at h
  have hw := h _ hcode
  have hlet : ∀ y ∈ u.map (colCode ws), y < (colParamsShort ws [] k).L := fun y hy =>
    letters_colCodes hcode y hy
  obtain ⟨-, -, hrel, -⟩ := walk_spec hinv (u.map (colCode ws)) (u.map (colCode ws)).length 0 1
    hlet
  rw [hw] at hrel
  simp only [Nat.sub_zero, List.take_length] at hrel
  rw [rel_iff, Inv.rep_one hinv, Subgroup.mem_bot, one_mul, inv_one, mul_one,
    evalWord_colCode] at hrel
  exact hrel

@[expose] def boxTuples : List ℕ → List (List ℕ)
  | [] => [[]]
  | e :: es => (List.range e).flatMap fun a => (boxTuples es).map (a :: ·)

@[expose] def boxWord : List (List (Fin m × Bool)) → List ℕ → List (Fin m × Bool)
  | u :: us, a :: as => (List.replicate a u).flatten ++ boxWord us as
  | _, _ => []

@[expose] def boxOrder : List ℕ → List ℕ → ℕ
  | e :: es, a :: as => Nat.lcm (e / Nat.gcd a e) (boxOrder es as)
  | _, _ => 1

@[expose] def kernelWords (t : List (List (Fin m × Bool) × ℕ)) : List (List (Fin m × Bool) × ℕ) :=
  t ++ ((boxTuples (t.map Prod.snd)).filter fun as => as.any (· != 0)).map fun as =>
    (boxWord (t.map Prod.fst) as, boxOrder (t.map Prod.snd) as)

private theorem mem_boxTuples {as es : List ℕ} (h : List.Forall₂ (· < ·) as es) :
    as ∈ boxTuples es := by
  induction h with
  | nil => simp [boxTuples]
  | cons hab _ ih =>
    simp only [boxTuples, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨_, hab, _, ih, rfl⟩

private theorem boxOrder_pos {as es : List ℕ} (h : List.Forall₂ (· < ·) as es) :
    0 < boxOrder es as := by
  induction h with
  | nil => simp [boxOrder]
  | cons hab _ ih =>
    simp only [boxOrder]
    exact Nat.lcm_pos (Nat.div_pos (Nat.gcd_le_right _ (by omega)) (Nat.gcd_pos_of_pos_right _
      (by omega))) ih

private theorem two_le_boxOrder {as es : List ℕ} (h : List.Forall₂ (· < ·) as es)
    (hne : as.any (· != 0) = true) : 2 ≤ boxOrder es as := by
  induction h with
  | nil => simp at hne
  | @cons a e as es hab hrest ih =>
    simp only [boxOrder]
    by_cases ha : a = 0
    · subst ha
      simp only [List.any_cons, bne_self_eq_false, Bool.false_or] at hne
      have := ih hne
      have hd : boxOrder es as ∣ Nat.lcm (e / Nat.gcd 0 e) (boxOrder es as) :=
        Nat.dvd_lcm_right _ _
      exact this.trans (Nat.le_of_dvd (Nat.lcm_pos (Nat.div_pos (Nat.gcd_le_right _ (by omega))
        (Nat.gcd_pos_of_pos_right _ (by omega))) (boxOrder_pos hrest)) hd)
    · have hg : Nat.gcd a e < e := lt_of_le_of_lt (Nat.gcd_le_left _ (by omega)) hab
      have hgpos : 0 < Nat.gcd a e := Nat.gcd_pos_of_pos_right _ (by omega)
      have h2 : 2 ≤ e / Nat.gcd a e := by
        obtain ⟨q, hq⟩ := Nat.gcd_dvd_right a e
        have hdiv : e / Nat.gcd a e = q := Nat.div_eq_of_eq_mul_right hgpos hq
        rw [hdiv]
        by_contra hq'
        interval_cases q <;> omega
      exact h2.trans (Nat.le_of_dvd (Nat.lcm_pos (by omega) (boxOrder_pos hrest))
        (Nat.dvd_lcm_left _ _))

@[expose] def boxProd {G : Type*} [Group G] : List G → List ℕ → G
  | z :: zs, a :: as => z ^ a * boxProd zs as
  | _, _ => 1

private theorem mk_boxWord {G : Type*} [Group G] (φ : FreeGroup (Fin m) →* G) :
    ∀ (us : List (List (Fin m × Bool))) (as : List ℕ),
      φ (FreeGroup.mk (boxWord us as)) = boxProd (us.map fun u => φ (FreeGroup.mk u)) as
  | u :: us, a :: as => by
    rw [boxWord, ← FreeGroup.mul_mk, map_mul, mk_flatten_replicate, map_pow, mk_boxWord φ us as]
    rfl
  | [], _ => by
    show φ (FreeGroup.mk []) = 1
    rw [← FreeGroup.one_eq_mk, map_one]
  | _ :: _, [] => by
    show φ (FreeGroup.mk []) = 1
    rw [← FreeGroup.one_eq_mk, map_one]

private theorem boxProd_ofFn {G : Type*} [Group G] :
    ∀ (r : ℕ) (z : Fin r → G) (a : Fin r → ℕ),
      boxProd (List.ofFn z) (List.ofFn a) = (List.ofFn fun j => z j ^ a j).prod
  | 0, _, _ => rfl
  | r + 1, z, a => by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, boxProd, List.prod_cons,
      boxProd_ofFn r]

private theorem pow_val_add {C : Type*} [CommGroup C] {e : ℕ} [NeZero e] {z : C}
    (hz : z ^ e = 1) (a b : ZMod e) : z ^ (a + b).val = z ^ a.val * z ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) e, pow_add, pow_mul, hz, one_pow, mul_one]

private def piHom {C : Type*} [CommGroup C] {r : ℕ} (e : Fin r → ℕ) [∀ j, NeZero (e j)]
    (z : Fin r → C) (hz : ∀ j, z j ^ e j = 1) :
    Multiplicative ((j : Fin r) → ZMod (e j)) →* C where
  toFun a := ∏ j, z j ^ (a.toAdd j).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [toAdd_mul, Pi.add_apply, pow_val_add (hz j)]

private theorem piHom_apply {C : Type*} [CommGroup C] {r : ℕ} (e : Fin r → ℕ)
    [∀ j, NeZero (e j)] (z : Fin r → C) (hz : ∀ j, z j ^ e j = 1) (a) :
    piHom e z hz a = ∏ j, z j ^ (a.toAdd j).val := rfl

theorem multiplier_eq_pi_of_orderCheck {X : Type} [Group X] {g : Fin m → X}
    {R : List (List (Fin m × Bool))} (hP : IsPresentation g (wordSet R))
    (c : Fin m → List (List (Fin m × Bool) × List (Fin m × Bool)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (commWords (c i))) = g i)
    (t : List (List (Fin m × Bool) × ℕ)) (ht : ∀ p ∈ t, FreeGroup.lift g (FreeGroup.mk p.1) = 1)
    (hpos : ∀ p ∈ t, 0 < p.2) (us : List (List (Fin m × Bool))) (s : Fin m) {κ : ℕ}
    (hκ : List.replicate κ (s, true) ∈ us) (hord : orderOf (g s) = κ)
    (hus : ∀ u ∈ us, PresentedGroup.mk
      {r : FreeGroup (Fin m) | r ∈ (coverWords R fun i => commWords (c i)).map FreeGroup.mk}
      (FreeGroup.mk u) = 1)
    {k cap n fuel cap₂ : ℕ}
    (h : orderCheck (coverWords R (fun i => commWords (c i)) ++ us) [s.val] k cap n
      (kernelWords t) fuel = true)
    (hsub : subsetCheckC (restrictWords (subsetOf m [s.val])
      (coverWords R (fun i => commWords (c i)) ++ us)) [] cap₂ κ = true)
    (hn : n * κ ≤ (t.map Prod.snd).prod * Nat.card X) :
    Group.IsPerfect X ∧
      Nonempty (griessHopfMultiplier X ≃* Multiplicative ((j : Fin t.length) → ZMod t[j].2)) := by
  have hw : ∀ i, FreeGroup.mk (commWords (c i)) ∈ commutator (FreeGroup (Fin m)) :=
    fun i => mk_commWords_mem_commutator _
  refine ⟨isPerfect_of_isPresentation hP hw hwg, ?_⟩
  set ws := coverWords R fun i => commWords (c i) with hws
  set w : Fin m → FreeGroup (Fin m) := fun i => FreeGroup.mk (commWords (c i))
  obtain ⟨hfin, hle⟩ : Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n * κ := by
    refine card_le_of_append ws _ hus ?_
    obtain ⟨hf1, hc1⟩ := card_le_of_subsetCheckC_nil _ hsub
    obtain ⟨hf2, hc2⟩ := card_le_of_subsetCheckShortC _ [s.val] (subsetCheckShortC_of_orderCheck h)
    exact ⟨hf2, hc2.trans (Nat.mul_le_mul_left _ hc1)⟩
  have hset := coverRelators_wordSet R fun i => commWords (c i)
  have hNZ : ∀ j : Fin t.length, NeZero t[j].2 := fun j => ⟨(hpos _ (List.getElem_mem _)).ne'⟩
  set E := PG m ws
  have he : ∀ r ∈ coverRelators (wordSet R) w,
      FreeGroup.lift (PresentedGroup.of : Fin m → E) r = 1 := by
    intro r hr
    rw [show coverRelators (wordSet R) w = wordSet ws from hset] at hr
    have hl : FreeGroup.lift (PresentedGroup.of : Fin m → E) =
        PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} :=
      FreeGroup.ext_hom _ _ fun _ => FreeGroup.lift_apply_of
    rw [hl]
    exact PresentedGroup.one_of_mem hr
  set mkE : FreeGroup (Fin m) →* E :=
    PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  have hlift : FreeGroup.lift (PresentedGroup.of : Fin m → E) = mkE :=
    FreeGroup.ext_hom _ _ fun _ => FreeGroup.lift_apply_of
  have key : ∀ S : Set (FreeGroup (Fin m)), wordSet ws = S → S = coverRelators (wordSet R) w →
      Finite (PresentedCover (wordSet R) w) ∧
        Nat.card (PresentedCover (wordSet R) w) ≤ (t.map Prod.snd).prod * Nat.card X ∧
        ∀ v : FreeGroup (Fin m), FreeGroup.lift g v = 1 → mkE v ∈ center E := by
    rintro S rfl hS
    refine ⟨by rw [PresentedCover, ← hS]; exact hfin,
      by rw [PresentedCover, ← hS]; exact hle.trans hn, fun v hv => ?_⟩
    have hz : PresentedGroup.mk (coverRelators (wordSet R) w) v ∈ (coverMap hP hwg).ker := by
      rw [MonoidHom.mem_ker, coverMap_mk]; exact hv
    have hcen := coverMap_ker_le_center hP hwg hz
    have hsurj : Function.Surjective (PresentedGroup.toGroup he) := by
      rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of, closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of he⟩
    have himg : PresentedGroup.toGroup he (PresentedGroup.mk (coverRelators (wordSet R) w) v) =
        mkE v := by
      show FreeGroup.lift _ v = _
      rw [hlift]
    rw [← himg, mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := hsurj y
    rw [← map_mul, ← map_mul, mem_center_iff.mp hcen y']
  obtain ⟨hfinP, hcard, hcen⟩ := key _ rfl hset.symm
  let _ : CommGroup (center E) :=
    { (center E).toGroup with mul_comm := fun a b => Subtype.ext (mem_center_iff.mp b.2 a) }
  set z : Fin t.length → center E := fun j => ⟨mkE (FreeGroup.mk t[j].1),
    hcen _ (ht _ (List.getElem_mem _))⟩ with hzdef
  have hf : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ (ws ++ us).map FreeGroup.mk},
      FreeGroup.lift (PresentedGroup.of : Fin m → E) r = 1 := by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map, List.mem_append] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    rw [hlift]
    rcases hv with hv | hv
    · exact PresentedGroup.one_of_mem (List.mem_map_of_mem hv)
    · exact hus v hv
  have hfmk : ∀ v, PresentedGroup.toGroup hf
      (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ (ws ++ us).map FreeGroup.mk} v) = mkE v := by
    intro v
    have hc : (PresentedGroup.toGroup hf).comp
        (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ (ws ++ us).map FreeGroup.mk}) = mkE := by
      rw [← hlift]
      exact FreeGroup.ext_hom _ _ fun i => by
        rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
        exact PresentedGroup.toGroup.of hf
    rw [← MonoidHom.comp_apply, hc]
  have hX : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}, FreeGroup.lift g r = 1 := by
    intro r hr
    have := lift_coverRelators_eq_one hP hwg r
    rw [show coverRelators (wordSet R) w = wordSet ws from hset] at this
    exact this hr
  have hπ : ∀ v, PresentedGroup.toGroup hX (mkE v) = FreeGroup.lift g v := by
    intro v
    have hc : (PresentedGroup.toGroup hX).comp mkE = FreeGroup.lift g :=
      FreeGroup.ext_hom _ _ fun i => by
        rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
        exact PresentedGroup.toGroup.of hX
    rw [← MonoidHom.comp_apply, hc]
  have hxs : (PresentedGroup.of s : E) = mkE (FreeGroup.mk [(s, true)]) := rfl
  have hsκ : (PresentedGroup.of s : E) ^ κ = 1 := by
    rw [hxs, ← map_pow, ← mk_flatten_replicate]
    have := hus _ hκ
    simpa [List.flatten_replicate_singleton] using this
  have hpow : ∀ j, z j ^ t[j].2 = 1 := by
    intro j
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, z]
    have hp := pow_mem_genSub_of_orderCheck h (u := t[j].1) (ℓ := t[j].2)
      (List.mem_append_left _ (List.getElem_mem _)) (hpos _ (List.getElem_mem _))
    have hle : genSub {r : FreeGroup (Fin m) | r ∈ (ws ++ us).map FreeGroup.mk}
        (subsetOf m [s.val]) ≤ (Subgroup.zpowers (PresentedGroup.of s : E)).comap
          (PresentedGroup.toGroup hf) := by
      rw [genSub, closure_le]
      rintro _ ⟨x, hx, rfl⟩
      have hxs' : x = s := by
        have hx' : x ∈ subsetOf m [s.val] := hx
        simp only [subsetOf, List.mem_filter] at hx'
        have := hx'.2
        simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at this
        exact Fin.ext this
      subst hxs'
      refine Subgroup.mem_comap.mpr ?_
      rw [PresentedGroup.toGroup.of]
      exact Subgroup.mem_zpowers _
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hle hp)
    rw [← hfmk, ← map_pow, ← hi]
    have hgi : g s ^ i = 1 := by
      have htj : FreeGroup.lift g (FreeGroup.mk t[j].1) = 1 := ht t[j] (List.getElem_mem _)
      have := congrArg (PresentedGroup.toGroup hX) hi
      rw [map_zpow, map_pow (PresentedGroup.toGroup hf), hfmk, map_pow, hπ, htj, one_pow,
        PresentedGroup.toGroup.of] at this
      exact this
    rw [← orderOf_dvd_iff_zpow_eq_one, hord] at hgi
    obtain ⟨q, rfl⟩ := hgi
    rw [zpow_mul, zpow_natCast, hsκ, one_zpow]
  set φ := @piHom (center E) _ t.length (fun j => t[j].2) hNZ z hpow
  have hcoe : ∀ a, ((φ a : center E) : E) =
      (List.ofFn fun j => mkE (FreeGroup.mk t[j].1) ^ (a.toAdd j).val).prod := by
    intro a
    rw [piHom_apply, ← List.prod_ofFn]
    show (center E).subtype (List.ofFn _).prod = _
    rw [map_list_prod, List.map_ofFn]
    rfl
  have hφ : ∀ a, ((φ a : center E) : E) =
      mkE (FreeGroup.mk (boxWord (t.map Prod.fst) (List.ofFn fun j => (a.toAdd j).val))) := by
    intro a
    rw [hcoe, mk_boxWord mkE]
    have hts : t.map Prod.fst = List.ofFn fun j : Fin t.length => t[j].1 := by
      apply List.ext_getElem <;> simp
    rw [hts, List.map_ofFn, boxProd_ofFn]
    rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    by_contra hne
    set as := List.ofFn fun j : Fin t.length => (a.toAdd j).val
    have hF : List.Forall₂ (· < ·) as (t.map Prod.snd) := by
      have hts : t.map Prod.snd = List.ofFn fun j : Fin t.length => t[j].2 := by
        apply List.ext_getElem <;> simp
      rw [hts, List.forall₂_iff_get]
      refine ⟨by simp [as], fun i h1 h2 => ?_⟩
      simp only [as, List.get_eq_getElem, List.getElem_ofFn]
      exact ZMod.val_lt _
    have hany : as.any (· != 0) = true := by
      rw [List.any_eq_true]
      obtain ⟨j, hj⟩ : ∃ j, a.toAdd j ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hne (by ext j; exact hall j)
      refine ⟨(a.toAdd j).val, List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
      simpa [ZMod.val_eq_zero] using hj
    have hmem : (boxWord (t.map Prod.fst) as, boxOrder (t.map Prod.snd) as) ∈ kernelWords t :=
      List.mem_append_right _
        (List.mem_map.mpr ⟨as, List.mem_filter.mpr ⟨mem_boxTuples hF, hany⟩, rfl⟩)
    have h2 := two_le_boxOrder hF hany
    have hdvd := dvd_orderOf_of_orderCheck h hmem (by omega)
    have h1 : mkE (FreeGroup.mk (boxWord (t.map Prod.fst) as)) = 1 := by
      rw [← hφ, ha, OneMemClass.coe_one]
    have hg : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk},
        FreeGroup.lift (PresentedGroup.of : Fin m → PG m (ws ++ us)) r = 1 := by
      intro r hr
      simp only [Set.mem_ofPred_eq, List.mem_map] at hr
      obtain ⟨v, hv, rfl⟩ := hr
      rw [lift_of_mk]
      exact PresentedGroup.one_of_mem (List.mem_map_of_mem (List.mem_append_left _ hv))
    have hmap : PresentedGroup.toGroup hg (mkE (FreeGroup.mk (boxWord (t.map Prod.fst) as))) =
        PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ (ws ++ us).map FreeGroup.mk}
          (FreeGroup.mk (boxWord (t.map Prod.fst) as)) := by
      have hc : (PresentedGroup.toGroup hg).comp mkE =
          FreeGroup.lift (PresentedGroup.of : Fin m → PG m (ws ++ us)) :=
        FreeGroup.ext_hom _ _ fun i => by
          rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
          exact PresentedGroup.toGroup.of hg
      rw [← MonoidHom.comp_apply, hc, lift_of_mk]
    have hd := orderOf_map_dvd (PresentedGroup.toGroup hg)
      (mkE (FreeGroup.mk (boxWord (t.map Prod.fst) as)))
    rw [hmap, h1, orderOf_one] at hd
    have := hdvd.trans hd
    rw [Nat.dvd_one] at this
    omega
  set ψ := (center E).subtype.comp φ
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp hinj
  have hK₀ : Nat.card ψ.range = (t.map Prod.snd).prod := by
    rw [Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv.symm, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, Fintype.card_pi]
    simp only [ZMod.card]
    have hts : t.map Prod.snd = List.ofFn fun j : Fin t.length => t[j].2 := by
      apply List.ext_getElem <;> simp
    rw [hts, List.prod_ofFn]
  have hT : ∀ v ∈ {v | ∃ p ∈ t, v = FreeGroup.mk p.1}, FreeGroup.lift g v = 1 := by
    rintro _ ⟨p, hp, rfl⟩
    exact ht p hp
  have hK : ψ.range ≤ closure (FreeGroup.lift (PresentedGroup.of : Fin m → E) ''
      {v | ∃ p ∈ t, v = FreeGroup.mk p.1}) := by
    rintro _ ⟨a, rfl⟩
    show ((φ a : center E) : E) ∈ _
    rw [hcoe]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    refine Subgroup.pow_mem _ (subset_closure ?_) _
    exact ⟨FreeGroup.mk t[j].1, ⟨t[j], List.getElem_mem _, rfl⟩, by rw [hlift]⟩
  obtain ⟨eM⟩ := nonempty_griessHopfMultiplier_mulEquiv_closure hP hw hwg hcard he hT hK₀ hK
  exact ⟨eM.trans (MonoidHom.ofInjective hψinj).symm⟩

end CFSG.LieType.Multipliers
