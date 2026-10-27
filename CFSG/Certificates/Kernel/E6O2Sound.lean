module

public import Certificates.Data.Kernel.E6O2
public import CFSG.Certificates.Kernel.E6Syl3Sound
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc

public section

namespace CFSG.KC.E6O2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3 CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.KC.E6Syl3


@[expose] noncomputable def pSub (gw : List (List ℕ)) : Subgroup (WeylGroup Tag.E6) :=
  Subgroup.closure {g | ∃ w ∈ gw, g = wordW w}

theorem wordW_mem {gw : List (List ℕ)} {w : List ℕ} (hw : w ∈ gw) : wordW w ∈ pSub gw :=
  Subgroup.subset_closure (⟨w, hw, rfl⟩ : ∃ v ∈ gw, wordW w = wordW v)

theorem pSub_mono {ws gw : List (List ℕ)} (h : ∀ w ∈ ws, w ∈ gw) : pSub ws ≤ pSub gw := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨w, hw, rfl⟩
  exact wordW_mem (h w hw)

theorem exists_mem_of_mem_pcTups {n : ℕ} : ∀ {gw : List (List ℕ)}, (∀ w ∈ gw, ∀ i ∈ w, i < 6) →
    ∀ {t : List ℕ}, t ∈ pcTups n gw → ∃ x ∈ pSub gw, e6Certificate.Represents t x
  | [], _, t, ht => by
    simp only [pcTups, List.foldr_nil, List.mem_singleton] at ht
    subst ht
    exact ⟨1, one_mem _, RootCertificate.represents_one e6Certificate_check⟩
  | w :: ws, hl, t, ht => by
    rw [pcTups, List.foldr_cons] at ht
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at ht
    obtain ⟨a, -, t', ht', rfl⟩ := ht
    obtain ⟨x, hx, hrep⟩ := exists_mem_of_mem_pcTups (n := n) (gw := ws)
      (fun v hv => hl v (List.mem_cons_of_mem _ hv)) (t := t') ht'
    have hw : wordW w ∈ pSub (w :: ws) := wordW_mem List.mem_cons_self
    refine ⟨wordW w ^ a * x, mul_mem (pow_mem hw a)
      (pSub_mono (fun v hv => List.mem_cons_of_mem _ hv) hx), ?_⟩
    exact rep_powT (hl w List.mem_cons_self) hrep a

theorem exists_subgroup_of_subCheck {n N : ℕ} {gw : List (List ℕ)}
    (h : subCheck gw N (pcTups n gw) = true) :
    Nat.card (pSub gw) = N ∧ ∀ y ∈ pSub gw, ∃ t ∈ pcTups n gw, e6Certificate.Represents t y := by
  set Q := pcTups n gw with hQ
  simp only [subCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨hl, hlen⟩, hnd⟩, hid⟩, hcl⟩ := h
  have hnodup := nodup_of_nodupB Q hnd
  have hstep : ∀ w ∈ gw, ∀ z : WeylGroup Tag.E6, (∃ t ∈ Q, e6Certificate.Represents t z) →
      ∃ t ∈ Q, e6Certificate.Represents t (wordW w * z) := by
    rintro w hw z ⟨t, ht, hrep⟩
    exact ⟨_, hcl t ht w hw, rep_wordT hrep w (hl w hw)⟩
  have hpow : ∀ w ∈ gw, ∀ m : ℕ, ∀ z : WeylGroup Tag.E6, (∃ t ∈ Q, e6Certificate.Represents t z) →
      ∃ t ∈ Q, e6Certificate.Represents t (wordW w ^ m * z) := by
    intro w hw m
    induction m with
    | zero => intro z hz; simpa using hz
    | succ m ih =>
      intro z hz
      rw [pow_succ', mul_assoc]
      exact hstep w hw _ (ih z hz)
  have hcover : ∀ g ∈ pSub gw, ∃ t ∈ Q, e6Certificate.Represents t g := by
    intro g hg
    induction hg using Subgroup.closure_induction_left with
    | one => exact ⟨_, hid, RootCertificate.represents_one e6Certificate_check⟩
    | mul_left x hx z _ ih =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact hstep w hw z ih
    | inv_mul_cancel x hx z _ ih =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨t, ht, hrep⟩ := hpow w hw (orderOf (wordW w) - 1) z ih
      refine ⟨t, ht, ?_⟩
      convert hrep using 2
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_succ, Nat.sub_add_cancel (isOfFinOrder_of_finite (wordW w)).orderOf_pos,
        pow_orderOf_eq_one]
  refine ⟨?_, hcover⟩
  have hex : ∀ i : Fin N, ∃ x ∈ pSub gw,
      e6Certificate.Represents (Q[i]'(by rw [hlen]; exact i.2)) x :=
    fun i => exists_mem_of_mem_pcTups hl (List.getElem_mem _)
  choose y hyS hyR using hex
  have e : Fin N ≃ pSub gw := Equiv.ofBijective (fun i => ⟨y i, hyS i⟩)
    ⟨fun i j hij => by
      have h1 : y i = y j := congrArg Subtype.val hij
      have h2 := tuple_unique (hyR i) (h1 ▸ hyR j)
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnodup).1 h2),
    fun g => by
      obtain ⟨t, ht, hrep⟩ := hcover g g.2
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
      exact ⟨⟨i, hlen ▸ hi⟩, Subtype.ext (RootCertificate.represents_unique (hyR _) hrep)⟩⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

@[expose] def InS (y : WeylGroup Tag.E6) (c : ZMod 3) (b : Fin Tag.E6.rank → ZMod 3) : Prop :=
  y ∈ charStabilizer (triChar b) ∧ triPairing b (e6Shift y) = c * triPairing b e6Omega3

@[expose] def O2At (y : WeylGroup Tag.E6) (c : ZMod 3) : Prop :=
  ∀ V : Finset (Fin Tag.E6.rank → ZMod 3), 27 ≤ V.card → (∀ b ∈ V, InS y c b) →
    ∃ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α ∧ ∀ b ∈ V, triPairing b α = 0

@[expose] def tpHom (b : Fin Tag.E6.rank → ZMod 3) : (Fin Tag.E6.rank → ℤ) →+ ZMod 3 where
  toFun v := triPairing b v
  map_zero' := triPairing_zero b
  map_add' u v := triPairing_add b u v

@[expose] def tpL (b : Fin Tag.E6.rank → ZMod 3) (u : List ℤ) : ZMod 3 :=
  triPairing b fun i => u.getD i 0

theorem tpL_ofFn (b : Fin Tag.E6.rank → ZMod 3) (v : Fin Tag.E6.rank → ℤ) :
    tpL b (List.ofFn v) = triPairing b v :=
  congrArg (triPairing b) (funext fun i => getD_ofFn6 v i)

theorem tpL_of_cong3 (b : Fin Tag.E6.rank → ZMod 3) {u v : List ℤ} (h : cong3 u v = true) :
    tpL b u = tpL b v := by
  simp only [cong3, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  unfold tpL triPairing
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := h i i.2
  have e : (((u.getD i 0 - v.getD i 0 : ℤ)) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (by exact_mod_cast Int.dvd_of_emod_eq_zero hi)
  rw [Int.cast_sub, sub_eq_zero] at e
  rw [e]

theorem om3L_eq : om3L = List.ofFn e6Omega3 := by
  rw [ofFn6]
  rfl

theorem shL_eq {t : List ℕ} {y : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t y) :
    shL t = List.ofFn (e6Shift y) := by
  rw [shL, om3L_eq, actV_ofFn hrep, negV_eq, addV_eq, List.map_ofFn]
  congr 1

theorem tp_smul_single (b : Fin Tag.E6.rank → ZMod 3) (j : Fin Tag.E6.rank) :
    triPairing b (Pi.single j 1) = b j := by
  have h := triPairing_zsmul_single b 1 j
  rwa [one_smul, Int.cast_one, mul_one] at h

theorem col_spec {t : List ℕ} {y : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t y)
    {c : ℕ} {b : Fin Tag.E6.rank → ZMod 3} (hb : InS y (c : ZMod 3) b) {j : ℕ} (hj : j < 7) :
    ∃ v, colL t c j = List.ofFn v ∧ triPairing b v = 0 := by
  have hfix := triPairing_smul_of_mem hb.1
  by_cases h6 : j < 6
  · have h6' : j < Tag.E6.rank := h6
    refine ⟨y • (Pi.single (⟨j, h6'⟩ : Fin Tag.E6.rank) 1 : Fin Tag.E6.rank → ℤ) +
      -(Pi.single (⟨j, h6'⟩ : Fin Tag.E6.rank) 1 : Fin Tag.E6.rank → ℤ), ?_, ?_⟩
    · rw [colL, if_pos h6, rvL_eq, (eV_eq ⟨j, h6'⟩ : eV j = _), negV_eq, (hrep.2 ⟨j, h6'⟩).2,
        addV_eq]
    · rw [← sub_eq_add_neg]
      change tpHom b (_ - _) = 0
      rw [map_sub]
      exact sub_eq_zero.2 (hfix _)
  · refine ⟨e6Shift y + (-(c : ℤ)) • e6Omega3, ?_, ?_⟩
    · rw [colL, if_neg h6, shL_eq hrep, om3L_eq, smulV_eq, addV_eq]
    · change tpHom b _ = 0
      rw [map_add, map_zsmul]
      change triPairing b _ + (-(c : ℤ)) • triPairing b _ = 0
      rw [hb.2, zsmul_eq_mul, Int.cast_neg, Int.cast_natCast]
      ring

theorem foldr_spec {t : List ℕ} {y : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t y)
    {c : ℕ} {b : Fin Tag.E6.rank → ZMod 3} (hb : InS y (c : ZMod 3) b) (x : List ℕ) :
    ∀ J : List ℕ, (∀ j ∈ J, j < 7) → ∃ v,
      J.foldr (fun j acc => addV (smulV (x.getD j 0 : ℤ) (colL t c j)) acc) zeroV =
        List.ofFn v ∧ triPairing b v = 0
  | [], _ => ⟨0, zeroV_eq, triPairing_zero b⟩
  | j :: J, hJ => by
    obtain ⟨u, hu, hu0⟩ := col_spec hrep hb (hJ j List.mem_cons_self)
    obtain ⟨v, hv, hv0⟩ := foldr_spec hrep hb x J fun k hk => hJ k (List.mem_cons_of_mem _ hk)
    refine ⟨(x.getD j 0 : ℤ) • u + v, ?_, ?_⟩
    · rw [List.foldr_cons, hu, hv, smulV_eq, addV_eq]
    · change tpHom b _ = 0
      rw [map_add, map_zsmul]
      change (x.getD j 0 : ℤ) • triPairing b u + triPairing b v = 0
      rw [hu0, hv0, smul_zero, add_zero]

theorem combL_spec {t : List ℕ} {y : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t y)
    {c : ℕ} {b : Fin Tag.E6.rank → ZMod 3} (hb : InS y (c : ZMod 3) b) (x : List ℕ) :
    tpL b (combL t c x) = 0 := by
  obtain ⟨v, hv, hv0⟩ := foldr_spec hrep hb x (List.range 7) fun j hj => List.mem_range.1 hj
  rw [combL, hv, tpL_ofFn, hv0]

theorem killW_sound {t : List ℕ} {y : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t y)
    {c : ℕ} {w : List ℕ} (h : killW t c w = true) : O2At y (c : ZMod 3) := by
  simp only [killW, Bool.and_eq_true, decide_eq_true_eq] at h
  refine fun V _ hV => ⟨_, isRoot_root72 h.1, fun b hb => ?_⟩
  rw [← tpL_ofFn, ← rvL_eq, tpL_of_cong3 b h.2, combL_spec hrep (hV b hb)]

theorem tpL_uV (b : Fin Tag.E6.rank → ZMod 3) {i f₀ f₁ : ℕ} (hi : i < 6) (h₀ : f₀ < 6)
    (h₁ : f₁ < 6) (a a' : ℕ) :
    tpL b (uV i f₀ f₁ a a') = b ⟨i, hi⟩ - (a : ZMod 3) * b ⟨f₀, h₀⟩ - (a' : ZMod 3) * b ⟨f₁, h₁⟩ := by
  rw [uV, (eV_eq ⟨i, hi⟩ : eV i = _), (eV_eq ⟨f₀, h₀⟩ : eV f₀ = _), (eV_eq ⟨f₁, h₁⟩ : eV f₁ = _),
    smulV_eq, smulV_eq, addV_eq, addV_eq, tpL_ofFn]
  change tpHom b _ = _
  rw [map_add, map_add]
  change triPairing b _ + (triPairing b _ + triPairing b _) = _
  rw [tp_smul_single, triPairing_zsmul_single, triPairing_zsmul_single, Int.cast_neg,
    Int.cast_neg, Int.cast_natCast, Int.cast_natCast]
  ring

theorem smallW_sound {t : List ℕ} {y : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t y)
    {c : ℕ} {w : List ℕ} (h : smallW t c w = true) : O2At y (c : ZMod 3) := by
  classical
  simp only [smallW, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h₀, h₁⟩, hb⟩ := h
  intro V hV hVS
  exfalso
  have hdet : ∀ b ∈ V, ∀ i : Fin Tag.E6.rank, b i =
      (((blkW w i).getD 0 0 : ℕ) : ZMod 3) * b ⟨_, h₀⟩ +
        (((blkW w i).getD 1 0 : ℕ) : ZMod 3) * b ⟨_, h₁⟩ := by
    intro b hbV i
    have e := tpL_of_cong3 b (hb i i.2)
    rw [combL_spec hrep (hVS b hbV), tpL_uV b i.2 h₀ h₁] at e
    rw [← sub_eq_zero, ← e]
    ring
  have hinj : Set.InjOn (fun b : Fin Tag.E6.rank → ZMod 3 => (b ⟨_, h₀⟩, b ⟨_, h₁⟩)) V := by
    intro b hbV b' hb'V e
    simp only [Prod.mk.injEq] at e
    funext i
    rw [hdet b hbV i, hdet b' hb'V i, e.1, e.2]
  have hle := Finset.card_le_card_of_injOn _ (fun b _ => Finset.mem_univ _) hinj
  rw [Finset.card_univ, Fintype.card_prod, ZMod.card] at hle
  omega

theorem witOK_sound {t : List ℕ} {y : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t y)
    {c : ℕ} {w : List ℕ} (h : witOK t c w = true) : O2At y (c : ZMod 3) := by
  simp only [witOK, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · exact killW_sound hrep h
  · exact smallW_sound hrep h

theorem o2Check_sound {Q : List (List ℕ)} {W : List (List (List ℕ))} (h : o2Check Q W = true)
    {t : List ℕ} (ht : t ∈ Q) {y : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t y)
    (hy : y ≠ 1) (c : ZMod 3) : O2At y c := by
  simp only [o2Check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  have hiW : i < W.length := h.1 ▸ hi
  have ha := h.2 (Q[i], W[i]) (by
    rw [List.mem_iff_getElem]
    exact ⟨i, by rw [List.length_zip, ← h.1, Nat.min_self]; exact hi, by rw [List.getElem_zip]⟩)
  simp only [o2At, Bool.or_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at ha
  rcases ha with hid | hall
  · exact absurd (RootCertificate.represents_unique hrep
      (hid ▸ RootCertificate.represents_one e6Certificate_check)) hy
  · have e := witOK_sound hrep (hall c.val (ZMod.val_lt c))
    rwa [ZMod.natCast_zmod_val] at e

end CFSG.KC.E6O2
