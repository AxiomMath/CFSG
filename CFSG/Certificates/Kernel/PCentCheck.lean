module

public import Certificates.Data.Kernel.PCent
public import CFSG.Certificates.Kernel.PCentSound
public import CFSG.Certificates.Kernel.Spor.PK.PermOf
public import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.PCent

open CFSG.KC.Enum (pg pcomp pidn allN)
open CFSG.KS (mask pinvS)
open CFSG.KC.BfsPin (PP)
open CFSG.KC.Misc.ArrEnum (conjAct)

theorem getD_evensL {α : Type} (d : α) : ∀ (l : List α) (k : Nat),
    (evensL l).getD k d = l.getD (2 * k) d
  | [], k => by simp [evensL]
  | [x], 0 => by simp [evensL]
  | [x], k + 1 => by simp [evensL, Nat.mul_succ]
  | x :: y :: l, 0 => by simp [evensL]
  | x :: y :: l, k + 1 => by
    rw [evensL, Nat.mul_succ, List.getD_cons_succ, getD_evensL d l k]
    simp

theorem getD_oddsL {α : Type} (d : α) : ∀ (l : List α) (k : Nat),
    (oddsL l).getD k d = l.getD (2 * k + 1) d
  | [], k => by simp [oddsL]
  | [x], k => by simp [oddsL]
  | x :: y :: l, 0 => by simp [oddsL]
  | x :: y :: l, k + 1 => by
    rw [oddsL, List.getD_cons_succ, getD_oddsL d l k, Nat.mul_succ]
    simp

theorem length_evensL {α : Type} : ∀ l : List α, (evensL l).length ≤ (l.length + 1) / 2
  | [] => by simp [evensL]
  | [x] => by simp [evensL]
  | x :: y :: l => by
    have := length_evensL l
    simp only [evensL, List.length_cons]
    omega

theorem length_oddsL {α : Type} : ∀ l : List α, (oddsL l).length ≤ l.length / 2
  | [] => by simp [oddsL]
  | [x] => by simp [oddsL]
  | x :: y :: l => by
    have := length_oddsL l
    simp only [oddsL, List.length_cons]
    omega

theorem getT_ofListT {α : Type} [Inhabited α] : ∀ (n : Nat) (L : List α), L.length ≤ n →
    ∀ i, getT (ofListT n L) i = L.getD i default
  | 0, L, h, i => by
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 h)]
    simp [ofListT, getT]
  | n + 1, [], _, i => by simp [ofListT, getT]
  | n + 1, x :: l, h, 0 => by simp [ofListT, getT]
  | n + 1, x :: l, h, i + 1 => by
    simp only [List.length_cons] at h
    have he := length_evensL l
    have ho := length_oddsL l
    simp only [ofListT, getT, List.getD_cons_succ]
    split
    · rw [getT_ofListT n _ (by omega), getD_evensL]
      congr 1
      omega
    · rw [getT_ofListT n _ (by omega), getD_oddsL]
      congr 1
      omega

theorem getT_treeOf {α : Type} [Inhabited α] (L : List α) (i : Nat) :
    getT (treeOf L) i = L.getD i default :=
  getT_ofListT L.length L (Nat.le_refl _) i

inductive Reach (ACT : Nat → Nat → Nat) (ngen root : Nat) : Nat → Prop
  | root : Reach ACT ngen root root
  | step {y : Nat} (k : Nat) (hk : k < ngen) : Reach ACT ngen root y →
      Reach ACT ngen root (ACT k y)

theorem walkK_cons (ACT : Nat → Nat → Nat) (ngen N root : Nat) (T : PTree Rec) (r : Rec)
    (l : List Rec) (lo : Nat) : walkK ACT ngen N root T (r :: l) lo =
      (Nat.ble lo r.1 && recK ACT ngen N root r (getT T r.2.2.2) &&
        walkK ACT ngen N root T l (Nat.add r.1 1)) := rfl

theorem walkK_spec {ACT : Nat → Nat → Nat} {ngen N root : Nat} {T : PTree Rec} :
    ∀ (R : List Rec) (lo : Nat), walkK ACT ngen N root T R lo = true →
      (R.map Prod.fst).Pairwise (· < ·) ∧ (∀ r ∈ R, lo ≤ r.1) ∧
        ∀ r ∈ R, recK ACT ngen N root r (getT T r.2.2.2) = true
  | [], _, _ => by simp
  | r :: l, lo, h => by
    rw [walkK_cons] at h
    simp only [Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨ih1, ih2, ih3⟩ := walkK_spec l _ h3
    refine ⟨?_, ?_, ?_⟩
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨fun b hb => ?_, ih1⟩
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hb
      have := ih2 r' hr'
      change r.1 + 1 ≤ r'.1 at this
      omega
    · intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact h1
      · have := ih2 r' hr'
        change r.1 + 1 ≤ r'.1 at this
        omega
    · intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact h2
      · exact ih3 r' hr'

theorem orbRecK_sound {ACT : Nat → Nat → Nat} {ngen root : Nat} {R : List Rec}
    (h : orbRecK ACT ngen root R = true) :
    (R.map Prod.fst).Pairwise (· < ·) ∧ ∀ r ∈ R, Reach ACT ngen root r.1 := by
  obtain ⟨h1, -, h3⟩ := walkK_spec R 0 h
  refine ⟨h1, ?_⟩
  suffices H : ∀ d, ∀ r ∈ R, r.2.1 = d → Reach ACT ngen root r.1 from
    fun r hr => H _ r hr rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro r hr hd
    have hc := h3 r hr
    rw [getT_treeOf] at hc
    unfold recK at hc
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hc
    rcases hc with ⟨-, he⟩ | ⟨⟨⟨hp, hk⟩, hq⟩, he⟩
    · rw [he]
      exact Reach.root
    · have hmem : R.getD r.2.2.2 default ∈ R := by
        rw [List.getD_eq_getElem _ _ hp]
        exact List.getElem_mem hp
      rw [he]
      exact Reach.step _ hk (ih _ (by omega) _ hmem rfl)

@[expose] noncomputable def toPerm (n w p : Nat) : Equiv.Perm (Fin n) :=
  CFSG.KS.PK.permOf n fun i => pg w (mask w) p i

variable {n w : Nat}

theorem isPermN_of_PP {p : Nat} (hp : PP n w p) : CFSG.KS.PK.IsPermN n fun i => pg w (mask w) p i :=
  ⟨hp.2.1, hp.2.2⟩

theorem toPerm_apply {p : Nat} (hp : PP n w p) (i : Fin n) :
    (toPerm n w p i : Nat) = pg w (mask w) p i :=
  CFSG.KS.PK.permOf_apply (isPermN_of_PP hp) i

theorem toPerm_mul {p q : Nat} (hp : PP n w p) (hq : PP n w q) :
    toPerm n w (pcomp n w (mask w) p q) = toPerm n w p * toPerm n w q := by
  unfold toPerm
  rw [CFSG.KS.PK.permOf_mul (isPermN_of_PP hp) (isPermN_of_PP hq)]
  exact CFSG.KS.PK.permOf_congr fun x hx => CFSG.KS.PF.pg_pcomp hp.lt32 hx

theorem toPerm_inv {p : Nat} (hp : PP n w p) :
    toPerm n w (pinvS n w (mask w) p) = (toPerm n w p)⁻¹ := by
  obtain ⟨-, hw, -, -⟩ := CFSG.KS.PF.canon_facts hp.1
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← toPerm_mul hp.inv hp]
  unfold toPerm
  rw [CFSG.KS.PK.permOf_eq_one_iff (isPermN_of_PP (hp.inv.mul hp))]
  intro x hx
  rw [CFSG.KS.PF.pg_pcomp hp.lt32 hx]
  exact CFSG.KS.PinvS.pg_pinvS (by omega) hp.2 hx

theorem toPerm_pidn (hsz : CFSG.KS.Raw.szOK n w = true) : toPerm n w (pidn n w) = 1 := by
  obtain ⟨hn, hw⟩ := CFSG.KC.BfsPin.szOK_facts' hsz
  unfold toPerm
  rw [CFSG.KS.PK.permOf_eq_one_iff (isPermN_of_PP (PP.id hsz))]
  intro x hx
  exact CFSG.KS.PF.pg_pidn hn hw hx

theorem toPerm_injective {p q : Nat} (hp : PP n w p) (hq : PP n w q)
    (h : toPerm n w p = toPerm n w q) : p = q := by
  obtain ⟨-, hw, hp0, -⟩ := CFSG.KS.PF.canon_facts hp.1
  obtain ⟨-, -, hq0, -⟩ := CFSG.KS.PF.canon_facts hq.1
  exact CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hp0 hq0
    ((CFSG.KS.PK.permOf_eq_iff (isPermN_of_PP hp) (isPermN_of_PP hq)).1 h)

theorem PP_conjAct {G : Nat → Nat} {k x : Nat} (hg : PP n w (G k)) (hx : PP n w x) :
    PP n w (conjAct n w G k x) :=
  hg.mul (hx.mul hg.inv)

theorem toPerm_conjAct {G : Nat → Nat} {k x : Nat} (hg : PP n w (G k)) (hx : PP n w x) :
    toPerm n w (conjAct n w G k x) = toPerm n w (G k) * toPerm n w x * (toPerm n w (G k))⁻¹ := by
  unfold conjAct
  rw [toPerm_mul hg (hx.mul hg.inv), toPerm_mul hx hg.inv, toPerm_inv hg, mul_assoc]

@[expose] def gens (n w : Nat) (G : Nat → Nat) (ngen : Nat) : Set (Equiv.Perm (Fin n)) :=
  {g | ∃ k < ngen, toPerm n w (G k) = g}

theorem gen_mem {G : Nat → Nat} {ngen k : Nat} (hk : k < ngen) :
    toPerm n w (G k) ∈ Subgroup.closure (gens n w G ngen) :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem reach_conj {G : Nat → Nat} {ACT : Nat → Nat → Nat} {ngen v : Nat}
    (hG : ∀ k < ngen, PP n w (G k)) (hA : ∀ k < ngen, ∀ y, ACT k y = conjAct n w G k y)
    (hv : PP n w v) {y : Nat} (h : Reach ACT ngen v y) :
    PP n w y ∧ ∃ g ∈ Subgroup.closure (gens n w G ngen),
      g * toPerm n w v * g⁻¹ = toPerm n w y := by
  induction h with
  | root => exact ⟨hv, 1, Subgroup.one_mem _, by group⟩
  | step k hk _ ih =>
    obtain ⟨hy, g, hg, he⟩ := ih
    rw [hA k hk]
    refine ⟨PP_conjAct (hG k hk) hy, toPerm n w (G k) * g, Subgroup.mul_mem _ (gen_mem hk) hg, ?_⟩
    rw [toPerm_conjAct (hG k hk) hy, ← he]
    group

theorem classK_sound {G GI : Nat → Nat} {ngen v : Nat} {R : List Rec}
    (hG : ∀ k < ngen, PP n w (G k)) (hv : PP n w v) (h : classK n w G GI ngen v R = true) :
    ∃ S : Finset (Equiv.Perm (Fin n)), S.card = R.length ∧
      ∀ s ∈ S, ∃ g ∈ Subgroup.closure (gens n w G ngen), g * toPerm n w v * g⁻¹ = s := by
  classical
  unfold classK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hI, h⟩ := h
  have hA : ∀ k < ngen, ∀ y, conjI n w G GI k y = conjAct n w G k y := by
    intro k hk y
    have e := CFSG.KS.Raw.Orb.allN_iff.1 hI k hk
    rw [Nat.beq_eq] at e
    unfold conjI conjAct
    rw [e]
  have hreach := fun {y} => reach_conj (ACT := conjI n w G GI) (y := y) hG hA hv
  obtain ⟨hs, hr⟩ := orbRecK_sound h
  have hR : ∀ x ∈ R.map Prod.fst, Reach (conjI n w G GI) ngen v x := by
    intro x hx
    obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hx
    exact hr r hr'
  refine ⟨((R.map Prod.fst).map (toPerm n w)).toFinset, ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup, List.length_map, List.length_map]
    refine List.Nodup.map_on (fun x hx y hy e => ?_) (hs.imp (fun h => Nat.ne_of_lt h))
    exact toPerm_injective (hreach (hR x hx)).1 (hreach (hR y hy)).1 e
  · intro s hs'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hs')
    exact (hreach (hR x hx)).2

theorem card_centralizer_le_of_classK {G GI : Nat → Nat} {ngen v : Nat} {R : List Rec}
    (hG : ∀ k < ngen, PP n w (G k)) (hv : PP n w v) (h : classK n w G GI ngen v R = true) :
    R.length * Nat.card (Subgroup.closure (gens n w G ngen) ⊓
        Subgroup.centralizer {toPerm n w v} : Subgroup (Equiv.Perm (Fin n))) ≤
      Nat.card (Subgroup.closure (gens n w G ngen)) := by
  obtain ⟨S, hS, hS'⟩ := classK_sound hG hv h
  rw [← hS]
  exact card_mul_card_centralizer_le S hS'

theorem reach_point {H : Nat → Nat} {ngen x : Nat} (hH : ∀ k < ngen, PP n w (H k)) (hx : x < n)
    {y : Nat} (h : Reach (fun k y => pg w (mask w) (H k) y) ngen x y) :
    ∃ hy : y < n, ∃ g ∈ Subgroup.closure (gens n w H ngen), g • (⟨x, hx⟩ : Fin n) = ⟨y, hy⟩ := by
  induction h with
  | root => exact ⟨hx, 1, Subgroup.one_mem _, one_smul _ _⟩
  | step k hk _ ih =>
    obtain ⟨hy, g, hg, he⟩ := ih
    refine ⟨(hH k hk).2.1 _ hy, toPerm n w (H k) * g, Subgroup.mul_mem _ (gen_mem hk) hg, ?_⟩
    rw [mul_smul, he]
    exact Fin.ext (toPerm_apply (hH k hk) _)

@[expose] noncomputable def ptsOf (n : Nat) (R : List Rec) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i : Fin n => (i : Nat) ∈ R.map Prod.fst

theorem mem_ptsOf {R : List Rec} {i : Fin n} : i ∈ ptsOf n R ↔ (i : Nat) ∈ R.map Prod.fst := by
  classical
  unfold ptsOf
  rw [Finset.mem_filter]
  simp

theorem card_ptsOf {R : List Rec} (hnd : (R.map Prod.fst).Nodup)
    (hlt : ∀ x ∈ R.map Prod.fst, x < n) : (ptsOf n R).card = R.length := by
  classical
  have e : (ptsOf n R).map Fin.valEmbedding = (R.map Prod.fst).toFinset := by
    ext z
    simp only [Finset.mem_map, Fin.valEmbedding_apply, List.mem_toFinset]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact mem_ptsOf.1 hi
    · intro hz
      exact ⟨⟨z, hlt z hz⟩, mem_ptsOf.2 hz, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, e, List.toFinset_card_of_nodup hnd, List.length_map]

theorem pointOrbK_sound {H : Nat → Nat} {ngen x : Nat} {R : List Rec}
    (hH : ∀ k < ngen, PP n w (H k)) (h : pointOrbK n w H ngen x R = true) :
    ∃ hx : x < n, (ptsOf n R).card = R.length ∧
      (∀ s ∈ ptsOf n R, ∃ g ∈ Subgroup.closure (gens n w H ngen), g • (⟨x, hx⟩ : Fin n) = s) ∧
      ∀ y ∈ R.map Prod.fst, y < n := by
  unfold pointOrbK at h
  rw [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hx, h⟩ := h
  obtain ⟨hs, hr⟩ := orbRecK_sound h
  have hR : ∀ y ∈ R.map Prod.fst, Reach (fun k y => pg w (mask w) (H k) y) ngen x y := by
    intro y hy
    obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hy
    exact hr r hr'
  have hlt : ∀ y ∈ R.map Prod.fst, y < n := fun y hy => (reach_point hH hx (hR y hy)).1
  refine ⟨hx, card_ptsOf (hs.imp (fun h => Nat.ne_of_lt h)) hlt, fun s hs' => ?_, hlt⟩
  obtain ⟨_, g, hg, he⟩ := reach_point hH hx (hR _ (mem_ptsOf.1 hs'))
  exact ⟨g, hg, he⟩

theorem wordK_sound {G : Nat → Nat} {ngen : Nat} (hsz : CFSG.KS.Raw.szOK n w = true)
    (hG : ∀ k < ngen, PP n w (G k)) : ∀ ws : List Nat, (∀ c ∈ ws, c < ngen) →
      PP n w (wordK n w G ws) ∧ toPerm n w (wordK n w G ws) ∈ Subgroup.closure (gens n w G ngen)
  | [], _ => by
    refine ⟨PP.id hsz, ?_⟩
    change toPerm n w (pidn n w) ∈ _
    rw [toPerm_pidn hsz]
    exact Subgroup.one_mem _
  | c :: ws, hc => by
    have hc0 : c < ngen := hc c List.mem_cons_self
    obtain ⟨h1, h2⟩ := wordK_sound hsz hG ws fun c' h' => hc c' (List.mem_cons_of_mem _ h')
    change PP n w (pcomp n w (mask w) (G c) (wordK n w G ws)) ∧
      toPerm n w (pcomp n w (mask w) (G c) (wordK n w G ws)) ∈ _
    refine ⟨(hG c hc0).mul h1, ?_⟩
    rw [toPerm_mul (hG c hc0) h1]
    exact Subgroup.mul_mem _ (gen_mem hc0) h2

theorem allL_iff {f : Nat → Bool} : ∀ {l : List Nat}, allL f l = true ↔ ∀ x ∈ l, f x = true
  | [] => by simp [allL]
  | x :: l => by
    change (f x && allL f l) = true ↔ _
    rw [Bool.and_eq_true, allL_iff]
    simp

theorem levelK_spec {G : Nat → Nat} {ngen : Nat} {pre : List Nat}
    {lv : Nat × List Nat × List (List Nat) × List Rec} (h : levelK n w G ngen pre lv = true) :
    (∀ k < lv.2.1.length, lv.2.1.getD k 0 = wordK n w G (lv.2.2.1.getD k []) ∧
      (∀ c ∈ lv.2.2.1.getD k [], c < ngen) ∧
      ∀ b ∈ pre, pg w (mask w) (lv.2.1.getD k 0) b = b) ∧
    pointOrbK n w (fun k => lv.2.1.getD k 0) lv.2.1.length lv.1 lv.2.2.2 = true := by
  unfold levelK at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨-, h2⟩, h3⟩ := h
  refine ⟨fun k hk => ?_, h3⟩
  have e := CFSG.KS.Raw.Orb.allN_iff.1 h2 k hk
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, allL_iff, allL_iff] at e
  obtain ⟨⟨e1, e2⟩, e3⟩ := e
  refine ⟨e1, fun c hc => ?_, fun b hb => ?_⟩
  · have e := e2 c hc
    rwa [Nat.blt_eq] at e
  · have e := e3 b hb
    rwa [Nat.beq_eq] at e

theorem levelsK_bound {G : Nat → Nat} {ngen : Nat} (hsz : CFSG.KS.Raw.szOK n w = true)
    (hG : ∀ k < ngen, PP n w (G k)) :
    ∀ (L : List (Nat × List Nat × List (List Nat) × List Rec)) (pre : List Nat)
      (K F : Subgroup (Equiv.Perm (Fin n))),
      (∀ g ∈ Subgroup.closure (gens n w G ngen),
        (∀ b ∈ pre, ∀ hb : b < n, g ⟨b, hb⟩ = ⟨b, hb⟩) → g ∈ K) → F ≤ K →
      (∀ g ∈ F, ∀ lv ∈ L, ∀ hb : lv.1 < n, g ⟨lv.1, hb⟩ = ⟨lv.1, hb⟩) →
      levelsK n w G ngen L pre = true →
      (L.map fun lv => lv.2.2.2.length).prod * Nat.card F ≤ Nat.card K
  | [], _, K, F, _, hFK, _, _ => by
    rw [List.map_nil, List.prod_nil, Nat.one_mul]
    exact Subgroup.card_le_of_le hFK
  | lv :: L, pre, K, F, hK, hFK, hF, h => by
    change (levelK n w G ngen pre lv && levelsK n w G ngen L (lv.1 :: pre)) = true at h
    rw [Bool.and_eq_true] at h
    obtain ⟨hl, ht⟩ := h
    obtain ⟨hw, hp⟩ := levelK_spec hl
    have hH : ∀ k < lv.2.1.length, PP n w (lv.2.1.getD k 0) := fun k hk => by
      rw [(hw k hk).1]
      exact (wordK_sound hsz hG _ (hw k hk).2.1).1
    obtain ⟨hx, hcard, hs, -⟩ := pointOrbK_sound hH hp
    have hgK : Subgroup.closure (gens n w (fun k => lv.2.1.getD k 0) lv.2.1.length) ≤ K := by
      rw [Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      refine hK _ ?_ fun b hb hbn => Fin.ext ?_
      · beta_reduce
        rw [(hw k hk).1]
        exact (wordK_sound hsz hG _ (hw k hk).2.1).2
      · beta_reduce
        rw [toPerm_apply (hH k hk)]
        exact (hw k hk).2.2 b hb
    have h1 := card_mul_card_stab_le (H := K) (x := (⟨lv.1, hx⟩ : Fin n)) (ptsOf n lv.2.2.2)
      fun s hs' => by
        obtain ⟨g, hg, he⟩ := hs s hs'
        exact ⟨g, hgK hg, he⟩
    have h2 := levelsK_bound hsz hG L (lv.1 :: pre)
      (K ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) (⟨lv.1, hx⟩ : Fin n)) F
      (fun g hg hfix => Subgroup.mem_inf.2 ⟨hK g hg fun b hb => hfix b (List.mem_cons_of_mem _ hb),
        MulAction.mem_stabilizer_iff.2 (by
          rw [Equiv.Perm.smul_def]
          exact hfix _ List.mem_cons_self hx)⟩)
      (fun g hg => Subgroup.mem_inf.2 ⟨hFK hg, MulAction.mem_stabilizer_iff.2 (by
          rw [Equiv.Perm.smul_def]
          exact hF g hg lv List.mem_cons_self hx)⟩)
      (fun g hg lv' hlv' => hF g hg lv' (List.mem_cons_of_mem _ hlv')) ht
    rw [hcard] at h1
    rw [List.map_cons, List.prod_cons, Nat.mul_assoc]
    exact (Nat.mul_le_mul_left _ h2).trans h1

theorem stabLowK_bound {G : Nat → Nat} {ngen : Nat} {L : List (Nat × List Nat × List (List Nat) × List Rec)}
    (hsz : CFSG.KS.Raw.szOK n w = true) (hG : ∀ k < ngen, PP n w (G k))
    (h : stabLowK n w G ngen L = true) (F : Subgroup (Equiv.Perm (Fin n)))
    (hFG : F ≤ Subgroup.closure (gens n w G ngen))
    (hF : ∀ g ∈ F, ∀ lv ∈ L, ∀ hb : lv.1 < n, g ⟨lv.1, hb⟩ = ⟨lv.1, hb⟩) :
    (L.map fun lv => lv.2.2.2.length).prod * Nat.card F ≤
      Nat.card (Subgroup.closure (gens n w G ngen)) :=
  levelsK_bound hsz hG L [] _ F (fun g hg _ => hg) hFG hF h

theorem prod_le_card_of_stabLowK {G : Nat → Nat} {ngen : Nat}
    {L : List (Nat × List Nat × List (List Nat) × List Rec)}
    (hsz : CFSG.KS.Raw.szOK n w = true) (hG : ∀ k < ngen, PP n w (G k))
    (h : stabLowK n w G ngen L = true) :
    (L.map fun lv => lv.2.2.2.length).prod ≤ Nat.card (Subgroup.closure (gens n w G ngen)) := by
  have := stabLowK_bound hsz hG h ⊥ bot_le fun g hg lv _ hb => by
    rw [Subgroup.mem_bot.1 hg]
    rfl
  rwa [Subgroup.card_bot, Nat.mul_one] at this

theorem testBit_maskK (y : Nat) : ∀ R : List Rec,
    Nat.testBit (maskK R) y = true ↔ y ∈ R.map Prod.fst
  | [] => by simp [maskK]
  | r :: R => by
    change Nat.testBit ((1 <<< r.1) ||| maskK R) y = true ↔ _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq, testBit_maskK y R, List.map_cons, List.mem_cons, eq_comm]

theorem inv_smul_mem {Ω : Finset (Fin n)} {a : Equiv.Perm (Fin n)} (ha : ∀ y ∈ Ω, a • y ∈ Ω)
    {y : Fin n} (hy : y ∈ Ω) : a⁻¹ • y ∈ Ω := by
  classical
  have hsub : Ω.map a.toEmbedding ⊆ Ω := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.1 hz
    exact ha t ht
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_map])
  rw [← heq] at hy
  obtain ⟨t, ht, rfl⟩ := Finset.mem_map.1 hy
  have e : a⁻¹ • a.toEmbedding t = t := by
    rw [Equiv.Perm.smul_def, Equiv.toEmbedding_apply]
    exact a.symm_apply_apply t
  rw [e]
  exact ht

theorem oddOrbK_sound {D : Nat → Nat} {ngen x OM : Nat} {R : List Rec}
    (hD : ∀ k < ngen, PP n w (D k)) (h : oddOrbK n w D ngen x OM R = true) :
    ∃ hx : x < n, Odd (ptsOf n R).card ∧
      (∀ y ∈ ptsOf n R, ∃ d ∈ Subgroup.closure (gens n w D ngen), d • (⟨x, hx⟩ : Fin n) = y) ∧
      ∀ d ∈ Subgroup.closure (gens n w D ngen), ∀ y ∈ ptsOf n R, d • y ∈ ptsOf n R := by
  unfold oddOrbK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨hx, hcard, htr, -⟩ := pointOrbK_sound hD h1
  have hg : ∀ k < ngen, ∀ y ∈ ptsOf n R, toPerm n w (D k) • y ∈ ptsOf n R := by
    intro k hk y hy
    have e := allL_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h3 k hk) y (mem_ptsOf.1 hy)
    rw [← h2, testBit_maskK] at e
    rw [mem_ptsOf, Equiv.Perm.smul_def, toPerm_apply (hD k hk)]
    exact e
  refine ⟨hx, ?_, htr, fun d hd => ?_⟩
  · rw [hcard]
    change R.length &&& 1 = 1 at h4
    rw [Nat.and_one_is_mod] at h4
    exact Nat.odd_iff.2 h4
  · induction hd using Subgroup.closure_induction with
    | mem g hg' =>
      obtain ⟨k, hk, rfl⟩ := hg'
      exact hg k hk
    | one =>
      intro y hy
      rwa [one_smul]
    | mul a b _ _ ha hb =>
      intro y hy
      rw [mul_smul]
      exact ha _ (hb y hy)
    | inv a _ ha =>
      intro y hy
      exact inv_smul_mem ha hy

theorem eq_bot_of_oddOrbK {D : Nat → Nat} {ngen x OM : Nat} {R : List Rec}
    (hD : ∀ k < ngen, PP n w (D k)) (h : oddOrbK n w D ngen x OM R = true)
    {Q : Subgroup (Equiv.Perm (Fin n))} {k : Nat} (hQD : Q ≤ Subgroup.closure (gens n w D ngen))
    (hQn : ∀ d ∈ Subgroup.closure (gens n w D ngen), ∀ q ∈ Q, d * q * d⁻¹ ∈ Q)
    (hQ : Nat.card Q = 2 ^ k)
    (hfaith : ∀ d ∈ Subgroup.closure (gens n w D ngen), (∀ y ∈ ptsOf n R, d • y = y) → d = 1) :
    Q = ⊥ := by
  obtain ⟨hx, hodd, htr, hinv⟩ := oddOrbK_sound hD h
  exact eq_bot_of_odd_orbit hQD hQn hQ _ ⟨x, hx⟩ htr hinv hodd hfaith

end CFSG.KC.PCent

end
