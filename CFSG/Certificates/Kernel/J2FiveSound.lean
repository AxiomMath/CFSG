module

public import Certificates.Data.Kernel.J2Five
public import CFSG.Certificates.Kernel.YoshQ.TabNSound
public import Mathlib.GroupTheory.Sylow

public section

set_option exponentiation.threshold 3000

namespace CFSG.KD.J2Five

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KS.PF Subgroup

@[expose] def PRep (x : ℕ) (X : Equiv.Perm (Fin 315)) : Prop :=
  ∀ q (hq : q < 315), ap x q = (X ⟨q, hq⟩ : ℕ)

theorem strictB_eq' (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bIf_eq (c : Bool) : Bool.rec (motive := fun _ => Bool) true false c = !c := by
  cases c <;> rfl

theorem bIf_true_eq (c b : Bool) : Bool.rec (motive := fun _ => Bool) b true c = (c || b) := by
  cases c <;> rfl

theorem nIf_eq (c : Bool) (a b : ℕ) :
    Bool.rec (motive := fun _ => ℕ) b a c = if c = true then a else b := by
  cases c <;> rfl

theorem prep_pm {x y : ℕ} {X Y : Equiv.Perm (Fin 315)} (hx : PRep x X) (hy : PRep y Y) :
    PRep (pm x y) (X * Y) := by
  intro q hq
  have hyq := hy q hq
  have hlt : pg 9 (mask 9) y q < 315 := by rw [← ap, hyq]; exact (Y ⟨q, hq⟩).isLt
  unfold pm ap
  rw [pmN, pg_pcomp (by norm_num) hq, pg_mod hlt]
  change ap x _ = _
  rw [hx _ hlt, Equiv.Perm.mul_apply]
  congr 2
  exact Fin.ext hyq

theorem prep_one : PRep one 1 := by
  intro q hq
  unfold ap one
  rw [pg_pidn (by norm_num) (by norm_num) hq]
  rfl

theorem prep_eq {x y : ℕ} {X Y : Equiv.Perm (Fin 315)} (hx : PRep x X) (hy : PRep y Y) :
    eq x y = true ↔ X = Y := by
  unfold eq eqN
  rw [Nat.beq_eq, ← tabN_inj_iff (n := 315) (w := 9) (by decide) (by decide)]
  constructor
  · intro h
    ext ⟨q, hq⟩
    have e := h q hq
    rw [ap_tabN (by decide), ap_tabN (by decide), pg_mod hq, pg_mod hq] at e
    have e1 := hx q hq
    have e2 := hy q hq
    unfold ap at e1 e2
    rw [e1, e2] at e
    exact e
  · rintro rfl q hq
    have e1 := hx q hq
    have e2 := hy q hq
    unfold ap at e1 e2
    rw [ap_tabN (by decide), ap_tabN (by decide), pg_mod hq, pg_mod hq, e1, e2]

theorem prep_of_eq {x y : ℕ} {Y : Equiv.Perm (Fin 315)} (h : eq x y = true) (hy : PRep y Y) :
    PRep x Y := by
  unfold eq eqN at h
  rw [Nat.beq_eq] at h
  intro q hq
  have e1 : pg 9 (mask 9) (x % 2 ^ (315 * 9)) q = pg 9 (mask 9) (y % 2 ^ (315 * 9)) q := by
    rw [h]
  rw [pg_mod hq, pg_mod hq] at e1
  have e2 := hy q hq
  unfold ap at e2 ⊢
  rw [e1, e2]

theorem lenN_eq (L : List ℕ) : lenN L = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [lenN, List.length_cons] at ih ⊢; rw [ih]

theorem lenW_eq (L : List (List ℕ)) : lenW L = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [lenW, List.length_cons] at ih ⊢; rw [ih]

theorem lenR_eq (R : List (ℕ × List ℕ)) : lenR R = R.length := by
  induction R with
  | nil => rfl
  | cons a R ih => simp only [lenR, List.length_cons] at ih ⊢; rw [ih]

theorem letOK_iff (m : ℕ) (w : List ℕ) : letOK m w = true ↔ ∀ a ∈ w, a < m := by
  induction w with
  | nil => simp [letOK]
  | cons a w ih =>
    have e : letOK m (a :: w) = (Nat.blt a m && letOK m w) := bAnd_eq _ _
    rw [e, Bool.and_eq_true, ih, Nat.blt_eq]
    simp

theorem getW_eq : ∀ (L : List (List ℕ)) (i : ℕ), getW L i = L.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => getW_eq L i

theorem getD_lt {α : Type*} (L : List α) (d : α) {i : ℕ} (hi : i < L.length) :
    L.getD i d = L[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

section Words

variable {G Gi : List ℕ} {σ : ℕ → Equiv.Perm (Fin 315)}

noncomputable def wordP (σ : ℕ → Equiv.Perm (Fin 315)) (w : List ℕ) : Equiv.Perm (Fin 315) :=
  (w.map σ).prod

theorem wordP_mem (K : Subgroup (Equiv.Perm (Fin 315))) {m : ℕ} (hK : ∀ i < m, σ i ∈ K)
    {w : List ℕ} (hw : ∀ a ∈ w, a < m) : wordP σ w ∈ K := by
  refine list_prod_mem ?_
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
  exact hK a (hw a ha)

theorem wImg_eq (hG : ∀ i < G.length, PRep (getN G i) (σ i)) {w : List ℕ}
    (hw : ∀ a ∈ w, a < G.length) (q : ℕ) (hq : q < 315) :
    wImg G w q = (wordP σ w ⟨q, hq⟩ : ℕ) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ih' := ih (fun b hb => hw b (List.mem_cons_of_mem a hb))
    have hlt : wImg G w q < 315 := by rw [ih']; exact Fin.isLt _
    change ap (getN G a) (wImg G w q) = _
    rw [hG a (hw a (List.mem_cons_self ..)) _ hlt]
    simp only [wordP, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
    congr 2
    exact Fin.ext ih'

theorem wInv_eq (hGi : ∀ i < Gi.length, PRep (getN Gi i) (σ i)⁻¹) {w : List ℕ}
    (hw : ∀ a ∈ w, a < Gi.length) (q : ℕ) (hq : q < 315) :
    wInv Gi w q = ((wordP σ w)⁻¹ ⟨q, hq⟩ : ℕ) := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
    have ha := hGi a (hw a (List.mem_cons_self ..)) q hq
    have hlt : ap (getN Gi a) q < 315 := by rw [ha]; exact Fin.isLt _
    change wInv Gi w (ap (getN Gi a) q) = _
    rw [ih (fun b hb => hw b (List.mem_cons_of_mem a hb)) _ hlt]
    simp only [wordP, List.map_cons, List.prod_cons, mul_inv_rev, Equiv.Perm.mul_apply]
    congr 2
    exact Fin.ext ha

theorem wordN_rep (hG : ∀ i < G.length, PRep (getN G i) (σ i)) {w : List ℕ}
    (hw : ∀ a ∈ w, a < G.length) : PRep (wordN G w) (wordP σ w) := by
  induction w with
  | nil => exact prep_one
  | cons a w ih =>
    change PRep (pm (getN G a) (wordN G w)) _
    simp only [wordP, List.map_cons, List.prod_cons] at ih ⊢
    exact prep_pm (hG a (hw a (List.mem_cons_self ..)))
      (ih fun b hb => hw b (List.mem_cons_of_mem a hb))

end Words

noncomputable def keyP (Y : Equiv.Perm (Fin 315)) : List ℕ → ℕ
  | [] => 0
  | p :: pts => Nat.lor (if h : p < 315 then (Y ⟨p, h⟩ : ℕ) else 0) (keyP Y pts <<< 9)

theorem keyX_eq {x : ℕ} {X : Equiv.Perm (Fin 315)} (hx : PRep x X) :
    ∀ pts : List ℕ, (∀ p ∈ pts, p < 315) → keyX x pts = keyP X pts
  | [], _ => rfl
  | p :: pts, hpts => by
    have hp := hpts p (List.mem_cons_self ..)
    change Nat.lor (ap x p) (keyX x pts <<< 9) = _
    rw [keyX_eq hx pts fun q hq => hpts q (List.mem_cons_of_mem p hq), keyP, dif_pos hp,
      hx p hp]

theorem keysN_eq {G Gi : List ℕ} {x : ℕ} {w : List ℕ} {σ : ℕ → Equiv.Perm (Fin 315)}
    {X : Equiv.Perm (Fin 315)} (hG : ∀ i < G.length, PRep (getN G i) (σ i))
    (hGi : ∀ i < Gi.length, PRep (getN Gi i) (σ i)⁻¹) (hx : PRep x X)
    (hw : ∀ a ∈ w, a < G.length) (hw' : ∀ a ∈ w, a < Gi.length) :
    ∀ pts : List ℕ, (∀ p ∈ pts, p < 315) →
      keysN G Gi x pts w = keyP ((wordP σ w)⁻¹ * X * wordP σ w) pts
  | [], _ => rfl
  | p :: pts, hpts => by
    have hp := hpts p (List.mem_cons_self ..)
    change Nat.lor (keyN G Gi x p w) (keysN G Gi x pts w <<< 9) = _
    rw [keysN_eq hG hGi hx hw hw' pts fun q hq => hpts q (List.mem_cons_of_mem p hq), keyP,
      dif_pos hp]
    congr 1
    have e1 := wImg_eq hG hw p hp
    have hlt : wImg G w p < 315 := by rw [e1]; exact Fin.isLt _
    have e2 := hx _ hlt
    have hlt2 : ap x (wImg G w p) < 315 := by rw [e2]; exact Fin.isLt _
    unfold keyN
    rw [wInv_eq hGi hw' _ hlt2, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    congr 2
    apply Fin.ext
    change ap x (wImg G w p) = _
    rw [e2]
    congr 2
    exact Fin.ext e1

theorem conjGo_spec {G Gi : List ℕ} {x : ℕ} {pts : List ℕ} {m : ℕ} :
    ∀ (R : List (ℕ × List ℕ)) (lo : ℕ), conjGo G Gi x pts m R lo = true →
      (∀ r ∈ R, lo ≤ r.1 ∧ letOK m r.2 = true ∧ keysN G Gi x pts r.2 = r.1) ∧
        R.Pairwise (fun r s => r.1 < s.1)
  | [], _, _ => ⟨by simp, List.Pairwise.nil⟩
  | (k, w) :: R, lo, h => by
    have e : conjGo G Gi x pts m ((k, w) :: R) lo =
        bAnd(Nat.ble lo k, bAnd(letOK m w, bAnd(Nat.beq (keysN G Gi x pts w) k,
          conjGo G Gi x pts m R (k + 1)))) := rfl
    rw [e, bAnd_eq, bAnd_eq, bAnd_eq] at h
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨ih1, ih2⟩ := conjGo_spec R (k + 1) h4
    refine ⟨?_, List.Pairwise.cons (fun s hs => (ih1 s hs).1) ih2⟩
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨h1, h2, h3⟩
    · have := ih1 r hr
      exact ⟨by omega, this.2⟩

theorem conjOK_sound {G Gi : List ℕ} {x : ℕ} {pts : List ℕ} {R : List (ℕ × List ℕ)}
    (σ : ℕ → Equiv.Perm (Fin 315)) (X : Equiv.Perm (Fin 315)) (hlen : Gi.length = G.length)
    (hG : ∀ i < G.length, PRep (getN G i) (σ i))
    (hGi : ∀ i < G.length, PRep (getN Gi i) (σ i)⁻¹) (hx : PRep x X)
    (hpts : ∀ p ∈ pts, p < 315) (h : conjOK G Gi x pts R = true) :
    R.length ≤ Nat.card {y | ∃ k ∈ closure (σ '' {i | i < G.length}), y = k⁻¹ * X * k} := by
  rw [conjOK, lenN_eq] at h
  obtain ⟨h1, h2⟩ := conjGo_spec R 0 h
  have hGi' : ∀ i < Gi.length, PRep (getN Gi i) (σ i)⁻¹ := by rw [hlen]; exact hGi
  have hkey : ∀ r ∈ R, r.1 = keyP ((wordP σ r.2)⁻¹ * X * wordP σ r.2) pts := by
    intro r hr
    obtain ⟨-, hl, hk⟩ := h1 r hr
    have hw := (letOK_iff _ _).1 hl
    rw [← hk]
    exact keysN_eq hG hGi' hx hw (by rw [hlen]; exact hw) pts hpts
  let f : ℕ × List ℕ → Equiv.Perm (Fin 315) := fun r => (wordP σ r.2)⁻¹ * X * wordP σ r.2
  have hnd : (R.map f).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine h2.imp_of_mem ?_
    intro r s hr hs hrs e
    have := hkey r hr
    rw [hkey s hs] at hrs
    rw [this] at hrs
    change keyP (f r) pts < keyP (f s) pts at hrs
    rw [e] at hrs
    exact lt_irrefl _ hrs
  have hsub : ((R.map f).toFinset : Set (Equiv.Perm (Fin 315))) ⊆
      {y | ∃ k ∈ closure (σ '' {i | i < G.length}), y = k⁻¹ * X * k} := by
    intro y hy
    simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_map] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    refine ⟨wordP σ r.2, list_prod_mem ?_, rfl⟩
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
    exact subset_closure ⟨a, (letOK_iff _ _).1 (h1 r hr).2.1 a ha, rfl⟩
  calc R.length = (R.map f).toFinset.card := by
        rw [List.toFinset_card_of_nodup hnd, List.length_map]
    _ = ((R.map f).toFinset : Set (Equiv.Perm (Fin 315))).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ _ := by
        rw [Nat.card_coe_set_eq]
        exact Set.ncard_le_ncard hsub (Set.toFinite _)

theorem keyGo_spec {S pts : List ℕ} {m : ℕ} :
    ∀ (W : List (List ℕ)) (lo : ℕ), keyGo S pts m W lo = true →
      (∀ w ∈ W, lo ≤ keyX (wordN S w) pts ∧ letOK m w = true) ∧
        W.Pairwise (fun v w => keyX (wordN S v) pts < keyX (wordN S w) pts)
  | [], _, _ => ⟨by simp, List.Pairwise.nil⟩
  | w :: W, lo, h => by
    have e : keyGo S pts m (w :: W) lo = bAnd(letOK m w,
        strictB (keyX (wordN S w) pts) fun k => bAnd(Nat.ble lo k, keyGo S pts m W (k + 1))) :=
      rfl
    rw [e, bAnd_eq, strictB_eq', bAnd_eq] at h
    simp only [Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨ih1, ih2⟩ := keyGo_spec W _ h3
    refine ⟨?_, List.Pairwise.cons (fun v hv => (ih1 v hv).1) ih2⟩
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact ⟨h2, h1⟩
    · have := ih1 v hv
      exact ⟨by omega, this.2⟩

theorem grpOK_sound {S pts : List ℕ} {W C : List (List ℕ)} {i₀ : ℕ}
    (σ : ℕ → Equiv.Perm (Fin 315)) (hS : ∀ j < S.length, PRep (getN S j) (σ j))
    (hpts : ∀ p ∈ pts, p < 315) (h : grpOK S pts W C i₀ = true) :
    (∀ y, y ∈ closure (σ '' {j | j < S.length}) ↔
      ∃ i < W.length, wordP σ (W.getD i []) = y) ∧
      Nat.card (closure (σ '' {j | j < S.length})) = W.length ∧
      (∀ i < W.length, ∀ a ∈ W.getD i [], a < S.length) ∧
      (∀ i < W.length, PRep (elt S W i) (wordP σ (W.getD i []))) ∧ i₀ < W.length ∧
      wordP σ (W.getD i₀ []) = 1 := by
  classical
  unfold grpOK at h
  rw [bAnd_eq, bAnd_eq, bAnd_eq] at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hk, hi0, he, hcl⟩ := h
  rw [lenN_eq] at hk
  rw [lenW_eq] at hi0 hcl
  obtain ⟨hk1, hk2⟩ := keyGo_spec W 0 hk
  replace hcl := CFSG.KS.allN_spec hcl
  set x : ℕ → Equiv.Perm (Fin 315) := fun i => wordP σ (W.getD i []) with hxdef
  have hlet : ∀ i < W.length, ∀ a ∈ W.getD i [], a < S.length := by
    intro i hi
    have hm : W.getD i [] ∈ W := by
      rw [getD_lt _ _ hi]
      exact List.getElem_mem hi
    exact (letOK_iff _ _).1 (hk1 _ hm).2
  have hrep : ∀ i < W.length, PRep (elt S W i) (x i) := by
    intro i hi
    unfold elt
    rw [getW_eq]
    exact wordN_rep hS (hlet i hi)
  have hx0 : x i₀ = 1 := (prep_eq (hrep i₀ hi0) prep_one).1 he
  have hcl' : ∀ i < W.length, ∀ j < S.length, ∃ q < W.length, x q = x i * σ j := by
    intro i hi j hj
    have h1 := hcl i hi
    rw [strictB_eq'] at h1
    have h2 := CFSG.KS.allN_spec h1 j (by rw [lenN_eq]; exact hj)
    rw [strictB_eq', bAnd_eq] at h2
    simp only [Bool.and_eq_true, Nat.blt_eq] at h2
    obtain ⟨hq, he⟩ := h2
    refine ⟨_, hq, ((prep_eq (prep_pm (hrep i hi) (hS j hj)) (hrep _ hq)).1 he).symm⟩
  have hinj : ∀ a < W.length, ∀ b < W.length, x a = x b → a = b := by
    intro a ha b hb e
    have hka : keyX (elt S W a) pts = keyP (x a) pts := keyX_eq (hrep a ha) pts hpts
    have hkb : keyX (elt S W b) pts = keyP (x b) pts := keyX_eq (hrep b hb) pts hpts
    unfold elt at hka hkb
    rw [getW_eq] at hka hkb
    by_contra hab
    rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
    · have := List.pairwise_iff_getElem.1 hk2 a b ha hb hlt
      rw [← getD_lt _ [] ha, ← getD_lt _ [] hb, hka, hkb, e] at this
      exact lt_irrefl _ this
    · have := List.pairwise_iff_getElem.1 hk2 b a hb ha hlt
      rw [← getD_lt _ [] ha, ← getD_lt _ [] hb, hka, hkb, e] at this
      exact lt_irrefl _ this
  let Rf : Finset (Equiv.Perm (Fin 315)) := (Finset.range W.length).image x
  have memR : ∀ y, y ∈ Rf ↔ ∃ i < W.length, x i = y := by
    intro y
    simp [Rf, Finset.mem_image, Finset.mem_range]
  let K : Subgroup (Equiv.Perm (Fin 315)) :=
    { carrier := {h | ∀ y ∈ Rf, y * h ∈ Rf}
      mul_mem' := fun {a b} ha hb y hy => by
        rw [← mul_assoc]
        exact hb _ (ha y hy)
      one_mem' := fun y hy => by rwa [mul_one]
      inv_mem' := fun {a} ha y hy => by
        have hsub : Rf.image (· * a) ⊆ Rf := by
          intro z hz
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hz
          exact ha u hu
        have heq : Rf.image (· * a) = Rf :=
          Finset.eq_of_subset_of_card_le hsub
            (by rw [Finset.card_image_of_injective _ (mul_left_injective a)])
        rw [← heq] at hy
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hy
        simpa using hu }
  have hmem : ∀ y, y ∈ closure (σ '' {j | j < S.length}) ↔ ∃ i < W.length, x i = y := by
    intro y
    constructor
    · intro hy
      have hK : closure (σ '' {j | j < S.length}) ≤ K := by
        rw [closure_le]
        rintro _ ⟨j, hj, rfl⟩ z hz
        obtain ⟨i, hi, rfl⟩ := (memR z).1 hz
        obtain ⟨q, hq, e⟩ := hcl' i hi j hj
        exact (memR _).2 ⟨q, hq, e⟩
      have h1 := hK hy (x i₀) ((memR _).2 ⟨i₀, hi0, rfl⟩)
      rw [hx0, one_mul] at h1
      exact (memR y).1 h1
    · rintro ⟨i, hi, rfl⟩
      exact wordP_mem (closure (σ '' {j | j < S.length})) (m := S.length)
        (fun j hj => subset_closure (Set.mem_image_of_mem σ hj)) (hlet i hi)
  refine ⟨hmem, ?_, hlet, hrep, hi0, hx0⟩
  have e : (closure (σ '' {j | j < S.length}) : Set (Equiv.Perm (Fin 315))) = (Rf : Set _) := by
    ext y
    simp only [SetLike.mem_coe, Finset.mem_coe]
    rw [hmem y, memR y]
  have hc : Nat.card (closure (σ '' {j | j < S.length})) =
      Nat.card ↥(Rf : Set (Equiv.Perm (Fin 315))) := by
    rw [← e]
    rfl
  rw [hc, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn,
    Finset.card_range]
  intro a ha b hb hab
  exact hinj a (by simpa using ha) b (by simpa using hb) hab

theorem kleinOK_sound {x u : ℕ} {X U : Equiv.Perm (Fin 315)} (hx : PRep x X) (hu : PRep u U)
    (h : kleinOK x u = true) :
    X ^ 3 = 1 ∧ U * U = 1 ∧ X * U * X⁻¹ * (X * U * X⁻¹) = 1 ∧
      U * (X * U * X⁻¹) = X * U * X⁻¹ * U ∧ X * (X * U * X⁻¹) * X⁻¹ = U * (X * U * X⁻¹) ∧
      X * U * X⁻¹ ≠ U := by
  unfold kleinOK at h
  rw [strictB_eq', strictB_eq'] at h
  simp only [bAnd_eq, bIf_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, -, h3, h4, h5⟩ := h
  have hX2 := prep_pm hx hx
  have hX3 : X ^ 3 = 1 := by
    have := (prep_eq (prep_pm hx hX2) prep_one).1 h1
    rw [pow_succ, pow_two, ← mul_assoc] at *
    calc X * X * X = X * (X * X) := mul_assoc _ _ _
      _ = 1 := this
  have hinv : X⁻¹ = X * X := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc]
    calc X * X * X = X ^ 3 := by rw [pow_succ, pow_two]
      _ = 1 := hX3
  have hU2 := prep_pm (prep_pm hx hu) hX2
  rw [← hinv] at hU2
  have hUU : U * U = 1 := (prep_eq (prep_pm hu hu) prep_one).1 h2
  refine ⟨hX3, hUU, ?_, (prep_eq (prep_pm hu hU2) (prep_pm hU2 hu)).1 h3, ?_, ?_⟩
  · calc X * U * X⁻¹ * (X * U * X⁻¹) = X * (U * U) * X⁻¹ := by group
      _ = 1 := by rw [hUU]; group
  · have := (prep_eq (prep_pm (prep_pm hx hU2) hX2) (prep_pm hu hU2)).1 h4
    rwa [← hinv] at this
  · intro e
    have := (prep_eq hU2 hu).2 e
    rw [this] at h5
    exact Bool.false_ne_true h5.symm

theorem conjTo_sound {G : List ℕ} {σ : ℕ → Equiv.Perm (Fin 315)}
    (hG : ∀ i < G.length, PRep (getN G i) (σ i)) (hl : G.length = 3) {x a c : ℕ}
    {X A Cc : Equiv.Perm (Fin 315)} (hx : PRep x X) (ha : PRep a A) (hc : PRep c Cc)
    {r : ℕ × List ℕ} (h : conjTo G x a c r = true) :
    (∀ b ∈ r.2, b < 3) ∧
      (wordP σ r.2)⁻¹ * X * wordP σ r.2 = if r.1 = 0 then A else Cc := by
  unfold conjTo at h
  rw [bAnd_eq, strictB_eq', nIf_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hw := (letOK_iff _ _).1 h1
  have hH := wordN_rep hG (by rw [hl]; exact hw)
  refine ⟨hw, ?_⟩
  have hZ : PRep (if Nat.beq r.1 0 = true then a else c) (if r.1 = 0 then A else Cc) := by
    by_cases h0 : r.1 = 0
    · rw [if_pos (by rw [h0]; rfl), if_pos h0]; exact ha
    · rw [if_neg (by rw [Nat.beq_eq]; exact h0), if_neg h0]; exact hc
  have e := (prep_eq (prep_pm hx hH) (prep_pm hH hZ)).1 h2
  rw [mul_assoc, e]
  group

section Groups

variable {Γ : Type*} [Group Γ]

theorem card_cent_le (K : Subgroup Γ) [Finite K] {x : Γ} {m : ℕ}
    (hm : m ≤ Nat.card {y | ∃ k ∈ K, y = k⁻¹ * x * k}) :
    Nat.card ↥(K ⊓ centralizer {x}) * m ≤ Nat.card K := by
  set S := {y | ∃ k ∈ K, y = k⁻¹ * x * k}
  have hS : ∀ y : S, ∃ k : K, (y : Γ) = (k : Γ)⁻¹ * x * k := fun y => by
    obtain ⟨k, hk, e⟩ := y.2
    exact ⟨⟨k, hk⟩, e⟩
  choose kf hkf using hS
  let F : ↥(K ⊓ centralizer {x}) × S → K := fun cy =>
    ⟨cy.1 * kf cy.2, K.mul_mem (mem_inf.1 cy.1.2).1 (kf cy.2).2⟩
  have hF : Function.Injective F := by
    rintro ⟨c, y⟩ ⟨c', y'⟩ e
    have e' : (c : Γ) * kf y = c' * kf y' := congrArg Subtype.val e
    have hc : x * c = c * x := (mem_centralizer_singleton_iff.1 (mem_inf.1 c.2).2).symm
    have hc' : x * c' = c' * x := (mem_centralizer_singleton_iff.1 (mem_inf.1 c'.2).2).symm
    have conj : ∀ (d : Γ) (k : Γ), x * d = d * x → (d * k)⁻¹ * x * (d * k) = k⁻¹ * x * k := by
      intro d k hd
      rw [mul_inv_rev, mul_assoc, mul_assoc, ← mul_assoc x, hd]
      group
    have hy : y = y' := by
      apply Subtype.ext
      calc (y : Γ) = (kf y : Γ)⁻¹ * x * kf y := hkf y
        _ = ((c : Γ) * kf y)⁻¹ * x * ((c : Γ) * kf y) := (conj c _ hc).symm
        _ = ((c' : Γ) * kf y')⁻¹ * x * ((c' : Γ) * kf y') := by rw [e']
        _ = (kf y' : Γ)⁻¹ * x * kf y' := conj c' _ hc'
        _ = y' := (hkf y').symm
    subst hy
    have : (c : Γ) = c' := mul_right_cancel e'
    rw [Subtype.ext this]
  have hfin : Finite (↥(K ⊓ centralizer {x}) × S) := Finite.of_injective F hF
  have := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod] at this
  calc Nat.card ↥(K ⊓ centralizer {x}) * m ≤ Nat.card ↥(K ⊓ centralizer {x}) * Nat.card S :=
        Nat.mul_le_mul_left _ hm
    _ ≤ _ := this

theorem exists_conj_mem [Finite Γ] {p k m : ℕ} (hp : p.Prime) {Q H : Subgroup Γ} (hHQ : H ≤ Q)
    (hH : Nat.card H = p ^ k) (hQ : Nat.card Q = p ^ k * m) (hpm : ¬ p ∣ m) {x : Γ}
    (hx : x ∈ Q) (ho : orderOf x = p) : ∃ g ∈ Q, g⁻¹ * x * g ∈ H := by
  have : Fact p.Prime := ⟨hp⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hpm (dvd_zero p)
  have hcardH : Nat.card (H.subgroupOf Q) = p ^ (Nat.card Q).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hHQ).toEquiv, hH, hQ,
      Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0]
    simp [hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd hpm]
  let P : Sylow p Q := Sylow.ofCard (H.subgroupOf Q) hcardH
  have hX : IsPGroup p (zpowers (⟨x, hx⟩ : Q)) := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers, orderOf_mk, ho, pow_one]
  obtain ⟨T, hT⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q P T
  have hmem : (⟨x, hx⟩ : Q) ∈ ((g • P : Sylow p Q) : Subgroup Q) := by
    rw [hg]
    exact hT (mem_zpowers _)
  rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply, Sylow.coe_ofCard, mem_subgroupOf] at hmem
  refine ⟨g, g.2, ?_⟩
  simpa only [coe_mul, coe_inv] using hmem

end Groups

end CFSG.KD.J2Five

end
