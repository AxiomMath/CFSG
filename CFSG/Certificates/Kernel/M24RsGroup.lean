module

public import CFSG.Certificates.Kernel.M24RsLemmas
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group
public import Certificates.Data.Kernel.M24Rs

public section

namespace CFSG.KM24.RS

open CFSG.KM24

variable {G : Type*} [Group G]

noncomputable def wv (P : ℕ) (gen : ℕ → G) : ℕ → G
  | d => if _h : 0 < d ∧ t8 P (2 * d) < d then wv P gen (t8 P (2 * d)) * ltv gen (t8 P (2 * d + 1)) else 1
termination_by d => d
decreasing_by exact _h.2

theorem wv_zero (P : ℕ) (gen : ℕ → G) : wv P gen 0 = 1 := by
  rw [wv.eq_1]
  simp

theorem wv_pos (P : ℕ) (gen : ℕ → G) {d : ℕ} (hd : 0 < d) (hp : t8 P (2 * d) < d) :
    wv P gen d = wv P gen (t8 P (2 * d)) * ltv gen (t8 P (2 * d + 1)) := by
  rw [wv.eq_1, dite_eq_left ⟨hd, hp⟩]

noncomputable def sch (T P k2 : ℕ) (gen : ℕ → G) (id : ℕ) : G :=
  wv P gen (id / k2) * ltv gen (id % k2) * (wv P gen (t8 T id))⁻¹

theorem id_div {c l k2 : ℕ} (hl : l < k2) : (c * k2 + l) / k2 = c := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hl, Nat.zero_add]

theorem id_mod {c l k2 : ℕ} (hl : l < k2) : (c * k2 + l) % k2 = l := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]

theorem isTree_iff (P c l d : ℕ) : isTree P c l d = true ↔
    (0 < d ∧ t8 P (2 * d) = c ∧ t8 P (2 * d + 1) = l) ∨
      (0 < c ∧ t8 P (2 * c) = d ∧ t8 P (2 * c + 1) = l ^^^ 1) := by
  unfold isTree
  rw [mOr_iff, mAnd_iff, mAnd_iff, mAnd_iff, mAnd_iff, blt_iff, blt_iff, beq_iff, beq_iff, beq_iff,
    beq_iff]
  rfl

theorem sch_tree {T P k2 nc : ℕ} (ht : chkTable T P k2 nc = true) (gen : ℕ → G) {c l : ℕ}
    (hc : c < nc) (hl : l < k2) (htr : isTree P c l (t8 T (c * k2 + l)) = true) :
    sch T P k2 gen (c * k2 + l) = 1 := by
  obtain ⟨hT, hP⟩ := chkTable_spec ht
  have hid : c * k2 + l < nc * k2 := by
    calc c * k2 + l < c * k2 + k2 := by omega
      _ = (c + 1) * k2 := by ring
      _ ≤ nc * k2 := Nat.mul_le_mul_right _ (by omega)
  have hd := hT _ hid
  unfold sch
  rw [id_div hl, id_mod hl]
  rcases (isTree_iff _ _ _ _).1 htr with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · have hpd := (hP _ h0 hd).1
    rw [wv_pos P gen h0 hpd, h1, h2]
    group
  · have hpd := (hP _ h0 hc).1
    rw [wv_pos P gen h0 hpd, h1, h2, ltv_xor]
    group

theorem ltv_mem {H : Subgroup G} {gen : ℕ → G} {k2 : ℕ} (hk : k2 % 2 = 0)
    (hH : ∀ g, 2 * g < k2 → gen g ∈ H) {l : ℕ} (hl : l < k2) : ltv gen l ∈ H := by
  unfold ltv
  have : 2 * (l / 2) < k2 := by omega
  split
  · exact hH _ this
  · exact H.inv_mem (hH _ this)

theorem wv_mem {T P k2 nc : ℕ} (ht : chkTable T P k2 nc = true) {H : Subgroup G} {gen : ℕ → G}
    (hk : k2 % 2 = 0) (hH : ∀ g, 2 * g < k2 → gen g ∈ H) : ∀ d < nc, wv P gen d ∈ H := by
  obtain ⟨-, hP⟩ := chkTable_spec ht
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    rcases Nat.eq_zero_or_pos d with rfl | h0
    · rw [wv_zero]
      exact H.one_mem
    · obtain ⟨h1, h2, -⟩ := hP d h0 hd
      rw [wv_pos P gen h0 h1]
      exact H.mul_mem (ih _ h1 (by omega)) (ltv_mem hk hH h2)

theorem sch_mem {T P k2 nc : ℕ} (ht : chkTable T P k2 nc = true) {H : Subgroup G} {gen : ℕ → G}
    (hk : k2 % 2 = 0) (hH : ∀ g, 2 * g < k2 → gen g ∈ H) {id : ℕ} (hid : id < nc * k2) :
    sch T P k2 gen id ∈ H := by
  obtain ⟨hT, -⟩ := chkTable_spec ht
  have hk0 : 0 < k2 := by
    rcases Nat.eq_zero_or_pos k2 with h | h
    · rw [h, Nat.mul_zero] at hid
      omega
    · exact h
  unfold sch
  refine H.mul_mem (H.mul_mem (wv_mem ht hk hH _ ?_) (ltv_mem hk hH (Nat.mod_lt _ hk0)))
    (H.inv_mem (wv_mem ht hk hH _ (hT _ hid)))
  exact (Nat.div_lt_iff_lt_mul hk0).2 hid

theorem relIndex_le_of_cover {K H : Subgroup G} (w : ℕ → G) {n : ℕ} (hw : ∀ c < n, w c ∈ H)
    (hcov : ∀ x ∈ H, ∃ c < n, x * (w c)⁻¹ ∈ K) : K.relIndex H ≠ 0 ∧ K.relIndex H ≤ n := by
  let f : Fin n → H ⧸ K.subgroupOf H := fun c => ((⟨(w c)⁻¹, H.inv_mem (hw c c.2)⟩ : H) :
    H ⧸ K.subgroupOf H)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨c, hc, hK⟩ := hcov _ (H.inv_mem y.2)
    refine ⟨⟨c, hc⟩, ?_⟩
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf]
    have e : ((⟨(w c)⁻¹, H.inv_mem (hw c hc)⟩ : H)⁻¹ * y : H) = w c * (y : G) := by
      simp
    rw [e]
    have : (w c * (y : G))⁻¹ = (y : G)⁻¹ * (w c)⁻¹ := by group
    rw [← K.inv_mem_iff, this]
    exact hK
  have hfin : Finite (H ⧸ K.subgroupOf H) := Finite.of_surjective f hf
  refine ⟨Subgroup.index_ne_zero_iff_finite.2 hfin, ?_⟩
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_card]
  calc _ ≤ Nat.card (Fin n) := Nat.card_le_card_of_surjective f hf
    _ = n := Nat.card_eq_fintype_card.trans (Fintype.card_fin n)

@[expose] noncomputable def K0 (T P k2 nc : ℕ) (gen : ℕ → G) : Subgroup G :=
  Subgroup.closure (sch T P k2 gen '' {id | id < nc * k2})

theorem cover_K0 {T P k2 nc : ℕ} (ht : chkTable T P k2 nc = true) (hnc : 0 < nc) (hk : k2 % 2 = 0)
    (gen : ℕ → G) :
    (K0 T P k2 nc gen).relIndex (Subgroup.closure (gen '' {g | 2 * g < k2})) ≠ 0 ∧
      (K0 T P k2 nc gen).relIndex (Subgroup.closure (gen '' {g | 2 * g < k2})) ≤ nc := by
  set H := Subgroup.closure (gen '' {g | 2 * g < k2})
  have hH : ∀ g, 2 * g < k2 → gen g ∈ H := fun g hg => Subgroup.subset_closure ⟨g, hg, rfl⟩
  obtain ⟨hT, -⟩ := chkTable_spec ht
  apply relIndex_le_of_cover (wv P gen) (wv_mem ht hk hH)
  have step : ∀ x : G, ∀ l < k2, (∃ c < nc, x * (wv P gen c)⁻¹ ∈ K0 T P k2 nc gen) →
      ∃ c < nc, x * ltv gen l * (wv P gen c)⁻¹ ∈ K0 T P k2 nc gen := by
    rintro x l hl ⟨c, hc, hx⟩
    have hid : c * k2 + l < nc * k2 := by
      calc c * k2 + l < c * k2 + k2 := by omega
        _ = (c + 1) * k2 := by ring
        _ ≤ nc * k2 := Nat.mul_le_mul_right _ (by omega)
    refine ⟨t8 T (c * k2 + l), hT _ hid, ?_⟩
    have hs : sch T P k2 gen (c * k2 + l) ∈ K0 T P k2 nc gen :=
      Subgroup.subset_closure ⟨_, hid, rfl⟩
    have e : x * ltv gen l * (wv P gen (t8 T (c * k2 + l)))⁻¹ =
        x * (wv P gen c)⁻¹ * sch T P k2 gen (c * k2 + l) := by
      unfold sch
      rw [id_div hl, id_mod hl]
      group
    rw [e]
    exact (K0 T P k2 nc gen).mul_mem hx hs
  intro x hx
  induction hx using Subgroup.closure_induction_right with
  | one => exact ⟨0, hnc, by rw [wv_zero, inv_one, mul_one]; exact Subgroup.one_mem _⟩
  | mul_right x _ y hy ih =>
    obtain ⟨g, hg, rfl⟩ := hy
    have := step x (2 * g) hg ih
    rwa [ltv_even] at this
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨g, hg, rfl⟩ := hy
    have hg' : 2 * g < k2 := hg
    have := step x (2 * g + 1) (by omega) ih
    rwa [ltv_odd] at this

theorem id_lt {c l k2 nc : ℕ} (hc : c < nc) (hl : l < k2) : c * k2 + l < nc * k2 :=
  calc c * k2 + l < c * k2 + k2 := by omega
    _ = (c + 1) * k2 := by ring
    _ ≤ nc * k2 := Nat.mul_le_mul_right _ (by omega)

theorem trace_spec {T P k2 nc : ℕ} (ht : chkTable T P k2 nc = true) (hb : nc * k2 < 32768)
    (gen : ℕ → G) {w n c : ℕ} (hc : c < nc) (hw : ∀ i < n, lt w i < k2) : ∀ k ≤ n,
    (trRec T P k2 w c k).1 < nc ∧ ∃ acc : List ℕ, (trRec T P k2 w c k).2 = (enc acc, acc.length) ∧
      acc.length ≤ k ∧ Ok16 acc ∧ (∀ x ∈ acc, ∃ id, x = 2 * id ∧ (gens T P k2 nc).testBit id = true) ∧
      lv (sch T P k2 gen) acc = wv P gen c * lv gen (wl w k) * (wv P gen (trRec T P k2 w c k).1)⁻¹ := by
  obtain ⟨hT, -⟩ := chkTable_spec ht
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨hc, [], rfl, le_refl _, fun _ h => absurd h (by simp), fun _ h => absurd h (by simp), ?_⟩
    simp [wl, trRec]
  | succ k ih =>
    intro hk
    obtain ⟨hcur, acc, hacc, hlen, hok, hlet, hval⟩ := ih (by omega)
    rw [trRec_succ]
    generalize hq : trRec T P k2 w c k = q at hcur hacc hval
    obtain ⟨cur, wm⟩ := q
    simp only at hcur hacc hval
    subst hacc
    have hl := hw k (by omega)
    have hid := id_lt hcur hl
    unfold trBody
    dsimp only
    simp only [Nat.add_eq, Nat.mul_eq]
    refine ⟨hT _ hid, ?_⟩
    cases htr : isTree P cur (lt w k) (t8 T (cur * k2 + lt w k))
    · dsimp only
      refine ⟨acc ++ [2 * (cur * k2 + lt w k)], push_eq hok _, by simp; omega, ?_, ?_, ?_⟩
      · rw [ok16_append]
        refine ⟨hok, fun d hd => ?_⟩
        rw [List.mem_singleton] at hd
        rw [hd]
        omega
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hlet x hx
        · rw [List.mem_singleton] at hx
          refine ⟨_, hx, (gens_testBit _ _ _ _ _).2 ⟨hid, ?_⟩⟩
          rw [id_div hl, id_mod hl]
          exact htr
      · rw [lv_append, hval, lv_singleton, ltv_even, wl_succ, lv_append, lv_singleton]
        unfold sch
        rw [id_div hl, id_mod hl]
        group
    · dsimp only
      refine ⟨acc, rfl, by omega, hok, hlet, ?_⟩
      have h1 := sch_tree ht gen hcur hl htr
      unfold sch at h1
      rw [id_div hl, id_mod hl] at h1
      rw [hval, wl_succ, lv_append, lv_singleton]
      calc wv P gen c * lv gen (wl w k) * (wv P gen cur)⁻¹ =
          wv P gen c * lv gen (wl w k) * (wv P gen cur)⁻¹ *
            (wv P gen cur * ltv gen (lt w k) * (wv P gen (t8 T (cur * k2 + lt w k)))⁻¹) := by
            rw [h1, mul_one]
        _ = _ := by group

@[expose] def RelOK (sv : ℕ → G) (Gs y : ℕ) : Prop :=
  ∃ acc : List ℕ, y = pk (enc acc) acc.length ∧ acc.length < 2 ^ 16 ∧ Ok16 acc ∧ lv sv acc = 1 ∧
    ∀ x ∈ acc, Gs.testBit (x / 2) = true

theorem relOK_zero (sv : ℕ → G) (Gs : ℕ) : RelOK sv Gs 0 :=
  ⟨[], rfl, by norm_num, fun _ h => absurd h (by simp), rfl, fun _ h => absurd h (by simp)⟩

theorem relOK_getD {sv : ℕ → G} {Gs : ℕ} {L : List ℕ} (h : ∀ y ∈ L, RelOK sv Gs y) (i : ℕ) :
    RelOK sv Gs (L.getD i 0) := by
  rcases Nat.lt_or_ge i L.length with hi | hi
  · exact h _ (mem_getD hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
    exact relOK_zero sv Gs

theorem relOK_pw_pn {y : ℕ} {acc : List ℕ} (hy : y = pk (enc acc) acc.length)
    (hl : acc.length < 2 ^ 16) (hok : Ok16 acc) :
    pw y = enc acc ∧ pn y = acc.length ∧ wl (pw y) (pn y) = acc := by
  subst hy
  rw [pw_pk hl, pn_pk hl, wl_enc hok]
  exact ⟨rfl, rfl, rfl⟩

theorem closes_relOK {T P k2 nc : ℕ} (ht : chkTable T P k2 nc = true) (hb : nc * k2 < 32768)
    (gen : ℕ → G) {x y : ℕ} (hx : ∀ i < pn x, lt (pw x) i < k2)
    (hv : lv gen (wl (pw x) (pn x)) = 1) (hc : Closes T P k2 nc x y) :
    RelOK (sch T P k2 gen) (gens T P k2 nc) y := by
  obtain ⟨c, hc, he, rfl⟩ := hc
  obtain ⟨-, acc, hacc, hlen, hok, hlet, hval⟩ := trace_spec ht hb gen hc hx (pn x) (le_refl _)
  rw [← trace_eq] at hacc hval
  rw [hacc]
  refine ⟨acc, rfl, Nat.lt_of_le_of_lt hlen (pn_lt x), hok, ?_, ?_⟩
  · rw [hval, hv, he, mul_one, mul_inv_cancel]
  · intro z hz
    obtain ⟨id, rfl, hid⟩ := hlet z hz
    rwa [Nat.mul_div_cancel_left _ (by norm_num)]

@[expose] def Inv (sv : ℕ → G) (B : ℕ) (K : Subgroup G) (A : List ℕ) (Gs : ℕ) : Prop :=
  (∀ y ∈ A, RelOK sv Gs y) ∧ (∀ j, Gs.testBit j = true → j < B) ∧
    K ≤ Subgroup.closure (sv '' {j | Gs.testBit j = true})

theorem lv_mem {sv : ℕ → G} {Gs : ℕ} {L : List ℕ} (h : ∀ x ∈ L, Gs.testBit (x / 2) = true) :
    lv sv L ∈ Subgroup.closure (sv '' {j | Gs.testBit j = true}) := by
  induction L with
  | nil => exact Subgroup.one_mem _
  | cons x L ih =>
    rw [lv_cons]
    refine Subgroup.mul_mem _ ?_ (ih fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hm : sv (x / 2) ∈ Subgroup.closure (sv '' {j | Gs.testBit j = true}) :=
      Subgroup.subset_closure ⟨_, h x (List.mem_cons_self ..), rfl⟩
    unfold ltv
    split
    · exact hm
    · exact Subgroup.inv_mem _ hm

theorem countP_wl (w g : ℕ) : ∀ n, ((Finset.range n).filter fun i => lt w i / 2 = g).card =
    (wl w n).countP fun d => d / 2 = g := by
  intro n
  induction n with
  | zero => simp [wl]
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert, wl_succ, List.countP_append, ← ih]
    by_cases h : lt w n / 2 = g
    · rw [ite_eq_left h, Finset.card_insert_of_notMem (by simp)]
      simp [h]
    · rw [ite_eq_right h]
      simp [h]

theorem length_subL {L : List ℕ} {g : ℕ} {S Si : List ℕ} (hl : Si.length = S.length) :
    (subL L g S Si).length ≤ L.length + (L.countP fun d => d / 2 = g) * S.length := by
  induction L with
  | nil => simp [subL]
  | cons l L ih =>
    have e : subL (l :: L) g S Si = (if l / 2 = g then (if l % 2 = 1 then Si else S) else [l]) ++
        subL L g S Si := by simp [subL]
    rw [e, List.length_append, List.countP_cons, List.length_cons]
    by_cases h : l / 2 = g
    · have h1 : (if l / 2 = g then (if l % 2 = 1 then Si else S) else [l]).length = S.length := by
        rw [ite_eq_left h]
        split
        · exact hl
        · rfl
      rw [h1]
      simp only [h, decide_true, ite_true]
      rw [Nat.add_mul, Nat.one_mul]
      omega
    · rw [ite_eq_right h, decide_eq_false h]
      simp only [List.length_singleton, Bool.false_eq_true, ite_false, Nat.add_zero]
      omega

theorem substFits_spec {L : List ℕ} {g ns : ℕ} (h : substFits L g ns = true) :
    ∀ y ∈ L, pn y + (occ (pw y) (pn y) g).1 * ns < 65536 := by
  induction L with
  | nil => intro y hy; simp at hy
  | cons x L ih =>
    change mAnd (Prod.rec (motive := fun _ => Bool)
        (fun c _ => Nat.blt (Nat.add (pn x) (Nat.mul c ns)) (nat_lit 65536)) (occ (pw x) (pn x) g))
      (substFits L g ns) = true at h
    rw [mAnd_iff] at h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · have := h.1
      generalize occ (pw y) (pn y) g = q at this ⊢
      obtain ⟨c, p⟩ := q
      exact (blt_iff _ _).1 this
    · exact ih h.2 y hy

theorem mem_take_pos {L : List ℕ} {p d : ℕ} (h : d ∈ L.take p) : ∃ i < p, ∃ hi : i < L.length, L[i] = d := by
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 h
  simp only [List.length_take] at hi
  exact ⟨i, by omega, by omega, by rw [← e, List.getElem_take]⟩

theorem mem_drop_pos {L : List ℕ} {p d : ℕ} (h : d ∈ L.drop (p + 1)) :
    ∃ i, p < i ∧ ∃ hi : i < L.length, L[i] = d := by
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 h
  simp only [List.length_drop] at hi
  exact ⟨p + 1 + i, by omega, by omega, by rw [← e, List.getElem_drop]⟩

theorem stepS_inv {sv : ℕ → G} {B : ℕ} {K : Subgroup G} {A : List ℕ} {Gs g i : ℕ}
    (hB15 : B ≤ 32768) (hinv : Inv sv B K A Gs) (hg : Gs.testBit g = true)
    (hc : (occ (pw (getR A i)) (pn (getR A i)) g).1 = 1)
    (hfit : substFits A g (pn (getR A i)) = true) :
    Inv sv B K (mapSubst A g (solveAt (pw (getR A i)) (pn (getR A i)) (occ (pw (getR A i)) (pn (getR A i)) g).2).1
        (wInv (solveAt (pw (getR A i)) (pn (getR A i)) (occ (pw (getR A i)) (pn (getR A i)) g).2).1
          (solveAt (pw (getR A i)) (pn (getR A i)) (occ (pw (getR A i)) (pn (getR A i)) g).2).2)
        (solveAt (pw (getR A i)) (pn (getR A i)) (occ (pw (getR A i)) (pn (getR A i)) g).2).2)
      (Gs - 2 ^ g) := by
  obtain ⟨hA, hB, hK⟩ := hinv
  obtain ⟨LR, hR, hRl, hRok, hRv, hRlet⟩ := relOK_getD hA i
  rw [getR_eq] at hc hfit ⊢
  rw [hR] at hc hfit ⊢
  simp only [pw_pk hRl, pn_pk hRl] at hc hfit ⊢
  obtain ⟨hp, hpg, huniq⟩ := occ_spec hc
  generalize (occ (enc LR) LR.length g).2 = p at hp hpg huniq ⊢
  have hwl' : wl (enc LR) LR.length = LR := wl_enc hRok
  rw [solveAt_eq _ _ _ hp, hwl']
  have hlt : ∀ j (hj : j < LR.length), lt (enc LR) j = LR[j]'hj := fun j hj => by
    rw [lt_enc hRok, getD_of_lt hj]
  have hQ : ∀ d ∈ solL LR p, Gs.testBit (d / 2) = true ∧ d / 2 ≠ g := by
    intro d hd
    have hd' := mem_frL hd
    rcases List.mem_append.1 hd' with hd' | hd'
    · obtain ⟨e, he, rfl⟩ := mem_invL hd'
      obtain ⟨j, hj, hjl, rfl⟩ := mem_take_pos he
      rw [xor1_div]
      refine ⟨hRlet _ (List.getElem_mem _), fun h => ?_⟩
      have := huniq j hjl (by rw [hlt j hjl]; exact h)
      omega
    · obtain ⟨e, he, rfl⟩ := mem_invL hd'
      obtain ⟨j, hj, hjl, rfl⟩ := mem_drop_pos he
      rw [xor1_div]
      refine ⟨hRlet _ (List.getElem_mem _), fun h => ?_⟩
      have := huniq j hjl (by rw [hlt j hjl]; exact h)
      omega
  have hsplit : LR = LR.take p ++ [LR[p]'hp] ++ LR.drop (p + 1) := by
    rw [List.append_assoc, List.singleton_append, List.cons_getElem_drop_succ, List.take_append_drop]
  have hval : lv sv (solL LR p) = ltv sv (LR[p]'hp) := by
    unfold solL
    rw [lv_frL, lv_append, lv_invL, lv_invL]
    rw [hsplit, lv_append, lv_append, lv_singleton] at hRv
    have : ltv sv (LR[p]'hp) = (lv sv (LR.take p))⁻¹ * (lv sv (LR.drop (p + 1)))⁻¹ := by
      rw [← mul_inv_rev, eq_inv_iff_mul_eq_one, ← mul_assoc]
      have h2 := hRv
      rw [mul_assoc] at h2 ⊢
      have := congrArg (fun z => (lv sv (List.take p LR))⁻¹ * z * lv sv (List.take p LR)) h2
      simp only [mul_one, inv_mul_cancel_left, inv_mul_cancel] at this
      rw [← mul_assoc]
      exact this
    rw [this]
  have hpg' : (LR[p]'hp) / 2 = g := by rw [← hlt p hp]; exact hpg
  set S := if lt (enc LR) p % 2 = 1 then invL (solL LR p) else solL LR p with hS
  have hSpair : (if lt (enc LR) p % 2 = 1 then (enc (invL (solL LR p)), (solL LR p).length)
      else (enc (solL LR p), (solL LR p).length)) = (enc S, S.length) := by
    rw [hS]
    split <;> simp
  rw [hSpair]
  dsimp only
  have hSQ : ∀ d ∈ S, Gs.testBit (d / 2) = true ∧ d / 2 ≠ g := by
    intro d hd
    rw [hS] at hd
    split at hd
    · obtain ⟨e, he, rfl⟩ := mem_invL hd
      rw [xor1_div]
      exact hQ e he
    · exact hQ d hd
  have hSiQ : ∀ d ∈ invL S, Gs.testBit (d / 2) = true ∧ d / 2 ≠ g := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := mem_invL hd
    rw [xor1_div]
    exact hSQ e he
  have hok16 : ∀ d, Gs.testBit (d / 2) = true → d < 2 ^ 16 := by
    intro d hd
    have := hB _ hd
    omega
  have hSok : Ok16 S := fun d hd => hok16 d (hSQ d hd).1
  have hSiok : Ok16 (invL S) := ok16_invL hSok
  rw [wInv_eq, wl_enc hSok]
  have hSv : lv sv S = sv g := by
    rw [hS, hlt p hp]
    split
    · rename_i hodd
      rw [lv_invL, hval]
      unfold ltv
      rw [ite_eq_right (by omega), hpg', inv_inv]
    · rename_i hev
      rw [hval]
      unfold ltv
      rw [ite_eq_left (by omega), hpg']
  have hSiv : lv sv (invL S) = (sv g)⁻¹ := by rw [lv_invL, hSv]
  have hSlen : S.length < LR.length := by
    have : (solL LR p).length < LR.length := by
      unfold solL
      refine Nat.lt_of_le_of_lt (length_frL _) ?_
      simp only [List.length_append, length_invL, List.length_take, List.length_drop]
      omega
    rw [hS]
    split
    · rw [length_invL]
      exact this
    · exact this
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    rw [mapSubst_eq] at hy
    obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hy
    obtain ⟨Lh, hLh, hLhl, hLhok, hLhv, hLhlet⟩ := hA h hh
    have hfit' := substFits_spec hfit h hh
    obtain ⟨hpw', hpn', hwl''⟩ := relOK_pw_pn hLh hLhl hLhok
    rw [hpw', hpn'] at hfit'
    rw [subst_eq hSok hSiok (length_invL S), hwl'']
    have hcnt : (occ (enc Lh) Lh.length g).1 = Lh.countP fun d => d / 2 = g := by
      rw [occ_eq, (ocRec_inv _ _ _).1, countP_wl, wl_enc hLhok]
    rw [hcnt] at hfit'
    have hlen := length_subL (L := Lh) (g := g) (length_invL S)
    have hlen2 := length_redL (subL Lh g S (invL S))
    have hm : (Lh.countP fun d => d / 2 = g) * S.length ≤ (Lh.countP fun d => d / 2 = g) * LR.length :=
      Nat.mul_le_mul_left _ (le_of_lt hSlen)
    refine ⟨_, rfl, by omega, ok16_redL ?_, lv_redL sv (by rw [lv_subL sv Lh g hSv hSiv]; exact hLhv), ?_⟩
    · intro d hd
      rcases mem_subL hd with ⟨hd, -⟩ | hd | hd
      · exact hLhok d hd
      · exact hSok d hd
      · exact hSiok d hd
    · intro d hd
      rw [testBit_sub_pow hg, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
      rcases mem_subL (mem_redL hd) with ⟨hd, hne⟩ | hd | hd
      · exact ⟨hLhlet d hd, hne⟩
      · exact hSQ d hd
      · exact hSiQ d hd
  · intro j hj
    rw [testBit_sub_pow hg, Bool.and_eq_true] at hj
    exact hB j hj.1
  · refine hK.trans ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨j, hj, rfl⟩
    by_cases hjg : j = g
    · rw [hjg, ← hSv]
      apply lv_mem
      intro d hd
      rw [testBit_sub_pow hg, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
      exact hSQ d hd
    · apply Subgroup.subset_closure
      refine ⟨j, ?_, rfl⟩
      change (Gs - 2 ^ g).testBit j = true
      rw [testBit_sub_pow hg, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
      exact ⟨hj, hjg⟩


theorem relOK_set {sv : ℕ → G} {Gs : ℕ} {A : List ℕ} (hA : ∀ y ∈ A, RelOK sv Gs y) {x : ℕ}
    (hx : RelOK sv Gs x) (j : ℕ) : ∀ y ∈ setR A j x, RelOK sv Gs y := by
  intro y hy
  rw [setR_eq] at hy
  rcases mem_set hy with hy | rfl
  · exact hA y hy
  · exact hx

theorem relOK_comb {sv : ℕ → G} {Gs : ℕ} {Li Lj : List ℕ} (hBi : ∀ x ∈ Li, x < 2 ^ 16)
    (hBj : ∀ x ∈ Lj, x < 2 ^ 16) (hvi : lv sv Li = 1) (hvj : lv sv Lj = 1)
    (hli : ∀ x ∈ Li, Gs.testBit (x / 2) = true) (hlj : ∀ x ∈ Lj, Gs.testBit (x / 2) = true)
    (hfit : Li.length + Lj.length < 65536) (a b : ℕ) (e : Bool) :
    RelOK sv Gs (red (Nat.lor (Bool.rec (enc (Li.drop b ++ Li.take b))
        (enc (invL (Li.drop b ++ Li.take b))) e) (Nat.shiftLeft (enc (Lj.drop a ++ Lj.take a))
        (Nat.mul 16 Li.length))) (Nat.add Li.length Lj.length)) := by
  set A1 := Bool.rec (motive := fun _ => List ℕ) (Li.drop b ++ Li.take b)
    (invL (Li.drop b ++ Li.take b)) e with hA1
  set B1 := Lj.drop a ++ Lj.take a
  have hA1l : A1.length = Li.length := by
    rw [hA1]
    cases e
    · exact length_rot Li b
    · rw [length_invL]
      exact length_rot Li b
  have hA1ok : Ok16 A1 ∧ lv sv A1 = 1 ∧ ∀ x ∈ A1, Gs.testBit (x / 2) = true := by
    rw [hA1]
    cases e
    · exact ⟨fun x hx => hBi x (mem_rot hx), lv_rot sv hvi b, fun x hx => hli x (mem_rot hx)⟩
    · refine ⟨ok16_invL fun x hx => hBi x (mem_rot hx), by rw [lv_invL, lv_rot sv hvi b, inv_one],
        fun x hx => ?_⟩
      obtain ⟨y, hy, rfl⟩ := mem_invL hx
      rw [xor1_div]
      exact hli y (mem_rot hy)
  have hB1ok : Ok16 B1 := fun x hx => hBj x (mem_rot hx)
  have e1 : Bool.rec (enc (Li.drop b ++ Li.take b)) (enc (invL (Li.drop b ++ Li.take b))) e = enc A1 := by
    rw [hA1]
    cases e <;> rfl
  rw [e1, ← hA1l, enc_concat hA1ok.1]
  have e2 : Nat.add A1.length Lj.length = (A1 ++ B1).length := by
    rw [List.length_append, length_rot]
    rfl
  rw [e2, red_eq_enc (ok16_append.2 ⟨hA1ok.1, hB1ok⟩)]
  have hlen := length_redL (A1 ++ B1)
  rw [List.length_append, hA1l, length_rot] at hlen
  refine ⟨_, rfl, by omega, ok16_redL (ok16_append.2 ⟨hA1ok.1, hB1ok⟩),
    lv_redL sv (by rw [lv_append, hA1ok.2.1, lv_rot sv hvj a, mul_one]), fun x hx => ?_⟩
  rcases List.mem_append.1 (mem_redL hx) with hx | hx
  · exact hA1ok.2.2 x hx
  · exact hlj x (mem_rot hx)

theorem relOK_bound {B Gs : ℕ} (hB15 : B ≤ 32768) (hB : ∀ j, Gs.testBit j = true → j < B)
    {L : List ℕ} (h : ∀ x ∈ L, Gs.testBit (x / 2) = true) : ∀ x ∈ L, x < 2 ^ 16 := by
  intro x hx
  have := hB _ (h x hx)
  omega

theorem stepC_inv {sv : ℕ → G} {B : ℕ} {K : Subgroup G} {A : List ℕ} {Gs j i a b inv : ℕ}
    (hB15 : B ≤ 32768) (hinv : Inv sv B K A Gs)
    (hfit : pn (getR A i) + pn (getR A j) < 65536) :
    Inv sv B K (stepC true A Gs j i a b inv).2.1 Gs := by
  obtain ⟨hA, hB, hK⟩ := hinv
  refine ⟨?_, hB, hK⟩
  unfold stepC
  dsimp only
  rw [getR_eq, getR_eq] at hfit ⊢
  obtain ⟨Li, hRi, hli, hoki, hvi, hleti⟩ := relOK_getD hA i
  obtain ⟨Lj, hRj, hlj, hokj, hvj, hletj⟩ := relOK_getD hA j
  rw [hRi, hRj] at hfit ⊢
  simp only [pw_pk hli, pn_pk hli, pw_pk hlj, pn_pk hlj] at hfit ⊢
  rw [rot_eq hoki, rot_eq hokj, wInv_eq, ← length_rot Li b, wl_enc (fun x hx => hoki x (mem_rot hx)),
    length_rot]
  exact relOK_set hA (relOK_comb (relOK_bound hB15 hB hleti) (relOK_bound hB15 hB hletj) hvi hvj
    hleti hletj hfit a b _) j


theorem sub_shl (G g : ℕ) : Nat.sub G (Nat.shiftLeft 1 g) = G - 2 ^ g := by
  change G - (1 <<< g) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem stepG_inv {sv : ℕ → G} {B : ℕ} {K : Subgroup G} (hB15 : B ≤ 32768) (r : ℕ) {ok : Bool}
    {A : List ℕ} {Gs : ℕ} (hinv : Inv sv B K A Gs) (h : (stepG r (ok, (A, Gs))).1 = true) :
    ok = true ∧ Inv sv B K (stepG r (ok, (A, Gs))).2.1 (stepG r (ok, (A, Gs))).2.2 := by
  unfold stepG at h ⊢
  dsimp only at h ⊢
  cases hf : stepFits r A
  · rw [hf] at h
    have h' : false = true := h
    exact absurd h' (by decide)
  rw [hf] at h
  dsimp only at h ⊢
  unfold step at h ⊢
  dsimp only at h ⊢
  unfold stepFits at hf
  rcases (show Nat.land r 3 = 0 ∨ Nat.land r 3 = 1 ∨ Nat.land r 3 = 2 ∨ 3 ≤ Nat.land r 3 by omega)
    with h0 | h0 | h0 | h0
  · have hb : Nat.beq (Nat.land r 3) 0 = true := (beq_iff _ _).2 h0
    rw [hb] at h hf ⊢
    dsimp only at h hf ⊢
    unfold stepS at h ⊢
    dsimp only at h ⊢
    generalize hq : occ (pw (getR A (fld r 18))) (pn (getR A (fld r 18))) (fld r 2) = q at h ⊢
    obtain ⟨c, p⟩ := q
    dsimp only at h ⊢
    generalize hs : solveAt (pw (getR A (fld r 18))) (pn (getR A (fld r 18))) p = sl at h ⊢
    obtain ⟨s, ns⟩ := sl
    dsimp only at h ⊢
    rw [mAnd_iff, mAnd_iff, live_iff, beq_iff] at h
    obtain ⟨hok, hg, hc⟩ := h
    refine ⟨hok, ?_⟩
    have := stepS_inv (i := fld r 18) hB15 hinv hg (by rw [hq]; exact hc) hf
    rw [hq] at this
    dsimp only at this
    rw [hs] at this
    simp only at this
    rw [sub_shl]
    exact this
  · have hb0 : Nat.beq (Nat.land r 3) 0 = false := by rw [beq_decide, h0]; rfl
    have hb : Nat.beq (Nat.land r 3) 1 = true := (beq_iff _ _).2 h0
    rw [hb0, hb] at h hf ⊢
    dsimp only at h hf ⊢
    unfold stepC at h ⊢
    dsimp only at h ⊢
    refine ⟨h, ?_⟩
    have := stepC_inv (j := fld r 2) (i := fld r 18) (a := fld r 34) (b := fld r 50)
      (inv := Nat.land (Nat.shiftRight r 66) 1) hB15 hinv ((blt_iff _ _).1 hf)
    unfold stepC at this
    exact this
  · have hb0 : Nat.beq (Nat.land r 3) 0 = false := by rw [beq_decide, h0]; rfl
    have hb1 : Nat.beq (Nat.land r 3) 1 = false := by rw [beq_decide, h0]; rfl
    have hb : Nat.beq (Nat.land r 3) 2 = true := (beq_iff _ _).2 h0
    rw [hb0, hb1, hb] at h ⊢
    dsimp only at h ⊢
    obtain ⟨hA, hB, hK⟩ := hinv
    exact ⟨h, relOK_set hA (relOK_zero sv Gs) _, hB, hK⟩
  · have hb0 : Nat.beq (Nat.land r 3) 0 = false := by
      rw [beq_decide, decide_eq_false_iff_not]
      omega
    have hb1 : Nat.beq (Nat.land r 3) 1 = false := by
      rw [beq_decide, decide_eq_false_iff_not]
      omega
    have hb : Nat.beq (Nat.land r 3) 2 = false := by
      rw [beq_decide, decide_eq_false_iff_not]
      omega
    rw [hb0, hb1, hb] at h
    have h' : false = true := h
    exact absurd h' (by decide)

theorem stepG_ok (r : ℕ) {ok : Bool} {A : List ℕ} {Gs : ℕ} (h : (stepG r (ok, (A, Gs))).1 = true) :
    ok = true := by
  cases ok
  · exfalso
    unfold stepG at h
    dsimp only at h
    cases hf : stepFits r A
    · rw [hf] at h
      exact Bool.false_ne_true h
    · rw [hf] at h
      dsimp only at h
      unfold step stepS stepC at h
      dsimp only at h
      cases h0 : Nat.beq (Nat.land r 3) 0
      · rw [h0] at h
        cases h1 : Nat.beq (Nat.land r 3) 1
        · rw [h1] at h
          cases h2 : Nat.beq (Nat.land r 3) 2
          · rw [h2] at h
            exact Bool.false_ne_true h
          · rw [h2] at h
            exact Bool.false_ne_true h
        · rw [h1] at h
          exact Bool.false_ne_true h
      · rw [h0] at h
        exact Bool.false_ne_true h
  · rfl

theorem replayG_inv {sv : ℕ → G} {B : ℕ} {K : Subgroup G} (hB15 : B ≤ 32768) (Bk : ℕ) :
    ∀ (m : ℕ) {ok : Bool} {A : List ℕ} {Gs : ℕ}, Inv sv B K A Gs →
      (replayG Bk m (ok, (A, Gs))).1 = true →
        ok = true ∧ Inv sv B K (replayG Bk m (ok, (A, Gs))).2.1 (replayG Bk m (ok, (A, Gs))).2.2 := by
  intro m
  induction m with
  | zero => intro ok A Gs hinv h; exact ⟨h, hinv⟩
  | succ m ih =>
    intro ok A Gs hinv h
    change (stepG _ (replayG Bk m (ok, (A, Gs)))).1 = true at h
    change ok = true ∧ Inv sv B K (stepG _ (replayG Bk m (ok, (A, Gs)))).2.1
      (stepG _ (replayG Bk m (ok, (A, Gs)))).2.2
    generalize hq : replayG Bk m (ok, (A, Gs)) = q at h ⊢
    obtain ⟨ok', A', Gs'⟩ := q
    have hih := ih (ok := ok) hinv
    rw [hq] at hih
    have h1 := stepG_ok _ h
    obtain ⟨h2, h3⟩ := hih h1
    exact ⟨h2, (stepG_inv hB15 _ h3 h).2⟩

theorem rsChain_inv {sv : ℕ → G} {B : ℕ} {K : Subgroup G} (hB15 : B ≤ 32768) {N : ℕ} {Rn : List ℕ}
    {ng kq : ℕ} : ∀ (steps : List (ℕ × (ℕ × (List ℕ × ℕ)))) {A : List ℕ} {GA : ℕ},
    Inv sv B K A GA → rsChain A GA steps N Rn ng kq = true →
      ∃ L Gf, Inv sv B K L Gf ∧ chkNext N L Rn Gf ng kq = true := by
  intro steps
  induction steps with
  | nil => intro A GA hinv h; exact ⟨A, GA, hinv, h⟩
  | cons st rest ih =>
    intro A GA hinv h
    obtain ⟨Bk, m, A', G'⟩ := st
    change mAnd (chkReplayG Bk m A A' GA G') (rsChain A' G' rest N Rn ng kq) = true at h
    rw [mAnd_iff] at h
    obtain ⟨h1, h2⟩ := h
    unfold chkReplayG at h1
    rw [mAnd_iff] at h1
    have h3 := h1.2
    have hr := replayG_inv (sv := sv) (K := K) hB15 Bk m (ok := true) hinv
    generalize replayG Bk m (true, (A, GA)) = q at h3 hr
    obtain ⟨ok, L, Gf⟩ := q
    dsimp only at h3 hr
    rw [mAnd_iff, mAnd_iff, beq_iff] at h3
    obtain ⟨hok, hL, hG⟩ := h3
    have hinv' := (hr hok).2
    rw [eqRL_eq hL, hG] at hinv'
    exact ih hinv' h2

end CFSG.KM24.RS

end
