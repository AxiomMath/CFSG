module

public import Certificates.Certificate442001
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameSylow
public import CFSG.GH74.KGroups.ClassCount

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

theorem sylowChk_true : Certificates.OmegaT0.sylowChk () = true :=
  (Bool.and_eq_true_iff.1 Certificates.certificate442001).1

theorem n7Chk_true : Certificates.OmegaT0.n7Chk () = true :=
  (Bool.and_eq_true_iff.1 Certificates.certificate442001).2

theorem card_centerIn_QT0 :
    Nat.card (centerIn QT0.originalSubgroup) = 2 := by
  rw [card_centerIn_originalSubgroup QT0 QT0_valid.1]
  have hs := sylowChk_true
  simp only [Certificates.OmegaT0.sylowChk, Bool.and_eq_true, decide_eq_true_eq] at hs
  exact hs.1

theorem centralizer_QT0_le
    {a : P45} (ha : a ∈ QA45.originalSubgroup)
    (h : ∀ t ∈ QT0.originalSubgroup, a * t = t * a) : a ∈ centerIn QT0.originalSubgroup := by
  have hs := sylowChk_true
  simp only [Certificates.OmegaT0.sylowChk, Bool.and_eq_true, decide_eq_true_eq] at hs
  have h2 := forall_of_all QA45 QA45_ok hs.2 a ha
  have hT : (elemsT QT0).all (fun t => decide (a * t = t * a)) = true := by
    rw [List.all_eq_true]
    intro t ht
    exact decide_eq_true (h t ((mem_elemsT QT0 QT0_valid.1 t).1 ht))
  rw [hT] at h2
  have h3 : a ∈ elemsT QT0 := by simpa using h2
  exact mem_centerIn_iff.2 ⟨(mem_elemsT QT0 QT0_valid.1 a).1 h3, h⟩

theorem wordW_mem {M : Type*} [Group M] {H : Subgroup M} {gs : List M} (hgs : ∀ s ∈ gs, s ∈ H)
    (w : List ℕ) : Certificates.OmegaT0.wordW gs w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons i w ih =>
    change gs.getD i 1 * Certificates.OmegaT0.wordW gs w ∈ H
    refine H.mul_mem ?_ ih
    rw [List.getD_eq_getElem?_getD]
    cases h : gs[i]? with
    | none => exact H.one_mem
    | some s => exact hgs s (List.mem_of_getElem? h)

theorem coverW_sound {M : Type*} [Group M] [DecidableEq M] (gs reps L : List M) :
    ∀ ws, Certificates.OmegaT0.coverW gs reps L ws = true → ∀ t ∈ L, t * t = 1 → t ≠ 1 →
      ∃ w, ∃ r ∈ reps,
        Certificates.OmegaT0.wordW gs w * t * (Certificates.OmegaT0.wordW gs w)⁻¹ = r := by
  induction L with
  | nil => exact fun _ _ t ht => absurd ht List.not_mem_nil
  | cons a L ih =>
    intro ws h t ht h1 h2
    by_cases hi : a * a = 1 ∧ a ≠ 1
    · cases ws with
      | nil =>
        simp only [Certificates.OmegaT0.coverW, decide_eq_true hi, ↓reduceIte,
          Bool.false_eq_true] at h
      | cons w ws =>
        simp only [Certificates.OmegaT0.coverW, decide_eq_true hi, ↓reduceIte,
          Bool.and_eq_true] at h
        rcases List.mem_cons.1 ht with rfl | ht
        · obtain ⟨r, hr, e⟩ := List.any_eq_true.1 h.1
          exact ⟨w, r, hr, of_decide_eq_true e⟩
        · exact ih ws h.2 t ht h1 h2
    · simp only [Certificates.OmegaT0.coverW, decide_eq_false hi, ↓reduceIte,
        Bool.false_eq_true] at h
      rcases List.mem_cons.1 ht with rfl | ht
      · exact absurd ⟨h1, h2⟩ hi
      · exact ih ws h t ht h1 h2

theorem nodupB_sound : ∀ (cs : List ℕ) (m : ℕ), Certificates.OmegaT0.nodupB cs m = true →
    cs.Nodup ∧ ∀ c ∈ cs, m.testBit c = false := by
  intro cs
  induction cs with
  | nil => exact fun _ _ => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | cons c cs ih =>
    intro m h
    simp only [Certificates.OmegaT0.nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hn, hb⟩ := ih _ h.2
    have hb' : ∀ d ∈ cs, c ≠ d ∧ m.testBit d = false := fun d hd => by
      have e := hb d hd
      simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at e
      exact ⟨e.2, e.1⟩
    refine ⟨List.nodup_cons.2 ⟨fun hc => (hb' c hc).1 rfl, hn⟩, fun d hd => ?_⟩
    rcases List.mem_cons.1 hd with rfl | hd
    · exact h.1
    · exact (hb' d hd).2

theorem ncard_conjSet_of_orbTr_aux {M : Type*} [Group M] [DecidableEq M] (cd : M → ℕ)
    (gs : List M) (r : M) (ps : List (ℕ × ℕ)) (ts : List (List ℕ)) (k : ℕ)
    (h : Certificates.OmegaT0.orbTr cd gs r ps ts k = true)
    (hr : r ∈ Certificates.OmegaT0.treeL (fun s o => s * o * s⁻¹) r gs ps)
    (hO : ∀ x ∈ Certificates.OmegaT0.treeL (fun s o => s * o * s⁻¹) r gs ps,
      x ∈ conjSet (Subgroup.closure {s | s ∈ gs}) r) :
    (conjSet (Subgroup.closure {s | s ∈ gs}) r).ncard = k := by
  unfold Certificates.OmegaT0.orbTr at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hk, hcd⟩, hlen⟩, htab⟩ := h
  set O := Certificates.OmegaT0.treeL (fun s o => s * o * s⁻¹) r gs ps
  have hnd : O.Nodup := (nodupB_sound _ _ hcd).1.of_map cd
  have hcl : ∀ s ∈ gs, ∀ o ∈ O, s * o * s⁻¹ ∈ O := by
    intro s hs o ho
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
    have hjz : j < (gs.zip ts).length := by
      rw [List.length_zip, hlen, Nat.min_self]
      exact hj
    obtain ⟨hl, hrow⟩ := htab _ (List.getElem_mem hjz)
    rw [List.getElem_zip] at hl hrow
    dsimp only at hl hrow
    have hiz : i < (O.zip ts[j]).length := by
      rw [List.length_zip, hl, ← hk, Nat.min_self]
      exact hi
    obtain ⟨hlt, he⟩ := hrow _ (List.getElem_mem hiz)
    rw [List.getElem_zip] at hlt he
    dsimp only at hlt he
    have hlt' : ts[j][i] < O.length := by
      rw [hk]
      exact hlt
    have e2 : O.getD ts[j][i] r = O[ts[j][i]] := by
      generalize ts[j][i] = m at hlt' ⊢
      simp [List.getD_eq_getElem?_getD, hlt']
    rw [e2] at he
    rw [he]
    exact List.getElem_mem _
  have hinv : ∀ s ∈ gs, ∀ o ∈ O, s⁻¹ * o * s⁻¹⁻¹ ∈ O := by
    intro s hs o ho
    have hm : Set.MapsTo (fun y => s * y * s⁻¹) {y | y ∈ O} {y | y ∈ O} :=
      fun y hy => hcl s hs y hy
    have hinj : Set.InjOn (fun y => s * y * s⁻¹) {y | y ∈ O} :=
      fun a _ b _ e => mul_left_cancel (mul_right_cancel e)
    obtain ⟨y, hy, e⟩ :=
      ((Set.Finite.injOn_iff_bijOn_of_mapsTo (List.finite_toSet O) hm).1 hinj).surjOn ho
    have e' : s * y * s⁻¹ = o := e
    have e2 : s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y := by group
    rw [← e', e2]
    exact hy
  have hP : ∀ g ∈ Subgroup.closure {s | s ∈ gs}, ∀ o ∈ O, g * o * g⁻¹ ∈ O := by
    intro g hg
    induction hg using Subgroup.closure_induction'' with
    | mem s hs => exact fun o ho => hcl s hs o ho
    | inv_mem s hs => exact hinv s hs
    | one => exact fun o ho => by rwa [one_mul, inv_one, mul_one]
    | mul a b _ _ ha hb =>
      intro o ho
      have e : a * b * o * (a * b)⁻¹ = a * (b * o * b⁻¹) * a⁻¹ := by group
      rw [e]
      exact ha _ (hb o ho)
  have heq : conjSet (Subgroup.closure {s | s ∈ gs}) r = (O.toFinset : Set M) := by
    ext x
    rw [List.coe_toFinset, Set.mem_setOf_eq]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hP g hg r hr
    · exact hO x
  rw [heq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hk]

theorem QP45_eq_closure : QP45.originalSubgroup = Subgroup.closure {s | s ∈ [x45, y45]} := by
  rw [QP45, certificate_originalSubgroup, tab_eq, tab_eq]

theorem forall_treeL {M : Type*} [One M] (P : M → Prop) (f : M → M → M) (a : M) (gs : List M)
    (ha : P a) (hf : ∀ k x, P x → P (f (gs.getD k 1) x)) (ps : List (ℕ × ℕ)) :
    ∀ x ∈ Certificates.OmegaT0.treeL f a gs ps, P x := by
  have key : ∀ (L : List M) (ps : List (ℕ × ℕ)), (∀ x ∈ L, P x) →
      ∀ x ∈ ps.foldl (fun L kp => L ++ [f (gs.getD kp.1 1) (L.getD kp.2 a)]) L, P x := by
    intro L ps
    induction ps generalizing L with
    | nil => exact fun h => h
    | cons kp ps ih =>
      intro hL
      simp only [List.foldl_cons]
      refine ih _ fun x hx => ?_
      rcases List.mem_append.1 hx with hx | hx
      · exact hL x hx
      · rw [List.mem_singleton.1 hx]
        refine hf _ _ ?_
        rw [List.getD_eq_getElem?_getD]
        cases h : L[kp.2]? with
        | none => rw [Option.getD_none]; exact ha
        | some y => rw [Option.getD_some]; exact hL y (List.mem_of_getElem? h)
  exact key [a] ps fun x hx => (List.mem_singleton.1 hx) ▸ ha

theorem mem_treeL {M : Type*} [One M] (f : M → M → M) (a : M) (gs : List M)
    (ps : List (ℕ × ℕ)) : a ∈ Certificates.OmegaT0.treeL f a gs ps := by
  have key : ∀ (L : List M) (ps : List (ℕ × ℕ)), a ∈ L →
      a ∈ ps.foldl (fun L kp => L ++ [f (gs.getD kp.1 1) (L.getD kp.2 a)]) L := by
    intro L ps
    induction ps generalizing L with
    | nil => exact id
    | cons kp ps ih =>
      intro h
      simp only [List.foldl_cons]
      exact ih _ (List.mem_append_left _ h)
  exact key [a] ps (List.mem_singleton_self a)

theorem mul_mem_of_mulTab {M : Type*} [Monoid M] [DecidableEq M] (gs L : List M)
    (ts : List (List ℕ)) (k : ℕ) (h : Certificates.OmegaT0.mulTab gs L ts k = true) :
    ∀ s ∈ gs, ∀ x ∈ L, s * x ∈ L := by
  unfold Certificates.OmegaT0.mulTab at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hk, hlen⟩, htab⟩ := h
  intro s hs x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hjz : j < (gs.zip ts).length := by
    rw [List.length_zip, hlen, Nat.min_self]
    exact hj
  have hz := htab _ (List.getElem_mem hjz) i (List.mem_range.2 (hk ▸ hi))
  rw [List.getElem_zip] at hz
  obtain ⟨hlt, he⟩ := hz
  dsimp only at hlt he
  have hlt' : ts[j].getD i 0 < L.length := by
    rw [hk]
    exact hlt
  have e1 : L.getD i 1 = L[i] := by simp [List.getD_eq_getElem?_getD, hi]
  have e2 : L.getD (ts[j].getD i 0) 1 = L[ts[j].getD i 0] := by
    generalize ts[j].getD i 0 = m at hlt' ⊢
    simp [List.getD_eq_getElem?_getD, hlt']
  rw [e1, e2] at he
  rw [he]
  exact List.getElem_mem _

theorem closure_sub_of_mul_mem {M : Type*} [Group M] (gs L : List M) (h1 : (1 : M) ∈ L)
    (h : ∀ s ∈ gs, ∀ x ∈ L, s * x ∈ L) : ∀ g ∈ Subgroup.closure {s | s ∈ gs}, g ∈ L := by
  have hinv : ∀ s ∈ gs, ∀ x ∈ L, s⁻¹ * x ∈ L := by
    intro s hs x hx
    have hm : Set.MapsTo (fun y => s * y) {y | y ∈ L} {y | y ∈ L} := fun y hy => h s hs y hy
    have hinj : Set.InjOn (fun y => s * y) {y | y ∈ L} := fun a _ b _ e => mul_left_cancel e
    obtain ⟨y, hy, e⟩ :=
      ((Set.Finite.injOn_iff_bijOn_of_mapsTo (List.finite_toSet L) hm).1 hinj).surjOn hx
    have e' : s * y = x := e
    rw [← e', inv_mul_cancel_left]
    exact hy
  have hP : ∀ g ∈ Subgroup.closure {s | s ∈ gs}, ∀ x ∈ L, g * x ∈ L := by
    intro g hg
    induction hg using Subgroup.closure_induction'' with
    | mem s hs => exact h s hs
    | inv_mem s hs => exact hinv s hs
    | one => exact fun x hx => by rwa [one_mul]
    | mul a b _ _ ha hb => exact fun x hx => by rw [mul_assoc]; exact ha _ (hb x hx)
  intro g hg
  have := hP g hg 1 h1
  rwa [mul_one] at this

theorem getD_mem_closureW {M : Type*} [Group M] (gs : List M) (k : ℕ) :
    gs.getD k 1 ∈ Subgroup.closure {s | s ∈ gs} := by
  rw [List.getD_eq_getElem?_getD]
  cases h : gs[k]? with
  | none => rw [Option.getD_none]; exact Subgroup.one_mem _
  | some s => rw [Option.getD_some]; exact Subgroup.subset_closure (List.mem_of_getElem? h)

theorem ncard_conjSet_of_orbTr {M : Type*} [Group M] [DecidableEq M] (cd : M → ℕ) (gs : List M)
    (r : M) (ps : List (ℕ × ℕ)) (ts : List (List ℕ)) (k : ℕ)
    (h : Certificates.OmegaT0.orbTr cd gs r ps ts k = true) :
    (conjSet (Subgroup.closure {s | s ∈ gs}) r).ncard = k :=
  ncard_conjSet_of_orbTr_aux cd gs r ps ts k h (mem_treeL _ _ _ _)
    (forall_treeL (fun x => x ∈ conjSet (Subgroup.closure {s | s ∈ gs}) r) _ r gs
      ⟨1, Subgroup.one_mem _, by rw [one_mul, inv_one, mul_one]⟩
      (fun k x ⟨g, hg, e⟩ => ⟨gs.getD k 1 * g, Subgroup.mul_mem _ (getD_mem_closureW gs k) hg, by
        beta_reduce
        rw [e]
        group⟩) ps)

theorem wordXY_eq_wordW (l : List Char) :
    wordXY l = Certificates.OmegaT0.wordW [x45, y45] (l.map fun c => if c = 'x' then 0 else 1) := by
  have key : ∀ g : P45, l.foldl (fun g c => g * if c = 'x' then x45 else y45) g =
      g * Certificates.OmegaT0.wordW [x45, y45] (l.map fun c => if c = 'x' then 0 else 1) := by
    induction l with
    | nil => exact fun g => (mul_one g).symm
    | cons c l ih =>
      intro g
      rw [List.foldl_cons, ih, List.map_cons, mul_assoc]
      congr 1
      change _ = [x45, y45].getD (if c = 'x' then 0 else 1) 1 * _
      congr 1
      by_cases hc : c = 'x' <;> simp [hc]
  exact (key 1).trans (one_mul _)

theorem syl_eq_sylW : [syl1, syl2, syl3] =
    Certificates.OmegaT0.sylW.map (Certificates.OmegaT0.wordW [x45, y45]) := by
  rw [syl1, syl2, syl3, wordXY_eq_wordW, wordXY_eq_wordW, wordXY_eq_wordW]
  simp only [Certificates.OmegaT0.sylW, List.map_cons, List.map_nil]
  exact congrArg₂ List.cons (congrArg _ (by decide))
    (congrArg₂ List.cons (congrArg _ (by decide)) (congrArg₂ List.cons (congrArg _ (by decide)) rfl))

theorem QT0_eq_closure : QT0.originalSubgroup = Subgroup.closure
    {s | s ∈ Certificates.OmegaT0.sylW.map (Certificates.OmegaT0.wordW [x45, y45])} := by
  rw [QT0, certificate_originalSubgroup, tab_eq, tab_eq, tab_eq, syl_eq_sylW]

theorem t0L_spec : (∀ g, g ∈ Certificates.OmegaT0.t0L () ↔ g ∈ QT0.originalSubgroup) ∧
    (Certificates.OmegaT0.t0L ()).Nodup := by
  have hn := n7Chk_true
  simp only [Certificates.OmegaT0.n7Chk, Bool.and_eq_true, and_assoc] at hn
  have hm := hn.1
  have hlen : (Certificates.OmegaT0.t0L ()).length = 64 := by
    have h := hm
    unfold Certificates.OmegaT0.mulTab at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  have hsub : ∀ x ∈ Certificates.OmegaT0.t0L (), x ∈ QT0.originalSubgroup := by
    rw [QT0_eq_closure]
    exact forall_treeL _ (· * ·) 1 _ (Subgroup.one_mem _)
      (fun k x hx => Subgroup.mul_mem _ (getD_mem_closureW _ k) hx) _
  have hsup : ∀ g ∈ QT0.originalSubgroup, g ∈ Certificates.OmegaT0.t0L () := by
    rw [QT0_eq_closure]
    exact closure_sub_of_mul_mem _ _ (mem_treeL _ _ _ _) (mul_mem_of_mulTab _ _ _ _ hm)
  have hmem : ∀ g, g ∈ Certificates.OmegaT0.t0L () ↔ g ∈ QT0.originalSubgroup :=
    fun g => ⟨hsub g, hsup g⟩
  refine ⟨hmem, ?_⟩
  have e : QT0.originalSubgroup ≃ {g // g ∈ (Certificates.OmegaT0.t0L ()).toFinset} :=
    Equiv.subtypeEquivRight fun g => by rw [List.mem_toFinset, hmem]
  have hc : (Certificates.OmegaT0.t0L ()).dedup.length = (Certificates.OmegaT0.t0L ()).length := by
    rw [← List.card_toFinset, hlen, ← card_QT0, Nat.card_congr e, Nat.card_eq_fintype_card,
      Fintype.card_coe]
  rw [← (List.dedup_sublist _).eq_of_length hc]
  exact List.nodup_dedup _

theorem card_inf_centralizer_t0L (τ : P45) :
    Nat.card ↥(QT0.originalSubgroup ⊓ centralizer ({τ} : Set P45)) =
      ((Certificates.OmegaT0.t0L ()).filter (fun g => decide (g * τ = τ * g))).length := by
  refine card_eq_length (fun g : P45 => g ∈ QT0.originalSubgroup ⊓ centralizer ({τ} : Set P45))
    id Function.injective_id _ (t0L_spec.2.filter _) ?_
  intro b
  simp only [List.mem_filter, decide_eq_true_eq, t0L_spec.1, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, id_eq, exists_eq_right]

theorem centCard_QP45 {cd : P45 → ℕ} {r : P45} {ps : List (ℕ × ℕ)} {ts : List (List ℕ)} {k : ℕ}
    (h : Certificates.OmegaT0.orbTr cd [x45, y45] r ps ts k = true) :
    k * centCard QP45.originalSubgroup r = 25920 := by
  have h1 := ncard_conjSet_of_orbTr _ _ _ _ _ _ h
  rw [← QP45_eq_closure] at h1
  rw [← h1, ← card_QP45]
  exact ncard_conjSet_mul _ _

theorem exists_cover {p : P45}
    (hp : p ∈ QP45.originalSubgroup) (h2 : orderOf p = 2) :
    ∃ c ∈ QP45.originalSubgroup,
      c * p * c⁻¹ = Certificates.OmegaT0.z0 () ∨ c * p * c⁻¹ = Certificates.OmegaT0.yB () := by
  have hn := n7Chk_true
  simp only [Certificates.OmegaT0.n7Chk, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hn
  have hcov := hn.2.1
  have hp2 : p * p = 1 := by
    have := pow_orderOf_eq_one p
    rwa [h2, pow_two] at this
  have hp1 : p ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at h2
    omega
  have hP : IsPGroup 2 (Subgroup.zpowers p) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2, pow_one])
  obtain ⟨Q, hQ, hle⟩ := exists_isSylow2Of_ge hP (Subgroup.zpowers_le.2 hp)
  obtain ⟨a, ha, hmem⟩ := IsSylow2Of.exists_conj_mem isSylow2Of_QT0 hQ
  have ht : a⁻¹ * p * a ∈ Certificates.OmegaT0.t0L () :=
    (t0L_spec.1 _).2 ((hmem p).1 (hle (Subgroup.mem_zpowers p)))
  have ht2 : a⁻¹ * p * a * (a⁻¹ * p * a) = 1 := by
    have e : a⁻¹ * p * a * (a⁻¹ * p * a) = a⁻¹ * (p * p) * a := by group
    rw [e, hp2, mul_one, inv_mul_cancel]
  have ht1 : a⁻¹ * p * a ≠ 1 := fun h => hp1 (by
    have e : p = a * (a⁻¹ * p * a) * a⁻¹ := by group
    rw [e, h, mul_one, mul_inv_cancel])
  obtain ⟨w, r, hr, e⟩ := coverW_sound _ _ _ _ hcov _ ht ht2 ht1
  have hS : ∀ s ∈ [x45, y45], s ∈ QP45.originalSubgroup := fun s hs => by
    rw [QP45_eq_closure]
    exact Subgroup.subset_closure hs
  set c := Certificates.OmegaT0.wordW [x45, y45] w
  have hc : c * a⁻¹ * p * (c * a⁻¹)⁻¹ = c * (a⁻¹ * p * a) * c⁻¹ := by group
  refine ⟨c * a⁻¹, QP45.originalSubgroup.mul_mem (wordW_mem hS w)
    (QP45.originalSubgroup.inv_mem ha), ?_⟩
  rw [hc, e]
  rcases List.mem_cons.1 hr with rfl | hr'
  · exact Or.inl rfl
  · exact Or.inr (List.mem_singleton.1 hr')

theorem isSylow2Of_inf_centralizer
    {r : P45} {k m : ℕ}
    (h1 : Nat.card ↥(QT0.originalSubgroup ⊓ centralizer ({r} : Set P45)) = 2 ^ k)
    (h2 : Nat.card ↥(QP45.originalSubgroup ⊓ centralizer ({r} : Set P45)) = 2 ^ k * m)
    (hm : m % 2 = 1) :
    IsSylow2Of (QT0.originalSubgroup ⊓ centralizer ({r} : Set P45))
      (QP45.originalSubgroup ⊓ centralizer ({r} : Set P45)) := by
  have hle : QT0.originalSubgroup ⊓ centralizer ({r} : Set P45) ≤
      QP45.originalSubgroup ⊓ centralizer ({r} : Set P45) := inf_le_inf_right _ X11.QT0_le
  refine ⟨hle, IsPGroup.of_card h1, ?_⟩
  have h := Subgroup.relIndex_mul_card (H := QT0.originalSubgroup ⊓ centralizer ({r} : Set P45))
    (K := QP45.originalSubgroup ⊓ centralizer ({r} : Set P45))
  rw [inf_eq_left.2 hle, h1, h2] at h
  have h' : (QT0.originalSubgroup ⊓ centralizer ({r} : Set P45)).relIndex
      (QP45.originalSubgroup ⊓ centralizer ({r} : Set P45)) * 2 ^ k = m * 2 ^ k := by
    rw [h, mul_comm]
  have hR := Nat.eq_of_mul_eq_mul_right (by positivity) h'
  rintro ⟨q, hq⟩
  omega

theorem n7_model
    {r : P45}
    (hr : r = Certificates.OmegaT0.z0 () ∨ r = Certificates.OmegaT0.yB ()) :
    r ∈ QT0.originalSubgroup ∧
      IsSylow2Of (QT0.originalSubgroup ⊓ centralizer ({r} : Set P45))
        (QP45.originalSubgroup ⊓ centralizer ({r} : Set P45)) ∧
      r ∈ ⁅QT0.originalSubgroup ⊓ centralizer ({r} : Set P45),
        QT0.originalSubgroup ⊓ centralizer ({r} : Set P45)⁆ := by
  have hn := n7Chk_true
  simp only [Certificates.OmegaT0.n7Chk, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hn
  obtain ⟨-, -, hzT, hyT, hoz, hzT64, hoy, hyT32, haT, hbT, haz, hbz, hab, hcT, hdT, hcy, hdy,
    hcd⟩ := hn
  have hz576 := centCard_QP45 hoz
  have hy96 := centCard_QP45 hoy
  have hT := t0L_spec.1
  have hTc : ∀ {a r' : P45}, a ∈ Certificates.OmegaT0.t0L () → a * r' = r' * a →
      a ∈ QT0.originalSubgroup ⊓ centralizer ({r'} : Set P45) := fun ha hc =>
    Subgroup.mem_inf.2 ⟨(hT _).1 ha, Subgroup.mem_centralizer_singleton_iff.2 hc⟩
  rcases hr with rfl | rfl
  · refine ⟨(hT _).1 hzT, isSylow2Of_inf_centralizer (k := 6) (m := 9) ?_ ?_ (by norm_num), ?_⟩
    · rw [card_inf_centralizer_t0L]
      exact hzT64
    · rw [card_inf_centralizer_eq]
      simp only [Nat.reducePow, Nat.reduceMul]
      omega
    · have := Subgroup.commutator_mem_commutator (hTc haT haz) (hTc hbT hbz)
      rwa [commutatorElement_def, hab] at this
  · refine ⟨(hT _).1 hyT, isSylow2Of_inf_centralizer (k := 5) (m := 3) ?_ ?_ (by norm_num), ?_⟩
    · rw [card_inf_centralizer_t0L]
      exact hyT32
    · rw [card_inf_centralizer_eq]
      simp only [Nat.reducePow, Nat.reduceMul]
      omega
    · have := Subgroup.commutator_mem_commutator (hTc hcT hcy) (hTc hdT hdy)
      rwa [commutatorElement_def, hcd] at this

end CFSG.OddStandard.SmallF3.Omega
